import LeanTLS.X509
import LeanTLS.HKDF
/-!
# Signing: ECDSA P-256 (RFC 6979 nonces), RSA-PSS, and private keys from PEM

What a TLS *server* needs to prove possession of its certificate key in CertificateVerify.

* ECDSA nonces are deterministic (RFC 6979 §3.2, HMAC-SHA-256), so signing needs no randomness
  and is a pure function that specs can check against the RFC's vectors.
* RSA-PSS takes its salt as an argument (the IO layer passes fresh random bytes).
* **Not constant-time**, like the rest of LeanTLS: scalar multiplication and modular
  exponentiation branch on secret bits. Research code; see the README.
-/
namespace LeanTLS.Sign
open LeanTLS ASN1

/-! ## ECDSA -/

/-- `bits2int` (RFC 6979 §2.3.2): the leftmost `qlen` bits of `b` as an integer. -/
def bits2int (c : EC.Curve) (b : ByteArray) : Nat :=
  let qlen := Nat.log2 c.n + 1
  let v := decodeBE b
  if 8 * b.size > qlen then v >>> (8 * b.size - qlen) else v

/-- Concatenate HMAC outputs `V = HMAC_K(V)` until `len` bytes are collected. -/
def genT (k : ByteArray) : Nat → ByteArray → ByteArray → Nat → ByteArray × ByteArray
  | 0, v, t, _ => (t, v)
  | fuel + 1, v, t, len =>
    if t.size ≥ len then (t, v) else
    let v := hmac k v
    genT k fuel v (t ++ v) len

/-- Candidate loop of RFC 6979 §3.2 step h. -/
def nonceLoop (c : EC.Curve) : Nat → ByteArray → ByteArray → Option Nat
  | 0, _, _ => none
  | fuel + 1, k, v =>
    let (t, v) := genT k 8 v ByteArray.empty c.len
    let cand := bits2int c t
    if 1 ≤ cand && cand < c.n then some cand
    else
      let k := hmac k (v ++ u8 0)
      nonceLoop c fuel k (hmac k v)

/-- RFC 6979 deterministic nonce for private key `x` and message hash `h1` (HMAC-SHA-256). -/
def rfc6979 (c : EC.Curve) (x : Nat) (h1 : ByteArray) : Option Nat :=
  let xo := beN c.len x
  let ho := beN c.len (bits2int c h1 % c.n)
  let v := mapBytes (fun _ => 1) (zeros 32)
  let k := zeros 32
  let k := hmac k (v ++ u8 0 ++ xo ++ ho)
  let v := hmac k v
  let k := hmac k (v ++ u8 1 ++ xo ++ ho)
  let v := hmac k v
  nonceLoop c 32 k v

/-- ECDSA signature `(r, s)` of a message digest with private key `d` (SEC1 §4.1.3), nonce from
RFC 6979. `none` only in the negligible cases `r = 0` or `s = 0`. -/
def ecdsaSign (c : EC.Curve) (d : Nat) (digest : ByteArray) : Option (Nat × Nat) := do
  let k ← rfc6979 c d digest
  let (x, _) ← c.toAffine (c.smul k c.G)
  let r := x % c.n
  let e := bits2int c digest
  let s := RSA.powMod k (c.n - 2) c.n * ((e + r * d) % c.n) % c.n
  if r == 0 || s == 0 then none else some (r, s)

/-- Minimal big-endian bytes of `x` (at least one byte). -/
def minBE (x : Nat) : ByteArray := beN ((Nat.log2 x + 8) / 8) x

def derLen (n : Nat) : ByteArray :=
  if n < 128 then u8 n else if n < 256 then u8 0x81 ++ u8 n else u8 0x82 ++ be16 n

/-- DER INTEGER for a non-negative integer (a leading zero byte if the top bit is set). -/
def derInt (x : Nat) : ByteArray :=
  let b := minBE x
  let b := if byteAt b 0 ≥ 0x80 then u8 0 ++ b else b
  u8 2 ++ derLen b.size ++ b

/-- DER `ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }`. -/
def derSig (r s : Nat) : ByteArray :=
  let body := derInt r ++ derInt s
  u8 0x30 ++ derLen body.size ++ body

/-! ## RSA-PSS (RFC 8017 §8.1.1, §9.1.1) -/

/-- EMSA-PSS-ENCODE with the given salt, then RSASP1 with private exponent `d`. -/
def pssSign (n d : Nat) (h : RSA.Hash) (msg salt : ByteArray) : Option ByteArray :=
  let modBits := Nat.log2 n + 1
  let emBits := modBits - 1
  let emLen := (emBits + 7) / 8
  let hLen := h.len
  let sLen := salt.size
  if emLen < hLen + sLen + 2 then none else
  let hh := h.digest (zeros 8 ++ h.digest msg ++ salt)
  let db := zeros (emLen - sLen - hLen - 2) ++ u8 1 ++ salt
  let masked := xorWith db (RSA.mgf1 h hh (emLen - hLen - 1))
  let topBits := 8 * emLen - emBits
  let topMask : UInt8 := (0xff : UInt8) >>> topBits.toUInt8
  let masked := masked.set! 0 (byteAt masked 0 &&& topMask)
  let em := masked ++ hh ++ u8 0xbc
  let k := (Nat.log2 n + 8) / 8
  some (beN k (RSA.powMod (decodeBE em) d n))

/-! ## Private keys -/

inductive PrivKey where
  /-- P-256 private scalar. -/
  | ec (d : Nat)
  | rsa (n e d : Nat)
  deriving Inhabited

/-- The TLS 1.3 signature scheme a key signs with: `ecdsa_secp256r1_sha256` or
`rsa_pss_rsae_sha256`. -/
def PrivKey.scheme : PrivKey → Nat
  | .ec _ => 0x0403
  | .rsa .. => 0x0804

/-- The public key that belongs to a private key. -/
def PrivKey.pub : PrivKey → Option X509.PubKey
  | .ec d => (EC.P256.toAffine (EC.P256.smul d EC.P256.G)).map fun (x, y) =>
      .ec X509.OID_P256 (EC.P256.encodePoint x y)
  | .rsa n e _ => some (.rsa ⟨n, e⟩)

/-- Does the private key belong to this certificate key? -/
def PrivKey.matches (k : PrivKey) (pub : X509.PubKey) : Bool :=
  match k.pub, pub with
  | some (.ec c1 p1), .ec c2 p2 => c1 == c2 && p1 == p2
  | some (.rsa a), .rsa b => a.n == b.n && a.e == b.e
  | _, _ => false

/-- CertificateVerify signature over `transcriptHash` (RFC 8446 §4.4.3): `(scheme, signature)`.
`salt` is used by RSA-PSS only (32 random bytes). -/
def certVerify (k : PrivKey) (transcriptHash salt : ByteArray) : Option (Nat × ByteArray) :=
  let msg := X509.certVerifyContent transcriptHash
  match k with
  | .ec d => (ecdsaSign EC.P256 d (SHA256.hash msg)).map fun (r, s) => (0x0403, derSig r s)
  | .rsa n _ d => (pssSign n d .sha256 msg salt).map fun sig => (0x0804, sig)

/-- All `-----BEGIN <label>-----` blocks of a PEM file, base64-decoded. -/
def pemBlocks (label pem : String) : List ByteArray :=
  ((pem.splitOn s!"-----BEGIN {label}-----").drop 1).filterMap fun blk =>
    match blk.splitOn s!"-----END {label}-----" with
    | body :: _ => some (X509.base64Decode body.toUTF8)
    | [] => none

def childAt (b : ByteArray) (t : TLV) (i : Nat) : Except String TLV :=
  match (children b t)[i]? with
  | some c => .ok c
  | none => .error "malformed private key"

/-- PKCS#1 `RSAPrivateKey` (version, n, e, d, …). -/
def parseRsa (b : ByteArray) : Except String PrivKey := do
  let some t := tlv b 0 | throw "malformed RSA private key"
  let n ← childAt b t 1
  let e ← childAt b t 2
  let d ← childAt b t 3
  pure (.rsa (natOf b n) (natOf b e) (natOf b d))

/-- SEC1 `ECPrivateKey` (version 1, private key OCTET STRING, [0] curve). -/
def parseSec1 (b : ByteArray) : Except String PrivKey := do
  let some t := tlv b 0 | throw "malformed EC private key"
  let d ← childAt b t 1
  for c in children b t do
    if c.tag == 0xa0 then
      if let some oid := tlv b c.start then
        unless oidString b oid == X509.OID_P256 do
          throw "only P-256 (prime256v1) EC keys are supported"
  pure (.ec (decodeBE (content b d)))

/-- PKCS#8 `PrivateKeyInfo` wrapping an RSA or EC key. -/
def parsePkcs8 (b : ByteArray) : Except String PrivKey := do
  let some t := tlv b 0 | throw "malformed PKCS#8 private key"
  let alg ← childAt b t 1
  let key ← childAt b t 2
  let oid ← childAt b alg 0
  let inner := content b key
  let a := oidString b oid
  if a == X509.OID_RSA then parseRsa inner
  else if a == X509.OID_EC then
    let some p := (children b alg)[1]? | throw "EC key without curve parameters"
    unless oidString b p == X509.OID_P256 do throw "only P-256 (prime256v1) EC keys are supported"
    parseSec1 inner
  else throw s!"unsupported private key algorithm {a}"

/-- Load a private key from PEM: `PRIVATE KEY` (PKCS#8), `EC PRIVATE KEY` (SEC1) or
`RSA PRIVATE KEY` (PKCS#1). Encrypted keys are not supported. -/
def parsePrivateKeyPem (pem : String) : Except String PrivKey :=
  if pem.contains "ENCRYPTED" then .error "encrypted private keys are not supported"
  else match pemBlocks "PRIVATE KEY" pem, pemBlocks "EC PRIVATE KEY" pem, pemBlocks "RSA PRIVATE KEY" pem with
    | b :: _, _, _ => parsePkcs8 b
    | [], b :: _, _ => parseSec1 b
    | [], [], b :: _ => parseRsa b
    | [], [], [] => .error "no private key found in PEM"

end LeanTLS.Sign
