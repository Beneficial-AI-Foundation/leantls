import LeanTLS.SHA256
import LeanTLS.SHA512
/-!
# RSA signature verification (RFC 8017): RSASSA-PKCS1-v1_5 and RSASSA-PSS

Public-key operations only (verification), over `Nat` (GMP-backed).
-/
namespace LeanTLS.RSA

/-- Hash functions used by TLS / X.509 signatures. -/
inductive Hash where
  | sha256 | sha384 | sha512
  deriving DecidableEq, Repr

def Hash.digest : Hash → ByteArray → ByteArray
  | .sha256, m => SHA256.hash m
  | .sha384, m => SHA512.hash384 m
  | .sha512, m => SHA512.hash512 m

def Hash.len : Hash → Nat
  | .sha256 => 32 | .sha384 => 48 | .sha512 => 64

theorem Hash.digest_size (h : Hash) (m : ByteArray) : (h.digest m).size = h.len := by
  cases h <;> simp [Hash.digest, Hash.len]

/-- `b ^ e mod m` by left-to-right square-and-multiply. -/
def powMod (b e m : Nat) : Nat :=
  (List.range (Nat.log2 e + 1)).reverse.foldl (fun r t =>
    let r := r * r % m
    if e.testBit t then r * b % m else r) (1 % m)

structure PublicKey where
  n : Nat
  e : Nat
  deriving DecidableEq, Repr

/-- Modulus length in bytes. -/
def PublicKey.k (pk : PublicKey) : Nat := (Nat.log2 pk.n + 8) / 8

/-- RSAVP1: `s ^ e mod n`, after the range check `s < n`. -/
def vp1 (pk : PublicKey) (sig : ByteArray) : Option Nat :=
  let s := decodeBE sig
  if sig.size == pk.k && s < pk.n then some (powMod s pk.e pk.n) else none

/-- ASN.1 DigestInfo prefixes (RFC 8017 §9.2, note 1). -/
def digestInfoPrefix : Hash → ByteArray
  | .sha256 => ofHex "3031300d060960864801650304020105000420"
  | .sha384 => ofHex "3041300d060960864801650304020205000430"
  | .sha512 => ofHex "3051300d060960864801650304020305000440"

/-- EMSA-PKCS1-v1_5 encoding: `00 01 FF…FF 00 ‖ DigestInfo`. -/
def emsaPkcs1 (h : Hash) (msg : ByteArray) (k : Nat) : Option ByteArray :=
  let t := digestInfoPrefix h ++ h.digest msg
  if k < t.size + 11 then none
  else some (ofHex "0001" ++ mapBytes (fun _ => 0xff) (zeros (k - t.size - 3)) ++ u8 0 ++ t)

def verifyPkcs1 (pk : PublicKey) (h : Hash) (msg sig : ByteArray) : Bool :=
  match vp1 pk sig, emsaPkcs1 h msg pk.k with
  | some m, some em => beN pk.k m == em
  | _, _ => false

/-- MGF1 mask generation (RFC 8017 §B.2.1). -/
def mgf1 (h : Hash) (seed : ByteArray) (len : Nat) : ByteArray :=
  let blocks := (len + h.len - 1) / h.len
  ((List.range blocks).foldl (fun acc c => acc ++ h.digest (seed ++ beN 4 c)) ByteArray.empty).extract 0 len

/-- EMSA-PSS verification (RFC 8017 §9.1.2) with salt length = hash length (as TLS 1.3 requires). -/
def verifyPss (pk : PublicKey) (h : Hash) (msg sig : ByteArray) : Bool :=
  match vp1 pk sig with
  | none => false
  | some m =>
    let modBits := Nat.log2 pk.n + 1
    let emBits := modBits - 1
    let emLen := (emBits + 7) / 8
    let hLen := h.len
    let sLen := hLen
    if m ≥ 2 ^ (8 * emLen) || emLen < hLen + sLen + 2 then false else
    let em := beN emLen m
    if byteAt em (emLen - 1) != 0xbc then false else
    let maskedDB := em.extract 0 (emLen - hLen - 1)
    let hh := em.extract (emLen - hLen - 1) (emLen - 1)
    let topBits := 8 * emLen - emBits
    let topMask : UInt8 := (0xff : UInt8) >>> topBits.toUInt8
    if topBits > 0 && (byteAt maskedDB 0 &&& ~~~topMask) != 0 then false else
    let db := xorWith maskedDB (mgf1 h hh (emLen - hLen - 1))
    let db := db.set! 0 (byteAt db 0 &&& topMask)
    let psLen := emLen - hLen - sLen - 2
    if (List.range psLen).any (fun i => byteAt db i != 0) || byteAt db psLen != 1 then false else
    let salt := db.extract (db.size - sLen) db.size
    let h' := h.digest (zeros 8 ++ h.digest msg ++ salt)
    ctEq hh h'

end LeanTLS.RSA
