import LeanTLS.EC
/-!
# X.509 certificates (RFC 5280): parsing, signatures, hostname matching, path validation

Everything here is pure; `LeanTLS.TrustStore` loads roots from disk and `LeanTLS.Client`
calls `validate` with the current time.

Policy (deliberately conservative):
* signatures: RSA PKCS#1 v1.5 with SHA-256/384/512, ECDSA P-256/P-384 with SHA-256/384/512;
* every certificate in the path must be inside its validity period;
* intermediates must assert `basicConstraints cA=TRUE`, have `keyCertSign` if `keyUsage` is
  present, and respect `pathLenConstraint`;
* an unknown **critical** extension rejects the certificate (e.g. name constraints);
* the leaf must list the host in `subjectAltName` (CN is ignored, as browsers do) and, if it has
  `extendedKeyUsage`, include `serverAuth`;
* revocation (CRL/OCSP) is not checked.
-/
namespace LeanTLS.X509
open ASN1

inductive PubKey where
  | rsa (pk : RSA.PublicKey)
  | ec (curve : String) (point : ByteArray)

instance : Inhabited PubKey := ⟨.rsa ⟨0, 0⟩⟩

structure Cert where
  der : ByteArray
  tbs : ByteArray
  sigAlg : String
  signature : ByteArray
  issuer : ByteArray
  subject : ByteArray
  notBefore : Int
  notAfter : Int
  key : PubKey
  isCA : Bool := false
  pathLen : Option Nat := none
  keyUsage : Option Nat := none        -- first two bytes of the KeyUsage BIT STRING, big-endian
  dnsNames : List String := []
  ekuServerAuth : Option Bool := none  -- `none` = no EKU extension
  unknownCritical : List String := []
  deriving Inhabited

def OID_RSA := "1.2.840.113549.1.1.1"
def OID_EC := "1.2.840.10045.2.1"
def OID_P256 := "1.2.840.10045.3.1.7"
def OID_P384 := "1.3.132.0.34"

def child? (l : List TLV) (i : Nat) : Except String TLV :=
  match l[i]? with
  | some t => .ok t
  | none => .error "truncated certificate"

def parseKey (b : ByteArray) (spki : TLV) : Except String PubKey := do
  let parts := children b spki
  let alg ← child? parts 0
  let bitsT ← child? parts 1
  let algParts := children b alg
  let oid ← child? algParts 0
  let keyBits := bits b bitsT
  match oidString b oid with
  | "1.2.840.113549.1.1.1" =>
    let some seq := tlv keyBits 0 | throw "bad RSA key"
    match children keyBits seq with
    | [n, e] => return .rsa ⟨natOf keyBits n, natOf keyBits e⟩
    | _ => throw "bad RSA key"
  | "1.2.840.10045.2.1" =>
    let curve ← child? algParts 1
    return .ec (oidString b curve) keyBits
  | o => throw s!"unsupported public key algorithm {o}"

/-- Parse the extensions we act on; remember unknown critical ones. -/
def parseExts (b : ByteArray) (exts : TLV) (c : Cert) : Cert := Id.run do
  let mut c := c
  for e in children b exts do
    let parts := children b e
    let some oidT := parts[0]? | continue
    let oid := oidString b oidT
    let critical : Bool := match parts[1]? with
      | some t => t.tag == TAG_BOOLEAN && rd8 b t.start != 0
      | none => false
    if critical && !(["2.5.29.19", "2.5.29.15", "2.5.29.17", "2.5.29.37"].contains oid) then
      c := { c with unknownCritical := oid :: c.unknownCritical }
    let some valT := parts.getLast? | continue
    let v := content b valT
    let some inner := tlv v 0 | continue
    match oid with
    | "2.5.29.19" =>   -- basicConstraints
      let fs := children v inner
      let ca := match fs[0]? with
        | some t => t.tag == TAG_BOOLEAN && rd8 v t.start != 0
        | none => false
      let pl := (fs.find? (·.tag == TAG_INTEGER)).map (natOf v)
      c := { c with isCA := ca, pathLen := pl }
    | "2.5.29.15" =>   -- keyUsage
      c := { c with keyUsage := some (rd8 v (inner.start + 1) * 256 + rd8 v (inner.start + 2)) }
    | "2.5.29.17" =>   -- subjectAltName
      let names := (children v inner).filterMap fun g =>
        if g.tag == 0x82 then some (String.ofList ((content v g).toList.map (fun x => Char.ofNat x.toNat)))
        else none
      c := { c with dnsNames := names }
    | "2.5.29.37" =>   -- extendedKeyUsage
      let oids := (children v inner).map (oidString v)
      c := { c with ekuServerAuth := some (oids.contains "1.3.6.1.5.5.7.3.1" || oids.contains "2.5.29.37.0") }
    | _ => pure ()
  return c

def parse (der : ByteArray) : Except String Cert := do
  let some top := tlv der 0 | throw "not DER"
  let parts := children der top
  let tbsT ← child? parts 0
  let sigAlgT ← child? parts 1
  let sigT ← child? parts 2
  let tbsParts := children der tbsT
  let off := if (tbsParts[0]?.map (·.tag)) == some 0xa0 then 1 else 0
  let issuerT ← child? tbsParts (off + 2)
  let validityT ← child? tbsParts (off + 3)
  let subjectT ← child? tbsParts (off + 4)
  let spkiT ← child? tbsParts (off + 5)
  let times := children der validityT
  let some nb := (times[0]?).bind (timeOf der) | throw "bad notBefore"
  let some na := (times[1]?).bind (timeOf der) | throw "bad notAfter"
  let sigOid ← child? (children der sigAlgT) 0
  let key ← parseKey der spkiT
  let c : Cert := {
    der, tbs := whole der tbsT, sigAlg := oidString der sigOid, signature := bits der sigT,
    issuer := whole der issuerT, subject := whole der subjectT,
    notBefore := nb, notAfter := na, key }
  match tbsParts.find? (·.tag == 0xa3) with
  | some wrap =>
    match children der wrap with
    | [exts] => return parseExts der exts c
    | _ => return c
  | none => return c

/-! ## signatures -/

def curveOf : String → Option EC.Curve
  | "1.2.840.10045.3.1.7" => some EC.P256
  | "1.3.132.0.34" => some EC.P384
  | _ => none

/-- Verify `sig` over `msg` with `key` for an X.509 signature algorithm OID. -/
def verifyWith (key : PubKey) (sigAlg : String) (msg sig : ByteArray) : Bool :=
  let rsaHash : Option RSA.Hash := match sigAlg with
    | "1.2.840.113549.1.1.11" => some .sha256
    | "1.2.840.113549.1.1.12" => some .sha384
    | "1.2.840.113549.1.1.13" => some .sha512
    | _ => none
  let ecHash : Option RSA.Hash := match sigAlg with
    | "1.2.840.10045.4.3.2" => some .sha256
    | "1.2.840.10045.4.3.3" => some .sha384
    | "1.2.840.10045.4.3.4" => some .sha512
    | _ => none
  match key, rsaHash, ecHash with
  | .rsa pk, some h, _ => RSA.verifyPkcs1 pk h msg sig
  | .ec curve pt, _, some h =>
    match curveOf curve with
    | some c => EC.verifyDer c pt h msg sig
    | none => false
  | _, _, _ => false

/-- `child` was signed by the holder of `issuerKey`. -/
def signedBy (child : Cert) (issuerKey : PubKey) : Bool :=
  verifyWith issuerKey child.sigAlg child.tbs child.signature

/-! ## hostname matching (RFC 6125 §6.4) -/

def lowerAscii (s : String) : String := s.map Char.toLower

def labels (s : String) : List String :=
  let s := lowerAscii s
  let s := if s.endsWith "." then (s.dropEnd 1).toString else s
  s.splitOn "."

/-- Match reference labels against a presented identifier's labels. A wildcard is allowed only
    as the complete left-most label, with at least two labels after it. -/
def matchLabels : List String → List String → Bool
  | "*" :: ps, h :: hs => h != "" && ps.length ≥ 2 && ps == hs && !ps.contains "*"
  | ps, hs => !ps.contains "*" && !ps.contains "" && ps == hs

/-- **A wildcard covers exactly one label.** -/
theorem matchLabels_wild_one (ps hs : List String) (h : matchLabels ("*" :: ps) hs = true) :
    hs.length = ps.length + 1 := by
  cases hs with
  | nil => simp [matchLabels] at h
  | cons x xs =>
    simp [matchLabels] at h
    obtain ⟨⟨_, rfl⟩, _⟩ := h
    simp

/-- **A wildcard never matches the bare parent domain** (`*.example.com` ≠ `example.com`). -/
theorem matchLabels_wild_not_parent (ps : List String) : matchLabels ("*" :: ps) ps = false := by
  cases h : matchLabels ("*" :: ps) ps
  · rfl
  · have := matchLabels_wild_one ps ps h; omega

/-- **No wildcard on public suffixes**: `*.com` matches nothing. -/
theorem matchLabels_wild_tld (tld : String) (hs : List String) :
    matchLabels ["*", tld] hs = false := by
  cases hs with
  | nil => rfl
  | cons x xs => simp [matchLabels]

def hostMatches (pattern host : String) : Bool := matchLabels (labels pattern) (labels host)

/-! ## path validation -/

def KU_DIGITAL_SIGNATURE : Nat := 0x8000
def KU_KEY_CERT_SIGN : Nat := 0x0400

def timeOk (c : Cert) (now : Int) : Bool := c.notBefore ≤ now && now ≤ c.notAfter

def caOk (c : Cert) (depth : Nat) : Bool :=
  c.isCA && (c.keyUsage.all (fun ku => ku &&& KU_KEY_CERT_SIGN != 0)) &&
    (c.pathLen.all (fun pl => depth ≤ pl + 1))

/-- Find a path from `cur` to a trust anchor. `depth` counts intermediates below `cur`. -/
def chainTo (roots pool : List Cert) (now : Int) : Nat → Cert → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, cur, depth =>
    roots.any (fun r => r.der == cur.der) ||
    roots.any (fun r => r.subject == cur.issuer && signedBy cur r.key) ||
    pool.any (fun i =>
      i.subject == cur.issuer && i.der != cur.der && timeOk i now && caOk i depth &&
      i.unknownCritical.isEmpty && signedBy cur i.key && chainTo roots pool now fuel i (depth + 1))

/-- Validate the server's chain (`chain[0]` = leaf) for `host` at Unix time `now`.
    Returns the leaf certificate. -/
def validate (roots : List Cert) (chain : List ByteArray) (host : String) (now : Int) :
    Except String Cert := do
  let some leafDer := chain.head? | throw "server sent no certificate"
  let leaf ← parse leafDer
  let pool := (chain.drop 1).filterMap fun d => (parse d).toOption
  unless timeOk leaf now do throw "certificate expired or not yet valid"
  unless leaf.unknownCritical.isEmpty do throw s!"unsupported critical extension {leaf.unknownCritical}"
  unless leaf.dnsNames.any (hostMatches · host) do
    throw s!"certificate is not valid for {host} (names: {leaf.dnsNames.take 6})"
  unless leaf.ekuServerAuth.getD true do throw "certificate not valid for TLS server authentication"
  unless chainTo roots pool now 8 leaf 0 do throw "no trusted path to a root certificate"
  return leaf

/-! ## TLS 1.3 CertificateVerify (RFC 8446 §4.4.3) -/

/-- The signed content: 64 spaces, context string, a zero byte, then the transcript hash. -/
def certVerifyContent (transcriptHash : ByteArray) : ByteArray :=
  mapBytes (fun _ => 0x20) (zeros 64) ++ ofString "TLS 1.3, server CertificateVerify" ++ u8 0 ++
    transcriptHash

/-- Verify a CertificateVerify signature with the leaf key. PKCS#1 v1.5 schemes are not allowed
    in TLS 1.3 CertificateVerify and are rejected. -/
def verifyCertificateVerify (key : PubKey) (scheme : Nat) (sig transcriptHash : ByteArray) : Bool :=
  let msg := certVerifyContent transcriptHash
  match scheme, key with
  | 0x0403, .ec curve pt => curve == OID_P256 && EC.verifyDer EC.P256 pt .sha256 msg sig
  | 0x0503, .ec curve pt => curve == OID_P384 && EC.verifyDer EC.P384 pt .sha384 msg sig
  | 0x0804, .rsa pk => RSA.verifyPss pk .sha256 msg sig
  | 0x0805, .rsa pk => RSA.verifyPss pk .sha384 msg sig
  | 0x0806, .rsa pk => RSA.verifyPss pk .sha512 msg sig
  | _, _ => false

/-! ## PEM -/

def b64val (c : UInt8) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c.toNat - 65)
  else if 97 ≤ c ∧ c ≤ 122 then some (c.toNat - 71)
  else if 48 ≤ c ∧ c ≤ 57 then some (c.toNat + 4)
  else if c == 43 then some 62 else if c == 47 then some 63 else none

/-- Base64 decode (whitespace ignored, stops at `=`). -/
def base64Decode (s : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut acc := 0
  let mut nbits := 0
  for c in s.toList do
    if c == 61 then break
    match b64val c with
    | some v =>
      acc := (acc * 64 + v) % 2 ^ 24
      nbits := nbits + 6
      if nbits ≥ 8 then
        nbits := nbits - 8
        out := out.push ((acc / 2 ^ nbits) % 256).toUInt8
    | none => pure ()
  return out

/-- All `CERTIFICATE` blocks of a PEM bundle, DER-decoded. -/
def pemCerts (pem : String) : List ByteArray :=
  ((pem.splitOn "-----BEGIN CERTIFICATE-----").drop 1).filterMap fun blk =>
    match blk.splitOn "-----END CERTIFICATE-----" with
    | body :: _ => some (base64Decode body.toUTF8)
    | [] => none

end LeanTLS.X509
