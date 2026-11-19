import LeanTLS.Record
import LeanTLS.SHA256
/-!
# TLS 1.3 handshake messages: ClientHello builder, ServerHello / Certificate parsers
-/
namespace LeanTLS.TLS13
open LeanTLS.Record

def TLS_CHACHA20_POLY1305_SHA256 : Nat := 0x1303
def GROUP_X25519 : Nat := 0x001d
def GROUP_SECP256R1 : Nat := 0x0017

/-- A total cursor parser over a fixed byte string. -/
abbrev Parser (α : Type) := ByteArray → Nat → Except String (α × Nat)

namespace Parser
def pure' (a : α) : Parser α := fun _ i => .ok (a, i)
def bind' (p : Parser α) (f : α → Parser β) : Parser β := fun b i =>
  match p b i with
  | .ok (a, j) => f a b j
  | .error e => .error e
instance : Monad Parser where
  pure := pure'
  bind := bind'
def fail (msg : String) : Parser α := fun _ _ => .error msg
def bytes (n : Nat) : Parser ByteArray := fun b i =>
  if i + n ≤ b.size then .ok (b.extract i (i + n), i + n) else .error "truncated"
def n8 : Parser Nat := fun b i => if i + 1 ≤ b.size then .ok (rd8 b i, i + 1) else .error "truncated"
def n16 : Parser Nat := fun b i => if i + 2 ≤ b.size then .ok (rd16 b i, i + 2) else .error "truncated"
def n24 : Parser Nat := fun b i => if i + 3 ≤ b.size then .ok (rd24 b i, i + 3) else .error "truncated"
def run (p : Parser α) (b : ByteArray) : Except String α := (p b 0).map (·.1)
/-- Run `p` on the next `n` bytes as a sub-buffer. -/
def sub (n : Nat) (p : Parser α) : Parser α := do
  let s ← bytes n
  match p s 0 with
  | .ok (a, _) => pure a
  | .error e => fail e
end Parser

open Parser

/-! ## ClientHello -/

def ext (ty : Nat) (data : ByteArray) : ByteArray := be16 ty ++ be16 data.size ++ data

def vec8 (b : ByteArray) : ByteArray := u8 b.size ++ b
def vec16 (b : ByteArray) : ByteArray := be16 b.size ++ b

/-- Signature schemes we can verify (CertificateVerify: ECDSA / RSA-PSS; certificates also
    use PKCS#1 v1.5). -/
def sigAlgs : List Nat :=
  [0x0403, 0x0503, 0x0804, 0x0805, 0x0806, 0x0401, 0x0501, 0x0601]

def concatAll (l : List ByteArray) : ByteArray := l.foldl (· ++ ·) ByteArray.empty

/-- ClientHello body offering TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256`, groups X25519 and P-256,
    with one key share `(group, public key)`; `cookie` echoes a HelloRetryRequest cookie. -/
def clientHelloBody (random sessionId : ByteArray) (share : Nat × ByteArray) (host : String)
    (cookie : Option ByteArray := none) : ByteArray :=
  let h := ofString host
  let exts := concatAll [
    ext 0 (vec16 (u8 0 ++ vec16 h)),                       -- server_name
    ext 10 (vec16 (be16 GROUP_X25519 ++ be16 GROUP_SECP256R1)), -- supported_groups
    ext 13 (vec16 (concatAll (sigAlgs.map be16))),         -- signature_algorithms
    ext 16 (vec16 (vec8 (ofString "http/1.1"))),           -- ALPN
    ext 43 (vec8 (be16 0x0304)),                           -- supported_versions
    ext 45 (vec8 (u8 1)),                                  -- psk_key_exchange_modes: psk_dhe_ke
    ext 51 (vec16 (be16 share.1 ++ vec16 share.2))] ++    -- key_share
    (match cookie with | some c => ext 44 c | none => ByteArray.empty)   -- cookie
  be16 0x0303 ++ random ++ vec8 sessionId ++ vec16 (be16 TLS_CHACHA20_POLY1305_SHA256) ++
    vec8 (u8 0) ++ vec16 exts

def clientHello (random sessionId : ByteArray) (share : Nat × ByteArray) (host : String)
    (cookie : Option ByteArray := none) : ByteArray :=
  hsMsg 1 (clientHelloBody random sessionId share host cookie)

/-- The ClientHello is a well-framed handshake message of type 1. -/
theorem parseHs_clientHello (r s : ByteArray) (k : Nat × ByteArray) (host : String)
    (c : Option ByteArray) (rest : ByteArray) (h : (clientHelloBody r s k host c).size < 16777216) :
    parseHs (clientHello r s k host c ++ rest) = some (1, clientHelloBody r s k host c, rest) :=
  parseHs_hsMsg 1 (by decide) _ rest h

/-! ## ServerHello -/

/-- SHA-256("HelloRetryRequest"): the `random` value marking a HelloRetryRequest. -/
def hrrRandom : ByteArray :=
  ofHex "cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c"

structure ServerHello where
  cipherSuite : Nat
  version : Nat
  keyShareGroup : Nat
  keyShare : ByteArray
  isHRR : Bool
  /-- Raw `cookie` extension data from a HelloRetryRequest (to be echoed). -/
  cookie : Option ByteArray := none

def parseExts (acc : ServerHello) : Nat → Parser ServerHello
  | 0 => pure acc
  | fuel + 1 => fun b i =>
    if i ≥ b.size then .ok (acc, i) else
    (do
      let ty ← n16
      let len ← n16
      let acc ← sub len (match ty with
        | 43 => do let v ← n16; pure { acc with version := v }
        | 44 => do let c ← bytes len; pure { acc with cookie := some c }
        | 51 => do
          let g ← n16
          if acc.isHRR then pure { acc with keyShareGroup := g } else
          let kl ← n16; let k ← bytes kl
          pure { acc with keyShareGroup := g, keyShare := k }
        | _ => pure acc)
      parseExts acc fuel) b i

def parseServerHello : Parser ServerHello := do
  let _legacyVersion ← n16
  let random ← bytes 32
  let sidLen ← n8
  let _sid ← bytes sidLen
  let suite ← n16
  let _comp ← n8
  let extLen ← n16
  sub extLen (parseExts
    { cipherSuite := suite, version := 0x0303, keyShareGroup := 0, keyShare := ByteArray.empty,
      isHRR := random == hrrRandom } 64)

/-- The transcript prefix replacing ClientHello1 after a HelloRetryRequest (RFC 8446 §4.4.1). -/
def messageHash (ch1 : ByteArray) : ByteArray := hsMsg 254 (SHA256.hash ch1)

/-- CertificateVerify body: `scheme(2) ‖ vec16 signature`. -/
def parseCertVerify : Parser (Nat × ByteArray) := do
  let scheme ← n16
  let l ← n16
  let sig ← bytes l
  pure (scheme, sig)

/-! ## Certificate (chain extraction; validation is in `LeanTLS.X509`) -/

def parseCertEntries : Nat → Parser (List ByteArray)
  | 0 => pure []
  | fuel + 1 => fun b i =>
    if i ≥ b.size then .ok ([], i) else
    (do
      let cl ← n24; let c ← bytes cl
      let el ← n16; let _ ← bytes el
      let rest ← parseCertEntries fuel
      pure (c :: rest)) b i

def parseCertificate : Parser (List ByteArray) := do
  let ctxLen ← n8
  let _ ← bytes ctxLen
  let listLen ← n24
  sub listLen (parseCertEntries 64)

end LeanTLS.TLS13
