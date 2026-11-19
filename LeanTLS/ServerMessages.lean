import LeanTLS.Messages
import LeanTLS.KeySchedule
import LeanTLS.Sign
/-!
# TLS 1.3 server side: ClientHello parsing, negotiation, server messages (pure)

The server mirrors the client: one cipher suite (`TLS_CHACHA20_POLY1305_SHA256`), key exchange
X25519 or P-256, certificates with ECDSA P-256 or RSA keys (signed with
`ecdsa_secp256r1_sha256` / `rsa_pss_rsae_sha256`), ALPN `http/1.1`. No HelloRetryRequest, no
session resumption, no 0-RTT, no client certificates.
-/
namespace LeanTLS.TLS13
open Parser

structure ClientHello where
  random : ByteArray
  sessionId : ByteArray
  suites : List Nat
  versions : List Nat := []
  groups : List Nat := []
  shares : List (Nat × ByteArray) := []
  sigAlgs : List Nat := []
  serverName : Option String := none
  alpn : List ByteArray := []

/-- Parse items until the (sub-)buffer is exhausted. -/
def many (p : Parser α) : Nat → Parser (List α)
  | 0 => pure []
  | fuel + 1 => fun b i =>
    if i ≥ b.size then .ok ([], i) else
    (do let x ← p; let xs ← many p fuel; pure (x :: xs)) b i

def vecOf16 (p : Parser α) : Parser (List α) := do
  let len ← n16
  sub len (many p len)

def keyShareEntry : Parser (Nat × ByteArray) := do
  let g ← n16
  let l ← n16
  let k ← bytes l
  pure (g, k)

def serverNameEntry : Parser (Nat × ByteArray) := do
  let ty ← n8
  let l ← n16
  let n ← bytes l
  pure (ty, n)

def vec8Item : Parser ByteArray := do
  let l ← n8
  bytes l

def parseCHExts (acc : ClientHello) : Nat → Parser ClientHello
  | 0 => pure acc
  | fuel + 1 => fun b i =>
    if i ≥ b.size then .ok (acc, i) else
    (do
      let ty ← n16
      let len ← n16
      let acc ← sub len (match ty with
        | 0 => do
          let names ← vecOf16 serverNameEntry
          pure { acc with serverName :=
            (names.find? (fun (e : Nat × ByteArray) => e.1 == 0)).bind fun (_, n) => String.fromUTF8? n }
        | 10 => do let gs ← vecOf16 n16; pure { acc with groups := gs }
        | 13 => do let ss ← vecOf16 n16; pure { acc with sigAlgs := ss }
        | 16 => do let ps ← vecOf16 vec8Item; pure { acc with alpn := ps }
        | 43 => do
          let l ← n8
          let vs ← sub l (many n16 l)
          pure { acc with versions := vs }
        | 51 => do let ks ← vecOf16 keyShareEntry; pure { acc with shares := ks }
        | _ => pure acc)
      parseCHExts acc fuel) b i

/-- Parse a ClientHello body (the handshake message without its 4-byte header). -/
def parseClientHello : Parser ClientHello := do
  let _legacyVersion ← n16
  let random ← bytes 32
  let sidLen ← n8
  let sid ← bytes sidLen
  let suites ← vecOf16 n16
  let compLen ← n8
  let _comp ← bytes compLen
  let ch : ClientHello := { random, sessionId := sid, suites }
  -- extensions are optional in the grammar, but TLS 1.3 needs them
  fun b i =>
    if i ≥ b.size then .ok (ch, i) else
    (do let extLen ← n16; sub extLen (parseCHExts ch 128)) b i

/-! ## Negotiation -/

/-- What the server will do with a ClientHello. -/
inductive Choice where
  | accept (group : Nat) (peerShare : ByteArray) (scheme : Nat) (alpn : Bool)
  /-- Abort with this alert description. -/
  | alert (code : Nat)
  deriving Inhabited

def http11 : ByteArray := ofString "http/1.1"

/-- RFC 8446 §4.1.1 server choices, for a certificate key that signs with `scheme`. -/
def negotiate (ch : ClientHello) (scheme : Nat) : Choice :=
  if !ch.versions.contains 0x0304 then .alert 70                  -- protocol_version
  else if !ch.suites.contains TLS_CHACHA20_POLY1305_SHA256 then .alert 40  -- handshake_failure
  else if !ch.sigAlgs.contains scheme then .alert 40
  else if !ch.alpn.isEmpty && !ch.alpn.contains http11 then .alert 120   -- no_application_protocol
  else
    let alpn := ch.alpn.contains http11
    match ch.shares.find? (fun (g, k) => g == GROUP_X25519 && k.size == 32) with
    | some (_, k) => .accept GROUP_X25519 k scheme alpn
    | none =>
      match ch.shares.find? (fun (g, k) => g == GROUP_SECP256R1 && k.size == 65) with
      | some (_, k) => .accept GROUP_SECP256R1 k scheme alpn
      | none => .alert 40   -- would need a HelloRetryRequest (not implemented)

/-! ## Server messages -/

def vec24 (b : ByteArray) : ByteArray := be24 b.size ++ b

/-- ServerHello body: TLS 1.3, ChaCha20-Poly1305, the server key share; echoes the session id. -/
def serverHelloBody (random sid : ByteArray) (group : Nat) (pub : ByteArray) : ByteArray :=
  be16 0x0303 ++ random ++ vec8 sid ++ be16 TLS_CHACHA20_POLY1305_SHA256 ++ u8 0 ++
    vec16 (ext 43 (be16 0x0304) ++ ext 51 (be16 group ++ vec16 pub))

def serverHello (random sid : ByteArray) (group : Nat) (pub : ByteArray) : ByteArray :=
  Record.hsMsg 2 (serverHelloBody random sid group pub)

def encryptedExtensions (alpn : Bool) : ByteArray :=
  Record.hsMsg 8 (vec16 (if alpn then ext 16 (vec16 (vec8 http11)) else ByteArray.empty))

def certificateMsg (chain : List ByteArray) : ByteArray :=
  Record.hsMsg 11 (u8 0 ++ vec24 (concatAll (chain.map fun c => vec24 c ++ be16 0)))

def certVerifyMsg (scheme : Nat) (sig : ByteArray) : ByteArray :=
  Record.hsMsg 15 (be16 scheme ++ vec16 sig)

def finishedMsg (baseKey transcript : ByteArray) : ByteArray :=
  Record.hsMsg 20 (finishedVerify baseKey transcript)

/-- The server's flight after ServerHello, as one byte string of handshake messages, and the
transcript through the server Finished. `transcript` is `ClientHello ‖ ServerHello`. -/
def serverFlight (secrets : HsSecrets) (transcript : ByteArray) (chain : List ByteArray)
    (key : Sign.PrivKey) (alpn : Bool) (salt : ByteArray) : Option (ByteArray × ByteArray) := do
  let t := transcript ++ encryptedExtensions alpn ++ certificateMsg chain
  let (scheme, sig) ← Sign.certVerify key (SHA256.hash t) salt
  let t := t ++ certVerifyMsg scheme sig
  let fin := finishedMsg secrets.serverHs t
  let flight := encryptedExtensions alpn ++ certificateMsg chain ++ certVerifyMsg scheme sig ++ fin
  pure (flight, t ++ fin)

end LeanTLS.TLS13
