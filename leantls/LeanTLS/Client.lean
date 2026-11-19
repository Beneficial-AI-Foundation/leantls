import Std.Async
import LeanTLS.Messages
import LeanTLS.KeySchedule
import LeanTLS.X25519
import LeanTLS.X509
import Std.Time
/-!
# TLS 1.3 client connection (IO)

A thin IO shell around the verified pure core: every byte that is framed, encrypted,
decrypted, parsed or derived goes through `Record`, `AEAD`, `KeySchedule` and `Messages`.

**Authentication:** the server's chain is validated against the system roots
(`X509.validate`: signatures, validity, CA constraints, hostname), its CertificateVerify
signature is checked with the leaf key, and both Finished MACs are checked. `insecure := true`
skips the certificate checks (for testing only). Revocation is not checked.
-/
namespace LeanTLS
open Std.Async Std.Net TLS13 Record

structure Dir where
  keys : TrafficKeys
  secret : ByteArray
  seq : Nat

def Dir.ofSecret (s : ByteArray) : Dir := { keys := trafficKeys s, secret := s, seq := 0 }

structure Conn where
  host : String
  sock : TCP.Socket.Client
  rbuf : IO.Ref ByteArray
  hsbuf : IO.Ref ByteArray
  rd : IO.Ref Dir
  wr : IO.Ref Dir
  closed : IO.Ref Bool
  /-- DER certificates the server presented (leaf first). -/
  peerCerts : List ByteArray
  /-- Chain validated against the trust store, hostname matched, CertificateVerify checked. -/
  verified : Bool
  leaf : Option X509.Cert
  /-- Key-exchange group used. -/
  group : String

def alertName : Nat → String
  | 0 => "close_notify" | 10 => "unexpected_message" | 20 => "bad_record_mac"
  | 40 => "handshake_failure" | 42 => "bad_certificate" | 47 => "illegal_parameter"
  | 50 => "decode_error" | 51 => "decrypt_error" | 70 => "protocol_version"
  | 71 => "insufficient_security" | 80 => "internal_error" | 109 => "missing_extension"
  | 110 => "unsupported_extension" | 112 => "unrecognized_name" | 120 => "no_application_protocol"
  | n => s!"alert {n}"

def tlsError (msg : String) : IO α := throw <| IO.userError s!"TLS: {msg}"

/-- Read one raw record `(type, header, body)`; `none` on clean TCP EOF. -/
partial def readRecord (sock : TCP.Socket.Client) (rbuf : IO.Ref ByteArray) :
    IO (Option (Nat × ByteArray × ByteArray)) := do
  let buf ← rbuf.get
  if buf.size ≥ 5 then
    let len := rd16 buf 3
    if len > 16384 + 256 then tlsError "record overflow"
    if buf.size ≥ 5 + len then
      rbuf.set (buf.extract (5 + len) buf.size)
      return some (rd8 buf 0, buf.extract 0 5, buf.extract 5 (5 + len))
  match ← (sock.recv? 16384).block with
  | some d =>
    if d.size == 0 then return none
    rbuf.modify (· ++ d)
    readRecord sock rbuf
  | none => return none

def sendRaw (sock : TCP.Socket.Client) (b : ByteArray) : IO Unit := (sock.send b).block

/-- Resolve and connect a TCP socket (IPv4 preferred). -/
def tcpConnect (host : String) (port : UInt16) : IO TCP.Socket.Client := do
  let addrs ← (DNS.getAddrInfo host (toString port)).block
  let ip ← match addrs.find? (·.family == .ipv4), addrs[0]? with
    | some a, _ => pure a
    | none, some a => pure a
    | none, none => throw <| IO.userError s!"DNS: no address for {host}"
  let sa : SocketAddress := match ip with
    | .v4 a => .v4 { addr := a, port := port }
    | .v6 a => .v6 { addr := a, port := port }
  let sock ← TCP.Socket.Client.mk
  (sock.connect sa).block
  return sock

/-- System root certificates. -/
structure TrustStore where
  roots : List X509.Cert

/-- Load roots from `$SSL_CERT_FILE` or the usual system bundle locations. -/
def TrustStore.load : IO TrustStore := do
  let candidates := ((← IO.getEnv "SSL_CERT_FILE").toList) ++
    ["/etc/ssl/cert.pem", "/etc/ssl/certs/ca-certificates.crt", "/etc/pki/tls/certs/ca-bundle.crt",
     "/etc/ssl/ca-bundle.pem", "/usr/local/etc/openssl/cert.pem", "/opt/homebrew/etc/openssl@3/cert.pem"]
  for f in candidates do
    if ← System.FilePath.pathExists f then
      let roots := (X509.pemCerts (← IO.FS.readFile f)).filterMap (fun d => (X509.parse d).toOption)
      unless roots.isEmpty do return { roots }
  throw <| IO.userError "TLS: no system root certificates found (set SSL_CERT_FILE)"

def unixNow : IO Int := return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- Read plaintext handshake records until one complete message is buffered. -/
partial def readPlainHs (sock : TCP.Socket.Client) (rbuf : IO.Ref ByteArray) (hs : ByteArray) :
    IO (Nat × ByteArray × ByteArray) := do
  match parseHs hs with
  | some m => return m
  | none =>
    match ← readRecord sock rbuf with
    | none => tlsError "connection closed during handshake"
    | some (22, _, b) => readPlainHs sock rbuf (hs ++ b)
    | some (21, _, b) => tlsError s!"server alert: {alertName (rd8 b 1)}"
    | some (20, _, _) => readPlainHs sock rbuf hs
    | some (t, _, _) => tlsError s!"unexpected record type {t} before ServerHello"

/-- An ephemeral key for one group: `(group, public share, shared-secret function)`. -/
def mkShare (group : Nat) : IO (Nat × ByteArray × (ByteArray → Option ByteArray)) := do
  let rnd ← IO.getRandomBytes 32
  if group == GROUP_X25519 then
    return (group, X25519.publicKey rnd, fun peer =>
      if peer.size != 32 then none else
      let z := X25519.x25519 rnd peer
      if z == zeros 32 then none else some z)
  else if group == GROUP_SECP256R1 then
    let (d, pub) := EC.p256Keygen rnd
    return (group, pub, EC.p256Shared d)
  else tlsError s!"server selected unsupported group 0x{String.ofList (Nat.toDigits 16 group)}"

/-- Open a TLS 1.3 connection to `host:port`.
    The server must present a certificate chain that `X509.validate` accepts against `trust`
    (system roots by default) and a valid CertificateVerify signature, unless `insecure`. -/
def connect (host : String) (port : UInt16 := 443) (trust : Option TrustStore := none)
    (insecure : Bool := false) : IO Conn := do
  let store ← if insecure then pure { roots := [] } else match trust with
    | some t => pure t
    | none => TrustStore.load
  let sock ← tcpConnect host port
  let rbuf ← IO.mkRef ByteArray.empty
  let random ← IO.getRandomBytes 32
  let sid ← IO.getRandomBytes 32
  -- ClientHello 1 (X25519 share; P-256 also advertised)
  let mut (group, pub, sharedOf) ← mkShare GROUP_X25519
  let mut ch := clientHello random sid (group, pub) host
  sendRaw sock (u8 22 ++ be16 0x0301 ++ be16 ch.size ++ ch)
  let mut transcript := ch
  let (ty, body, rest) ← readPlainHs sock rbuf ByteArray.empty
  if ty != 2 then tlsError s!"expected ServerHello, got handshake type {ty}"
  let mut sh ← match Parser.run parseServerHello body with
    | .ok sh => pure sh
    | .error e => tlsError s!"bad ServerHello: {e}"
  let mut shBody := body
  let mut leftover := rest
  -- HelloRetryRequest: one retry with the group the server asked for
  if sh.isHRR then
    if sh.keyShareGroup == group then tlsError "HelloRetryRequest for a group we already sent"
    let (g, p, f) ← mkShare sh.keyShareGroup
    group := g; pub := p; sharedOf := f
    transcript := messageHash ch ++ hsMsg 2 body
    ch := clientHello random sid (group, pub) host sh.cookie
    sendRaw sock (ofHex "140303000101")   -- middlebox-compat CCS
    sendRaw sock (u8 22 ++ be16 0x0303 ++ be16 ch.size ++ ch)
    transcript := transcript ++ ch
    let (ty2, body2, rest2) ← readPlainHs sock rbuf leftover
    if ty2 != 2 then tlsError s!"expected ServerHello, got handshake type {ty2}"
    sh ← match Parser.run parseServerHello body2 with
      | .ok sh2 => pure sh2
      | .error e => tlsError s!"bad ServerHello: {e}"
    if sh.isHRR then tlsError "second HelloRetryRequest"
    shBody := body2; leftover := rest2
  if sh.version != 0x0304 then tlsError "server did not negotiate TLS 1.3"
  if sh.cipherSuite != TLS_CHACHA20_POLY1305_SHA256 then
    tlsError s!"server chose unsupported cipher suite 0x{String.ofList (Nat.toDigits 16 sh.cipherSuite)}"
  if sh.keyShareGroup != group then tlsError "server key_share group mismatch"
  let some shared := sharedOf sh.keyShare | tlsError "invalid server key share"
  transcript := transcript ++ hsMsg 2 shBody
  let secrets := handshakeSecrets shared transcript
  let sKeys := trafficKeys secrets.serverHs
  let cKeys := trafficKeys secrets.clientHs
  -- Encrypted server flight: EncryptedExtensions, Certificate, CertificateVerify, Finished
  let mut buf := leftover
  let mut seq := 0
  let mut certs : List ByteArray := []
  let mut leaf : Option X509.Cert := none
  let mut cvOk := false
  let mut done := false
  while !done do
    match parseHs buf with
    | some (ty, body, rest) =>
      let msg := hsMsg ty body
      buf := rest
      match ty with
      | 8 => transcript := transcript ++ msg
      | 11 =>
        certs := (Parser.run parseCertificate body).toOption.getD []
        unless insecure do
          match X509.validate store.roots certs host (← unixNow) with
          | .ok l => leaf := some l
          | .error e => tlsError s!"certificate verify failed: {e}"
        transcript := transcript ++ msg
      | 15 =>
        unless insecure do
          let some l := leaf | tlsError "CertificateVerify without a validated certificate"
          let some (scheme, sig) := (Parser.run parseCertVerify body).toOption
            | tlsError "malformed CertificateVerify"
          unless X509.verifyCertificateVerify l.key scheme sig (SHA256.hash transcript) do
            tlsError s!"CertificateVerify signature invalid (scheme 0x{String.ofList (Nat.toDigits 16 scheme)})"
          cvOk := true
        transcript := transcript ++ msg
      | 20 =>
        unless insecure || cvOk do tlsError "server did not prove possession of its key"
        if !ctEq body (finishedVerify secrets.serverHs transcript) then
          tlsError "server Finished MAC mismatch"
        transcript := transcript ++ msg
        done := true
      | 13 => tlsError "server requested a client certificate (unsupported)"
      | t => tlsError s!"unexpected handshake message {t}"
    | none =>
      match ← readRecord sock rbuf with
      | none => tlsError "connection closed during handshake"
      | some (20, _, _) => pure ()
      | some (21, _, b) => tlsError s!"server alert: {alertName (rd8 b 1)}"
      | some (23, hdr, body) =>
        match openRecord sKeys.key sKeys.iv seq hdr body with
        | none => tlsError "handshake record failed to decrypt"
        | some (content, ity) =>
          seq := seq + 1
          if ity == 22 then buf := buf ++ content
          else if ity == 21 then tlsError s!"server alert: {alertName (rd8 content 1)}"
          else tlsError s!"unexpected inner type {ity} during handshake"
      | some (t, _, _) => tlsError s!"unexpected record type {t}"
  -- Client: middlebox-compat CCS (unless already sent), then Finished
  sendRaw sock (ofHex "140303000101")
  let cfin := hsMsg 20 (finishedVerify secrets.clientHs transcript)
  sendRaw sock (sealRecord cKeys.key cKeys.iv 0 22 cfin)
  let (cAp, sAp) := appSecrets secrets.master transcript
  return {
    host, sock, rbuf
    hsbuf := ← IO.mkRef buf
    rd := ← IO.mkRef (Dir.ofSecret sAp)
    wr := ← IO.mkRef (Dir.ofSecret cAp)
    closed := ← IO.mkRef false
    peerCerts := certs
    verified := !insecure
    leaf
    group := if group == GROUP_X25519 then "X25519" else "P-256" }

namespace Conn

def sendRecord (c : Conn) (ty : UInt8) (content : ByteArray) : IO Unit := do
  let d ← c.wr.get
  sendRaw c.sock (sealRecord d.keys.key d.keys.iv d.seq ty content)
  c.wr.set { d with seq := d.seq + 1 }

def write (c : Conn) (data : ByteArray) : IO Unit := do
  let mut off := 0
  while off < data.size do
    let n := min 16384 (data.size - off)
    c.sendRecord 23 (data.extract off (off + n))
    off := off + n

def writeString (c : Conn) (s : String) : IO Unit := c.write s.toUTF8

/-- Handle post-handshake messages (NewSessionTicket, KeyUpdate). -/
partial def handlePostHandshake (c : Conn) : IO Unit := do
  match parseHs (← c.hsbuf.get) with
  | none => pure ()
  | some (ty, body, rest) =>
    c.hsbuf.set rest
    match ty with
    | 4 => pure ()  -- NewSessionTicket: no resumption support, ignore
    | 24 =>         -- KeyUpdate
      c.rd.modify fun d => Dir.ofSecret (nextTrafficSecret d.secret)
      if rd8 body 0 == 1 then
        c.sendRecord 22 (hsMsg 24 (u8 0))
        c.wr.modify fun d => Dir.ofSecret (nextTrafficSecret d.secret)
    | t => tlsError s!"unexpected post-handshake message {t}"
    handlePostHandshake c

/-- Next chunk of application data; `none` once the peer has closed. -/
partial def read (c : Conn) : IO (Option ByteArray) := do
  if ← c.closed.get then return none
  match ← readRecord c.sock c.rbuf with
  | none => c.closed.set true; return none
  | some (20, _, _) => c.read
  | some (23, hdr, body) =>
    let d ← c.rd.get
    match openRecord d.keys.key d.keys.iv d.seq hdr body with
    | none => tlsError "bad_record_mac"
    | some (content, ity) =>
      c.rd.set { d with seq := d.seq + 1 }
      match ity with
      | 23 => if content.size == 0 then c.read else return some content
      | 22 => c.hsbuf.modify (· ++ content); handlePostHandshake c; c.read
      | 21 =>
        if rd8 content 1 == 0 then c.closed.set true; return none
        tlsError s!"server alert: {alertName (rd8 content 1)}"
      | t => tlsError s!"unexpected inner content type {t}"
  | some (t, _, _) => tlsError s!"unexpected record type {t}"

/-- Read until the peer closes. -/
partial def readAll (c : Conn) (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  match ← c.read with
  | some d => c.readAll (acc ++ d)
  | none => return acc

def close (c : Conn) : IO Unit := do
  try c.sendRecord 21 (ofHex "0100") catch _ => pure ()
  try (c.sock.shutdown).block catch _ => pure ()

end Conn
end LeanTLS
