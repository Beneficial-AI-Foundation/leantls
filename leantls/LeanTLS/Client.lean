import Std.Async
import LeanTLS.Messages
import LeanTLS.KeySchedule
import LeanTLS.X25519
/-!
# TLS 1.3 client connection (IO)

A thin IO shell around the verified pure core: every byte that is framed, encrypted,
decrypted, parsed or derived goes through `Record`, `AEAD`, `KeySchedule` and `Messages`.

**Security status:** the server's certificate chain and CertificateVerify signature are
*not* validated yet. The handshake is authenticated against the transcript (both Finished
MACs are checked), but an active man-in-the-middle can impersonate the server.
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
  /-- DER certificates the server presented (leaf first). NOT validated. -/
  peerCerts : List ByteArray

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

/-- Open a TLS 1.3 connection to `host:port`. -/
def connect (host : String) (port : UInt16 := 443) : IO Conn := do
  let sock ← tcpConnect host port
  let rbuf ← IO.mkRef ByteArray.empty
  -- ClientHello
  let sk ← IO.getRandomBytes 32
  let random ← IO.getRandomBytes 32
  let sid ← IO.getRandomBytes 32
  let ch := clientHello random sid (X25519.publicKey sk) host
  sendRaw sock (u8 22 ++ be16 0x0301 ++ be16 ch.size ++ ch)
  -- ServerHello (plaintext)
  let mut hs := ByteArray.empty
  let mut shOpt : Option (ByteArray × ByteArray) := none
  while shOpt.isNone do
    match parseHs hs with
    | some (ty, body, rest) =>
      if ty != 2 then tlsError s!"expected ServerHello, got handshake type {ty}"
      shOpt := some (body, rest)
    | none =>
      match ← readRecord sock rbuf with
      | none => tlsError "connection closed during handshake"
      | some (22, _, b) => hs := hs ++ b
      | some (21, _, b) => tlsError s!"server alert: {alertName (rd8 b 1)}"
      | some (20, _, _) => pure ()
      | some (t, _, _) => tlsError s!"unexpected record type {t} before ServerHello"
  let some (shBody, leftover) := shOpt | tlsError "unreachable"
  let sh ← match Parser.run parseServerHello shBody with
    | .ok sh => pure sh
    | .error e => tlsError s!"bad ServerHello: {e}"
  if sh.isHRR then tlsError "server sent HelloRetryRequest (only X25519 is offered)"
  if sh.version != 0x0304 then tlsError "server did not negotiate TLS 1.3"
  if sh.cipherSuite != TLS_CHACHA20_POLY1305_SHA256 then
    tlsError s!"server chose unsupported cipher suite 0x{String.ofList (Nat.toDigits 16 sh.cipherSuite)}"
  if sh.keyShareGroup != GROUP_X25519 || sh.keyShare.size != 32 then tlsError "bad key_share"
  let shared := X25519.x25519 sk sh.keyShare
  if shared == zeros 32 then tlsError "X25519 produced the all-zero value"
  let mut transcript := ch ++ hsMsg 2 shBody
  let secrets := handshakeSecrets shared transcript
  let sKeys := trafficKeys secrets.serverHs
  let cKeys := trafficKeys secrets.clientHs
  -- Encrypted server flight: EncryptedExtensions, Certificate, CertificateVerify, Finished
  let mut buf := leftover
  let mut seq := 0
  let mut certs : List ByteArray := []
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
        transcript := transcript ++ msg
      | 15 => transcript := transcript ++ msg   -- CertificateVerify: signature NOT checked yet
      | 20 =>
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
  -- Client: middlebox-compat CCS, then Finished
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
    peerCerts := certs }

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
