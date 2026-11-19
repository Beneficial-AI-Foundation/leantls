import Std.Async
import LeanTLS.Client
import LeanTLS.ServerMessages
/-!
# TLS 1.3 server connection (IO)

A thin `Async` shell around the pure server side (`ServerMessages`, `Sign`, `KeySchedule`,
`Record`): it reads and writes records over a caller-supplied `Transport`, so the caller keeps
control of sockets and timeouts.

Handshake: ClientHello → ServerHello, (CCS), {EncryptedExtensions, Certificate,
CertificateVerify, Finished} → client {Finished}, which is checked. Then application data in
both directions, KeyUpdate, close_notify. Unsupported: HelloRetryRequest, resumption, 0-RTT,
client certificates (the server never asks for them).
-/
namespace LeanTLS.Server
open Std.Async TLS13 Record

/-- A byte stream the TLS layer runs over. `recv ms`: `none` = timed out, `some none` = closed. -/
structure Transport where
  recv : Nat → Async (Option (Option ByteArray))
  send : ByteArray → Async Unit

/-- A certificate chain (DER, leaf first) and its private key. -/
structure Identity where
  chain : List ByteArray
  key : Sign.PrivKey

/-- Load an identity from PEM files' contents; checks that the key matches the leaf. -/
def Identity.ofPem (certPem keyPem : String) : Except String Identity :=
  let chain := X509.pemCerts certPem
  match chain.head? with
  | none => .error "no certificate found in PEM"
  | some leafDer =>
    match X509.parse leafDer with
    | .error e => .error e
    | .ok leaf =>
      match Sign.parsePrivateKeyPem keyPem with
      | .error e => .error e
      | .ok key =>
        if key.matches leaf.key then .ok { chain, key }
        else .error "private key does not match the certificate"

structure Conn where
  t : Transport
  rbuf : IO.Ref ByteArray
  hsbuf : IO.Ref ByteArray
  rd : IO.Ref Dir
  wr : IO.Ref Dir
  closed : IO.Ref Bool
  /-- SNI host name the client asked for. -/
  serverName : Option String
  alpn : Bool

inductive Accepted where
  | tls (c : Conn)
  /-- The peer did not speak TLS; these are the bytes it sent (e.g. a plain HTTP request). -/
  | plain (firstBytes : ByteArray)
  | failed (reason : String)

def record (ty : Nat) (body : ByteArray) : ByteArray := u8 ty ++ be16 0x0303 ++ be16 body.size ++ body

/-- One raw record `(type, header, body)`; `none` on close, timeout, or a malformed header. -/
partial def readRecord (t : Transport) (rbuf : IO.Ref ByteArray) (ms : Nat) :
    Async (Option (Nat × ByteArray × ByteArray)) := do
  let buf ← rbuf.get
  if buf.size ≥ 5 then
    let len := rd16 buf 3
    if len > 16384 + 256 then return none
    if buf.size ≥ 5 + len then
      rbuf.set (buf.extract (5 + len) buf.size)
      return some (rd8 buf 0, buf.extract 0 5, buf.extract 5 (5 + len))
  match ← t.recv ms with
  | some (some d) =>
    if d.size == 0 then return none
    rbuf.modify (· ++ d)
    readRecord t rbuf ms
  | _ => return none

def alert (t : Transport) (code : Nat) : Async Unit := do
  try t.send (record 21 (u8 2 ++ u8 code)) catch _ => pure ()

/-- Seal handshake bytes into as many records as needed, starting at sequence number `seq`. -/
def sealChunks (keys : TrafficKeys) (seq : Nat) (ty : UInt8) (data : ByteArray) : ByteArray × Nat :=
  go (data.size / 16384 + 1) 0 seq ByteArray.empty
where
  go : Nat → Nat → Nat → ByteArray → ByteArray × Nat
    | 0, _, s, acc => (acc, s)
    | fuel + 1, off, s, acc =>
      if off ≥ data.size && off > 0 then (acc, s) else
      let n := min 16384 (data.size - off)
      let acc := acc ++ sealRecord keys.key keys.iv s ty (data.extract off (off + n))
      if off + n ≥ data.size then (acc, s + 1) else go fuel (off + n) (s + 1) acc

/-- Run the server handshake. `pick` chooses the identity for the SNI name (or the default).
`ms` is the timeout for each read. -/
def accept (t : Transport) (pick : Option String → Option Identity) (ms : Nat) : Async Accepted := do
  let rbuf ← IO.mkRef ByteArray.empty
  -- First bytes: a TLS handshake record starts with 0x16.
  let first ← match ← t.recv ms with
    | some (some d) => pure d
    | _ => return .failed "no data"
  if first.size == 0 then return .failed "no data"
  if byteAt first 0 != 22 then return .plain first
  rbuf.set first
  -- Collect the ClientHello (it may span several records).
  let mut hs := ByteArray.empty
  let mut chMsg : Option (ByteArray × ByteArray) := none
  for _ in [0:64] do
    match parseHs hs with
    | some (1, body, _) => chMsg := some (hsMsg 1 body, body); break
    | some _ => alert t 10; return .failed "expected ClientHello"
    | none =>
      match ← readRecord t rbuf ms with
      | some (22, _, b) => hs := hs ++ b
      | _ => return .failed "connection closed before ClientHello"
  let some (chRaw, chBody) := chMsg | alert t 50; return .failed "ClientHello too large"
  let ch ← match Parser.run parseClientHello chBody with
    | .ok ch => pure ch
    | .error e => alert t 50; return .failed s!"bad ClientHello: {e}"
  let some ident := pick ch.serverName | alert t 112; return .failed "no certificate for this name"
  match negotiate ch ident.key.scheme with
  | .alert code => alert t code; return .failed s!"negotiation failed (alert {code})"
  | .accept group peer _ alpn =>
  -- Ephemeral key exchange
  let rnd ← IO.getRandomBytes 32
  let (pub, shared?) :=
    if group == GROUP_X25519 then
      let z := X25519.x25519 rnd peer
      (X25519.publicKey rnd, if z == zeros 32 then none else some z)
    else
      let (d, p) := EC.p256Keygen rnd
      (p, EC.p256Shared d peer)
  let some shared := shared? | alert t 47; return .failed "invalid key share"
  let srvRandom ← IO.getRandomBytes 32
  let sh := serverHello srvRandom ch.sessionId group pub
  let transcript := chRaw ++ sh
  let secrets := handshakeSecrets shared transcript
  let salt ← IO.getRandomBytes 32
  let some (flight, transcript) := serverFlight secrets transcript ident.chain ident.key alpn salt
    | alert t 80; return .failed "signing failed"
  let sKeys := trafficKeys secrets.serverHs
  let cKeys := trafficKeys secrets.clientHs
  let (sealed, _) := sealChunks sKeys 0 22 flight
  t.send (record 22 sh ++ ofHex "140303000101" ++ sealed)
  -- Client Finished
  let mut cbuf := ByteArray.empty
  let mut seq := 0
  let mut finished := false
  for _ in [0:16] do
    if finished then break
    match parseHs cbuf with
    | some (20, body, _) =>
      if !ctEq body (finishedVerify secrets.clientHs transcript) then
        alert t 51; return .failed "client Finished MAC mismatch"
      finished := true
    | some (ty, _, _) => alert t 10; return .failed s!"unexpected handshake message {ty}"
    | none =>
      match ← readRecord t rbuf ms with
      | some (20, _, _) => pure ()
      | some (21, _, b) => return .failed s!"client alert: {alertName (rd8 b 1)}"
      | some (23, hdr, body) =>
        match openRecord cKeys.key cKeys.iv seq hdr body with
        | none => alert t 20; return .failed "bad_record_mac in handshake"
        | some (content, ity) =>
          seq := seq + 1
          if ity == 22 then cbuf := cbuf ++ content
          else if ity == 21 then return .failed s!"client alert: {alertName (rd8 content 1)}"
          else alert t 10; return .failed "unexpected record during handshake"
      | _ => return .failed "connection closed during handshake"
  unless finished do return .failed "no client Finished"
  let (cAp, sAp) := appSecrets secrets.master transcript
  return .tls {
    t, rbuf
    hsbuf := ← IO.mkRef ByteArray.empty
    rd := ← IO.mkRef (Dir.ofSecret cAp)
    wr := ← IO.mkRef (Dir.ofSecret sAp)
    closed := ← IO.mkRef false
    serverName := ch.serverName
    alpn }

namespace Conn

/-- Send application data (split into records of at most 16 KiB). -/
def write (c : Conn) (data : ByteArray) : Async Unit := do
  if data.size == 0 then return
  let d ← c.wr.get
  let (sealed, seq) := sealChunks d.keys d.seq 23 data
  c.wr.set { d with seq := seq }
  c.t.send sealed

/-- Post-handshake messages from the client (KeyUpdate). -/
partial def handlePostHandshake (c : Conn) : Async Unit := do
  match parseHs (← c.hsbuf.get) with
  | none => pure ()
  | some (ty, body, rest) =>
    c.hsbuf.set rest
    if ty == 24 then
      c.rd.modify fun d => Dir.ofSecret (nextTrafficSecret d.secret)
      if rd8 body 0 == 1 then
        let d ← c.wr.get
        c.t.send (sealRecord d.keys.key d.keys.iv d.seq 22 (hsMsg 24 (u8 0)))
        c.wr.set (Dir.ofSecret (nextTrafficSecret d.secret))
    else throw <| IO.userError s!"TLS: unexpected post-handshake message {ty}"
    handlePostHandshake c

/-- Next chunk of application data: `none` = timed out, `some none` = closed by the peer. -/
partial def read (c : Conn) (ms : Nat) : Async (Option (Option ByteArray)) := do
  if ← c.closed.get then return some none
  let buf ← c.rbuf.get
  -- Distinguish a timeout from a close: try one receive ourselves when no full record is buffered.
  if buf.size < 5 || buf.size < 5 + rd16 buf 3 then
    match ← c.t.recv ms with
    | none => return none
    | some none => c.closed.set true; return some none
    | some (some d) =>
      if d.size == 0 then c.closed.set true; return some none
      c.rbuf.modify (· ++ d)
      return ← c.read ms
  match ← readRecord c.t c.rbuf ms with
  | none => c.closed.set true; return some none
  | some (20, _, _) => c.read ms
  | some (23, hdr, body) =>
    let d ← c.rd.get
    match openRecord d.keys.key d.keys.iv d.seq hdr body with
    | none => c.closed.set true; throw <| IO.userError "TLS: bad_record_mac"
    | some (content, ity) =>
      c.rd.set { d with seq := d.seq + 1 }
      match ity with
      | 23 => if content.size == 0 then c.read ms else return some (some content)
      | 22 => c.hsbuf.modify (· ++ content); handlePostHandshake c; c.read ms
      | 21 => c.closed.set true; return some none
      | _ => c.closed.set true; return some none
  | some _ => c.closed.set true; return some none

/-- Send close_notify. -/
def close (c : Conn) : Async Unit := do
  try
    let d ← c.wr.get
    c.t.send (sealRecord d.keys.key d.keys.iv d.seq 21 (ofHex "0100"))
    c.wr.set { d with seq := d.seq + 1 }
  catch _ => pure ()

end Conn
end LeanTLS.Server
