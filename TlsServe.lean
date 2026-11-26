import LeanTLS.Server
/-!
# `tlsserve` — a minimal HTTPS server over LeanTLS

A worked version of the sketch in the README's "Use LeanTLS as a server": it supplies the two
pieces that sketch leaves open, a `Transport` with a real receive timeout and a listen loop, and
answers every request with a fixed body.

```sh
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 \
  -keyout key.pem -out cert.pem -days 30 -nodes \
  -subj "/CN=localhost" -addext "subjectAltName=DNS:localhost"
tlsserve cert.pem key.pem 8443 &
curl --cacert cert.pem https://localhost:8443/
```

It binds the loopback interface only: this is research code with non-constant-time arithmetic,
and it is meant for interoperability testing, not for serving traffic.
-/
open Std.Async Std.Net LeanTLS LeanTLS.Server

/-- The README's `myRecvWithTimeout`: data, `none` on timeout, `some none` on a clean close. -/
def recvWithTimeout (sock : TCP.Socket.Client) (ms : Nat) :
    Async (Option (Option ByteArray)) := do
  let timeout ← Selector.sleep (Std.Time.Millisecond.Offset.ofInt ms)
  Selectable.one #[
    .case (TCP.Socket.Client.recvSelector sock 65536) (fun d => pure (some d)),
    .case timeout (fun _ => pure none)
  ]

/-- Handshake, read the request, answer, close. One connection, start to finish. -/
def handle (ident : Identity) (body : String) (sock : TCP.Socket.Client) : Async Unit := do
  let t : Transport := { recv := recvWithTimeout sock, send := sock.send }
  match ← accept t (fun _sni => some ident) 30000 with
  | .tls c =>
    -- The SNI name the client asked for; `pick` above could answer it with a different identity.
    IO.eprintln s!"[tlsserve] TLS 1.3 handshake complete (sni: {c.serverName.getD "-"})"
    match ← c.read 30000 with
    | none => IO.eprintln "[tlsserve] timed out waiting for the request"
    | some none => IO.eprintln "[tlsserve] client closed before sending a request"
    | some (some _) =>
      c.write s!"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\
        Content-Length: {body.utf8ByteSize}\r\nConnection: close\r\n\r\n{body}".toUTF8
    c.close
  | .plain _ =>
    -- Not TLS: most often a plain `http://` request to the TLS port. Say so in the clear.
    IO.eprintln "[tlsserve] peer did not speak TLS"
    let msg := "This is an HTTPS port; use https://."
    sock.send s!"HTTP/1.1 400 Bad Request\r\nContent-Type: text/plain\r\n\
      Content-Length: {msg.utf8ByteSize}\r\nConnection: close\r\n\r\n{msg}".toUTF8
  | .failed reason => IO.eprintln s!"[tlsserve] handshake failed: {reason}"

/--
`tlsserve [-n N] CERT KEY [PORT]` — serve HTTPS on `127.0.0.1:PORT` (default 8443).
`-n N` stops after `N` connections, which keeps scripted tests from leaving a server behind.
-/
def main (args : List String) : IO UInt32 := do
  let (limit, rest) := match args with
    | "-n" :: n :: rest => (n.toNat?, rest)
    | _ => (none, args)
  match rest with
  | certPath :: keyPath :: more =>
    let port := (more.head?.bind String.toNat?).getD 8443
    let ident ← match Identity.ofPem (← IO.FS.readFile certPath) (← IO.FS.readFile keyPath) with
      | .ok ident => pure ident
      | .error e => IO.eprintln s!"[tlsserve] {certPath}/{keyPath}: {e}"; return 1
    let srv ← TCP.Socket.Server.mk
    srv.bind (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := port.toUInt16 })
    srv.listen 16
    IO.eprintln s!"[tlsserve] listening on 127.0.0.1:{port}"
    -- One connection at a time: enough for interoperability testing, and easy to follow.
    let mut served := 0
    repeat
      if limit.any (served ≥ ·) then break
      let sock ← srv.accept.block
      try (handle ident "hello from LeanTLS\n" sock).block
      catch e => IO.eprintln s!"[tlsserve] {e}"
      served := served + 1
    return 0
  | _ =>
    IO.eprintln "usage: tlsserve [-n N] CERT KEY [PORT]"
    return 2
