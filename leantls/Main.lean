import LeanTLS
import LeanTLS.Client
open LeanTLS

/-- `tlsget HOST [PATH]` — HTTPS GET over the LeanTLS TLS 1.3 client; prints the raw response. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | host :: rest =>
    let path := rest.headD "/"
    let c ← LeanTLS.connect host
    IO.eprintln s!"[leantls] TLS 1.3 established with {host} (TLS_CHACHA20_POLY1305_SHA256, X25519); \
      {c.peerCerts.length} certificate(s) received — NOT validated"
    c.writeString s!"GET {path} HTTP/1.1\r\nHost: {host}\r\nUser-Agent: leantls/0.1\r\nConnection: close\r\n\r\n"
    let body ← c.readAll
    c.close
    (← IO.getStdout).write body
    return 0
  | [] => IO.eprintln "usage: tlsget HOST [PATH]"; return 2
