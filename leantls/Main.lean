import LeanTLS
import LeanTLS.Client
open LeanTLS

/-- `tlsget [--insecure] HOST [PATH] [PORT]` — HTTPS GET over LeanTLS; prints the raw response. -/
def main (args : List String) : IO UInt32 := do
  let insecure := args.contains "--insecure"
  match args.filter (· != "--insecure") with
  | host :: rest =>
    let path := rest.headD "/"
    let port := ((rest.drop 1).head?.bind String.toNat?).getD 443
    try
      let c ← LeanTLS.connect host port.toUInt16 (insecure := insecure)
      let auth := if c.verified then
          s!"certificate verified ({c.peerCerts.length} in chain)"
        else "certificate NOT verified (--insecure)"
      IO.eprintln s!"[leantls] TLS 1.3 with {host}: ChaCha20-Poly1305, {c.group}; {auth}"
      c.writeString s!"GET {path} HTTP/1.1\r\nHost: {host}\r\nUser-Agent: leantls/0.2\r\nConnection: close\r\n\r\n"
      let body ← c.readAll
      c.close
      (← IO.getStdout).write body
      return 0
    catch e =>
      IO.eprintln s!"[leantls] {e}"
      return 1
  | [] => IO.eprintln "usage: tlsget [--insecure] HOST [PATH] [PORT]"; return 2
