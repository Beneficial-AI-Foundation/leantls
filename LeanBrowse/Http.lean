import LeanTLS.Client
import LeanBrowse.Url
import LeanBrowse.Chunked
/-!
# HTTP/1.1 client over LeanTLS (https) or plain TCP (http)
-/
namespace LeanBrowse
open LeanTLS

structure Response where
  status : Nat
  reason : String
  headers : List (String × String)
  body : ByteArray

def Response.header? (r : Response) (name : String) : Option String :=
  (r.headers.find? (fun (k, _) => lower k == lower name)).map (·.2)

/-- Index of the first `\r\n\r\n`. -/
def findHeaderEnd (b : ByteArray) : Option Nat := Id.run do
  for i in [0:b.size - 3] do
    if b.get! i == 13 && b.get! (i+1) == 10 && b.get! (i+2) == 13 && b.get! (i+3) == 10 then
      return some i
  return none

def latin1 (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

def decodeText (b : ByteArray) : String := (String.fromUTF8? b).getD (latin1 b)

def parseResponse (raw : ByteArray) : Except String Response := do
  let some i := findHeaderEnd raw | throw "malformed HTTP response (no header terminator)"
  let head := latin1 (raw.extract 0 i)
  let rest := raw.extract (i + 4) raw.size
  let lines := head.splitOn "\r\n"
  let statusLine := lines.headD ""
  let parts := statusLine.splitOn " "
  let some status := (parts.getD 1 "").toNat? | throw s!"bad status line: {statusLine}"
  let headers := (lines.drop 1).filterMap fun l =>
    match l.splitOn ":" with
    | k :: v => some (k.trimAscii.toString, (":".intercalate v).trimAscii.toString)
    | [] => none
  let r : Response := { status, reason := " ".intercalate (parts.drop 2), headers, body := rest }
  let te := (r.header? "transfer-encoding").map lower
  if te.any (·.contains "chunked") then
    match Chunked.decode rest.toList with
    | some b => return { r with body := ⟨b.toArray⟩ }
    | none => throw "malformed chunked body"
  else match (r.header? "content-length").bind String.toNat? with
    | some n => return { r with body := rest.extract 0 n }
    | none => return r

/-- Has a full response arrived? (lets us stop without waiting for the server to close) -/
def responseComplete (raw : ByteArray) : Bool :=
  match findHeaderEnd raw with
  | none => false
  | some i =>
    match parseResponse raw with
    | .error _ => false
    | .ok r =>
      if r.status / 100 == 1 || r.status == 204 || r.status == 304 then true
      else if ((r.header? "transfer-encoding").map lower).any (·.contains "chunked") then
        let tail := raw.extract (raw.size - 5) raw.size
        tail == "0\r\n\r\n".toUTF8 || tail.extract 1 5 == "\r\n\r\n".toUTF8 &&
          (Chunked.decode (raw.extract (i + 4) raw.size).toList).isSome
      else match (r.header? "content-length").bind String.toNat? with
        | some n => raw.size ≥ i + 4 + n
        | none => false

/-- What we know about the transport of a fetched page. -/
structure Transport where
  tls : Bool
  certCount : Nat := 0
  verified : Bool := false
  group : String := ""
  /-- Leaf certificate subject names, when verified. -/
  names : List String := []

/-- How to make TLS connections: roots to trust, or `insecure` to skip certificate checks. -/
structure TlsConfig where
  trust : Option LeanTLS.TrustStore := none
  insecure : Bool := false

partial def recvAll (sock : Std.Async.TCP.Socket.Client) (acc : ByteArray := .empty) : IO ByteArray := do
  match ← (sock.recv? 65536).block with
  | some d =>
    if d.size == 0 then return acc
    let acc := acc ++ d
    if responseComplete acc then return acc else recvAll sock acc
  | none => return acc

partial def tlsReadResponse (c : LeanTLS.Conn) (acc : ByteArray := .empty) : IO ByteArray := do
  match ← c.read with
  | some d =>
    let acc := acc ++ d
    if responseComplete acc then return acc else tlsReadResponse c acc
  | none => return acc

def requestBytes (u : Url) : ByteArray :=
  s!"GET {u.path} HTTP/1.1\r\nHost: {u.host}\r\nUser-Agent: LeanBrowse/0.1 (LeanTLS)\r\n\
     Accept: text/html,text/plain;q=0.9,*/*;q=0.5\r\nAccept-Encoding: identity\r\n\
     Connection: close\r\n\r\n".toUTF8

def fetchOnce (cfg : TlsConfig) (u : Url) : IO (Response × Transport) := do
  if u.scheme == "https" then
    let c ← LeanTLS.connect u.host u.port.toUInt16 cfg.trust cfg.insecure
    c.write (requestBytes u)
    let raw ← tlsReadResponse c
    c.close
    match parseResponse raw with
    | .ok r => return (r, { tls := true, certCount := c.peerCerts.length, verified := c.verified,
                            group := c.group, names := (c.leaf.map (·.dnsNames)).getD [] })
    | .error e => throw <| IO.userError e
  else
    let sock ← LeanTLS.tcpConnect u.host u.port.toUInt16
    (sock.send (requestBytes u)).block
    let raw ← recvAll sock
    match parseResponse raw with
    | .ok r => return (r, { tls := false })
    | .error e => throw <| IO.userError e

/-- GET with redirects. Returns the final URL. -/
def fetch (cfg : TlsConfig) (u : Url) (maxRedirects : Nat := 8) : IO (Url × Response × Transport) := do
  let mut u := u
  for _ in [0:maxRedirects + 1] do
    let (r, t) ← fetchOnce cfg u
    if r.status ∈ [301, 302, 303, 307, 308] then
      match (r.header? "location").bind (resolve u) with
      | some u' => u := u'; continue
      | none => return (u, r, t)
    return (u, r, t)
  throw <| IO.userError "too many redirects"

end LeanBrowse
