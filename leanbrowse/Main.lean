import LeanBrowse
open LeanBrowse

/-! # lbrowse — a tiny terminal web browser on LeanTLS -/

structure View where
  url : Url
  page : Html.Page
  lines : Array String      -- wrapped
  status : Nat
  transport : Transport

def termWidth : IO Nat := do
  let w := (← IO.getEnv "COLUMNS").bind String.toNat?
  return min 110 ((w.getD 100) - 2)

def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
def dim (s : String) : String := s!"\x1b[2m{s}\x1b[0m"
def yellow (s : String) : String := s!"\x1b[33m{s}\x1b[0m"
def green (s : String) : String := s!"\x1b[32m{s}\x1b[0m"

def load (cfg : TlsConfig) (u : Url) : IO View := do
  let (u, r, t) ← fetch cfg u
  let ct := ((r.header? "content-type").getD "text/html").toLower
  let text := decodeText r.body
  let page :=
    if ct.startsWith "text/html" || ct.contains "xhtml" then Html.render text
    else if ct.startsWith "text/" then { title := "", lines := (text.splitOn "\n").toArray, links := #[] }
    else { title := "", lines := #[s!"[{ct} — {r.body.size} bytes, not displayed]"], links := #[] }
  let w ← termWidth
  let lines := page.lines.toList.flatMap (Html.wrap w) |>.toArray
  return { url := u, page, lines, status := r.status, transport := t }

def banner (v : View) : String :=
  let title := if v.page.title.isEmpty then v.url.toString else v.page.title
  let t := v.transport
  let sec := if t.tls && t.verified then
      green s!"🔒 TLS 1.3 · ChaCha20-Poly1305 · {t.group} · certificate verified ({t.certCount} in chain)"
    else if t.tls then
      yellow s!"TLS 1.3 · ChaCha20-Poly1305 · {t.group} · ⚠ certificate NOT verified (--insecure)"
    else yellow "plain HTTP · not encrypted"
  s!"{bold ("━━ " ++ title)}\n{dim v.url.toString} · {v.status}\n{sec}\n"

def showLines (v : View) (start n : Nat) : IO Unit := do
  for l in (v.lines.extract start (start + n)) do IO.println l

def help : String :=
  "Enter: next page · <n>: follow link n · g <url>: go · b: back · l: list links · r: reload · \
   t: top · q: quit"

partial def loop (cfg : TlsConfig) (stdin : IO.FS.Stream) (hist : List View) (v : View) (pos : Nat) (pageLen : Nat) :
    IO Unit := do
  let more := pos < v.lines.size
  IO.print (dim s!"[{min pos v.lines.size}/{v.lines.size} lines · {v.page.links.size} links{if more then " · Enter for more" else ""}] ")
  IO.print "> "
  (← IO.getStdout).flush
  let line ← stdin.getLine
  if line.isEmpty then return   -- EOF
  let cmd := line.trimAscii.toString
  let go (u? : Option Url) : IO Unit := do
    match u? with
    | none => IO.println "  (unsupported or invalid link)"; loop cfg stdin hist v pos pageLen
    | some u =>
      IO.println (dim s!"  loading {u} …")
      try
        let v' ← load cfg u
        IO.println ""
        IO.print (banner v')
        showLines v' 0 pageLen
        loop cfg stdin (v :: hist) v' pageLen pageLen
      catch e =>
        IO.println (yellow s!"  error: {e}")
        loop cfg stdin hist v pos pageLen
  if cmd.isEmpty then
    if more then showLines v pos pageLen; loop cfg stdin hist v (pos + pageLen) pageLen
    else loop cfg stdin hist v pos pageLen
  else if cmd == "q" then return
  else if cmd == "h" || cmd == "?" then IO.println help; loop cfg stdin hist v pos pageLen
  else if cmd == "t" then showLines v 0 pageLen; loop cfg stdin hist v pageLen pageLen
  else if cmd == "l" then
    for (h, i) in v.page.links.toList.zipIdx do IO.println s!"  [{i + 1}] {h}"
    loop cfg stdin hist v pos pageLen
  else if cmd == "b" then
    match hist with
    | p :: rest => IO.print (banner p); showLines p 0 pageLen; loop cfg stdin rest p pageLen pageLen
    | [] => IO.println "  (no history)"; loop cfg stdin hist v pos pageLen
  else if cmd == "r" then go (some v.url)
  else if cmd.startsWith "g " then go (parseUrl (cmd.drop 2).toString)
  else match cmd.toNat? with
    | some n =>
      match v.page.links[n - 1]? with
      | some h => go (resolve v.url h)
      | none => IO.println s!"  no link [{n}]"; loop cfg stdin hist v pos pageLen
    | none => go (parseUrl cmd)

def main (args : List String) : IO UInt32 := do
  let dump := args.contains "--dump"
  let insecure := args.contains "--insecure"
  let args := args.filter (fun a => a != "--dump" && a != "--insecure")
  let start := args.headD "https://example.com/"
  let some u := parseUrl start | IO.eprintln s!"bad URL: {start}"; return 2
  try
    let trust ← if insecure then pure none else some <$> LeanTLS.TrustStore.load
    let cfg : TlsConfig := { trust, insecure }
    let v ← load cfg u
    if dump then
      IO.print (banner v)
      for l in v.lines do IO.println l
      unless v.page.links.isEmpty do
        IO.println "\nLinks:"
        for (h, i) in v.page.links.toList.zipIdx do
          IO.println s!"  [{i + 1}] {(resolve v.url h).map toString |>.getD h}"
      return 0
    IO.print (banner v)
    IO.println (dim help)
    showLines v 0 40
    loop cfg (← IO.getStdin) [] v 40 40
    return 0
  catch e =>
    IO.eprintln s!"lbrowse: {e}"
    return 1
