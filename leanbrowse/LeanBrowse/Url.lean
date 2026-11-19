/-!
# URLs: parsing, relative resolution, dot-segment removal (RFC 3986 §5.2)
-/
namespace LeanBrowse

structure Url where
  scheme : String      -- "https" or "http"
  host : String
  port : Nat
  path : String        -- path + optional "?query", always starts with "/"
  deriving DecidableEq, Repr, Inhabited

def Url.defaultPort : String → Nat
  | "http" => 80
  | _ => 443

def Url.toString (u : Url) : String :=
  let p := if u.port == Url.defaultPort u.scheme then "" else s!":{u.port}"
  s!"{u.scheme}://{u.host}{p}{u.path}"

instance : ToString Url := ⟨Url.toString⟩

/-! ## dot segments -/

/-- Remove `.` and `..` path segments. -/
def removeDots : List String → List String → List String
  | [], acc => acc.reverse
  | s :: rest, acc =>
    if s = "." then removeDots rest acc
    else if s = ".." then removeDots rest acc.tail
    else removeDots rest (s :: acc)

/-- **No `..` survives normalization**, so a resolved link can never climb above `/`. -/
theorem removeDots_no_dotdot (segs acc : List String) (h : ".." ∉ acc) :
    ".." ∉ removeDots segs acc := by
  induction segs generalizing acc with
  | nil => simpa [removeDots] using h
  | cons s rest ih =>
    unfold removeDots
    split
    · exact ih acc h
    · split
      · exact ih acc.tail (fun hm => h (List.mem_of_mem_tail hm))
      · apply ih
        intro hm
        cases hm with
        | head => contradiction
        | tail _ hm => exact h hm

theorem removeDots_no_dot (segs acc : List String) (h : "." ∉ acc) :
    "." ∉ removeDots segs acc := by
  induction segs generalizing acc with
  | nil => simpa [removeDots] using h
  | cons s rest ih =>
    unfold removeDots
    split
    · exact ih acc h
    · split
      · exact ih acc.tail (fun hm => h (List.mem_of_mem_tail hm))
      · apply ih
        intro hm
        cases hm with
        | head => contradiction
        | tail _ hm => exact h hm

/-- Normalize an absolute path (keeps any `?query` untouched). -/
def normalizePath (p : String) : String :=
  let (path, query) := match p.splitOn "?" with
    | [] => ("/", "")
    | a :: rest => (a, if rest.isEmpty then "" else "?" ++ "?".intercalate rest)
  let segs := (path.splitOn "/").drop 1
  let trailing := match segs.getLast? with
    | some "." | some ".." => true
    | _ => false
  let out := removeDots segs []
  let out := if trailing then out ++ [""] else out
  "/" ++ "/".intercalate out ++ query

/-! ## parsing -/

def lower (s : String) : String := s.map Char.toLower

def dropPrefixCI (s pre : String) : Option String :=
  if lower (s.take pre.length).toString == pre then some (s.drop pre.length).toString else none

/-- Parse an absolute `http(s)://` URL. A bare `host/path` is treated as https. -/
def parseUrl (s : String) : Option Url := do
  let s := s.trimAscii.toString
  let (scheme, rest) ←
    match dropPrefixCI s "https://", dropPrefixCI s "http://" with
    | some r, _ => some ("https", r)
    | _, some r => some ("http", r)
    | none, none => if s.contains ':' && !(s.contains '.') then none else some ("https", s)
  let rest := (rest.splitOn "#").headD ""
  let authEnd := rest.toList.findIdx (fun c => c == '/' || c == '?')
  let auth := (rest.take authEnd).toString
  let path := (rest.drop authEnd).toString
  let path := if path.isEmpty then "/" else if path.startsWith "?" then "/" ++ path else path
  let auth := ((auth.splitOn "@").getLast?).getD auth   -- drop userinfo
  let (host, port) ← match auth.splitOn ":" with
    | [h] => some (h, Url.defaultPort scheme)
    | [h, p] => (fun n => (h, n)) <$> (if p.isEmpty then some (Url.defaultPort scheme) else p.toNat?)
    | _ => none
  if host.isEmpty then none
  some { scheme, host := lower host, port, path := normalizePath path }

/-- Resolve `href` against `base` (absolute, scheme-relative, absolute-path, relative, query). -/
def resolve (base : Url) (href : String) : Option Url :=
  let h := href.trimAscii.toString
  if h.isEmpty then some base
  else if (dropPrefixCI h "http://").isSome || (dropPrefixCI h "https://").isSome then parseUrl h
  else if h.startsWith "//" then parseUrl (base.scheme ++ ":" ++ h)
  else if h.startsWith "#" then some base
  else
    let firstSeg := (h.splitOn "/").headD ""
    if firstSeg.contains ':' then none     -- mailto:, javascript:, tel:, …
    else
    let h := (h.splitOn "#").headD ""
    let basePath := (base.path.splitOn "?").headD "/"
    let p :=
      if h.startsWith "/" then h
      else if h.startsWith "?" then basePath ++ h
      else
        let dir := match (basePath.splitOn "/").dropLast with
          | [] => "/"
          | ds => "/".intercalate ds ++ "/"
        dir ++ h
    some { base with path := normalizePath p }

end LeanBrowse
