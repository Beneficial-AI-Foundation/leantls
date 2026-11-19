/-!
# HTML → text

A forgiving tokenizer and a text renderer. Everything here is total (fuel-bounded structural
recursion, no `partial`), so rendering any byte string terminates.
-/
namespace LeanBrowse.Html

inductive Tok where
  | text (s : String)
  | openTag (name : String) (attrs : List (String × String))
  | closeTag (name : String)
  deriving Repr, DecidableEq

def isNameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == ':'

def startsWithCI (l : List Char) (pat : List Char) : Bool :=
  (l.take pat.length).map Char.toLower == pat

/-- Drop through the first occurrence of `pat` (or everything). -/
def dropPast (pat : List Char) : Nat → List Char → List Char
  | 0, _ => []
  | _, [] => []
  | f + 1, c :: cs => if startsWithCI (c :: cs) pat then (c :: cs).drop pat.length else dropPast pat f cs

/-- Split at the first occurrence of `pat` (case-insensitive): `(before, fromPat)`. -/
def breakAt (pat : List Char) : Nat → List Char → List Char × List Char
  | 0, l => ([], l)
  | _, [] => ([], [])
  | f + 1, c :: cs =>
    if startsWithCI (c :: cs) pat then ([], c :: cs)
    else let (a, b) := breakAt pat f cs; (c :: a, b)

def readAttrValue : Nat → List Char → String × List Char
  | 0, l => ("", l)
  | _, '"' :: cs => let (v, r) := cs.span (· != '"'); (String.ofList v, r.drop 1)
  | _, '\'' :: cs => let (v, r) := cs.span (· != '\''); (String.ofList v, r.drop 1)
  | _, cs => let (v, r) := cs.span (fun c => !c.isWhitespace && c != '>'); (String.ofList v, r)

/-- Attributes up to and including the closing `>`. -/
def readAttrs : Nat → List Char → List (String × String) → List (String × String) × List Char
  | 0, l, acc => (acc.reverse, l)
  | f + 1, l, acc =>
    let l := l.dropWhile Char.isWhitespace
    match l with
    | [] => (acc.reverse, [])
    | '>' :: r => (acc.reverse, r)
    | '/' :: r => readAttrs f r acc
    | _ =>
      let (n, r) := l.span (fun c => !c.isWhitespace && c != '=' && c != '>' && c != '/')
      if n.isEmpty then readAttrs f (l.drop 1) acc else
      let r := r.dropWhile Char.isWhitespace
      match r with
      | '=' :: r =>
        let (v, r) := readAttrValue f (r.dropWhile Char.isWhitespace)
        readAttrs f r ((String.ofList (n.map Char.toLower), v) :: acc)
      | _ => readAttrs f r ((String.ofList (n.map Char.toLower), "") :: acc)

/-- Elements whose content is not HTML and never shown. -/
def rawSkip : List String := ["script", "style", "template", "svg", "noscript", "iframe", "object"]

def tokenize : Nat → List Char → Array Tok → Array Tok
  | 0, _, acc => acc
  | _, [], acc => acc
  | f + 1, '<' :: cs, acc =>
    if startsWithCI cs "!--".toList then tokenize f (dropPast "-->".toList f cs) acc
    else if startsWithCI cs "!".toList || startsWithCI cs "?".toList then
      tokenize f (dropPast ">".toList f cs) acc
    else
      match cs with
      | '/' :: r =>
        let (n, r) := r.span isNameChar
        if n.isEmpty then tokenize f r (acc.push (.text "</"))
        else tokenize f (dropPast ">".toList f r) (acc.push (.closeTag (String.ofList (n.map Char.toLower))))
      | c :: _ =>
        if !c.isAlpha then tokenize f cs (acc.push (.text "<")) else
        let (n, r) := cs.span isNameChar
        let name := String.ofList (n.map Char.toLower)
        let (attrs, r) := readAttrs f r []
        if rawSkip.contains name then
          let (_, r) := breakAt ("</" ++ name).toList f r
          tokenize f (dropPast ">".toList f r) (acc.push (.openTag name attrs) |>.push (.closeTag name))
        else tokenize f r (acc.push (.openTag name attrs))
      | [] => acc.push (.text "<")
  | f + 1, cs, acc =>
    let (t, r) := cs.span (· != '<')
    tokenize f r (acc.push (.text (String.ofList t)))

def tokens (s : String) : Array Tok := tokenize (s.length + 1) s.toList #[]

/-! ## entities -/

def namedEntity : String → Option String
  | "amp" => "&" | "lt" => "<" | "gt" => ">" | "quot" => "\"" | "apos" => "'"
  | "nbsp" => " " | "mdash" => "—" | "ndash" => "–" | "hellip" => "…" | "copy" => "©"
  | "reg" => "®" | "trade" => "™" | "rsquo" => "’" | "lsquo" => "‘" | "rdquo" => "”"
  | "ldquo" => "“" | "laquo" => "«" | "raquo" => "»" | "middot" => "·" | "bull" => "•"
  | "times" => "×" | "deg" => "°" | "euro" => "€" | "pound" => "£" | "para" => "¶"
  | "sect" => "§" | "shy" => "" | "zwj" => "" | "zwnj" => "" | "thinsp" => " " | "ensp" => " "
  | "emsp" => " " | "larr" => "←" | "rarr" => "→" | "uarr" => "↑" | "darr" => "↓"
  | _ => none

def numEntity (s : String) : Option String :=
  let n? := if s.startsWith "x" || s.startsWith "X" then
      (s.drop 1).toString.toList.foldl (fun acc c => acc.bind fun a =>
        if c.isDigit then some (a * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f' then some (a * 16 + (c.toLower.toNat - 'a'.toNat + 10))
        else none) (some 0)
    else s.toNat?
  n?.map fun n => if n == 0 || n > 0x10FFFF then "�" else String.singleton (Char.ofNat n)

def decodeEntities (s : String) : String := Id.run do
  if !s.contains '&' then return s
  let cs := s.toList
  let mut out := ""
  let mut i := 0
  let arr := cs.toArray
  while i < arr.size do
    let c := arr[i]!
    if c == '&' then
      let rest := (arr.extract (i + 1) (i + 33)).toList
      match rest.findIdx? (· == ';') with
      | some j =>
        let name := String.ofList (rest.take j)
        let rep := if name.startsWith "#" then numEntity (name.drop 1).toString else namedEntity name
        match rep with
        | some r => out := out ++ r; i := i + j + 2
        | none => out := out.push c; i := i + 1
      | none => out := out.push c; i := i + 1
    else
      out := out.push c; i := i + 1
  return out

/-! ## rendering -/

structure Page where
  title : String
  lines : Array String
  links : Array String
  deriving Repr, DecidableEq, Inhabited

structure R where
  out : Array String := #[]
  line : String := ""
  links : Array String := #[]
  linkOpen : Option Nat := none
  title : String := ""
  inTitle : Bool := false
  inHead : Bool := false
  pre : Nat := 0
  listDepth : Nat := 0

def blockTags : List String :=
  ["p", "div", "section", "article", "header", "footer", "nav", "main", "aside", "ul", "ol",
   "table", "tr", "blockquote", "form", "dl", "dt", "dd", "figure", "figcaption", "h1", "h2",
   "h3", "h4", "h5", "h6", "pre", "li", "address", "fieldset", "details", "summary", "body", "center"]

def R.flush (r : R) : R :=
  let l := r.line.trimAsciiEnd.toString
  if l.isEmpty then { r with line := "" } else { r with out := r.out.push l, line := "" }

/-- Flush and leave at most one blank line. -/
def R.para (r : R) : R :=
  let r := r.flush
  if r.out.isEmpty || r.out.back! == "" then r else { r with out := r.out.push "" }

def R.addText (r : R) (raw : String) : R :=
  if r.inTitle then { r with title := r.title ++ decodeEntities raw } else
  if r.inHead then r else
  let t := decodeEntities raw
  if r.pre > 0 then
    match t.splitOn "\n" with
    | [] => r
    | first :: rest =>
      rest.foldl (fun r seg => { r.flush with line := seg }) { r with line := r.line ++ first }
  else
    let words := (t.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty)
    if words.isEmpty then
      if t.isEmpty || r.line.isEmpty || r.line.endsWith " " then r else { r with line := r.line ++ " " }
    else
      let lead := if t.front.isWhitespace && !r.line.isEmpty && !r.line.endsWith " " then " " else ""
      let trail := if t.back.isWhitespace then " " else ""
      { r with line := r.line ++ lead ++ " ".intercalate words ++ trail }

def attr (as : List (String × String)) (k : String) : Option String := (as.find? (·.1 == k)).map (·.2)

def R.openTag (r : R) (name : String) (as : List (String × String)) : R :=
  match name with
  | "title" => { r with inTitle := true }
  | "head" => { r with inHead := true }
  | "body" => { r with inHead := false }
  | "br" => r.flush
  | "hr" => { r.para with out := r.para.out.push "────────────────────────────────" } |>.para
  | "pre" => { r.para with pre := r.pre + 1 }
  | "ul" | "ol" => { r.flush with listDepth := r.listDepth + 1 }
  | "li" => { r.flush with line := "".pushn ' ' (2 * r.listDepth) ++ "• " }
  | "h1" => { r.para with line := "# " }
  | "h2" => { r.para with line := "## " }
  | "h3" => { r.para with line := "### " }
  | "td" | "th" => if r.line.isEmpty then r else { r with line := r.line ++ "  " }
  | "img" =>
    match attr as "alt" with
    | some a => if a.trimAscii.isEmpty then r else r.addText s!" [{a.trimAscii}] "
    | none => r
  | "a" =>
    match attr as "href" with
    | some h =>
      if h.startsWith "#" || h.trimAscii.isEmpty then r
      else { r with links := r.links.push h.trimAscii.toString, linkOpen := some r.links.size }
    | none => r
  | _ => if blockTags.contains name then r.para else r

def R.closeTag (r : R) (name : String) : R :=
  match name with
  | "title" => { r with inTitle := false }
  | "head" => { r with inHead := false }
  | "pre" => { r.para with pre := r.pre - 1 }
  | "ul" | "ol" => { r.para with listDepth := r.listDepth - 1 }
  | "li" => r.flush
  | "a" =>
    match r.linkOpen with
    | some i => { r with line := r.line ++ s!"[{i + 1}]", linkOpen := none }
    | none => r
  | _ => if blockTags.contains name then r.para else r

def render (html : String) : Page :=
  let r := (tokens html).foldl (fun r t =>
    match t with
    | .text s => r.addText s
    | .openTag n as => r.openTag n as
    | .closeTag n => r.closeTag n) ({} : R)
  let r := r.flush
  let lines := if !r.out.isEmpty && r.out.back! == "" then r.out.pop else r.out
  { title := (" ".intercalate ((r.title.split Char.isWhitespace).toList.map (·.toString)
              |>.filter (!·.isEmpty)))
    lines, links := r.links }

/-- Word-wrap one line to `width` columns (continuation lines keep the list indent). -/
def wrap (width : Nat) (line : String) : List String :=
  if line.length ≤ width then [line] else
  let lead := (line.takeWhile (· == ' ')).toString
  let indent := if (line.drop lead.length).startsWith "• " then lead ++ "  " else lead
  let words := (line.splitOn " ").filter (!·.isEmpty)
  let (ls, cur) := words.foldl (fun (ls, cur) w =>
    if cur.isEmpty then (ls, lead ++ w)
    else if cur.length + 1 + w.length > width then (ls ++ [cur], indent ++ w)
    else (ls, cur ++ " " ++ w)) (([] : List String), "")
  if cur.isEmpty then ls else ls ++ [cur]

end LeanBrowse.Html
