import LeanTLS.Bytes
/-!
# DER (X.690) parsing

A DER element is located by offsets into the original buffer, so no bytes are copied while
walking a certificate. The parser is total, and `tlv_bounds` proves that every element it
returns lies inside the buffer and after its own header.
-/
namespace LeanTLS.ASN1

/-- One parsed element: `tag`, content `[start, stop)`, element `[hdr, stop)`. -/
structure TLV where
  tag : Nat
  hdr : Nat
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Definite-length form only (DER). Long form up to 4 length bytes, minimal-length not enforced. -/
def readLen (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if i < b.size then
    let l0 := rd8 b i
    if l0 < 128 then some (l0, i + 1)
    else
      let n := l0 - 128
      if n = 0 ∨ n > 4 ∨ i + 1 + n > b.size then none
      else some ((List.range n).foldl (fun acc k => acc * 256 + rd8 b (i + 1 + k)) 0, i + 1 + n)
  else none

/-- Parse the element starting at `i` (single-byte tags only, as used by X.509). -/
def tlv (b : ByteArray) (i : Nat) : Option TLV :=
  if i < b.size then
    let tag := rd8 b i
    if tag % 32 = 31 then none else
    match readLen b (i + 1) with
    | none => none
    | some (len, s) => if s + len ≤ b.size then some ⟨tag, i, s, s + len⟩ else none
  else none

theorem readLen_gt (b : ByteArray) (i len s : Nat) (h : readLen b i = some (len, s)) : i < s := by
  unfold readLen at h
  dsimp only at h
  split at h
  · split at h
    · simp at h; omega
    · split at h
      · contradiction
      · simp at h; omega
  · contradiction

/-- **Bounds**: a parsed element starts at `i`, its content follows its header, and it ends
    inside the buffer. -/
theorem tlv_bounds (b : ByteArray) (i : Nat) (t : TLV) (h : tlv b i = some t) :
    t.hdr = i ∧ i < t.start ∧ t.start ≤ t.stop ∧ t.stop ≤ b.size := by
  unfold tlv at h
  dsimp only at h
  split at h
  · split at h
    · contradiction
    · split at h
      · contradiction
      · next len s hl =>
        split at h
        · simp at h; subst h
          have := readLen_gt b (i + 1) len s hl
          refine ⟨rfl, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
        · contradiction
  · contradiction

/-- Children of a constructed element (fuel-bounded; at most one per content byte). -/
def children (b : ByteArray) (t : TLV) : List TLV :=
  let rec go : Nat → Nat → List TLV
    | 0, _ => []
    | f + 1, i =>
      if i ≥ t.stop then [] else
      match tlv b i with
      | some c => if c.stop ≤ t.stop then c :: go f c.stop else []
      | none => []
  go (t.stop - t.start) t.start

def content (b : ByteArray) (t : TLV) : ByteArray := b.extract t.start t.stop
def whole (b : ByteArray) (t : TLV) : ByteArray := b.extract t.hdr t.stop

/-- Unsigned big-endian value of an INTEGER's content (leading zero allowed). -/
def natOf (b : ByteArray) (t : TLV) : Nat := decodeBE (content b t)

/-- BIT STRING content without the unused-bits byte. -/
def bits (b : ByteArray) (t : TLV) : ByteArray := b.extract (t.start + 1) t.stop

/-- OID as a dotted string, e.g. `1.2.840.113549.1.1.11`. -/
def oidString (b : ByteArray) (t : TLV) : String := Id.run do
  let c := content b t
  if c.size == 0 then return ""
  let first := rd8 c 0
  let mut parts : Array Nat := #[first / 40, first % 40]
  let mut acc := 0
  for i in [1:c.size] do
    let x := rd8 c i
    acc := acc * 128 + x % 128
    if x < 128 then parts := parts.push acc; acc := 0
  return ".".intercalate (parts.toList.map toString)

def TAG_BOOLEAN := 1
def TAG_INTEGER := 2
def TAG_BITSTRING := 3
def TAG_OCTETSTRING := 4
def TAG_OID := 6
def TAG_UTCTIME := 23
def TAG_GENTIME := 24
def TAG_SEQUENCE := 48
def TAG_SET := 49

/-- Days from 1970-01-01 to the given civil date (Howard Hinnant's algorithm). -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- UTCTime `YYMMDDHHMMSSZ` / GeneralizedTime `YYYYMMDDHHMMSSZ` → Unix seconds. -/
def timeOf (b : ByteArray) (t : TLV) : Option Int := do
  let s := (content b t).toList.map (fun x => Char.ofNat x.toNat)
  let digits (cs : List Char) : Option Int :=
    cs.foldlM (fun acc c => if c.isDigit then some (acc * 10 + (c.toNat - 48 : Nat)) else none) 0
  let (y, rest) ←
    if t.tag == TAG_UTCTIME then do
      let yy ← digits (s.take 2)
      pure (if yy ≥ 50 then 1900 + yy else 2000 + yy, s.drop 2)
    else if t.tag == TAG_GENTIME then do
      pure ((← digits (s.take 4)), s.drop 4)
    else none
  let mo ← digits (rest.take 2)
  let d ← digits ((rest.drop 2).take 2)
  let hh ← digits ((rest.drop 4).take 2)
  let mi ← digits ((rest.drop 6).take 2)
  let ss ← digits ((rest.drop 8).take 2)
  if rest.getLast? != some 'Z' then none
  pure (daysFromCivil y mo d * 86400 + hh * 3600 + mi * 60 + ss)

end LeanTLS.ASN1
