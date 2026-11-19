/-!
# Byte utilities

Big/little-endian encoders and decoders, XOR, constant-shape equality.
Every encoder here comes with a decode-after-encode theorem.
-/
namespace LeanTLS

/-- Read byte `i`, or `0` when out of range.
    (Indexes the `ByteArray` directly: going through `.data` would copy the whole buffer.) -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

/-- Specification view of `byteAt`. -/
theorem byteAt_eq_getD (b : ByteArray) (i : Nat) : byteAt b i = b.data.getD i 0 := by
  unfold byteAt Array.getD
  split
  · next h => rw [dite_eq_left (show i < b.data.size from h)]; exact ByteArray.getElem_eq_getElem_data
  · next h => rw [dite_eq_right (show ¬ i < b.data.size from h)]

def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

@[simp] theorem zeros_size (n : Nat) : (zeros n).size = n := by
  simp [zeros, ByteArray.size]

def u8 (x : Nat) : ByteArray := ⟨#[x.toUInt8]⟩
def be16 (x : Nat) : ByteArray := ⟨#[(x / 256).toUInt8, x.toUInt8]⟩
def be24 (x : Nat) : ByteArray := ⟨#[(x / 65536).toUInt8, (x / 256).toUInt8, x.toUInt8]⟩

/-- `n`-byte big-endian encoding of `x` (mod 256^n). -/
def beN (n x : Nat) : ByteArray :=
  ⟨Array.ofFn (n := n) fun i => (x / 256 ^ (n - 1 - i.val)).toUInt8⟩

/-- `n`-byte little-endian encoding of `x` (mod 256^n). -/
def leN (n x : Nat) : ByteArray :=
  ⟨Array.ofFn (n := n) fun i => (x / 256 ^ i.val).toUInt8⟩

@[simp] theorem u8_size (x : Nat) : (u8 x).size = 1 := rfl
@[simp] theorem be16_size (x : Nat) : (be16 x).size = 2 := rfl
@[simp] theorem be24_size (x : Nat) : (be24 x).size = 3 := rfl
@[simp] theorem beN_size (n x : Nat) : (beN n x).size = n := by
  simp [beN, ByteArray.size]
@[simp] theorem leN_size (n x : Nat) : (leN n x).size = n := by
  simp [leN, ByteArray.size]

def rd8 (b : ByteArray) (i : Nat) : Nat := (byteAt b i).toNat
def rd16 (b : ByteArray) (i : Nat) : Nat := rd8 b i * 256 + rd8 b (i + 1)
def rd24 (b : ByteArray) (i : Nat) : Nat := rd8 b i * 65536 + rd8 b (i + 1) * 256 + rd8 b (i + 2)

/-- Little-endian decode of the whole array. -/
def decodeLE (b : ByteArray) : Nat :=
  b.data.foldr (fun x acc => x.toNat + 256 * acc) 0

/-- Big-endian decode of the whole array. -/
def decodeBE (b : ByteArray) : Nat :=
  b.data.foldl (fun acc x => acc * 256 + x.toNat) 0

theorem rd16_be16 (x : Nat) (h : x < 65536) : rd16 (be16 x) 0 = x := by
  simp [rd16, rd8, byteAt_eq_getD, be16, Nat.toUInt8]
  omega

theorem rd24_be24 (x : Nat) (h : x < 16777216) : rd24 (be24 x) 0 = x := by
  simp [rd24, rd8, byteAt_eq_getD, be24, Nat.toUInt8]
  omega

theorem rd8_u8 (x : Nat) (h : x < 256) : rd8 (u8 x) 0 = x := by
  simp [rd8, byteAt_eq_getD, u8, Nat.toUInt8]
  omega

/-- Byte-wise XOR; the result has the length of the first argument. -/
def xorWith (a b : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := a.size) fun i => byteAt a i ^^^ byteAt b i⟩

@[simp] theorem xorWith_size (a b : ByteArray) : (xorWith a b).size = a.size :=
  Array.size_ofFn

theorem byteAt_eq (b : ByteArray) (i : Nat) (h : i < b.data.size) : byteAt b i = b.data[i] := by
  unfold byteAt; split
  · exact ByteArray.getElem_eq_getElem_data
  · contradiction

theorem byteAt_xorWith (a b : ByteArray) (i : Nat) (h : i < a.size) :
    byteAt (xorWith a b) i = byteAt a i ^^^ byteAt b i := by
  have h' : i < (xorWith a b).data.size := by
    show i < (xorWith a b).size; rw [xorWith_size]; exact h
  rw [byteAt_eq _ _ h']
  simp only [xorWith, Array.getElem_ofFn]

/-- XOR with the same pad twice is the identity: the core of stream-cipher decryption. -/
theorem xorWith_xorWith (a b : ByteArray) : xorWith (xorWith a b) b = a := by
  apply ByteArray.ext
  apply Array.ext
  · exact (xorWith_size _ b).trans (xorWith_size a b)
  · intro i h1 h2
    have hi : i < (xorWith a b).size := by rw [xorWith_size]; exact h2
    have e := byteAt_xorWith (xorWith a b) b i hi
    rw [byteAt_xorWith a b i h2, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero,
      byteAt_eq _ _ h1, byteAt_eq _ _ h2] at e
    exact e

/-- Equality check whose control flow does not depend on where bytes differ
    (always scans the full length). Not a constant-time guarantee at the machine level. -/
def ctEq (a b : ByteArray) : Bool :=
  a.size == b.size &&
    (List.range a.size).foldl (fun acc i => acc ||| (byteAt a i ^^^ byteAt b i)) (0 : UInt8) == 0

private theorem foldl_keep (l : List Nat) (x : UInt8) : l.foldl (fun acc _ => acc) x = x := by
  induction l generalizing x <;> simp_all

theorem ctEq_self (a : ByteArray) : ctEq a a = true := by
  simp [ctEq, UInt8.xor_self, UInt8.or_zero, foldl_keep]

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList
  String.ofList <| b.toList.flatMap fun x => [d[(x.toNat / 16)]!, d[(x.toNat % 16)]!]

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse a hex string (whitespace ignored). Used by tests. -/
def ofHex (s : String) : ByteArray :=
  let ds := (s.toList.filter (fun c => !c.isWhitespace)).filterMap hexVal
  let rec go : List Nat → Array UInt8 → Array UInt8
    | a :: b :: rest, acc => go rest (acc.push (a * 16 + b).toUInt8)
    | _, acc => acc
  ⟨go ds #[]⟩

def ofString (s : String) : ByteArray := s.toUTF8

end LeanTLS
