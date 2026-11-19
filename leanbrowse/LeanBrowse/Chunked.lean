/-!
# HTTP/1.1 chunked transfer coding (RFC 9112 §7.1)

Works on `List UInt8`. Proved: decoding an encoding returns the concatenated chunks.
-/
namespace LeanBrowse.Chunked

def hexDigitVal (b : UInt8) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b ∧ b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b ∧ b ≤ 70 then some (b.toNat - 55)
  else none

def hexChar (d : Nat) : UInt8 := if d < 10 then (48 + d).toUInt8 else (87 + d).toUInt8

/-- Hex digits of `n`, most significant first. -/
def hexDigits (n : Nat) : List Nat :=
  if n < 16 then [n] else hexDigits (n / 16) ++ [n % 16]
termination_by n
decreasing_by omega

def fromDigits (l : List Nat) : Nat := l.foldl (fun acc d => acc * 16 + d) 0

theorem fromDigits_append (l : List Nat) (d : Nat) :
    fromDigits (l ++ [d]) = fromDigits l * 16 + d := by
  simp [fromDigits, List.foldl_append]

theorem fromDigits_hexDigits (n : Nat) : fromDigits (hexDigits n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold hexDigits
    split
    · simp [fromDigits]
    · rw [fromDigits_append, ih (n / 16) (by omega)]
      omega

theorem hexDigits_lt (n : Nat) : ∀ d ∈ hexDigits n, d < 16 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold hexDigits
    split
    · intro d hd; simp at hd; omega
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact ih (n / 16) (by omega) d hd
      · omega

theorem hexDigitVal_hexChar : ∀ d, d < 16 → hexDigitVal (hexChar d) = some d := by
  decide

def hexBytes (n : Nat) : List UInt8 := (hexDigits n).map hexChar

/-- Consume hex digits: `(value, rest)`. -/
def readHex : List UInt8 → Nat → Nat × List UInt8
  | [], acc => (acc, [])
  | b :: bs, acc =>
    match hexDigitVal b with
    | some d => readHex bs (acc * 16 + d)
    | none => (acc, b :: bs)

theorem readHex_digits (ds : List Nat) (hds : ∀ d ∈ ds, d < 16) (acc : Nat) (rest : List UInt8) :
    readHex (ds.map hexChar ++ 13 :: rest) acc =
      (ds.foldl (fun a d => a * 16 + d) acc, 13 :: rest) := by
  induction ds generalizing acc with
  | nil => simp [readHex, hexDigitVal]
  | cons d ds ih =>
    simp only [List.map_cons, List.cons_append, readHex,
      hexDigitVal_hexChar d (hds d (by simp)), List.foldl_cons]
    exact ih (fun x hx => hds x (by simp [hx])) _

def CRLF : List UInt8 := [13, 10]

def encodeChunk (c : List UInt8) : List UInt8 := hexBytes c.length ++ CRLF ++ c ++ CRLF

/-- `chunk₁ ‖ … ‖ chunkₙ ‖ "0\r\n\r\n"` -/
def encode (chunks : List (List UInt8)) : List UInt8 :=
  (chunks.map encodeChunk).flatten ++ [48, 13, 10, 13, 10]

/-- Skip to just past the next CRLF (drops chunk extensions). -/
def skipLine : List UInt8 → Option (List UInt8)
  | 13 :: 10 :: rest => some rest
  | _ :: rest => skipLine rest
  | [] => none

def decodeAux : Nat → List UInt8 → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | fuel + 1, l, acc =>
    match l with
    | [] => none
    | b :: _ =>
      if (hexDigitVal b).isNone then none else
      let (n, rest) := readHex l 0
      match skipLine rest with
      | none => none
      | some rest =>
        if n = 0 then some acc else
        match rest.drop n with
        | 13 :: 10 :: rest' => decodeAux fuel rest' (acc ++ rest.take n)
        | _ => none

/-- Decode a chunked body (trailers ignored). -/
def decode (l : List UInt8) : Option (List UInt8) := decodeAux (l.length + 1) l []

theorem hexBytes_ne_nil (n : Nat) : hexBytes n ≠ [] := by
  unfold hexBytes hexDigits; split <;> simp

theorem decodeAux_encode (chunks : List (List UInt8)) (hne : ∀ c ∈ chunks, c ≠ [])
    (fuel : Nat) (hf : chunks.length < fuel) (acc : List UInt8) :
    decodeAux fuel (encode chunks) acc = some (acc ++ chunks.flatten) := by
  induction chunks generalizing fuel acc with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [encode, decodeAux, hexDigitVal, readHex, skipLine]
  | cons c cs ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hc : c ≠ [] := hne c (by simp)
    have hlen : 0 < c.length := List.length_pos_iff.mpr hc
    have hd := hexDigits_lt c.length
    -- the encoded stream starts with hex digits of `c.length`
    obtain ⟨b, bs, hb⟩ : ∃ b bs, hexBytes c.length = b :: bs := by
      cases h : hexBytes c.length with
      | nil => exact absurd h (hexBytes_ne_nil _)
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hfirst : (hexDigitVal b).isSome := by
      have : b ∈ hexBytes c.length := by rw [hb]; simp
      simp only [hexBytes, List.mem_map] at this
      obtain ⟨d, hdm, rfl⟩ := this
      simp [hexDigitVal_hexChar d (hd d hdm)]
    have hstream : encode (c :: cs) =
        (hexDigits c.length).map hexChar ++ 13 :: (10 :: (c ++ 13 :: 10 :: encode cs)) := by
      simp [encode, encodeChunk, hexBytes, CRLF]
    have hread := readHex_digits (hexDigits c.length) hd 0 (10 :: (c ++ 13 :: 10 :: encode cs))
    have hfold : (hexDigits c.length).foldl (fun a d => a * 16 + d) 0 = c.length :=
      fromDigits_hexDigits c.length
    rw [hfold] at hread
    have hdrop : (c ++ 13 :: 10 :: encode cs).drop c.length = 13 :: 10 :: encode cs := by simp
    have htake : (c ++ 13 :: 10 :: encode cs).take c.length = c := by simp
    have hstart : encode (c :: cs) = b :: (bs ++ CRLF ++ c ++ CRLF ++ encode cs) := by
      simp [encode, encodeChunk, hb, CRLF]
    have hnone : (hexDigitVal b).isNone = false := by
      cases h : hexDigitVal b <;> simp_all
    rw [hstart]
    simp only [decodeAux, hnone, Bool.false_eq_true, ite_false]
    rw [← hstart, hstream, hread]
    simp only [skipLine, Nat.ne_of_gt hlen, ite_false, hdrop, htake]
    rw [ih (fun x hx => hne x (by simp [hx])) f (by simp at hf; omega)]
    simp

theorem encode_cons (c : List UInt8) (cs : List (List UInt8)) :
    encode (c :: cs) = encodeChunk c ++ encode cs := by
  simp [encode, List.append_assoc]

theorem length_le_encode (chunks : List (List UInt8)) : chunks.length ≤ (encode chunks).length := by
  induction chunks with
  | nil => simp
  | cons c cs ih =>
    rw [encode_cons]
    simp only [List.length_append, List.length_cons, encodeChunk, CRLF, List.length_nil] at ih ⊢
    omega

/-- **Chunked round-trip**: decoding the encoding of non-empty chunks yields their concatenation. -/
theorem decode_encode (chunks : List (List UInt8)) (hne : ∀ c ∈ chunks, c ≠ []) :
    decode (encode chunks) = some chunks.flatten := by
  unfold decode
  rw [decodeAux_encode chunks hne _ ?_ []]
  · simp
  · have := length_le_encode chunks
    omega

end LeanBrowse.Chunked
