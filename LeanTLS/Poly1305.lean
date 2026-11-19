import LeanTLS.Bytes
/-!
# Poly1305 (RFC 8439 §2.5): specification, fast implementation, and their equality

`mac` is the specification: arbitrary-precision arithmetic modulo `2^130 - 5`, one 16-byte block
at a time. It is slow because every block becomes a bignum (`decodeLE`) and every step is a bignum
multiplication and division.

`macFast` keeps the accumulator as five limbs of 26 bits ("poly1305-donna"), reads each block's
bytes directly, and folds the weight-`2^130` terms back with `2^130 ≡ 5`. All values stay below
`2^63`, so the compiled code works on unboxed machine integers; about 50x faster.

`macFast_eq` proves the two equal for every key and message. The `@[csimp]` lemma `mac_eq_macFast`
makes the compiler run `macFast` wherever `mac` is called, while every definition and theorem keeps
talking about the simple `mac`.
-/
namespace LeanTLS.Poly1305


def p : Nat := 2 ^ 130 - 5

def clampR (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- One-time authenticator. `key` is 32 bytes `r ‖ s`. -/
def mac (key msg : ByteArray) : ByteArray :=
  let r := clampR (decodeLE (key.extract 0 16))
  let s := decodeLE (key.extract 16 32)
  let nblk := (msg.size + 15) / 16
  let acc := (List.range nblk).foldl (fun acc i =>
    let chunk := msg.extract (16 * i) (16 * i + 16)
    let n := decodeLE chunk + 2 ^ (8 * chunk.size)
    (acc + n) * r % p) 0
  leN 16 (acc + s)

@[simp] theorem mac_size (k m : ByteArray) : (mac k m).size = 16 := leN_size _ _



/-- Five limbs, `h0 + h1·2^26 + h2·2^52 + h3·2^78 + h4·2^104`. -/
structure Limbs where
  h0 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat

def Limbs.val (l : Limbs) : Nat := l.h0 + l.h1 * 2^26 + l.h2 * 2^52 + l.h3 * 2^78 + l.h4 * 2^104

def limbsOf (x : Nat) : Limbs :=
  ⟨x % 2^26, x / 2^26 % 2^26, x / 2^52 % 2^26, x / 2^78 % 2^26, x / 2^104⟩

/-- The 16 bytes at `o` plus the `2^128` marker bit, as limbs, read byte by byte. -/
@[inline] def blockLimbs (m : ByteArray) (o : Nat) : Limbs :=
  let b0 := rd8 m o; let b1 := rd8 m (o + 1); let b2 := rd8 m (o + 2); let b3 := rd8 m (o + 3)
  let b4 := rd8 m (o + 4); let b5 := rd8 m (o + 5); let b6 := rd8 m (o + 6); let b7 := rd8 m (o + 7)
  let b8 := rd8 m (o + 8); let b9 := rd8 m (o + 9); let b10 := rd8 m (o + 10); let b11 := rd8 m (o + 11)
  let b12 := rd8 m (o + 12); let b13 := rd8 m (o + 13); let b14 := rd8 m (o + 14); let b15 := rd8 m (o + 15)
  ⟨b0 + b1 * 2^8 + b2 * 2^16 + b3 % 4 * 2^24,
   b3 / 4 + b4 * 2^6 + b5 * 2^14 + b6 % 16 * 2^22,
   b6 / 16 + b7 * 2^4 + b8 * 2^12 + b9 % 64 * 2^20,
   b9 / 64 + b10 * 2^2 + b11 * 2^10 + b12 * 2^18,
   b13 + b14 * 2^8 + b15 * 2^16 + 2^24⟩

/-- Limb-wise sum (no carries needed: limbs are `Nat`). -/
@[inline] def addLimbs (a b : Limbs) : Limbs :=
  ⟨a.h0 + b.h0, a.h1 + b.h1, a.h2 + b.h2, a.h3 + b.h3, a.h4 + b.h4⟩

/-- Product modulo `2^130 - 5` before carrying: terms of weight `2^130` and above fold back with
factor 5. -/
@[inline] def mulLimbs (h r : Limbs) : Limbs :=
  let s1 := r.h1 * 5; let s2 := r.h2 * 5; let s3 := r.h3 * 5; let s4 := r.h4 * 5
  ⟨h.h0 * r.h0 + h.h1 * s4 + h.h2 * s3 + h.h3 * s2 + h.h4 * s1,
   h.h0 * r.h1 + h.h1 * r.h0 + h.h2 * s4 + h.h3 * s3 + h.h4 * s2,
   h.h0 * r.h2 + h.h1 * r.h1 + h.h2 * r.h0 + h.h3 * s4 + h.h4 * s3,
   h.h0 * r.h3 + h.h1 * r.h2 + h.h2 * r.h1 + h.h3 * r.h0 + h.h4 * s4,
   h.h0 * r.h4 + h.h1 * r.h3 + h.h2 * r.h2 + h.h3 * r.h1 + h.h4 * r.h0⟩

/-- Carry each limb into the next; the carry out of the top limb re-enters with factor 5. -/
@[inline] def carry (d : Limbs) : Limbs :=
  let c := d.h0 / 2^26; let h0 := d.h0 % 2^26
  let d1 := d.h1 + c; let c := d1 / 2^26; let h1 := d1 % 2^26
  let d2 := d.h2 + c; let c := d2 / 2^26; let h2 := d2 % 2^26
  let d3 := d.h3 + c; let c := d3 / 2^26; let h3 := d3 % 2^26
  let d4 := d.h4 + c; let c := d4 / 2^26; let h4 := d4 % 2^26
  let h0 := h0 + c * 5; let c := h0 / 2^26; let h0 := h0 % 2^26
  ⟨h0, h1 + c, h2, h3, h4⟩

/-- One block: `h ← (h + n) · r` modulo `2^130 - 5` (up to a multiple of it). -/
@[inline] def step (r h n : Limbs) : Limbs := carry (mulLimbs (addLimbs h n) r)

/-- Poly1305 with limbs. Equal to `mac` for every key and message (`macFast_eq`). -/
def macFast (key msg : ByteArray) : ByteArray :=
  let r := clampR (decodeLE (key.extract 0 16))
  let s := decodeLE (key.extract 16 32)
  let rl := limbsOf r
  let full := msg.size / 16
  let h := (List.range full).foldl (fun h i => step rl h (blockLimbs msg (16 * i))) ⟨0, 0, 0, 0, 0⟩
  let acc := h.val % p
  let acc := if msg.size % 16 = 0 then acc else
    let chunk := msg.extract (16 * full) (16 * full + 16)
    (acc + (decodeLE chunk + 2 ^ (8 * chunk.size))) * r % p
  leN 16 (acc + s)


/-! ## Proof that `macFast = mac` -/

theorem limbsOf_val (x : Nat) : (limbsOf x).val = x := by
  simp only [limbsOf, Limbs.val]; omega

theorem addLimbs_val (a b : Limbs) : (addLimbs a b).val = a.val + b.val := by
  simp only [addLimbs, Limbs.val]; omega

/-- The schoolbook product of the limb polynomials, with `2^130 = p + 5`. -/
theorem mulLimbs_val (h r : Limbs) :
    h.val * r.val = (mulLimbs h r).val +
      p * (h.h1 * r.h4 + h.h2 * r.h3 + h.h3 * r.h2 + h.h4 * r.h1 +
        (h.h2 * r.h4 + h.h3 * r.h3 + h.h4 * r.h2) * 2^26 +
        (h.h3 * r.h4 + h.h4 * r.h3) * 2^52 + h.h4 * r.h4 * 2^78) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h
  obtain ⟨b0, b1, b2, b3, b4⟩ := r
  simp only [mulLimbs, Limbs.val, p]
  grind

/-- Carrying changes the value by a multiple of `p` only. -/
theorem carry_val (d : Limbs) : ∃ c, (carry d).val + p * c = d.val := by
  obtain ⟨d0, d1, d2, d3, d4⟩ := d
  simp only [carry, Limbs.val, p]
  exact ⟨((d4 + (d3 + (d2 + (d1 + d0 / 2^26) / 2^26) / 2^26) / 2^26) / 2^26), by omega⟩

theorem step_mod (r h n : Limbs) : (step r h n).val % p = ((h.val + n.val) * r.val) % p := by
  obtain ⟨c, hc⟩ := carry_val (mulLimbs (addLimbs h n) r)
  have hm := mulLimbs_val (addLimbs h n) r
  rw [addLimbs_val] at hm
  simp only [step]
  rw [hm, ← hc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]

/-- `decodeLE` of a concatenation. -/
theorem foldr_le_init (l : List UInt8) (c : Nat) :
    l.foldr (fun x acc => x.toNat + 256 * acc) c =
      l.foldr (fun x acc => x.toNat + 256 * acc) 0 + 256 ^ l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, List.length_cons, ih, Nat.pow_succ]
    grind

theorem decodeLE_append (a b : ByteArray) :
    decodeLE (a ++ b) = decodeLE a + 256 ^ a.size * decodeLE b := by
  simp only [decodeLE, ByteArray.data_append, Array.foldr_append]
  rw [← Array.foldr_toList (xs := a.data), foldr_le_init, Array.foldr_toList, Array.length_toList]
  rfl

theorem decodeLE_extract_one (b : ByteArray) (i : Nat) (h : i + 1 ≤ b.size) :
    decodeLE (b.extract i (i + 1)) = rd8 b i := by
  rw [ByteArray.extract_add_one h]
  simp [decodeLE, rd8, byteAt, show i < b.size by omega, List.toByteArray, List.toByteArray.loop,
    ByteArray.push]

/-- `n` bytes from `o`, little-endian, read one at a time. -/
def leBytes (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rd8 b o + 256 * leBytes b (o + 1) n

theorem decodeLE_extract (b : ByteArray) : ∀ (n o : Nat), o + n ≤ b.size →
    decodeLE (b.extract o (o + n)) = leBytes b o n
  | 0, o, _ => by simp [leBytes, decodeLE, ByteArray.extract_same]
  | n + 1, o, h => by
    rw [ByteArray.extract_eq_extract_append_extract (o + 1) (by omega) (by omega), decodeLE_append,
      decodeLE_extract_one b o (by omega), ByteArray.size_extract,
      show o + (n + 1) = (o + 1) + n by omega, decodeLE_extract b n (o + 1) (by omega)]
    simp only [leBytes]
    rw [show min (o + 1) b.size - o = 1 by omega]

theorem rd8_lt (b : ByteArray) (i : Nat) : rd8 b i < 256 := (byteAt b i).toNat_lt

theorem blockLimbs_val (m : ByteArray) (o : Nat) :
    (blockLimbs m o).val = leBytes m o 16 + 2 ^ 128 := by
  simp only [blockLimbs, Limbs.val, leBytes, Nat.add_assoc, Nat.reduceAdd]
  have := rd8_lt m o; have := rd8_lt m (o + 1); have := rd8_lt m (o + 2); have := rd8_lt m (o + 3)
  have := rd8_lt m (o + 4); have := rd8_lt m (o + 5); have := rd8_lt m (o + 6); have := rd8_lt m (o + 7)
  have := rd8_lt m (o + 8); have := rd8_lt m (o + 9); have := rd8_lt m (o + 10); have := rd8_lt m (o + 11)
  have := rd8_lt m (o + 12); have := rd8_lt m (o + 13); have := rd8_lt m (o + 14); have := rd8_lt m (o + 15)
  omega

/-- The spec's per-block step. -/
def specStep (msg : ByteArray) (r : Nat) (acc i : Nat) : Nat :=
  let chunk := msg.extract (16 * i) (16 * i + 16)
  (acc + (decodeLE chunk + 2 ^ (8 * chunk.size))) * r % p

theorem fold_full (msg : ByteArray) (r : Nat) (hr : r < 2 ^ 130) :
    ∀ k, k ≤ msg.size / 16 →
      (List.range k).foldl (specStep msg r) 0 =
        ((List.range k).foldl (fun h i => step (limbsOf r) h (blockLimbs msg (16 * i)))
          ⟨0, 0, 0, 0, 0⟩).val % p
  | 0, _ => by simp [Limbs.val]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, fold_full msg r hr k (by omega), step_mod, limbsOf_val,
      blockLimbs_val]
    have hb : 16 * k + 16 ≤ msg.size := by omega
    simp only [specStep]
    rw [ByteArray.size_extract, show min (16 * k + 16) msg.size - 16 * k = 16 by omega,
      show 16 * k + 16 = 16 * k + 16 from rfl, decodeLE_extract msg 16 (16 * k) hb]
    simp [Nat.add_mod, Nat.mul_mod]

theorem clampR_lt (x : Nat) : clampR x < 2 ^ 130 := by
  unfold clampR
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- **The fast implementation computes exactly the specification**, for every key and message. -/
theorem macFast_eq (key msg : ByteArray) : macFast key msg = mac key msg := by
  unfold macFast mac
  simp only
  generalize hr : clampR (decodeLE (key.extract 0 16)) = r
  have hrlt : r < 2 ^ 130 := hr ▸ clampR_lt _
  have hfold := fold_full msg r hrlt (msg.size / 16) (Nat.le_refl _)
  congr 2
  by_cases hz : msg.size % 16 = 0
  · simp only [hz, ↓reduceIte]
    rw [← hfold, show (msg.size + 15) / 16 = msg.size / 16 by omega]
    rfl
  · simp only [hz, ↓reduceIte]
    rw [show (msg.size + 15) / 16 = msg.size / 16 + 1 by omega, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    change _ = specStep msg r _ _
    rw [show (List.foldl (fun acc i => let chunk := msg.extract (16 * i) (16 * i + 16);
        (acc + (decodeLE chunk + 2 ^ (8 * chunk.size))) * r % p) 0 (List.range (msg.size / 16))) =
        (List.range (msg.size / 16)).foldl (specStep msg r) 0 from rfl, hfold]
    simp only [specStep]


/-- Compile `mac` as `macFast` (justified by `macFast_eq`). -/
@[csimp] theorem mac_eq_macFast : @mac = @macFast := by
  funext key msg
  exact (macFast_eq key msg).symm

end LeanTLS.Poly1305
