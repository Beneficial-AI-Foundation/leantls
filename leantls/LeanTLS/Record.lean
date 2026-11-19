import LeanTLS.AEAD
/-!
# TLS 1.3 record layer (RFC 8446 §5) and handshake framing (§4)

Proved here:
* `parseInner_inner`   — inner-plaintext decoding inverts encoding, for any amount of zero padding
* `openRecord_sealRecord` — a protected record decrypts to exactly the content and type sealed
* `parseHs_hsMsg`      — handshake message framing round-trips, leaving trailing bytes untouched
-/
namespace LeanTLS.Record

/-! ## byte-level helper lemmas -/

theorem byteAt_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    byteAt (a ++ b) i = byteAt a i := by
  have h' : i < (a ++ b).data.size := by
    show i < (a ++ b).size; rw [ByteArray.size_append]; omega
  rw [byteAt_eq _ _ h', byteAt_eq _ _ h]
  simp [ByteArray.data_append, Array.getElem_append_left h]

theorem byteAt_append_right (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) (a.size + i) = byteAt b i := by
  simp only [byteAt_eq_getD, ByteArray.data_append, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_append_right (by simp [ByteArray.size_data])]
  simp [ByteArray.size_data]

theorem byteAt_zeros (n i : Nat) : byteAt (zeros n) i = 0 := by
  unfold zeros
  simp [byteAt_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-! ## inner plaintext: `content ‖ type ‖ 0…0` -/

def single (x : UInt8) : ByteArray := ⟨#[x]⟩

@[simp] theorem single_size (x : UInt8) : (single x).size = 1 := rfl

theorem byteAt_single (x : UInt8) : byteAt (single x) 0 = x := rfl

def inner (content : ByteArray) (ty : UInt8) (padLen : Nat := 0) : ByteArray :=
  content ++ single ty ++ zeros padLen

/-- Index of the last non-zero byte among the first `n`. -/
def lastNZ (b : ByteArray) : Nat → Option Nat
  | 0 => none
  | i + 1 => if byteAt b i ≠ 0 then some i else lastNZ b i

def parseInner (b : ByteArray) : Option (ByteArray × UInt8) :=
  match lastNZ b b.size with
  | none => none
  | some i => some (b.extract 0 i, byteAt b i)

theorem lastNZ_skip_zeros (b : ByteArray) (m k : Nat)
    (hz : ∀ j, j < k → byteAt b (m + j) = 0) : lastNZ b (m + k) = lastNZ b m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [lastNZ, hz k (by omega), ne_eq, not_true_eq_false, ite_false]
    exact ih (fun j hj => hz j (by omega))

/-- **Inner plaintext round-trip** (any non-zero content type, any padding length). -/
theorem parseInner_inner (c : ByteArray) (ty : UInt8) (hty : ty ≠ 0) (k : Nat) :
    parseInner (inner c ty k) = some (c, ty) := by
  have hsz : (inner c ty k).size = (c.size + 1) + k := by
    simp [inner, ByteArray.size_append]
  have hty' : byteAt (inner c ty k) c.size = ty := by
    unfold inner
    rw [byteAt_append_left _ _ _ (by simp [ByteArray.size_append])]
    have := byteAt_append_right c (single ty) 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  have hz : ∀ j, j < k → byteAt (inner c ty k) ((c.size + 1) + j) = 0 := by
    intro j _
    unfold inner
    have h1 : (c ++ single ty).size = c.size + 1 := by simp [ByteArray.size_append]
    rw [← h1, byteAt_append_right, byteAt_zeros]
  unfold parseInner
  rw [hsz, lastNZ_skip_zeros _ _ _ hz]
  simp only [lastNZ, hty', ne_eq, hty, not_false_eq_true, ite_true]
  congr 2
  unfold inner
  rw [ByteArray.append_assoc]
  exact ByteArray.extract_append_eq_left rfl

/-! ## protected records -/

/-- Per-record nonce: `iv XOR be96(seq)` (RFC 8446 §5.3). -/
def nonce (iv : ByteArray) (seq : Nat) : ByteArray := xorWith iv (beN 12 seq)

def header (len : Nat) : ByteArray := u8 23 ++ be16 0x0303 ++ be16 len

@[simp] theorem header_size (n : Nat) : (header n).size = 5 := by
  simp [header, ByteArray.size_append]

/-- Encrypt one record: `header ‖ AEAD(inner)`; the header is the AEAD's associated data. -/
def sealRecord (key iv : ByteArray) (seq : Nat) (ty : UInt8) (content : ByteArray) : ByteArray :=
  let pt := inner content ty
  let hdr := header (pt.size + 16)
  hdr ++ AEAD.sealMsg key (nonce iv seq) hdr pt

/-- Decrypt one record given its 5-byte header and body. -/
def openRecord (key iv : ByteArray) (seq : Nat) (hdr body : ByteArray) : Option (ByteArray × UInt8) :=
  (AEAD.openMsg key (nonce iv seq) hdr body).bind parseInner

/-- **Record round-trip**: splitting a sealed record at the header and opening it with the
    same key, IV and sequence number yields the original content and content type. -/
theorem openRecord_sealRecord (key iv : ByteArray) (seq : Nat) (ty : UInt8) (hty : ty ≠ 0)
    (c : ByteArray) :
    let r := sealRecord key iv seq ty c
    openRecord key iv seq (r.extract 0 5) (r.extract 5 r.size) = some (c, ty) := by
  simp only [sealRecord]
  rw [ByteArray.extract_append_eq_left (by simp),
      ByteArray.extract_append_eq_right (by simp) (by simp [ByteArray.size_append])]
  simp only [openRecord, AEAD.openMsg_sealMsg, Option.bind_some]
  exact parseInner_inner c ty hty 0

/-! ## handshake framing: `type ‖ be24 len ‖ body` -/

def hsMsg (ty : Nat) (body : ByteArray) : ByteArray := u8 ty ++ be24 body.size ++ body

/-- Split one complete handshake message off the front of `buf`:
    `(type, body, rest)`, or `none` if `buf` does not yet hold a whole message. -/
def parseHs (buf : ByteArray) : Option (Nat × ByteArray × ByteArray) :=
  if buf.size < 4 then none else
  let len := rd24 buf 1
  if buf.size < 4 + len then none else
  some (rd8 buf 0, buf.extract 4 (4 + len), buf.extract (4 + len) buf.size)

theorem byteAt_append_ge (a b : ByteArray) (j : Nat) (h : a.size ≤ j) :
    byteAt (a ++ b) j = byteAt b (j - a.size) := by
  have := byteAt_append_right a b (j - a.size)
  rwa [Nat.add_sub_cancel' h] at this

theorem rd8_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    rd8 (a ++ b) i = rd8 a i := by
  simp [rd8, byteAt_append_left a b i h]

/-- **Handshake framing round-trip.** -/
theorem parseHs_hsMsg (ty : Nat) (hty : ty < 256) (body rest : ByteArray)
    (hlen : body.size < 16777216) :
    parseHs (hsMsg ty body ++ rest) = some (ty, body, rest) := by
  have hhdr : (u8 ty ++ be24 body.size).size = 4 := by simp [ByteArray.size_append]
  have hsz : (hsMsg ty body ++ rest).size = 4 + body.size + rest.size := by
    simp [hsMsg, ByteArray.size_append]
  have hlen' : rd24 (hsMsg ty body ++ rest) 1 = body.size := by
    have target := rd24_be24 _ hlen
    simp only [rd24, rd8, hsMsg, ByteArray.append_assoc] at target ⊢
    rw [byteAt_append_ge _ _ 1 (by simp), byteAt_append_ge _ _ 2 (by simp),
      byteAt_append_ge _ _ 3 (by simp)]
    simp only [u8_size]
    rw [byteAt_append_left _ _ 0 (by simp), byteAt_append_left _ _ 1 (by simp),
      byteAt_append_left _ _ 2 (by simp)]
    exact target
  have hty' : rd8 (hsMsg ty body ++ rest) 0 = ty := by
    simp only [hsMsg]
    rw [ByteArray.append_assoc, ByteArray.append_assoc, rd8_append_left _ _ 0 (by simp)]
    exact rd8_u8 ty hty
  unfold parseHs
  rw [hsz, hlen', ite_eq_right (by omega), ite_eq_right (by omega), hty']
  have hb : (hsMsg ty body ++ rest).extract 4 (4 + body.size) = body := by
    simp only [hsMsg]
    have := ByteArray.extract_append_size_add' (a := u8 ty ++ be24 body.size) (b := body ++ rest)
      (i := 0) (j := body.size) hhdr.symm
    rw [Nat.add_zero] at this
    rw [ByteArray.append_assoc, this]
    exact ByteArray.extract_append_eq_left rfl
  have hr : (hsMsg ty body ++ rest).extract (4 + body.size) (4 + body.size + rest.size) = rest :=
    ByteArray.extract_append_eq_right (by simp [hsMsg, ByteArray.size_append])
      (by simp [hsMsg, ByteArray.size_append])
  rw [hb, hr]

end LeanTLS.Record
