import LeanTLS.ChaCha20
/-!
# Poly1305 and ChaCha20-Poly1305 AEAD (RFC 8439 §2.5–2.8)
-/
namespace LeanTLS

namespace Poly1305

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

end Poly1305

namespace AEAD

def pad16 (b : ByteArray) : ByteArray := zeros ((16 - b.size % 16) % 16)

def macData (aad ct : ByteArray) : ByteArray :=
  aad ++ pad16 aad ++ ct ++ pad16 ct ++ leN 8 aad.size ++ leN 8 ct.size

def tag (key nonce aad ct : ByteArray) : ByteArray :=
  let otk := (ChaCha20.block key 0 nonce).extract 0 32
  Poly1305.mac otk (macData aad ct)

@[simp] theorem tag_size (k n a c : ByteArray) : (tag k n a c).size = 16 := Poly1305.mac_size _ _

/-- Encrypt and authenticate: returns `ciphertext ‖ 16-byte tag`. -/
def sealMsg (key nonce aad pt : ByteArray) : ByteArray :=
  let ct := ChaCha20.encrypt key 1 nonce pt
  ct ++ tag key nonce aad ct

theorem sealMsg_size (k n a m : ByteArray) : (sealMsg k n a m).size = m.size + 16 := by
  simp [sealMsg, ByteArray.size_append]

/-- Verify and decrypt. `none` iff the tag does not match (or input is shorter than a tag). -/
def openMsg (key nonce aad ctt : ByteArray) : Option ByteArray :=
  if ctt.size < 16 then none else
  let ct := ctt.extract 0 (ctt.size - 16)
  let t := ctt.extract (ctt.size - 16) ctt.size
  if ctEq t (tag key nonce aad ct) then some (ChaCha20.encrypt key 1 nonce ct) else none

/-- **Correctness**: opening a sealed message with the same key/nonce/AAD returns it. -/
theorem openMsg_sealMsg (k n a m : ByteArray) : openMsg k n a (sealMsg k n a m) = some m := by
  have hs := sealMsg_size k n a m
  have hct : (sealMsg k n a m).extract 0 (m.size) = ChaCha20.encrypt k 1 n m := by
    simp only [sealMsg]
    exact ByteArray.extract_append_eq_left (by simp)
  have htag : (sealMsg k n a m).extract m.size (m.size + 16) =
      tag k n a (ChaCha20.encrypt k 1 n m) := by
    simp only [sealMsg]
    exact ByteArray.extract_append_eq_right (by simp) (by simp)
  unfold openMsg
  rw [hs, ite_eq_right (by omega), Nat.add_sub_cancel, hct, htag]
  simp [ctEq_self, ChaCha20.encrypt_encrypt]

/-- **Integrity (structural)**: whatever `open` accepts, it accepted because the tag over the
    received ciphertext matched. -/
theorem openMsg_some_tag (k n a c m : ByteArray) (h : openMsg k n a c = some m) :
    16 ≤ c.size ∧
    ctEq (c.extract (c.size - 16) c.size) (tag k n a (c.extract 0 (c.size - 16))) = true := by
  unfold openMsg at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · exact ⟨by omega, by assumption⟩
    · contradiction

end AEAD
end LeanTLS
