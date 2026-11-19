import LeanTLS.SHA256
/-!
# HMAC-SHA256 (RFC 2104) and HKDF (RFC 5869)
-/
namespace LeanTLS

def mapBytes (f : UInt8 → UInt8) (b : ByteArray) : ByteArray := ⟨b.data.map f⟩

def hmac (key msg : ByteArray) : ByteArray :=
  let k := if key.size > 64 then SHA256.hash key else key
  let k := k ++ zeros (64 - k.size)
  SHA256.hash (mapBytes (· ^^^ 0x5c) k ++ SHA256.hash (mapBytes (· ^^^ 0x36) k ++ msg))

@[simp] theorem hmac_size (key msg : ByteArray) : (hmac key msg).size = 32 := by
  simp [hmac]

namespace HKDF

def extract (salt ikm : ByteArray) : ByteArray := hmac salt ikm

/-- Produce `n` more blocks `T(i)`, appending to `acc`. -/
def blocks (prk info : ByteArray) : Nat → Nat → ByteArray → ByteArray → ByteArray
  | 0, _, _, acc => acc
  | n + 1, i, prev, acc =>
    let t := hmac prk (prev ++ info ++ u8 i)
    blocks prk info n (i + 1) t (acc ++ t)

theorem blocks_size (prk info : ByteArray) (n i : Nat) (prev acc : ByteArray) :
    (blocks prk info n i prev acc).size = acc.size + 32 * n := by
  induction n generalizing i prev acc with
  | zero => simp [blocks]
  | succ n ih => simp [blocks, ih, ByteArray.size_append]; omega

def expand (prk info : ByteArray) (len : Nat) : ByteArray :=
  (blocks prk info ((len + 31) / 32) 1 ByteArray.empty ByteArray.empty).extract 0 len

/-- HKDF-Expand returns exactly the requested number of bytes. -/
@[simp] theorem expand_size (prk info : ByteArray) (len : Nat) : (expand prk info len).size = len := by
  simp [expand, blocks_size, ByteArray.size_extract]; omega

end HKDF
end LeanTLS
