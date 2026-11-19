import LeanTLS.Bytes
/-!
# SHA-256 (FIPS 180-4)
-/
namespace LeanTLS.SHA256

def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Number of zero bytes so that `len + 1 + z + 8 ≡ 0 (mod 64)`. -/
def padZeros (len : Nat) : Nat := (119 - len % 64) % 64

/-- Message padding: `m ‖ 0x80 ‖ 0…0 ‖ be64(bitlen)`. -/
def pad (m : ByteArray) : ByteArray :=
  m ++ u8 0x80 ++ zeros (padZeros m.size) ++ beN 8 (m.size * 8)

theorem pad_size (m : ByteArray) : (pad m).size = m.size + 1 + padZeros m.size + 8 := by
  simp [pad, ByteArray.size_append]

/-- Padding always yields whole 64-byte blocks. -/
theorem pad_size_mod (m : ByteArray) : (pad m).size % 64 = 0 := by
  rw [pad_size]; unfold padZeros; omega

/-- Padding keeps the message as a prefix. -/
theorem pad_prefix (m : ByteArray) : (pad m).extract 0 m.size = m := by
  simp [pad, ByteArray.append_assoc, ByteArray.extract_append_eq_left]

@[inline] def word (b : ByteArray) (i : Nat) : UInt32 :=
  ((byteAt b i).toUInt32 <<< 24) ||| ((byteAt b (i+1)).toUInt32 <<< 16) |||
  ((byteAt b (i+2)).toUInt32 <<< 8) ||| (byteAt b (i+3)).toUInt32

/-- One compression of the 64-byte block at offset `off`. -/
def compress (h : Array UInt32) (blk : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for t in [0:16] do
    w := w.set! t (word blk (off + 4 * t))
  for t in [16:64] do
    let s0 := rotr w[t-15]! 7 ^^^ rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
    let s1 := rotr w[t-2]! 17 ^^^ rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
    w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for t in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + S1 + ch + K[t]! + w[t]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- Serialize the 8-word state big-endian. -/
def digestBytes (h : Array UInt32) : ByteArray :=
  ⟨Array.ofFn (n := 32) fun i => (h[i.val / 4]! >>> (8 * (3 - (i.val % 4))).toUInt32).toUInt8⟩

def hash (m : ByteArray) : ByteArray :=
  let p := pad m
  let n := p.size / 64
  digestBytes <| (List.range n).foldl (fun h k => compress h p (64 * k)) H0

/-- SHA-256 output is always 32 bytes. -/
@[simp] theorem digestBytes_size (h : Array UInt32) : (digestBytes h).size = 32 :=
  Array.size_ofFn

@[simp] theorem hash_size (m : ByteArray) : (hash m).size = 32 := digestBytes_size _

end LeanTLS.SHA256
