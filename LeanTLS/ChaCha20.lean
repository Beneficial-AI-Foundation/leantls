import LeanTLS.Bytes
/-!
# ChaCha20 (RFC 8439 §2.3–2.4)
-/
namespace LeanTLS.ChaCha20

@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

@[inline] def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  (byteAt b i).toUInt32 ||| ((byteAt b (i+1)).toUInt32 <<< 8) |||
  ((byteAt b (i+2)).toUInt32 <<< 16) ||| ((byteAt b (i+3)).toUInt32 <<< 24)

@[inline] def qr (s : Array UInt32) (a b c d : Nat) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 7)
  return s

def initState (key : ByteArray) (counter : UInt32) (nonce : ByteArray) : Array UInt32 :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    le32 key 0, le32 key 4, le32 key 8, le32 key 12,
    le32 key 16, le32 key 20, le32 key 24, le32 key 28,
    counter, le32 nonce 0, le32 nonce 4, le32 nonce 8]

/-- The 64-byte ChaCha20 block function. -/
def block (key : ByteArray) (counter : UInt32) (nonce : ByteArray) : ByteArray :=
  let s0 := initState key counter nonce
  let s := (List.range 10).foldl (fun s _ =>
    let s := qr s 0 4 8 12; let s := qr s 1 5 9 13
    let s := qr s 2 6 10 14; let s := qr s 3 7 11 15
    let s := qr s 0 5 10 15; let s := qr s 1 6 11 12
    let s := qr s 2 7 8 13; qr s 3 4 9 14) s0
  ⟨Array.ofFn (n := 64) fun i =>
    ((s[i.val / 4]! + s0[i.val / 4]!) >>> (8 * (i.val % 4)).toUInt32).toUInt8⟩

@[simp] theorem block_size (k : ByteArray) (c : UInt32) (n : ByteArray) : (block k c n).size = 64 :=
  Array.size_ofFn

/-- Keystream of `nblocks` consecutive blocks starting at `counter`. -/
def keystream (key : ByteArray) (counter : UInt32) (nonce : ByteArray) (nblocks : Nat) : ByteArray :=
  (List.range nblocks).foldl (fun acc j => acc ++ block key (counter + j.toUInt32) nonce) ByteArray.empty

/-- Encryption = XOR with the keystream. Decryption is the same function. -/
def encrypt (key : ByteArray) (counter : UInt32) (nonce : ByteArray) (m : ByteArray) : ByteArray :=
  xorWith m (keystream key counter nonce ((m.size + 63) / 64))

@[simp] theorem encrypt_size (k : ByteArray) (c : UInt32) (n m : ByteArray) :
    (encrypt k c n m).size = m.size := xorWith_size _ _

/-- ChaCha20 decryption inverts encryption, for every key, counter, nonce and message. -/
theorem encrypt_encrypt (k : ByteArray) (c : UInt32) (n m : ByteArray) :
    encrypt k c n (encrypt k c n m) = m := by
  unfold encrypt
  rw [xorWith_size]
  exact xorWith_xorWith _ _

end LeanTLS.ChaCha20
