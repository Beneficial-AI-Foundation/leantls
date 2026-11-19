import LeanTLS.Bytes
/-!
# X25519 (RFC 7748 §5)

Field arithmetic over `Nat` (GMP-backed at runtime). Note: this is *not* constant-time.
-/
namespace LeanTLS.X25519

def p : Nat := 2 ^ 255 - 19
def a24 : Nat := 121665

@[inline] def fadd (a b : Nat) : Nat := (a + b) % p
@[inline] def fsub (a b : Nat) : Nat := (a + p - b % p) % p
@[inline] def fmul (a b : Nat) : Nat := a * b % p

/-- `b ^ e mod m` by square-and-multiply over the low `bits` bits of `e`. -/
def powMod (b e m : Nat) (bits : Nat := 256) : Nat :=
  (List.range bits).reverse.foldl (fun r t =>
    let r := r * r % m
    if e.testBit t then r * b % m else r) (1 % m)

def finv (a : Nat) : Nat := powMod a (p - 2) p

/-- Scalar decoding with clamping, stated arithmetically:
    clear the 3 low bits, clear bit 255, set bit 254. -/
def clamp (n : Nat) : Nat := 2 ^ 254 + (n % 2 ^ 254) / 8 * 8

def decodeScalar (k : ByteArray) : Nat := clamp (decodeLE (k.extract 0 32))

/-- u-coordinate decoding: mask bit 255, reduce mod p. -/
def decodeU (u : ByteArray) : Nat := decodeLE (u.extract 0 32) % 2 ^ 255 % p

def encodeU (x : Nat) : ByteArray := leN 32 (x % p)

theorem clamp_mul8 (n : Nat) : clamp n % 8 = 0 := by
  unfold clamp; omega

theorem clamp_range (n : Nat) : 2 ^ 254 ≤ clamp n ∧ clamp n < 2 ^ 255 := by
  unfold clamp
  have h := Nat.mod_lt n (show 2 ^ 254 > 0 by decide)
  constructor <;> omega

@[inline] def cswap (swap : Bool) (a b : Nat) : Nat × Nat := if swap then (b, a) else (a, b)

/-- Montgomery ladder (RFC 7748 §5), returning projective `(X, Z)`. -/
def ladderXZ (k u : Nat) : Nat × Nat :=
  let x1 := u
  let st := (List.range 255).reverse.foldl (fun (st : Nat × Nat × Nat × Nat × Bool) t =>
    let (x2, z2, x3, z3, swap) := st
    let kt := k.testBit t
    let sw := swap ^^ kt
    let (x2, x3) := cswap sw x2 x3
    let (z2, z3) := cswap sw z2 z3
    let A := fadd x2 z2; let AA := fmul A A
    let B := fsub x2 z2; let BB := fmul B B
    let E := fsub AA BB
    let C := fadd x3 z3; let D := fsub x3 z3
    let DA := fmul D A; let CB := fmul C B
    let x3 := fmul (fadd DA CB) (fadd DA CB)
    let z3 := fmul x1 (fmul (fsub DA CB) (fsub DA CB))
    let x2 := fmul AA BB
    let z2 := fmul E (fadd AA (fmul a24 E))
    (x2, z2, x3, z3, kt)) (1, 0, u, 1, false)
  let (x2, z2, x3, z3, swap) := st
  let (x2, _) := cswap swap x2 x3
  let (z2, _) := cswap swap z2 z3
  (x2, z2)

def ladder (k u : Nat) : Nat :=
  let r := ladderXZ k u
  fmul r.1 (finv r.2)

/-- `X25519(k, u)`: 32-byte scalar, 32-byte u-coordinate → 32-byte shared value. -/
def x25519 (k u : ByteArray) : ByteArray := encodeU (ladder (decodeScalar k) (decodeU u))

def basepoint : ByteArray := leN 32 9

def publicKey (sk : ByteArray) : ByteArray := x25519 sk basepoint

@[simp] theorem x25519_size (k u : ByteArray) : (x25519 k u).size = 32 := leN_size _ _

/-- The ladder's output is always a reduced field element. -/
theorem ladder_lt (k u : Nat) : ladder k u < p := by
  unfold ladder fmul
  exact Nat.mod_lt _ (by decide)

end LeanTLS.X25519
