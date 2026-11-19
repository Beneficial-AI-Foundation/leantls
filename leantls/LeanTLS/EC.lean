import LeanTLS.RSA
import LeanTLS.ASN1
/-!
# NIST P-256 / P-384: point arithmetic, ECDSA verification, P-256 ECDH

Short Weierstrass curves `y² = x³ + a·x + b` over `Nat` mod p, Jacobian coordinates.
**Not constant-time.** Verification only handles public data; the ECDH secret is ephemeral.
The curve constants are checked by specs (`LeanTLS.Spec.Kernel`): the base point is on the
curve and `n · G = ∞`.
-/
namespace LeanTLS.EC

structure Curve where
  p : Nat
  a : Nat
  b : Nat
  n : Nat
  gx : Nat
  gy : Nat
  /-- Field element length in bytes. -/
  len : Nat
  deriving Repr

def P256 : Curve where
  p := 2^256 - 2^224 + 2^192 + 2^96 - 1
  a := 2^256 - 2^224 + 2^192 + 2^96 - 1 - 3
  b := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  n := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  gx := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  gy := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  len := 32

def P384 : Curve where
  p := 2^384 - 2^128 - 2^96 + 2^32 - 1
  a := 2^384 - 2^128 - 2^96 + 2^32 - 1 - 3
  b := 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
  n := 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
  gx := 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
  gy := 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
  len := 48

namespace Curve
variable (c : Curve)

@[inline] def add' (x y : Nat) : Nat := (x + y) % c.p
@[inline] def sub' (x y : Nat) : Nat := (x + c.p - y % c.p) % c.p
@[inline] def mul' (x y : Nat) : Nat := x * y % c.p
def inv (x : Nat) : Nat := RSA.powMod x (c.p - 2) c.p

def onCurve (x y : Nat) : Bool :=
  x < c.p && y < c.p && c.mul' y y == c.add' (c.add' (c.mul' x (c.mul' x x)) (c.mul' c.a x)) c.b

/-- Jacobian point `(X, Y, Z)`; `Z = 0` is the point at infinity. -/
abbrev Jac := Nat × Nat × Nat

def infinity : Jac := (1, 1, 0)

def double : Jac → Jac
  | (x, y, z) =>
    if z == 0 || y == 0 then infinity else
    let xx := c.mul' x x; let yy := c.mul' y y; let yyyy := c.mul' yy yy; let zz := c.mul' z z
    let s := c.mul' 4 (c.mul' x yy)
    let m := c.add' (c.mul' 3 xx) (c.mul' c.a (c.mul' zz zz))
    let x3 := c.sub' (c.mul' m m) (c.mul' 2 s)
    let y3 := c.sub' (c.mul' m (c.sub' s x3)) (c.mul' 8 yyyy)
    (x3, y3, c.mul' 2 (c.mul' y z))

def add : Jac → Jac → Jac
  | (x1, y1, z1), (x2, y2, z2) =>
    if z1 == 0 then (x2, y2, z2) else if z2 == 0 then (x1, y1, z1) else
    let z1z1 := c.mul' z1 z1; let z2z2 := c.mul' z2 z2
    let u1 := c.mul' x1 z2z2; let u2 := c.mul' x2 z1z1
    let s1 := c.mul' y1 (c.mul' z2 z2z2); let s2 := c.mul' y2 (c.mul' z1 z1z1)
    if u1 == u2 then (if s1 == s2 then c.double (x1, y1, z1) else infinity) else
    let h := c.sub' u2 u1; let r := c.sub' s2 s1
    let hh := c.mul' h h; let hhh := c.mul' h hh
    let x3 := c.sub' (c.sub' (c.mul' r r) hhh) (c.mul' 2 (c.mul' u1 hh))
    let y3 := c.sub' (c.mul' r (c.sub' (c.mul' u1 hh) x3)) (c.mul' s1 hhh)
    (x3, y3, c.mul' h (c.mul' z1 z2))

/-- `k · P`, double-and-add from the top bit. -/
def smul (k : Nat) (pt : Jac) : Jac :=
  (List.range (Nat.log2 k + 1)).reverse.foldl (fun acc t =>
    let acc := c.double acc
    if k.testBit t then c.add acc pt else acc) infinity

def toAffine : Jac → Option (Nat × Nat)
  | (x, y, z) =>
    if z % c.p == 0 then none else
    let zi := c.inv z; let zi2 := c.mul' zi zi
    some (c.mul' x zi2, c.mul' y (c.mul' zi2 zi))

def G : Jac := (c.gx, c.gy, 1)

/-- SEC1 uncompressed point `04 ‖ X ‖ Y`, validated to lie on the curve. -/
def decodePoint (b : ByteArray) : Option Jac :=
  if b.size != 2 * c.len + 1 || byteAt b 0 != 4 then none else
  let x := decodeBE (b.extract 1 (1 + c.len))
  let y := decodeBE (b.extract (1 + c.len) (1 + 2 * c.len))
  if c.onCurve x y then some (x, y, 1) else none

def encodePoint (x y : Nat) : ByteArray := u8 4 ++ beN c.len x ++ beN c.len y

/-- ECDSA verification (SEC1 §4.1.4) on a message digest. -/
def ecdsaVerify (q : Jac) (digest : ByteArray) (r s : Nat) : Bool :=
  if r == 0 || s == 0 || r ≥ c.n || s ≥ c.n then false else
  let nBits := Nat.log2 c.n + 1
  let e := decodeBE digest
  let e := if 8 * digest.size > nBits then e >>> (8 * digest.size - nBits) else e
  let w := RSA.powMod s (c.n - 2) c.n
  let u1 := e * w % c.n
  let u2 := r * w % c.n
  match c.toAffine (c.add (c.smul u1 c.G) (c.smul u2 q)) with
  | none => false
  | some (x, _) => x % c.n == r

end Curve

/-- DER `ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }`. -/
def parseSig (b : ByteArray) : Option (Nat × Nat) := do
  let t ← ASN1.tlv b 0
  if t.tag != ASN1.TAG_SEQUENCE || t.stop != b.size then none
  match ASN1.children b t with
  | [r, s] =>
    if r.tag != ASN1.TAG_INTEGER || s.tag != ASN1.TAG_INTEGER then none
    else some (ASN1.natOf b r, ASN1.natOf b s)
  | _ => none

/-- Verify a DER-encoded ECDSA signature over `msg` with hash `h`. -/
def verifyDer (c : Curve) (pub : ByteArray) (h : RSA.Hash) (msg sig : ByteArray) : Bool :=
  match c.decodePoint pub, parseSig sig with
  | some q, some (r, s) => c.ecdsaVerify q (h.digest msg) r s
  | _, _ => false

/-! ## P-256 ECDH (for key_share `secp256r1`) -/

/-- Derive a scalar in `[1, n-1]` from 32 random bytes, and the public point. -/
def p256Keygen (rnd : ByteArray) : Nat × ByteArray :=
  let d := decodeBE rnd % (P256.n - 1) + 1
  match P256.toAffine (P256.smul d P256.G) with
  | some (x, y) => (d, P256.encodePoint x y)
  | none => (d, ByteArray.empty)

/-- Shared secret: the x-coordinate of `d · Q` (32 bytes), after validating `Q`. -/
def p256Shared (d : Nat) (peer : ByteArray) : Option ByteArray := do
  let q ← P256.decodePoint peer
  let (x, _) ← P256.toAffine (P256.smul d q)
  pure (beN 32 x)

end LeanTLS.EC
