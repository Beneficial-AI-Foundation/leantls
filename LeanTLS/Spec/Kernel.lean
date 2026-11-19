import LeanTLS.HKDF
import LeanTLS.AEAD
import LeanTLS.X25519
/-!
# Specs checked by the Lean kernel

Known-answer vectors from the RFCs, proved with `decide +kernel`: the kernel itself evaluates
the implementation, so these rely on nothing beyond Lean's kernel (no compiler, no `native_decide`).
Only primitives cheap enough for the kernel on the 3 GB VD box live here; heavier composite
vectors are in `LeanTLS.Spec.Native`.
-/
namespace LeanTLS.Spec
open LeanTLS

/-! ## SHA-256 (FIPS 180-4 examples) -/

theorem sha256_empty :
    SHA256.hash ByteArray.empty =
    ofHex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  decide +kernel

theorem sha256_abc :
    SHA256.hash (ofString "abc") =
    ofHex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel

/-- 56-byte message: padding spills into a second block. -/
theorem sha256_two_block :
    SHA256.hash (ofString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
    ofHex "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  decide +kernel

/-! ## HMAC-SHA256 (RFC 4231) -/

theorem hmac_rfc4231_2 :
    hmac (ofString "Jefe") (ofString "what do ya want for nothing?") =
    ofHex "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843" := by
  decide +kernel

/-! ## ChaCha20 / Poly1305 (RFC 8439) -/

/-- RFC 8439 §2.3.2 block function. -/
theorem chacha20_block_rfc8439 :
    ChaCha20.block (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f") 1
      (ofHex "000000090000004a00000000") =
    ofHex ("10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e" ++
           "d2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e") := by
  decide +kernel

/-- RFC 8439 §2.5.2 Poly1305 tag. -/
theorem poly1305_rfc8439 :
    Poly1305.mac (ofHex "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
      (ofString "Cryptographic Forum Research Group") =
    ofHex "a8061dc1305136c6c22b8baf0c0127a9" := by
  decide +kernel

/-! ## X25519 (RFC 7748) -/

/-- RFC 7748 §5.2, first vector. -/
theorem x25519_rfc7748_1 :
    X25519.x25519 (ofHex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
      (ofHex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c") =
    ofHex "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552" := by
  decide +kernel

def aliceSk := ofHex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
def bobSk   := ofHex "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"

/-- RFC 7748 §6.1: Alice's public key. -/
theorem x25519_alice_pk :
    X25519.publicKey aliceSk =
    ofHex "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a" := by
  decide +kernel

/-- RFC 7748 §6.1: Bob's public key. -/
theorem x25519_bob_pk :
    X25519.publicKey bobSk =
    ofHex "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f" := by
  decide +kernel

/-- RFC 7748 §6.1: both parties derive the same shared secret. -/
theorem x25519_dh_agree :
    X25519.x25519 aliceSk (X25519.publicKey bobSk) =
    X25519.x25519 bobSk (X25519.publicKey aliceSk) := by
  decide +kernel

end LeanTLS.Spec
