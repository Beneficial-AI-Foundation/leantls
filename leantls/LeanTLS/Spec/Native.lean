import LeanTLS.HKDF
import LeanTLS.AEAD
/-!
# Specs checked by compiled evaluation (`native_decide`)

Multi-block known-answer vectors too heavy for kernel reduction on the VD box.
**Trust note:** `native_decide` trusts Lean's compiler (axiom `Lean.ofReduceBool`), in addition
to the kernel. Run `#print axioms` on any of these to see it.
-/
namespace LeanTLS.Spec
open LeanTLS

/-- RFC 4231 test case 6 (131-byte key: exercises the hash-the-key branch). -/
theorem hmac_rfc4231_6 :
    hmac (mapBytes (fun _ => 0xaa) (zeros 131))
      (ofString "Test Using Larger Than Block-Size Key - Hash Key First") =
    ofHex "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54" := by
  native_decide

/-- RFC 5869 test case 1. -/
theorem hkdf_rfc5869_1 :
    let prk := HKDF.extract (ofHex "000102030405060708090a0b0c")
      (ofHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b")
    prk = ofHex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5" ∧
    HKDF.expand prk (ofHex "f0f1f2f3f4f5f6f7f8f9") 42 =
      ofHex ("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf" ++
             "34007208d5b887185865") := by
  native_decide

def rfc8439Key := ofHex "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
def rfc8439Nonce := ofHex "070000004041424344454647"
def rfc8439Aad := ofHex "50515253c0c1c2c3c4c5c6c7"
def rfc8439Pt := ofString ("Ladies and Gentlemen of the class of '99: If I could offer you " ++
  "only one tip for the future, sunscreen would be it.")

/-- RFC 8439 §2.8.2 AEAD: first ciphertext block and the 16-byte tag. -/
theorem aead_rfc8439 :
    let c := AEAD.sealMsg rfc8439Key rfc8439Nonce rfc8439Aad rfc8439Pt
    c.extract 0 16 = ofHex "d31a8d34648e60db7b86afbc53ef7ec2" ∧
    c.extract 114 130 = ofHex "1ae10b594f09e26a7e902ecbd0600691" := by
  native_decide

/-- RFC 8439 AEAD: flipping one ciphertext bit makes `openMsg` reject. -/
theorem aead_rfc8439_tamper :
    let c := AEAD.sealMsg rfc8439Key rfc8439Nonce rfc8439Aad rfc8439Pt
    AEAD.openMsg rfc8439Key rfc8439Nonce rfc8439Aad (c.set! 0 (c.get! 0 ^^^ 1)) = none := by
  native_decide

end LeanTLS.Spec
