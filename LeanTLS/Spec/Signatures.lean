import LeanTLS.EC
/-!
# Specs: signature verification

* Curve constants: the base points lie on P-256 / P-384 and have order `n`.
* ECDSA and RSA vectors produced by an independent implementation (OpenSSL 3.6,
  `openssl dgst -sign`), plus tampered-message rejections.
-/
namespace LeanTLS.Spec.Signatures
open LeanTLS LeanTLS.EC

/-! ## curve constants -/

theorem p256_base_on_curve : P256.onCurve P256.gx P256.gy = true := by decide +kernel
theorem p384_base_on_curve : P384.onCurve P384.gx P384.gy = true := by decide +kernel

/-- `n · G = ∞`: `n` is the order of the P-256 base point. -/
theorem p256_order : (P256.smul P256.n P256.G).2.2 % P256.p = 0 := by native_decide
theorem p384_order : (P384.smul P384.n P384.G).2.2 % P384.p = 0 := by native_decide

def msg : ByteArray := ofHex "4c65616e544c53207369676e617475726520766563746f72"
def badMsg : ByteArray := msg ++ ofString "!"

def p256_pub : ByteArray :=
  ofHex ("042c71449b3fa4328caede599fefa42d2c304dfbd0a91ffe0f522b15fbf9978c" ++
    "59653061bc3e7d997e26a2109a357e7f28632d40b71dfb429362baec62db53d7" ++
    "71")

def p256_sig : ByteArray :=
  ofHex ("3046022100b949761db4ae12c5baec239a95b4d3c420fc0521b1b6d298bd1882" ++
    "bd396b05d1022100ed6ce5aa6044fccd1acfad1ddcfd3c8a8f17330bab4544e5" ++
    "397599c27b752568")

def p384_pub : ByteArray :=
  ofHex ("042643ed2974a2ca59bad8f9e11426d47ad8c8644a5a35daeba52bffd452d3fb" ++
    "a51e4594759850a8827e21bc2c4d6d65522591c7fa191a64cd9873c79551c4cb" ++
    "3a3a980d0e2c9913238c6a0960a3d118eea8997a04794ba4201802e17e87a4bc" ++
    "e5")

def p384_sig : ByteArray :=
  ofHex ("3064023067cfcd1e4994932304191e5102aacf093258efa01744134dc0900a1e" ++
    "3f7c68302f93a7f033b2ed11648e2694d40cfe7f023018c0e10cd107c1980b9d" ++
    "1492bf336a5cf9f8fb107c6db09ab7a9154f0db071ec4055a5bfeedb8dd6bc1d" ++
    "e69b5a6c8cd9")

def rsa_pkcs1_sig : ByteArray :=
  ofHex ("66d24a37c8c70832072cb07f2cd6f0989dcf354b620a0a4251f405cb0c69b562" ++
    "6e3d8720ecfba0fa6403d9807bba084b9189f81a3bc03b91c7711e0c724662eb" ++
    "859e401487c237bfd1c1a9713f55dffffafaaae02d16afe634988fa19a781430" ++
    "844210d12f3e1432d0f18f9b62cac0269871a77b142e3f4ffd587604d5f11505" ++
    "33fc25e990981f5861129162242e5cbd2e557b726e3074b1f0dd507f13aa7868" ++
    "e152856447cd27eacb74d4b5903ca5f8df7375b6764dd6d5ef05df9f04350898" ++
    "4371beb816c08e1234c29ae637675dd048ac6bf8b3d367d22c0b39b51f728386" ++
    "bd1f84564b6a62de278e94904f9900da61519768affecbbd3b23229c4d368da5")

def rsa_pss384_sig : ByteArray :=
  ofHex ("135c34effd2af56191ffd02352b7b4e7f3433134c4312bd55af6e329ba92a345" ++
    "311c1981ad8bbe856b1af0f8f29ee266f093ddabca3384b229d5793074c1f1b2" ++
    "cd16bbb76af3f49fa438338c6de77d21694a95164a750e5c34ad0ba5a8b7ca70" ++
    "244c5cbc7a95c0e532958830d73a126bbf35d6c7d7b77e0d7bdd7d3b6b3439f2" ++
    "39c0ace709f394d841d40a97749038c054606f01e4370f5d76cc06a5d58e4a59" ++
    "a0315d88aeb2c53d33a6400e58ca73160716b60f5e8d128e08986cfe96f9531a" ++
    "4ae1a50a647dd3ce1fce2e026267f8eb657c1531d259c0f9156586c1da45ecbb" ++
    "32de4af80ca0de9327ad3f5172b97a177b7134a9190c9abbe063ff33b3b61f92")

def rsaKey : RSA.PublicKey := { n := 0x919c17325617ab242ad8ba2e52573f87b2aab10236622b1278d5516453045171d56ff18fddc34b678f822e287977cc6732f4e3440871974f2308ad7a4ef596ed7149850b2dd9fe17ba6892f7ecfe2439e5f4e3710610739f3851435319efe019745ac59dd694fd0b4a0017b0f17c53a9ccf41bccfbabe9213b92cc681fbad6d76de00c438f9a1cae4f021a8fa15993afe52caa185b20a6564fec83bc44ef4b707d8ec3d4277960ff5490c89969970edcf9a2ef19c014a186296eea69b0cf5734e23c4334f3e8c10e31dbee947b4b80e323d21ab7a976be5b379dc44d3f0f71b303e9d62d175ca8d4f1fe60dae6b7c4a1baa036eb4e0715f8d998161575f386e5, e := 65537 }

/-! ## ECDSA -/

theorem ecdsa_p256_sha256_valid : verifyDer P256 p256_pub .sha256 msg p256_sig = true := by native_decide
theorem ecdsa_p256_rejects_tampered : verifyDer P256 p256_pub .sha256 badMsg p256_sig = false := by native_decide
theorem ecdsa_p384_sha384_valid : verifyDer P384 p384_pub .sha384 msg p384_sig = true := by native_decide
theorem ecdsa_p384_rejects_wrong_curve_key : verifyDer P384 p256_pub .sha384 msg p384_sig = false := by native_decide

/-! ## RSA -/

theorem rsa_pkcs1_sha256_valid : RSA.verifyPkcs1 rsaKey .sha256 msg rsa_pkcs1_sig = true := by native_decide
theorem rsa_pkcs1_rejects_tampered : RSA.verifyPkcs1 rsaKey .sha256 badMsg rsa_pkcs1_sig = false := by native_decide
theorem rsa_pkcs1_rejects_wrong_hash : RSA.verifyPkcs1 rsaKey .sha384 msg rsa_pkcs1_sig = false := by native_decide
theorem rsa_pss_sha384_valid : RSA.verifyPss rsaKey .sha384 msg rsa_pss384_sig = true := by native_decide
theorem rsa_pss_rejects_tampered : RSA.verifyPss rsaKey .sha384 badMsg rsa_pss384_sig = false := by native_decide

end LeanTLS.Spec.Signatures
