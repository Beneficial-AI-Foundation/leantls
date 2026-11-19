import LeanTLS.KeySchedule
import LeanTLS.Messages
import LeanTLS.X25519
/-!
# Specs: RFC 8448 §3 "Simple 1-RTT Handshake" trace

The constants below are copied mechanically from the RFC text. The trace negotiates
TLS_AES_128_GCM_SHA256; the key schedule, Finished computation and message parsing are
cipher-independent for SHA-256 suites, so they are checked against it directly.

`x25519_rfc8448_shared` is kernel-checked; the rest use `native_decide`
(trusts Lean's compiler in addition to the kernel).
-/
namespace LeanTLS.Spec.RFC8448
open LeanTLS LeanTLS.TLS13

/-- client ephemeral X25519 private key -/
def clientSk : ByteArray :=
  ofHex "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"

/-- client public key -/
def clientPk : ByteArray :=
  ofHex "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"

/-- ClientHello handshake message -/
def clientHello : ByteArray :=
  ofHex ("010000c00303cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef" ++
    "6283024dece7000006130113031302010000910000000b000900000673657276" ++
    "6572ff01000100000a00140012001d0017001800190100010101020103010400" ++
    "230000003300260024001d002099381de560e4bd43d23d8e435a7dbafeb3c06e" ++
    "51c13cae4d5413691e529aaf2c002b0003020304000d0020001e040305030603" ++
    "020308040805080604010501060102010402050206020202002d00020101001c" ++
    "00024001")

/-- server private key -/
def serverSk : ByteArray :=
  ofHex "b1580eeadf6dd589b8ef4f2d5652578cc810e9980191ec8d058308cea216a21e"

/-- server public key -/
def serverPk : ByteArray :=
  ofHex "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"

/-- ServerHello handshake message -/
def serverHello : ByteArray :=
  ofHex ("020000560303a6af06a4121860dc5e6e60249cd34c95930c8ac5cb1434dac155" ++
    "772ed3e2692800130100002e00330024001d0020c9828876112095fe66762bdb" ++
    "f7c672e156d6cc253b833df1dd69b1b04e751f0f002b00020304")

/-- (EC)DHE shared secret (IKM of "handshake") -/
def sharedSecret : ByteArray :=
  ofHex "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"

/-- handshake secret -/
def hsSecret : ByteArray :=
  ofHex "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"

/-- client handshake traffic secret -/
def cHsTraffic : ByteArray :=
  ofHex "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"

/-- server handshake traffic secret -/
def sHsTraffic : ByteArray :=
  ofHex "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"

/-- master secret -/
def masterSecret : ByteArray :=
  ofHex "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"

/-- server handshake write key (AES-128: 16 bytes) -/
def serverHsKey : ByteArray :=
  ofHex "3fce516009c21727d0f2e4e86ee403bc"

/-- server handshake write IV -/
def serverHsIv : ByteArray :=
  ofHex "5d313eb2671276ee13000b30"

/-- EncryptedExtensions -/
def encExts : ByteArray :=
  ofHex ("080000240022000a00140012001d00170018001901000101010201030104001c" ++
    "0002400100000000")

/-- Certificate -/
def certificate : ByteArray :=
  ofHex ("0b0001b9000001b50001b0308201ac30820115a003020102020102300d06092a" ++
    "864886f70d01010b0500300e310c300a06035504031303727361301e170d3136" ++
    "303733303031323335395a170d3236303733303031323335395a300e310c300a" ++
    "0603550403130372736130819f300d06092a864886f70d010101050003818d00" ++
    "30818902818100b4bb498f8279303d980836399b36c6988c0c68de55e1bdb826" ++
    "d3901a2461eafd2de49a91d015abbc9a95137ace6c1af19eaa6af98c7ced4312" ++
    "0998e187a80ee0ccb0524b1b018c3e0b63264d449a6d38e22a5fda4308467480" ++
    "30530ef0461c8ca9d9efbfae8ea6d1d03e2bd193eff0ab9a8002c47428a6d35a" ++
    "8d88d79f7f1e3f0203010001a31a301830090603551d1304023000300b060355" ++
    "1d0f0404030205a0300d06092a864886f70d01010b05000381810085aad2a0e5" ++
    "b9276b908c65f73a7267170618a54c5f8a7b337d2df7a594365417f2eae8f8a5" ++
    "8c8f8172f9319cf36b7fd6c55b80f21a03015156726096fd335e5e67f2dbf102" ++
    "702e608ccae6bec1fc63a42a99be5c3eb7107c3c54e9b9eb2bd5203b1c3b84e0" ++
    "a8b2f759409ba3eac9d91d402dcc0cc8f8961229ac9187b42b4de10000")

/-- CertificateVerify -/
def certVerify : ByteArray :=
  ofHex ("0f000084080400805a747c5d88fa9bd2e55ab085a61015b7211f824cd484145a" ++
    "b3ff52f1fda8477b0b7abc90db78e2d33a5c141a078653fa6bef780c5ea248ee" ++
    "aaa785c4f394cab6d30bbe8d4859ee511f602957b15411ac027671459e46445c" ++
    "9ea58c181e818e95b8c3fb0bf3278409d3be152a3da5043e063dda65cdf5aea2" ++
    "0d53dfacd42f74f3")

/-- server Finished message -/
def serverFinished : ByteArray :=
  ofHex ("140000209b9b141d906337fbd2cbdce71df4deda4ab42c309572cb7fffee5454" ++
    "b78f0718")

/-- server encrypted flight payload (EE‖Cert‖CV‖Fin) -/
def serverFlight : ByteArray :=
  ofHex ("080000240022000a00140012001d00170018001901000101010201030104001c" ++
    "00024001000000000b0001b9000001b50001b0308201ac30820115a003020102" ++
    "020102300d06092a864886f70d01010b0500300e310c300a0603550403130372" ++
    "7361301e170d3136303733303031323335395a170d3236303733303031323335" ++
    "395a300e310c300a0603550403130372736130819f300d06092a864886f70d01" ++
    "0101050003818d0030818902818100b4bb498f8279303d980836399b36c6988c" ++
    "0c68de55e1bdb826d3901a2461eafd2de49a91d015abbc9a95137ace6c1af19e" ++
    "aa6af98c7ced43120998e187a80ee0ccb0524b1b018c3e0b63264d449a6d38e2" ++
    "2a5fda430846748030530ef0461c8ca9d9efbfae8ea6d1d03e2bd193eff0ab9a" ++
    "8002c47428a6d35a8d88d79f7f1e3f0203010001a31a301830090603551d1304" ++
    "023000300b0603551d0f0404030205a0300d06092a864886f70d01010b050003" ++
    "81810085aad2a0e5b9276b908c65f73a7267170618a54c5f8a7b337d2df7a594" ++
    "365417f2eae8f8a58c8f8172f9319cf36b7fd6c55b80f21a03015156726096fd" ++
    "335e5e67f2dbf102702e608ccae6bec1fc63a42a99be5c3eb7107c3c54e9b9eb" ++
    "2bd5203b1c3b84e0a8b2f759409ba3eac9d91d402dcc0cc8f8961229ac9187b4" ++
    "2b4de100000f000084080400805a747c5d88fa9bd2e55ab085a61015b7211f82" ++
    "4cd484145ab3ff52f1fda8477b0b7abc90db78e2d33a5c141a078653fa6bef78" ++
    "0c5ea248eeaaa785c4f394cab6d30bbe8d4859ee511f602957b15411ac027671" ++
    "459e46445c9ea58c181e818e95b8c3fb0bf3278409d3be152a3da5043e063dda" ++
    "65cdf5aea20d53dfacd42f74f3140000209b9b141d906337fbd2cbdce71df4de" ++
    "da4ab42c309572cb7fffee5454b78f0718")

/-- client application traffic secret -/
def cApTraffic : ByteArray :=
  ofHex "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"

/-- server application traffic secret -/
def sApTraffic : ByteArray :=
  ofHex "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"

/-- client Finished message -/
def clientFinished : ByteArray :=
  ofHex ("14000020a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2" ++
    "edd5ce61")

/-- Body of a handshake message (drop the 4-byte header). -/
def body (m : ByteArray) : ByteArray := m.extract 4 m.size

/-! ## (EC)DHE -/

theorem x25519_rfc8448_pubkeys :
    X25519.publicKey clientSk = clientPk ∧ X25519.publicKey serverSk = serverPk := by
  decide +kernel

theorem x25519_rfc8448_shared :
    X25519.x25519 clientSk serverPk = sharedSecret := by
  decide +kernel

/-! ## key schedule -/

theorem handshake_secrets :
    let s := handshakeSecrets sharedSecret (clientHello ++ serverHello)
    s.handshake = hsSecret ∧ s.clientHs = cHsTraffic ∧ s.serverHs = sHsTraffic ∧
    s.master = masterSecret := by
  native_decide

theorem server_handshake_keys :
    trafficKeys sHsTraffic 16 = { key := serverHsKey, iv := serverHsIv } := by
  native_decide

theorem server_finished :
    finishedVerify sHsTraffic (clientHello ++ serverHello ++ encExts ++ certificate ++ certVerify) =
    body serverFinished := by
  native_decide

theorem client_finished :
    finishedVerify cHsTraffic
      (clientHello ++ serverHello ++ encExts ++ certificate ++ certVerify ++ serverFinished) =
    body clientFinished := by
  native_decide

theorem application_secrets :
    appSecrets masterSecret
      (clientHello ++ serverHello ++ encExts ++ certificate ++ certVerify ++ serverFinished) =
    (cApTraffic, sApTraffic) := by
  native_decide

/-! ## parsing -/

theorem server_hello_parses :
    ((Parser.run parseServerHello (body serverHello)).toOption).map
      (fun sh => (sh.cipherSuite, sh.version, sh.keyShareGroup, sh.keyShare, sh.isHRR)) =
    some (0x1301, 0x0304, GROUP_X25519, serverPk, false) := by
  native_decide

/-- The coalesced server flight splits into EE, Certificate, CertificateVerify, Finished. -/
theorem server_flight_frames :
    (Record.parseHs serverFlight).map (·.1) = some 8 ∧
    serverFlight = encExts ++ certificate ++ certVerify ++ serverFinished := by
  native_decide

theorem certificate_parses :
    ((Parser.run parseCertificate (body certificate)).toOption).map List.length = some 1 := by
  native_decide

end LeanTLS.Spec.RFC8448
