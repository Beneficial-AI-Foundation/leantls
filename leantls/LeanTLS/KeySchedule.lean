import LeanTLS.HKDF
/-!
# TLS 1.3 key schedule (RFC 8446 §7), SHA-256 suites

Pure functions; the client in `LeanTLS.Client` calls exactly these, and
`LeanTLS.Spec.RFC8448` checks them against the RFC 8448 handshake trace.
-/
namespace LeanTLS.TLS13

/-- `HKDF-Expand-Label(secret, label, context, length)` -/
def expandLabel (secret : ByteArray) (label : String) (ctx : ByteArray) (len : Nat) : ByteArray :=
  let l := ofString ("tls13 " ++ label)
  HKDF.expand secret (be16 len ++ u8 l.size ++ l ++ u8 ctx.size ++ ctx) len

@[simp] theorem expandLabel_size (s : ByteArray) (l : String) (c : ByteArray) (n : Nat) :
    (expandLabel s l c n).size = n := HKDF.expand_size _ _ _

/-- `Derive-Secret(secret, label, messages)` -/
def deriveSecret (secret : ByteArray) (label : String) (msgs : ByteArray) : ByteArray :=
  expandLabel secret label (SHA256.hash msgs) 32

structure HsSecrets where
  handshake : ByteArray
  clientHs : ByteArray
  serverHs : ByteArray
  master : ByteArray

/-- Secrets after the ServerHello. `shared` is the (EC)DHE output,
    `chsh` the transcript `ClientHello ‖ ServerHello`. -/
def handshakeSecrets (shared chsh : ByteArray) : HsSecrets :=
  let early := HKDF.extract (zeros 32) (zeros 32)
  let hs := HKDF.extract (deriveSecret early "derived" ByteArray.empty) shared
  { handshake := hs
    clientHs := deriveSecret hs "c hs traffic" chsh
    serverHs := deriveSecret hs "s hs traffic" chsh
    master := HKDF.extract (deriveSecret hs "derived" ByteArray.empty) (zeros 32) }

/-- Application traffic secrets from the transcript through the server Finished. -/
def appSecrets (master toServerFinished : ByteArray) : ByteArray × ByteArray :=
  (deriveSecret master "c ap traffic" toServerFinished,
   deriveSecret master "s ap traffic" toServerFinished)

/-- `verify_data` of a Finished message (RFC 8446 §4.4.4). -/
def finishedVerify (baseKey transcript : ByteArray) : ByteArray :=
  hmac (expandLabel baseKey "finished" ByteArray.empty 32) (SHA256.hash transcript)

@[simp] theorem finishedVerify_size (k t : ByteArray) : (finishedVerify k t).size = 32 :=
  hmac_size _ _

structure TrafficKeys where
  key : ByteArray
  iv : ByteArray
  deriving DecidableEq

def trafficKeys (secret : ByteArray) (keyLen : Nat := 32) : TrafficKeys :=
  { key := expandLabel secret "key" ByteArray.empty keyLen
    iv := expandLabel secret "iv" ByteArray.empty 12 }

theorem trafficKeys_sizes (s : ByteArray) (n : Nat) :
    (trafficKeys s n).key.size = n ∧ (trafficKeys s n).iv.size = 12 := by
  simp [trafficKeys]

/-- KeyUpdate (RFC 8446 §7.2). -/
def nextTrafficSecret (s : ByteArray) : ByteArray := expandLabel s "traffic upd" ByteArray.empty 32

end LeanTLS.TLS13
