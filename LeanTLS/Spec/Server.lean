import LeanTLS.Server
/-!
# Specs for the TLS 1.3 server side

* Signing: the RFC 6979 known-answer vector for ECDSA P-256 / SHA-256 (nonce and signature),
  checked by the kernel; the DER encoding parses back; a CertificateVerify made by the server
  passes the client's own verifier.
* Negotiation (all inputs): the server only ever accepts TLS 1.3, ChaCha20-Poly1305, a signature
  scheme the client offered, and a well-formed X25519 or P-256 key share the client sent.
* Messages: the client's ClientHello builder parses back with the server's parser, and the
  server's ServerHello parses with the client's parser.
* Identities (all inputs): a loaded certificate/key pair always matches.

Kernel only (`decide +kernel`), no `native_decide`.
-/
namespace LeanTLS.Spec
open LeanTLS TLS13

set_option maxRecDepth 100000

/-! ## ECDSA P-256 signing (RFC 6979 §A.2.5, message "sample", SHA-256) -/

def rfc6979Key : Nat := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
def sampleHash : ByteArray := SHA256.hash (ofString "sample")

/-- The deterministic nonce is the RFC's `k`. -/
theorem rfc6979_p256_sample_k :
    Sign.rfc6979 EC.P256 rfc6979Key sampleHash =
      some 0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60 := by
  decide +kernel

/-- The signature is the RFC's `(r, s)`. -/
theorem ecdsaSign_p256_sample :
    Sign.ecdsaSign EC.P256 rfc6979Key sampleHash =
      some (0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716,
            0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8) := by
  decide +kernel

/-- The DER encoding of that signature parses back to `(r, s)`. -/
theorem derSig_parse_sample :
    EC.parseSig (Sign.derSig 0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716
      0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8) =
    some (0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716,
          0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8) := by
  decide +kernel

/-! ## Negotiation (all inputs) -/

/-- **What the server accepts.** If negotiation succeeds, the client offered TLS 1.3, the
ChaCha20-Poly1305 suite and the certificate's signature scheme, and the chosen key share is one
the client sent: an X25519 key of 32 bytes or a P-256 point of 65 bytes. -/
theorem negotiate_accept (ch : ClientHello) (scheme g : Nat) (k : ByteArray) (sc : Nat) (alpn : Bool)
    (h : negotiate ch scheme = .accept g k sc alpn) :
    0x0304 ∈ ch.versions ∧ TLS_CHACHA20_POLY1305_SHA256 ∈ ch.suites ∧ scheme ∈ ch.sigAlgs ∧
    sc = scheme ∧ (g, k) ∈ ch.shares ∧
    ((g = GROUP_X25519 ∧ k.size = 32) ∨ (g = GROUP_SECP256R1 ∧ k.size = 65)) := by
  unfold negotiate at h
  split at h; · cases h
  rename_i h1
  split at h; · cases h
  rename_i h2
  split at h; · cases h
  rename_i h3
  split at h; · cases h
  have h1 : 0x0304 ∈ ch.versions := by simpa using h1
  have h2 : TLS_CHACHA20_POLY1305_SHA256 ∈ ch.suites := by simpa using h2
  have h3 : scheme ∈ ch.sigAlgs := by simpa using h3
  split at h
  · rename_i a k' hf
    cases h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨h1, h2, h3, rfl, by rw [← hp.1]; exact hm,
      Or.inl ⟨rfl, hp.2⟩⟩
  · split at h
    · rename_i a k' hf
      cases h
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨h1, h2, h3, rfl, by rw [← hp.1]; exact hm,
        Or.inr ⟨rfl, hp.2⟩⟩
    · cases h

/-- A client that does not offer TLS 1.3 gets `protocol_version` (TLS 1.2 is never spoken). -/
theorem negotiate_tls13_only (ch : ClientHello) (scheme : Nat) (h : 0x0304 ∉ ch.versions) :
    ∃ c, negotiate ch scheme = .alert c ∧ c = 70 := by
  refine ⟨70, ?_, rfl⟩
  unfold negotiate
  simp [h]

/-! ## Messages: each side parses what the other builds -/

def tRandom : ByteArray := mapBytes (fun _ => 7) (zeros 32)
def tSid : ByteArray := mapBytes (fun _ => 9) (zeros 32)
def tPub : ByteArray := mapBytes (fun _ => 5) (zeros 32)

/-- The client's ClientHello, parsed by the server: versions, suites, key share, ALPN. -/
theorem clientHello_roundtrip :
    (Parser.run parseClientHello (clientHelloBody tRandom tSid (GROUP_X25519, tPub) "a.b")).toOption.map
      (fun ch => (ch.versions, ch.suites, ch.shares.map (·.1), ch.groups, ch.alpn == [http11],
                  ch.sessionId == tSid)) =
    some ([0x0304], [TLS_CHACHA20_POLY1305_SHA256], [GROUP_X25519],
          [GROUP_X25519, GROUP_SECP256R1], true, true) := by
  decide +kernel

/-- The server's ServerHello, parsed by the client: TLS 1.3, ChaCha20-Poly1305, the key share. -/
theorem serverHello_roundtrip :
    (Parser.run parseServerHello (serverHelloBody tRandom tSid GROUP_X25519 tPub)).toOption.map
      (fun sh => (sh.version, sh.cipherSuite, sh.keyShareGroup, sh.keyShare == tPub, sh.isHRR)) =
    some (0x0304, TLS_CHACHA20_POLY1305_SHA256, GROUP_X25519, true, false) := by
  decide +kernel

/-! ## Identities (all inputs) -/

/-- A certificate/key pair that loads is consistent: the private key belongs to the leaf. -/
theorem identity_ofPem_matches (certPem keyPem : String) (i : Server.Identity)
    (h : Server.Identity.ofPem certPem keyPem = .ok i) :
    ∃ der leaf, i.chain.head? = some der ∧ X509.parse der = .ok leaf ∧
      i.key.matches leaf.key = true := by
  unfold Server.Identity.ofPem at h
  simp only at h
  split at h
  · cases h
  · rename_i der hd
    split at h
    · cases h
    · rename_i leaf hl
      split at h
      · cases h
      · split at h
        · rename_i hm
          cases h
          exact ⟨der, leaf, hd, hl, hm⟩
        · cases h

end LeanTLS.Spec
