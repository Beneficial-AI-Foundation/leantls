# LeanTLS + LeanBrowse

A TLS 1.3 client library written from scratch in Lean 4 (`leantls/`) and a small terminal web
browser built on it (`leanbrowse/`). Both compile to C. Tests are written as **specs**: Lean
theorems checked on every `lake build`. There is no separate runtime test suite.

> ⚠ **Research code, not production TLS.** It validates certificate chains against the system
> roots, checks the hostname and the server's CertificateVerify signature, but it does not check
> revocation, its arithmetic is not constant-time, and nobody has audited it.

## What's implemented

| Layer | Module | Notes |
|---|---|---|
| SHA-256, HMAC, HKDF | `LeanTLS/SHA256.lean`, `HKDF.lean` | FIPS 180-4, RFC 2104, RFC 5869 |
| ChaCha20, Poly1305, AEAD | `ChaCha20.lean`, `AEAD.lean` | RFC 8439 |
| X25519 | `X25519.lean` | RFC 7748, Montgomery ladder over `Nat` (GMP) |
| Record layer, handshake framing | `Record.lean` | RFC 8446 §5, §4 |
| Key schedule | `KeySchedule.lean` | RFC 8446 §7 |
| ClientHello / ServerHello / Certificate | `Messages.lean` | total cursor parser, HelloRetryRequest |
| SHA-384, SHA-512 | `SHA512.lean` | FIPS 180-4 |
| DER / ASN.1 | `ASN1.lean` | offset-based, total, bounds proved |
| RSA verification | `RSA.lean` | PKCS#1 v1.5 and PSS (RFC 8017) |
| P-256 / P-384 | `EC.lean` | ECDSA verification, P-256 ECDH |
| X.509 path validation | `X509.lean` | chain to system roots, validity, CA constraints, hostname (RFC 6125), CertificateVerify |
| Connection (IO) | `Client.lean` | `Std.Async` TCP/DNS, trust store, KeyUpdate, close_notify |
| URL parsing and resolution | `LeanBrowse/Url.lean` | RFC 3986 §5.2 |
| Chunked transfer coding | `Chunked.lean` | RFC 9112 §7.1 |
| HTTP/1.1 client | `Http.lean` | https over LeanTLS, plain http over TCP, redirects |
| HTML → text | `Html.lean` | total tokenizer (no `partial`) and renderer, numbered links |

The only cipher suite is `TLS_CHACHA20_POLY1305_SHA256`; key exchange is X25519, or P-256 after a
HelloRetryRequest. Server signatures: ECDSA P-256/P-384 and RSA-PSS (CertificateVerify), plus RSA
PKCS#1 v1.5 in certificates. Tested against Cloudflare, Google, GitHub, Wikipedia, Hacker News and
lean-lang.org (all verified), and against `openssl s_server` for HelloRetryRequest, RSA-PSS, wrong
hostname, expired and untrusted certificates (all behave correctly).

## Proved (for all inputs)

- `AEAD.openMsg_sealMsg`: decrypting a sealed message returns the original.
  `AEAD.openMsg_some_tag`: `openMsg` accepts only when the tag matches.
- `ChaCha20.encrypt_encrypt`: decryption inverts encryption.
- `Record.openRecord_sealRecord`: a protected TLS record opens to the exact content and type.
- `Record.parseInner_inner`: inner-plaintext decoding round-trips for any zero-padding length.
- `Record.parseHs_hsMsg`: handshake framing round-trips and leaves trailing bytes untouched.
- `X25519.clamp_mul8`, `clamp_range`, `ladder_lt`: scalar clamping and field-range facts.
- Output sizes: `hash_size`, `hmac_size`, `expand_size`, `expandLabel_size`, `trafficKeys_sizes`,
  `pad_size_mod`.
- `Chunked.decode_encode`: chunked decoding inverts encoding.
- `removeDots_no_dotdot`: a resolved URL path never contains `..`, so links cannot climb above `/`.
- `ASN1.tlv_bounds`: every DER element the parser returns lies inside the buffer, after its header.
- `X509.matchLabels_wild_one`, `matchLabels_wild_not_parent`, `matchLabels_wild_tld`: a wildcard
  certificate name covers exactly one label, never the bare parent domain, and `*.com` matches nothing.

These theorems rely only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Specs: known-answer vectors as theorems

- `leantls/LeanTLS/Spec/Kernel.lean`: SHA-256, HMAC, ChaCha20 block, Poly1305 and X25519 vectors
  (RFC 7748 §5.2 and §6.1), checked by the Lean **kernel** (`decide +kernel`), so the compiler is
  not trusted.
- `leantls/LeanTLS/Spec/Native.lean`: long-key HMAC, HKDF, the full AEAD vector and a tamper check.
- `leantls/LeanTLS/Spec/RFC8448.lean`: the RFC 8448 §3 handshake trace. It covers the shared
  secret, handshake/master secrets, traffic keys, both Finished MACs, application secrets, and
  ServerHello/Certificate parsing.
- `leantls/LeanTLS/Spec/Signatures.lean`: the P-256/P-384 base points are on their curves (kernel)
  and have order `n`; ECDSA and RSA (PKCS#1 v1.5, PSS) signatures made by OpenSSL verify, and
  tampered ones do not.
- `leantls/LeanTLS/Spec/X509.lean`: example.com's real chain validates at a fixed date and fails for a
  wrong host, two-label wildcard use, after expiry, without roots and with a flipped signature bit;
  RFC 8448's CertificateVerify verifies; RFC 6125 hostname cases; P-256 key agreement.
- `leanbrowse/LeanBrowse/Spec/Examples.lean`: URL resolution, chunked decoding, HTTP response
  parsing and HTML rendering cases.

`Native` and `RFC8448` (except the X25519 parts) and the browser examples use `native_decide`,
which also trusts Lean's compiler (`#print axioms` shows it). They were too heavy for the kernel on
the 3 GB build box, or work with `String`s, which the kernel does not reduce.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned to Lean 4.36.0.

```sh
lake build                         # at the root: checks every proof and spec (root package owns both libraries)
cd leanbrowse && lake build        # builds the lbrowse binary
.lake/build/bin/lbrowse https://example.com      # interactive: <n> follows a link, b goes back, q quits
.lake/build/bin/lbrowse --dump https://news.ycombinator.com
.lake/build/bin/lbrowse --insecure https://self-signed.example   # skip certificate checks (testing only)
cd ../leantls && lake build && .lake/build/bin/tlsget example.com /
```

Split workflow: check proofs and generate C on a remote Linux box, then compile natively on your
machine with `leanc`:

```sh
cd leanbrowse && ./vd.sh push && ./vd.sh build && ./build-local.sh   # → build-local/lbrowse
```

Roots come from `$SSL_CERT_FILE` or the system bundle (`/etc/ssl/cert.pem` on macOS,
`/etc/ssl/certs/ca-certificates.crt` or `/etc/pki/tls/certs/ca-bundle.crt` on Linux).

## Not done yet

- `TLS_AES_128_GCM_SHA256` (servers that refuse ChaCha20 fail the handshake)
- Revocation (CRL / OCSP), name constraints (a CA with a critical nameConstraints is rejected),
  RSA-PSS and Ed25519 in certificate signatures, IP-address hosts
- Session resumption, client certificates
- Constant-time field arithmetic
