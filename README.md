# LeanTLS + LeanBrowse

A TLS 1.3 client library written from scratch in Lean 4 (`leantls/`) and a small terminal web
browser built on it (`leanbrowse/`). Both compile to C. Tests are written as **specs**: Lean
theorems checked on every `lake build`. There is no separate runtime test suite.

> ⚠ **Research code, not production TLS.** The server certificate chain and the CertificateVerify
> signature are **not validated yet**, so an active man-in-the-middle can impersonate any server.
> The arithmetic is not constant-time.

## What's implemented

| Layer | Module | Notes |
|---|---|---|
| SHA-256, HMAC, HKDF | `LeanTLS/SHA256.lean`, `HKDF.lean` | FIPS 180-4, RFC 2104, RFC 5869 |
| ChaCha20, Poly1305, AEAD | `ChaCha20.lean`, `AEAD.lean` | RFC 8439 |
| X25519 | `X25519.lean` | RFC 7748, Montgomery ladder over `Nat` (GMP) |
| Record layer, handshake framing | `Record.lean` | RFC 8446 §5, §4 |
| Key schedule | `KeySchedule.lean` | RFC 8446 §7 |
| ClientHello / ServerHello / Certificate | `Messages.lean` | total cursor parser |
| Connection (IO) | `Client.lean` | `Std.Async` TCP/DNS, KeyUpdate, close_notify |
| URL parsing and resolution | `LeanBrowse/Url.lean` | RFC 3986 §5.2 |
| Chunked transfer coding | `Chunked.lean` | RFC 9112 §7.1 |
| HTTP/1.1 client | `Http.lean` | https over LeanTLS, plain http over TCP, redirects |
| HTML → text | `Html.lean` | total tokenizer (no `partial`) and renderer, numbered links |

The only cipher suite is `TLS_CHACHA20_POLY1305_SHA256` with X25519. Tested against Cloudflare,
Google, GitHub, Wikipedia, Hacker News and lean-lang.org.

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

These theorems rely only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Specs: known-answer vectors as theorems

- `leantls/LeanTLS/Spec/Kernel.lean`: SHA-256, HMAC, ChaCha20 block, Poly1305 and X25519 vectors
  (RFC 7748 §5.2 and §6.1), checked by the Lean **kernel** (`decide +kernel`), so the compiler is
  not trusted.
- `leantls/LeanTLS/Spec/Native.lean`: long-key HMAC, HKDF, the full AEAD vector and a tamper check.
- `leantls/LeanTLS/Spec/RFC8448.lean`: the RFC 8448 §3 handshake trace. It covers the shared
  secret, handshake/master secrets, traffic keys, both Finished MACs, application secrets, and
  ServerHello/Certificate parsing.
- `leanbrowse/LeanBrowse/Spec/Examples.lean`: URL resolution, chunked decoding, HTTP response
  parsing and HTML rendering cases.

`Native` and `RFC8448` (except the X25519 parts) and the browser examples use `native_decide`,
which also trusts Lean's compiler (`#print axioms` shows it). They were too heavy for the kernel on
the 3 GB build box, or work with `String`s, which the kernel does not reduce.

## Build

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned to Lean 4.36.0.

```sh
lake build                         # at the root: checks every proof and spec in both packages
cd leanbrowse && lake build        # builds the lbrowse binary
.lake/build/bin/lbrowse https://example.com      # interactive: <n> follows a link, b goes back, q quits
.lake/build/bin/lbrowse --dump https://news.ycombinator.com
cd ../leantls && lake build && .lake/build/bin/tlsget example.com /
```

Split workflow: check proofs and generate C on a remote Linux box, then compile natively on your
machine with `leanc`:

```sh
cd leanbrowse && ./vd.sh push && ./vd.sh build && ./build-local.sh   # → build-local/lbrowse
```

## Not done yet

- X.509 chain validation, hostname check, CertificateVerify (RSA-PSS / ECDSA P-256)
- `TLS_AES_128_GCM_SHA256` (servers that refuse ChaCha20 fail the handshake)
- HelloRetryRequest, session resumption, client certificates
- Constant-time field arithmetic
