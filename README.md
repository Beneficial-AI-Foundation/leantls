# LeanTLS + LeanBrowse

A TLS 1.3 client library written from scratch in Lean 4 (`LeanTLS`) and a small terminal web
browser built on it (`LeanBrowse`). Both compile to native code through C. Tests are written as
**specs**: Lean theorems that `lake build` checks. There is no separate runtime test suite.

> ⚠ **Research code, not production TLS.** It validates certificate chains against your system's
> root certificates, checks the hostname and the server's CertificateVerify signature. It does not
> check revocation, its arithmetic is not constant-time, and nobody has audited it.

- [Install](#install)
- [Use the browser: `lbrowse`](#use-the-browser-lbrowse)
- [Use the HTTPS fetcher: `tlsget`](#use-the-https-fetcher-tlsget)
- [Use LeanTLS as a library](#use-leantls-as-a-library)
- [What's implemented](#whats-implemented)
- [What's proved](#whats-proved)
- [Not done yet](#not-done-yet)

## Install

### Prebuilt binaries (macOS, Apple Silicon)

Each [release](https://github.com/Beneficial-AI-Foundation/leantls/releases) has `lbrowse` and
`tlsget` for macOS arm64. They depend only on system libraries.

```sh
curl -LO https://github.com/Beneficial-AI-Foundation/leantls/releases/latest/download/leantls-macos-arm64.tar.gz
tar xzf leantls-macos-arm64.tar.gz
xattr -d com.apple.quarantine lbrowse tlsget 2>/dev/null   # the binaries are not notarized
mkdir -p ~/.local/bin && mv lbrowse tlsget ~/.local/bin/   # make sure ~/.local/bin is on your PATH
lbrowse https://example.com
```

### From source (macOS or Linux)

You need [elan](https://github.com/leanprover/elan), the Lean toolchain manager. The repository
pins Lean 4.36.0, and elan installs it on the first build. You also need a C toolchain, which
ships with Lean.

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh     # if you don't have elan yet
git clone https://github.com/Beneficial-AI-Foundation/leantls
cd leantls
lake build                     # checks every proof and spec, then builds both binaries (a few minutes)
cp .lake/build/bin/lbrowse .lake/build/bin/tlsget ~/.local/bin/
```

`lake build` fails if any proof or spec fails, so a successful build means every theorem in
[What's proved](#whats-proved) was checked on your machine.

### Root certificates

LeanTLS reads trusted roots from `$SSL_CERT_FILE` if it is set. Otherwise it uses the first system
bundle it finds: `/etc/ssl/cert.pem` (macOS), `/etc/ssl/certs/ca-certificates.crt` (Debian,
Ubuntu) or `/etc/pki/tls/certs/ca-bundle.crt` (Fedora, RHEL).

## Use the browser: `lbrowse`

```sh
lbrowse                                   # opens https://example.com
lbrowse https://en.wikipedia.org/wiki/Lean_(proof_assistant)
lbrowse news.ycombinator.com              # https:// is assumed
lbrowse --dump https://lean-lang.org      # print the page and its links, then exit
lbrowse --insecure https://localhost:8443 # skip certificate checks (testing only)
```

Every page starts with a status line. It shows 🔒 and the chain length when the certificate was
verified, and a warning for `--insecure` or plain `http://`. Links appear inline as `[n]`.

| Key | Action |
|---|---|
| Enter | next page of text (40 lines) |
| `<n>` | follow link number `n` |
| `g <url>` | go to a URL |
| `b` | back |
| `l` | list all links with their URLs |
| `r` | reload |
| `t` | back to the top of the page |
| `h` or `?` | help |
| `q` | quit |

Pages are fetched with HTTP/1.1 and redirects are followed. HTML is rendered as text: headings,
paragraphs, lists, preformatted blocks and image alt text. Scripts, styles and CSS are ignored.
Set `COLUMNS` to change the wrap width.

## Use the HTTPS fetcher: `tlsget`

```sh
tlsget example.com                        # GET / and print the raw HTTP response
tlsget github.com /about                  # another path
tlsget localhost / 8443                   # another port
tlsget --insecure localhost / 8443        # skip certificate checks
```

The connection summary goes to stderr, for example
`TLS 1.3 with github.com: ChaCha20-Poly1305, X25519; certificate verified (3 in chain)`. The
response goes to stdout. If the handshake or certificate check fails, `tlsget` prints the reason
and exits with code 1.

## Use LeanTLS as a library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "leantls"
git = "https://github.com/Beneficial-AI-Foundation/leantls"
rev = "main"
```

Then:

```lean
import LeanTLS.Client

def main : IO Unit := do
  let trust ← LeanTLS.TrustStore.load            -- load the system roots once, reuse them
  let c ← LeanTLS.connect "example.com" 443 (some trust)
  IO.println s!"verified: {c.verified}, group: {c.group}, chain: {c.peerCerts.length}"
  c.writeString "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
  let response ← c.readAll                        -- or `c.read` for one chunk at a time
  c.close
  IO.println (String.fromUTF8! response)
```

`connect` throws an `IO.userError` with the reason if the handshake fails, the chain does not lead
to a trusted root, the certificate is expired or doesn't name the host, or the CertificateVerify
signature is invalid. The pure building blocks can also be used on their own: `SHA256.hash`,
`SHA512.hash384`, `hmac`, `HKDF`, `AEAD.sealMsg`/`openMsg`, `X25519.x25519`, `RSA.verifyPss`,
`EC.verifyDer`, `X509.parse` and `X509.validate`.

## What's implemented

| Layer | Module | Notes |
|---|---|---|
| SHA-256, HMAC, HKDF | `LeanTLS/SHA256.lean`, `HKDF.lean` | FIPS 180-4, RFC 2104, RFC 5869 |
| SHA-384, SHA-512 | `SHA512.lean` | FIPS 180-4 |
| ChaCha20, Poly1305, AEAD | `ChaCha20.lean`, `AEAD.lean` | RFC 8439 |
| X25519 | `X25519.lean` | RFC 7748, Montgomery ladder over `Nat` (GMP) |
| P-256 / P-384 | `EC.lean` | ECDSA verification, P-256 ECDH |
| RSA verification | `RSA.lean` | PKCS#1 v1.5 and PSS (RFC 8017) |
| DER / ASN.1 | `ASN1.lean` | offset-based, total, bounds proved |
| X.509 path validation | `X509.lean` | chain to system roots, validity, CA constraints, hostname (RFC 6125), CertificateVerify |
| Record layer, handshake framing | `Record.lean` | RFC 8446 §5, §4 |
| Key schedule | `KeySchedule.lean` | RFC 8446 §7 |
| Handshake messages | `Messages.lean` | ClientHello, ServerHello, HelloRetryRequest, Certificate, CertificateVerify |
| Connection (IO) | `Client.lean` | `Std.Async` TCP/DNS, trust store, KeyUpdate, close_notify |
| URL parsing and resolution | `LeanBrowse/Url.lean` | RFC 3986 §5.2 |
| Chunked transfer coding | `Chunked.lean` | RFC 9112 §7.1 |
| HTTP/1.1 client | `Http.lean` | https over LeanTLS, plain http over TCP, redirects |
| HTML → text | `Html.lean` | total tokenizer (no `partial`) and renderer, numbered links |

`LeanBrowse` uses only LeanTLS's public API. The two are separate libraries in one Lake package, so
tools that analyse the root package, such as VeriLib, see both.

The only cipher suite is `TLS_CHACHA20_POLY1305_SHA256`. Key exchange is X25519, or P-256 after a
HelloRetryRequest. Accepted server signatures:
- **CertificateVerify:** ECDSA P-256/P-384 and RSA-PSS.
- **Certificates:** the same, plus RSA PKCS#1 v1.5.

Tested against Cloudflare, Google, GitHub, Wikipedia, Hacker News and lean-lang.org (all
verified). Also tested against `openssl s_server`, with HelloRetryRequest, RSA-PSS, a wrong hostname,
an expired certificate and an untrusted root (each accepted or rejected as it should be).

## What's proved

**For all inputs:**

- `AEAD.openMsg_sealMsg`: decrypting a sealed message returns the original.
  `AEAD.openMsg_some_tag`: `openMsg` accepts only when the tag matches.
- `ChaCha20.encrypt_encrypt`: decryption inverts encryption.
- `Record.openRecord_sealRecord`: a protected TLS record opens to the exact content and type.
- `Record.parseInner_inner`: inner-plaintext decoding round-trips for any zero-padding length.
- `Record.parseHs_hsMsg`: handshake framing round-trips and leaves trailing bytes untouched.
- `ASN1.tlv_bounds`: every DER element the parser returns lies inside the buffer, after its header.
- `X509.matchLabels_wild_one`, `matchLabels_wild_not_parent`, `matchLabels_wild_tld`: a wildcard
  certificate name covers exactly one label and never the bare parent domain, and `*.com` matches
  nothing.
- `X25519.clamp_mul8`, `clamp_range`, `ladder_lt`: scalar clamping and field-range facts.
- Output sizes: `hash_size`, `hmac_size`, `expand_size`, `expandLabel_size`, `trafficKeys_sizes`,
  `pad_size_mod`.
- `Chunked.decode_encode`: chunked decoding inverts encoding.
- `removeDots_no_dotdot`: a resolved URL path never contains `..`, so links cannot climb above `/`.

These theorems rely only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Specs, known-answer cases as theorems:**

- `LeanTLS/Spec/Kernel.lean`: SHA-256, HMAC, ChaCha20, Poly1305 and X25519 vectors (FIPS, RFC 4231,
  RFC 8439, RFC 7748). These are checked by the Lean **kernel** (`decide +kernel`), so the compiler
  is not trusted.
- `LeanTLS/Spec/Native.lean`: long-key HMAC, HKDF, the full RFC 8439 AEAD vector and a tamper check.
- `LeanTLS/Spec/RFC8448.lean`: the RFC 8448 §3 handshake trace. It covers the shared secret,
  handshake and master secrets, traffic keys, both Finished MACs, application secrets, and message
  parsing.
- `LeanTLS/Spec/Signatures.lean`:
  - The P-256/P-384 base points are on their curves (kernel-checked) and have order `n`.
  - ECDSA and RSA signatures made by OpenSSL verify, and tampered ones do not.
- `LeanTLS/Spec/X509.lean`:
  - example.com's real chain validates at a fixed date. It fails for a wrong host, for a wildcard
    used across two labels, after expiry, without roots, and with one flipped signature bit.
  - RFC 8448's CertificateVerify verifies.
  - RFC 6125 hostname cases and P-256 key agreement.
- `LeanBrowse/Spec/Examples.lean`: URL resolution, chunked decoding, HTTP response parsing and
  HTML rendering.

Specs marked `native_decide` also trust Lean's compiler, and `#print axioms` shows this. They were
too heavy for the kernel on a 3 GB build machine, or they work on `String`s, which the kernel
does not evaluate.

### Remote proof checking

`vd.sh` and `build-local.sh` split the work between two machines. A remote Linux box (host alias
`VD`) checks the proofs and generates C. `leanc` then compiles that C on your machine:

```sh
./vd.sh push && ./vd.sh build && ./build-local.sh   # → build-local/lbrowse, build-local/tlsget
```

## Not done yet

- `TLS_AES_128_GCM_SHA256`: servers that refuse ChaCha20 fail the handshake.
- Revocation (CRL / OCSP).
- Name constraints: a CA with a critical nameConstraints extension is rejected.
- RSA-PSS and Ed25519 signatures inside certificates.
- IP-address hosts.
- Session resumption and client certificates.
- Constant-time field arithmetic.
