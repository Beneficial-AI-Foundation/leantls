# LeanTLS + LeanBrowse

A TLS 1.3 client and server library written from scratch in Lean 4 (`LeanTLS`) and a small
terminal web browser built on it (`LeanBrowse`). The server side powers HTTPS in
[leannginx](https://github.com/Beneficial-AI-Foundation/leannginx). Both compile to native code through C. Tests are written as
**specs**: Lean theorems that `lake build` checks. There is no separate runtime test suite.

> ⚠ **Research code, not production TLS.** It validates certificate chains against your system's
> root certificates, checks the hostname and the server's CertificateVerify signature. It does not
> check revocation, its arithmetic is not constant-time, and nobody has audited it.

- [Install](#install)
- [Use the browser: `lbrowse`](#use-the-browser-lbrowse)
- [Use the HTTPS fetcher: `tlsget`](#use-the-https-fetcher-tlsget)
- [Use LeanTLS as a library](#use-leantls-as-a-library)
- [Use LeanTLS as a server](#use-leantls-as-a-server)
- [What's implemented](#whats-implemented)
- [What's proved](#whats-proved)
- [Not done yet](#not-done-yet)

## Install

### From source (macOS or Linux)

You need [elan](https://github.com/leanprover/elan), the Lean toolchain manager. The repository
pins Lean 4.36.0, and elan installs it on the first build. You also need a C toolchain, which
ships with Lean.

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh     # if you don't have elan yet
git clone https://github.com/Beneficial-AI-Foundation/leantls
cd leantls
lake build                     # checks every proof and spec (a few minutes)
lake build tlsget lbrowse      # builds the two binaries
mkdir -p ~/.local/bin && cp .lake/build/bin/lbrowse .lake/build/bin/tlsget ~/.local/bin/   # ~/.local/bin must be on PATH
```

The first `lake build` fails if any proof or spec fails, so a successful build means every theorem in
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

## Use LeanTLS as a server

`LeanTLS.Server.accept` runs the server handshake over any byte stream (a `Transport` with
`recv`/`send`), so the caller keeps control of sockets and timeouts:

```lean
import LeanTLS.Server
open LeanTLS Server

-- once, at startup
let ident ← IO.ofExcept (Identity.ofPem (← IO.FS.readFile "cert.pem") (← IO.FS.readFile "key.pem"))
-- per connection, inside `Async`
let t : Transport := { recv := myRecvWithTimeout, send := sock.send }
match ← accept t (fun _sni => some ident) 60000 with
| .tls c => do
  let req ← c.read 60000          -- `none` = timeout, `some none` = closed
  c.write "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi".toUTF8
  c.close
| .plain bytes => ...             -- the peer sent something that is not TLS (e.g. plain HTTP)
| .failed reason => ...
```

Certificates: ECDSA P-256 keys (signed with `ecdsa_secp256r1_sha256`, deterministic RFC 6979
nonces) or RSA keys (`rsa_pss_rsae_sha256`), from PEM (`PRIVATE KEY`, `EC PRIVATE KEY`,
`RSA PRIVATE KEY`; not encrypted). `Identity.ofPem` checks that the key belongs to the leaf
certificate. The callback receives the SNI name, so different names can get different
certificates.

### `tlsserve`, a worked example

[`TlsServe.lean`](TlsServe.lean) fills in the two pieces the sketch above leaves open — a
`Transport` whose `recv` honours the timeout, and a listen loop — in about 70 lines. Build it
and serve a self-signed certificate on the loopback interface:

```sh
lake build tlsserve
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:prime256v1 \
  -keyout key.pem -out cert.pem -days 30 -nodes \
  -subj "/CN=localhost" -addext "subjectAltName=DNS:localhost"
.lake/build/bin/tlsserve cert.pem key.pem 8443 &
```

Then point clients at it. `-n N` serves `N` connections and exits, so scripted tests don't leave
a server behind.

```sh
curl --cacert cert.pem https://localhost:8443/              # hello from LeanTLS
curl --cacert cert.pem --curves P-256 https://localhost:8443/        # P-256 key share
openssl s_client -connect 127.0.0.1:8443 -CAfile cert.pem -tls1_3    # Verify return code: 0 (ok)
SSL_CERT_FILE=cert.pem .lake/build/bin/tlsget localhost / 8443       # LeanTLS on both ends
openssl s_client -connect 127.0.0.1:8443 -tls1_2            # rejected: alert 70 protocol_version
```

`tlsserve` binds `127.0.0.1` only. It exists to exercise the server handshake against other
implementations, not to serve traffic: this is research code and its arithmetic is not
constant-time.

## What's implemented

| Layer | Module | Notes |
|---|---|---|
| SHA-256, HMAC, HKDF | `LeanTLS/SHA256.lean`, `HKDF.lean` | FIPS 180-4, RFC 2104, RFC 5869 |
| SHA-384, SHA-512 | `SHA512.lean` | FIPS 180-4 |
| ChaCha20, Poly1305, AEAD | `ChaCha20.lean`, `Poly1305.lean`, `AEAD.lean` | RFC 8439; Poly1305 runs a 26-bit-limb version proved equal to the spec (`macFast_eq`, compiled in via `@[csimp]`) |
| X25519 | `X25519.lean` | RFC 7748, Montgomery ladder over `Nat` (GMP) |
| P-256 / P-384 | `EC.lean` | ECDSA verification, P-256 ECDH |
| RSA verification | `RSA.lean` | PKCS#1 v1.5 and PSS (RFC 8017) |
| DER / ASN.1 | `ASN1.lean` | offset-based, total, bounds proved |
| X.509 path validation | `X509.lean` | chain to system roots, validity, CA constraints, hostname (RFC 6125), CertificateVerify |
| Record layer, handshake framing | `Record.lean` | RFC 8446 §5, §4 |
| Key schedule | `KeySchedule.lean` | RFC 8446 §7 |
| Handshake messages | `Messages.lean` | ClientHello, ServerHello, HelloRetryRequest, Certificate, CertificateVerify |
| Connection (IO) | `Client.lean` | `Std.Async` TCP/DNS, trust store, KeyUpdate, close_notify |
| Signing, private keys | `Sign.lean` | ECDSA P-256 with RFC 6979 nonces, RSA-PSS, PKCS#8 / SEC1 / PKCS#1 PEM |
| Server handshake (pure) | `ServerMessages.lean` | ClientHello parsing, negotiation, ServerHello … Finished |
| Server connection (IO) | `Server.lean` | `Std.Async`, caller-supplied transport, SNI, KeyUpdate, close_notify |
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

The server accepts TLS 1.3 only (a TLS 1.2 client gets `protocol_version`), with ChaCha20-Poly1305
and an X25519 or P-256 key share; there is no HelloRetryRequest, so a client that sends neither
share fails. Tested with curl, OpenSSL `s_client` (X25519, P-256, ECDSA and RSA certificates),
Python's `ssl` and Go's `crypto/tls`.

## What's proved

**For all inputs:**

- `AEAD.openMsg_sealMsg`: decrypting a sealed message returns the original.
  `AEAD.openMsg_some_tag`: `openMsg` accepts only when the tag matches.
- `ChaCha20.encrypt_encrypt`: decryption inverts encryption.
- `Poly1305.macFast_eq`: the fast 26-bit-limb Poly1305 equals the arbitrary-precision specification
  for every key and message (about 50x faster; the compiler uses it in place of the spec).
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
- `LeanTLS/Spec/Server.lean` (kernel-checked):
  - The RFC 6979 §A.2.5 vector for ECDSA P-256 / SHA-256: the deterministic nonce and the
    signature `(r, s)`; the DER encoding parses back.
  - For all ClientHellos (`negotiate_accept`): the server accepts only TLS 1.3, ChaCha20-Poly1305,
    a signature scheme the client offered, and a key share the client sent with the right size
    for X25519 or P-256. Without TLS 1.3 on offer the answer is `protocol_version`.
  - The client's ClientHello parses with the server's parser, and the server's ServerHello with
    the client's.
  - For all PEM inputs (`identity_ofPem_matches`): a loaded certificate/key pair belongs together.
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
- Server: HelloRetryRequest, `TLS_AES_128_GCM_SHA256`, P-384 and Ed25519 certificate keys,
  encrypted private keys. Bulk throughput is bounded by pure-Lean ChaCha20 (about 45 MB/s).
- Constant-time field arithmetic.
