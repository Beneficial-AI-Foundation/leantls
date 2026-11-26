# Contributing to LeanTLS

Thanks for your interest in contributing. LeanTLS is a TLS 1.3 client and server
library written from scratch in Lean 4, with a small terminal web browser
(`lbrowse`) and an HTTPS fetcher (`tlsget`) built on it. Its guarantees come from
machine-checked proofs and specs that `lake build` verifies. This guide covers how
to build it, how it is tested, and how to send a change. It follows the shared
contribution standard used across the
[Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation) Lean projects.

## Prerequisites

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads `lean-toolchain` and fetches the exact Lean/Lake version this project
uses, so you don't install Lean by hand:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

You also need a C toolchain (LeanTLS compiles to native code through C); the one
Lean ships with is enough. LeanTLS builds on **macOS and Linux** only — it uses
`Std.Async` sockets, DNS and the system certificate bundle, and there is no Windows
support (and no AES-GCM).

## Building

```sh
lake build                     # checks every proof and spec (a few minutes)
lake build tlsget lbrowse      # builds the two binaries at .lake/build/bin/
```

The first `lake build` fails if any proof or spec fails, so a successful build means
every theorem listed in the README's "What's proved" section was checked on your
machine.

## Testing

There is no separate runtime test suite: **the tests are specs**, Lean theorems that
`lake build` checks. Running `lake build` re-checks all of them. The specs live under
`LeanTLS/Spec/` and `LeanBrowse/Spec/` (known-answer vectors from the relevant RFCs
and FIPS standards, the RFC 8448 handshake trace, X.509 path validation, and the
server negotiation). Add or update a spec for any behaviour you change.

Continuous integration runs the build, the proofs and the binaries on Linux and
macOS for every push and pull request (see `.github/workflows/ci.yml`). Please make
sure `lake build` passes locally before opening a PR.

## Submitting a change

1. **Branch** off `main` (or fork the repository).
2. Keep each pull request focused, and add or update a spec/theorem for behaviour you
   change — tests are theorems here.
3. Make sure `lake build` and `lake build tlsget lbrowse` pass.
4. Write a clear PR description: what changed, why, and how you verified it.
5. By contributing, you agree your contribution is licensed under this repository's
   license (see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest input (host, URL or certificate) that reproduces it. This is research code,
not production TLS: if you find a security-relevant weakness, you can report it
privately to **support@beneficialaifoundation.org** instead of a public issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers may
remove comments, commits or contributions that don't meet this standard.
