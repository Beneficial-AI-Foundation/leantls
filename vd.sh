#!/bin/sh
# Usage: ./vd.sh push | build | pull | all
# push: local source -> VD:~/<project> ; build: lake build on VD (type-checks all proofs)
# pull: generated C from VD -> ./c/
set -e
HOST=${VD_HOST:-VD}
RDIR=$(basename "$(pwd)")
SSH="ssh -o LogLevel=ERROR"
# VD (old glibc) cannot run Lean's bundled clang: it only checks proofs + emits C; we compile C locally.
DEFAULT_TARGETS=${DEFAULT_TARGETS:-"LeanTLS LeanBrowse +TlsGet +LBrowse"}
push()  { rsync -az --delete -e "$SSH" --exclude .lake --exclude c --exclude build-local ./ "$HOST:$RDIR/"; }
build() { $SSH "$HOST" "cd $RDIR && PATH=\$HOME/.elan/bin:\$PATH lake build ${TARGETS:-$DEFAULT_TARGETS} 2>&1"; }
pull()  { mkdir -p c && rsync -az --delete -e "$SSH" "$HOST:$RDIR/.lake/build/ir/" c/; }
case "${1:-all}" in
  push) push;; build) build;; pull) pull;;
  all) push; build; pull;;
  *) echo "usage: $0 push|build|pull|all" >&2; exit 1;;
esac
