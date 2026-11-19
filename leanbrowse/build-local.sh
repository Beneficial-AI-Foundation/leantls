#!/bin/sh
# Compile the C that Lean generated on VD into native binaries on this machine.
#   ./vd.sh all        # push sources, check proofs + emit C on VD, pull C to ./c
#   ./build-local.sh   # leanc: C -> build-local/lbrowse (and build-local/tlsget)
set -e
cd "$(dirname "$0")"
SSH="ssh -o LogLevel=ERROR"
HOST=${VD_HOST:-VD}
mkdir -p c/leantls c/leanbrowse build-local/obj
rsync -az --delete -e "$SSH" "$HOST:leantls/.lake/build/ir/" c/leantls/
rsync -az --delete -e "$SSH" "$HOST:leanbrowse/.lake/build/ir/" c/leanbrowse/
LEANC=${LEANC:-leanc}
compile() { # $1 = c dir, $2 = obj prefix
  find "$1" -name '*.c' | while read -r f; do
    o="build-local/obj/$2_$(echo "${f#$1/}" | tr / _ | sed 's/\.c$/.o/')"
    [ "$o" -nt "$f" ] || "$LEANC" -c -O3 -DNDEBUG -o "$o" "$f"
  done
}
compile c/leantls tls
compile c/leanbrowse br
# lbrowse = all leantls modules except its Main + all leanbrowse modules
"$LEANC" -o build-local/lbrowse $(ls build-local/obj/tls_*.o | grep -v '/tls_Main.o$') build-local/obj/br_*.o
"$LEANC" -o build-local/tlsget build-local/obj/tls_*.o
echo "built: build-local/lbrowse build-local/tlsget"
