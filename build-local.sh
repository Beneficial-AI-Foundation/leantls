#!/bin/sh
# Compile the C that Lean generated on VD into native binaries on this machine.
#   ./vd.sh push && ./vd.sh build   # check proofs + emit C on VD
#   ./build-local.sh                # pull C, leanc -> build-local/lbrowse, build-local/tlsget
set -e
cd "$(dirname "$0")"
SSH="ssh -o LogLevel=ERROR"
HOST=${VD_HOST:-VD}
RDIR=${RDIR:-$(basename "$(pwd)")}
mkdir -p c build-local/obj
rsync -az --delete -e "$SSH" "$HOST:$RDIR/.lake/build/ir/" c/
LEANC=${LEANC:-leanc}
find c -name '*.c' | while read -r f; do
  o="build-local/obj/$(echo "${f#c/}" | tr / _ | sed 's/\.c$/.o/')"
  [ "$o" -nt "$f" ] || "$LEANC" -c -O3 -DNDEBUG -o "$o" "$f"
done
OBJS=$(ls build-local/obj/*.o | grep -v -e '/TlsGet.o$' -e '/LBrowse.o$')
"$LEANC" -o build-local/lbrowse $OBJS build-local/obj/LBrowse.o
"$LEANC" -o build-local/tlsget $OBJS build-local/obj/TlsGet.o
echo "built: build-local/lbrowse build-local/tlsget"
