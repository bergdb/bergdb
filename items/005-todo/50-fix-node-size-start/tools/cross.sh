#!/bin/sh
# bergdb 005-50: CrossNodeSize, release 2026.1 (rel) and the prototype (proto) on the same
# databases. Usage: sh cross.sh SCRATCH, where SCRATCH has jars/rel.jar and jars/proto.jar;
# it compiles CrossNodeSize against each and works in SCRATCH/cross/.
set -u
S=$1
T=$(cd "$(dirname "$0")" && pwd)
W=$S/cross
rm -rf "$W"
mkdir -p "$W"
for v in rel proto; do
    mkdir -p "$W/cls-$v"
    javac --release 17 -nowarn -cp "$S/jars/$v.jar" -d "$W/cls-$v" "$T/CrossNodeSize.java" || exit 1
done
run() { v=$1; shift; java -Xmx1g -cp "$W/cls-$v:$S/jars/$v.jar" bergdb.core.CrossNodeSize "$@" | sed "s|$W/||; s|^|$v |"; }

echo "X1. A database of release 2026.1 (no node size in its meta blocks), then the prototype."
run rel write "$W/x1" 30 0 20000
run rel meta "$W/x1"
run proto start "$W/x1" 8 20000
run proto start "$W/x1" 30 20000
run proto write "$W/x1" 30 20000 20100
run proto meta "$W/x1"
run proto start "$W/x1" 8 20100
run proto start "$W/x1" 62 20100
run rel start "$W/x1" 30 20100

echo "X2. A database of the prototype, then release 2026.1, then the prototype."
run proto write "$W/x2" 30 0 20000
run proto meta "$W/x2"
run rel start "$W/x2" 30 20000
run rel write "$W/x2" 30 20000 20100
run rel meta "$W/x2"
run proto start "$W/x2" 8 20100
run proto start "$W/x2" 30 20100
