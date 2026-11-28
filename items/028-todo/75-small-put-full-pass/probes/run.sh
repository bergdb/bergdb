#!/bin/sh
# bergdb 028-75: how the runs in ../runs/ were made, from the repository's root, on main with
# prototype.diff applied (git apply), after java/build.sh. OUT is a directory for the classes.
# A switch picks the prototype's pass rule: none, the table's last done row ('rows');
# -Dproto.f=true, two counts a record would carry ('counts'); -Dproto.x=true, the exact live
# stream bytes ('exact'); -Dproto.b=true adds B1; -Dproto.m=true M2' (a commit's iteration
# stepped by the calls within its allowance, a pass over it); -Dproto.knum=4 k = 2 (3, k = 1.5,
# by default); -Dproto.off=true is main's rule.
# Usage: sh items/028-todo/75-small-put-full-pass/probes/run.sh OUT [switches]
# Kind: functional (bytes only).
OUT=${1:?out dir}
shift
J=java/build/bergdb.jar
P=items/028-todo/75-small-put-full-pass/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT" $P/*.java items/033-bugs/probes/*.java || exit 1
for c in "20000 100 1000 1000000" "20000 100 1000 50000000" "20000 1000 1000 1000000" \
        "100000 200 100000 1000000" "200000 20 10000 1000000" "2000 100 1000 1000000"; do
    java "$@" -ea -Xmx2g -cp "$OUT:$J" bergdb.core.LiveProbe $c
done
java "$@" -ea -Xmx2g -cp "$OUT:$J" bergdb.core.PassRoundsProbe 20000 100 1000 4 1000000
java "$@" -ea -Xmx2g -cp "$OUT:$J" bergdb.core.PassRoundsProbe 100000 200 100000 8 1000000
for a in "4000 20000" "20000 20000"; do
    java "$@" -ea -cp "$OUT:$J" bergdb.core.HoleProbe $a
done
java "$@" -ea -cp "$OUT:$J" bergdb.core.TwoStretchProbe 390000 390000 390000 10000 20000
java "$@" -ea -cp "$OUT:$J" bergdb.core.TwoStretchProbe 395000 393000 380000 196000 20000 after
