#!/bin/sh
# bergdb 031-06, review 3, W1 and W2: WarmAheadProbe (the warm-up of a commit's step with
# several writers: the steps whose scan loaded under the lock, the warm-ups' scans, the
# loads in all), review-3-probes/MwWarmProbe's cases, and HandoverWarmProbe (maintain()'s
# warm-up scans while it gives way to commits, and the rows that publishWarm copies).
# Usage, from the repository's root, after java/build.sh (JAR= another jar, e.g. main's):
#   sh items/031-release-2026-7/06-one-record-an-action/probes/warmahead.sh OUT
# Kind: functional (counts; no time is measured; the counts vary with the threads).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT" $P/WarmAheadProbe.java $P/HandoverWarmProbe.java || exit 1
C="-cp $OUT:$J"
w() { echo "== $*"; java -ea -Xmx6g "$@" 2>&1 | grep -v "^\s*at "; }
for n in 1 2 4; do
    w $C bergdb.core.WarmAheadProbe 100000 200 20000 200 20 5000000 $n
done
for n in 2 4 8; do
    w -Dhold=50000 -Dpause=200000 $C bergdb.core.WarmAheadProbe 100000 200 20000 200 20 5000000 $n
done
w $C bergdb.core.HandoverWarmProbe 50000 200 20000 200 20 5000000 2 2000
w $C bergdb.core.HandoverWarmProbe 50000 200 20000 200 20 5000000 1 300
echo WARM AHEAD DONE
