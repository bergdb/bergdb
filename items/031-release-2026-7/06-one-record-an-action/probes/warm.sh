#!/bin/sh
# bergdb 031-06, landing step 3 (the review's F4): WarmProbe, the versions read from the
# stream under the write lock by the records that carry a step, without and with the
# warm-up of the step's reads before the lock, on databases larger than their cache budget
# (5 MB); each pair of runs must give the same stream. Usage, from the repository's root,
# after java/build.sh:
#   sh items/031-release-2026-7/06-one-record-an-action/probes/warm.sh OUT
# Kind: functional (counts; no time is measured).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT" $P/WarmProbe.java || exit 1
C="-cp $OUT:$J"
w() { echo "== $*"; java -ea -Xmx6g "$@" 2>&1 | grep -v "^\s*at "; }
w $C bergdb.core.WarmProbe 100000 200 20000 200 20 5000000
w $C bergdb.core.WarmProbe 100000 200 20000 200 20 5000000 8
w -Dmaint=50 $C bergdb.core.WarmProbe 100000 200 20000 200 20 5000000
w $C bergdb.core.WarmProbe 20000 1000 1500 300000 200 5000000
w -Dputs=200 -Dhot=20000 $C bergdb.core.WarmProbe 20000 1000 1500 20000 200 5000000
echo WARM DONE
