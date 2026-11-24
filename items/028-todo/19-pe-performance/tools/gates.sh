#!/bin/sh
# bergdb 028-19: the gates of the night's change, each in its own clone of the branch 028-19
# of CLONE (default /Users/f/fl/bench/2026-11-24/todo/c19), at nice 10, at the same time:
# level1.sh, level2.sh, level3.sh, level4.sh and kill-restart.sh 1000; then StreamDigest quick
# with main's build (BASE, the clone main beside tools/) against the change's. Functional
# tests only. Each gate's output in OUT/NAME.txt, a line a gate in OUT/log.txt; the clones are
# removed at the end.
# Usage: sh gates.sh OUT
set -u
OUT=$1
D=$(cd "$(dirname "$0")/.." && pwd)
CLONE=${CLONE:-/Users/f/fl/bench/2026-11-24/todo/c19}
BASE=${BASE:-$D/main}
JAVA=${JAVA:-/opt/homebrew/opt/openjdk/bin/java}
mkdir -p "$OUT"
log() { echo "$(date '+%Y-%m-%d %H:%M:%S') $*" >> "$OUT/log.txt"; }
head=$(git -C "$CLONE" rev-parse --short HEAD)
log "gates of $head"
for g in level1 level2 level3 level4 kill; do
    C=$OUT/clone-$g
    rm -rf "$C"
    git clone -q "$CLONE" "$C" && git -C "$C" checkout -q "$head"
    cp -cR /Users/f/fl/repos/bergdb/lean/.lake "$C/lean/" 2>/dev/null
    cp -cR /Users/f/fl/repos/bergdb/lean/contract/.lake "$C/lean/contract/" 2>/dev/null
done
run() {  # NAME COMMAND...
    name=$1; shift
    log "start $name"
    (cd "$OUT/clone-$name" && nice -n 10 "$@") > "$OUT/$name.txt" 2>&1
    log "end $name rc=$? $(grep -E 'LEVEL [0-9] (OK|FAILED)|KILL RESTART (OK|FAILED)|FAILED' "$OUT/$name.txt" | tail -1)"
}
run level1 sh java/stress/level1.sh &
run level2 sh java/stress/level2.sh &
run level3 sh java/stress/level3.sh &
run level4 sh java/stress/level4.sh &
run kill sh java/stress/kill-restart.sh 1000 &
wait
# StreamDigest: one compiled copy of the class, main's, on both jars (its header).
B=$BASE/java/build
N=$OUT/clone-level1/java/build
log "start digest"
nice -n 10 "$JAVA" -cp "$B/bergdb.jar:$B/stress" bergdb.core.StreamDigest quick > "$OUT/digest-base.txt" 2>&1
nice -n 10 "$JAVA" -cp "$N/bergdb.jar:$B/stress" bergdb.core.StreamDigest quick > "$OUT/digest-cur.txt" 2>&1
"$JAVA" -cp "$N/bergdb.jar:$B/stress" bergdb.core.StreamDigest compare "$OUT/digest-base.txt" "$OUT/digest-cur.txt" > "$OUT/digest.txt" 2>&1
log "end digest rc=$? $(tail -1 "$OUT/digest.txt")"
rm -rf "$OUT"/clone-*          # the clones and their data: tens of GB; the outputs stay
log "GATES END"
