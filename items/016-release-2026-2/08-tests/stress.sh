#!/bin/sh
# H4's stress runner (bergdb 016-08, section 4.6): the stress programs of the level
# scripts, each as the level script starts it, with fresh seeds, in chunks of rounds,
# until a deadline. A tool of item 016, not a gate. Written 2026-11-03, not yet run:
# run it with SMOKE=1 first.
#
# Usage, from java/ of a clone, after sh build.sh:
#   sh .../stress.sh OUT DEADLINE BASE MAXJOBS [PROGRAM ...]
#   OUT       the output directory (made): one file per JVM, summary.txt, and
#             next-P (the next seed of program P)
#   DEADLINE  seconds since the epoch (date +%s); no chunk starts after it, and a
#             chunk that has started runs to its end
#   BASE      the first seed; the k-th program of the list uses seeds from
#             BASE + k * 100000 (PowerLossTest parses an int: keep BASE below 2^31
#             minus a million)
#   MAXJOBS   lanes: at most this many JVMs at once; the programs are dealt to the
#             lanes in turn, and each lane runs its programs' chunks in turn
#   PROGRAM   a subset of: dagfuzz restart restartdisk crash reclaim readers evinv
#             powerloss interrupt ltm (default: all)
# Environment: SMOKE=1 (one small chunk of each program, about 3 to 5 minutes);
#   JAVA_HOME (else the PATH's java); XMX (the heap of most JVMs, default 2g; 1g on
#   s1); EVXMX (EvictionInvariance's, default 3g); LTM (LargerThanMemory's flags).
# Prints STRESS OK, or STRESS FAILED with the programs that failed; exits 1 then.
# A program stops at its first failed chunk; its output stays in OUT.

OUT=${1:?OUT}
DEADLINE=${2:?DEADLINE}
BASE=${3:?BASE}
MAXJOBS=${4:?MAXJOBS}
shift 4
PROGRAMS=${*:-"dagfuzz restart restartdisk crash reclaim readers evinv powerloss interrupt ltm"}

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi
XMX=${XMX:-2g}
EVXMX=${EVXMX:-3g}
LTM=${LTM:-"-Xmx1g -Dkeys=4000000 -Dbudget=80 -Dsd=5000000 -Dupdates=50000 -Dgets=300000 -Dscans=10 -Drestarts=2 -Dmaxnode=14"}
LTM_SMOKE="-Xmx384m -Dkeys=500000 -Dbudget=20 -Dsd=2000000 -Dupdates=20000 -Dgets=100000 -Dscans=5 -Drestarts=1"
CP=build/bergdb.jar:build/stress
DONE='^Done: .* 0 failures'

[ -f build/bergdb.jar ] && [ -d build/stress ] || { echo "STRESS FAILED: no build here (sh build.sh)"; exit 1; }
mkdir -p "$OUT" || exit 1
SUM=$OUT/summary.txt

# rounds FULL SMOKE: the rounds of one chunk.
rounds() {
    if [ -n "$SMOKE" ]; then echo $2; else echo $1; fi
}

# run NAME PATTERN COMMAND...: runs the command, output in OUT/NAME.txt; true if the
# output has a line that matches PATTERN.
run() {
    name=$1; pat=$2; shift 2
    "$@" > "$OUT/$name.txt" 2>&1
    grep -q "$pat" "$OUT/$name.txt"
}

# chunk PROGRAM SEED: one chunk; writes the number of seeds it used to OUT/used-PROGRAM.
chunk() {
    c=$(cat "$OUT/count-$1" 2>/dev/null || echo 0)
    echo $((c + 1)) > "$OUT/count-$1"
    case $1 in
    dagfuzz)    # level1.sh, step 2: four node sizes
        r=$(rounds 300 5); echo $r > "$OUT/used-$1"
        run dagfuzz8-$2 "$DONE" $JAVA -ea -Dquiet=1 -Dmaxnode=8 -Dkeys=10 -Dn=40 -cp $CP bergdb.dag.DagFuzz $2 $r &&
        run dagfuzz14-$2 "$DONE" $JAVA -ea -Dquiet=1 -Dmaxnode=14 -Dops=12 -Dkeys=12 -Dn=60 -cp $CP bergdb.dag.DagFuzz $2 $r &&
        run dagfuzz30-$2 "$DONE" $JAVA -ea -Dquiet=1 -Dmaxnode=30 -Dops=20 -Dkeys=20 -Dn=40 -cp $CP bergdb.dag.DagFuzz $2 $r &&
        run dagfuzz62-$2 "$DONE" $JAVA -ea -Dquiet=1 -Dmaxnode=62 -Dops=50 -Dkeys=50 -Dn=40 -cp $CP bergdb.dag.DagFuzz $2 $r
        ;;
    restart)    # level2.sh, step 2: random configurations
        r=$(rounds 20 2); echo $r > "$OUT/used-$1"
        run restart-$2 "$DONE" $JAVA -ea -Xmx$XMX -cp $CP RestartStress $2 $r
        ;;
    restartdisk)    # level1.sh, step 4: on disk, restarts by full replay
        r=$(rounds 2 1); echo $r > "$OUT/used-$1"
        run restartdisk-$2 "$DONE" $JAVA -ea -Xmx$XMX -Dsd=200000000 -Dsessions=25 -Dkeys=3000 \
            -Dmaxnode=0 -Dfile=true -Ddir="$OUT/disk" -cp $CP RestartStress $2 $r &&
        rm -rf "$OUT/disk"
        ;;
    crash)    # level2.sh, step 5
        r=$(rounds 5 1); echo $r > "$OUT/used-$1"
        if [ $((c % 2)) = 0 ]; then
            run crash-$2 "$DONE" $JAVA -ea -Xmx$XMX -cp $CP bergdb.core.CrashTest $2 $r
        else
            run crash-node8-$2 "$DONE" $JAVA -ea -Xmx$XMX -Dmaxnode=8 -Dsd=500 -cp $CP bergdb.core.CrashTest $2 $r
        fi
        ;;
    reclaim)    # level3.sh, step 2
        r=$(rounds 20 2); echo $r > "$OUT/used-$1"
        run reclaim-$2 "$DONE" $JAVA -ea -Xmx$XMX -cp $CP bergdb.core.ReclaimStress $2 $r
        ;;
    readers)    # level3.sh, step 5, and level4.sh, step 4: one variant a chunk, in turn
        r=$(rounds 3 1); echo $r > "$OUT/used-$1"
        case $((c % 7)) in
        0) v="-Devict=random" ;;
        1) v="-Ddisk=1 -Devict=random" ;;
        2) v="-Dreaders=8 -Devict=random" ;;
        3) v="-Devict=every" ;;
        4) v="-Dreaders=4 -Devict=budget -Devictbudget=20000" ;;
        5) v="" ;;
        6) v="-Ddisk=1" ;;
        esac
        run readers-$2 "$DONE" $JAVA -ea -Xmx$XMX $v -cp $CP bergdb.core.ReclaimReaders $2 $r
        ;;
    evinv)    # level4.sh, step 2: one seed a run, one configuration a chunk, in turn
        echo 1 > "$OUT/used-$1"
        case $((c % 8)) in
        0) v="-Dsd=1000 -Dkeys=500 -Devery=100 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10" ;;
        1) v="-Drestarts=1 -Dsd=1000 -Dkeys=500 -Devery=100 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10" ;;
        2) v="-Drestarts=1 -Dretain=1 -Dsd=500 -Dkeys=100 -Devery=1 -Dlong=1 -Dn=1000" ;;
        3) v="-Dsd=10000 -Dkeys=500 -Devery=200 -Dmaxnode=14 -Dlong=1" ;;
        4) v="-Drestarts=1 -Dsd=100000 -Dkeys=1000 -Devery=200 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400" ;;
        5) v="-Drestarts=1 -Dsd=100 -Dkeys=100 -Devery=1 -Dlong=1 -Dempty=30 -Dnodel=20 -Dn=400" ;;
        6) v="-Dretain=1 -Dsd=1000 -Dkeys=500 -Devery=50 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10" ;;
        7) v="-Drestarts=1 -Dretain=1 -Dsd=10000 -Dkeys=1000 -Devery=100 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400" ;;
        esac
        n=2000; [ -n "$SMOKE" ] && n=300
        run evinv-$2 '^EVICTION INVARIANCE OK' $JAVA -ea -Xmx$EVXMX -Ddel=1 -Daudit=5 -Dn=$n $v \
            -Devictseed=$2 -cp $CP bergdb.core.EvictionInvariance $2 &&
        grep -q '^AUDIT: .* 0 failed' "$OUT/evinv-$2.txt"
        ;;
    powerloss)    # level3.sh, step 7
        r=$(rounds 2 1); echo $r > "$OUT/used-$1"
        if [ -n "$SMOKE" ]; then t=600; e=1; else t=1500; e=3; fi
        run powerloss-$2 '^POWERLOSS OK' $JAVA -ea -Xmx$XMX -cp $CP bergdb.core.PowerLossTest $2 $r $t $e
        ;;
    interrupt)    # level3.sh, step 9; no seed: the seed only names the output
        echo 1 > "$OUT/used-$1"
        sec=$(rounds 600 10)
        run interrupt-$2 '^INTERRUPT STRESS OK' $JAVA -ea -Xmx$XMX -cp $CP bergdb.core.InterruptStress \
            $sec "$OUT/interrupt" &&
        rm -rf "$OUT/interrupt"
        ;;
    ltm)    # level4.sh, step 6, with other sizes; no seed: the seed only names the output
        echo 1 > "$OUT/used-$1"
        if [ -n "$SMOKE" ]; then f=$LTM_SMOKE; else f=$LTM; fi
        run ltm-$2 '^LARGER THAN MEMORY OK' $JAVA -ea $f -Ddir="$OUT/ltm" -cp $CP bergdb.core.LargerThanMemory &&
        rm -rf "$OUT/ltm"
        ;;
    *)
        echo "unknown program $1" > "$OUT/unknown-$1.txt"; echo 1 > "$OUT/used-$1"; false
        ;;
    esac
}

# lane PROGRAM...: the programs' chunks in turn until the deadline (one round with SMOKE).
lane() {
    while [ "$(date +%s)" -lt "$DEADLINE" ]; do
        any=0
        for p in "$@"; do
            [ -f "$OUT/failed-$p" ] && continue
            [ "$(date +%s)" -lt "$DEADLINE" ] || break
            any=1
            s=$(cat "$OUT/next-$p")
            t0=$(date +%s)
            if chunk $p $s; then st=ok; else st=FAILED; touch "$OUT/failed-$p"; fi
            u=$(cat "$OUT/used-$p")
            echo "$p seed=$s seeds=$u $st $(( $(date +%s) - t0 )) s" >> "$SUM"
            echo $((s + u)) > "$OUT/next-$p"
        done
        [ $any = 1 ] || break
        [ -n "$SMOKE" ] && break
    done
}

{
    echo "stress.sh $(date '+%Y-%m-%d %H:%M') in $(pwd)"
    echo "JDK: $($JAVA -version 2>&1 | head -1)"
    echo "deadline $(date -r "$DEADLINE" '+%H:%M' 2>/dev/null || date -d "@$DEADLINE" '+%H:%M'), base $BASE, lanes $MAXJOBS, smoke ${SMOKE:-0}"
} >> "$SUM"

i=0
for p in $PROGRAMS; do
    echo $((BASE + i * 100000)) > "$OUT/next-$p"
    l=$((i % MAXJOBS))
    eval "LANE$l=\"\$LANE$l $p\""
    i=$((i + 1))
done
j=0
while [ $j -lt $MAXJOBS ]; do
    eval "ps=\$LANE$j"
    if [ -n "$ps" ]; then lane $ps & fi
    j=$((j + 1))
done
wait

if ls "$OUT"/failed-* > /dev/null 2>&1; then
    echo "STRESS FAILED: $(cd "$OUT" && ls failed-* | sed 's/^failed-//' | tr '\n' ' ')(summary: $SUM)"
    exit 1
fi
echo "STRESS OK: $(grep -c ' ok ' "$SUM") chunks (summary: $SUM)"
