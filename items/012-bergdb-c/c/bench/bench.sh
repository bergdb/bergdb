#!/bin/sh
# The benchmarks of bergdb 012-15: C's bench-cbench (bench/cbench.c) and
# Java's JBench (bench/JBench.java) on the same workloads, in turns, each
# run a fresh process, each after a check that the machine is quiet.
#
# Usage: sh bench/bench.sh smoke|timed|extra|lto OUT
#   smoke   small sizes, one run each: the plumbing (about 30 s)
#   timed   the measurements of 012-15 (about an hour):
#           A. 1M keys: run C and Java in turns, 3 each
#           B. 10M keys: likewise; the last run's database is kept (sd 50 MB)
#           C. 10M keys at sd 200 MB: one C run, without reads, its database kept
#           D. startup: each of the two databases opened by C and Java in
#              turns, 3 each, after one untimed open (warm: the OS cache)
#   extra   1M keys, 2 runs each: the first sync alone (firstsync), gets
#           under a budget of 128 MB (above D), then opens of that database
#           under 16 and 128 MB budgets (about 10 minutes)
#   lto     timed's A, B, C and D with C's release build twice (012-17): as
#           built (-O2 -flto, run name c) and without link-time optimization
#           (LTO= build.sh into build/nolto: -O2 alone, run name co2), in
#           turns with Java (about 40 minutes)
#   OUT: a new directory for the outputs (outside the repository); data in
#   OUT/data.noindex (not indexed by Spotlight), deleted at the end.
# Builds first (build.sh, the Java harness, JBench). Each run's output is
# OUT/NN-NAME-LANG.txt with /usr/bin/time -l's counts at its end; the log of
# the whole is OUT/log.txt, which ends with "BENCH DONE". Summarize with
# python3 -I bench/summary.py OUT.
#
# Quiet: before each run, at most 20 minutes of waiting until no other JVM
# (but an editor's), no cc or clang, no cross.sh, before-commit.sh, night.sh,
# performance.sh, bergdb-run or Lean runs, and the CPU is at least 85 percent
# idle; a run that started without that is marked "quiet=no" in the log.
# Set JAVA_HOME (default /opt/homebrew/opt/openjdk).

set -e
C=$(cd "$(dirname "$0")/.." && pwd)
MODE=$1
OUT=$2
[ -n "$OUT" ] || { echo "usage: bench.sh smoke|timed|extra|lto OUT"; exit 2; }
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
export JAVA_HOME
mkdir -p "$OUT/data.noindex"
DATA=$OUT/data.noindex
LOG=$OUT/log.txt
JFLAGS=${JFLAGS:-"-Xms12g -Xmx12g"}
COOLDOWN=${COOLDOWN:-5}

log() {
    echo "$(date '+%Y-%m-%d %H:%M:%S') $*" | tee -a "$LOG"
}

# The build, before any timing.
cd "$C"
./build.sh > "$OUT/build.txt" 2>&1 || { log "BENCH FAILED: build"; exit 1; }
sh test/cross/java-build.sh >> "$OUT/build.txt" 2>&1 || { log "BENCH FAILED: java build"; exit 1; }
mkdir -p build/bench/java
"$JAVA_HOME/bin/javac" --release 17 -encoding UTF-8 -nowarn -cp build/java/classes \
    -d build/bench/java bench/JBench.java >> "$OUT/build.txt" 2>&1 || { log "BENCH FAILED: javac"; exit 1; }
if [ "$MODE" = lto ]; then
    LTO= BUILD=$C/build/nolto ./build.sh >> "$OUT/build.txt" 2>&1 || { log "BENCH FAILED: build without LTO"; exit 1; }
fi
CB=$C/build/release/bench-cbench
CBO2=$C/build/nolto/release/bench-cbench
JB="$JAVA_HOME/bin/java $JFLAGS -cp $C/build/java/classes:$C/build/bench/java bergdb.core.JBench"
log "build OK: $(git -C "$C" rev-parse --short HEAD) $(git -C "$C" status --short | wc -l | tr -d ' ') changed files; java $("$JAVA_HOME/bin/java" -version 2>&1 | head -1); JFLAGS $JFLAGS"

busy() {    # prints the heavy processes, if any
    ps -Ao pid=,args= | grep -v grep | grep -v "bench.sh" | grep -E \
        "bin/java |[ /]cc |clang|cross\.sh|before-commit|night\.sh|performance\.sh|bergdb-run|bergdb-dump|lake |/lean " \
        | grep -v -E "vscode|jdtls|languageserver" || true
}

idle() {    # the CPU's idle percent over one second
    top -l 2 -n 0 -s 1 | grep "CPU usage" | tail -1 | sed 's/.* \([0-9.]*\)% idle.*/\1/'
}

QUIET=yes
wait_quiet() {
    if [ "$MODE" = smoke ]; then QUIET="not checked"; return 0; fi
    i=0
    while [ $i -lt 240 ]; do
        bz=$(busy)
        id=$(idle)
        if [ -z "$bz" ] && [ "$(echo "$id >= 85" | bc)" = 1 ]; then
            QUIET="yes idle=$id"
            return 0
        fi
        [ $((i % 12)) = 0 ] && log "waiting for quiet: idle=$id; $(echo "$bz" | head -3 | cut -c1-120 | tr '\n' ';')"
        sleep 5
        i=$((i + 1))
    done
    QUIET="no idle=$(idle)"
}

N=0
run() {    # run NAME LANG ARGS...: one run, output in OUT/NN-NAME-LANG.txt
    name=$1 lang=$2
    shift 2
    N=$((N + 1))
    f=$OUT/$(printf %02d $N)-$name-$lang.txt
    sleep "$COOLDOWN"
    wait_quiet
    log "run $N $name $lang quiet=$QUIET: $*"
    if [ "$lang" = c ]; then
        /usr/bin/time -l "$CB" "$@" > "$f" 2>&1 || { log "BENCH FAILED: $f"; tail -5 "$f"; exit 1; }
    elif [ "$lang" = co2 ]; then
        /usr/bin/time -l "$CBO2" "$@" > "$f" 2>&1 || { log "BENCH FAILED: $f"; tail -5 "$f"; exit 1; }
    else
        /usr/bin/time -l $JB "$@" > "$f" 2>&1 || { log "BENCH FAILED: $f"; tail -5 "$f"; exit 1; }
    fi
    log "  done: $(grep -E 'real|maximum resident' "$f" | tr -s ' ' | tr '\n' ' ')"
}

extrastarts() {
    for bud in 16000000 128000000; do
        for i in 1 2; do
            for lang in java c; do
                run start-1m-budget$bud $lang start "$DATA/1m" keys=1000000 budget=$bud
            done
        done
    done
}

case $MODE in
smoke)
    A="keys=100000 upd=100000 single=10000 syncs=20 syncb=5 gets=100000 scans=10 low=4000000 rounds=2"
    COOLDOWN=0
    for lang in c java; do
        rm -rf "$DATA/s"
        run smoke $lang run "$DATA/s" $A
    done
    run smoke-start c start "$DATA/s" keys=100000
    run smoke-start java start "$DATA/s" keys=100000
    ;;
timed)
    # A. 1M keys
    A="keys=1000000 upd=1000000 single=100000 syncs=200 syncb=50 gets=1000000 scans=100 low=16000000 rounds=3"
    for i in 1 2 3; do
        for lang in java c; do
            rm -rf "$DATA/1m"
            run 1m $lang run "$DATA/1m" $A
        done
    done
    rm -rf "$DATA/1m"
    # B. 10M keys, sd 50 MB; the last database is kept for D
    B="keys=10000000 upd=2000000 single=100000 syncs=200 syncb=50 gets=1000000 scans=100 low=16000000 rounds=3"
    for i in 1 2 3; do
        for lang in java c; do
            rm -rf "$DATA/10m"
            run 10m $lang run "$DATA/10m" $B
        done
    done
    # C. 10M keys, sd 200 MB, as 007-05's: 3M updates
    rm -rf "$DATA/10m-sd200"
    run 10m-sd200-make c run "$DATA/10m-sd200" keys=10000000 upd=3000000 sd=200000000
    # D. startup, warm
    for db in 10m 10m-sd200; do
        run start-$db-warmup c start "$DATA/$db" keys=10000000
        for i in 1 2 3; do
            for lang in java c; do
                run start-$db $lang start "$DATA/$db" keys=10000000
            done
        done
    done
    ;;
extra)
    # After the timed part: the first sync timed alone, gets under a budget
    # above D (128 MB), and opens under budgets (the open's own peak)
    E="keys=1000000 upd=1000000 single=100000 syncs=200 syncb=50 gets=1000000 low=128000000 rounds=3 firstsync=1"
    for i in 1 2; do
        for lang in java c; do
            rm -rf "$DATA/1m"
            run 1m-extra $lang run "$DATA/1m" $E
        done
    done
    extrastarts
    ;;
extrastarts)
    # the opens of extra alone, on extra's database left in OUT
    extrastarts
    ;;
lto)
    # timed's, with C's release build with and without -flto (012-17)
    A="keys=1000000 upd=1000000 single=100000 syncs=200 syncb=50 gets=1000000 scans=100 low=16000000 rounds=3"
    for i in 1 2 3; do
        for lang in java c co2; do
            rm -rf "$DATA/1m"
            run 1m $lang run "$DATA/1m" $A
        done
    done
    rm -rf "$DATA/1m"
    B="keys=10000000 upd=2000000 single=100000 syncs=200 syncb=50 gets=1000000 scans=100 low=16000000 rounds=3"
    for i in 1 2 3; do
        for lang in java c co2; do
            rm -rf "$DATA/10m"
            run 10m $lang run "$DATA/10m" $B
        done
    done
    for lang in c co2; do
        rm -rf "$DATA/10m-sd200"
        run 10m-sd200-make $lang run "$DATA/10m-sd200" keys=10000000 upd=3000000 sd=200000000
    done
    for db in 10m 10m-sd200; do
        run start-$db-warmup c start "$DATA/$db" keys=10000000
        for i in 1 2 3; do
            for lang in java c co2; do
                run start-$db $lang start "$DATA/$db" keys=10000000
            done
        done
    done
    ;;
*)
    echo "usage: bench.sh smoke|timed|extra|lto OUT"
    exit 2
    ;;
esac
rm -rf "$DATA"
log "BENCH DONE"
