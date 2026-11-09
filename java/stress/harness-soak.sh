#!/bin/sh
# Long runs of the Pub layer's randomized harnesses against their references
# (bergdb 020-17): many seeds and larger sizes than the night's runs, until a
# time or for a number of rounds. Not a commit gate, not a step of night.sh
# by itself; a soak, for a spare machine (the VPS s1) or a quiet night.
#
# Usage: java/stress/harness-soak.sh [-j JAR] [-o DIR] [-u HH:MM] [-r ROUNDS]
#            [-b BASE] [-c CPUS] [-x HEAP] [-t SECONDS] [-h NAMES]
#   -j JAR      the jar (default build/bergdb.jar; build it first with build.sh)
#   -o DIR      the output directory (default build/harness-soak); refused if it
#               holds a soak's results
#   -u HH:MM    starts no job at or after this time of day (default: none)
#   -r ROUNDS   at most this many rounds (default 1, or none with -u)
#   -b BASE     the first seed (default the date as YYYYMMDD times 1000)
#   -c CPUS     Linux only: the CPUs of taskset, such as 1 or 0-1; "auto"
#               (the default on Linux) takes CPU 1 while another java process
#               runs on the machine and every CPU while none does, decided
#               before each job; "all" never pins
#   -x HEAP     the JVM's -Xmx (default 1g)
#   -t SECONDS  the time limit of a job, a hang beyond it (default 1800)
#   -h NAMES    the harnesses, comma-separated (default all): h2, h3, h4,
#               obj, dobj
#
# A round runs one job of each harness, with the seed BASE + round and sizes
# that cycle with the round (lists below, of coprime lengths, so that the
# combinations vary): each job is its own JVM with -ea, through bergdb.dev.Run.
# The jobs that start databases (h2, h3, h4) also cycle through the Core's
# eviction schedules and its audit, by their system properties (Eviction,
# Audit): the default (the capacity controller, a cache of a fifth of the
# heap), every (every detachable object after every transaction), random,
# values, and a budget of 20,000 bytes; the audit after every 10th
# transaction in one job of three. A failed audit prints "AUDIT FAILED". In
# half the rounds, h2 and h4 set the startup distance to 400,000 bytes (the
# harnesses' property harness.sd), so that the nodes written before it can be
# evicted and reclaim cuts (with the Pub API's 5 MB at least, it does not in
# a harness's run).
#   h2    IndexHarness (020-10, section 9.1): SEED STEPS THREADS 1 KEYS WIDE
#         DIR RESTART: operations 400 to 5,000 (2,000 with KEYS), writer
#         threads 1 to 8, 0 to 400 more object names (several build steps and
#         scan pages), the wide variant (up to 8 levels, the parent and a
#         neighbour directory, rw() reads before it writes), in memory or in a
#         directory, a restart every 100 to 500 operations or the random ones.
#   h3    IndexJobsHarness (020-10, section 9.3): random runs, SEED RUNS
#         OBJECTS, objects 30 to 20,000, the runs scaled to the size; its
#         runs take the seeds SEED to SEED + RUNS - 1, so SEED is the round's
#         seed times 1000; its bounds of a join and a cleanup multiplied by
#         1 + OBJECTS / 2000, and by 5 with the audit (harness.slow).
#   h4    PrimaryHarness (020-10, section 9.4): SEED STEPS 1 RECLAIM, steps 500
#         to 20,000, reclaim on in half the jobs, always with harness.sd.
#   obj   ObjectFormatTester's H0a and H0b against its reference codec (020-08,
#         section 6.3): SEED TREES SAMPLES.
#   dobj  DataObjectsTester's properties R1 to R3 (020-09, section 8.5): SEED
#         COUNT 1, some objects through a database.
# A job passes if the JVM exits with 0, prints the harness's line of success
# (for h3, "0 kinds of findings, 0 of known faults") and no "AUDIT FAILED"; else FAIL, or
# TIMEOUT past -t. A passing job whose output has "Exception in thread", an
# OutOfMemoryError or an hs_err file is WARN: a thread died and the harness
# did not see it. The output of each job that does not pass is kept in
# DIR/fail/; that of a passing job is deleted, its last line kept.
#
# Files in DIR: results.tsv (a line per job: the time, the job's number, the
# harness, its arguments, the result, the seconds, the output's last line),
# summary.txt (made again after each job: the counts by harness and result,
# and every job that did not pass), fail/ (with each one's command), soak.log.
# A file DIR/STOP ends the soak after the job that runs. The last line is
# HARNESS SOAK OK, or HARNESS SOAK FAILED with the exit status 1 if a job
# failed or hung (WARN does not fail it).
#
# On s1 (bergdb 020-17), started under nohup until 18:00:
#   nohup sh harness-soak.sh -j bergdb.jar -o soak -u 18:00 > soak.out 2>&1 &
# and checked with one command:
#   ssh root@s1 cat /root/bench/2026-11-09-s17/soak/summary.txt

ORIG=$(pwd)
JAVADIR=$(cd "$(dirname "$0")/.." && pwd)

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

JAR=$JAVADIR/build/bergdb.jar
OUT=$JAVADIR/build/harness-soak
UNTIL=
ROUNDS=
BASE=$(date +%Y%m%d)000
CPUS=auto
HEAP=1g
LIMIT=1800
NAMES=h2,h3,h4,obj,dobj
while getopts j:o:u:r:b:c:x:t:h: opt; do
    case $opt in
    j) JAR=$OPTARG ;;
    o) OUT=$OPTARG ;;
    u) UNTIL=$(echo "$OPTARG" | tr -d :) ;;
    r) ROUNDS=$OPTARG ;;
    b) BASE=$OPTARG ;;
    c) CPUS=$OPTARG ;;
    x) HEAP=$OPTARG ;;
    t) LIMIT=$OPTARG ;;
    h) NAMES=$OPTARG ;;
    *) sed -n '2,25p' "$0"; exit 2 ;;
    esac
done
if [ -z "$ROUNDS" ]; then
    if [ -n "$UNTIL" ]; then ROUNDS=1000000; else ROUNDS=1; fi
fi
case $JAR in /*) ;; *) JAR=$ORIG/$JAR ;; esac
case $OUT in /*) ;; *) OUT=$ORIG/$OUT ;; esac
[ -f "$JAR" ] || { echo "harness-soak: no jar $JAR"; exit 2; }
if [ -s "$OUT/results.tsv" ]; then
    echo "harness-soak: $OUT has the results of a soak; take another -o, or delete them"
    exit 2
fi

TIMEOUT=
if command -v timeout > /dev/null 2>&1; then TIMEOUT="timeout $LIMIT"; fi
HAS_TASKSET=
if command -v taskset > /dev/null 2>&1; then HAS_TASKSET=1; fi

mkdir -p "$OUT/fail" "$OUT/run"
rm -f "$OUT"/run/* "$OUT/STOP"
: > "$OUT/results.tsv"
LOGF=$OUT/soak.log
STARTED=$(date '+%Y-%m-%d %H:%M:%S')
echo "harness-soak: started $STARTED, jar $JAR, seeds from $BASE, until ${UNTIL:-none}, rounds $ROUNDS, cpus $CPUS, -Xmx$HEAP, limit ${LIMIT}s, harnesses $NAMES" | tee "$LOGF"
"$JAVA" -version >> "$LOGF" 2>&1

# The word number $1 (from 0, cyclic) of the words that follow.
pick() {
    i=$1
    shift
    n=$#
    k=$((i % n + 1))
    eval echo "\${$k}"
}

# The taskset prefix of the next job, by -c.
pin() {
    [ -n "$HAS_TASKSET" ] || return 0
    case $CPUS in
    all) ;;
    auto)
        # Other java processes on the machine (not this soak's, which has none
        # running between jobs): one CPU; none: every CPU.
        if pgrep -x java > /dev/null 2>&1; then echo "taskset -c 1"; fi ;;
    *) echo "taskset -c $CPUS" ;;
    esac
}

summary() {
    {
        echo "harness-soak (bergdb 020-17): started $STARTED, now $(date '+%Y-%m-%d %H:%M:%S'), until ${UNTIL:-none}"
        echo "jar $JAR"
        echo "seeds from $BASE; rounds done $DONE; jobs $N; $(cat "$OUT/STATE" 2>/dev/null)"
        echo
        awk -F'\t' '
            { runs[$3]++; res[$3 "\t" $5]++; secs[$3] += $6; all[$5]++ }
            END {
                printf "%-6s %6s %6s %6s %6s %6s %8s\n", "", "jobs", "OK", "FAIL", "TIMEOUT", "WARN", "seconds"
                split("h2 h3 h4 obj dobj", order, " ")
                for (i = 1; i <= 5; i++) {
                    h = order[i]
                    if (!(h in runs)) continue
                    printf "%-6s %6d %6d %6d %6d %6d %8d\n", h, runs[h], res[h "\tOK"], res[h "\tFAIL"], res[h "\tTIMEOUT"], res[h "\tWARN"], secs[h]
                }
                printf "\nALL: %d jobs, %d OK, %d FAIL, %d TIMEOUT, %d WARN\n", NR, all["OK"], all["FAIL"], all["TIMEOUT"], all["WARN"]
            }' "$OUT/results.tsv"
        echo
        echo "Jobs that did not pass (output in fail/; repeat from java/ with the command):"
        awk -F'\t' '$5 != "OK" { printf "* %s job %s %s %s: %s, %ss: %s\n", $1, $2, $3, $5, $4, $6, $7 }' "$OUT/results.tsv"
    } > "$OUT/summary.tmp"
    mv "$OUT/summary.tmp" "$OUT/summary.txt"
}

N=0
DONE=0

# Runs one job: $1 the harness's short name, $2 the success pattern (grep -E),
# the rest the class and its arguments.
job() {
    name=$1
    okpat=$2
    shift 2
    N=$((N + 1))
    f=$OUT/run/$N-$name.txt
    p=$(pin)
    cmd="$JAVA -ea -Xmx$HEAP $PROPS -cp $JAR bergdb.dev.Run $*"
    echo "$(date +%H:%M:%S) job $N $name: ${p:+$p }$*" >> "$LOGF"
    t0=$(date +%s)
    (cd "$OUT/run" && $TIMEOUT $p $cmd) > "$f" 2>&1
    st=$?
    t1=$(date +%s)
    if [ $st -eq 124 ] && [ -n "$TIMEOUT" ]; then
        result=TIMEOUT
    elif [ $st -ne 0 ] || ! grep -Eq "$okpat" "$f" || grep -q 'AUDIT FAILED' "$f"; then
        result=FAIL
    elif grep -Eq 'Exception in thread|OutOfMemoryError' "$f" || ls "$OUT"/run/hs_err* > /dev/null 2>&1; then
        result=WARN
    else
        result=OK
    fi
    # The output's last line, but PrimaryHarness's "OK" (its counts are the line before).
    last=$(grep -v -e '^[[:space:]]*$' -e '^PrimaryHarness OK$' "$f" | tail -1)
    if [ $result != OK ]; then
        # The first line that says what failed, if one does.
        first=$(grep -E -m1 '^\* |AUDIT FAILED|Error|Exception' "$f")
        [ -n "$first" ] && last=$first
    fi
    last=$(echo "$last" | cut -c1-300 | tr '\t' ' ')
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date '+%m-%d %H:%M:%S')" "$N" "$name" "${PROPS:+$PROPS }$*" "$result" "$((t1 - t0))" "$last" >> "$OUT/results.tsv"
    if [ $result = OK ]; then
        rm -f "$f"
    else
        { echo "command (from java/): $cmd"; echo "exit status $st, $((t1 - t0)) s, ${p:-no taskset}"; echo; cat "$f"; } > "$OUT/fail/$N-$name.txt"
        rm -f "$f"
        mv "$OUT"/run/hs_err* "$OUT/fail/" 2> /dev/null
        echo "$(date +%H:%M:%S) job $N $name: $result (fail/$N-$name.txt)" | tee -a "$LOGF"
    fi
    summary
}

# Whether to start no more jobs: STOP, or the time is -u's.
over() {
    [ -f "$OUT/STOP" ] && return 0
    [ -n "$UNTIL" ] && [ "$(date +%H%M)" -ge "$UNTIL" ] && return 0
    return 1
}

has() {
    case ",$NAMES," in *",$1,"*) return 0 ;; esac
    return 1
}

r=0
while [ $r -lt "$ROUNDS" ]; do
    seed=$((BASE + r))
    echo "round $r, seed $seed" > "$OUT/STATE"
    evict=$(pick $r "" "-Devict=every" "-Devict=random -Devictseed=$seed" "-Devict=values" "-Devict=budget -Devictbudget=20000")
    audit=$(pick $r "" "-Daudit=10" "")
    sd=$(pick $((r / 5)) "" "-Dharness.sd=400000")
    PROPS="$evict${audit:+ $audit}"
    PROPS=${PROPS# }
    if has h2 && ! over; then
        steps=$(pick $r 400 2000 5000 1000 3000)
        threads=$(pick $r 1 4 2 8 1 3)
        keys=$(pick $r 0 300 0 150 400 0 60)
        [ $keys -gt 0 ] && [ $steps -gt 2000 ] && steps=2000
        wide=$(pick $((r / 2)) 0 1)
        disk=$(pick $((r / 3)) 0 0 1)
        restart=$(pick $r 500 100 0 250)
        saved=$PROPS
        PROPS="$PROPS${sd:+ $sd}"
        PROPS=${PROPS# }
        job h2 '^IndexHarness OK' bergdb.pubimp.IndexHarness $seed $steps $threads 1 $keys $wide $disk $restart
        PROPS=$saved
    fi
    if has h3 && ! over; then
        objects=$(pick $r 30 500 110 2000 260 5000 61 20000)
        # About 40 s on one CPU of s1: a run of 500 objects 0.2 s, of 20,000
        # objects 5 s (2026-11-09).
        runs=$((200000 / (objects + 400)))
        [ $runs -lt 2 ] && runs=2
        [ $runs -gt 200 ] && runs=200
        # The harness's bounds of a join and a cleanup (10 s, 5 s) are for the night's 500
        # objects: harness.slow multiplies them, by the size and five times with the audit.
        slow=$((1 + objects / 2000))
        [ -n "$audit" ] && slow=$((slow * 5))
        saved=$PROPS
        [ $slow -gt 1 ] && PROPS="$PROPS -Dharness.slow=$slow"
        PROPS=${PROPS# }
        job h3 'IndexJobsHarness: seed .* 0 kinds of findings, 0 of known faults' bergdb.pubimp.IndexJobsHarness $((seed * 1000)) $runs $objects
        PROPS=$saved
    fi
    if has h4 && ! over; then
        steps=$(pick $r 5000 500 10000 2000 20000)
        reclaim=$(pick $((r / 2)) 1 0)
        saved=$PROPS
        # Reclaim cuts only with a small startup distance (harness.sd).
        hsd=$sd
        [ $reclaim = 1 ] && hsd="-Dharness.sd=400000"
        PROPS="$PROPS${hsd:+ $hsd}"
        PROPS=${PROPS# }
        job h4 '^PrimaryHarness OK' bergdb.pubimp.PrimaryHarness $seed $steps 1 $reclaim
        PROPS=$saved
    fi
    PROPS=
    if has obj && ! over; then
        trees=$(pick $r 2000 5000 500)
        job obj '^ObjectFormatTester: seed' bergdb.pubimp.ObjectFormatTester $seed $trees 40
    fi
    if has dobj && ! over; then
        count=$(pick $r 5000 20000)
        job dobj ', 0 failed;' bergdb.pubimp.DataObjectsTester $seed $count 1
    fi
    over && break
    r=$((r + 1))
    DONE=$r
done
DONE=$r
echo "ended $(date '+%Y-%m-%d %H:%M:%S') after $r rounds" > "$OUT/STATE"
summary
echo "harness-soak: ended $(date '+%Y-%m-%d %H:%M:%S'), $N jobs" | tee -a "$LOGF"
grep '^ALL' "$OUT/summary.txt"
# The last line, for night.sh's report: OK unless a job failed or hung.
if grep -q '^ALL: .* 0 FAIL, 0 TIMEOUT' "$OUT/summary.txt"; then
    echo "HARNESS SOAK OK: $N jobs, $r rounds"
else
    echo "HARNESS SOAK FAILED (summary: $OUT/summary.txt)"
    exit 1
fi
