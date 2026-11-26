#!/bin/sh
# The large reclaim history (bergdb 028-43), only in week.sh's functional set.
# Kind: functional: fixed numbers of keys, epochs, reads and restarts decide a pass.
# Time is printed as information; waits and a 12-hour JVM limit are hang guards.
# No quiet-machine check.
#
# Usage: sh java/stress/large.sh [full|quick] [SEED]
#   full (default): 10 million keys, 40 epochs of four-key transactions; on a Mac with
#     32 GB (F53), 79 minutes with seed 20778's local order (028-43), 5.5 hours with seed
#     20782's (2026-11-26, alone on the machine), an order that, as most seeds' orders,
#     writes about 3.8 times 20778's bytes (028-63); quick: 1 million keys, 16 epochs,
#     about 3 minutes (seed 20782).
#   SEED defaults to the date (YYYYMMDD); week.sh passes its day's seed explicitly.
#   On macOS, caffeinate -i sh java/stress/large.sh full SEED keeps the machine awake.
#
# Checks every returned value against a constant-history-space oracle; complete forward
# and backward scan pages; older snapshots within retention, the exact available frontier
# and refusal before it; actual file cuts; the kept stream's fixed space envelope over
# many sweeps; two clean restarts; SIGKILL of a child while writing and recovery of a whole
# prefix including every synced batch; a full oracle scan after each restart and at the end.
# A simulated clock gives short retention (one tenth of an epoch); reclaim runs at the
# normal commits, with its default fraction, without a maintenance drive. File sizes are
# capped at 2 GB, so physical rounding adds at most 2 GB to the logical bound (028-43).
# The capacity controller stays on, with a 3 GB resident cache (quick: 300 MB).
# Kept bytes have a bound: 8 L0 + 2 GB, with L0 the fresh filled stream, which the seed's
# key order sets: about 2 to 7.3 GB in full mode (028-63); a fill of more than 1,000 bytes
# a key fails.
#
# Builds and copies the jar and stress classes into build/large/MODE-SEED-TIME/bin/, so
# another build does not change a running test. Logs (out.txt, child.txt, journal.txt),
# source.txt and fresh.txt stay there. Successful data is deleted unless KEEPDATA=1;
# a failure ALWAYS keeps its data and seed. No directory is replaced. Full requires
# 85 GB free before building (quick 13 GB): the data cap 8 L0 + 3 GB of the largest fill
# allowed and a 2 GB reserve. The harness caps the data at 8 L0 + 3 GB, and after the fill
# requires free disk for the rest of it.
#
# Environment: JAVA_HOME or JAVA, HEAP (default 10g, quick 3g), CHILD_HEAP (same default),
# EPOCHS (>=12, fixed work override for reproductions), KEEPDATA=1. OUT may name a NEW
# output directory. Neither night.sh nor timing.sh calls this test.

cd "$(dirname "$0")/.." || exit 1
echo "Kind: functional"

main() {
    mode=${1:-full}
    seed=${2:-$(date +%Y%m%d)}
    case $mode in
        full) keys=10000000; epochs=${EPOCHS:-40}; heap=${HEAP:-10g}; disk=85000000 ;;
        quick) keys=1000000; epochs=${EPOCHS:-16}; heap=${HEAP:-3g}; disk=13000000 ;;
        *) echo "Usage: sh java/stress/large.sh [full|quick] [SEED]"; return 2 ;;
    esac
    [ $# -le 2 ] || { echo "large.sh: at most MODE and SEED"; return 2; }
    case $seed in ''|*[!0-9]*) echo "large.sh: SEED must be a nonnegative integer"; return 2 ;; esac
    case $epochs in ''|*[!0-9]*) echo "large.sh: EPOCHS must be an integer >=12"; return 2 ;; esac
    [ "$epochs" -ge 12 ] || { echo "large.sh: EPOCHS must be >=12"; return 2; }
    if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=${JAVA:-java}; fi
    run=${OUT:-build/large/$mode-$seed-$(date +%Y%m%dT%H%M%S)}
    [ ! -e "$run" ] || { echo "large.sh: output already exists: $run"; return 2; }
    free=$(df -Pk . | awk 'END {print $4}')
    [ "$free" -ge "$disk" ] || { echo "LARGE RECLAIM FAILED: need $disk KB free, have $free"; return 1; }
    mkdir -p "$run/bin" || return 1
    sh build.sh > "$run/build.txt" 2>&1 || { cat "$run/build.txt"; return 1; }
    cp build/bergdb.jar "$run/bin/" && cp -R build/stress "$run/bin/stress" || return 1
    {
        echo "kind functional"
        echo "mode $mode seed $seed keys $keys epochs $epochs"
        echo "commit $(git rev-parse HEAD)"
        echo "changed files:"
        git status --short -- ../java ../items/028-todo
        echo "jar $(shasum -a 256 "$run/bin/bergdb.jar" | cut -d' ' -f1)"
        echo "harness $(shasum -a 256 stress/LargeReclaimRun.java | cut -d' ' -f1)"
        echo "java $("$JAVA" -version 2>&1 | tr '\n' ' ')"
        echo "heap $heap childHeap ${CHILD_HEAP:-$heap}"
        echo "freeKB $free"
        echo "started $(date '+%Y-%m-%d %H:%M:%S %Z')"
    } > "$run/source.txt"
    echo "Large reclaim: $mode, seed $seed, $keys keys, $epochs epochs; log java/$run/out.txt"
    "$JAVA" -Xms256m "-Xmx$heap" -XX:+UseG1GC "-Dlarge.childheap=${CHILD_HEAP:-$heap}" \
        -cp "$run/bin/bergdb.jar:$run/bin/stress" bergdb.core.LargeReclaimRun \
        run "$run" "$seed" "$keys" "$epochs" > "$run/out.txt" 2>&1
    status=$?
    echo "ended $(date '+%Y-%m-%d %H:%M:%S %Z') status $status" >> "$run/source.txt"
    if [ "$status" -eq 0 ] && grep -q ' LARGE RECLAIM OK ' "$run/out.txt"; then
        if [ "${KEEPDATA:-0}" != 1 ]; then
            find "$run/data" -type f -delete && rmdir "$run/data" || return 1
        fi
        tail -1 "$run/out.txt"
        return 0
    fi
    tail -30 "$run/out.txt"
    echo "LARGE RECLAIM FAILED: seed $seed; data kept in java/$run/data"
    return 1
}

main "$@"
