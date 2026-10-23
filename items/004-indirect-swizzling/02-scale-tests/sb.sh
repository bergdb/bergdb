# Functions for ScaleBench runs (004-02, part D), sourced by plan-f53.sh and plan-s1.sh.
# Needs JAVA, CP (bergdb.jar and the classes of ScaleBench and PerfUtil), DATA (the
# databases), OUT (the outputs). Optional: THREADS (default 1,2,4,8), SAMPLED (default 4),
# PIDIO (macOS: the pidio tool), DISK (Linux: the device of DATA, default sda), MEMEXTRA
# (Linux, regime D: the cgroup's memory above the heap, default 300M), SBFLAGS (more -D
# flags for every run; for trials).
# Each run writes OUT/NAME.txt (the summary), OUT/NAME.json and OUT/NAME.gc.log, and appends
# a line to OUT/runs.txt; a run that does not end with SCALEBENCH OK stops the plan.

sb_jvm() {      # sb_jvm NAME HEAP ARGS...: the JVM with the flags of every run
    name=$1
    heap=$2
    shift 2
    set -- -Xms$heap -Xmx$heap -XX:+AlwaysPreTouch \
        "-Xlog:gc*,safepoint:file=$OUT/$name.gc.log:uptime,level,tags" \
        -Dsb.threads=${THREADS:-1,2,4,8} -Dsb.sampled=${SAMPLED:-4} -Dsb.disk=${DISK:-sda} \
        ${PIDIO:+-Dsb.pidio=$PIDIO} -Dsb.label=$name -Dsb.out=$OUT/$name.json \
        -Dsb.gclog=$OUT/$name.gc.log $SBFLAGS "$@" -cp "$CP" bergdb.core.ScaleBench
    echo "$(date '+%F %T') start $name: $*" >> "$OUT/runs.txt"
    if [ -n "$CGROUP_MAX" ]; then
        systemd-run --scope --quiet -p MemoryMax=$CGROUP_MAX -p MemorySwapMax=0 "$JAVA" "$@" > "$OUT/$name.txt" 2>&1 || true
    else
        "$JAVA" "$@" > "$OUT/$name.txt" 2>&1 || true
    fi
    if tail -n 1 "$OUT/$name.txt" | grep -q 'SCALEBENCH OK'; then
        echo "$(date '+%F %T') ok $name" >> "$OUT/runs.txt"
    else
        echo "$(date '+%F %T') FAILED $name" >> "$OUT/runs.txt"
        exit 1
    fi
}

# sb_load NAME KEYTYPE KEYS HEAP BUDGET PHASES: a new database DATA/KEYTYPE-KEYS (an old one
# is deleted), then the phases in the same JVM (budget 0: regime M).
sb_load() {
    rm -rf "$DATA/$2-$3"
    sb_jvm "$1" "$4" -Dsb.mode=load -Dsb.dir="$DATA/$2-$3" -Dsb.keys=$3 -Dsb.keytype=$2 \
        -Dsb.budget=$5 -Dsb.phases=$6
}

# sb_get NAME KEYTYPE KEYS HEAP BUDGET REGIME PHASES: the database DATA/KEYTYPE-KEYS in a new
# JVM. Regime C: the stream's files read once first. Regime D (Linux): the OS caches dropped
# first, and the JVM in a cgroup whose memory limit is the heap and MEMEXTRA.
sb_get() {
    extra=
    CGROUP_MAX=
    case $6 in
    C)
        extra=-Dsb.warmos=1
        ;;
    D)
        if [ -w /proc/sys/vm/drop_caches ]; then
            sync
            echo 3 > /proc/sys/vm/drop_caches
            h=$(echo "$4" | sed 's/[mM]$//; s/[gG]$/000/')
            x=$(echo "${MEMEXTRA:-300M}" | sed 's/[mM]$//')
            CGROUP_MAX=$((h + x))M
        fi
        ;;
    esac
    sb_jvm "$1" "$4" -Dsb.mode=get -Dsb.dir="$DATA/$2-$3" -Dsb.budget=$5 -Dsb.phases=$7 $extra
    CGROUP_MAX=
}
