#!/bin/sh
# bergdb 030-20: writes the jobs files of s1-run.sh (ABBA order: off, on, on, off, ...). 2026-11-18.
# Usage: sh make-jobs.sh   (in this directory)
abba() {   # PREFIX ROUNDS HEAP CLASS ARGS...
    prefix=$1; rounds=$2; heap=$3; shift 3
    r=1
    while [ $r -le $rounds ]; do
        if [ $((r % 2)) = 1 ]; then o="0 1"; else o="1 0"; fi
        for tc in $o; do echo "$prefix-r$r-tc$tc $tc $heap $*"; done
        r=$((r + 1))
    done
}
{
    echo "# set 1: CCBench, 1M keys of 100 bytes, transaction sizes 1, 10, 100, 500; ABBA"
    abba cc1m 4 2g CCBench -Dcc.n=1000000 -Dcc.valsize=100 -Dcc.ops=200000 -Dcc.warm=40000
} > jobs-1m.txt
{
    echo "# set 2: Perf, the write scenarios of the quick suite and w-uni-100-inf of the principal one"
    abba w-uni-1k-inf 3 2g Perf write -Dperf.n=100000 -Dperf.valsize=1000 -Dperf.work=uniform -Dperf.retain=inf -Dperf.ops=1000000
    abba w-uni-1k-fin 3 2g Perf write -Dperf.n=100000 -Dperf.valsize=1000 -Dperf.work=uniform -Dperf.retain=1 -Dperf.mincuts=6 -Dperf.ops=1000000 -Dperf.maxops=6000000
    abba w-uni-100-inf 3 2500m Perf write -Dperf.n=1000000 -Dperf.valsize=100 -Dperf.work=uniform -Dperf.retain=inf -Dperf.ops=4500000
} > jobs-perf.txt
{
    echo "# set 3: JFR profiles with the check on, 1M keys, updates, one transaction size each"
    echo "jfr jfr-t1 1 2g CCBench -Dcc.n=1000000 -Dcc.valsize=100 -Dcc.ops=200000 -Dcc.warm=40000 -Dcc.tsizes=1 -Dcc.kinds=update"
    echo "jfr jfr-t500 1 2g CCBench -Dcc.n=1000000 -Dcc.valsize=100 -Dcc.ops=200000 -Dcc.warm=40000 -Dcc.tsizes=500 -Dcc.kinds=update"
    echo "jfr jfr-off-t1 0 2g CCBench -Dcc.n=1000000 -Dcc.valsize=100 -Dcc.ops=200000 -Dcc.warm=40000 -Dcc.tsizes=1 -Dcc.kinds=update"
} > jobs-jfr.txt
{
    echo "# set 4: CCBench, 10M keys of 8 bytes (all in a 2.9 GB heap), updates and mixed; ABBAAB"
    abba cc10m 3 2900m CCBench -Dcc.n=10000000 -Dcc.valsize=8 -Dcc.ops=100000 -Dcc.warm=20000 -Dcc.kinds=update,mixed
} > jobs-10m.txt
{
    echo "# set 5: CCBench as set 1, the tuned check (tuned/TransCheck.java) against none; ABBAAB"
    abba cctuned1m 3 2g CCBenchTuned -Dcc.n=1000000 -Dcc.valsize=100 -Dcc.ops=200000 -Dcc.warm=40000
} > jobs-tuned.txt
{
    echo "# set 6: Perf, the durable commits of the principal suite (execute, then sync), 1 and 16 threads; ABBAAB"
    abba d-1k-t1 3 2g Perf write -Dperf.n=100000 -Dperf.valsize=1000 -Dperf.commit=durable -Dperf.threads=1 -Dperf.ops=100 -Dperf.warmup=100000
    abba d-1k-t16 3 2g Perf write -Dperf.n=100000 -Dperf.valsize=1000 -Dperf.commit=durable -Dperf.threads=16 -Dperf.ops=1600 -Dperf.warmup=100000
} > jobs-durable.txt
