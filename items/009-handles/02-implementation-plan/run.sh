#!/bin/sh
# TableBench's runs for 009-02 (decision T1), one after the other, on a quiet machine.
# Usage: run.sh OUT_DIR. Each run's line goes to OUT_DIR/table.txt, its GC log to OUT_DIR/gc-*.log.
# Timing: ZGC at 1M, 10M and 30M handles, G1 at 100M (ZGC's heap at 100M would need about
# 22 GB here); memory: G1 and ZGC at 10M.
cd "$(dirname "$0")"
out=$1
mkdir -p "$out"
run() {
    gc=$1; xmx=$2; shift 2
    log="$out/gc-$gc-$1-$2${3:+-$3}.log"
    java -XX:+Use$gc -Xmx$xmx -Xms$xmx -Xlog:gc:file="$log" TableBench.java "$@" \
        | sed "s/^/$gc /" >> "$out/table.txt"
}
for n in 1000000 10000000 30000000; do
    for t in maps256 maps4096 intr4096; do run ZGC 10g $t $n; done
done
for t in maps256 maps4096 intr4096; do run G1GC 16g $t 100000000; done
for gc in G1GC ZGC; do
    for t in handles maps4096 intr4096; do run $gc 8g $t 10000000 mem; done
done
echo done >> "$out/table.txt"
