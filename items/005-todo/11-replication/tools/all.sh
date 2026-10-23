#!/bin/sh
# All probes but P8, one after the other; outputs in runs/. P8 times syncs and writes, so
# run it alone on a quiet machine: tools/run.sh slow DIR > runs/p8-slow.txt
# Usage: items/005-todo/11-replication/tools/all.sh   (about 6 minutes on F53)
set -e
cd "$(dirname "$0")/.."
R=runs
mkdir -p $R
tools/run.sh identity > $R/p1-identity.txt 2>&1
tools/p2-all.sh
tools/run.sh addafter > $R/p3-addafter.txt 2>&1
tools/run.sh restore > $R/p4-restore.txt 2>&1
tools/run.sh crashsync "${PROBE_TMP:-${TMPDIR:-/tmp}}/replicaprobe-p5" > $R/p5-crashsync.txt 2>&1
tools/run.sh fail > $R/p6-fail.txt 2>&1
tools/run.sh evict > $R/p7-evict.txt 2>&1
tools/run.sh diverge > $R/p9-diverge.txt 2>&1
tools/run.sh pubapi > $R/p10-pubapi.txt 2>&1
tools/run.sh metaedge > $R/p11-metaedge.txt 2>&1
java -ea -da:bergdb.stream.MemoryStream -Xmx3g -Dtrans=150000 -Dvalue=8 \
    -cp ../../../java/build/bergdb.jar:../../../java/build/replicaprobe \
    bergdb.core.ReplicaProbe metaedge > $R/p11-metaedge-small.txt 2>&1
echo ALL DONE
