#!/bin/sh
# bergdb 031-06, landing step 3: P1 (010-01, about 20 ms for BergDB's own code) with the
# pace of step 3, P1Probe on a database larger than its cache budget, on disk (FileStream,
# in OUT/db). Kind: timing (the times are the result): the lead runs it on a quiet machine
# (no other heavy run; timing.sh's load check is not in it). Usage, from the repository's
# root, after java/build.sh:
#   sh items/031-release-2026-7/06-one-record-an-action/probes/p1.sh OUT [small]
# The default is the timing run: 20M keys of 200 bytes (a stream of about 6 GB), a cache
# budget of 200 MB, 1M commits, every 50th of 200 kB, retain 10 s, with ZGC and a GC log in
# OUT/gc.log. "small" is the functional check that the probe runs: 200,000 keys, 20 MB,
# 50,000 commits. The stream's files stay in the OS page cache unless the machine's memory
# is short of them: the database is larger than the cache budget, not than the memory
# (dropping the page cache, "sudo purge", needs root).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT/classes" $P/P1Probe.java || exit 1
if [ "$2" = small ]; then
    java -Xmx2g -XX:+UseZGC -Ddir="$OUT/db" -Dkeys=200000 -Dbudget=20 -Dcommits=50000 \
        -Dsd=5000000 -cp "$OUT/classes:$J" bergdb.core.P1Probe
else
    java -Xmx8g -XX:+UseZGC -Xlog:gc*,safepoint:file="$OUT/gc.log":uptime,level,tags \
        -Ddir="$OUT/db" -Dkeys=20000000 -Dbudget=200 -Dcommits=1000000 \
        -cp "$OUT/classes:$J" bergdb.core.P1Probe
fi
rm -rf "$OUT/db"
