#!/bin/sh
# bergdb 031-06, review 3, section 5, point 2: BigStepProbe, the time under the write lock
# of a commit that carries a step of up to 128 KiB of values of 20 to 30 bytes (900 to
# 1,200 copies), after commits of 600 kB among small ones, on a database larger than its
# cache budget, on disk (FileStream, in OUT/db); the longest under the lock and the longest
# commit against P1's 20 ms. Kind: timing (the times are the result): the lead runs it on a
# quiet machine (no other heavy run; timing.sh's load check is not in it), once on main's
# jar (16 kB steps) and once on this branch's. Usage, from the repository's root, after
# java/build.sh:
#   sh items/031-release-2026-7/06-one-record-an-action/probes/bigstep.sh OUT [small]
#   JAR=MAIN/java/build/bergdb.jar sh items/031-release-2026-7/06-one-record-an-action/probes/bigstep.sh OUT2
# The default is the timing run: 2M cold keys (a stream of about 200 MB after the load), a
# cache budget of 50 MB, 100,000 commits, every 50th of 600 kB, retain 10 s, with ZGC and a
# GC log in OUT/gc.log. "small" is the functional check that the probe runs: 200,000 keys,
# 5 MB, 10,000 commits. The stream's files stay in the OS page cache unless the machine's
# memory is short of them (dropping it, "sudo purge", needs root).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT/classes" $P/BigStepProbe.java || exit 1
if [ "$2" = small ]; then
    java -Xmx2g -XX:+UseZGC -Ddir="$OUT/db" -Dkeys=200000 -Dbudget=5 -Dcommits=10000 \
        -Dsd=2000000 -cp "$OUT/classes:$J" bergdb.core.BigStepProbe
else
    java -Xmx8g -XX:+UseZGC -Xlog:gc*,safepoint:file="$OUT/gc.log":uptime,level,tags \
        -Ddir="$OUT/db" -Dkeys=2000000 -Dbudget=50 -Dcommits=100000 \
        -cp "$OUT/classes:$J" bergdb.core.BigStepProbe
fi
rm -rf "$OUT/db"
