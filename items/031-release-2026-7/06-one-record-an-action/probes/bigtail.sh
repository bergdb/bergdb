#!/bin/sh
# bergdb 031-06, review 3, section 5, point 5: BigTailProbe, the time of a start of a file
# database (FileStream, in OUT/db) whose last record is 100 MB or more: the take of a whole
# tree's dirty index nodes after the startup distance is lowered from 1 GB to 1 MB. Since
# step 4 the recovery's walk of the tail and the start each parse that record whole. Kind:
# timing (the times are the result): the lead runs it on a quiet machine, once on main's jar
# and once on this branch's. Usage, from the repository's root, after java/build.sh:
#   sh items/031-release-2026-7/06-one-record-an-action/probes/bigtail.sh OUT [small]
#   JAR=MAIN/java/build/bergdb.jar sh items/031-release-2026-7/06-one-record-an-action/probes/bigtail.sh OUT2
# The default is the timing run: 4M keys of 20 bytes in random order, a last record of
# about 145 MB (the probe prints its size), three starts. "small" is the functional check:
# 200,000 keys. The files may stay in the OS page cache (dropping it needs root).
OUT=${1:?out dir}
J=${JAR:-java/build/bergdb.jar}
P=items/031-release-2026-7/06-one-record-an-action/probes
mkdir -p "$OUT"
javac -nowarn -cp $J -d "$OUT/classes" $P/BigTailProbe.java || exit 1
if [ "$2" = small ]; then
    java -Xmx2g -XX:+UseZGC -Ddir="$OUT/db" -Dkeys=200000 -cp "$OUT/classes:$J" \
        bergdb.core.BigTailProbe
else
    java -Xmx12g -XX:+UseZGC -Xlog:gc*,safepoint:file="$OUT/gc.log":uptime,level,tags \
        -Ddir="$OUT/db" -Dkeys=4000000 -cp "$OUT/classes:$J" bergdb.core.BigTailProbe
fi
rm -rf "$OUT/db"
