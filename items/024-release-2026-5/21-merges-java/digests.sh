#!/bin/sh
# 024-21, section 8: the put path writes main's bytes. PutDigest (puts and overwrites only)
# and StreamDigest quick, on main's build at 1076235c and on the branch with its record format
# set back to 6 (f6wt), one compiled copy of each probe (main's StreamDigest).
M=/Users/f/fl/bench/2026-11-11/mgj
R=$M/runs
java -XX:ActiveProcessorCount=2 -cp $M/probe/pd-main:$M/mainwt/java/build/bergdb.jar bergdb.core.PutDigest > $R/pd-main.txt 2>&1 &
java -XX:ActiveProcessorCount=2 -cp $M/probe/pd-f6:$M/f6wt/java/build/bergdb.jar bergdb.core.PutDigest > $R/pd-f6.txt 2>&1 &
wait
diff $R/pd-main.txt $R/pd-f6.txt > $R/pd-diff.txt && echo "PUTDIGEST IDENTICAL ($(grep -c PUTDIGEST $R/pd-main.txt))" || echo "PUTDIGEST DIFFER"
SD=$M/mainwt/java/build/stress
java -XX:ActiveProcessorCount=2 -cp $M/mainwt/java/build/bergdb.jar:$SD bergdb.core.StreamDigest quick > $R/sd-main.txt 2>&1 &
java -XX:ActiveProcessorCount=2 -cp $M/f6wt/java/build/bergdb.jar:$SD bergdb.core.StreamDigest quick > $R/sd-f6.txt 2>&1 &
wait
java -XX:ActiveProcessorCount=2 -cp $M/f6wt/java/build/bergdb.jar:$SD bergdb.core.StreamDigest compare $R/sd-main.txt $R/sd-f6.txt > $R/sd-compare.txt 2>&1
tail -3 $R/sd-compare.txt
