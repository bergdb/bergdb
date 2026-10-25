#!/bin/sh
# 009's pause probe on s1: each jar with G1 and ZGC, in turns. Usage: run-pp.sh JAR... (in /opt/bergdb-bench/009)
cd /opt/bergdb-bench/009
J=/opt/bergdb-bench/jdk-27/bin/java
mkdir -p out
for jar in "$@"; do
  for gc in G1 Z; do
    name=$(basename $jar .jar)-$gc
    rm -rf /opt/bergdb-bench/009/db
    $J -XX:+Use${gc}GC -Xmx1200m -Xms1200m -Xlog:gc*,safepoint:file=out/$name-gc.log:uptime,level,tags \
      -Dkeys=1000000 -Dbudget=20 -Dreaders=2 -Dseconds=60 -Dtsize=1,1000 -Ddir=/opt/bergdb-bench/009/db \
      -cp $jar:pp bergdb.core.PauseProbe > out/$name.txt 2>&1
    echo "$name: $(tail -1 out/$name.txt)"
  done
done
rm -rf /opt/bergdb-bench/009/db
echo ALL DONE
