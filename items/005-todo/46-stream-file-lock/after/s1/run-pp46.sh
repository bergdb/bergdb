#!/bin/sh
# 005-46's pause probe on s1, in turns: run-pp46.sh "GCS" "BUDGETS" JAR... (in /opt/bergdb-bench/005-46)
# As 009-03's run-pp2.sh; the probe (pp/) prints the disk's waits after each phase (005-46,
# change 7: the forces, the deletes, and with the new jar the writer's waits for room).
cd /opt/bergdb-bench/005-46
J=/opt/bergdb-bench/jdk-27/bin/java
GCS=$1; BUDGETS=$2; shift 2
mkdir -p out
for b in $BUDGETS; do
for jar in "$@"; do
  for gc in $GCS; do
    flags="-XX:+Use${gc}GC"
    name=$(basename $jar .jar)-$gc-b$b
    rm -rf /opt/bergdb-bench/005-46/db
    $J $flags -Xmx1200m -Xms1200m -XX:+AlwaysPreTouch -Xlog:gc*,safepoint:file=out/$name-gc.log:uptime,level,tags \
      -Dkeys=1000000 -Dbudget=$b -Dreaders=2 -Dseconds=60 -Dtsize=1,1000 -Ddir=/opt/bergdb-bench/005-46/db \
      -cp $jar:pp bergdb.core.PauseProbe > out/$name.txt 2>&1
    echo "$(date '+%T') $name: $(tail -1 out/$name.txt)"
  done
done
done
rm -rf /opt/bergdb-bench/005-46/db
echo ALL DONE
