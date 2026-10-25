#!/bin/sh
# 009's pause probe on s1, in turns: run-pp2.sh "GCS" "BUDGETS" JAR... (in /opt/bergdb-bench/009)
# GCS: G1, Z, Shen (generational Shenandoah); BUDGETS in MB. Each run deletes its database.
cd /opt/bergdb-bench/009
J=/opt/bergdb-bench/jdk-27/bin/java
GCS=$1; BUDGETS=$2; shift 2
mkdir -p out
for b in $BUDGETS; do
for jar in "$@"; do
  for gc in $GCS; do
    case $gc in
      Shen) flags="-XX:+UseShenandoahGC -XX:ShenandoahGCMode=generational";;
      *) flags="-XX:+Use${gc}GC";;
    esac
    name=$(basename $jar .jar)-$gc-b$b
    rm -rf /opt/bergdb-bench/009/db
    $J $flags -Xmx1200m -Xms1200m -XX:+AlwaysPreTouch -Xlog:gc*,safepoint:file=out/$name-gc.log:uptime,level,tags \
      -Dkeys=1000000 -Dbudget=$b -Dreaders=2 -Dseconds=60 -Dtsize=1,1000 -Ddir=/opt/bergdb-bench/009/db \
      -cp $jar:pp bergdb.core.PauseProbe > out/$name.txt 2>&1
    echo "$(date '+%T') $name: $(tail -1 out/$name.txt)"
  done
done
done
rm -rf /opt/bergdb-bench/009/db
echo ALL DONE
