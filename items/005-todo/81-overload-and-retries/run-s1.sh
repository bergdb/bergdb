#!/bin/sh
# bergdb 005-81: runs RetryBench on s1 (2 vCPUs), stock and probe jars in turns.
# Usage: run-s1.sh SESSION REPS "CASE ..." where a CASE is workload:threads, such as hot:2.
# Needs /opt/bergdb-bench/005-81/{stock,probe}/java/build/bergdb.jar (built from a git
# archive; probe/ patched by make-probe.py) and RetryBench.java in /opt/bergdb-bench/005-81/in.
# Stops if another JVM runs. Outputs in /opt/bergdb-bench/005-81/out/SESSION/. With storage=file,
# each run gets an empty /opt/bergdb-bench/005-81/data, removed after the run.
set -e
R=/opt/bergdb-bench/005-81
SESSION=$1; REPS=$2; CASES=$3; shift 3
JAVA=/opt/bergdb-bench/jdk-27/bin
O=$R/out/$SESSION
mkdir -p $O
for b in stock probe; do
  mkdir -p $R/classes-$b
  $JAVA/javac --release 17 -nowarn -Xlint:-options -cp $R/$b/java/build/bergdb.jar -d $R/classes-$b $R/in/RetryBench.java
done
sha256sum $R/in/RetryBench.java $R/*/java/build/bergdb.jar > $O/identity.txt
FLAGS="-Xms1500m -Xmx1500m -XX:+UseZGC -da"
echo "flags $FLAGS; args $*" >> $O/identity.txt
for rep in $(seq 1 $REPS); do
  if [ $((rep % 2)) = 1 ]; then order="stock probe"; else order="probe stock"; fi
  for c in $CASES; do
    w=${c%%:*}; t=${c##*:}
    for b in $order; do
      if pgrep -x java > /dev/null; then echo "another JVM runs; stopped"; exit 2; fi
      d=$O/$w-t$t-$b-$rep; rm -rf $d; mkdir -p $d
      dir=""
      case "$*" in *storage=file*) rm -rf $R/data; mkdir -p $R/data; dir=dir=$R/data;; esac
      echo "$(date +%T) $(cut -d' ' -f1-3 /proc/loadavg) $w t$t $b rep $rep" | tee -a $O/runs.txt
      $JAVA/java $FLAGS -Xlog:gc:file=$d/gc.log -cp $R/classes-$b:$R/$b/java/build/bergdb.jar RetryBench \
        threads=$t workload=$w out=$d $dir "$@" > $d/stdout.txt 2> $d/stderr.txt
      [ -n "$dir" ] && du -sk $R/data > $d/data-size.txt && rm -rf $R/data
      grep -v '^RESULT' $d/stdout.txt >> $d/stderr.txt || true
      grep '^RESULT' $d/stdout.txt | cut -c8- > $d/result.json
      sed 's/^/    /' $d/stderr.txt | tee -a $O/runs.txt
      sleep 3
    done
  done
done
echo "$(date +%T) DONE" | tee -a $O/runs.txt
