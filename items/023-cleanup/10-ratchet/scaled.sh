#!/bin/sh
# The scaled ratchet runs of 023-10 (2026-11-10), one at a time: CleanupRatchet (probe/,
# compiled apart into classes-main and classes-core) on the builds in wt-main (main,
# 51987a7b) and wt-core (023-core, 2c67f887). Outputs in runs/scaled/.
R=/Users/f/fl/bench/2026-11-10/ratchet
OUT=$R/runs/scaled
one() {   # name build args...
  name=$1; b=$2; shift 2
  echo "$(date +%H:%M:%S) start $name $b: $*"
  ( cd $R/wt-$b/java && /usr/bin/time -p java -ea -Xmx8g -cp $R/classes-$b:build/bergdb.jar \
      bergdb.core.CleanupRatchet "$@" ) > $OUT/$name-$b.txt 2>&1
  echo "$(date +%H:%M:%S) end $name $b: exit $?"
}
for b in main core; do one A-queue-300k-100k $b work=queue m=300000 dist=100000 n=1000000; done
for b in main core; do one B-drive-300k-100k $b work=drive m=300000 dist=100000 n=1000000; done
for b in main core; do one C-drive-500k-50k $b work=drive m=500000 dist=50000 n=1000000; done
for b in main core; do one D-drive-300k-50k-n100k $b work=drive m=300000 dist=50000 n=100000; done
for b in main core; do one E-queue-500k-50k $b work=queue m=500000 dist=50000 n=1000000; done
echo "$(date +%H:%M:%S) SCALED DONE"
