#!/bin/sh
# The prototype's runs for bergdb 023-03, section 9: T1 and its matrix at N = 1,000 and
# 100,000 (kept from the decided cut), phase twins, T3 with R forever, and T1 on a FileStream.
cd /Users/f/fl/bench/2026-11-10/t23/clone/java
CP=build/bergdb.jar:build/stress
run() { java -ea -Xmx6g -cp $CP bergdb.core.CleanupRule hello "$@" 2>&1; }
F="^RESULT\|in progress\|Exception\|Error"
echo "== phase twins"
run n=0 pre=137 | grep "$F"
run n=0 pre=611 | grep "$F"
echo "== T1 and T2"
for n in 1000 100000; do
  for shape in after before around inter hashed; do
    order=asc; [ $shape = hashed ] && order=random
    run n=$n shape=$shape order=$order | grep "$F"
  done
  run n=$n shape=after order=desc | grep "$F"
  run n=$n shape=after order=random | grep "$F"
  run n=$n shape=after versions=3 | grep "$F"
done
run n=1000 shape=long | grep "$F"
run n=10000 shape=long | grep "$F"
echo "== T1 at N = 1,000,000"
run n=1000000 twin=0 | grep "$F\|deleted:\|drive 4000"
echo "== T3, R forever, no drive: after the deletes"
for shape in after before around inter long hashed; do
  n=100000; [ $shape = long ] && n=10000
  order=asc; [ $shape = hashed ] && order=random
  run n=$n shape=$shape order=$order retain=0 drive=0 twin=0 | grep "filled:\|deleted:"
done
run n=0 retain=0 drive=0 twin=0 | grep "RESULT1"
echo "== T1 on a FileStream, sd 1 MB"
run n=100000 sd=1000000 stream=file dir=/Users/f/fl/bench/2026-11-10/t23/data drive=24000 every=4000 | grep "$F\|drive 24000\|window"
rm -rf /Users/f/fl/bench/2026-11-10/t23/data
echo MATRIX2 DONE
