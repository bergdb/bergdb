#!/bin/sh
# 024-21, section 8: 024-11's probe shapes with 024-14's THR (mgj/probe/thr, with BU1's check),
# the branch's frozen build b1 against main's build at 1076235c (mainwt). Two JVMs at a time:
# a job on the branch and the same on main. Counts only. Usage: numbers.sh OUTDIR N...
M=/Users/f/fl/bench/2026-11-11/mgj
O=$1; shift
mkdir -p $O $M/data
job() {   # build name args...
  b=$1; nm=$2; shift 2
  case $b in
    br) CP=$M/probe/thr-b1:$M/b1/bergdb.jar ;;
    main) CP=$M/probe/thr-main:$M/mainwt/java/build/bergdb.jar ;;
  esac
  F=$O/$nm-$b.txt; DD=$M/data/$nm-$b
  echo "== $nm $b $(date +%H:%M:%S) $*" > $F
  java -Xmx3g -XX:+UseG1GC -XX:ActiveProcessorCount=2 -cp $CP bergdb.core.THR "$@" dir=$DD >> $F 2>&1
  echo "rc=$? $(date +%H:%M:%S)" >> $F
  rm -rf $DD $DD-twin
}
for n in "$@"; do
  for k in 2 10 30 100; do
    for o in asc desc hashed; do
      a="run n=$n fill=seq shape=keep keep=$k order=$o drive=0"
      job br n$n-k$k-$o $a twin=1 &
      job main n$n-k$k-$o $a twin=0 &
      wait
    done
  done
  a="run n=$n fill=random shape=over phase=2000 drive=0 twin=0"
  job br n$n-over $a &
  job main n$n-over $a &
  wait
done
echo "numbers done $(date +%H:%M:%S)"
