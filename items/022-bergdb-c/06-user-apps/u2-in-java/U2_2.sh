#!/bin/sh
# bergdb 022-06, u2's U2-2 in Java's Core: repro_full_zerofill.sh with U2_2.java: a 12 MB
# transaction fails on a nearly full disk (a 40 MB HFS+ image); then the start with 6 MB
# free (with a small transaction and a sync), and with all freed. Needs hdiutil; about 20 s.
# Usage: U2_2.sh CLASSES
cd "$(dirname "$0")"
CL=$1
J="java -ea -cp $CL:."
M=/Users/f/fl/bench/022/f2/mnt-zf; IMG=/Users/f/fl/bench/022/f2/zf.dmg
rm -f $IMG; mkdir -p $M
hdiutil create -size 40m -fs HFS+ -volname bdbzfj $IMG >/dev/null 2>&1
hdiutil attach -nobrowse -mountpoint $M $IMG >/dev/null 2>&1 || exit 2
dd if=/dev/zero of=$M/reserve bs=1m count=20 2>/dev/null
$J U2_2 $M/db open
dd if=/dev/zero of=$M/filler bs=64k 2>/dev/null       # the disk full
s=$(stat -f %z $M/filler); dd if=/dev/zero of=$M/filler bs=1 count=0 seek=$((s - 2097152)) 2>/dev/null
echo "--- 2 MB free"; df -k $M | tail -1
$J U2_2 $M/db fill
echo "stream files: $(ls $M/db | grep -c bergdb\$), bytes: $(cat $M/db/*.bergdb | wc -c)"
s=$(stat -f %z $M/filler); dd if=/dev/zero of=$M/filler bs=1 count=0 seek=$((s - 6291456)) 2>/dev/null
echo "--- 6 MB more freed"; df -k $M | tail -1
$J U2_2 $M/db use
echo "stream files: $(ls $M/db | grep -c bergdb\$), bytes: $(cat $M/db/*.bergdb | wc -c)"
rm $M/filler $M/reserve; echo "--- all freed"
$J U2_2 $M/db open
echo "stream files: $(ls $M/db | grep -c bergdb\$), bytes: $(cat $M/db/*.bergdb | wc -c)"
hdiutil detach $M >/dev/null 2>&1; rm -f $IMG; rmdir $M
