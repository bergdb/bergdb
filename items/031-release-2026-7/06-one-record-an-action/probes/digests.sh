#!/bin/sh
# bergdb 031-06: StreamDigest quick (its four modes must give the same stream) and
# RestartInvariance with reclaim in level3.sh's four configurations of step 3 at its full
# size (2,000 transactions; every1 1,000), and level1.sh's step 5 configuration (no reclaim),
# as 031-05 (section 7.3) ran them. Usage, from java/: sh ../items/.../probes/digests.sh OUT
# with JAR and STRESS (the stress classes) set. Kind: functional.
OUT=${1:?out dir}
J=${JAR:-build/bergdb.jar}; S=${STRESS:-build/stress}
CP=$J:$S
mkdir -p $OUT
java -ea -Xmx4g -cp $CP bergdb.core.StreamDigest quick > $OUT/digest-quick.txt 2>&1
grep -c "the modes give the same stream" $OUT/digest-quick.txt
I="-ea -Xmx2g -Ddel=1 -Dretain=1 -Dn=2000"
inv() { name=$1; shift; java $I "$@" -cp $CP bergdb.core.RestartInvariance 1 > $OUT/inv-$name.txt 2>&1; }
inv every1 -Dsd=500 -Dkeys=100 -Devery=1 -Dlong=1 -Dn=1000
inv node8 -Dsd=1000 -Dkeys=500 -Devery=50 -Dmaxnode=8 -Dlong=1 -Dbigtrans=10
inv node14 -Dsd=3000 -Dkeys=50 -Devery=37 -Dmaxnode=14
inv node62 -Dsd=10000 -Dkeys=1000 -Devery=100 -Dmaxnode=62 -Dbigtrans=40 -Dvalsize=400
java -ea -Xmx9g -Dsd=200000000 -Dn=12000 -Dkeys=3000 -Dvalsize=8000 -Devery=4000 -Ddel=1 -cp $CP bergdb.core.RestartInvariance 1 > $OUT/inv-level1.txt 2>&1
for F in $OUT/inv-*.txt; do
    echo "$(basename $F): $(grep -E '^STREAM: ' $F | head -1); $(grep -E '^CUT: ' $F | head -1); checks with 0: $(grep -Ec '^(TRANSSEQ|KV CHECKSUM|IDENTITY .*|LOOKUP .*): 0 of' $F)"
done
echo "DIGESTS DONE"
