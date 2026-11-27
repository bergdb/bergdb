#!/bin/sh
# Review of 031-06: SafetyProbe on the item's configurations 3, 4 and 7 with other seeds, and
# RvFront with eviction. From the repository's root.
J=java/build/bergdb.jar
run() { echo "== $PROPS $*"; java -ea -Xmx4g $PROPS -cp "review-probes/out-safety:$J" bergdb.core.SafetyProbe "$@" 2>&1 | grep -v "^\s*at "; }
PROPS="-Dlimit=100000 -Dreserve=500 -Dnode=8 -Dcold=600"; run 103 6000
PROPS="-Dlimit=300000 -Dreserve=100000 -Dnode=30 -Dhot=200"; run 104 6000
PROPS="-Dlimit=150000 -Dreserve=300 -Dnode=8 -Dsd=500 -Dcold=200 -Dhot=20"; run 107 8000
PROPS="-Dlimit=120000 -Dreserve=400 -Dnode=8 -Dsd=300 -Dcold=1500 -Dhot=5"; run 211 8000
echo "SAFETY2 DONE"
