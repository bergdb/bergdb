#!/bin/sh
# Bergdb 005-04, option 4 (../04-a6-failures.md, "Outcome"): traces that contain A6's kind
# (a segment root made and split in place in one transaction), checked by the Lean checker:
# C-S (records and D), C-R (probes after restarts), C-L, and with run E (an eviction schedule)
# C-P (INV-SLOT on Java's physical states) and run E's stream against run A's. The
# configurations are those of conformance.sh's "big" with two-segment keys (long=1), at node
# sizes 8 and 14, without and with eviction. A tool for this subitem only.
#
# Usage: sh traces.sh BERGDB OUT
#   BERGDB  a checkout of bergdb with java/ built (java/build.sh) and the checker built
#           (cd lean && lake build tracecheck)
#   OUT     a directory for the traces and the checker's outputs
# About a minute. Prints one line per trace.
HERE=$(cd "$(dirname "$0")" && pwd)
B=$(cd "$1" && pwd)
mkdir -p "$2"
OUT=$(cd "$2" && pwd)
CP=$B/java/build/bergdb.jar:$B/java/build/stress
CHECK=$B/lean/.lake/build/bin/tracecheck
while read name props; do
    case "$name" in ""|\#*) continue ;; esac
    for s in 1 2 3; do
        t=$OUT/$name-$s.trace
        nice java -ea $props -cp $CP bergdb.core.TraceExport $s $t > $OUT/$name-$s.export.txt 2>&1 \
            || { echo "$name-$s: TraceExport failed: $(tail -1 $OUT/$name-$s.export.txt)"; continue; }
        nice $CHECK $t > $OUT/$name-$s.check.txt 2>&1
        f=$OUT/$name-$s.check.txt
        echo "$name-$s | $(tail -1 $f) | $(grep -o 'C-S steps: [0-9]* of [0-9]*' $f)" \
            "| $(grep -o 'C-R probes: [0-9]* of [0-9]*' $f)" \
            "| $(grep -o 'C-P slots[^;]*; [0-9]* SLOT lines, [0-9]* checked' $f | sed 's/ (INV-SLOT on run E.s states)//')" \
            "| $(grep -o 'diagnostics: .*' $f) | $(grep -o 'T([0-9]*) A6' $f | tr '\n' ' ')"
    done
done <<EOF
a6-big      -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10
a6-big14    -Dn=40 -Dkeys=400 -Dmaxnode=14 -Dsd=1000 -Dops=60 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10
a6-random   -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=random
a6-every    -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=every
a6-budget   -Dn=40 -Dkeys=200 -Dmaxnode=8 -Dsd=1000 -Dops=40 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=budget -Devictbudget=30000
a6-14-rand  -Dn=40 -Dkeys=400 -Dmaxnode=14 -Dsd=1000 -Dops=60 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=random
a6-14-every -Dn=40 -Dkeys=400 -Dmaxnode=14 -Dsd=1000 -Dops=60 -Dexact=1 -Dlong=1 -Ddel=25 -Dprobe=10 -Drune=every
EOF
