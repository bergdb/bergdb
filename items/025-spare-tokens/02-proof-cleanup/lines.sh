#!/bin/sh
# 025-02 (2026-11-14): lines and files of lean/ per area. Usage: sh lines.sh LEANDIR
cd $1 || exit 1
area() { n=$(find $2 -maxdepth $3 -name '*.lean' | wc -l | tr -d ' '); l=$(find $2 -maxdepth $3 -name '*.lean' -exec cat {} + | wc -l | tr -d ' '); echo "lines $1: $n files, $l lines"; }
area SIS/Tree SIS/Tree 1
area SIS/Proof SIS/Proof 1
area SIS-top SIS 1
area BergDB BergDB 9
area Check Check 1
area programs . 1
echo "lines all: $(find . -name '*.lean' -not -path './.lake/*' | wc -l | tr -d ' ') files, $(find . -name '*.lean' -not -path './.lake/*' -exec cat {} + | wc -l | tr -d ' ') lines; README.md $(wc -l < README.md | tr -d ' ')"
