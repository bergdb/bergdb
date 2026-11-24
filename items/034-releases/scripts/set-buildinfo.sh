#!/bin/sh
# Sets BuildInfo's version in a clone (bergdb 018-09, steps R2 and R9; as 016-09's), nothing else:
#   commit A: sh set-buildinfo.sh CLONE 2026.6 266        RELEASE "2026.6", BUILD "2026.6.YYMMDD.HHMM"
#             (the date and time from date now, for example 2026.6.261123.2310);
#   commit B: sh set-buildinfo.sh CLONE 2026.7-dev 267    RELEASE and BUILD "2026.7-dev"
#             (stage-b.sh calls it so).
# RELEASE_INT is set to INT. A version ending in -dev gets BUILD equal to it.
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.3's copy 2026-11-06; 2026.6's 2026-11-23
# (bergdb 026-27; the examples only).
# Prints the three lines changed and "BUILDINFO SET ..." or "BUILDINFO FAILED: ..." (exit 1);
# then git diff in CLONE shows one file.
C=${1:?usage: set-buildinfo.sh CLONE VERSION INT}
V=${2:?usage: set-buildinfo.sh CLONE VERSION INT}
I=${3:?usage: set-buildinfo.sh CLONE VERSION INT}
F=$C/java/src/bergdb/core/BuildInfo.java
[ -f "$F" ] || { echo "BUILDINFO FAILED: no $F"; exit 1; }
case $V in
    *-dev) B=$V ;;
    *) B=$V.$(date +%y%m%d.%H%M) ;;
esac
python3 -I - "$F" "$V" "$I" "$B" <<'EOF' || { echo "BUILDINFO FAILED: the three lines were not found as expected"; exit 1; }
import re, sys
f, v, i, b = sys.argv[1:]
s = open(f, encoding="utf-8", newline="").read()
pats = [(r'(public static final int RELEASE_INT = Util\.identity\()\d+(\);)', r'\g<1>' + i + r'\g<2>'),
        (r'(public static final String RELEASE = Util\.identity\(")[^"]*("\);)', r'\g<1>' + v + r'\g<2>'),
        (r'(public static final String BUILD = Util\.identity\(")[^"]*("\);)', r'\g<1>' + b + r'\g<2>')]
for p, r in pats:
    s, n = re.subn(p, r, s)
    if n != 1:
        sys.exit(1)
open(f, "w", encoding="utf-8", newline="").write(s)
EOF
grep -n 'RELEASE_INT = \|RELEASE = \|BUILD = ' "$F"
n=$(git -C "$C" diff --numstat | wc -l | tr -d ' ')
echo "BUILDINFO SET: RELEASE $V, RELEASE_INT $I, BUILD $B; files changed in $C: $n"
