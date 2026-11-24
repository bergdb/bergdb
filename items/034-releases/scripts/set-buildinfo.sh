#!/bin/sh
# Sets BuildInfo's version in a clone (bergdb 034-01, steps 7 and 10; 018-09, steps R2 and R9;
# as 016-09's), nothing else:
#   commit A: sh set-buildinfo.sh CLONE V INT          RELEASE "V", BUILD "V.YYMMDD.HHMM"
#             (the date and time from date now; for 2026.7: sh set-buildinfo.sh CLONE 2026.7
#             267 gives the build 2026.7.YYMMDD.HHMM);
#   commit B: sh set-buildinfo.sh CLONE NEXT NEXTINT   RELEASE and BUILD "NEXT", such as
#             2026.8-dev 268 (stage-b.sh calls it so).
# RELEASE_INT is set to INT, (YYYY - 2000) * 10 + N for YYYY.N, such as 267 for 2026.7. A
# version ending in -dev gets BUILD equal to it.
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.3's copy 2026-11-06; 2026.6's 2026-11-23;
# for every release 2026-11-24 (bergdb 034; the examples only).
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
