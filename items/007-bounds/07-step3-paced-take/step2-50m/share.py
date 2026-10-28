#!/usr/bin/env python3
"""006-10 (r50): after a decrease, estimate each record's share (TransSeq.take: D * o/O * S/sd)
from wb.rec, against the index nodes it wrote. o = record bytes - index bytes; O = the same over
the records whose tpos is after the startup pos; S = the lag before the record. An estimate:
own bytes here include the got-dirty list. Usage: share.py FILE.rec [FIRST LAST]"""
import sys
from summary import load
rows = load(sys.argv[1])
d0 = [i for i, r in enumerate(rows) if r[0] == 2][0]
a = int(sys.argv[2]) if len(sys.argv) > 2 else -1
b = int(sys.argv[3]) if len(sys.argv) > 3 else 210
import bisect
tpos = [r[8] - r[5] for r in rows]
own = [r[5] - r[6] for r in rows]
cum = [0]
for o in own:
    cum.append(cum[-1] + o)
for k in range(a, b):
    i = d0 + k
    p = rows[i - 1]
    sp = p[8] - p[7]
    j = bisect.bisect_right(tpos, sp, 0, i)
    O = cum[i] - cum[j]
    sd = rows[i][12]
    share = p[10] * own[i] / O * p[7] / sd
    r = rows[i]
    if k < 5 or k % 10 == 0 or k > b - 12:
        print("%4d rec %6.2f MB nodes %7d share~%7.0f ratio %5.2f S %5.0f MB O %6.1f MB D %7d sec %4.0f"
              % (k, r[5] / 1e6, r[2], share, r[2] / share, p[7] / 1e6, O / 1e6, p[10], r[9] / 1e6))
