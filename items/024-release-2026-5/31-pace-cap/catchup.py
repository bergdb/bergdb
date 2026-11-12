#!/usr/bin/env python3
"""024-31: a decrease run's catch-up, on WriteBench's wb.rec (77 bytes a record, see
summary.py's fields). The catch-up: from the call's record (phase 2) until the section
without its last record (field 9) is first below the new 2 sd, that record included. The new
mean: the mean record (field 5) in the second half of the records after the catch-up (as
007-07, section 11.2). Prints one line a file: section and debt before; the call's record;
the catch-up's puts, stream (from the end of the record before the call) and records; its
largest user record and its multiple of the new mean; its records (the call's included)
over 3, 5 and 10 times the new mean; the new mean; after, 2nd half: section max in sd and
the largest record; and the largest user record after the catch-up.
Usage: catchup.py FILE.rec ...   (beside 007-06's summary.py)"""
import sys
from summary import load

MB = 1e6
for path in sys.argv[1:]:
    rows = load(path)
    d = [i for i, r in enumerate(rows) if r[0] == 2]
    d0, d1 = d[0], d[-1]
    sd = rows[d1][12]
    b = rows[d0 - 1]
    j = next(i for i in range(d1, len(rows)) if rows[i][9] < 2 * sd)
    cu = rows[d0:j + 1]
    user = [r for r in cu if r[0] == 1]
    rest = rows[j + 1:]
    half = rest[len(rest) // 2:]
    mean = sum(r[5] for r in half) / len(half)
    big = max(r[5] for r in user) if user else 0
    over = [sum(1 for r in cu if r[5] > k * mean) for k in (3, 5, 10)]
    print("%s: before sec %.0f / debt %.0f MB; call %.2f MB; to 2 sd: %.2fM puts, %.0f MB, %d records;"
          " largest user %.2f MB (%.1fx); over 3/5/10x %d/%d/%d; new mean %.0f kB;"
          " after 2nd half: sec max %.2f sd, largest %.2f MB; largest user after catch-up %.2f MB"
          % (path, b[9] / MB, b[11] / MB, max(rows[i][5] for i in d) / MB,
             sum(r[1] for r in user) / 1e6, (rows[j][8] - b[8]) / MB, len(cu),
             big / MB, big / mean, over[0], over[1], over[2], mean / 1e3,
             max(r[9] / r[12] for r in half), max(r[5] for r in half) / MB,
             max(r[5] for r in rest) / MB))
