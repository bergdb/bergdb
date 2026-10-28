#!/usr/bin/env python3
"""007-07: the deadline after a decrease (D4:B), checked on WriteBench's records (wb.rec, see
summary.py). Field 9, the section without its last record, R(s+1)..R(k-1), is the span of the
section's transactions that TransSeq.take's deadline uses, up to a meta block (128 bytes).
For each run with a decrease: from the record after the dummy on, while the section is at
least 2 new sd it must shrink with every record; after it is first below 2 new sd, it must
stay below. For a steady run: the section must stay below 2 sd. Prints the violations.
Usage: ratchet.py FILE.rec ...   (beside 007-06's summary.py, in 06-debt-test/)"""
import sys
from summary import load

TOL = 128
for path in sys.argv[1:]:
    rows = load(path)
    d = [i for i, r in enumerate(rows) if r[0] == 2]
    if not d:
        work = [r for r in rows if r[0] != 0]
        over = sum(1 for r in work if r[9] >= 2 * r[12] + TOL)
        print("%s: steady, %d records, max section %.3f sd, %d at or over 2 sd"
              % (path, len(work), max(r[9] / r[12] for r in work), over))
        continue
    d1 = d[-1]
    sd = rows[d1][12]
    grew = 0
    worst = 0
    below = None
    over_after = 0
    for i in range(d1 + 1, len(rows)):
        prev, cur = rows[i - 1][9], rows[i][9]
        if below is None:
            if prev >= 2 * sd:
                if cur >= prev + TOL:
                    grew += 1
                    worst = max(worst, cur - prev)
            if cur < 2 * sd:
                below = i
        elif cur >= 2 * sd + TOL:
            over_after += 1
    print("%s: section at the decrease %.0f MB (%.2f new sd), below 2 new sd after %s records; "
          "grew %d times while at or over 2 sd (most %d bytes); %d records at or over 2 sd after"
          % (path, rows[d1][9] / 1e6, rows[d1][9] / sd, "never" if below is None else below - d1,
             grew, worst, over_after))
