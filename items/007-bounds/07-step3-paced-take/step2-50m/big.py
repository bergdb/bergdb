#!/usr/bin/env python3
"""006-10 (r50): records over a few times the mean, from WriteBench's wb.rec (see summary.py).
Steady run: over the second half of the workload by puts, the mean record, the largest, and the
records over 3, 5 and 10 times the mean. Run with a decrease: the same over the stretch from
the first dummy record until the section is first below the new 2 sd ("catch-up"), against the
mean of the second half after it (the new distance's steady records), and the puts and records
of the catch-up.
Usage: big.py FILE.rec ..."""
import sys
from summary import load
MB = 1e6

def second_half(work):
    half = sum(r[1] for r in work) / 2
    acc = 0
    for i, r in enumerate(work):
        acc += r[1]
        if acc >= half:
            return work[i + 1:]
    return []

def over(rows, mean):
    return " ".join(">%dx %d" % (k, sum(1 for r in rows if r[5] > k * mean)) for k in (3, 5, 10))

for path in sys.argv[1:]:
    rows = load(path)
    work = [r for r in rows if r[0] != 0]
    d = [i for i, r in enumerate(rows) if r[0] == 2]
    name = path.split("/")[-1]
    if not d:
        h = second_half(work)
        mean = sum(r[5] for r in h) / len(h)
        mx = max(r[5] for r in h)
        print("%s: steady 2nd half, %d records, mean %.1f kB, max %.2f MB (%.1fx), %s, >100 kB %d"
              % (name, len(h), mean / 1e3, mx / MB, mx / mean, over(h, mean), sum(1 for r in h if r[5] > 1e5)))
        continue
    d0, d1 = d[0], d[-1]
    sd = rows[d1][12]
    j = next((i for i in range(d1, len(rows)) if rows[i][9] < 2 * sd), len(rows) - 1)
    after = rows[j + 1:]
    ah = after[len(after) // 2:]
    mean = sum(r[5] for r in ah) / len(ah)
    pre = second_half(rows[next(i for i, r in enumerate(rows) if r[0] != 0):d0])
    pmean = sum(r[5] for r in pre) / len(pre)
    cu = rows[d0:j + 1]
    user = [r for r in cu if r[0] == 1]
    mx = max(r[5] for r in cu)
    umx = max(r[5] for r in user) if user else 0
    print("%s: before (2nd half) mean %.3f MB; after (2nd half) mean %.3f MB; catch-up %d records, "
          "%d puts, %.0f MB: max %.2f MB (%.1fx after's mean), largest user %.2f MB (%.1fx), %s; "
          "after (2nd half) max %.2f MB (%.1fx), %s"
          % (name, pmean / MB, mean / MB, len(cu), sum(r[1] for r in user), (rows[j][8] - rows[d0 - 1][8]) / MB,
             mx / MB, mx / mean, umx / MB, umx / mean, over(cu, mean),
             max(r[5] for r in ah) / MB, max(r[5] for r in ah) / mean, over(ah, mean)))
