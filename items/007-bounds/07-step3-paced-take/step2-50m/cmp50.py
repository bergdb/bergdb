#!/usr/bin/env python3
"""006-10 (r50): 007-07's step-2 runs at 50M keys against 10M (007-07, section 10.4), as
markdown tables. Steady runs over the second half of the workload by puts; a decrease from
setStartupDistance's record until the section is first below the new 2 sd ("catch-up"),
records compared with the mean record of the second half of the rest of the run (the new
distance's steady records).
Usage: cmp50.py DIR10M DIR50M   (DIR10M holds d4b-*.rec, DIR50M m50-*.rec; beside summary.py)"""
import os
import sys
from summary import load, pct
from tables import second_half, steady

MB = 1e6
d10, d50 = sys.argv[1], sys.argv[2]


def done(p):
    t = p[:-4] + ".txt"
    return os.path.exists(p) and os.path.exists(t) and "WRITEBENCH OK" in open(t).read()


def kb(x):
    return "%.0f" % (x / 1e3) if x >= 1e4 else "%.2f" % (x / 1e3)


def over(rows, mean):
    return " / ".join(str(sum(1 for r in rows if r[5] > k * mean)) for k in (3, 5, 10))


def steady_row(label, keys, p):
    rows = load(p)
    work = [r for r in rows if r[0] != 0]
    h, end = second_half(work)
    s = steady(h, end)
    mean = sum(r[5] for r in h) / len(h)
    big = sum(1 for r in h if r[5] > 1e5)
    return ("| %s | %s | %.1fM | %.0f | %s kB | %.2f MB (%.1f×) | %s | %s | %.2f / %.2f / %.2f | %.2f | %.0fk |"
            % (label, keys, sum(r[1] for r in h) / 1e6, s["bput"], kb(mean), s["maxrec"], s["maxrec"] * MB / mean,
               over(h, mean), big, s["secmean"], s["sec99"], s["secmax"], s["debtmax"], s["dmax"] / 1000))


def decrease_row(label, keys, p):
    rows = load(p)
    d = [i for i, r in enumerate(rows) if r[0] == 2]
    d0, d1 = d[0], d[-1]
    b = rows[d0 - 1]
    sd = rows[d1][12]
    j = next(i for i in range(d1, len(rows)) if rows[i][9] < 2 * sd)
    j1 = next(i for i in range(d1, len(rows)) if rows[i][9] < sd)
    rest, end = second_half(rows[j + 1:])
    s = steady(rest, end)
    mean = sum(r[5] for r in rest) / len(rest)
    cu = rows[d0:j + 1]
    user = [r for r in cu if r[0] == 1]
    u1 = [r for r in rows[d0:j1 + 1] if r[0] == 1]
    umx = max(r[5] for r in user)
    return ("| %s | %s | %.0f / %.0f MB | %.2f MB | %.2fM, %.0f MB, %d | %.2f MB (%.1f×) | %s | %.2fM, %.0f MB | %.0f kB | %.2f sd, %.2f MB |"
            % (label, keys, b[9] / MB, b[11] / MB, rows[d0][5] / MB,
               sum(r[1] for r in user) / 1e6, (rows[j][8] - b[8]) / MB, j - d0,
               umx / MB, umx / mean, over(cu, mean),
               sum(r[1] for r in u1) / 1e6, (rows[j1][8] - b[8]) / MB, mean / 1e3, s["secmax"], s["maxrec"]))


print("| run | keys | puts | B/put | mean record | largest record (× mean) | records over 3 / 5 / 10 × mean | over 100 kB | section mean / p99 / max (sd) | debt max (sd) | D max |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for kind, label in (("upd", "updates"), ("del", "deletes"), ("one", "single puts")):
    for sd in (50, 200, 1000):
        for keys, dd, v in (("10M", d10, "d4b"), ("50M", d50, "m50")):
            p = os.path.join(dd, "%s-%s-sd%d.rec" % (v, kind, sd))
            if done(p):
                print(steady_row("%s, %d MB" % (label, sd), keys, p))
print()
print("| decrease | keys | section / debt before | setStartupDistance's record | to 2 sd: puts, stream, records | largest user record (× new mean) | catch-up records over 3 / 5 / 10 × new mean | to sd: puts, stream | new mean record | after, 2nd half: section max, largest record |")
print("|---|---|---|---|---|---|---|---|---|---|")
for fr, to in ((1000, 100), (200, 50)):
    for tag in ("w", "t"):
        for keys, dd, v in (("10M", d10, "d4b"), ("50M", d50, "m50")):
            p = os.path.join(dd, "%s-low%d-%d-once-%s.rec" % (v, fr, to, tag))
            if done(p):
                print(decrease_row("%d to %d, %s" % (fr, to, "worst" if tag == "w" else "20M"), keys, p))
