#!/usr/bin/env python3
"""007-06: the tables of 06-debt-test.md, from the runs' wb.rec files (see summary.py).

Usage: tables.py OUTDIR VARIANT...   (VARIANT head or paced)
Steady runs are measured over the second half of the workload by puts; a run with a decrease
from the first dummy record (phase 2) on, and "after" from where the section is first below
the new 2 sd to the end, over its second half by puts."""
import os
import sys

from summary import load, pct

MB = 1e6


def second_half(work):
    half = sum(r[1] for r in work) / 2
    acc = 0
    for i, r in enumerate(work):
        acc += r[1]
        if acc >= half:
            return work[i + 1:], work[i][8]
    return [], 0


def steady(rows, start_end):
    puts = sum(r[1] for r in rows)
    sec = sorted(r[9] / r[12] for r in rows)
    return {
        "bput": (rows[-1][8] - start_end) / puts,
        "maxrec": max(r[5] for r in rows) / MB,
        "own": max(r[5] - r[6] for r in rows),
        "secmean": sum(sec) / len(sec), "secmax": sec[-1], "sec99": pct(sec, 99),
        "debtmax": max(r[11] / r[12] for r in rows),
        "dmax": max(r[10] for r in rows),
        "sum": max((r[9] + r[11]) / r[12] for r in rows),
    }


def steady_row(name, path):
    rows = load(path)
    work = [r for r in rows if r[0] != 0]
    h, end = second_half(work)
    s = steady(h, end)
    return ("| %s | %.0f | %.2f | %.2f / %.2f / %.2f | %.2f | %.0fk | %.2f |"
            % (name, s["bput"], s["maxrec"], s["secmean"], s["sec99"], s["secmax"], s["debtmax"],
               s["dmax"] / 1000, s["sum"]))


def decrease_row(name, path):
    rows = load(path)
    d = [i for i, r in enumerate(rows) if r[0] == 2]
    d0, d1 = d[0], d[-1]
    b = rows[d0 - 1]
    newsd = rows[d1][12]
    t0 = b[8]
    dm = [rows[i] for i in d]
    out = ["| %s | %.0f / %.0f MB | %d, %.0f MB, %.2f MB |" % (
        name, b[9] / MB, b[11] / MB, len(dm), sum(r[5] for r in dm) / MB, max(r[5] for r in dm) / MB)]
    for f in (2, 1):
        j = next((i for i in range(d1, len(rows)) if rows[i][9] < f * newsd), None)
        if j is None:
            out.append(" never |")
            continue
        seg = [r for r in rows[d0:j + 1] if r[0] == 1]
        out.append(" %.2fM, %.0f MB, %.2f MB |" % (sum(r[1] for r in seg) / 1e6, (rows[j][8] - t0) / MB,
                                                   max([r[5] for r in seg] or [0]) / MB))
        if f == 2:
            j2 = j
    rest, end = second_half(rows[j2 + 1:])
    s = steady(rest, end)
    out.append(" %.2f sd, %.2f MB |" % (s["secmax"], s["maxrec"]))
    return "".join(out)


def done(p):
    """The run of p (a wb.rec) has ended."""
    t = p[:-4] + ".txt"
    return os.path.exists(p) and os.path.exists(t) and "WRITEBENCH OK" in open(t).read()


def main():
    od = sys.argv[1]
    for v in sys.argv[2:]:
        print("\n%s, steady runs: run | B/put | largest record (MB) | section mean / p99 / max (sd) |"
              " debt max (sd) | D max (nodes) | section + debt max (sd)" % v)
        for kind, label in (("upd", "updates"), ("del", "deletes"), ("one", "single puts")):
            for sd in (50, 200, 1000):
                p = os.path.join(od, "%s-%s-sd%d.rec" % (v, kind, sd))
                if done(p):
                    print(steady_row("%s, %d MB" % (label, sd), p))
        print("\n%s, decreases: run | at it: section / debt | dummy records: count, MB, largest |"
              " to 2 sd: puts, stream, largest user record | to sd: the same | after, second half: section max, largest record" % v)
        for fr, to in ((1000, 100), (200, 50)):
            for tag in ("w", "t"):
                for how in ("once", "steps", "follow", "pace"):
                    vv = v + {"follow": "2", "pace": "3"}.get(how, "")
                    p = os.path.join(od, "%s-low%d-%d-%s-%s.rec" % (vv, fr, to, how, tag))
                    if done(p):
                        print(decrease_row("%d to %d, %s, %s" % (fr, to, how, "worst" if tag == "w" else "20M"), p))


if __name__ == "__main__":
    main()
