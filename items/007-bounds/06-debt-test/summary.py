#!/usr/bin/env python3
"""007-06: summary of WriteBench runs (wb.rec of 77 bytes a record; see WriteBench's comment).

Usage: summary.py FILE.rec [FILE.rec ...]

For each run, over the workload after the load (phases 1 and 2):
  B/put      the stream's bytes a put (a delete counts as a put), all and second half
  maxrec     the largest record (MB) and the largest index bytes of a record (MB)
  sec        the section without its last record (R(s+1)..R(k-1)), in sd: mean, p99, max
  lag        the stream's end minus the startup pos, max, in sd
  D, debt    the largest D (nodes) and debt (MB and in sd), the debt when the section
             was at its largest, and the largest section plus debt (in sd)
For a run with a decrease of the startup distance (phase 2 records), also: the state just
before it, the dummy records, and from the first dummy record: the puts and stream bytes until
the section is first below the new d_h = 2 sd and until it stays below it, the largest record
and index bytes meanwhile, the same for the new sd, and the section after that.
"""
import struct
import sys

REC = struct.Struct(">biiiqqqqqqiqi")
# fields: 0 phase, 1 puts, 2 index nodes, 3 got-dirty, 4 value bytes, 5 record bytes,
# 6 index bytes, 7 lag, 8 end, 9 section without last, 10 D nodes, 11 debt, 12 sd
MB = 1e6


def load(path):
    data = open(path, "rb").read()
    return list(REC.iter_unpack(data[: len(data) - len(data) % REC.size]))


def pct(s, p):
    return s[min(len(s) - 1, max(0, int(round(p / 100.0 * (len(s) - 1)))))]


def stats(rows, start_end, label):
    if not rows:
        return label + ": none"
    puts = sum(r[1] for r in rows)
    stream = rows[-1][8] - start_end
    sec = sorted(r[9] / r[12] for r in rows)
    imax = max(range(len(rows)), key=lambda i: rows[i][9] / rows[i][12])
    rmax = max(rows, key=lambda r: r[11])
    return ("%s: %d puts, B/put %.0f; maxrec %.2f MB, idx %.2f MB; sec mean %.2f p99 %.2f max %.2f sd;"
            " lag max %.2f sd; D max %d nodes, debt max %.0f MB (%.2f sd), debt at max sec %.2f sd; sec+debt max %.2f sd"
            % (label, puts, stream / max(1, puts), max(r[5] for r in rows) / MB, max(r[6] for r in rows) / MB,
               sum(sec) / len(sec), pct(sec, 99), sec[-1], max(r[7] / r[12] for r in rows),
               max(r[10] for r in rows), rmax[11] / MB, rmax[11] / rmax[12], rows[imax][11] / rows[imax][12], max((r[9] + r[11]) / r[12] for r in rows)))


def until(rows, base_end, limit, first_dummy_tpos, last_dummy_i):
    """From the first dummy: puts and bytes until the section is first < limit after the
    dummies, and until it stays < limit; the largest record and index bytes meanwhile."""
    first = None
    last_above = None
    for i in range(last_dummy_i, len(rows)):
        if rows[i][9] < limit:
            if first is None:
                first = i
        else:
            last_above = i
    out = []
    stays = None
    if last_above is None:
        stays = first
    elif last_above + 1 < len(rows):
        stays = last_above + 1
    for name, j in (("first below", first), ("stays below", stays)):
        if j is None or j >= len(rows):
            out.append("%s: never" % name)
            continue
        seg = rows[base_end: j + 1]
        user = [r for r in seg if r[0] == 1]
        puts = sum(r[1] for r in user)
        out.append("%s: %d puts, %.0f MB of stream, largest user record %.2f MB (idx %.2f MB)"
                   % (name, puts, (rows[j][8] - first_dummy_tpos) / MB,
                      max([r[5] for r in user] or [0]) / MB, max([r[6] for r in user] or [0]) / MB))
    return "; ".join(out)


def main():
    for path in sys.argv[1:]:
        rows = load(path)
        n0 = next((i for i, r in enumerate(rows) if r[0] != 0), len(rows))
        load_end = rows[n0 - 1][8] if n0 else 0
        work = rows[n0:]
        print("== %s: %d records, %d after the load" % (path, len(rows), len(work)))
        dummies = [i for i in range(n0, len(rows)) if rows[i][0] == 2]
        if not dummies:
            print("  " + stats(work, load_end, "all"))
            half = sum(r[1] for r in work) / 2
            acc = 0
            for i, r in enumerate(work):
                acc += r[1]
                if acc >= half:
                    break
            print("  " + stats(work[i + 1:], work[i][8], "2nd half"))
            continue
        d0, d1 = dummies[0], dummies[-1]
        pre = rows[n0:d0]
        print("  " + stats(pre, load_end, "before"))
        b = rows[d0 - 1]
        print("  at the decrease: sec %.0f MB, lag %.0f MB, D %d nodes, debt %.0f MB, sd %d -> %d MB"
              % (b[9] / MB, b[7] / MB, b[10], b[11] / MB, b[12] / MB, rows[d1][12] / MB))
        dm = [rows[i] for i in dummies]
        first_tpos = rows[d0 - 1][8]
        print("  dummies: %d records, %.1f MB in all, largest %.2f MB (idx %.2f MB); after them sec %.0f MB, debt %.0f MB"
              % (len(dm), (rows[d1][8] - first_tpos) / MB, max(r[5] for r in dm) / MB,
                 max(r[6] for r in dm) / MB, rows[d1][9] / MB, rows[d1][11] / MB))
        newsd = rows[d1][12]
        for f, name in ((2, "2 sd"), (1, "sd")):
            print("  to %s (%.0f MB): %s" % (name, f * newsd / MB, until(rows, d0, f * newsd, first_tpos, d1)))
        # after: from where the section is first below 2 sd, the rest
        j = next((i for i in range(d1, len(rows)) if rows[i][9] < 2 * newsd), None)
        if j is not None and j + 1 < len(rows):
            rest = rows[j + 1:]
            print("  " + stats(rest, rows[j][8], "after"))
            half = len(rest) // 2
            print("  " + stats(rest[half:], rest[half - 1][8] if half else rows[j][8], "after, 2nd half"))


if __name__ == "__main__":
    main()
