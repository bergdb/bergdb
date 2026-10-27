#!/usr/bin/env python3
"""005-49: one line a WriteBench run (wb.rec), for comparing takes; see analyze.py.

Usage: summary.py SD_BYTES FILE.rec [FILE.rec ...]
With WB_PUTS=N in the environment, only the update phase's first N puts count (to compare runs
cut at different points: a long run ends where WriteBench's heap ends, as it retains every
version and never evicts).

Columns, over the update phase ("all") and its second half by puts ("2nd"), where the
take has settled after the load:
  B/put     the stream's bytes a put, all and 2nd
  idx       index bytes a put, 2nd
  maxrec    the largest record's index bytes (MB), all
  max/mean  the largest record's index bytes over the mean a record, 2nd
  >4x       the share of index bytes in records with more than 4 times the mean, 2nd
  section   the startup section after a record (the stream's end minus the startup pos),
            in sd: mean, p99 and max of 2nd, and max of all
  age       the mean age of a got-dirty id when written, in puts (analyze.py), all
"""
import os
import struct
import sys

REC = struct.Struct(">biiiqqqqq")   # phase, puts, index nodes, got-dirty, value bytes, record bytes, index bytes, lag, end


def load(path):
    data = open(path, "rb").read()
    return [REC.unpack_from(data, i * REC.size) for i in range(len(data) // REC.size)]


def pct(s, p):
    return s[min(len(s) - 1, max(0, int(round(p / 100.0 * (len(s) - 1)))))]


def age_puts(rows, first_upd):
    ends = [r[8] for r in rows]
    tpos = [0] + ends[:-1]
    sp = [e - r[7] for e, r in zip(ends, rows)]
    cum = [0]
    for r in rows:
        cum.append(cum[-1] + r[1])
    j = 0
    while j < len(rows) and tpos[j] <= sp[first_upd - 1]:
        j += 1
    w = s = 0
    for i in range(first_upd, len(rows)):
        while j < i and tpos[j] <= sp[i]:
            w += rows[j][3]
            s += rows[j][3] * (cum[i] - cum[j])
            j += 1
    return s / w if w else 0


def summary(sd, path):
    rows = load(path)
    first = sum(1 for r in rows if r[0] == 0)
    upd = rows[first:]
    if os.environ.get("WB_PUTS"):
        limit, acc, k = int(os.environ["WB_PUTS"]), 0, 0
        while k < len(upd) and acc < limit:
            acc += upd[k][1]
            k += 1
        upd = upd[:k]
        rows = rows[:first + k]
    start = rows[first - 1][8] if first else 0
    puts = sum(r[1] for r in upd)
    half, acc = 0, 0
    while acc < puts / 2:
        acc += upd[half][1]
        half += 1
    second = upd[half:]
    p2 = sum(r[1] for r in second)
    s2start = upd[half - 1][8]
    bput = (upd[-1][8] - start) / puts
    bput2 = (upd[-1][8] - s2start) / p2
    idx2 = [r[6] for r in second]
    mean2 = sum(idx2) / len(idx2)
    big = sum(i for i in idx2 if i > 4 * mean2) / max(1, sum(idx2))
    lag2 = sorted(r[7] / sd for r in second)
    lagall = max(r[7] / sd for r in upd)
    name = path.rsplit("/", 1)[-1].replace(".rec", "")
    print("%-24s %6.1f %6.1f %6.1f %7.2f %8.1f %6.1f%% %5.2f %5.2f %5.2f %5.2f %9.0f"
          % (name, bput, bput2, sum(idx2) / p2, max(r[6] for r in upd) / 1e6, max(idx2) / mean2,
             100 * big, sum(lag2) / len(lag2), pct(lag2, 99), lag2[-1], lagall, age_puts(rows, first)))


if __name__ == "__main__":
    sd = float(sys.argv[1])
    print("%-24s %6s %6s %6s %7s %8s %7s %5s %5s %5s %5s %9s"
          % ("run", "B/put", "2nd", "idx", "maxrec", "max/mean", ">4x", "sect", "p99", "max", "all", "age"))
    for p in sys.argv[2:]:
        summary(sd, p)
