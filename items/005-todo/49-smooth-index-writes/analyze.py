#!/usr/bin/env python3
"""005-49: every record of a WriteBench run (wb.rec), the update phase.

Usage: analyze.py SD_BYTES FILE.rec [FILE.rec ...]

For each file: the stream's bytes a put; a record's index bytes against its own bytes (its
value nodes and a 48-byte header): percentiles, the largest records; the bursts (records
whose index bytes pass 10 times their own bytes, and how often they come); the startup lag
after each record in units of sd; the age of a transaction when its nodes are written, in
bytes and in puts; bytes a put in windows of 1M puts.
"""
import struct
import sys

REC = struct.Struct(">biiiqqqqq")   # phase, puts, index nodes, got-dirty, value bytes, record bytes, index bytes, lag, end


def load(path):
    data = open(path, "rb").read()
    n = len(data) // REC.size
    rows = [REC.unpack_from(data, i * REC.size) for i in range(n)]
    return rows


def pct(sorted_vals, p):
    if not sorted_vals:
        return 0
    k = min(len(sorted_vals) - 1, max(0, int(round(p / 100.0 * (len(sorted_vals) - 1)))))
    return sorted_vals[k]


def analyze(sd, path):
    rows = load(path)
    load_rows = [r for r in rows if r[0] == 0]
    upd = [r for r in rows if r[0] == 1]
    start = load_rows[-1][8] if load_rows else 0     # the stream's end after the load
    end = upd[-1][8]
    puts = sum(r[1] for r in upd)
    stream = end - start
    idx = [r[6] for r in upd]
    own = [r[4] + 48 for r in upd]                   # value nodes and a 48-byte header
    total_idx = sum(idx)
    total_own = sum(own)
    nodes = sum(r[2] for r in upd)
    print("== %s" % path)
    print("records %d, puts %d, stream %.3f GB, %.1f B/put; index %.1f B/put (%.2f x own bytes,"
          " %.3f nodes/put, %.0f B/node); own %.1f B/put; got-dirty %.3f/put"
          % (len(upd), puts, stream / 1e9, stream / puts, total_idx / puts, total_idx / total_own,
             nodes / puts, total_idx / max(1, nodes), total_own / puts, sum(r[3] for r in upd) / puts))
    s_idx = sorted(idx)
    mean = total_idx / len(upd)
    print("index bytes a record: mean %.0f; p50 %d, p90 %d, p99 %d, p99.9 %d, max %d"
          % (mean, pct(s_idx, 50), pct(s_idx, 90), pct(s_idx, 99), pct(s_idx, 99.9), s_idx[-1]))
    ratio = sorted(i / o for i, o in zip(idx, own))
    print("index / own bytes a record: p50 %.2f, p90 %.2f, p99 %.2f, p99.9 %.2f, max %.2f"
          % (pct(ratio, 50), pct(ratio, 90), pct(ratio, 99), pct(ratio, 99.9), ratio[-1]))
    rec = sorted(r[5] for r in upd)
    print("record bytes: p50 %d, p99 %d, max %d" % (pct(rec, 50), pct(rec, 99), rec[-1]))
    zero = sum(1 for i in idx if i == 0)
    print("records with no index node: %d (%.1f%%)" % (zero, 100.0 * zero / len(upd)))
    # Bursts: records whose index bytes pass 10 times their own bytes; an episode is a run
    # of them with gaps of at most 5 records.
    burst = [i for i, r in enumerate(upd) if r[6] > 10 * (r[4] + 48)]
    episodes = []
    for i in burst:
        if episodes and i - episodes[-1][-1] <= 6:
            episodes[-1].append(i)
        else:
            episodes.append([i])
    bb = sum(upd[i][6] for i in burst)
    print("bursts (index > 10 x own bytes): %d records (%.2f%%), %.1f%% of the index bytes, %d episodes, %.2f a sd"
          % (len(burst), 100.0 * len(burst) / len(upd), 100.0 * bb / max(1, total_idx), len(episodes),
             len(episodes) / (stream / sd)))
    if len(episodes) > 1:
        starts = [(upd[e[0]][8] - upd[p[0]][8]) / sd for p, e in zip(episodes, episodes[1:])]
        lens = [(upd[e[-1]][8] - upd[e[0]][8] + upd[e[0]][5]) / sd for e in episodes]
        recs = sorted(len(e) for e in episodes)
        sb = sorted(starts)
        print("  episodes: %d to %d records (median %d), %.3f to %.3f sd long (mean %.3f);"
              " starts %.2f to %.2f sd apart (median %.2f)"
              % (recs[0], recs[-1], recs[len(recs) // 2], min(lens), max(lens), sum(lens) / len(lens),
                 sb[0], sb[-1], sb[len(sb) // 2]))
    # Concentration: the fewest records that write half and 90 percent of the index bytes.
    desc = sorted(idx, reverse=True)
    acc, n50, n90 = 0, None, None
    for k, v in enumerate(desc):
        acc += v
        if n50 is None and acc >= 0.5 * total_idx:
            n50 = k + 1
        if n90 is None and acc >= 0.9 * total_idx:
            n90 = k + 1
    print("half of the index bytes in %.1f%% of the records, 90%% in %.1f%%"
          % (100.0 * n50 / len(upd), 100.0 * n90 / len(upd)))
    # Profile: index bytes a put in bins of sd / 4 of stream, 16 bins from the middle.
    mid = start + (end - start) // 2
    bins = [[0, 0] for _ in range(16)]
    for r in upd:
        b = int((r[8] - mid) // (sd / 4))
        if 0 <= b < 16:
            bins[b][0] += r[6]
            bins[b][1] += r[1]
    print("profile, index bytes a put by sd/4 from the middle: "
          + " ".join("%.0f" % (b[0] / b[1]) if b[1] else "-" for b in bins))
    top = sorted(range(len(upd)), key=lambda i: -upd[i][6])[:5]
    print("largest records (index bytes, puts, at sd from the phase's start, lag before):")
    for i in top:
        r = upd[i]
        before = upd[i - 1][7] if i > 0 else 0
        print("  %9d B, %d puts, %.2f MB record, at %.2f sd, lag before %.2f sd"
              % (r[6], r[1], r[5] / 1e6, (r[8] - start) / sd, before / sd))
    lags = sorted(r[7] / sd for r in upd)
    over15 = sum(1 for x in lags if x > 1.5)
    over2 = sum(1 for x in lags if x > 2.0)
    print("startup lag after a record (sd): mean %.2f; p1 %.2f, p50 %.2f, p90 %.2f, p99 %.2f, max %.2f;"
          " over 1.5 sd %.1f%%, over 2 sd %.2f%%"
          % (sum(lags) / len(lags), pct(lags, 1), pct(lags, 50), pct(lags, 90), pct(lags, 99), lags[-1],
             100.0 * over15 / len(lags), 100.0 * over2 / len(lags)))
    # The age of a transaction when its nodes are written: from its position to the stream's
    # end before the record that takes it, weighted by its got-dirty ids. A record starts at
    # the end of the one before; the startup pos after a record is its end minus its lag.
    ends = [r[8] for r in rows]
    tpos = [0] + ends[:-1]
    sp = [e - r[7] for e, r in zip(ends, rows)]
    first_upd = len(load_rows)
    cum = [0]
    for r in rows:
        cum.append(cum[-1] + r[1])      # puts before record k: cum[k]
    j = 0
    while j < len(rows) and tpos[j] <= sp[first_upd - 1]:
        j += 1
    wsum = asum = psum = 0
    ages = []
    for i in range(first_upd, len(rows)):
        while j < i and tpos[j] <= sp[i]:
            g = rows[j][3]
            age = (ends[i - 1] - tpos[j]) / sd
            wsum += g
            asum += g * age
            psum += g * (cum[i] - cum[j])
            ages.append((age, g))
            j += 1
    if wsum:
        ages.sort()
        acc, med, p90 = 0, None, None
        for a, g in ages:
            acc += g
            if med is None and acc >= wsum / 2:
                med = a
            if p90 is None and acc >= 0.9 * wsum:
                p90 = a
        print("age at write (sd, weighted by got-dirty ids): mean %.2f, median %.2f, p90 %.2f, max %.2f;"
              " in puts: mean %.0f, %.2f sd at the phase's bytes a put"
              % (asum / wsum, med, p90, ages[-1][0], psum / wsum, psum / wsum * (stream / puts) / sd))
    # Windows of 1M puts, as 005-38.
    w, wp, wstart, out = 0, 0, start, []
    for r in upd:
        wp += r[1]
        if wp >= 1000000:
            out.append((r[8] - wstart) / wp)
            wstart, wp = r[8], 0
    print("B/put, windows of 1M puts: " + " ".join("%.0f" % x for x in out))
    print()


if __name__ == "__main__":
    sd = float(sys.argv[1])
    for p in sys.argv[2:]:
        analyze(sd, p)
