#!/usr/bin/env python3
# bergdb 030-20: summary of the commit check's cost, from the logs of s1-run.sh. 2026-11-18.
# Usage: python3 -I summarize.py OUT PREFIX   (PREFIX: cc1m, cc10m, ...)
# For CCBench logs (PREFIX-rN-tcT.txt): per kind and transaction size, the median and range
# over the runs of the time per operation (execute's wall time over the phase's operations),
# off and on, the ratio of the medians, and the median time per transaction. Markdown.
import glob
import os
import re
import statistics
import sys


def parse(path):
    rows = {}
    for line in open(path):
        if not line.startswith("RESULT "):
            continue
        f = dict(kv.split("=", 1) for kv in line.split()[1:])
        rows[(f["kind"], int(f["tsize"]))] = f
    return rows


def main():
    out, prefix = sys.argv[1], sys.argv[2]
    runs = {0: [], 1: []}
    loads = {0: [], 1: []}
    for p in sorted(glob.glob(os.path.join(out, prefix + "-r*-tc*.txt"))):
        m = re.search(r"-tc(\d)\.txt$", p)
        tc = int(m.group(1))
        text = open(p).read()
        if "CCBENCH DONE" not in text:
            print("incomplete, skipped:", os.path.basename(p), file=sys.stderr)
            continue
        runs[tc].append(parse(p))
        lm = re.search(r"LOAD n=\d+ ([\d.]+) s, execute ([\d.]+) s", text)
        if lm:
            loads[tc].append(float(lm.group(2)))
    keys = []
    for r in runs[0] + runs[1]:
        for k in r:
            if k not in keys:
                keys.append(k)
    keys.sort(key=lambda k: (k[1], ["update", "insert", "delete", "mixed"].index(k[0])))

    def stat(vals):
        return statistics.median(vals), min(vals), max(vals)

    print(f"Runs: {len(runs[0])} off, {len(runs[1])} on.\n")
    if loads[0] and loads[1]:
        a, b = statistics.median(loads[0]), statistics.median(loads[1])
        print(f"Load (transactions of 500 puts, execute's time): off {a:.1f} s, on {b:.1f} s, "
              f"ratio {b / a:.2f}.\n")
    print("Time per operation in µs (median, range), and per transaction (median of the runs'"
          " medians):\n")
    for k in keys:
        off = [float(r[k]["op_mean_us"]) for r in runs[0] if k in r]
        on = [float(r[k]["op_mean_us"]) for r in runs[1] if k in r]
        if not off or not on:
            continue
        txoff = statistics.median(float(r[k]["tx_med_us"]) for r in runs[0] if k in r)
        txon = statistics.median(float(r[k]["tx_med_us"]) for r in runs[1] if k in r)
        mo, lo, ho = stat(off)
        mn, ln, hn = stat(on)
        print(f"- {k[0]}, {k[1]} a transaction: off {mo:.2f} ({lo:.2f}–{ho:.2f}), "
              f"on {mn:.2f} ({ln:.2f}–{hn:.2f}), ratio {mn / mo:.2f}; "
              f"a transaction {txoff:.0f} → {txon:.0f} µs")
    # Per transaction size, all kinds: the ratio of the summed medians.
    print()
    for t in sorted({k[1] for k in keys}):
        so = sum(statistics.median(float(r[k]["op_mean_us"]) for r in runs[0] if k in r)
                 for k in keys if k[1] == t)
        sn = sum(statistics.median(float(r[k]["op_mean_us"]) for r in runs[1] if k in r)
                 for k in keys if k[1] == t)
        print(f"- {t} a transaction, all kinds: ratio {sn / so:.2f}, the check "
              f"{100 * (sn - so) / sn:.0f} % of a commit with it")


main()
