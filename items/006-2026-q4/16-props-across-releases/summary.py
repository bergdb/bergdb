#!/usr/bin/env python3
"""bergdb 006-16: tables from the run files of run.sh.

    python3 -I summary.py [RUNS_DIR] > summary.txt

Per version (in time order) the median, minimum and maximum of each number over its
runs: MEM and SS from every run (Props runs and the mem and ss runs); CORE and its
parts only from timed runs (run.sh rounds: "timed: yes", taken on a quiet machine).
Ratios: CORE to its 1.00 (cissi, July 2013) is the value itself; to 2026.3 the ratio
of the medians. Runs in subdirectories (failed/, smoke/) are not read.
"""

import os
import re
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "runs")
ORDER_V = ["2013.1", "2013-07-05", "2013.3", "2014.1", "2015.1", "2015.4", "2015-12-28",
           "2017-07-29", "2017-08-01", "2026-10-19", "2026.1", "2026.2", "2026.3", "2026.4c"]
PARTS = {"CORE": ["get", "get4t", "getmany", "set"], "SS": ["SS1", "SS2", "SS3", "SS4"]}


def parse(path):
    head, body = {}, []
    with open(path) as f:
        lines = f.read().splitlines()
    i = 0
    while i < len(lines) and lines[i] != "----":
        k, _, v = lines[i].partition(": ")
        head[k] = v
        i += 1
    body = "\n".join(lines[i + 1:])
    vals = {}
    m = re.search(r"MEM:(\d+)", body)
    if m:
        vals["MEM"] = float(m.group(1))
    for name, parts in PARTS.items():
        m = re.search(name + r":([0-9.]+) \(([^)]*)\)", body)
        if m:
            vals[name] = float(m.group(1))
            for p, v in zip(parts, m.group(2).split(",")):
                vals[p] = float(v)
    head["values"] = vals
    head["timed"] = head.get("timed", "").startswith("yes")
    head["done"] = "seconds: " in body and "EXIT CODE" not in body
    return head


def stats(rs, name):
    xs = [r["values"][name] for r in rs if name in r["values"]]
    if not xs:
        return None
    return statistics.median(xs), min(xs), max(xs), len(xs)


def fmt(x, name):
    if name == "MEM":
        return "%.0f" % x if abs(x - round(x)) < 1e-6 else "%.1f" % x
    if abs(x * 100 - round(x * 100)) > 1e-6:
        return "%.3f" % x
    return "%.2f" % x


def cell(s, name):
    if s is None:
        return "-"
    m, lo, hi, n = s
    if lo == hi:
        return "%s (%d)" % (fmt(m, name), n)
    return "%s (%s-%s, %d)" % (fmt(m, name), fmt(lo, name), fmt(hi, name), n)


def table(title, names, runs, ref="2026.3"):
    print("== %s ==" % title)
    print()
    print("| Version | Commit | " + " | ".join(names) + " | %s / %s |" % (names[0], ref))
    print("|---|---|" + "---|" * (len(names) + 1))
    refs = stats(runs.get(ref, []), names[0])
    for v in ORDER_V:
        rs = runs.get(v, [])
        if not rs:
            print("| %s | | not run |" % v)
            continue
        st0 = stats(rs, names[0])
        ratio = "%.2f" % (st0[0] / refs[0]) if st0 and refs else "-"
        print("| %s | %s | %s | %s |" % (v, rs[0].get("commit", "")[:7],
                                         " | ".join(cell(stats(rs, n), n) for n in names), ratio))
    print("(each cell: median (min-max, number of runs))")
    print()


def main():
    files = [f for f in sorted(os.listdir(RUNS)) if f.endswith(".txt") and f != "machine.txt"]
    runs = [parse(os.path.join(RUNS, f)) for f in files]
    runs = [r for r in runs if r["done"]]
    by_v = {}
    for r in runs:
        by_v.setdefault(r["version"], []).append(r)
    timed = {v: [r for r in rs if r["timed"]] for v, rs in by_v.items()}
    print("Runs read: %d (%d timed) from %s" % (len(runs), sum(len(x) for x in timed.values()), RUNS))
    print()
    table("MEM, heap bytes per KV", ["MEM"], by_v)
    table("SS, stream bytes per user byte", ["SS"] + PARTS["SS"], by_v)
    if any(timed.values()):
        table("CORE, timed runs only (1.00 = cissi, July 2013)", ["CORE"] + PARTS["CORE"],
              {v: rs for v, rs in timed.items() if rs})
    else:
        print("== CORE ==")
        print()
        print("No timed runs: CORE not run (run.sh rounds main 6 on a quiet F53).")
        print()


if __name__ == "__main__":
    main()
