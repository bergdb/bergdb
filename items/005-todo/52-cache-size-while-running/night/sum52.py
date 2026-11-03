#!/usr/bin/env python3
"""bergdb 005-52's summary of lowered.sh's runs (016-05; 005-52, Plan for 2026.2).

Reads OUT/RUN.txt of PauseProbe for the runs zgc-a1 zgc-b zgc-a2 g1-a1 g1-b g1-a2 and
prints, as Markdown:

* one row per run and phase: the gets' count, p99.9 and longest wait; the commits' count,
  p99.9 and longest wait; the resident bytes at the phase's end and the longest eviction
  batch so far (PauseProbe's eviction line, CacheStats: "ms at most"); for (b), the
  lowering and the seconds until the resident bytes reached the lower budget;
* the comparison for each collector and phase: (b) against the larger of a1 and a2, and the
  spread between a1 and a2; "longer" when (b) exceeds that larger value by more than the
  spread (005-52, Left to do: "no wait in (b) is longer than in (a) beyond the spread
  between two runs of (a)");
* the five longest gets and commits of each (b) phase with their JVM uptimes, to find in
  RUN.gc.log.

Exits 1, with a last line "incomplete: ...", unless every run has all its phases (the
tsize list of its header) and each phase of a (b) run has its "lowered:" line.
Usage: python3 sum52.py OUT.  Created 2026-11-03 by Frans Lundberg.
"""
import os
import re
import sys

RUNS = ["zgc-a1", "zgc-b", "zgc-a2", "g1-a1", "g1-b", "g1-a2"]
LAT = re.compile(r"^\s+(gets|commits)\s+(\d+), median ([\d.]+) ms, p99 ([\d.]+), "
                 r"p99\.9 ([\d.]+), p99\.99 ([\d.]+), max ([\d.]+) ms; longest at uptime(.*)$")
EVICT = re.compile(r"^\s+resident (\d+) MB, .* ([\d.]+) ms at most")
LOWERED = re.compile(r"^\s+lowered: (.*)$")
REACHED = re.compile(r"reached in ([\d.]+) s")
PHASE = re.compile(r"^phase tsize=(\d+),")
HEADER = re.compile(r"^PauseProbe: .*tsize=\[([\d, ]+)\]")


def parse(path):
    """Returns (tsizes from the header, {tsize: phase dict}) for one run's output."""
    tsizes, phases, cur = [], {}, None
    with open(path, errors="replace") as f:
        for line in f:
            line = line.rstrip("\n")
            m = HEADER.match(line)
            if m:
                tsizes = [int(x) for x in m.group(1).split(",")]
                continue
            m = PHASE.match(line)
            if m:
                cur = {"tsize": int(m.group(1))}
                phases[cur["tsize"]] = cur
                continue
            if line.startswith("load:"):
                cur = None
                continue
            if cur is None:
                continue
            m = LOWERED.match(line)
            if m:
                cur["lowered"] = m.group(1)
                r = REACHED.search(m.group(1))
                cur["reached"] = r.group(1) if r else "not reached"
                continue
            m = LAT.match(line)
            if m:
                cur[m.group(1)] = {"n": int(m.group(2)), "p999": float(m.group(5)),
                                   "max": float(m.group(7)), "top": m.group(8).strip()}
                continue
            m = EVICT.match(line)
            if m:
                cur["resident"] = int(m.group(1))
                cur["batch"] = float(m.group(2))
    return tsizes, phases


def fmt(x):
    return "%.2f" % x


def main():
    out = sys.argv[1]
    problems, data = [], {}
    for run in RUNS:
        path = os.path.join(out, run + ".txt")
        if not os.path.exists(path):
            problems.append(run + ": no output")
            continue
        tsizes, phases = parse(path)
        if not tsizes:
            problems.append(run + ": no header")
        for t in tsizes:
            p = phases.get(t)
            if p is None or "gets" not in p or "commits" not in p:
                problems.append("%s: phase tsize=%d missing" % (run, t))
            elif run.endswith("-b") and "lowered" not in p:
                problems.append("%s: phase tsize=%d without its lowering" % (run, t))
        data[run] = (tsizes, phases)

    print("# PauseProbe with a lowered budget (bergdb 005-52)\n")
    print("Times in ms. Resident: at the phase's end, MB. Batch: the longest eviction batch")
    print("so far in the run. Reached: seconds from the lowering to the lower budget.\n")
    print("| run | phase | gets | p99.9 | max | commits | p99.9 | max | resident | batch "
          "| reached |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    rows = 0
    for run in RUNS:
        if run not in data:
            continue
        tsizes, phases = data[run]
        for t in tsizes:
            p = phases.get(t)
            if not p or "gets" not in p or "commits" not in p:
                continue
            g, c = p["gets"], p["commits"]
            print("| %s | tsize=%d | %d | %s | %s | %d | %s | %s | %s | %s | %s |" % (
                run, t, g["n"], fmt(g["p999"]), fmt(g["max"]), c["n"], fmt(c["p999"]),
                fmt(c["max"]), p.get("resident", "-"), fmt(p["batch"]) if "batch" in p else "-",
                p.get("reached", "-")))
            rows += 1

    print("\n## (b) against (a)\n")
    print("Longer: (b) above the larger of a1 and a2 by more than the spread |a1 - a2|.\n")
    print("| gc | phase | what | a1 | a2 | b | spread | verdict |")
    print("|---|---|---|---|---|---|---|---|")
    longer = 0
    for gc in ("zgc", "g1"):
        runs = [gc + "-a1", gc + "-a2", gc + "-b"]
        if not all(r in data for r in runs):
            continue
        for t in data[gc + "-b"][0]:
            ps = [data[r][1].get(t) for r in runs]
            if not all(p and "gets" in p and "commits" in p for p in ps):
                continue
            for what in ("gets", "commits"):
                for q in ("p999", "max"):
                    a1, a2, b = (p[what][q] for p in ps)
                    spread = abs(a1 - a2)
                    bad = b - max(a1, a2) > spread
                    longer += bad
                    print("| %s | tsize=%d | %s %s | %s | %s | %s | %s | %s |" % (
                        gc, t, what, "p99.9" if q == "p999" else "max", fmt(a1), fmt(a2),
                        fmt(b), fmt(spread), "LONGER" if bad else "ok"))

    print("\n## The longest waits of (b), by JVM uptime (for RUN.gc.log)\n")
    for gc in ("zgc", "g1"):
        run = gc + "-b"
        if run not in data:
            continue
        for t in data[run][0]:
            p = data[run][1].get(t)
            if not p:
                continue
            print("* %s, tsize=%d: lowered: %s" % (run, t, p.get("lowered", "-")))
            for what in ("gets", "commits"):
                if what in p:
                    print("  * %s: %s" % (what, p[what]["top"]))

    expected = sum(len(data[r][0]) for r in data) if data else 0
    print("\nRows: %d of %d; comparisons longer: %d." % (rows, expected, longer))
    if rows != 12:
        problems.append("%d rows, not 12" % rows)
    if problems:
        print("incomplete: " + "; ".join(problems))
        sys.exit(1)
    print("complete")


if __name__ == "__main__":
    main()
