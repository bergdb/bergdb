#!/usr/bin/env python3
# bergdb 030-20: summary of the Perf runs of s1-run.sh (jobs-perf.txt), the check off and on.
# 2026-11-18. Usage: python3 -I perf-summary.py OUT
# For each scenario (OUT/SCENARIO-rN-tcT/write.result.json): the median and range over the
# runs of the measured phase's puts per second and of the append commit's (and the durable
# commit's, if any) mean, median and 99th percentile latency, off and on, and the ratio of the medians. Markdown.
import glob
import json
import os
import re
import statistics
import sys

out = sys.argv[1]
runs = {}
for p in sorted(glob.glob(os.path.join(out, "*-r*-tc*", "write.result.json"))):
    label = os.path.basename(os.path.dirname(p))
    m = re.match(r"(.*)-r(\d+)-tc(\d)$", label)
    r = json.load(open(p))
    if r.get("status") not in (None, "ok", "OK"):
        print("not ok, skipped:", label, r.get("status"), file=sys.stderr)
        continue
    runs.setdefault(m.group(1), {0: [], 1: []})[int(m.group(3))].append(r["metrics"])

fields = [("puts_per_s", "puts/s", 0), ("commit.append.mean_us", "mean µs", 1),
          ("commit.append.p50_us", "p50 µs", 1), ("commit.append.p99_us", "p99 µs", 1),
          ("commit.durable.mean_us", "durable mean µs", 1), ("commit.durable.p50_us", "durable p50 µs", 1),
          ("commit.durable.p99_us", "durable p99 µs", 1)]
for sc, by in runs.items():
    print(f"- {sc}: {len(by[0])} off, {len(by[1])} on")
    for key, name, dec in fields:
        off = [m[key] for m in by[0] if key in m]
        on = [m[key] for m in by[1] if key in m]
        if not off or not on:
            continue
        mo, mn = statistics.median(off), statistics.median(on)
        f = f"{{:.{dec}f}}"
        print(f"  - {name}: off {f.format(mo)} ({f.format(min(off))}–{f.format(max(off))}), "
              f"on {f.format(mn)} ({f.format(min(on))}–{f.format(max(on))}), "
              f"on/off {mn / mo:.2f}")
