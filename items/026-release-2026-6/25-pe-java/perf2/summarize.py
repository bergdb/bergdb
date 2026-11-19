#!/usr/bin/env python3
# bergdb 026-25, perf2: summary of the runs of main and pe (s1-run.sh's and f53-run.sh's logs), from
# 25-pe-java/s1/summarize.py; CCBench's logs named cc*-BUILD-rN?.txt. 2026-11-19.
# Usage: python3 -I summarize.py OUT
# CCBench (cc*-BUILD-rN?.txt): per kind and transaction size, the median over the runs of the
# time per operation (execute's wall time over the phase's operations) of main and pe, the
# ratio pe/main, and the load's puts per second and the stream's size. Perf
# (SCENARIO-BUILD-rN?/MODE.result.json): the median of each metric of main and pe, the ratio;
# the metrics of KEY below only, all with --all.
import glob
import json
import os
import re
import statistics
import sys

out = sys.argv[1]
ALL = "--all" in sys.argv
KEY = ["commits", "commits_per_s", "commit.append.mean_us", "commit.append.p99_us",
       "commit.append.p999_us", "commit.append.max_us", "load.puts_per_s", "bytes_appended_per_put",
       "stream_appended_mb", "gc.mxbean.count", "gc.mxbean.time_ms", "heap.after_gc_mb_max",
       "rss_mb_max", "reclaim.steps", "reclaim.cuts_physical", "kept_mb_max", "restart.startup_sec"]


def cc(build):
    runs, loads, streams = [], [], []
    for p in sorted(glob.glob(os.path.join(out, "cc*-%s-r*.txt" % build))):
        rows = {}
        for line in open(p):
            if line.startswith("RESULT "):
                f = dict(kv.split("=", 1) for kv in line.split()[1:])
                rows[(f["kind"], int(f["tsize"]))] = float(f["op_mean_us"])
            elif line.startswith("LOAD "):
                loads.append(float(re.search(r"([0-9.]+) puts/s", line).group(1)))
            elif line.startswith("STREAM "):
                streams.append(int(line.split()[1]))
        if rows:
            runs.append(rows)
    return runs, loads, streams


rm, lm, sm = cc("main")
rp, lp, sp = cc("pe")
if rm and rp:
    print(f"CCBench: {len(rm)} runs of main, {len(rp)} of pe; µs an operation, median (range)")
    ratios = []
    for key in rm[0]:
        a = [r[key] for r in rm if key in r]
        b = [r[key] for r in rp if key in r]
        if not a or not b:
            continue
        ma, mb = statistics.median(a), statistics.median(b)
        ratios.append(mb / ma)
        print(f"- {key[0]} {key[1]}: main {ma:.2f} ({min(a):.2f}-{max(a):.2f}), "
              f"pe {mb:.2f} ({min(b):.2f}-{max(b):.2f}), pe/main {mb / ma:.3f}")
    print(f"- geometric mean of pe/main over the {len(ratios)} cases: "
          f"{statistics.geometric_mean(ratios):.3f}")
    print(f"- load puts/s: main {statistics.median(lm):.0f}, pe {statistics.median(lp):.0f}, "
          f"pe/main {statistics.median(lp) / statistics.median(lm):.3f}")
    print(f"- stream MB: main {statistics.median(sm)}, pe {statistics.median(sp)}")

res = {}
for p in glob.glob(os.path.join(out, "*-r*", "*.result.json")):
    label = os.path.basename(os.path.dirname(p))
    m = re.match(r"(.*)-(main|pe)-r\d+[ab]$", label)
    if not m:
        continue
    r = json.load(open(p))
    if r.get("status") not in (None, "ok", "OK"):
        print("not ok:", label, r.get("status"))
        continue
    res.setdefault(m.group(1), {}).setdefault(m.group(2), []).append(r.get("metrics", {}))
for sc in sorted(res):
    by = res[sc]
    if "main" not in by or "pe" not in by:
        continue
    print(f"Perf {sc}: {len(by['main'])} runs of main, {len(by['pe'])} of pe; medians")
    keys = sorted(set(k for m in by["main"] for k, v in m.items() if isinstance(v, (int, float))))
    if not ALL:
        keys = [k for k in KEY if k in keys]
    for k in keys:
        a = [m[k] for m in by["main"] if k in m]
        b = [m[k] for m in by["pe"] if k in m]
        if not a or not b:
            continue
        ma, mb = statistics.median(a), statistics.median(b)
        ratio = f"{mb / ma:.3f}" if ma else "-"
        print(f"- {k}: main {ma:.4g} ({min(a):.4g}-{max(a):.4g}), pe {mb:.4g} ({min(b):.4g}-{max(b):.4g}), pe/main {ratio}")
