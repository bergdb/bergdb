"""005-13: the sweep's tables, from runs/round*/<scenario>/run1/write.result.json.
Each cell is the median over the rounds, with the range when it is wider than 10 percent.
Usage: python3 -I tools/table.py RUNSDIR > table.md
"""
import glob, json, os, re, statistics, sys

runs = sys.argv[1]
data = {}
for f in sorted(glob.glob(os.path.join(runs, "round*", "*", "run*", "write.result.json"))):
    scen = f.split(os.sep)[-3]
    m = json.load(open(f))["metrics"]
    data.setdefault(scen, []).append(m)

def cell(scen, key, scale=1.0, fmt="{:,.0f}"):
    vals = [m[key] * scale for m in data.get(scen, []) if key in m]
    if not vals:
        return "-"
    med = statistics.median(vals)
    s = fmt.format(med)
    lo, hi = min(vals), max(vals)
    if med and (hi - lo) / abs(med) > 0.10:
        s += " (" + fmt.format(lo) + "–" + fmt.format(hi) + ")"
    return s

BT = [10, 25, 50, 100, 200]
n = max((len(v) for v in data.values()), default=0)
print("Medians of %d rounds (range when wider than 10 %%).\n" % n)

print("Durable commits: sync(ORDINARY) after each transaction, 1 KB values.\n")
print("| threads | buffer ms | commits/s | sync p50 ms | p99 ms | max ms | forces/s | KB per force | ms per force |")
print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for t in [1, 4, 16, 64]:
    for b in BT:
        s = "d-t%d-b%d" % (t, b)
        if s not in data:
            continue
        print("| %d | %d | %s | %s | %s | %s | %s | %s | %s |" % (
            t, b, cell(s, "commits_per_s"),
            cell(s, "commit.durable.p50_us", 1e-3, "{:.1f}"), cell(s, "commit.durable.p99_us", 1e-3, "{:.1f}"),
            cell(s, "commit.durable.max_us", 1e-3, "{:.1f}"), cell(s, "forces_per_s", 1, "{:.1f}"),
            cell(s, "bytes_per_force", 1e-3, "{:,.1f}"), cell(s, "force_ms_mean", 1, "{:.2f}")))
print()
print("Append-only writes: no sync, one thread; x100 is 100 puts per transaction.\n")
print("| value bytes | buffer ms | puts/s | user MB/s | commits/s | append p50 us | p99.9 us | max ms | forces/s | KB per force | ms per force | force busy |")
print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for v, name in [("100", "a-100"), ("1000", "a-1k"), ("1000 x100", "a-1k-x100")]:
    for b in BT:
        s = "%s-b%d" % (name, b)
        if s not in data:
            continue
        print("| %s | %d | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            v, b, cell(s, "puts_per_s"), cell(s, "user_mb_per_s", 1, "{:.1f}"), cell(s, "commits_per_s"), cell(s, "commit.append.p50_us", 1, "{:.1f}"),
            cell(s, "commit.append.p999_us", 1, "{:.1f}"), cell(s, "commit.append.max_us", 1e-3, "{:.2f}"),
            cell(s, "forces_per_s", 1, "{:.1f}"), cell(s, "bytes_per_force", 1e-3, "{:,.0f}"),
            cell(s, "force_ms_mean", 1, "{:.2f}"), cell(s, "force_busy_fraction", 100, "{:.0f} %")))
