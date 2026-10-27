"""bergdb 005-48: the tables of the timed runs, HEAD against the prototype, from a results
directory of night/run-f53.sh or night/run-s1.sh: OUT/ref/<scenario>/run*/write.result.json
(HEAD) and OUT/cand/... (the prototype). Each cell is the median over the runs, with the range
when it is wider than 10 percent. After 005-13's tools/table.py. Written 2026-10-27 by Claude
(Opus 5.5, Claude Code).
Usage: python3 -I tools/table.py OUT > OUT/table.md
"""
import glob, json, os, statistics, sys

out = sys.argv[1]
data = {}
for tag in ("ref", "cand"):
    for f in sorted(glob.glob(os.path.join(out, tag, "*", "run*", "write.result.json"))):
        scen = f.split(os.sep)[-3]
        data.setdefault((tag, scen), []).append(json.load(open(f))["metrics"])


def cell(tag, scen, key, scale=1.0, fmt="{:,.0f}"):
    vals = [m[key] * scale for m in data.get((tag, scen), []) if key in m]
    if not vals:
        return "-"
    med = statistics.median(vals)
    s = fmt.format(med)
    lo, hi = min(vals), max(vals)
    if med and (hi - lo) / abs(med) > 0.10:
        s += " (" + fmt.format(lo) + "–" + fmt.format(hi) + ")"
    return s


scens = sorted({s for (_, s) in data}, key=lambda s: (s[0] != "d", s))
runs = {tag: max([len(v) for (t, _), v in data.items() if t == tag] or [0]) for tag in ("ref", "cand")}
print("Medians of %d runs of HEAD and %d of the prototype (range when wider than 10 %%).\n"
      % (runs["ref"], runs["cand"]))
NAMES = {"ref": "HEAD", "cand": "prototype"}

print("Durable commits: sync(ORDINARY) after each transaction, 1 KB values (question 1).\n")
print("| scenario | build | commits/s | sync p50 ms | p99 ms | max ms | forces/s | KB per force | ms per force |")
print("|---|---|---:|---:|---:|---:|---:|---:|---:|")
for s in scens:
    if not s.startswith("d-"):
        continue
    for tag in ("ref", "cand"):
        print("| %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            s, NAMES[tag], cell(tag, s, "commits_per_s"),
            cell(tag, s, "commit.durable.p50_us", 1e-3, "{:.1f}"),
            cell(tag, s, "commit.durable.p99_us", 1e-3, "{:.1f}"),
            cell(tag, s, "commit.durable.max_us", 1e-3, "{:.1f}"),
            cell(tag, s, "forces_per_s", 1, "{:.1f}"), cell(tag, s, "bytes_per_force", 1e-3, "{:,.1f}"),
            cell(tag, s, "force_ms_mean", 1, "{:.2f}")))
print()
print("Writers that do not sync: one thread; x100 is 100 puts per transaction (question 2).\n")
print("| scenario | build | puts/s | user MB/s | append p50 us | p99.9 us | max ms | forces/s | KB per force | ms per force | force busy |")
print("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for s in scens:
    if s.startswith("d-"):
        continue
    for tag in ("ref", "cand"):
        print("| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            s, NAMES[tag], cell(tag, s, "puts_per_s"), cell(tag, s, "user_mb_per_s", 1, "{:.1f}"),
            cell(tag, s, "commit.append.p50_us", 1, "{:.1f}"),
            cell(tag, s, "commit.append.p999_us", 1, "{:.1f}"),
            cell(tag, s, "commit.append.max_us", 1e-3, "{:.2f}"),
            cell(tag, s, "forces_per_s", 1, "{:.1f}"), cell(tag, s, "bytes_per_force", 1e-3, "{:,.0f}"),
            cell(tag, s, "force_ms_mean", 1, "{:.2f}"), cell(tag, s, "force_busy_fraction", 100, "{:.0f} %")))
