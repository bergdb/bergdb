# bergdb 028-19 (ccsumm2.py: ccsumm.py with FIELD): CCBench's runs (run2.sh's OUT/cc-BUILD-rN?.txt), 026-25 perf2's summarize.py
# for any builds: per kind and transaction size the median over the runs of the time an operation,
# each build against the first. Usage: python3 ccsumm.py OUT BUILD...
import glob, os, re, statistics, sys

out, builds = sys.argv[1], sys.argv[2:]
FIELD = os.environ.get('FIELD', 'op_mean_us')   # tx_med_us: the median transaction, not moved by a GC pause


def cc(build):
    runs, loads, streams = [], [], []
    for p in sorted(glob.glob(os.path.join(out, "cc-%s-r*.txt" % build))):
        rows = {}
        for line in open(p):
            if line.startswith("RESULT "):
                f = dict(kv.split("=", 1) for kv in line.split()[1:])
                rows[(f["kind"], int(f["tsize"]))] = float(f[FIELD])
            elif line.startswith("LOAD "):
                loads.append(float(re.search(r"([0-9.]+) puts/s", line).group(1)))
            elif line.startswith("STREAM "):
                streams.append(int(line.split()[1]))
        if rows:
            runs.append(rows)
    return runs, loads, streams


data = {b: cc(b) for b in builds}
base = builds[0]
print(FIELD + ", the median of %s runs; each build / %s" %
      ("/".join(str(len(data[b][0])) for b in builds), base))
ratios = {b: [] for b in builds[1:]}
for key in data[base][0][0]:
    med = {b: statistics.median([r[key] for r in data[b][0] if key in r]) for b in builds}
    parts = []
    for b in builds:
        s = f"{b} {med[b]:.2f}"
        if b != base:
            ratios[b].append(med[b] / med[base])
            s += f" ({med[b] / med[base]:.3f})"
        parts.append(s)
    print(f"- {key[0]} {key[1]}: " + ", ".join(parts))
for b in builds[1:]:
    print(f"- {b}/{base}, geometric mean of {len(ratios[b])} cases: {statistics.geometric_mean(ratios[b]):.3f}")
for b in builds:
    l = data[b][1]
    print(f"- load puts/s {b}: {statistics.median(l):.0f} ({min(l):.0f}-{max(l):.0f})"
          + (f", / {base} {statistics.median(l) / statistics.median(data[base][1]):.3f}" if b != base else "")
          + f"; stream MB {statistics.median(data[b][2])}")
