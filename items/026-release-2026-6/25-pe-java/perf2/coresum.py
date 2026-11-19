# bergdb 026-25, perf2: summary of core-f53.sh's runs: each test's figure of Props CORE (the
# best of five, against cissi 2013; smaller is faster) per run, the median and range for main
# and pe, and pe/main. Written 2026-11-19. Usage: python3 -I coresum.py OUT
import glob, os, re, statistics, sys
out = sys.argv[1]
names = ["CORE", "get", "get4t", "getmany", "set"]
runs = {"main": [], "pe": []}
for p in sorted(glob.glob(os.path.join(out, "core-*-r*.txt"))):
    m = re.search(r"core-(main|pe)-(r\d+\w)", p)
    c = re.search(r"CORE:([0-9.]+) \(([0-9.]+), ([0-9.]+), ([0-9.]+), ([0-9.]+)\)", open(p).read())
    if m and c:
        v = [float(x) for x in c.groups()]
        runs[m.group(1)].append((m.group(2), v))
        print(f"{m.group(2)} {m.group(1):4} " + " ".join(f"{n} {x:.2f}" for n, x in zip(names, v)))
print(f"{len(runs['main'])} runs of main, {len(runs['pe'])} of pe: median (range), pe/main")
for i, n in enumerate(names):
    a = [v[i] for _, v in runs["main"]]
    b = [v[i] for _, v in runs["pe"]]
    ma, mb = statistics.median(a), statistics.median(b)
    print(f"- {n}: main {ma:.3f} ({min(a):.2f}-{max(a):.2f}), pe {mb:.3f} ({min(b):.2f}-{max(b):.2f}), pe/main {mb / ma:.3f}")
