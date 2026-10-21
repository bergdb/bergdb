"""005-13 follow-up: the table of idle-run.sh's results. Per configuration, the median over
the rounds of: interrupt wakeups a second, CPU ms a second (and the part on P-cores), the
energy the kernel attributes to the process (ri_energy_nj) as an average power in uW, and
the consumer thread's CPU (IdleProbe's THREAD lines). Then the reference processes.
Usage: python3 -I idle-table.py RUNSDIR
"""
import glob, os, re, statistics, sys

d = sys.argv[1]

def parse(path):
    rows = {}
    for line in open(path):
        kv = dict(x.split("=", 1) for x in line.split() if "=" in x)
        if "cpu_ns" in kv:
            rows[int(kv["pid"])] = {k: int(v) for k, v in kv.items() if v.isdigit()}
    return rows

conf = {}
refs = {}
for t0 in sorted(glob.glob(os.path.join(d, "*.t0"))):
    name = os.path.basename(t0)[:-3]
    base = re.sub(r"-r\d+$", "", name)
    a, b = parse(t0), parse(t0[:-3] + ".t1")
    sec = int(open(t0[:-3] + ".time1").read()) - int(open(t0[:-3] + ".time0").read())
    log = open(os.path.join(d, name + ".log")).read()
    pid = int(re.search(r"READY pid=(\d+)", log).group(1))
    m = re.search(r"T1 elapsed_s=([\d.]+)", log)
    el = float(m.group(1)) if m else float("nan")
    cons = sum(float(x) for x in re.findall(r"THREAD ([\d.]+) ms BufferedStream-consumer", log))
    for p in a:
        if p not in b:
            continue
        x = {k: b[p][k] - a[p][k] for k in a[p] if k in b[p]}
        r = {
            "wk": x["interrupt_wkups"] / sec,
            "pkg": x["pkg_idle_wkups"] / sec,
            "cpu": x["cpu_ns"] / 1e6 / sec,
            "pcpu": x["pcpu_ns"] / 1e6 / sec,
            "uw": x["energy_nj"] / 1e3 / sec,
            "instr": x["instructions"] / sec,
        }
        if p == pid:
            r["cons"] = cons / el
            conf.setdefault(base, []).append(r)
        else:
            refs.setdefault(p, []).append(r)

def med(rs, k, f):
    v = [r[k] for r in rs if k in r]
    if not v:
        return "-"
    m = statistics.median(v)
    s = f.format(m)
    if len(v) > 1 and m and (max(v) - min(v)) / abs(m) > 0.15:
        s += " (" + f.format(min(v)) + "–" + f.format(max(v)) + ")"
    return s

order = ["cur-jvm-0", "cur-db-100", "cur-db-50", "cur-db-20", "proto-db-20", "fix-db-20", "fix-db-100"]
label = {"cur-jvm-0": "JVM only, no database", "cur-db-100": "database, 100 ms, before the fix",
         "cur-db-50": "database, 50 ms, before the fix", "cur-db-20": "database, 20 ms, before the fix",
         "proto-db-20": "database, 20 ms, consumer sleeps when idle (prototype)",
         "fix-db-20": "database, 20 ms, with the fix", "fix-db-100": "database, 100 ms, with the fix"}
n = max(len(v) for v in conf.values())
print("Medians of %d rounds of 60 s (range when wider than 15 %%).\n" % n)
print("| process | wakeups/s | CPU ms/s | on P-cores ms/s | consumer thread CPU ms/s | energy, uW | instructions/s |")
print("|---|---:|---:|---:|---:|---:|---:|")
for c in order:
    if c not in conf:
        continue
    rs = conf[c]
    print("| %s | %s | %s | %s | %s | %s | %s |" % (label[c], med(rs, "wk", "{:.0f}"), med(rs, "cpu", "{:.2f}"),
          med(rs, "pcpu", "{:.2f}"), med(rs, "cons", "{:.2f}"), med(rs, "uw", "{:.0f}"), med(rs, "instr", "{:,.0f}")))
print()
print("Reference processes in the same windows (all %d windows):\n" % sum(len(v) for v in conf.values()))
# The pids of 2026-10-21 on F53.
names = {471: "Dock", 482: "Finder", 2827: "VS Code, main process", 10131: "VS Code's Java language server (a JVM)"}
print("| process | wakeups/s | CPU ms/s | energy, uW |")
print("|---|---:|---:|---:|")
for p, rs in sorted(refs.items()):
    print("| %s | %s | %s | %s |" % (names.get(p, "pid %d" % p), med(rs, "wk", "{:.0f}"), med(rs, "cpu", "{:.2f}"), med(rs, "uw", "{:.0f}")))
