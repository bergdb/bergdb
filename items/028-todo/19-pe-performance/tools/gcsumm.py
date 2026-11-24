# bergdb 028-19: the G1 pauses of a Perf write run's measured phase (run.sh's LABEL.gc.log,
# -Xlog:gc with uptime; the phase's uptimes from LABEL/write.result.json), and whether each of
# the slowest commits (write.raw.json) falls in one. Usage: python3 gcsumm.py OUT LABEL...
import json, re, sys
out = sys.argv[1]
for lab in sys.argv[2:]:
    r = json.load(open(f"{out}/{lab}/write.result.json"))
    up0, up1 = r["uptimeMs"]
    pauses = []
    for line in open(f"{out}/{lab}.gc.log"):
        m = re.match(r"\[([0-9.]+)s\] GC\((\d+)\) (Pause \S+(?: \([^)]*\))*?) .*? (\d+)M->(\d+)M\((\d+)M\) ([0-9.]+)ms", line)
        if m:
            t = float(m.group(1)) * 1000
            if up0 <= t <= up1:
                pauses.append((t, m.group(3), int(m.group(4)), int(m.group(5)), float(m.group(7))))
    young = [p for p in pauses if p[1].startswith("Pause Young")]
    ms = sorted(p[4] for p in young)
    freed = [p[2] - p[3] for p in young]
    raw = json.load(open(f"{out}/{lab}/write.raw.json"))
    slow = raw["slowest"][:5]
    hit = sum(1 for s in slow if any(p[0] - 50 <= s["uptimeMs"] <= p[0] + p[4] + 50 for p in pauses))
    print(f"{lab}: {len(pauses)} pauses in the phase, {len(young)} young; young ms mean "
          f"{sum(ms) / len(ms):.0f}, median {ms[len(ms) // 2]:.0f}, max {ms[-1]:.0f}; freed a young "
          f"pause {sum(freed) / len(freed):.0f} MB; the 5 slowest commits ({', '.join('%.0f' % s['ms'] for s in slow)} ms):"
          f" {hit} in a pause")
