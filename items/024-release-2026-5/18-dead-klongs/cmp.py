#!/usr/bin/env python3
# 024-18: one line a run: the end census (leaves + inner) and the stream bytes an operation over the
# phase after the shape (from the census before the phase to the last one). cmp.py FILE...
import re, sys
def kv(s):
    return {m.group(1): m.group(2) for m in re.finditer(r'(\w[\w/]*)=(\[[^\]]*\]|[-\d.]+)', s)}
print("%-22s %7s %8s %5s %5s %6s %7s %7s %6s %7s %7s %8s %6s" % ("run", "nodes", "dead", "d/l", "deld", "T/nd", "stMB", "liveMB", "ratio", "withD", "set3", "B/op", "cmp/op"))
for f in sys.argv[1:]:
    L = open(f).read().splitlines()
    cens = []  # (label, len, tx)
    last = {}
    for l in L:
        m = re.search(r'\] CENSUS (\S+) .* len=(\d+) .* tx=(\d+)', l)
        if m: cens.append((m.group(1), int(m.group(2)), int(m.group(3))))
        m = re.search(r'\] (CLEAF|CINNER) (\S+) (leaf|inner) (.*)', l)
        if m: last.setdefault(m.group(2), {})[m.group(3)] = kv(m.group(4))
    comp = [kv(l)['compact/op'] for l in L if ' PHASE RUN' in l]
    if not cens: continue
    start = [c for c in cens if c[0] in ('deleted', 'fill')][-1]
    end = cens[-1]
    d = last[end[0]]
    tot = lambda k: sum(int(d[c][k]) for c in d)
    nodes, dead, live, T = tot('nodes'), tot('dead'), tot('live'), tot('time')
    deld = tot('deleted')
    st, lb = tot('bytes') / 1e6, tot('liveBytes') / 1e6
    bop = (end[1] - start[1]) / max(1, (end[2] - start[2]) * 100.0)
    name = f.split('/')[-1][:-4] + "@" + end[0]
    print("%-22s %7d %8d %5.2f %5d %6.2f %7.1f %7.1f %6.2f %7s %7s %8.1f %6s" % (name, nodes, dead, dead / live, deld, T / nodes, st, lb, st / lb,
          tot('withDead'), tot('set3'), bop, comp[-1] if comp else '-'))
