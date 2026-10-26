#!/usr/bin/env python3
"""D (the dirty nodes TransSeq holds) over the update phase: mean and max of its nodes and
stored MB, and of the startup lag, from the per-window lines (bergdb 005-38)."""
import glob, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
W = re.compile(r'^upd (\d+) keys: B/put (\d+).*startup lag (\d+) MB; D (\d+) nodes, (\d+) MB')
def one(p):
    rows = [W.match(l) for l in open(p)]
    rows = [m for m in rows if m]
    if not rows: return None
    h = open(p).readline()
    keys = int(re.search(r'(\d+) keys', h).group(1)); sd = int(re.search(r'sd (\d+)', h).group(1)) // 1000000
    m = re.search(r'node (\d+)', h); node = m.group(1) if m else '30'
    name = os.path.basename(p)
    if name.startswith('m-'): node = name.split('-')[1]
    rows = rows[len(rows) // 5:]
    lag = [int(m.group(3)) for m in rows]; dn = [int(m.group(4)) for m in rows]; dmb = [int(m.group(5)) for m in rows]
    mem = None
    for l in open(p):
        mm = re.match(r'D: .*?(\d+) stream bytes .*memory estimate (\d+) bytes', l)
        if mm: mem = int(mm.group(2)) / max(1, int(mm.group(1)))
    return keys, sd, node, sum(dn) / len(dn), max(dn), sum(dmb) / len(dmb), max(dmb), sum(lag) / len(lag), max(lag), mem
rows = []
for p in sorted(glob.glob(os.path.join(HERE, 'out', 'u-n*.txt'))) + sorted(glob.glob(os.path.join(HERE, 'out', 'm-*.txt'))) + sorted(glob.glob(os.path.join(HERE, '..', 'wb', 'out', 'u-sd*.txt'))):
    r = one(p)
    if r: rows.append(r)
rows.sort(key=lambda r: (r[0], r[1], str(r[2])))
print('| keys | sd MB | node | D nodes, mean (max) | D stored MB, mean (max) | startup lag MB, mean (max) | memory/stored |')
print('|---|---|---|---|---|---|---|')
for k, sd, n, dn, dnx, dm, dmx, lg, lgx, mem in rows:
    print('| %dM | %d | %s | %.0fk (%.0fk) | %.0f (%.0f) | %.0f (%.0f) | %s |' % (k // 1000000, sd, n, dn / 1000, dnx / 1000, dm, dmx, lg, lgx, '%.1f' % mem if mem else '-'))
