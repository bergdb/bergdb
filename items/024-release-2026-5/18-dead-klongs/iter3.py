#!/usr/bin/env python3
# 024-18: option 3a's price at each iteration's end: nodes with a dead klong, the closure with
# ancestors (set3), its bytes as last versions, those not changed since the census before, and
# the iteration's stream bytes. iter3.py FILE...
import re, sys
def kv(s):
    return {m.group(1): m.group(2) for m in re.finditer(r'(\w[\w/]*)=(\[[^\]]*\]|[-\d.]+)', s)}
for f in sys.argv[1:]:
    print("#", f.split('/')[-1])
    print("  %-6s %8s %8s %8s %8s %8s %8s %9s %6s" % ("iter", "nodes", "withD", "set3", "s3cold", "s3MB", "iterMB", "iterTx", "s3/it"))
    it = {}
    cur = {}
    for l in open(f):
        m = re.search(r'\] ITER (\d+) stream=(\d+) rec=(\d+) tx=(\d+)', l)
        if m: it[m.group(1)] = (int(m.group(2)), int(m.group(4)))
        m = re.search(r'\] (CLEAF|CINNER) iter(\d+) (leaf|inner) (.*)', l)
        if m:
            cur.setdefault(m.group(2), {})[m.group(3)] = kv(m.group(4))
    for k in sorted(cur, key=int):
        d = cur[k]
        t = lambda x: sum(int(d[c][x]) for c in d)
        s3b = t('set3Bytes')
        st, tx = it.get(k, (0, 0))
        print("  %-6s %8d %8d %8d %8d %8.1f %8.1f %9d %5.1f%%" % (k, t('nodes'), t('withDead'), t('set3'), t('set3Cold'),
              s3b / 1e6, st / 1e6, tx, 100.0 * s3b / st if st else 0))
