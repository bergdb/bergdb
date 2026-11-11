import re, sys, os, glob
D = sys.argv[1]
def parse(f):
    r = {}
    if not os.path.exists(f): return r
    for l in open(f):
        m = re.search(r'\] (TWIN )?(FILL|DELETE|PHASE|OVER|NODES|FILL) (.*)', l)
        tw = 'TWIN ' in l
        if '] FILL tx=' in l or '] TWIN FILL tx=' in l:
            r[('twin' if tw else '') + 'fill'] = dict(re.findall(r'(\S+)=(\S+)', l))
        elif '] DELETE tx=' in l:
            r['delete'] = dict(re.findall(r'(\S+)=(\S+)', l))
        elif re.search(r'\] (TWIN )?NODES (\w+)', l):
            ph = re.search(r'NODES (\w+)', l).group(1)
            r[('twin' if tw else '') + 'nodes-' + ph] = dict(re.findall(r'(\S+)=(\S+)', l))
        elif re.search(r'\] (TWIN )?FILL (\w+) key nodes', l):
            ph = re.search(r'FILL (\w+) key nodes', l).group(1)
            m2 = re.search(r'key nodes (\d+), trees (\d+), live keys (\d+), leaf klongs (\d+), underfull (\d+)(.*)', l)
            r[('twin' if tw else '') + 'bu1-' + ph] = m2.groups()
        elif '] OVER' in l or '] PHASE' in l or 'tx=' in l and 'ops=' in l and 'FILL' not in l and 'DELETE' not in l:
            key = l.split(']')[1].split()[0]
            r['phase-' + key] = dict(re.findall(r'(\S+)=(\S+)', l))
    return r
rows = []
for f in sorted(glob.glob(D + '/n*-k*-br.txt')):
    nm = os.path.basename(f)[:-7]
    b = parse(f); m = parse(f[:-7] + '-main.txt')
    bu = b.get('bu1-shape'); tw = b.get('twinbu1-fill')
    if not bu or not tw: rows.append((nm, 'incomplete')); continue
    kn, kt = int(bu[0]), int(tw[0])
    S, n, e = int(bu[1]), int(bu[2]), int(bu[3])
    bound = S + e // 6
    mk = int(m.get('nodes-shape', {}).get('keyNodes', 0))
    dl = b.get('delete', {}); dm = m.get('delete', {})
    rows.append((nm, kn, kt, kn / kt, mk, mk / kt if kt else 0, bu[4], (bu[5].strip() or 'ok'), bound,
                 float(dl.get('merge/op', 0)), float(dl.get('rec/op', 0)), float(dm.get('rec/op', 1)),
                 float(dl.get('stream/op', 0)), float(dm.get('stream/op', 1))))
print("| Shape            | Keys nodes | Twin  | x    | main   | x     | BU1 | TU2 bound | merges/del | rec/del br/main |")
for r in rows:
    if r[1] == 'incomplete': print(r); continue
    print("| %-16s | %10d | %5d | %.2f | %6d | %5.2f | %s %s | %d | %.3f | %.1f/%.1f = %.2f (stream %.2f) |" % (
        r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11], r[10] / r[11], r[12] / r[13]))
for f in sorted(glob.glob(D + '/n*-over-br.txt')):
    b = open(f).read(); m = open(f[:-7] + '-main.txt').read()
    print(os.path.basename(f))
    for l1, l2 in zip([l for l in b.splitlines() if 'tx=' in l or 'NODES' in l or 'key nodes' in l],
                      [l for l in m.splitlines() if 'tx=' in l or 'NODES' in l or 'key nodes' in l]):
        print("  br  ", l1[:200]); print("  main", l2[:200])
