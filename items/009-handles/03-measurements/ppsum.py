import re, sys, os
# ppsum.py FILE...: one row per PauseProbe phase: name, phase, gets n/p99.9/max, commits n/p99.9/max, resident or pinned
def num(s): return s.replace(',', '')
rows = []
for f in sys.argv[1:]:
    name = os.path.basename(f)[:-4]
    phase = None
    cur = None
    for line in open(f):
        m = re.match(r'(load:|phase) (.*?);', line)
        if m:
            if cur: rows.append(cur)
            phase = 'load' if m.group(1) == 'load:' else m.group(2).replace(', 2 readers, 60 s', '')
            cur = {'name': name, 'phase': phase}
            continue
        m = re.match(r'\s+(gets|commits)\s+(\d+), median ([\d.]+) ms, p99 ([\d.]+), p99.9 ([\d.]+), p99.99 ([\d.]+), max ([\d.]+) ms', line)
        if m and cur is not None:
            cur[m.group(1)] = (int(m.group(2)), float(m.group(5)), float(m.group(7)))
            continue
        if cur is None: continue
        m = re.search(r'resident (\d+) MB', line)
        if m: cur['res'] = m.group(1) + ' MB'
        m = re.search(r'last sweep \d+ -> (\d+) bytes', line)
        if m: cur['res'] = '%d MB' % (int(m.group(1)) / 1e6)
        m = re.search(r'(\d+) ms at most', line)
        if m: cur['evmax'] = m.group(1)
        m = re.search(r'([\d.]+) ms at most$', line.strip())
        if m: cur['evmax'] = m.group(1)
    if cur: rows.append(cur)
print('| run | phase | gets | p99.9 | max | commits | p99.9 | max | resident | longest batch |')
print('|---|---|---|---|---|---|---|---|---|---|')
for r in rows:
    g = r.get('gets', ('', '', '')); c = r.get('commits', ('', '', ''))
    print('| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (r['name'], r['phase'], g[0], g[1], g[2], c[0], c[1], c[2], r.get('res', ''), r.get('evmax', '')))
