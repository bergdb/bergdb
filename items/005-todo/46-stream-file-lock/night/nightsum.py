#!/usr/bin/env python3
# nightsum.py OUT: the summary of the night steps' outputs in OUT (bergdb 005-46, 006-09's W1.3
# and W1.4: soak.sh, props.sh, scalebench-c.sh): the soak's report, Props in turns, and
# ScaleBench from the OS's cache in turns, with HEAD's gets a second against bf19075's.
# Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
import glob, os, re, sys

out = sys.argv[1]


def fmt(n):
    return '{:,}'.format(int(round(n)))


print('# 1. The soak (W1.3)\n')
for f in sorted(glob.glob(os.path.join(out, 'soak', '*-report.txt'))):
    print(open(f).read())

print('# 2. Props, in turns (W1.4; CORE and SS: lower is faster)\n')
props = {}
for f in sorted(glob.glob(os.path.join(out, 'props', 'props-*.txt'))):
    m = re.match(r'props-(.+)-(\d+)\.txt', os.path.basename(f))
    t = open(f).read()
    vals = dict((k, float(v)) for k, v in re.findall(r'^(MEM|CORE|SS):([\d.]+)', t, re.M))
    props.setdefault(m.group(1), []).append((int(m.group(2)), vals))
for jar in sorted(props):
    rs = sorted(props[jar])
    print('%-8s ' % jar + '; '.join('round %d: MEM %s, CORE %s, SS %s' % (
        r, v.get('MEM', '?'), v.get('CORE', '?'), v.get('SS', '?')) for r, v in rs))
    cores = [v['CORE'] for r, v in rs if 'CORE' in v]
    if cores:
        print('%-8s CORE mean %.3f, from %.2f to %.2f' % ('', sum(cores) / len(cores), min(cores), max(cores)))
print()

print('# 3. ScaleBench from the OS\'s cache, in turns (W1.4; gets a second)\n')
cols = ['startup', 'uniform 1', 'hot 1', 'threads 1', '2', '4', '8', 'sampled 4', 'blocked reading',
        'uniform timed max', 'longest of the thread phases']
runs = {}
for f in sorted(glob.glob(os.path.join(out, 'scalebench-c', 'f53-c-*.txt'))):
    name = os.path.basename(f)[:-4]
    m = re.match(r'f53-c-[0-9a-z]+-(b\d+-[0-9a-z]+)-(head|bf19075)-(\d+)$', name)
    if not m:
        continue
    t = open(f).read()
    ok = 'SCALEBENCH OK' in t
    v = {}
    x = re.search(r'startup ([\d.]+) s', t)
    if x: v['startup'] = float(x.group(1))
    x = re.search(r'uniform, 1 thread: (\d+) gets a second', t)
    if x: v['uniform 1'] = float(x.group(1))
    x = re.search(r'hot, 1 thread: (\d+) gets a second', t)
    if x: v['hot 1'] = float(x.group(1))
    x = re.search(r'uniform, timed \d+ gets: .*?max ([\d.]+) us', t)
    if x: v['uniform timed max'] = float(x.group(1)) / 1000
    th = re.findall(r'threads (\d+): (\d+) gets a second; .*?max ([\d.]+) us', t)
    for n, g, mxus in th:
        v['threads 1' if n == '1' else n] = float(g)
    if th:
        v['longest of the thread phases'] = max(float(mxus) for n, g, mxus in th) / 1000
    x = re.search(r'sampled (\d+) threads: (\d+) gets a second', t)
    if x: v['sampled 4'] = float(x.group(2))
    # the sampled threads' share BLOCKED reading the stream (on a file's or the stream's monitor)
    v['blocked reading'] = sum(float(b) for b in re.findall(r'([\d.]+)% BLOCKED reading the stream', t))
    runs.setdefault(m.group(1), []).append((m.group(2), int(m.group(3)), ok, v))


def cell(c, val):
    if val is None:
        return ''
    if c == 'startup':
        return '%.2f s' % val
    if c in ('uniform timed max', 'longest of the thread phases'):
        return '%.2f ms' % val
    if c == 'blocked reading':
        return '%.1f%%' % val
    return fmt(val)


for cfg in sorted(runs):
    print('## %s\n' % cfg)
    print('| run | ' + ' | '.join(cols) + ' |')
    print('|---|' + '---|' * len(cols))
    for jar, rnd, ok, v in sorted(runs[cfg], key=lambda x: (x[1], x[0])):
        print('| %s, round %d%s | ' % (jar, rnd, '' if ok else ', FAILED') +
              ' | '.join(cell(c, v.get(c)) for c in cols) + ' |')
    means = {}
    for jar in ('bf19075', 'head'):
        vs = [v for j, r, ok, v in runs[cfg] if j == jar and ok]
        means[jar] = dict((c, sum(x[c] for x in vs) / len(vs)) for c in cols
                          if vs and all(c in x for x in vs))
        if vs:
            print('| %s, mean of %d | ' % (jar, len(vs)) +
                  ' | '.join(cell(c, means[jar].get(c)) for c in cols) + ' |')
    a, b = means.get('bf19075', {}), means.get('head', {})
    rel = []
    for c in cols:
        if c in a and c in b and a[c] > 0 and c not in ('startup', 'blocked reading',
                                                         'uniform timed max', 'longest of the thread phases'):
            rel.append('%s %+.1f%%' % (c, 100.0 * (b[c] - a[c]) / a[c]))
    if rel:
        print('\nHEAD against bf19075, gets a second: ' + ', '.join(rel))
    print()

print('# 4. performance.sh ab, quick suite, 2026.1 against HEAD (009-01, done item 7)\n')
for n in ('1', '2'):
    f = os.path.join(out, 'perf-ab', 'ab-%s.txt' % n)
    if not os.path.exists(f):
        continue
    t = open(f).read()
    i = t.find('COMPARE ')
    print('## ab run %s\n' % n)
    print(t[i:] if i >= 0 else t[-2000:])
f = os.path.join(out, 'perf-ab', 'confirm.txt')
if os.path.exists(f):
    print('## the first reference against both candidate sessions\n')
    for line in open(f):
        if re.search(r'CONFIRMED|NOT REPEATED|ALERT|NO ALERTS', line):
            print(line.rstrip())
