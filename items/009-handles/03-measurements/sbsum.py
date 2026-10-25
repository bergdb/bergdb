import re, sys, os
# sbsum.py FILE...: ScaleBench outputs as table rows: the run, startup, uniform 1 thread (gets/s, timed max),
# threads N (gets/s; max), heap per key (M).
def fmt(n):
    return '{:,}'.format(int(n))
def ms(us):
    us = float(us)
    return ('%.2f ms' % (us / 1000)) if us < 10000 else ('%d ms' % round(us / 1000))
print('| run | startup | uniform, 1 thread | timed max | threads 1 | 2 | 4 | 8 | longest of the thread phases | heap a key |')
print('|---|---|---|---|---|---|---|---|---|---|')
for f in sys.argv[1:]:
    t = open(f).read()
    name = os.path.basename(f)[:-4]
    st = re.search(r'startup ([\d.]+) s', t)
    u = re.search(r'uniform, 1 thread: (\d+) gets a second', t)
    um = re.search(r'uniform, timed \d+ gets: .*?max ([\d.]+) us', t)
    th = dict((m.group(1), (m.group(2), m.group(3))) for m in re.finditer(r'threads (\d+): (\d+) gets a second; .*?max ([\d.]+) us', t))
    hp = re.search(r'heap after a full GC \d+ MB \(\d+ MB before the load\), ([\d.]+) bytes per key', t)
    longest = max([float(v[1]) for v in th.values()] or [0])
    cells = [name, (st.group(1) + ' s') if st else '', fmt(u.group(1)) if u else '', ms(um.group(1)) if um else '']
    for n in ['1', '2', '4', '8']:
        cells.append(fmt(th[n][0]) if n in th else '')
    cells.append(ms(longest) if th else '')
    cells.append((hp.group(1) + ' B') if hp else '')
    print('| ' + ' | '.join(cells) + ' |')
