"""bergdb 026-22: sums of mtcheck's RESULT lines, by set and in all.
Usage: python3 agg.py RUNSDIR MODE SET..."""
import sys, os, re, collections
runs, mode, sets = sys.argv[1], sys.argv[2], sys.argv[3:]
NUM = ['txs', 'ops', 'dels', 'steps', 'csteps', 'c1loose', 'c1leaf', 'c1user', 'c1fix', 'midsteps', 'midscans', 'midscanshort',
       'fixsteps', 'fixcalls', 'groupsfixed', 'gets', 'jreads', 'scans', 'taken']
MAPS = ['fails', 'wouldbump', 'shapeend', 'shapemid']
def parse(line):
    d = {}
    for tok in line.split()[1:]:
        if '=' in tok:
            k, v = tok.split('=', 1); d[k] = v
    return d
def mp(s):
    m = {}
    for part in filter(None, s.split(',')):
        k, v = part.rsplit(':', 1); m[k] = int(v)
    return m
total = collections.Counter(); tmaps = {k: collections.Counter() for k in MAPS}
tr_all = 0; tr_fail = collections.Counter(); notdone = []
for st in sets:
    c = collections.Counter(); ms = {k: collections.Counter() for k in MAPS}; n = 0; nf = collections.Counter()
    d = os.path.join(runs, st, mode)
    for f in sorted(os.listdir(d)):
        text = open(os.path.join(d, f)).read()
        if not re.search(r'^STEPTIMES', text, re.M):
            notdone.append(f'{st}/{f}'); continue
        for line in text.splitlines():
            if line.startswith('RESULT'):
                r = parse(line); n += 1
                for k in NUM: c[k] += int(r.get(k, 0))
                for k in MAPS: ms[k].update(mp(r.get(k, '')))
                for k in mp(r.get('fails', '')): nf[k] += 1
    print(f'{st}: traces={n} ' + ' '.join(f'{k}={c[k]}' for k in NUM))
    for k in MAPS: print(f'  {k}: ' + ','.join(f'{a}:{b}' for a, b in sorted(ms[k].items())))
    print('  traces with a failure, by check: ' + ','.join(f'{a}:{b}' for a, b in sorted(nf.items())))
    total.update(c); tr_all += n; tr_fail.update(nf)
    for k in MAPS: tmaps[k].update(ms[k])
print(f'ALL: traces={tr_all} ' + ' '.join(f'{k}={total[k]}' for k in NUM))
for k in MAPS: print(f'  {k}: ' + ','.join(f'{a}:{b}' for a, b in sorted(tmaps[k].items())))
print('  traces with a failure, by check: ' + ','.join(f'{a}:{b}' for a, b in sorted(tr_fail.items())))
if notdone: print('NOT DONE: ' + ' '.join(notdone))
