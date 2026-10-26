#!/usr/bin/env python3
"""Tables for the node-size report (bergdb 005-38): the key table, the mixed table, the load
table, D, the model fit. Usage: python3 -I assemble.py [key|mixed|load|d|model]"""
import glob
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import analyze  # noqa: E402

OUT = os.path.join(HERE, 'out')
WB = os.path.join(HERE, '..', 'wb', 'out')


def runinfo(p):
    r = analyze.parse(p)
    h = r.get('header', '')
    keys = int(re.search(r'(\d+) keys', h).group(1))
    sd = int(re.search(r'sd (\d+)', h).group(1)) // 1000000
    m = re.search(r'node (\d+)', h)
    node = m.group(1) if m else '30'
    name = os.path.basename(p)
    if name.startswith('m-'):
        node = name.split('-')[1]
    whole = None
    complete = False
    for line in open(p):
        mm = re.match(r'updates total: \d+ puts, \d+ bytes, ([\d.]+) B/put', line) or re.match(r'updates: \d+, stream \d+ bytes, ([\d.]+) B/update', line)
        if mm:
            whole = float(mm.group(1))
            complete = True
    if whole is None and r['upd']:
        whole = analyze.mean([w['B'] for w in r['upd']])
    t = analyze.tail(r['upd'], 0.8)
    after = analyze.mean([w['B'] for w in t]) if t else None
    load = None
    for line in open(p):
        if line.startswith('load:') or (line.startswith('total:') and load is None):
            load = float(re.search(r'([\d.]+) B/key', line).group(1))
    lt = analyze.tail(r['load'], 0.2)
    loadmarg = analyze.mean([w['B'] for w in lt]) if lt else None
    return dict(keys=keys, sd=sd, node=node, whole=whole, after=after, complete=complete, load=load,
                loadmarg=loadmarg, windows=len(r['upd']), path=p)


def allruns():
    rs = {}
    for p in glob.glob(os.path.join(OUT, 'u-n*.txt')) + glob.glob(os.path.join(OUT, 'm-*.txt')):
        x = runinfo(p)
        rs[(x['keys'], x['sd'], x['node'])] = x
    for p in glob.glob(os.path.join(WB, 'u-sd*.txt')):
        x = runinfo(p)
        if x['whole'] is not None:
            rs.setdefault((x['keys'], x['sd'], '30'), x)
    return rs


def cell(x, best=False):
    if x is None or x['whole'] is None:
        return '-'
    s = '%.0f' % x['whole']
    if not x['complete']:
        s += '*'
    if best:
        s = '**' + s + '**'
    return s


def key_table():
    rs = allruns()
    nodes = ['8', '14', '30', '62']
    combos = sorted({(k, sd) for (k, sd, n) in rs})
    print('| keys | sd MB | node 8 | node 14 | node 30 | node 62 | best against 30 |')
    print('|---|---|---|---|---|---|---|')
    for k, sd in combos:
        xs = {n: rs.get((k, sd, n)) for n in nodes}
        vals = {n: x['whole'] for n, x in xs.items() if x and x['whole'] is not None and x['complete']}
        if not vals:
            continue
        b = min(vals, key=vals.get)
        rel = ''
        if '30' in vals and b != '30':
            rel = 'node %s %+.0f%%' % (b, 100 * (vals[b] / vals['30'] - 1))
        elif '30' in vals:
            others = [v for n, v in vals.items() if n != '30']
            rel = 'node 30 (next %+.0f%%)' % (100 * (min(others) / vals['30'] - 1)) if others else ''
        print('| %dM | %d | %s | %s | %s | %s | %s |' % (k // 1000000, sd, *(cell(xs[n], n == b) for n in nodes), rel))


def mixed_table():
    rs = allruns()
    cols = ['14', '30', '62', 'L14I30', 'L14I62', 'L30I62']
    combos = sorted({(k, sd) for (k, sd, n) in rs if n.startswith('L')})
    print('| keys | sd MB | ' + ' | '.join(('node ' + c) if not c.startswith('L') else c for c in cols) + ' |')
    print('|---|---|' + '---|' * len(cols))
    for k, sd in combos:
        print('| %dM | %d | %s |' % (k // 1000000, sd, ' | '.join(cell(rs.get((k, sd, c))) for c in cols)))


def load_table():
    rs = allruns()
    nodes = ['8', '14', '30', '62']
    combos = sorted({(k, sd) for (k, sd, n) in rs})
    print('| keys | sd MB | ' + ' | '.join('node %s' % n for n in nodes) + ' |')
    print('|---|---|' + '---|' * len(nodes))
    for k, sd in combos:
        cells = []
        for n in nodes:
            x = rs.get((k, sd, n))
            cells.append('%.0f (%.0f)' % (x['load'], x['loadmarg']) if x and x['load'] else '-')
        print('| %dM | %d | %s |' % (k // 1000000, sd, ' | '.join(cells)))


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'key'
    {'key': key_table, 'mixed': mixed_table, 'load': load_table}[what]()
