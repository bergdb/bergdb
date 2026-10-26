#!/usr/bin/env python3
"""Markdown tables for the node-size report (bergdb 005-38). Usage: python3 -I tables.py
Reads out/ (NodeSizeBench) and ../wb/out/ (the coordinator's WriteBench, node 30)."""
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import analyze  # noqa: E402

OUT = os.path.join(HERE, 'out')
WB = os.path.join(HERE, '..', 'wb', 'out')


def runs():
    rs = []
    for p in sorted(glob.glob(os.path.join(OUT, 'u-n*.txt'))) + sorted(glob.glob(os.path.join(OUT, 'm-*.txt'))):
        rs.append(analyze.parse(p))
    for p in sorted(glob.glob(os.path.join(WB, 'u-sd*.txt'))):
        rs.append(analyze.parse(p))
    return rs


def info(r):
    h = r.get('header', '')
    keys = int(re.search(r'(\d+) keys', h).group(1))
    sd = int(re.search(r'sd (\d+)', h).group(1))
    m = re.search(r'node (\d+)', h)
    node = int(m.group(1)) if m else 30
    name = os.path.basename(r['path'])
    if name.startswith('m-'):
        node = name.split('-')[1]
    upd = r['upd']
    upd_b = None
    if 'updtotal' in r:
        upd_b = float(re.search(r'([\d.]+) B/put', r['updtotal']).group(1))
    elif upd:
        upd_b = analyze.mean([w['B'] for w in upd])
    else:
        for line in open(r['path']):
            if line.startswith('updates:'):
                upd_b = float(re.search(r'([\d.]+) B/update', line).group(1))
    t = analyze.tail(upd, 0.8)
    cm = analyze.classmean(t) if t and t[0]['classes'] else None
    km = analyze.kindmean(t) if t else None
    load_end = None
    for line in open(r['path']):
        if line.startswith('load:') or (line.startswith('total:') and load_end is None):
            load_end = float(re.search(r'([\d.]+) B/key', line).group(1))
    return dict(keys=keys, sd=sd, node=node, upd_b=upd_b, cm=cm, km=km, load=load_end, r=r,
                complete=('updtotal' in r) or any(l.startswith('updates:') for l in open(r['path'])),
                windows=len(upd))


def fmt_keys(k):
    return '%dM' % (k // 1000000)


def main():
    rows = [info(r) for r in runs()]
    rows.sort(key=lambda x: (x['keys'], x['sd'], str(x['node'])))
    print('| keys | sd MB | node | B/put, updates | B/key after the load | node writes a put | update windows |')
    print('|---|---|---|---|---|---|---|')
    for x in rows:
        nw = sum(v[0] for v in x['cm'].values()) if x['cm'] else (sum(v[0] for v in x['km'].values()) if x['km'] else float('nan'))
        print('| %s | %d | %s | %s | %s | %.2f | %d%s |' % (fmt_keys(x['keys']), x['sd'] // 1000000, x['node'],
              '%.0f' % x['upd_b'] if x['upd_b'] else '-', '%.0f' % x['load'] if x['load'] else '-', nw, x['windows'],
              '' if x['complete'] else ' (incomplete)'))
    print()
    print('Per class, updates after the first 20% of the phase: writes a put x bytes a written node')
    for x in rows:
        if x['cm']:
            parts = ['%s %.3f x %.0f' % (c, v[0], v[1]) for c, v in x['cm'].items() if v[0] >= 0.001]
        elif x['km']:
            parts = ['%s %.3f x %.0f' % (k, v[0], v[1]) for k, v in x['km'].items() if v[0] >= 0.001]
        else:
            parts = []
        print('- %s, sd %d, node %s: %s' % (fmt_keys(x['keys']), x['sd'] // 1000000, x['node'], '; '.join(parts)))


if __name__ == '__main__':
    main()
