#!/usr/bin/env python3
"""Bytes a put by level, update phase after its first 20%, across node sizes (bergdb 005-38).

Usage: python3 -I breakdown.py KEYS_M SD_MB  (e.g. 10 200). Levels: value leaves (s3h0;
WriteBench's vleaf), inner nodes of height 1, 2, 3 and more (any segment; in1, in2, in3+),
segment leaves above the last segment (s0h0 to s2h0; lleaf). Cells: writes a put x bytes a
written node = bytes a put."""
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import analyze  # noqa: E402

LEVELS = ['value leaves', 'height 1', 'height 2', 'height 3+', 'upper segment leaves']


def level_of_class(c):
    s, h = int(c[1]), int(c[3])
    if h == 0:
        return 'value leaves' if s == 3 else 'upper segment leaves'
    return 'height %d' % h if h < 3 else 'height 3+'


def level_of_kind(k):
    return {'vleaf': 'value leaves', 'lleaf': 'upper segment leaves', 'in1': 'height 1',
            'in2': 'height 2'}.get(k, 'height 3+')


def summarize(path):
    r = analyze.parse(path)
    t = analyze.tail(r['upd'], 0.8)
    if not t:
        return None
    acc = {l: [0.0, 0.0] for l in LEVELS}
    if t[0]['classes']:
        for c, v in analyze.classmean(t).items():
            if c == 'unk':
                continue
            a = acc[level_of_class(c)]
            a[0] += v[0]
            a[1] += v[0] * v[1]
    else:
        for k, v in analyze.kindmean(t).items():
            a = acc[level_of_kind(k)]
            a[0] += v[0]
            a[1] += v[0] * v[1]
    out = {'B': analyze.mean([w['B'] for w in t]), 'value': analyze.mean([w['value'] for w in t]),
           'dirty': analyze.mean([w['dirty'] for w in t]), 'top': analyze.mean([w['top'] for w in t]),
           'levels': acc, 'windows': len(t)}
    return out


def main():
    km, sdm = int(sys.argv[1]), int(sys.argv[2])
    cols = []
    for p in sorted(glob.glob(os.path.join(HERE, 'out', 'u-n*-sd%d-%dM.txt' % (sdm, km)))) + \
            sorted(glob.glob(os.path.join(HERE, 'out', 'm-*-sd%d-%dM.txt' % (sdm, km)))):
        name = os.path.basename(p)
        label = name.split('-')[1].replace('n', 'node ') if name.startswith('u-') else name.split('-')[1]
        cols.append((label, summarize(p)))
    wb = os.path.join(HERE, '..', 'wb', 'out', 'u-sd%d-%dM.txt' % (sdm, km))
    if os.path.exists(wb) and not any(c[0] == 'node 30' for c in cols):
        cols.append(('node 30', summarize(wb)))
    cols = [c for c in cols if c[1]]
    order = {'node 8': 0, 'node 14': 1, 'node 30': 2, 'node 62': 3}
    cols.sort(key=lambda c: order.get(c[0], 9))
    print('%dM keys, sd %d MB, updates (after the first 20%% of the phase): writes a put x bytes a node = bytes a put' % (km, sdm))
    print()
    print('| level | ' + ' | '.join(c[0] for c in cols) + ' |')
    print('|---|' + '---|' * len(cols))
    for l in LEVELS:
        cells = []
        for _, s in cols:
            w, b = s['levels'][l]
            cells.append('%.3f x %.0f = %.0f' % (w, b / w, b) if w > 0.0005 else '-')
        print('| %s | %s |' % (l, ' | '.join(cells)))
    print('| key nodes, all | ' + ' | '.join('%.2f writes, %.0f B' % (sum(v[0] for v in s['levels'].values()), sum(v[1] for v in s['levels'].values())) for _, s in cols) + ' |')
    print('| got-dirty list | ' + ' | '.join('%.0f' % s['dirty'] for _, s in cols) + ' |')
    print('| value nodes | ' + ' | '.join('%.0f' % s['value'] for _, s in cols) + ' |')
    print('| **B/put** | ' + ' | '.join('**%.0f**' % s['B'] for _, s in cols) + ' |')


if __name__ == '__main__':
    main()
