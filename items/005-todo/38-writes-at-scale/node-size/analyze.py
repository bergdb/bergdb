#!/usr/bin/env python3
"""Summaries of NodeSizeBench and WriteBench outputs (bergdb 005-38, node-size study).

Usage: python3 -I analyze.py FILE...   prints one block a file:
  - load: B/key after the load; marginal B/put = mean of the windows in the last 20% of
    the load (equal windows); per class (segment, height) writes a put and bytes a node in
    those windows (NodeSizeBench) or WriteBench's kinds;
  - updates: B/put over the whole phase and over its second half;
  - D, heap, tree, reach lines as printed.
"""
import re
import sys

WIN = re.compile(r'^(upd )?(\d+) keys: B/put (\d+) = value (\d+) \+ key nodes (\d+) \+ top (\d+) \+ dirty list (\d+) \+ rec other (\d+) \+ meta (\d+); nodes/put(.*?); still dirty')
KIND = re.compile(r' (\w+\+?) ([\d.]+) \((\d+) B, ([\d.]+) kl\)')
CLS = re.compile(r' (s\dh\d|unk) ([\d.]+)/put (\d+)B ([\d.]+)kl ([\d.]+)t ([\d.]+)live(?: ([\d.]+)still)?(?: ([\d.]+)old ([\d.]+)oldstill)?;')


def parse(path):
    r = {'path': path, 'load': [], 'upd': [], 'other': []}
    cur = None
    for line in open(path):
        line = line.rstrip('\n')
        m = WIN.match(line)
        if m:
            w = {'keys': int(m.group(2)), 'B': int(m.group(3)), 'value': int(m.group(4)),
                 'keynodes': int(m.group(5)), 'top': int(m.group(6)), 'dirty': int(m.group(7)),
                 'kinds': {k: (float(a), int(b), float(c)) for k, a, b, c in KIND.findall(m.group(10))},
                 'classes': {}}
            (r['upd'] if m.group(1) else r['load']).append(w)
            cur = w
            continue
        if line.startswith('  classes:') and cur is not None:
            cur['classes'] = {c: (float(a), int(b), float(k), float(t), float(l))
                              for c, a, b, k, t, l, st, o, os_ in CLS.findall(line)}
            cur['extra'] = {c: (float(st or 'nan'), float(o or 'nan'), float(os_ or 'nan'))
                            for c, a, b, k, t, l, st, o, os_ in CLS.findall(line)}
            continue
        if line.startswith(('WriteBench:', 'NodeSizeBench:')):
            r['header'] = line
        elif line.startswith('total:'):
            r['total'] = line
            m = re.search(r'([\d.]+) B/key', line)
            r['Bkey'] = float(m.group(1))
        elif line.startswith('updates total:'):
            r['updtotal'] = line
        elif line.startswith(('D:', '  D classes', 'heap:', 'tree', '  tree', 'reach:')):
            r['other'].append(line)
    return r


def mean(xs):
    return sum(xs) / len(xs) if xs else float('nan')


def tail(ws, frac):
    if not ws:
        return []
    k = ws[-1]['keys']
    return [w for w in ws if w['keys'] > (1 - frac) * k + 1e-9] or ws[-1:]


def classmean(ws):
    """Mean writes a put and bytes a node, by class, over windows (equal puts each)."""
    acc = {}
    for w in ws:
        for c, (wp, b, kl, t, lv) in w['classes'].items():
            a = acc.setdefault(c, [0.0, 0.0, 0.0, 0.0, 0.0])
            a[0] += wp
            a[1] += wp * b
            a[2] += wp * kl
            a[3] += wp * t
            a[4] += wp * lv
    n = len(ws)
    out = {}
    for c, a in sorted(acc.items()):
        if a[0] == 0:
            continue
        out[c] = (a[0] / n, a[1] / a[0], a[2] / a[0], a[3] / a[0], a[4] / a[0])
    return out


def extramean(ws):
    acc = {}
    for w in ws:
        for c, (wp, b, kl, t, lv) in w['classes'].items():
            st, o, os_ = w.get('extra', {}).get(c, (float('nan'),) * 3)
            a = acc.setdefault(c, [0.0, 0.0, 0.0, 0.0])
            a[0] += wp
            a[1] += wp * st
            a[2] += wp * o
            a[3] += wp * os_
    return {c: (a[1] / a[0], a[2] / a[0], a[3] / a[0]) for c, a in sorted(acc.items()) if a[0] > 0}


def kindmean(ws):
    acc = {}
    for w in ws:
        for k, (wp, b, kl) in w['kinds'].items():
            a = acc.setdefault(k, [0.0, 0.0, 0.0])
            a[0] += wp
            a[1] += wp * b
            a[2] += wp * kl
    n = len(ws)
    return {k: (a[0] / n, a[1] / a[0] if a[0] else 0, a[2] / a[0] if a[0] else 0) for k, a in acc.items()}


def block(r):
    print('==', r['path'])
    print('  ', r.get('header', ''))
    print('  ', r.get('total', ''))
    for name, ws, frac in (('load, last 20%', r['load'], 0.2), ('updates, after the first 20%', r['upd'], 0.8)):
        t = tail(ws, frac)
        if not t:
            continue
        print('   %s (%d windows): B/put %.0f = value %.0f + key nodes %.0f + top %.1f + dirty list %.0f'
              % (name, len(t), mean([w['B'] for w in t]), mean([w['value'] for w in t]),
                 mean([w['keynodes'] for w in t]), mean([w['top'] for w in t]), mean([w['dirty'] for w in t])))
        cm = classmean(t)
        if cm:
            print('     classes: ' + '; '.join('%s %.3f/put %.0fB %.1fkl %.1ft %.1flive' % ((c,) + v) for c, v in cm.items()
                                              if v[0] >= 0.0005))
            print('     node writes a put: %.2f' % sum(v[0] for v in cm.values()))
            em = extramean(t)
            if any(v[0] == v[0] for v in em.values()):
                print('     of the writes: ' + '; '.join('%s %.0f%% still dirty after%s' % (c, 100 * v[0], '' if v[1] != v[1] else ', %.0f%% old versions (%.0f%% old and still dirty)' % (100 * v[1], 100 * v[2]))
                                                    for c, v in em.items() if cm.get(c, (0,))[0] >= 0.0005))
        else:
            km = kindmean(t)
            print('     kinds: ' + '; '.join('%s %.3f/put %.0fB %.1fkl' % ((k,) + v) for k, v in km.items()))
            print('     node writes a put: %.2f' % sum(v[0] for v in km.values()))
    if 'updtotal' in r:
        print('  ', r['updtotal'])
    for line in r['other']:
        print('  ', line)


if __name__ == '__main__':
    for p in sys.argv[1:]:
        block(parse(p))
