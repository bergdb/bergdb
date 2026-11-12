#!/usr/bin/env python3
"""bergdb 024-20: the tables of the item from CN's outputs. summary.py OUTDIR...

Prints, per run, bytes an operation by part, and what each candidate saves an operation."""
import sys, glob, os, re

def parse(path):
    r = {'cat': {}, 'cand': {}, 'name': os.path.basename(path)[:-4]}
    for line in open(path):
        if line.startswith('CAT '):
            name, rest = line[4:].split('|', 1)
            m = re.match(r'\s*(.*?)\s+(\d+)\s+[\d.]+%\s+[\d.]+/op', rest)
            r['cat'][m.group(1)] = int(m.group(2))
        elif line.startswith('CAND '):
            name, rest = line[5:].split('|', 1)
            m = re.match(r'\s*(.*?)\s+(\d+)\s+[\d.]+/op', rest)
            r['cand'][m.group(1)] = int(m.group(2))
        elif line.startswith('SCAN '):
            m = re.search(r'bytes=(\d+) records=(\d+).* ops=(\d+) value=(\d+) delete=(\d+)', line)
            r['bytes'], r['records'], r['ops'], r['values'], r['deletes'] = map(int, m.groups())
        elif ' FILL ' in line:
            r['fill'] = float(re.search(r'bytes/op=([\d.]+)', line).group(1))
        elif ' PHASE ' in line:
            r['phase'] = float(re.search(r'bytes/op=([\d.]+)', line).group(1))
        elif line.startswith('DEFLATE '):
            r['defl6'] = float(re.search(r'level6=\d+ \(([\d.]+)\)', line).group(1))
            r['defl1'] = float(re.search(r'level1=\d+ \(([\d.]+)\)', line).group(1))
        elif line.startswith('DEFLATE-INDEX '):
            r['deflidx'] = float(re.search(r'\(([\d.]+)\)', line).group(1))
        elif line.startswith('DEFLATE-NODE '):
            r['deflnode'] = float(re.search(r'\(([\d.]+)\)', line).group(1))
        elif line.startswith('RECSIZE '):
            r['recsize'] = line.split(' ', 2)[2].strip()
    return r

def g(d, k):
    return d.get(k, 0)

def parts(r):
    c, k = r['cat'], r['cand']
    ops = max(1, r['ops'])
    val = g(c, 'value node value')
    vover = sum(v for n, v in c.items() if n.startswith('value node') or n.startswith('delete node')) - val
    idx = sum(v for n, v in c.items() if n.startswith('leaf') or n.startswith('inner') or n.startswith('top'))
    keyb = g(c, 'leaf live key klongs') + g(c, 'inner live key klongs') + g(c, 'leaf dead key klongs') + g(c, 'inner dead key klongs')
    refs = sum(g(c, p + s) for p in ('leaf ', 'inner ') for s in ('live key refs', 'dead key refs'))
    nullrefs = sum(g(c, p + s) for p in ('leaf ', 'inner ') for s in ('time klong refs (-1)', 'bitmap refs (-1)'))
    times = g(c, 'leaf time klongs') + g(c, 'inner time klongs') + g(c, 'leaf bitmap klongs') + g(c, 'inner bitmap klongs')
    hdr = sum(g(c, p + s) for p in ('leaf ', 'inner ') for s in ('node header', 'prevPos', 'leaf, n, reserved', 'id'))
    dead = sum(g(c, p + s) for p in ('leaf ', 'inner ') for s in ('dead key klongs', 'dead key refs'))
    frame = sum(g(c, n) for n in ('record header', 'end marker and count', 'got-dirty ids',
                                  'got-dirty positions', 'padding', 'last byte', 'meta blocks', 'failed record'))
    gd = g(c, 'got-dirty ids') + g(c, 'got-dirty positions')
    total = r['bytes']
    kc = lambda s: g(k, 'leaf ' + s) + g(k, 'inner ' + s)
    K0 = kc('K0 today')
    sav = {
        'K1': K0 - kc('K1 no refs of time and bitmap klongs'),
        'K2': K0 - kc('K2 K1 + compact header'),
        'K2f': K0 - kc('K2f K2 + 6-byte refs'),
        'K3': K0 - kc('K3 K2 + refs relative to the record'),
        'K3a': K0 - kc('K3a K2 + refs absolute varint'),
        'K4': K0 - kc('K4 K3 + compact klongs, shared prefix'),
        'K4b': K0 - kc('K4b K3 + klongs as zigzag deltas'),
        'K5': K0 - kc('K5 K4 without dead klongs'),
        'dead': K0 - kc('K0d today without dead klongs'),
        'D0': K0 - kc('D0 delta in format 2: 32 + 16 a new klong'),
        'D1': K0 - kc('D1 delta in encoding C'),
        'V1': g(k, 'V0 value today') + g(k, 'V0 delete today') - g(k, 'V1 value compact') - g(k, 'V1 delete compact'),
        'V2': g(k, 'V0 value today') + g(k, 'V0 delete today') - g(k, 'V2 value compact no offset') - g(k, 'V2 delete compact no offset'),
        'R1': g(k, 'R0 record frame today') + g(k, 'R0 padding today') - g(k, 'R1 record frame compact')
              - 3.5 * r['records'],   # a compact record keeps 8-byte alignment: 3.5 bytes of padding on average
        'T1': g(k, 'T0 top today') - g(k, 'T1 top compact'),
    }
    sav['ALL'] = sav['K4'] + sav['V1'] + sav['R1'] + sav['T1']
    return dict(ops=ops, total=total, val=val, vover=vover, idx=idx, frame=frame, gd=gd, keyb=keyb,
                refs=refs, nullrefs=nullrefs, times=times, hdr=hdr, dead=dead, sav=sav)

def main():
    files = []
    for d in sys.argv[1:]:
        files += sorted(glob.glob(os.path.join(d, '*.txt')))
    rows = []
    for f in files:
        if os.path.basename(f) == 'runs.log':
            continue
        r = parse(f)
        if 'bytes' not in r:
            continue
        rows.append((r, parts(r)))
    print('Bytes an operation, by part (window of the scan)')
    print('%-16s %7s %6s %6s %6s %6s | %5s %5s %5s %5s %5s %5s %5s' % (
        'run', 'total', 'value', 'v.ovh', 'index', 'frame', 'hdr', 'time', 'nulrf', 'keys', 'refs', 'dead', 'gd'))
    for r, p in rows:
        o = p['ops']
        print('%-16s %7.1f %6.1f %6.1f %6.1f %6.1f | %5.1f %5.1f %5.1f %5.1f %5.1f %5.1f %5.1f' % (
            r['name'], p['total'] / o, p['val'] / o, p['vover'] / o, p['idx'] / o, p['frame'] / o,
            p['hdr'] / o, p['times'] / o, p['nullrefs'] / o, p['keyb'] / o, p['refs'] / o,
            p['dead'] / o, p['gd'] / o))
    print()
    print('Saved an operation, by candidate (and in % of the total)')
    keys = ['K1', 'K2', 'K2f', 'K3a', 'K3', 'K4', 'K4b', 'K5', 'dead', 'D0', 'D1', 'V1', 'R1', 'ALL']
    print('%-16s ' % 'run' + ' '.join('%6s' % k for k in keys) + '  ALL%   defl6  dIdx  dNode')
    for r, p in rows:
        o = p['ops']
        s = p['sav']
        print('%-16s ' % r['name'] + ' '.join('%6.1f' % (s[k] / o) for k in keys)
              + '  %4.1f%%  %5s %5s %5s' % (100.0 * s['ALL'] / p['total'],
                                         r.get('defl6', '-'), r.get('deflidx', '-'), r.get('deflnode', '-')))
    print()
    print('Index share and what the index candidates save of the index')
    for r, p in rows:
        o = p['ops']
        s = p['sav']
        print('%-16s index %5.1f%% of total; K1 %4.1f%% K3 %4.1f%% K4 %4.1f%% K5 %4.1f%% of index; fill %s phase %s; rec %s' % (
            r['name'], 100.0 * p['idx'] / p['total'], 100.0 * s['K1'] / max(1, p['idx']),
            100.0 * s['K3'] / max(1, p['idx']), 100.0 * s['K4'] / max(1, p['idx']),
            100.0 * s['K5'] / max(1, p['idx']), r.get('fill'), r.get('phase'), r.get('recsize')))

    print()
    print('Encoding C by kind of klong (024-19): a written key node, leaves and inner nodes together')
    print('%-16s %8s %6s | %5s %5s %5s %5s | %6s %6s %6s %6s %6s | %6s %6s' % (
        'run', 'nodes', 'n', 'time', 'bmp', 'live', 'dead', 'hdrC', 'B/time', 'B/bmp', 'B/live',
        'B/dead', 'today', 'C'))
    for r, p in rows:
        k = r['cand']
        kc = lambda s: g(k, 'leaf ' + s) + g(k, 'inner ' + s)
        nodes = kc('count nodes')
        if not nodes:
            continue
        nt, nb, nl, nd = (kc('count time klongs'), kc('count bitmap klongs'),
                          kc('count live key klongs'), kc('count dead key klongs'))
        n = nt + nb + nl + nd
        print('%-16s %8d %6.2f | %5.2f %5.2f %5.2f %5.2f | %6.1f %6.2f %6.2f %6.2f %6.2f | %6.1f %6.1f' % (
            r['name'], nodes, n / nodes, nt / nodes, nb / nodes, nl / nodes, nd / nodes,
            kc('C part header') / nodes, kc('C kind time klongs') / max(1, nt),
            kc('C kind bitmaps') / max(1, nb),
            kc('C kind live key klongs with refs') / max(1, nl),
            kc('C kind dead key klongs with refs') / max(1, nd),
            kc('K0 today') / nodes, kc('K4 K3 + compact klongs, shared prefix') / nodes))

main()
