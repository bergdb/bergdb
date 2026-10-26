#!/usr/bin/env python3
"""The write model (model.py) for a run without tree stats: node counts from another run's
tree, scaled by keys (the segment-3 trees are full from 1M keys on, so every class grows
with K); bytes a written node from the run's own windows (classes, or WriteBench's kinds:
vleaf s3h0, lleaf s2h0, in1 s3h1 and s2h1, in2 s3h2 and s2h2, in3+ the rest).

Usage: python3 -I model2.py TREE_RUN RUN [RUN...]"""
import math
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze  # noqa: E402
from model import TREE, predict  # noqa: E402

L0 = 13.6


def kind_of(c):
    s, h = int(c[1]), int(c[3])
    if h == 0:
        return 'vleaf' if s == 3 else 'lleaf'
    return {1: 'in1', 2: 'in2'}.get(h, 'in3')


def main():
    tree = sys.argv[1]
    k0 = int(re.search(r'(\d+) keys', open(tree).readline()).group(1))
    N0 = {}
    global L0
    for line in open(tree):
        t = TREE.match(line)
        if t:
            N0[t.group(1)] = int(t.group(2))
            if t.group(1) == 's3h0':
                L0 = float(t.group(4))
    for p in sys.argv[2:]:
        r = analyze.parse(p)
        keys = int(re.search(r'(\d+) keys', r['header']).group(1))
        sd = int(re.search(r'sd (\d+)', r['header']).group(1))
        N = {c: max(1, round(n * keys / k0)) if c[1] in '23' else n for c, n in N0.items()}
        ws = analyze.tail(r['upd'], 0.8)
        meas = analyze.mean([w['B'] for w in ws])
        V = analyze.mean([w['value'] + w['top'] for w in ws]) + 1
        if ws[0]['classes']:
            cm = analyze.classmean(ws)
            b = {c: (cm[c][1] if c in cm else 300.0) for c in N}
            mw = {c: (cm[c][0] if c in cm else 0.0) for c in N}
            group = {c: c for c in N}
        else:
            km = analyze.kindmean(ws)
            b = {c: (km[kind_of(c)][1] if kind_of(c) in km else 300.0) for c in N}
            mw = {k: v[0] for k, v in km.items()}
            group = {c: kind_of(c) for c in N}
        lags = [int(m.group(1)) * 1000000 for m in (re.search(r'startup lag (\d+) MB', l) for l in open(p)) if m]
        lags = lags[len(lags) - len(ws):] if len(lags) >= len(ws) else lags
        lag = sum(lags) / len(lags) if lags else sd
        node = int(re.search(r'node (\d+)', r['header']).group(1)) if 'node' in r['header'] else 30
        live0 = L0
        r0 = 2.0 / max(2.0, node - 1 - live0)
        B, P, wp = predict(N, b, sd, V)
        B2, P2, wp2 = predict(N, b, lag, V)
        B3, P3, wp3 = predict(N, b, lag, V, r0)
        print('== %s: %d keys, sd %d MB (lag %.0f MB): measured B/put %.0f; model %.0f (window sd), %.0f (window lag), %.0f (lag and dead leaves, r0 %.3f)' % (
            os.path.basename(p), keys, sd // 1000000, lag / 1e6, meas, B, B2, B3, r0))
        wp = wp3
        agg = {}
        for c in N:
            agg[group[c]] = agg.get(group[c], 0.0) + wp[c]
        for g in sorted(agg):
            print('   %-6s writes/put measured %.3f model %.3f' % (g, mw.get(g, 0.0), agg[g]))


if __name__ == '__main__':
    main()
