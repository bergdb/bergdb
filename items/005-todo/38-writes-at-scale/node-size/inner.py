#!/usr/bin/env python3
"""Share of the current index that is not value leaves (s3h0), by count, memory and stream bytes."""
import re, sys
T = re.compile(r'^  tree (s\dh\d): (\d+) nodes, ([\d.]+) klongs, ([\d.]+) live keys, ([\d.]+) capacity, (\d+) B on stream, (\d+) B mem est')
for p in sys.argv[1:]:
    rows = [T.match(l) for l in open(p)]
    rows = [(m.group(1), int(m.group(2)), int(m.group(6)), int(m.group(7))) for m in rows if m]
    keys = int(re.search(r'(\d+) keys', open(p).readline()).group(1))
    n = sum(r[1] for r in rows); nl = sum(r[1] for r in rows if r[0] == 's3h0')
    s = sum(r[1] * r[2] for r in rows); sl = sum(r[1] * r[2] for r in rows if r[0] == 's3h0')
    m = sum(r[1] * r[3] for r in rows); ml = sum(r[1] * r[3] for r in rows if r[0] == 's3h0')
    path = re.search(r'longest path (\d+)', open(p).read()).group(1)
    print('%s: %d keys; nodes %.3f a key, not value leaves %.1f%% of nodes, %.1f%% of memory est., %.1f%% of stream bytes; index %.1f B a key on stream, %.1f B a key memory est.; longest path %s' % (
        p, keys, n / keys, 100 * (n - nl) / n, 100 * (m - ml) / m, 100 * (s - sl) / s, s / keys, m / keys, path))
