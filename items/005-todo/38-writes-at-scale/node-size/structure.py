#!/usr/bin/env python3
"""The tree after a load, by node size (bergdb 005-38): from NodeSizeBench outputs."""
import re, sys
TREE = re.compile(r'^  tree (s\dh\d): (\d+) nodes, ([\d.]+) klongs, ([\d.]+) live keys, ([\d.]+) capacity, (\d+) B on stream, (\d+) B mem est')
for p in sys.argv[1:]:
    keys = None; nodes = {}; path = None; heap = None; reach = None; hu = None; dl = None; heap0 = None; upd = 0
    for line in open(p):
        m = re.match(r'NodeSizeBench: (\d+) keys .* node (\d+).*updates (\d+)', line)
        if m: keys = int(m.group(1)); node = m.group(2); upd = int(m.group(3))
        t = TREE.match(line)
        if t: nodes[t.group(1)] = (int(t.group(2)), float(t.group(3)), float(t.group(4)), float(t.group(5)), int(t.group(6)), int(t.group(7)))
        m = re.match(r'tree: (\d+) current key nodes.*longest path (\d+)', line)
        if m: total = int(m.group(1)); path = int(m.group(2))
        m = re.match(r'heap: (\d+) bytes after the load, (\d+) before, ([\d.]+) B a key', line)
        if m: heap = float(m.group(3)); h1 = int(m.group(1))
        m = re.match(r'heap after the updates: (\d+) bytes', line)
        if m: hu = (int(m.group(1)) - h1) / upd
        m = re.match(r'reach: (\d+) key nodes \(([\d.]+) a key', line)
        if m: reach = float(m.group(2))
        if line.startswith('D:') and dl is None:
            m = re.search(r'(\d+) nodes .*?(\d+) stream bytes \(([\d.]+) MB\), memory estimate \d+ bytes \(([\d.]+) MB', line)
            dl = (int(m.group(1)), float(m.group(3)), float(m.group(4)))
    idx = sum(n * b for n, kl, lv, cap, b, mem in nodes.values())
    leaf = nodes.get('s3h0')
    s3 = sorted(c for c in nodes if c.startswith('s3'))
    print('%s: node %s, %d keys: %d key nodes (%.3f a key), longest path %d, s3 levels %d; leaves %d (%.1f klongs, %.1f live keys, capacity %.1f); index on stream %.1f B a key; heap %.0f B a key after the load, +%s B an update; reachable key nodes %s a key; D at the end of the load %d nodes, %.1f MB stored, %.1f MB in memory (estimate)' % (
        p, node, keys, total, total / keys, path, len(s3), leaf[0], leaf[1], leaf[2], leaf[3], idx / keys, heap, '%.0f' % hu if hu else '-', reach, dl[0], dl[1], dl[2]))
