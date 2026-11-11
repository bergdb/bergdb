#!/usr/bin/env python3
"""024-11: the model (sim.py) with a fill in random order, 100 keys a transaction, then single-key
overwrites at random: key nodes, live keys a node, klongs a node and splits a put, for P5's
thresholds and the denser set of QU4. 2026-11-11."""
import random, sys
from sim import Tree, fill
n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
for name, kw in (('P5: m 7, h 15, c 15', {}), ('dense: m 10, h 20, c 20', dict(m=10, h=20, c=20))):
    t = Tree(**kw); keys = list(range(n)); random.Random(1).shuffle(keys); fill(t, keys)
    nodes, live, used = t.walk(); s1 = t.n_time + t.n_space; new1 = t.n_new
    print('%s: random fill: %d nodes, %.1f keys a node, %.1f klongs a node, %.3f splits and %.3f new nodes a put'
          % (name, nodes, live / nodes, used / nodes, s1 / n, new1 / n))
    rnd = random.Random(2)
    for _ in range(2 * n):
        t.begin(); t.put(rnd.randrange(n))
    nodes, live, used = t.walk()
    print('   after %d overwrites: %d nodes, %.1f klongs a node, %.3f splits and %.3f new nodes an overwrite'
          % (2 * n, nodes, used / nodes, (t.n_time + t.n_space - s1) / (2 * n), (t.n_new - new1) / (2 * n)))
