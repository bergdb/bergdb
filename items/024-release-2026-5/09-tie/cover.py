#!/usr/bin/env python3
# bergdb 024-09, A3: step 3 of 001-07, section 5, checked on reclaim traces of TraceExport.
# For every cut "CUT c f" of a trace: the iteration's steps are the records of kind=step
# after the cut before's f, up to f. Every index node reachable at time f (the model's
# reachability: the root's last top node, its root pointer, the live klongs) that was made
# before the iteration's first step must be in the TOUCH line of one of those steps.
# Usage: cover.py trace...
import sys

def live(entries, f):
    m = {}        # compare value -> child or None, in order of first appearance
    rootp = None; top = None
    for t, toks in entries:
        if t > f: break
        k = toks[0]
        if k == 'K': m[toks[1]] = toks[2]
        elif k == 'D':
            for c in toks[2:]:
                if c in m: m[c] = None
        elif k == 'R': rootp = toks[1]
        elif k == 'T': top = toks[1]
    r = [y for y in m.values() if y is not None]
    if rootp is not None: r.append(rootp)
    if top is not None: r.append(top)
    return r

def check(path):
    made = {}; kind = {}; ents = {}; touch = {}; txkind = {}; cuts = []
    i = None
    for line in open(path):
        p = line.split()
        if not p: continue
        if p[0] == 'TX': i = int(p[1])
        elif p[0] == '#':
            for w in p:
                if w.startswith('kind='): txkind[i] = w[5:]
        elif p[0] == 'NEW': made[p[1]] = i; kind[p[1]] = p[3]
        elif p[0] == 'ADD': ents.setdefault(p[1], []).append((int(p[2]), p[3:]))
        elif p[0] == 'TOUCH': touch[i] = set(p[1:])
        elif p[0] == 'CUT': cuts.append((i, int(p[1]), int(p[2])))
    res = dict(cuts=0, steps=0, old=0, touched=0, new=0, bad=0, changed=0)
    prevf = 0
    for d, c, f in cuts:
        steps = [j for j in sorted(txkind) if txkind[j] == 'step' and prevf < j <= f]
        prevf = f
        if not steps: continue
        res['cuts'] += 1; res['steps'] += len(steps)
        first = steps[0]
        tset = set()
        for j in steps: tset |= touch.get(j, set())
        seen = set(); todo = ['0']
        while todo:
            x = todo.pop()
            if x in seen: continue
            seen.add(x)
            todo.extend(live(ents.get(x, []), f))
        for x in seen:
            if kind.get(x) != 'I' or x == '0': continue
            if made[x] >= first: res['new'] += 1; continue
            res['old'] += 1
            if x in tset: res['touched'] += 1
            else:
                res['bad'] += 1
                ch = any(first <= t <= f for t, _ in ents.get(x, []))
                if ch: res['changed'] += 1
                print("  NOT TOUCHED %s: cut at R(%d) c=%d f=%d, node %s made in TX %d, steps %d..%d%s"
                      % (path.split('/')[-1], d, c, f, x, made[x], steps[0], steps[-1],
                         ", got an entry in the iteration" if ch else ""))
    return res

tot = {}
for path in sys.argv[1:]:
    r = check(path)
    for k, v in r.items(): tot[k] = tot.get(k, 0) + v
print("traces %d: iterations with a cut %d, steps %d; index nodes reachable at f: made before"
      " the first step %d, of them in a step's touch %d, not %d (with an entry in the"
      " iteration %d); made in the iteration %d"
      % (len(sys.argv) - 1, tot['cuts'], tot['steps'], tot['old'], tot['touched'], tot['bad'],
         tot['changed'], tot['new']))
