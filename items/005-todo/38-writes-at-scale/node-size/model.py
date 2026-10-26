#!/usr/bin/env python3
"""The write model of the node-size study (bergdb 005-38), against a NodeSizeBench run.

Steady state at a fixed size, random puts: every put dirties its whole path, one node a
class (segment s, height h). A class has N nodes; a window (sd bytes of stream) has
P = sd / B puts, so a node of the class is touched x = P / N times a window.

  value leaves (s3h0, no key node children): dirty for one window after a touch, then clean
      until the next touch: w = 1 / (1 + x) writes a put;
  every other node: also written again while a child is dirty at its write, which happens
      if it was touched in the window before (Db.handleStillDirtyNodes): w = 1 / (x + e^-x);
  B = V + sum over classes of w * (b + 16): b the bytes of a written node of the class
      (measured), 16 its entry in a got-dirty list; V the value node (68 B) and the rest.

Solved for B by iteration. Usage: python3 -I model.py FILE [FILE...] (NodeSizeBench outputs
with an update phase); compares with the update phase's second half.
"""
import math
import re
import sys

sys.path.insert(0, __import__('os').path.dirname(__file__))
import analyze  # noqa: E402

TREE = re.compile(r'^  tree (s\dh\d): (\d+) nodes, ([\d.]+) klongs, ([\d.]+) live keys, ([\d.]+) capacity, (\d+) B on stream')


def predict(N, b, sd, V, r0=0.0):
    """sd: the window in bytes (the startup distance, or the measured startup lag); r0:
    leaf replacements a put (time splits; 0 leaves out dead versions): a leaf that is dirty
    when it is replaced is written once more, as a dead version."""
    B = V + 100.0
    for _ in range(200):
        P = sd / B
        tot = V
        ws = {}
        for c in N:
            x = P / N[c]
            if c == 's3h0':
                w = 1.0 / (1.0 + x) + r0 * (1.0 - math.exp(-x))
            else:
                w = 1.0 / (x + math.exp(-x))
            ws[c] = w
            tot += w * (b[c] + 16)
        B = 0.5 * B + 0.5 * tot
    return B, P, ws


def run(path):
    r = analyze.parse(path)
    m = re.search(r'sd (\d+)', r['header'])
    sd = int(m.group(1))
    N = {}
    for line in r['other']:
        t = TREE.match(line)
        if t:
            N[t.group(1)] = int(t.group(2))
    ws = analyze.tail(r["upd"], 0.8)
    cm = analyze.classmean(ws)
    meas = analyze.mean([w['B'] for w in ws])
    V = analyze.mean([w['value'] + w['top'] for w in ws]) + 1
    b = {c: (cm[c][1] if c in cm else 300.0) for c in N}
    B, P, wp = predict(N, b, sd, V)
    print('== %s: sd %d MB; measured B/put %.0f, model %.0f (P = %.0f puts a window)' % (path, sd // 1000000, meas, B, P))
    for c in sorted(N):
        mw = cm[c][0] if c in cm else 0.0
        print('   %s N %8d  x %8.3f  writes/put measured %.3f model %.3f  (b %.0f B)' % (c, N[c], P / N[c], mw, wp[c], b[c]))


if __name__ == '__main__':
    for p in sys.argv[1:]:
        run(p)
