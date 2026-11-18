#!/usr/bin/env python3
"""Mode bp (the step writer as it would be, Study/ExecStep.lean) against mode
b (today's writer under the rule) on every trace (bergdb 026-21, section 5):
every field of the RESULT lines equal but the mode, the reasons' names
(`bumpwhy`: the first breach found differs where the pruned writer breaks
the rule otherwise) and `pathfresh` (counted by bp's binary only).

Usage: compare-bp.py RUNSDIR
"""
import os, sys
SKIP = ("mode=", "bumpwhy=", "pathfresh=")
runs = sys.argv[1]
same = diff = missing = 0
for s in sorted(os.listdir(runs)):
    bd = os.path.join(runs, s, "b")
    pd = os.path.join(runs, s, "bp")
    if not os.path.isdir(bd) or not os.path.isdir(pd):
        continue
    for f in sorted(os.listdir(bd)):
        def res(path):
            if not os.path.exists(path):
                return None
            for line in open(path):
                if line.startswith("RESULT"):
                    return [t for t in line.split() if not t.startswith(SKIP)]
            return None
        a, b = res(os.path.join(bd, f)), res(os.path.join(pd, f))
        if a is None or b is None:
            missing += 1
        elif a == b:
            same += 1
        else:
            diff += 1
            print("DIFF", s, f, [x for x in a if x not in b][:4], [x for x in b if x not in a][:4])
print(f"bp against b: {same} traces equal, {diff} differ, {missing} missing")
