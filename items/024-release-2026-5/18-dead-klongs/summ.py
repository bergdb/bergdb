#!/usr/bin/env python3
# 024-18: summarize DK outputs. summ.py FILE... ; one block a file.
import re, sys
def kv(s):
    d = {}
    for m in re.finditer(r'(\w[\w/]*)=(\[[^\]]*\]|[-\d.]+)', s):
        d[m.group(1)] = m.group(2)
    return d
for f in sys.argv[1:]:
    lines = open(f).read().splitlines()
    print("#", f.split('/')[-1], lines[0][3:60] if lines else "")
    cen = {}
    for L in lines:
        m = re.search(r'\] (CLEAF|CINNER) (\S+) (leaf|inner) (.*)', L)
        if m:
            cen.setdefault(m.group(2), {})[m.group(3)] = kv(m.group(4))
            continue
        m = re.search(r'\] PHASE (\S+) (.*)', L)
        if m:
            d = kv(m.group(2))
            print("  PHASE %-14s rec/op=%s stream/op=%s tsplit/op=%s ssplit/op=%s merge/op=%s compact/op=%s kept=%.0fMB" % (
                m.group(1), d['rec/op'], d['stream/op'], d['tsplit/op'], d['ssplit/op'], d['merge/op'],
                d.get('compact/op', '-'), int(d['kept']) / 1e6))
            continue
        m = re.search(r'\] ITER (\d+) stream=(\d+) rec=(\d+) tx=(\d+)', L)
        if m:
            print("  ITER %s stream=%.0fMB rec=%.0fMB tx=%s" % (m.group(1), int(m.group(2)) / 1e6, int(m.group(3)) / 1e6, m.group(4)))
            continue
        m = re.search(r'\] CENSUS (\S+) ', L)
        if m:
            lab = m.group(1)
            continue
        m = re.search(r'^rc=(\d+)', L)
        if m and m.group(1) != '0': print("  RC", L)
    print("  %-8s %-5s %7s %8s %8s %5s %7s %8s %7s %7s %6s %6s %5s %6s %7s %7s %6s %6s %s" % (
        "census", "cls", "nodes", "live", "dead", "d/l", "deld", "T", "withD", "coldD", "set3", "s3cold", "s3MB",
        "stMB", "liveMB", "deadMB", "heapMB", "lheapM", "hist(0,1,2,3-4,5-8,9-16,17-24,25+)"))
    for lab, c in cen.items():
        for cls in ("leaf", "inner"):
            d = c.get(cls)
            if not d: continue
            print("  %-8s %-5s %7s %8s %8s %5.2f %7s %8s %7s %7s %6s %6s %5.1f %6.1f %7.1f %7.1f %6.1f %6.1f %s" % (
                lab, cls, d['nodes'], d['live'], d['dead'], float(d['dead/live']), d['deleted'], d['time'], d['withDead'],
                d['coldWithDead'], d['set3'], d['set3Cold'], int(d['set3Bytes']) / 1e6, int(d['bytes']) / 1e6, int(d['liveBytes']) / 1e6,
                int(d['deadBytes']) / 1e6, int(d['heap']) / 1e6, int(d['liveHeap']) / 1e6, d['hist']))
