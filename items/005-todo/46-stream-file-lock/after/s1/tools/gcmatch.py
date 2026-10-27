#!/usr/bin/env python3
"""For each phase of a pause probe output, the five longest gets and commits, and what overlapped
each: a collector's pause or allocation stall (from the run's GC log, -Xlog:gc*,safepoint), a file
force, a wait for room in the write buffer (from the probe's disk lines). Usage: gcmatch.py OUT.txt GC.log"""
import re, sys

out, gclog = sys.argv[1], sys.argv[2]
events = []     # (end uptime s, duration ms, what)
for line in open(gclog):
    m = re.match(r"\[([\d.]+)s\].*Allocation Stall \(([^)]*)\) ([\d.]+)ms", line)
    if m:
        events.append((float(m.group(1)), float(m.group(3)), "allocation stall (%s)" % m.group(2)))
        continue
    m = re.match(r'\[([\d.]+)s\].*Safepoint "([^"]+)".* Total: (\d+) ns', line)
    if m and int(m.group(3)) / 1e6 >= 5:
        events.append((float(m.group(1)), int(m.group(3)) / 1e6, "safepoint " + m.group(2)))

def longest(line):
    m = re.search(r"longest at uptime (.*)$", line)
    return [(float(a), float(b)) for a, b in re.findall(r"([\d.]+)s \(([\d.]+) ms\)", m.group(1))] if m else []

phase = None
disk = {}
lines = open(out).read().split("\n")
for line in lines:
    s = line.strip()
    m = re.match(r"phase tsize=(\d+)", s)
    if m:
        phase = "tsize=" + m.group(1)
    if s.startswith("load:"):
        phase = "load"
    if phase and (s.startswith("file forces") or s.startswith("waits for room")):
        disk.setdefault(phase, []).extend((u, d, s.split(" ")[0] + " " + s.split(" ")[1]) for u, d in longest(s))
phase = None
for line in lines:
    s = line.strip()
    m = re.match(r"phase tsize=(\d+)", s)
    if m:
        phase = "tsize=" + m.group(1)
        continue
    if phase and (s.startswith("gets ") or s.startswith("commits ")):
        kind = s.split()[0]
        for end, dur in longest(s):
            start = end - dur / 1000
            over = [f"{w} {d:.1f} ms at {u:.3f}s" for u, d, w in events + disk.get(phase, [])
                    if u - d / 1000 <= end + 0.003 and u >= start - 0.003 and d >= min(5, dur / 2)]
            print(f"{phase:11s} {kind:8s} {dur:8.1f} ms at {end:8.3f}s: " + ("; ".join(over) if over else "nothing"))
