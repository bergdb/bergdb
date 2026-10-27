#!/usr/bin/env python3
"""Summarizes 005-46's pause probe outputs (PauseProbe with the disk's waits): for each run and
phase, the longest get and commit, the longest file force, the writer's waits for room, and
which of the five longest gets ended within 15 ms of one of the five longest forces' ends.
Usage: s1sum.py FILE..."""
import re, sys

def longest(line):
    m = re.search(r"longest at uptime (.*)$", line)
    if not m:
        return []
    return [(float(a), float(b)) for a, b in re.findall(r"([\d.]+)s \(([\d.]+) ms\)", m.group(1))]

def maxval(line):
    m = re.search(r"max ([\d.,]+) ms", line)
    return float(m.group(1).replace(",", "")) if m else None

for path in sys.argv[1:]:
    name = path.split("/")[-1].replace(".txt", "")
    phase = None
    rows = {}
    for line in open(path):
        line = line.rstrip("\n")
        if line.startswith("load:"):
            phase = "load"
        m = re.match(r"phase tsize=(\d+)", line)
        if m:
            phase = "tsize=" + m.group(1)
        if phase is None:
            continue
        r = rows.setdefault(phase, {})
        s = line.strip()
        if s.startswith("gets "):
            r["gets"] = (maxval(s), longest(s))
        elif s.startswith("commits "):
            r["commits"] = (maxval(s), longest(s))
        elif s.startswith("file forces"):
            r["forces"] = longest(s)
        elif s.startswith("waits for room"):
            r["room"] = longest(s)
            r["roomline"] = s
    for phase, r in rows.items():
        if phase == "load" or "gets" not in r:
            continue
        forces = r.get("forces", [])
        gmax, gl = r["gets"]
        cmax, cl = r["commits"]
        matched = [g for g in gl if any(abs(g[0] - f[0]) <= 0.015 for f in forces)]
        fmax = max([f[1] for f in forces], default=0)
        room = r.get("room")
        rmax = max([w[1] for w in room], default=0.0) if room is not None else None
        print(f"{name:22s} {phase:11s} get max {gmax:8.1f}  commit max {cmax:8.1f}  force max {fmax:7.1f}"
              f"  room max {('%.1f' % rmax) if rmax is not None else 'n/a':>7s}"
              f"  gets at a force {len(matched)} of {len(gl)}"
              + ("  " + ", ".join(f"{g[0]:.3f}s {g[1]:.1f}ms" for g in matched) if matched else ""))
