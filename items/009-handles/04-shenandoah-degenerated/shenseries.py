#!/usr/bin/env python3
"""Shenandoah's cycles over time, from a GC log (-Xlog:gc*:...:uptime,level,tags), for 009-04.

Usage: shenseries.py STEP FROM TO GCLOG [GCLOG...]   (logs in time order; FROM, TO in uptime s)

Per window of STEP seconds: the cycles that started in it; the cancellations ("Cancelling
GC") for an allocation failure and for a concurrent GC (an old marking preempted by a young
cycle); degenerated and full cycles; the old generation's use and capacity at the end of the
window's last young cycle and its least available (generational), or the heap's use at the
end of the last cycle and its least available (satb); the increments of old marking (each
"Concurrent marking (Old)" line; one marking runs in several when young cycles preempt it); the mixed
evacuations, their regions and the MB they reclaimed. Then the totals over FROM to TO and
the triggers. A cycle's wall time is from its first line to its last, so in the generational
mode an old marking that spans young cycles counts them again.
"""
import re
import sys
from collections import Counter, defaultdict

UP = re.compile(r"^\[(\d+\.\d+)s\]\[\w+\s*\]\[([\w,]+)\s*\]\s*(.*)$")
GCN = re.compile(r"GC\((\d+)\)")
MB = {"B": 1 / 2**20, "K": 1 / 1024, "M": 1, "G": 1024}


def mb(num, unit):
    return float(num) * MB[unit]


def main():
    step, lo, hi = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    cycles = {}          # n -> dict
    workers = {}         # (n, phase) -> workers
    triggers = Counter()
    pending_trigger = None
    oldmarks = []
    cancels = []         # (t, reason)
    for path in sys.argv[4:]:
        with open(path, errors="replace") as f:
            for line in f:
                m = UP.match(line)
                if not m:
                    continue
                t = float(m.group(1))
                msg = m.group(3)
                cg = re.match(r"Cancelling GC: (.*)$", msg)
                if cg:
                    cancels.append((t, cg.group(1).strip()))
                    continue
                if msg.startswith("Trigger"):
                    pending_trigger = re.sub(r"[0-9]+(\.[0-9]+)?([KMGB%]|ms)?", "#", msg)
                    if lo <= t <= hi:
                        triggers[pending_trigger] += 1
                    continue
                g = GCN.search(msg)
                if not g:
                    continue
                n = int(g.group(1))
                c = cycles.setdefault(n, {"start": t, "end": t, "kind": None, "trigger": None,
                                          "degen": False, "full": False,
                                          "mixed": None, "oldUsed": None, "oldAvail": None,
                                          "used": None, "avail": None, "conc": 0.0, "concW": 0.0,
                                          "pause": 0.0})
                c["end"] = t
                k = re.search(r"Start GC cycle(?: \((\w+)\))?", msg)
                if k:
                    c["kind"] = k.group(1) or "Global"
                    c["trigger"] = pending_trigger
                    pending_trigger = None
                if "Degenerated" in msg:
                    c["degen"] = True
                if "Pause Full" in msg:
                    c["full"] = True
                w = re.search(r"Using (\d+) of \d+ workers for (.*)$", msg)
                if w:
                    workers[(n, w.group(2).strip().lower())] = int(w.group(1))
                    continue
                p = re.search(r"\)\s+(Concurrent [^0-9]*?)\s+(?:\d+[KMG]->\S+\s+)?(\d+\.\d+)ms\s*$", msg)
                if p:
                    ms = float(p.group(2))
                    c["conc"] += ms
                    name = p.group(1).lower()
                    nw = 1
                    for (wn, wp), v in workers.items():
                        if wn == n and (wp.startswith(name.replace("concurrent ", "")[:12])
                                        or name.replace("concurrent ", "")[:12] in wp):
                            nw = v
                    c["concW"] += ms * nw
                q = re.search(r"(Pause [^0-9]*?)\s+(?:\d+[KMG]->\S+\s+)?(\d+\.\d+)ms\s*$", msg)
                if q:
                    c["pause"] += float(q.group(2))
                    if "Final Mark (Old)" in q.group(1) or "Init Mark (Old)" in q.group(1):
                        pass
                mx = re.search(r"Old-gen mixed evac \((\d+) regions, evacuating (\d+)([KMGB]), reclaiming: (\d+)([KMGB])\)", msg)
                if mx:
                    c["mixed"] = (int(mx.group(1)), mb(mx.group(2), mx.group(3)), mb(mx.group(4), mx.group(5)))
                o = re.search(r"Old generation used: (\d+)([KMGB]), .*max capacity: (\d+)([KMGB]), available: (\d+)([KMGB])", msg)
                if o:
                    c["oldUsed"] = mb(o.group(1), o.group(2))
                    c["oldMax"] = mb(o.group(3), o.group(4))
                    c["oldAvail"] = mb(o.group(5), o.group(6))
                a = re.search(r"At end of (?:Concurrent |Degenerated |Full )?GC: used: (\d+)([KMGB]), .*available: (\d+)([KMGB])", msg)
                if a:
                    c["used"] = mb(a.group(1), a.group(2))
                    c["avail"] = mb(a.group(3), a.group(4))
                if "Concurrent marking (Old)" in msg and msg.rstrip().endswith("ms"):
                    oldmarks.append((t, n))
    rows = defaultdict(list)
    for n, c in sorted(cycles.items()):
        if lo <= c["start"] <= hi:
            rows[int((c["start"] - lo) // step)].append(c)
    def win(t):
        return int((t - lo) // step)
    cw = defaultdict(Counter)
    for t, why in cancels:
        if lo <= t <= hi:
            cw[win(t)][why] += 1
    mw = Counter(win(t) for t, n in oldmarks if lo <= t <= hi)
    print("window(s) cycles cancelled(alloc,conc) degen full | oldUsed oldMax minOldAvail | used minAvail | oldMarkIncrements | mixed n regions reclaimedMB")
    for i in sorted(rows):
        cs = rows[i]
        olds = [c for c in cs if c["oldUsed"] is not None]
        useds = [c for c in cs if c["used"] is not None]
        mixed = [c["mixed"] for c in cs if c["mixed"]]
        s = f"{lo + i * step:7.0f} {len(cs):5d} {cw[i].get('Allocation Failure', 0)},{cw[i].get('Concurrent GC', 0)}"
        s += f" {sum(c['degen'] for c in cs)} {sum(c['full'] for c in cs)} |"
        if olds:
            s += f" {olds[-1]['oldUsed']:7.0f} {olds[-1]['oldMax']:7.0f} {min(c['oldAvail'] for c in olds):6.0f} |"
        else:
            s += " - - - |"
        if useds:
            s += f" {useds[-1]['used']:6.0f} {min(c['avail'] for c in useds):6.0f} |"
        else:
            s += " - - |"
        s += f" {mw.get(i, 0)} | {len(mixed)} {sum(x[0] for x in mixed)} {sum(x[2] for x in mixed):.0f}"
        print(s)
    allc = [c for c in cycles.values() if lo <= c["start"] <= hi]
    wall = sum(c["end"] - c["start"] for c in allc)
    print(f"cycles {len(allc)}, wall {wall:.1f} s ({100 * wall / (hi - lo):.1f}% of the window), "
          f"concurrent phases {sum(c['conc'] for c in allc) / 1000:.1f} s, worker time {sum(c['concW'] for c in allc) / 1000:.1f} s, "
          f"pauses {sum(c['pause'] for c in allc):.0f} ms; degenerated {sum(c['degen'] for c in allc)}, full {sum(c['full'] for c in allc)}, "
          f"cancelled {dict(Counter(why for t, why in cancels if lo <= t <= hi))}; old marking increments {sum(1 for t, n in oldmarks if lo <= t <= hi)}")
    mixed = [c["mixed"] for c in allc if c["mixed"]]
    if mixed:
        print(f"mixed evacuations {len(mixed)}: regions {sum(x[0] for x in mixed)}, evacuated {sum(x[1] for x in mixed):.0f} MB, reclaimed {sum(x[2] for x in mixed):.0f} MB")
    for k, v in triggers.most_common():
        print(f"  {v:5d}  {k}")


main()
