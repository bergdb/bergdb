#!/usr/bin/env python3
"""The pauses in a JVM's GC log (-Xlog:gc*,safepoint:...:uptime,level,tags), for 004-04.

Usage: gcsum.py GCLOG [FROM TO]   (FROM, TO: an uptime window in seconds; default the whole log)

Prints the collector; its pauses (count, total, the longest, how many above 1, 10 and 100 ms)
with the longest five; the stop-the-world fallbacks (G1: full collections and evacuation
failures; Shenandoah: degenerated and full cycles; ZGC: allocation stalls), those that
System.gc() asked for counted apart; and the safepoints (the time from the request to the
end, reaching included), by operation, the longest first. One line of JSON at the end.
"""
import json
import re
import sys

UP = re.compile(r"^\[(\d+\.\d+)s\]\[(\w+)\s*\]\[([\w,]+)\s*\]\s*(.*)$")
PAUSE = re.compile(r"GC\((\d+)\)\s+(?:[YyOo]: )?(Pause .*?)\s+(\d+\.\d+)ms\s*$")
HEAP = re.compile(r"\s*\d+[KMG]->.*$")
SAFEPOINT = re.compile(r'Safepoint "([^"]+)".*Reaching safepoint: (\d+) ns.*Total: (\d+) ns')
STALL = re.compile(r"Allocation Stall \((.*?)\)\s+(\d+\.\d+)ms")


def main():
    path = sys.argv[1]
    lo = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
    hi = float(sys.argv[3]) if len(sys.argv) > 3 else 1e12
    collector = "?"
    pauses = []          # (ms, uptime, what)
    fallbacks = []       # (what, ms, uptime)
    syscalls = 0
    evacfail = 0
    stalls = []
    safepoints = {}      # name -> [count, total ms, max ms, max reaching ms]
    with open(path, errors="replace") as f:
        for line in f:
            m = UP.match(line)
            if not m:
                continue
            up = float(m.group(1))
            tags = m.group(3)
            msg = m.group(4)
            if collector == "?" and tags == "gc,init" or (collector == "?" and tags == "gc"):
                if msg.startswith("Using "):
                    collector = msg[6:].strip()
            if up < lo or up > hi:
                continue
            if tags in ("gc", "gc,phases"):
                p = PAUSE.search(msg)
                if p and (tags == "gc" or "Mark Start" in msg or "Mark End" in msg
                          or "Relocate Start" in msg):
                    if tags == "gc,phases" and "ZGC" not in collector and "Z Garbage" not in collector:
                        continue
                    what = HEAP.sub("", p.group(2)).strip()
                    ms = float(p.group(3))
                    pauses.append((ms, up, what))
                    if "System.gc()" in what:
                        if "Full" in what or "Degenerated" in what:
                            syscalls += 1
                    elif "Pause Full" in what or "Degenerated" in what:
                        fallbacks.append((what, ms, up))
                    if "Evacuation Failure" in what:
                        evacfail += 1
                s = STALL.search(msg)
                if s and tags == "gc":
                    stalls.append((float(s.group(2)), up, s.group(1)))
            elif tags == "safepoint":
                s = SAFEPOINT.search(msg)
                if s:
                    name = s.group(1)
                    total = int(s.group(3)) / 1e6
                    reach = int(s.group(2)) / 1e6
                    e = safepoints.setdefault(name, [0, 0.0, 0.0, 0.0])
                    e[0] += 1
                    e[1] += total
                    e[2] = max(e[2], total)
                    e[3] = max(e[3], reach)
    ms = sorted((p[0] for p in pauses), reverse=True)
    out = {
        "log": path.split("/")[-1], "collector": collector, "window": [lo, hi],
        "pauses": len(ms), "pauseTotalMs": round(sum(ms), 1), "pauseMaxMs": ms[0] if ms else 0.0,
        "over1ms": sum(1 for x in ms if x > 1), "over10ms": sum(1 for x in ms if x > 10),
        "over100ms": sum(1 for x in ms if x > 100),
        "fallbacks": len(fallbacks), "fallbackTotalMs": round(sum(f[1] for f in fallbacks), 1),
        "fallbackMaxMs": max((f[1] for f in fallbacks), default=0.0),
        "systemGcFull": syscalls, "evacuationFailures": evacfail,
        "allocationStalls": len(stalls), "stallMaxMs": max((s[0] for s in stalls), default=0.0),
        "safepointMaxMs": round(max((e[2] for e in safepoints.values()), default=0.0), 2),
    }
    print("%s: %s, window %s to %s s" % (out["log"], collector, lo, hi if hi < 1e12 else "end"))
    print("  pauses: %d, %.1f ms in all, longest %.2f ms; above 1 ms %d, 10 ms %d, 100 ms %d"
          % (out["pauses"], out["pauseTotalMs"], out["pauseMaxMs"], out["over1ms"],
             out["over10ms"], out["over100ms"]))
    for p in sorted(pauses, reverse=True)[:5]:
        print("    %10.2f ms at %9.1f s  %s" % p)
    print("  fallbacks (full, degenerated; not System.gc()): %d, %.1f ms in all, longest %.1f ms;"
          " System.gc() full: %d; evacuation failures: %d; allocation stalls: %d (longest %.2f ms)"
          % (out["fallbacks"], out["fallbackTotalMs"], out["fallbackMaxMs"], syscalls, evacfail,
             len(stalls), out["stallMaxMs"]))
    print("  safepoints by operation (count, total ms, longest ms, longest reaching ms):")
    for name, e in sorted(safepoints.items(), key=lambda kv: -kv[1][2])[:8]:
        print("    %-32s %6d %10.1f %9.2f %8.2f" % (name, e[0], e[1], e[2], e[3]))
    print("JSON " + json.dumps(out))


if __name__ == "__main__":
    main()
