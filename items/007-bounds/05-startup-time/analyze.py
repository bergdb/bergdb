#!/usr/bin/env python3
"""007-05: where a start's time goes, and the fit, from StartupBench's outputs.

Usage: python3 -I analyze.py OUTDIR (the night's out/, with s1/ in it).

* F53, warm: the third start of each database (the warmest; the first counts
  the reads by phase, at about 6 us a read), its time split by the sampler's
  shares into reading the section, the rerun, rule 4 (linkD), the section's
  nodes (createMaps to findSuperNodeAtStartupTime), the check
  (postStartupCheck) and the rest. Reads by phase from the first start.
* The fit: time = a * section MB + b * puts rerun + c * random reads, by
  least squares over the warm databases (not the 50M ones, which F53's
  32 GB does not keep in the OS cache).
* s1, cold: the timed cold start (cold2) and the third start, in reads and
  the rest; rule 4's share from the counted cold start (cold1).
"""

import glob
import json
import os
import sys

TX = 1000   # puts a transaction, StartupBench.TX
GROUPS = [
    ("read", ["readTransactions"]),
    ("rerun", ["starter.rerunTransactions"]),
    ("rule4", ["starter.linkD"]),
    ("nodes", ["starter.createMaps", "starter.updateStreamPointers",
               "starter.changeKeyNodesToStateAtStartupTime", "starter.checkStreamPointers",
               "starter.createMemoryPointers", "starter.registerSectionNodes",
               "starter.findSuperNodeAtStartupTime"]),
    ("check", ["starter.postStartupCheck"]),
]


def result(path):
    with open(path) as f:
        for line in f:
            if line.startswith("RESULT "):
                return json.loads(line[7:])
    return None


def split(r):
    ph, t, g, used = r["phases"], r["startupSec"], {}, set()
    for name, phases in GROUPS:
        g[name] = t * sum(ph.get(p, {}).get("timeShare", 0) for p in phases)
        used.update(phases)
    g["rest"] = t * sum(v.get("timeShare", 0) for p, v in ph.items() if p not in used)
    return g


def reads(r, phase=None):
    ph = r["phases"]
    if phase:
        return ph.get(phase, {}).get("reads", 0), ph.get(phase, {}).get("readSec", 0)
    return sum(v["reads"] for v in ph.values()), sum(v["readSec"] for v in ph.values())


def lstsq(rows, ys):
    k = len(rows[0])
    m = [[sum(r[i] * r[j] for r in rows) for j in range(k)] + [sum(r[i] * y for r, y in zip(rows, ys))]
         for i in range(k)]
    for i in range(k):
        p = max(range(i, k), key=lambda q: abs(m[q][i]))
        m[i], m[p] = m[p], m[i]
        for q in range(k):
            if q != i:
                f = m[q][i] / m[i][i]
                m[q] = [a - f * b for a, b in zip(m[q], m[i])]
    return [m[i][k] / m[i][i] for i in range(k)]


def main(out):
    names = sorted({os.path.basename(f)[:-len("-start1.txt")] for f in glob.glob(out + "/f53-*-start1.txt")})
    data = {}
    print("F53, warm: the third start split by phase (s)")
    print("%-16s %7s %7s %7s %7s %7s %7s %7s | %9s %9s %10s" % (
        "database", "start", "read", "rerun", "rule4", "nodes", "check", "rest", "rerun rd", "rule4 rd", "puts"))
    for n in names:
        r1, r3 = result(f"{out}/{n}-start1.txt"), result(f"{out}/{n}-start3.txt")
        if not (r1 and r3):
            continue
        g = split(r3)
        rr, lr = reads(r1, "starter.rerunTransactions")[0], reads(r1, "starter.linkD")[0]
        puts = r3["transRerun"] * TX
        data[n] = (r3, g, rr, lr, puts, reads(r1)[0])
        print("%-16s %7.2f %7.2f %7.2f %7.2f %7.2f %7.2f %7.2f | %9d %9d %10d" % (
            n, r3["startupSec"], g["read"], g["rerun"], g["rule4"], g["nodes"], g["check"], g["rest"], rr, lr, puts))

    print()
    print("F53, warm: unit costs of the third start")
    print("%-16s %9s %9s %9s %10s %10s %9s %9s" % (
        "database", "ms/MB", "read ms/MB", "rerun us/put", "rule4 us/rd", "rule4 rd/D", "nodes us/D", "check us/D"))
    for n, (r3, g, rr, lr, puts, _) in data.items():
        mb, d = r3["sectionBytes"] / 1e6, r3["dNodes"]
        print("%-16s %9.1f %9.1f %9.2f %10.2f %10.2f %9.2f %9.2f" % (
            n, r3["startupSec"] * 1e3 / mb, g["read"] * 1e3 / mb, g["rerun"] * 1e6 / puts, g["rule4"] * 1e6 / max(lr, 1),
            lr / d, g["nodes"] * 1e6 / d, g["check"] * 1e6 / d))

    warm = [n for n in data if "-50m-" not in n]
    rows = [[data[n][0]["sectionBytes"] / 1e6, data[n][4] / 1e6, data[n][5] / 1e6] for n in warm]
    ys = [data[n][0]["startupSec"] for n in warm]
    a, b, c = lstsq(rows, ys)
    print()
    print("Fit over %s: time = %.2f ms * MB + %.2f us * puts + %.2f us * reads" % (", ".join(warm), a * 1e3, b, c))
    for n in data:
        r3, _, _, _, puts, rd = data[n]
        f = a * r3["sectionBytes"] / 1e6 + b * puts / 1e6 + c * rd / 1e6
        print("  %-16s %7.2f s, fit %7.2f s (%+.0f %%)%s" % (
            n, r3["startupSec"], f, 100 * (f - r3["startupSec"]) / r3["startupSec"], "" if n in warm else ", not in the fit"))

    print()
    print("s1, cold and third start: reads and the rest")
    print("%-26s %8s %9s %8s %8s %7s %9s" % ("start", "time s", "reads", "in reads", "us/read", "rest s", "device MB"))
    for f in sorted(glob.glob(out + "/s1/s1-*-cold2.txt") + glob.glob(out + "/s1/s1-*-warm.txt")):
        r = result(f)
        if not r:
            continue
        n, s = reads(r)
        print("%-26s %8.1f %9d %8.1f %8.0f %7.1f %9.0f" % (
            os.path.basename(f), r["startupSec"], n, s, s * 1e6 / n, r["startupSec"] - s, r.get("deviceReadBytes", 0) / 1e6))
    print()
    print("s1, counted cold start: rule 4 and the rerun")
    for f in sorted(glob.glob(out + "/s1/s1-*-cold1.txt")):
        r = result(f)
        if not r:
            continue
        n, s = reads(r)
        ln, ls = reads(r, "starter.linkD")
        rn, rs = reads(r, "starter.rerunTransactions")
        share = r["phases"]["starter.linkD"]["timeShare"]
        print("  %-24s rule 4: %d reads (%.1f %% of %d), %.1f s (%.1f %% of %.1f s in reads), %.1f %% of the samples;"
              " rerun: %d reads, %.1f s" % (os.path.basename(f), ln, 100 * ln / n, n, ls, 100 * ls / s, s, 100 * share, rn, rs))


if __name__ == "__main__":
    main(sys.argv[1])
