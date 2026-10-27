#!/usr/bin/env python3
"""005-57: the tables of the report from StartBench's outputs.

Usage: python3 -I analyze.py OUTDIR, where OUTDIR has F53's outputs (f53-*.txt) and s1/
(s1-*.txt), as f53-57.sh and s1-57.sh write them.

* Startup time by scenario and version: warm on F53 (the median of the three timed
  starts), cold on s1 (the two timed cold starts).
* The reads of a start by where they come from (the counted starts), F53 and s1.
* Rule 4 by position against rule 4 by id (the check runs).
* After the start: N transactions of 1,000 updates, time and reads by source.
"""

import glob
import json
import os
import statistics
import sys

VERSIONS = [("rel", "2026.1"), ("head", "current"), ("proto", "part 1"), ("proto2", "parts 1+2")]


def result(path):
    try:
        with open(path) as f:
            for line in f:
                if line.startswith("RESULT "):
                    return json.loads(line[7:])
    except FileNotFoundError:
        pass
    return None


def results(pattern):
    return [r for r in (result(f) for f in sorted(glob.glob(pattern))) if r]


def reads(r, key="startReads"):
    return sum(v["reads"] for v in r[key].values())


def main(out):
    for sc in ("10m-sd50", "10m-sd200"):
        print("Scenario", sc)
        print("  %-10s %28s %24s %12s" % ("version", "warm F53 (median; runs)", "cold s1 (runs)", "reads"))
        for v, name in VERSIONS:
            w = [r["startupSec"] for r in results("%s/f53-%s-%s-warm[0-9].txt" % (out, sc, v))]
            c = [r["startupSec"] for r in results("%s/s1/s1-%s-%s-cold[0-9].txt" % (out, sc, v))]
            n = results("%s/f53-%s-%s-warm1.txt" % (out, sc, v))
            ws = "%.2f s; %s" % (statistics.median(w), " ".join("%.2f" % x for x in w)) if w else "-"
            cs = " ".join("%.1f" % x for x in c) + " s" if c else "-"
            print("  %-10s %28s %24s %12s" % (name, ws, cs, reads(n[0]) if n else "-"))
        print()
        for where, pat in (("F53, warm", "%s/f53-%s-%s-counted.txt"), ("s1, cold", "%s/s1/s1-%s-%s-counted.txt")):
            print("  Reads by where they come from, %s (counted start; reads, s in reads):" % where)
            for v, name in VERSIONS:
                r = result(pat % (out, sc, v))
                if not r:
                    continue
                parts = ["%s %d %.1f" % (k.replace("starter.", ""), x["reads"], x["readSec"])
                         for k, x in r["startReads"].items() if x["reads"] > 0 and k not in ("recover", "handleStartParams")]
                print("    %-10s %.1f s: %s" % (name, r["startupSec"], "; ".join(parts)))
        for where, pat in (("F53", "%s/f53-%s-proto-check.txt"), ("s1", "%s/s1/s1-%s-proto-check.txt")):
            r = result(pat % (out, sc))
            if r and "rule4" in r:
                print("  Check, %s: %s" % (where, r["rule4"]))
        for label, pat in (("F53, counted", "%s/f53-%s-%s-after1.txt"), ("F53, timed", "%s/f53-%s-%s-after0.txt"),
                           ("s1, cold, timed", "%s/s1/s1-%s-%s-after.txt")):
            print("  After the start (%s):" % label)
            for v, name in VERSIONS:
                r = result(pat % (out, sc, v))
                if not r or "afterSec" not in r:
                    continue
                parts = ["%s %d" % (k.replace("after.", ""), x["reads"]) for k, x in r["afterReads"].items()]
                print("    %-10s start %.2f s; %d transactions in %.2f s (first half %.2f s); start and after %.1f s; reads: %s" % (
                    name, r["startupSec"], r["afterTrans"], r["afterSec"], r["afterFirstHalfSec"],
                    r["startupSec"] + r["afterSec"], "; ".join(parts) if parts else "none"))
        print()


def checks(out):
    """The sums of the prototype's checks in the gates' logs (out/checks-*.txt: the lines
    "005-57 rule 4 by position, checked: ..." and "005-57 resolvePointers by position, ...")."""
    import re
    for f in sorted(glob.glob(out + "/checks-*.txt")):
        r4 = [0] * 6
        rp = [0] * 6
        for line in open(f):
            m = re.search(r"rule 4 by position, checked: (\d+) startups, (\d+) pointers examined, (\d+) linked, "
                          r"(\d+) linked by id, (\d+) differences, (\d+) header reads", line)
            if m:
                r4 = [a + int(b) for a, b in zip(r4, m.groups())]
            m = re.search(r"resolvePointers by position, checked: (\d+) pointers without a handle, (\d+) in the "
                          r"section's ids, (\d+) pinned by position, (\d+) pinned by id, (\d+) checked, (\d+) differences", line)
            if m:
                rp = [a + int(b) for a, b in zip(rp, m.groups())]
        print("%s: rule 4: %d startups, %d pointers, %d linked, %d by id, %d differences, %d header reads; "
              "resolvePointers: %d pointers, %d in ids, %d pinned by position, %d by id, %d checked, %d differences"
              % tuple([os.path.basename(f)] + r4 + rp))


if __name__ == "__main__":
    main(sys.argv[1])
    checks(sys.argv[1])
