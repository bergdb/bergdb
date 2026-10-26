"""007-05: a table of StartupBench's results. Usage: python3 summary.py OUTDIR > summary.txt

Reads the RESULT lines of OUTDIR/*.txt and OUTDIR/s1/*.txt: one line a database (make) and
one a start, with the section, D, the startup time and the reads of rerun and of linkD."""
import glob, json, os, re, sys

out = sys.argv[1]
rows = []
for f in sorted(glob.glob(os.path.join(out, "*.txt")) + glob.glob(os.path.join(out, "s1", "*.txt"))):
    for line in open(f, errors="replace"):
        if line.startswith("RESULT "):
            try:
                r = json.loads(line[7:])
            except ValueError:
                continue
            r["file"] = os.path.relpath(f, out)
            rows.append(r)

MB = 1e6
print("Databases (make)")
print("%-28s %6s %6s %7s %8s %9s %9s %10s %8s %7s" % ("file", "keys", "val", "sd MB", "updates",
      "stream MB", "lag MB", "lag max MB", "D nodes", "D MB"))
for r in rows:
    if r["mode"] != "make":
        continue
    print("%-28s %5.0fM %6d %7.0f %7.1fM %9.0f %9.0f %10.0f %8d %7.0f" % (r["file"], r["keys"] / 1e6, r["valsize"],
          r["sd"] / MB, r["updates"] / 1e6, r["streamBytes"] / MB, r["lagEnd"] / MB, r["lagMax"] / MB,
          r["dNodes"], r["dBytes"] / MB))
print()
print("Starts")
print("%-28s %7s %8s %6s %8s %8s %9s %9s %9s %9s %9s" % ("file", "phases", "startup", "sect", "sect/sd",
      "rerun tx", "rerun rd", "rerun s", "linkD rd", "linkD s", "device MB"))
for r in rows:
    if r["mode"] != "start":
        continue
    ph = r.get("phases", {})
    rr = ph.get("starter.rerunTransactions", {})
    ld = ph.get("starter.linkD", {})
    dev = r.get("deviceReadBytes")
    if r.get("byPhase"):
        cols = (rr.get("reads", 0), rr.get("readSec", 0), ld.get("reads", 0), ld.get("readSec", 0))
        reads = "%9d %9.2f %9d %9.2f" % cols
    else:
        st = ph.get("start", {})
        reads = "%9s %9s %9s %9s" % ("-", "-", "%d all" % st.get("reads", 0), "%.2f all" % st.get("readSec", 0))
    print("%-28s %7s %7.2fs %5.0fM %8.2f %8d %s %9s" % (r["file"], "yes" if r.get("byPhase") else "no",
          r["startupSec"], r["sectionBytes"] / MB, r["sectionBytes"] / r["sd"], r["transRerun"], reads,
          "-" if dev is None else "%.0f" % (dev / MB)))
print()
print("Time shares by phase (samples of the starting thread), counted starts")
for r in rows:
    if r["mode"] != "start" or not r.get("byPhase"):
        continue
    ph = r.get("phases", {})
    top = sorted(ph.items(), key=lambda e: -e[1].get("timeShare", 0))[:5]
    print("%-28s %s" % (r["file"], ", ".join("%s %.0f%%" % (k, 100 * v.get("timeShare", 0)) for k, v in top)))
