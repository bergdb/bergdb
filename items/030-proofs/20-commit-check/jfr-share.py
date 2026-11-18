#!/usr/bin/env python3
# bergdb 030-20: the check's share of a commit from a JFR recording of CCBench (s1-run.sh's
# "jfr" jobs, JFR's profile settings: an execution sample every 10 ms or so). 2026-11-18.
# Usage: python3 -I jfr-share.py JFR LOG
#   JFR: the recording; LOG: CCBench's output, whose last RESULT line gives the measured
#   phase's start and end (epoch ms). Needs `jfr` on the PATH (JAVA_HOME/bin).
# Counts the samples of the thread "main" in the phase: those in Db.execute, and of them
# those in TransCheck, split by the TransCheck method nearest the top of the stack and by
# what that frame called (the leaf frame's class). GC threads are not sampled by JFR's
# execution sampler; GC time is reported apart (jdk.GarbageCollection in the phase).
import collections
import json
import re
import subprocess
import sys
from datetime import datetime


def ms(ts):
    # "2026-11-18T14:02:03.123456789+01:00" or with Z
    m = re.match(r"(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)(\.\d+)?(Z|[+-]\d\d:\d\d)", ts)
    frac = (m.group(2) or ".0")[:7]
    tz = m.group(3).replace("Z", "+00:00")
    return datetime.fromisoformat(m.group(1) + frac + tz).timestamp() * 1000


def main():
    jfr, logp = sys.argv[1], sys.argv[2]
    start = end = None
    for line in open(logp):
        if line.startswith("RESULT "):
            f = dict(kv.split("=", 1) for kv in line.split()[1:])
            start, end = int(f["start_ms"]), int(f["end_ms"])
            desc = f"{f['kind']}, {f['tsize']} a transaction"
    data = json.loads(subprocess.run(
        ["jfr", "print", "--json", "--stack-depth", "200", "--events",
         "jdk.ExecutionSample,jdk.GarbageCollection", jfr],
        check=True, capture_output=True, text=True).stdout)
    events = data["recording"]["events"]
    total = inexec = incheck = 0
    by_method = collections.Counter()
    by_leaf = collections.Counter()
    gc_ms = 0.0
    for e in events:
        v = e["values"]
        t = ms(v["startTime"])
        if t < start or t > end:
            continue
        if e["type"] == "jdk.GarbageCollection":
            d = v["duration"]   # e.g. "PT0.0123S"
            gc_ms += float(re.match(r"PT([\d.]+)S", d).group(1)) * 1000 if d.startswith("PT") else 0
            continue
        th = v.get("sampledThread") or {}
        if th.get("javaName") != "main":
            continue
        total += 1
        frames = v["stackTrace"]["frames"]
        names = [f["method"]["type"]["name"].replace("/", ".") + "." + f["method"]["name"] for f in frames]
        if not any(n.endswith("bergdb.core.Db.execute") for n in names):
            continue
        inexec += 1
        tc = [n for n in names if "bergdb.core.TransCheck" in n]
        if tc:
            incheck += 1
            by_method[tc[0].replace("bergdb.core.", "")] += 1
            by_leaf[names[0].rsplit(".", 1)[0]] += 1
    print(f"{desc}: phase {(end - start) / 1000:.1f} s, {total} samples of main, {inexec} in "
          f"Db.execute, {incheck} in TransCheck: {100 * incheck / max(1, inexec):.0f} % of "
          f"execute's samples; GC pauses in the phase {gc_ms:.0f} ms")
    print("TransCheck's samples by its innermost TransCheck method:")
    for m, c in by_method.most_common(12):
        print(f"  {100 * c / max(1, incheck):5.1f} %  {m}")
    print("and by the class of the frame at the top of the stack:")
    for m, c in by_leaf.most_common(12):
        print(f"  {100 * c / max(1, incheck):5.1f} %  {m}")


main()
