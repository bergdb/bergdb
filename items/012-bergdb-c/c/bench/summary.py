"""The tables of bergdb 012-15 from bench.sh's outputs.

Usage: python3 -I bench/summary.py OUT

Reads OUT/NN-NAME-LANG.txt (bench.sh's runs) and prints, per workload
(NAME) and phase, C's and Java's medians over the runs, with the range and
the run count, and C's value against Java's. A run's figure for a phase with
rounds (get, hist, many, lowget, get4t) is its best round, as Props takes
the best of its rounds (006-02). Rates are operations a second; times
(create, close, lowopen, start) are seconds. Then the bytes appended per
put, the memory and the maximum resident sets.
"""
import glob
import os
import re
import statistics
import sys

ROUNDED = {"get", "hist", "many", "lowget", "get4t"}
TIMES = {"create", "close", "lowopen", "start"}


def parse(path):
    r = {"phases": {}, "mem": {}, "extra": {}}
    for line in open(path, errors="replace"):
        if line.startswith("RESULT "):
            kv = dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)
            ph = kv["phase"]
            val = float(kv["sec"]) if ph in TIMES else float(kv["per_sec"])
            if ph in ROUNDED:
                old = r["phases"].get(ph)
                r["phases"][ph] = val if old is None else max(old, val)
            else:
                r["phases"][ph] = val
            r["extra"][ph] = kv
        elif line.startswith("MEM "):
            kv = dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)
            r["mem"][kv["at"]] = kv
        elif "maximum resident set size" in line:
            r["maxrss"] = int(line.split()[0])
        elif line.strip().endswith(" real") or " real " in line:
            m = re.match(r"\s*([0-9.]+) real", line)
            if m:
                r["real"] = float(m.group(1))
    return r


def med(xs):
    return statistics.median(xs) if xs else None


def fmt(x, time=False):
    if x is None:
        return "-"
    if time:
        return "%.3f s" % x if x < 10 else "%.1f s" % x
    if x >= 100:
        return "{:,.0f}".format(x)
    return "%.1f" % x


def main(out):
    runs = {}
    for f in sorted(glob.glob(os.path.join(out, "[0-9][0-9]-*.txt"))):
        m = re.match(r"\d\d-(.*)-(c|java)\.txt$", os.path.basename(f))
        if not m:
            continue
        name, lang = m.group(1), m.group(2)
        if name.endswith("-warmup"):
            continue
        runs.setdefault(name, {}).setdefault(lang, []).append(parse(f))
    for name, by in runs.items():
        print("## %s (runs: C %d, Java %d)" % (name, len(by.get("c", [])), len(by.get("java", []))))
        print()
        print("| Phase | C | Java | C/Java | C range | Java range |")
        print("|---|---:|---:|---:|---|---|")
        phases = []
        for lang in ("c", "java"):
            for r in by.get(lang, []):
                for p in r["phases"]:
                    if p not in phases:
                        phases.append(p)
        for p in phases:
            t = p in TIMES
            cs = [r["phases"][p] for r in by.get("c", []) if p in r["phases"]]
            js = [r["phases"][p] for r in by.get("java", []) if p in r["phases"]]
            c, j = med(cs), med(js)
            ratio = "%.2f" % (c / j) if c and j else "-"
            rng = lambda xs: "%s to %s" % (fmt(min(xs), t), fmt(max(xs), t)) if xs else "-"
            print("| %s | %s | %s | %s | %s | %s |" % (p, fmt(c, t), fmt(j, t), ratio, rng(cs), rng(js)))
        print()
        # bytes appended per put, and the stream (equal by construction)
        for p in ("load", "batch", "single", "syncone", "syncbatch"):
            vals = set()
            for lang in ("c", "java"):
                for r in by.get(lang, []):
                    x = r["extra"].get(p)
                    if x and "bytes_per_put" in x:
                        vals.add((lang, x["bytes_per_put"], x.get("stream")))
            if vals:
                print("bytes per put, %s: %s" % (p, sorted(vals)))
        # memory
        for lang in ("c", "java"):
            for i, r in enumerate(by.get(lang, [])):
                ms = r["mem"]
                if lang == "c" and "load" in ms and "empty" in ms:
                    keys = int(ms["load"]["keys"])
                    live = int(ms["load"]["live"]) - int(ms["empty"]["live"])
                    print("C run %d: allocator bytes a key after the load %.1f (index %.1f, value %.1f, handle %.1f, "
                          "table %.1f, state %.1f), resident (bergdb_stats) %.1f, rss (all of the process) %.1f; after the writes: live %.1f, "
                          "rss %.1f; maxrss %s" % (
                              i, live / keys,
                              int(ms["load"]["index"]) / keys, int(ms["load"]["value"]) / keys,
                              int(ms["load"]["handle"]) / keys, int(ms["load"]["table"]) / keys,
                              int(ms["load"]["state"]) / keys, int(ms["load"]["resident"]) / keys,
                              int(ms["load"]["rss"]) / keys,
                              (int(ms["writes"]["live"]) - int(ms["empty"]["live"])) / keys if "writes" in ms else -1,
                              int(ms["writes"]["rss"]) / keys if "writes" in ms else -1,
                              r.get("maxrss")))
                    for at in ("lowopen", "lowget", "start"):
                        if at in ms:
                            print("C run %d at %s: live %s resident %s pinned %s evicted %s peak %s rss %s" % (
                                i, at, ms[at]["live"], ms[at]["resident"], ms[at]["pinned"], ms[at]["evicted"],
                                ms[at]["peak"], ms[at]["rss"]))
                if lang == "java":
                    parts = []
                    for at in ("load", "writes", "lowopen", "lowget", "start"):
                        if at in ms:
                            parts.append("%s %s (heap %s)" % (at, ms[at]["per_key"], ms[at]["heap"]))
                    print("Java run %d: heap bytes a key: %s; maxrss %s" % (i, ", ".join(parts), r.get("maxrss")))
                if lang == "c" and "start" in r["extra"]:
                    print("C run %d start: %s" % (i, r["extra"]["start"]))
                if lang == "java" and "start" in r["extra"]:
                    print("Java run %d start: %s" % (i, r["extra"]["start"]))
        print()


if __name__ == "__main__":
    main(sys.argv[1])
