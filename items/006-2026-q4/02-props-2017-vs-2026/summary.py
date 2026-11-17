#!/usr/bin/env python3
"""006-02: tables from the run files in runs/ (see run.sh).

    python3 -I summary.py > summary.txt

Props runs are grouped by label (the set of runs) and version (by commit); per
measure the median, minimum and maximum over the runs. Then the ratios of the
medians that the report uses, the same code on F53 against cissi, and the probe
runs (Probe006: MEM, SS and set at a chosen startup distance).
"""

import os
import re
import statistics

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.join(HERE, "runs")

VERSIONS = {          # commit prefix: name
    "358ad6b": "2015-12-28",
    "b64383a": "2017-07-29",
    "0257e0b": "2017-08-01",
    "0e7292d": "2026-10-19",
}
ORDER_V = ["2015-12-28", "2017-07-29", "2017-08-01", "2026-10-19", "2026-10-19-maphash"]

PARTS = {
    "CORE": ["get", "get4t", "getmany", "set"],
    "SS": ["SS1", "SS2", "SS3", "SS4"],
}
ORDER = ["MEM", "CORE", "get", "get4t", "getmany", "set", "SS", "SS1", "SS2", "SS3", "SS4"]

# Cissi (Intel i7 at 2.1 GHz, 8 GB, Ubuntu): Props.java's "151228" (HotSpot
# 1.7.0_76) and F1-007 bergdb/log.md, 170729 (OpenJDK 1.8.0_131).
CISSI = {
    "2015-12-28": {
        "MEM": 169, "CORE": 0.81, "get": 0.82, "get4t": 0.99, "getmany": 0.87,
        "set": 0.60, "SS": 1.47, "SS1": 1.13, "SS2": 1.22, "SS3": 1.57, "SS4": 2.15,
    },
    "2017-07-29": {
        "MEM": 169, "CORE": 0.76, "get": 0.76, "get4t": 0.94, "getmany": 0.77,
        "set": 0.61, "SS": 1.52, "SS1": 1.15, "SS2": 1.24, "SS3": 1.65, "SS4": 2.27,
    },
}


def parse(path):
    head, body, seconds = {}, [], None
    with open(path) as f:
        lines = f.read().splitlines()
    i = 0
    while i < len(lines) and lines[i] != "----":
        k, _, v = lines[i].partition(": ")
        head[k] = v
        i += 1
    for line in lines[i + 1:]:
        if line.startswith("seconds: "):
            seconds = int(line.split()[1])
        elif line != "----":
            body.append(line)
    text = "\n".join(body)
    values = {}
    m = re.search(r"MEM:(\d+)", text)
    if m:
        values["MEM"] = float(m.group(1))
    for name, parts in PARTS.items():
        m = re.search(name + r":([0-9.]+) \(([^)]*)\)", text)
        if m:
            values[name] = float(m.group(1))
            for p, v in zip(parts, m.group(2).split(",")):
                values[p] = float(v)
    m = re.search(r"set:([0-9.]+) \(best ([0-9.]+) us", text)
    if m:
        values["set"] = float(m.group(1))
        values["set_us"] = float(m.group(2))
    m = re.search(r"startupDistance=(\d+)", text)
    head["distance"] = int(m.group(1)) if m else None
    head["values"] = values
    head["seconds"] = seconds
    head["failed"] = "EXIT CODE" in text or "Exception" in text
    head["file"] = os.path.basename(path)
    head["vname"] = VERSIONS.get(head.get("commit", "")[:7], head.get("version"))
    if head.get("version", "").endswith("-maphash"):
        head["vname"] = head["version"]               # the experiment, same commit
    elif head["vname"] not in VERSIONS.values():
        head["vname"] = head.get("commit", "")[:7]   # another original commit (the sweep)
    head["text"] = text
    return head


def fmt(x, name):
    if x is None:
        return "-"
    if name == "MEM":
        return "%.0f" % x if abs(x - round(x)) < 1e-6 else "%.1f" % x
    if abs(x * 100 - round(x * 100)) > 1e-6:
        return "%.3f" % x        # a median between two values of Props's 0.01 steps
    return "%.2f" % x


def stats(rs, name):
    xs = [r["values"][name] for r in rs if name in r["values"]]
    if not xs:
        return None
    return statistics.median(xs), min(xs), max(xs), len(xs)


def cell(s, name):
    if s is None:
        return "-"
    m, lo, hi, n = s
    if n == 1:
        return fmt(m, name)
    return "%s (%s-%s)" % (fmt(m, name), fmt(lo, name), fmt(hi, name))


def describe(label, groups):
    print("== %s ==" % label)
    print()
    for v, rs in groups.items():
        bad = [r["file"] for r in rs if r["failed"] or not r["values"]]
        idle = [float(r["idle"]) for r in rs if r.get("idle")]
        secs = [r["seconds"] for r in rs if r["seconds"] is not None]
        print("%s: %d runs%s, %s to %s; idle at the start %.1f to %.1f%%; %d to %d s a run; flags: %s" % (
            v, len(rs), (" (FAILED: %s)" % ", ".join(bad)) if bad else "",
            min(r["start"] for r in rs)[11:16], max(r["start"] for r in rs)[11:16],
            min(idle), max(idle), min(secs), max(secs), rs[0]["flags"] or "(none)"))
    print()


def props_table(label, groups, ratios):
    vs = list(groups)
    print("| Measure | " + " | ".join(vs) + "".join(" | %s / %s" % (b, a) for a, b in ratios) + " |")
    print("|---|" + "---|" * (len(vs) + len(ratios)))
    for name in ORDER:
        st = {v: stats(groups[v], name) for v in vs}
        row = [cell(st[v], name) for v in vs]
        for a, b in ratios:
            if st.get(a) and st.get(b):
                row.append("%.3f" % (st[b][0] / st[a][0]))
            else:
                row.append("-")
        print("| %s | %s |" % (name, " | ".join(row)))
    print()


def cissi_table(groups):
    vs = [v for v in groups if v in CISSI]
    if not vs:
        return
    head = []
    for v in vs:
        head += ["cissi, %s code" % v, "F53, same code", "F53 / cissi"]
    print("| Measure | " + " | ".join(head) + " |")
    print("|---|" + "---|" * len(head))
    for name in ORDER:
        row = []
        for v in vs:
            s = stats(groups[v], name)
            ref = CISSI[v][name]
            row += [fmt(ref, name), cell(s, name), "%.2f" % (s[0] / ref) if s else "-"]
        print("| %s | %s |" % (name, " | ".join(row)))
    print()


def per_run(groups):
    print("Per run:")
    for v, rs in groups.items():
        for r in rs:
            vals = r["values"]
            print("  %s: MEM %s, CORE %s (%s), SS %s (%s), %s s, idle %s%%" % (
                r["file"], fmt(vals.get("MEM"), "MEM"), fmt(vals.get("CORE"), "CORE"),
                ", ".join(fmt(vals.get(p), p) for p in PARTS["CORE"]),
                fmt(vals.get("SS"), "SS"),
                ", ".join(fmt(vals.get(p), p) for p in PARTS["SS"]),
                r["seconds"], r.get("idle")))
    print()


def main():
    runs = [parse(os.path.join(RUNS, f)) for f in sorted(os.listdir(RUNS))
            if f.endswith(".txt") and f != "machine.txt"]
    runs = [r for r in runs if r["seconds"] is not None]   # not a run in progress
    props =[r for r in runs if r.get("class", "").startswith("bergdb.dev.props.Props")]
    probes = [r for r in runs if r.get("class", "").startswith("Probe006")]

    labels = []
    for r in props:
        if r["label"] not in labels:
            labels.append(r["label"])
    for label in labels:
        groups = {}
        others = []
        for r in props:
            if r["label"] == label and r["vname"] not in ORDER_V and r["vname"] not in others:
                others.append(r["vname"])
        for v in ORDER_V + others:
            rs = [r for r in props if r["label"] == label and r["vname"] == v]
            if rs:
                groups[v] = rs
        describe(label, groups)
        ratios = []
        if "2017-08-01" in groups and "2026-10-19" in groups:
            ratios.append(("2017-08-01", "2026-10-19"))
        if "2017-07-29" in groups and "2017-08-01" in groups:
            ratios.append(("2017-07-29", "2017-08-01"))
        if "2026-10-19" in groups and "2026-10-19-maphash" in groups:
            ratios.append(("2026-10-19", "2026-10-19-maphash"))
        props_table(label, groups, ratios)
        cissi_table(groups)
        per_run(groups)

    if probes:
        print("== Probe006 ==")
        print()
        print("| Version | Mode | Startup distance | Runs | Result (median, min-max) |")
        print("|---|---|---|---|---|")
        keys = []
        for r in probes:
            mode = r["class"].split()[1] if len(r["class"].split()) > 1 else "?"
            k = (r["vname"], mode, r["distance"], r["flags"])
            if k not in keys:
                keys.append(k)
        for k in sorted(keys, key=lambda k: (k[1], ORDER_V.index(k[0]) if k[0] in ORDER_V else 9, k[2] or 0)):
            v, mode, dist, flags = k
            rs = [r for r in probes if r["vname"] == v and r["class"].split()[1] == mode
                  and r["distance"] == dist and r["flags"] == flags]
            if mode == "ss":
                res = "; ".join(re.search(r"SS:[^\n]*\)", r["text"]).group(0) for r in rs)
            elif mode == "mem":
                res = cell(stats(rs, "MEM"), "MEM")
            elif mode == "histo":
                res = "; ".join(re.search(r"HISTO: ([0-9.]+) bytes per KV", r["text"]).group(1)
                                + " bytes per KV" for r in rs)
            elif mode == "set":
                res = "%s; best %s us" % (cell(stats(rs, "set"), "set"),
                                          cell(stats(rs, "set_us"), "set_us"))
            else:
                res = "?"
            print("| %s | %s | %s MB | %d | %s |" % (v, mode, "%g" % (dist / 1e6) if dist else "?",
                                                    len(rs), res))
        print()
        for r in probes:
            if r["failed"]:
                print("FAILED: %s" % r["file"])


if __name__ == "__main__":
    main()
