#!/usr/bin/env python3
"""Sums the RESULT lines of `petrial` runs (bergdb 026-24) by set and mode, and
gives PE's counts against today's on the same traces.

Usage: agg.py [--by-trace] [--by-config] RUNSDIR [SET...]   (RUNSDIR/SET/MODE/*.txt)

Bytes are 026-17's stand-ins (as 026-21): B-new = record + values + deletes +
top nodes + the key nodes made; B-all = the same with every key node changed;
"index" leaves out the values and the deletes, which no writer changes.
Paired: PE against today's writer run from PE's tree before each
transaction (pe mode's --paired), so both start every transaction from the
same tree.
"""
import os, sys, collections

MAPS = {"shapeend", "fails", "reached", "cmp"}
TEXT = {"trace", "mode"}

def parse(line):
    d = {}
    for tok in line.split()[1:]:
        if "=" not in tok:
            continue
        k, v = tok.split("=", 1)
        if k in MAPS:
            m = {}
            for kv in v.split(","):
                if ":" in kv:
                    a, b = kv.rsplit(":", 1)
                    m[a] = int(b)
            d[k] = m
        elif k in TEXT:
            d[k] = v
        else:
            try:
                d[k] = int(v)
            except ValueError:
                d[k] = v
    return d

def load(runs, sets):
    rows = []
    for s in sets:
        sd = os.path.join(runs, s)
        if not os.path.isdir(sd):
            continue
        for mode in sorted(os.listdir(sd)):
            md = os.path.join(sd, mode)
            for f in sorted(os.listdir(md)):
                ok = False
                res = None
                for line in open(os.path.join(md, f)):
                    if line.startswith("RESULT"):
                        res = parse(line)
                    if line.startswith("PETRIAL"):
                        ok = True
                if res is not None:
                    res["set"] = s
                    res["complete"] = ok
                    rows.append(res)
    return rows

def add(a, d):
    for k, v in d.items():
        if isinstance(v, int):
            a[k] = a.get(k, 0) + v
        elif isinstance(v, dict):
            m = a.setdefault(k, collections.Counter())
            m.update(v)
    a["traces"] = a.get("traces", 0) + 1
    a["height_max"] = max(a.get("height_max", 0), d.get("height", 0))
    a["incomplete"] = a.get("incomplete", 0) + (0 if d.get("complete") else 1)

def tnew(a): return a["brec"] + a["bval"] + a["bdel"] + a["btop"] + a["bnew"]
def tall(a): return a["brec"] + a["bval"] + a["bdel"] + a["btop"] + a["ball"]
def inew(a): return a["brec"] + a["btop"] + a["bnew"]
def iall(a): return a["brec"] + a["btop"] + a["ball"]
def ptnew(a): return a["prec"] + a["bval"] + a["bdel"] + a["ptop"] + a["pnew"]
def ptall(a): return a["prec"] + a["bval"] + a["bdel"] + a["ptop"] + a["pall"]

def r(x, y):
    return "-" if not y else "%.3f" % (x / y)

def fill(a):
    return (a["slive"] / a["snodes"]) if a.get("snodes") else 0.0

def report(title, groups):
    print("== " + title)
    for key in sorted(groups):
        g = groups[key]
        if "pe" not in g or "today" not in g:
            print(f"{key}: modes {sorted(g)}")
            continue
        p, t = g["pe"], g["today"]
        print(f"{key}: traces {p['traces']}/{t['traces']} (incomplete {p['incomplete']}/{t['incomplete']}), "
              f"txs {p['txs']}, ops {p['ops']}, dels {p['dels']}, tx1 {p['tx1']}")
        print(f"  fails pe {dict(p.get('fails', {}))} today {dict(t.get('fails', {}))}")
        print(f"  shape pe {dict(p.get('shapeend', {}))} today {dict(t.get('shapeend', {}))}")
        print(f"  B-new {r(tnew(p), tnew(t))}  B-all {r(tall(p), tall(t))}  "
              f"index B-new {r(inew(p), inew(t))}  index B-all {r(iall(p), iall(t))}")
        print(f"  key nodes made {r(p['madekey'], t['madekey'])}  key klongs {r(p['klongs'], t['klongs'])}  "
              f"top nodes {r(p['tops'], t['tops'])}  versions {r(p['versions'], t['versions'])}")
        print(f"  fill (live klongs a node, sampled) pe {fill(p):.2f} today {fill(t):.2f}; "
              f"end nodes {p['endnodes']} / {t['endnodes']}; dead a node {r(p['sdead'], p['snodes'])} / "
              f"{r(t['sdead'], t['snodes'])}; height max {p['height_max']} / {t['height_max']}")
        if p.get("ptxs"):
            print(f"  paired (today from PE's tree, {p['ptxs']} txs): B-new {r(tnew(p), ptnew(p))}  "
                  f"B-all {r(tall(p), ptall(p))}  index B-new {r(inew(p), p['prec'] + p['ptop'] + p['pnew'])}  "
                  f"index B-all {r(iall(p), p['prec'] + p['ptop'] + p['pall'])}  "
                  f"key nodes made {r(p['madekey'], p['pmadekey'])}  key klongs {r(p['klongs'], p['pklongs'])}")
        c = p.get("cmp", {})
        if c:
            kinds = ["exact", "lists", "other.samenodes", "other.othernodes"]
            print("  cmp1: " + ", ".join(f"{k} {c.get(k, 0)} (put {c.get(k + '.put', 0)}, del {c.get(k + '.del', 0)})"
                                          for k in kinds))
            for k in kinds[1:]:
                if c.get(k):
                    print(f"    {k}: key klongs pe {c.get(k + '.kpe', 0)} today {c.get(k + '.ktoday', 0)}; "
                          f"B-all key bytes pe {c.get(k + '.bpe', 0)} today {c.get(k + '.btoday', 0)}")
        if "pet" in g:
            q = g["pet"]
            c = q.get("cmp", {})
            kinds = ["exact", "lists", "other.samenodes", "other.othernodes"]
            print(f"  pet (today's cut emulated) fails {dict(q.get('fails', {}))} shape {dict(q.get('shapeend', {}))}")
            print("  cmp1 of pet: " + ", ".join(f"{k} {c.get(k, 0)} (put {c.get(k + '.put', 0)}, del {c.get(k + '.del', 0)})"
                                                for k in kinds))
            for k in kinds[1:]:
                if c.get(k):
                    print(f"    {k}: key klongs pet {c.get(k + '.kpe', 0)} today {c.get(k + '.ktoday', 0)}; "
                          f"B-all key bytes pet {c.get(k + '.bpe', 0)} today {c.get(k + '.btoday', 0)}")
        pr = {k: v for k, v in p.get("reached", {}).items() if k.startswith("pe.")}
        print(f"  pe decisions {dict(sorted(pr.items()))}")

def main():
    args = sys.argv[1:]
    by_trace = "--by-trace" in args
    by_config = "--by-config" in args
    args = [a for a in args if not a.startswith("--")]
    runs = args[0]
    sets = args[1:] or sorted(os.listdir(runs))
    rows = load(runs, sets)
    # only traces run to the end in both pe and today (pet apart)
    done = collections.defaultdict(set)
    for d in rows:
        if d.get("complete"):
            done[(d["set"], d["trace"])].add(d["mode"])
    both = {k for k, v in done.items() if "pe" in v and "today" in v}
    left = sorted(k for k in done if k not in both)
    rows = [d for d in rows if (d["set"], d["trace"]) in both and d.get("complete")]
    print(f"traces in both pe and today: {len(both)}; left out: {len(left)}")
    def group(keyf):
        g = collections.defaultdict(dict)
        for d in rows:
            a = g[keyf(d)].setdefault(d["mode"], {})
            add(a, d)
        return g
    report("by set", group(lambda d: d["set"]))
    report("by node size", group(lambda d: "M=%d" % d.get("M", 0)))
    report("all", group(lambda d: "all"))
    if by_config:
        def cfg(d):
            n = d["trace"].rsplit(".", 1)[0]
            base = n.rstrip("0123456789").rstrip("-")
            return d["set"] + ":" + base
        report("by workload", group(cfg))
    if by_trace:
        report("by trace", group(lambda d: d["set"] + ":" + d["trace"]))

main()
