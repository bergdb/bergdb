#!/usr/bin/env python3
"""Sums the RESULT lines of `steptimes` runs (bergdb 026-21) by set, node size
and mode, and gives each mode's counts against today's on the same traces.

Usage: aggregate.py [--by-trace | --by-config] RUNSDIR [SET...]   (RUNSDIR/SET/MODE/*.txt)
"""
import os, sys, collections

MAPS = {"bumpwhy", "wouldbump", "selfev", "shapeend", "shapemid", "fails", "reached"}
TEXT = {"trace", "mode", "stephist"}

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
        elif k == "stephist":
            d[k] = [int(x) for x in v.split(",")]
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
                    if line.startswith("STEPTIMES"):
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
        elif k == "stephist":
            h = a.setdefault(k, [0] * 5)
            for i, x in enumerate(v):
                h[i] += x
    a["traces"] = a.get("traces", 0) + 1
    a["maxsteps_max"] = max(a.get("maxsteps_max", 0), d.get("maxsteps", 0))
    a["height_max"] = max(a.get("height_max", 0), d.get("height", 0))

def total_new(a):
    return a["brec"] + a["bval"] + a["bdel"] + a["btop"] + a["bnew"]

def total_all(a):
    return a["brec"] + a["bval"] + a["bdel"] + a["btop"] + a["ball"]

def splits(a):
    r = a.get("reached", {})
    t = sum(v for k, v in r.items() if k.startswith("split.time"))
    sp = sum(v for k, v in r.items() if k.startswith("split.space"))
    m = r.get("merge.one", 0) + r.get("merge.two", 0)
    return t, sp, m

def fmt_map(m, n=12):
    return ", ".join(f"{k} {v}" for k, v in sorted(m.items(), key=lambda kv: -kv[1])[:n]) or "none"

def report(rows, key):
    groups = collections.OrderedDict()
    for r in rows:
        g = key(r)
        groups.setdefault(g, {}).setdefault(r["mode"], {})
        add(groups[g][r["mode"]], r)
    out = []
    for g, modes in groups.items():
        out.append(f"== {g}")
        base = modes.get("today")
        for mode in ["today", "split", "b0", "b", "bs", "d"]:
            if mode not in modes:
                continue
            a = modes[mode]
            t, sp, m = splits(a)
            line = (f"  {mode}: traces {a['traces']}, txs {a['txs']}, ops {a['ops']} "
                    f"(dels {a['dels']}), dupkeys {a['dupkeys']}; steps {a['steps']} "
                    f"({a['steps']/max(1,a['txs']):.3f} a tx, most {a['maxsteps_max']}, "
                    f"txs with >1 {a['multitx']} = {100*a['multitx']/max(1,a['txs']):.1f} %, "
                    f"hist {a.get('stephist')}); bumps between ops {a['bumpsbetween']}, "
                    f"inside {a['bumpsinside']}")
            out.append(line)
            out.append(f"    bump reasons: {fmt_map(a.get('bumpwhy', {}))}; would bump (no bump made): "
                       f"{fmt_map(a.get('wouldbump', {}))}")
            out.append(f"    self (an action on its own nodes): {a['selfacts']} actions; "
                       f"{fmt_map(a.get('selfev', {}))}; taken back {a['taken']}")
            fill = (f"klongs/node {a['sklongs']/max(1,a['snodes']):.2f}, live/node "
                    f"{a['slive']/max(1,a['snodes']):.2f}, dead/node {a['sdead']/max(1,a['snodes']):.2f}, "
                    f"time klongs/node {a['stimes']/max(1,a['snodes']):.2f}, nodes/sample "
                    f"{a['snodes']/max(1,a['samples']):.1f}, height max {a['height_max']}")
            out.append(f"    fill (samples {a['samples']}): {fill}")
            out.append(f"    made key nodes {a['madekey']}, tops {a['tops']}, versions {a['versions']}, "
                       f"key klongs added {a['klongs']}, time splits {t}, space splits {sp}, merges {m}")
            out.append(f"    bytes: B-new {total_new(a)}, B-all {total_all(a)} (values {a['bval']}, "
                       f"deletes {a['bdel']}, records {a['brec']}, tops {a['btop']}, made key nodes "
                       f"{a['bnew']}, changed key nodes {a['ball']})")
            if base and mode != "today":
                def ratio(k):
                    return a[k] / base[k] if base.get(k) else float("nan")
                bt, bsp, bm = splits(base)
                out.append(
                    f"    against today: versions {ratio('versions'):.3f}, klongs {ratio('klongs'):.3f}, "
                    f"made key nodes {ratio('madekey'):.3f}, tops {ratio('tops'):.3f}, "
                    f"B-new {total_new(a)/max(1,total_new(base)):.3f}, "
                    f"B-all {total_all(a)/max(1,total_all(base)):.3f}, "
                    f"index B-new {(total_new(a)-a['bval']-a['bdel'])/max(1,total_new(base)-base['bval']-base['bdel']):.3f}, "
                    f"index B-all {(total_all(a)-a['bval']-a['bdel'])/max(1,total_all(base)-base['bval']-base['bdel']):.3f}, "
                    f"time splits {t/max(1,bt):.3f}, space splits {sp/max(1,bsp):.3f}, "
                    f"dead/node {(a['sdead']/max(1,a['snodes']))/max(1e-9,base['sdead']/max(1,base['snodes'])):.3f}")
            out.append(f"    checks: gets {a['gets']}, scans {a['scans']}, Java reads {a['jreads']}, "
                       f"contract steps {a['csteps']}; failures: {fmt_map(a.get('fails', {}))}; "
                       f"writer's rules at tx ends: {fmt_map(a.get('shapeend', {}))}; "
                       f"between: {fmt_map(a.get('shapemid', {}))}")
            inc = sum(1 for r in rows if key(r) == g and r["mode"] == mode and not r["complete"])
            if inc:
                out.append(f"    INCOMPLETE runs: {inc}")
    return "\n".join(out)

def complete_only(rows):
    """Keeps the traces that every mode of their set has run to its end, so
    that each mode's sums are over the same traces as today's."""
    modes = collections.defaultdict(set)
    have = collections.defaultdict(set)
    for r in rows:
        modes[r["set"]].add(r["mode"])
        if r["complete"]:
            have[(r["set"], r["trace"])].add(r["mode"])
    keep = [r for r in rows if have[(r["set"], r["trace"])] == modes[r["set"]]]
    dropped = len({(r["set"], r["trace"]) for r in rows}) - len({(r["set"], r["trace"]) for r in keep})
    return keep, dropped

def main():
    args = sys.argv[1:]
    bytrace = "--by-trace" in args
    byconfig = "--by-config" in args
    args = [a for a in args if a not in ("--by-trace", "--by-config")]
    runs = args[0]
    sets = [s for s in (args[1:] or sorted(os.listdir(runs))) if os.path.isdir(os.path.join(runs, s))]
    rows, dropped = complete_only(load(runs, sets))
    print(f"traces left out (not run to the end in every mode of their set): {dropped}\n")
    if bytrace:
        print(report(rows, lambda r: f"{r['set']}/{r['trace']}"))
        return
    if byconfig:
        print(report(rows, lambda r: f"{r['set']}/{r['trace'].rsplit('-', 1)[0]} M={r['M']}"))
        return
    print("# By set\n")
    print(report(rows, lambda r: r["set"]))
    print("\n# By node size\n")
    print(report(rows, lambda r: f"M={r['M']}"))
    print("\n# All\n")
    print(report(rows, lambda r: "all"))

if __name__ == "__main__":
    main()
