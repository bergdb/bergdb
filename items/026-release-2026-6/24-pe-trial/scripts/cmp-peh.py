#!/usr/bin/env python3
"""bergdb 026-24, section 2.6: PE with parts of at most M / 2 (mode peh)
against PE (mode pe, parts of at most h) and today, by trace and summed, on
the traces that all three ran to the end.

Usage: cmp-peh.py PEDIR PEHDIR SET...   (PEDIR/SET/{pe,today}/*.txt, PEHDIR/SET/peh/*.txt)
"""
import os, sys

def parse(path):
    txt = open(path).read()
    if "PETRIAL" not in txt:
        return None
    for l in txt.splitlines():
        if l.startswith("RESULT"):
            d = {}
            for tok in l.split()[1:]:
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    try:
                        d[k] = int(v)
                    except ValueError:
                        d[k] = v
            return d
    return None

def tnew(d): return d["brec"] + d["bval"] + d["bdel"] + d["btop"] + d["bnew"]
def tall(d): return d["brec"] + d["bval"] + d["bdel"] + d["btop"] + d["ball"]
def inew(d): return d["brec"] + d["btop"] + d["bnew"]
def iall(d): return d["brec"] + d["btop"] + d["ball"]

pedir, pehdir, sets = sys.argv[1], sys.argv[2], sys.argv[3:]
tot = {m: {} for m in ("today", "pe", "peh")}
for s in sets:
    for f in sorted(os.listdir(os.path.join(pehdir, s, "peh"))):
        r = {"peh": parse(os.path.join(pehdir, s, "peh", f)),
             "pe": parse(os.path.join(pedir, s, "pe", f)),
             "today": parse(os.path.join(pedir, s, "today", f))}
        if any(v is None for v in r.values()):
            continue
        t = r["today"]
        line = f"{s}:{f[:-4]}"
        for m in ("pe", "peh"):
            d = r[m]
            line += (f"  {m}: B-new {tnew(d)/tnew(t):.3f} B-all {tall(d)/tall(t):.3f}"
                     f" index {inew(d)/inew(t):.3f} {iall(d)/iall(t):.3f}"
                     f" fill {d['slive']/max(d['snodes'],1):.2f}")
            if d.get("fails"):
                line += f" FAILS {d['fails']}"
        line += f"  today fill {t['slive']/max(t['snodes'],1):.2f}"
        print(line)
        for m in tot:
            for k in ("brec", "bval", "bdel", "btop", "bnew", "ball", "slive", "snodes"):
                tot[m][k] = tot[m].get(k, 0) + r[m][k]
t = tot["today"]
for m in ("pe", "peh"):
    d = tot[m]
    print(f"ALL {m}: B-new {tnew(d)/tnew(t):.3f} B-all {tall(d)/tall(t):.3f} index {inew(d)/inew(t):.3f}"
          f" {iall(d)/iall(t):.3f} fill {d['slive']/d['snodes']:.2f} (today {t['slive']/t['snodes']:.2f})")
