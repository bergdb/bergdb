"""Aggregates CstChecks' output (031-07 probe): outcome lines mapped to the check that
refused, by region. Usage: python3 -I tally.py FILE [FILE2]."""
import re
import sys

RULES = [
    ("UNDETECTED", "UNDETECTED (wrong values)"),
    ("MORE THAN THE REAL", "STALE RECORDS TAKEN"),
    ("THREW", "THREW"),
    ("TIMEOUT", "TIMEOUT"),
    ("known 019-31", "known 019-31 (undetected)"),
    ("known 019-30", "known 019-30 (undetected)"),
    ("known 015-73", "known 015-73 (undetected)"),
    ("014-01", "014-01: zero fill > 1 MB"),
    ("holds all", "holds all (harmless)"),
    ("holds a prefix", "holds a prefix (as a cut)"),
    ("StreamChecksumException", "node CRC"),
    ("BadMagicBytes", "meta magic"),
    ("Cannot read meta block with version", "meta version"),
    ("Meta block, bad", "meta fields (checkFormat)"),
    ("names the last transaction at", "meta lastTrans range"),
    ("maximum node size", "meta node size"),
    ("Could not find *any* valid meta block", "no valid meta block"),
    ("DatabaseNotCreatedException", "incomplete creation"),
    ("Bad transaction size in db stream", "recovery walk: size"),
    ("Bad transaction byte", "recovery walk: size"),
    ("Bad transaction size, N, transPos", "record size (walk)"),
    ("Bad item byte size", "size beyond the stream"),
    ("EOFException", "read beyond the stream"),
    ("Bad lastByte", "record last byte"),
    ("is not committed", "record last byte"),
    ("Cannot parse stored transaction", "record format byte"),
    ("Bad transaction size in header", "record parse"),
    ("Missing node end marker", "record parse"),
    ("gotDirtyCount", "record parse"),
    ("No room for", "record parse"),
    ("by its content", "record parse (015-72)"),
    ("Bad node size, N, at offset", "record parse: node size"),
    ("has startupPos", "startupPos check"),
    ("topPos", "topPos check"),
    ("names no top node", "topPos check"),
    ("super root", "super root"),
    ("No super root", "super root"),
    ("non-increasing", "section order"),
    ("Time not increasing", "section order"),
    ("Transaction time out of range", "section order"),
    ("The got-dirty entry", "got-dirty check"),
    ("got dirty in trans", "got-dirty check"),
    ("out of key order", "rerun key order"),
    ("Unexpected stream pointer", "stream pointers"),
    ("startup distance", "sd KV"),
    ("InternalDataException", "sd KV"),
    ("Cannot parse key node", "node format byte"),
    ("Cannot parse top node", "node format byte"),
    ("Cannot parse value node", "node format byte"),
    ("unknown node type", "node type"),
    ("Bad node type", "node type"),
    ("Bad node byte size", "node size"),
    ("less than a node's header", "node size"),
    ("Bad node position", "node position"),
    ("names a node of type", "pointee type"),
    ("Two nodes with the id", "pointee id"),
    ("Pointer to node", "pointee id"),
    ("Bad pointer N, index", "pointer value"),
    ("Bad value pointer", "pointer value"),
    ("TopNode at", "top node parse"),
    ("Time too", "top node parse"),
    ("Invalid root pointer", "top node parse"),
    ("Bad value", "value node parse"),
    ("Bad key size when reading value node", "value node parse"),
    ("Bad key of value node", "value node parse"),
    ("Bad flags", "value node parse"),
    ("Bad offset from transaction", "value node parse"),
    ("Bad key node size", "key node parse"),
    ("Bad second byte", "key node parse"),
    ("Bad key count", "key node parse"),
    ("Bad KeyNode", "key node parse"),
    ("Bad Node size", "key node parse"),
    ("Bad size:", "key node parse"),
    ("Bad klong type", "key node parse"),
    ("Bad time klong", "key node parse"),
    ("Bad pointer, N, of klong", "key node parse"),
    ("has no live klong", "key node invariant"),
]


def label(line):
    for pat, lab in RULES:
        if pat in line:
            where = "read failed: " if line.startswith("read failed") else ""
            fill = " (after a fill)" if "after a fill" in line else ""
            return where + lab + fill
    return "OTHER: " + line[:60]


def parse(path):
    regions = {}
    cur = None
    for raw in open(path, encoding="utf-8", errors="replace"):
        line = raw.rstrip("\n")
        if line.startswith("== "):
            continue
        m = re.match(r"^(\S.*)  \((\d+)\)$", line)
        if m and not line.startswith(" "):
            cur = m.group(1)
            regions[cur] = {}
            continue
        m = re.match(r"^    (\d+)\t(.*)$", line)
        if m and cur is not None:
            lab = label(m.group(2))
            regions[cur][lab] = regions[cur].get(lab, 0) + int(m.group(1))
    return regions


def group(region):
    r = region
    r = re.sub(r"node (top|key|value|delete): body", r"node \1: body", r)
    return r


def show(path):
    regions = parse(path)
    groups = {}
    for reg, labs in regions.items():
        g = group(reg)
        d = groups.setdefault(g, {})
        for k, v in labs.items():
            d[k] = d.get(k, 0) + v
    total = {}
    for g in sorted(groups):
        d = groups[g]
        n = sum(d.values())
        parts = sorted(d.items(), key=lambda kv: -kv[1])
        print(f"{g} ({n}): " + "; ".join(f"{k} {v}" for k, v in parts))
        for k, v in d.items():
            total[k] = total.get(k, 0) + v
    print("TOTAL " + str(sum(total.values())))
    for k, v in sorted(total.items(), key=lambda kv: -kv[1]):
        print(f"  {v}\t{k}")


for p in sys.argv[1:]:
    print("#### " + p)
    show(p)
    print()
