"""Who uses a class: the other top-level classes whose source refers to it.

Usage: python3 -I users.py <c dir> <idx dir> [category]

For each top-level class in the category (default: classes in java/src that
the public API does not reach), prints the top-level classes outside
itself that refer to it in the source, ignoring the test packs' lists and
imports, and whether those referrers are used in the 'all' configuration.
"""

import csv
import os
import sys
from collections import defaultdict

cdir, idxdir = sys.argv[1], sys.argv[2]
cat = sys.argv[3] if len(sys.argv) > 3 else "src-test-only"

rows = {int(r["id"]): r for r in csv.DictReader(open(os.path.join(cdir, "decls-status.tsv")), delimiter="\t")}
enc = {}
for line in open(os.path.join(idxdir, "decls.tsv"), encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    enc[int(f[0])] = int(f[12])


def top(i):
    while enc.get(i, -1) >= 0:
        i = enc[i]
    return i


users = defaultdict(set)
for line in open(os.path.join(idxdir, "refs.tsv")):
    a, b = (int(x) for x in line.split())
    if a < 0:
        continue
    ta, tb = top(a), top(b)
    if ta != tb:
        users[tb].add(ta)


def name(i):
    return rows[i]["class"].split("$")[0]


def selected(r):
    if "$" in r["class"] or r["kind"] not in ("CLASS", "INTERFACE", "ENUM", "ANNOTATION_TYPE"):
        return False
    if cat == "src-test-only":
        return r["file"].startswith("java/src/") and r["api"] == "1" and r["run"] == "0"
    if cat == "tools":
        return r["run"] == "1" and r["all"] == "0"
    if cat == "dead":
        return r["all"] == "1"
    return r["file"].startswith(cat)


for i, r in sorted(rows.items(), key=lambda x: x[1]["class"]):
    if not selected(r):
        continue
    us = sorted({name(u) for u in users[i]
                 if not name(u).endswith(".Pack") and not name(u).endswith(".PackForPub")})
    live = [u for u in us]
    print("%s\t%s" % (r["class"], ", ".join(u.replace("bergdb.", "") for u in live) or "-"))
