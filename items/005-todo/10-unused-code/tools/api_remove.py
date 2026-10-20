"""Selects public API members to remove, for remove.py (005-10, G1).

Usage: python3 -I api_remove.py <repo> <decls.tsv> <api-remove.txt> <out.tsv>

api-remove.txt: one member a line, "class<TAB>key" as in the tables
(bergdb.pub.Duration<TAB>days(double)). The public API is an entry point,
so the analysis never calls these unused; this writes them, with their
positions from the index, in members.tsv's form, for remove.py. Fails if
one is not found.
"""

import os
import sys

repo, decls_path, names_path, outpath = sys.argv[1:5]
repo = os.path.realpath(repo)

wanted = []
for line in open(names_path, encoding="utf-8"):
    line = line.rstrip("\n")
    if line and not line.startswith("#"):
        cls, key = line.split("\t")
        wanted.append((cls, key))

found = {}
for line in open(decls_path, encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    k = (f[2], f[3])
    if k in wanted:
        found[k] = (f[0], f[1], os.path.relpath(os.path.realpath(f[4]), repo), f[5], f[6])

missing = [k for k in wanted if k not in found]
if missing:
    sys.exit("not found: %s" % missing)

with open(outpath, "w") as w:
    w.write("action\tid\tkind\tclass\tkey\tfile\tl1\tl2\n")
    for k in wanted:
        i, kind, f, l1, l2 = found[k]
        w.write("\t".join(["remove", i, kind, k[0], k[1], f, l1, l2]) + "\n")
print("%d API members" % len(wanted))
