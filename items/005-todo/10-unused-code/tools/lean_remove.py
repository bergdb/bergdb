"""Removes Lean declarations by the ranges that lake build recorded (005-10).

Usage: python3 -I lean_remove.py <repo> <names.txt>

names.txt: one declaration per line, "name<TAB>module". The range of each
is read from lean/.lake/build/lib/lean/<module>.ilean (so lake build must be
up to date); the lines go, with a doc comment directly above and one blank
line when the declaration stood between two.
"""

import json
import os
import sys
from collections import defaultdict

repo, names_path = sys.argv[1], sys.argv[2]
build = os.path.join(repo, "lean", ".lake", "build", "lib", "lean")

by_mod = defaultdict(list)
for line in open(names_path, encoding="utf-8"):
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    name, mod = line.split("\t")
    by_mod[mod].append(name)

for mod, names in sorted(by_mod.items()):
    il = json.load(open(os.path.join(build, *mod.split(".")) + ".ilean", encoding="utf-8"))
    path = os.path.join(repo, "lean", *mod.split(".")) + ".lean"
    lines = open(path, encoding="utf-8", newline="").read().split("\n")
    spans = []
    for n in names:
        r = il["decls"][n]
        a, b = r[0], r[2]          # 0-based first and last line
        assert lines[a][:r[1]].strip() == "", (n, "does not start a line")
        assert lines[b][r[3]:].strip() == "", (n, "does not end a line")
        if a > 0 and lines[a - 1].rstrip().endswith("-/"):
            c = a - 1
            while c >= 0 and "/-" not in lines[c]:
                c -= 1
            if c >= 0 and lines[c].lstrip().startswith("/--"):
                a = c
        if a > 0 and lines[a - 1].strip() == "" and b + 1 < len(lines) and lines[b + 1].strip() == "":
            b += 1
        spans.append((a, b, n))
    for a, b, n in sorted(spans, reverse=True):
        del lines[a:b + 1]
    open(path, "w", encoding="utf-8", newline="").write("\n".join(lines))
    print("%s: %d removed" % (mod, len(names)))
