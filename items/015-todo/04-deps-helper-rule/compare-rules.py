#!/usr/bin/env python3
"""bergdb 015-04: lists the declarations of java/src that deps.py's helper rule counted
as test code before 015-04's fix and counts as production code after it.

Usage: python3 -I compare-rules.py JAVA_SRC
  In a directory with deps_on.py, java/deps.py before the fix
  (git show 015-04's-commit^:java/deps.py), and deps_x.py, java/deps.py after it.
Written 2026-11-05.
"""
import os, re, sys
sys.path.insert(0, '.')
import deps_on as A, deps_x as B
src = sys.argv[1]
files = {}
for d, _, fs in os.walk(os.path.join(src, "bergdb")):
    for f in fs:
        if f.endswith(".java"):
            p = os.path.join(d, f); files[p] = A.strip(open(p, encoding="utf-8").read())
words, counts = {}, {}
for p, c in files.items():
    words[p] = B.production_words(c, os.path.basename(p))
    for w in words[p]: counts[w] = counts.get(w, 0) + 1
decl = re.compile(r"(?:class\s+(\w+)|(\w+)\s*\([^;{}]*\)[^;{}]*\{)")
tot_old = tot_new = 0
rows = []
for p, code in sorted(files.items()):
    f = os.path.basename(p)
    base = A.test_regions(code, f, False)
    old = [r for r in A.test_regions(code, f) if r not in base]
    own = words[p]
    new = [r for r in B.test_regions(code, f, True, lambda w: counts.get(w, 0) > (w in own)) if r not in base]
    tot_old += len(old); tot_new += len(new)
    for r in old:
        if r not in new:
            m = decl.search(code, r[0], r[1])
            rows.append((os.path.relpath(p, src)[7:-5].replace('/', '.'), m.group(1) or m.group(2)))
print("helper regions: old %d, new %d, moved to production %d" % (tot_old, tot_new, len(rows)))
for c, n in rows: print("%s.%s" % (c, n))
