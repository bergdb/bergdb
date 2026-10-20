"""Exact text replacements, each of which must match exactly once.

Usage: python3 -I edit.py <repo> <edits.py>; the edits file defines
EDITS = [(path, old, new), ...].
"""
import sys

repo, spec = sys.argv[1], sys.argv[2]
ns = {}
exec(open(spec).read(), ns)
for path, old, new in ns["EDITS"]:
    p = repo + "/" + path
    text = open(p, encoding="utf-8", newline="").read()
    n = text.count(old)
    if n != 1:
        sys.exit("%s: %d matches for %r" % (path, n, old[:60]))
    open(p, "w", encoding="utf-8", newline="").write(text.replace(old, new))
    print("edited", path)
