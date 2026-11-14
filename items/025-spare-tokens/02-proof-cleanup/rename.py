#!/usr/bin/env python3
"""025-02 tool (2026-11-14): renames declarations and files in lean/, by a table.

Usage, from the clone's lean/ directory:
  python3 rename.py TABLE [--apply] [--join]
TABLE lines (tab or space separated; # comments):
  old new                     a declaration: every whole identifier `old`, also inside a
                              dotted name (SIS.Tree.old, KNode.old when old is KNode.old)
  FILE SIS/Tree/A.lean SIS/Tree/B.lean
                              a file: git mv, and every `import SIS.Tree.A` becomes B
Checks before it changes anything: an old name is a whole identifier somewhere; a new name
is not one already (no clash with any identifier in lean/); no two rows share a new name.
--join (step 4, duplicates): a new name may exist already (the copy kept).
Without --apply it prints what it would change (files and counts). macOS sed has no \\b, so
this is Python (bergdb memory: lean-no-mathlib-gotchas).
"""
import os, re, subprocess, sys

table, apply_, join = sys.argv[1], "--apply" in sys.argv, "--join" in sys.argv
rows, files = [], []
for l in open(table):
    l = l.split("#", 1)[0].strip()
    if not l:
        continue
    p = l.split()
    if p[0] == "FILE":
        files.append((p[1], p[2]))
    else:
        rows.append((p[0], p[1]))

paths = [os.path.join(dp, f) for dp, _, fs in os.walk(".") if ".lake" not in dp
         for f in fs if f.endswith(".lean")] + ["README.md"]
text = {p: open(p).read() for p in paths if os.path.exists(p)}
IDC = r"A-Za-z0-9_'!?₀-₉"
def rx(name):
    return re.compile(r"(?<![" + IDC + r"])" + re.escape(name) + r"(?![" + IDC + r"])")

errors = []
news = [n for _, n in rows]
if len(set(news)) != len(news) and not join:
    errors.append("two rows share a new name")
for old, new in rows:
    if not any(rx(old).search(t) for t in text.values()):
        errors.append(f"{old}: not found")
    if not join and any(rx(new).search(t) for t in text.values()):
        errors.append(f"{new}: already an identifier in lean/ (a clash)")
for a, b in files:
    if not os.path.exists(a):
        errors.append(f"FILE {a}: missing")
    if os.path.exists(b):
        errors.append(f"FILE {b}: exists")
if errors:
    print("REFUSED:\n  " + "\n  ".join(errors))
    sys.exit(1)

changed = {}
for p, t in text.items():
    t2 = t
    for old, new in rows:
        t2 = rx(old).sub(new, t2)
    for a, b in files:
        ma, mb = a[:-5].replace("/", "."), b[:-5].replace("/", ".")
        t2 = re.sub(r"(?m)^import " + re.escape(ma) + r"\s*$", "import " + mb, t2)
    if t2 != t:
        changed[p] = t2
print(f"{len(rows)} names, {len(files)} files; {len(changed)} files change")
if apply_:
    for p, t in changed.items():
        open(p, "w").write(t)
    for a, b in files:
        subprocess.run(["git", "mv", a, b], check=True)
    print("applied")
