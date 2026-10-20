"""Unused Lean declarations for 005-10.

Usage: python3 -I lean_unused.py <bergdb clone> <deps.tsv> <out dir>

A declaration is used if a root reaches it, through the constants that the
compiled terms use (deps.tsv, from LeanDeps.lean) or the names that the
source refers to (the .ilean files of lake build). The roots:

  * the theorems that lean/README.md lists for `#print axioms`;
  * names that docs/*.md, README.md or lean/README.md cite in backticks;
  * everything that the executables' modules (Test, TraceCheck, PhysTest,
    ReclaimTest) refer to;
  * what commands outside a declaration refer to (#guard, example, #eval,
    attribute): the tests that lake build runs.

Writes lean-unused.tsv (declaration, module, file, lines) and prints a
summary per file.
"""

import glob
import json
import os
import re
import sys
from collections import defaultdict

repo, deps_path, out = sys.argv[1:4]
lean = os.path.join(repo, "lean")
build = os.path.join(lean, ".lake", "build", "lib", "lean")

edges = defaultdict(set)
kind = {}
module = {}
for line in open(deps_path, encoding="utf-8"):
    parts = line.rstrip("\n").split("\t")
    if len(parts) < 3:
        continue
    n, k, m = parts[0], parts[1], parts[2]
    kind[n] = k
    module[n] = m
    if len(parts) > 3 and parts[3]:
        edges[n].update(parts[3].split(" "))

decls = {}        # name -> (module, l1, l2)
roots = set()
EXE = {"Test", "TraceCheck", "PhysTest", "ReclaimTest"}
for p in glob.glob(os.path.join(build, "**", "*.ilean"), recursive=True):
    d = json.load(open(p, encoding="utf-8"))
    mod = d["module"]
    for n, r in d.get("decls", {}).items():
        decls[n] = (mod, r[0] + 1, r[2] + 1)
    for key, ref in d.get("references", {}).items():
        try:
            k = json.loads(key)
        except ValueError:
            continue
        if "c" not in k:
            continue
        target = k["c"]["n"]
        for u in ref.get("usages", []):
            parent = u[4] if len(u) > 4 else None
            if mod in EXE or not parent:
                roots.add(target)
            else:
                edges[parent].add(target)

# The theorems of lean/README.md's #print axioms lists.
readme = open(os.path.join(lean, "README.md"), encoding="utf-8").read()
roots.update(re.findall(r"#print axioms (\S+)", readme))

# Names that the documents cite.
cited = set()
for p in glob.glob(os.path.join(repo, "docs", "*.md")) + [
        os.path.join(repo, "README.md"), os.path.join(lean, "README.md")]:
    text = open(p, encoding="utf-8").read()
    for tok in re.findall(r"`([^`\s]+)`", text):
        tok = tok.strip("(),.;:")
        if re.match(r"^[A-Za-z_][\w.'?!₀-₉]*$", tok):
            cited.add(tok)
by_last = defaultdict(set)
for n in set(kind) | set(decls):
    by_last[n].add(n)
    parts = n.split(".")
    for i in range(1, len(parts)):
        by_last[".".join(parts[i:])].add(n)
doc_roots = set()
for tok in cited:
    doc_roots |= by_last.get(tok, set())
roots |= doc_roots

seen = set()
todo = [r for r in roots]
while todo:
    n = todo.pop()
    if n in seen:
        continue
    seen.add(n)
    for m in edges.get(n, ()):
        if m not in seen:
            todo.append(m)
    # A structure or inductive is used when one of its parts is.
    if "." in n:
        todo.append(n.rsplit(".", 1)[0])


def auxiliary(n):
    last = n.split(".")[-1]
    return (n.startswith("_") or "._" in n or last in (
        "rec", "recOn", "casesOn", "below", "brecOn", "noConfusion", "noConfusionType",
        "ibelow", "binductionOn", "mk", "ctorIdx", "induct", "mutual_induct", "eq_def")
        or re.match(r"(match|proof|eq|_)\_?\d+$", last) or last.startswith("inst"))


unused = []
for n, (mod, l1, l2) in sorted(decls.items()):
    if mod in EXE or n in seen or auxiliary(n):
        continue
    if not (mod == "SIS" or mod == "Check" or mod.startswith(("SIS.", "Check."))):
        continue
    unused.append((n, kind.get(n, "?"), mod, l1, l2))

os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "lean-unused.tsv"), "w") as w:
    w.write("name\tkind\tmodule\tfile\tl1\tl2\n")
    for n, k, mod, l1, l2 in unused:
        w.write("%s\t%s\t%s\tlean/%s.lean\t%d\t%d\n" % (n, k, mod, mod.replace(".", "/"), l1, l2))

per = defaultdict(lambda: [0, 0])
for n, k, mod, l1, l2 in unused:
    per[mod][0] += 1
    per[mod][1] += l2 - l1 + 1
total = [0, 0]
for mod in sorted(per):
    total[0] += per[mod][0]
    total[1] += per[mod][1]
    print("%-32s %4d declarations %6d lines" % (mod, per[mod][0], per[mod][1]))
print("total", total, "roots", len(roots), "cited", len(doc_roots), "decls", len(decls))
