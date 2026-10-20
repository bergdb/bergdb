"""Class-level reachability for 005-10.

Usage: python3 -I classes.py <bergdb clone> <out dir>

Reads java/build/classes (without the ICU copy in bergdb/icu50) and
java/build/stress, maps each class to its source file, and walks the class
references from three sets of roots:

  run:  the public API (public classes in bergdb.pub, bergdb.pub.util), the
        classes that the scripts in java/stress start, and the unit and
        f-test suites (bergdb.dev.Unit, bergdb.dev.F) with the test classes
        their packs list;
  all:  run, plus every class with a main method;
  none: what neither reaches.

Writes classes.json (per class) and files.tsv (per source file).
"""

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classfile  # noqa: E402

repo, out = sys.argv[1], sys.argv[2]
java = os.path.join(repo, "java")

classes = {}
for base, kind in (("build/classes", "jar"), ("build/stress", "stress")):
    root = os.path.join(java, base)
    for p in classfile.walk(root, skip=("bergdb/icu50",)):
        c = classfile.parse(p)
        c["kind"] = kind
        classes[c["name"]] = c


def source_path(c):
    pkg = c["name"].rsplit(".", 1)[0].replace(".", "/") if "." in c["name"] else ""
    if c["kind"] == "stress":
        return "java/stress/" + c["source"]
    for d in ("src", "src-dev", "src-icu"):
        p = os.path.join("java", d, pkg, c["source"])
        if os.path.exists(os.path.join(repo, p)):
            return p
    return None


for c in classes.values():
    c["file"] = source_path(c)

ours = set(classes)


def has_main(c):
    return any(m["name"] == "main" and m["desc"] == "([Ljava/lang/String;)V"
               and m["access"] & classfile.ACC_STATIC for m in c["methods"])


# Classes that the scripts start: bergdb.x.Y names on lines that are not
# comments, in java/stress/*.sh.
script_mains = set()
for f in sorted(os.listdir(os.path.join(java, "stress"))):
    if not f.endswith(".sh"):
        continue
    for line in open(os.path.join(java, "stress", f), encoding="utf-8"):
        if line.lstrip().startswith("#"):
            continue
        for m in re.finditer(r"\b(?:bergdb(?:\.[a-z0-9]+)+\.)?[A-Z]\w*", line):
            if m.group(0) in classes:
                script_mains.add(m.group(0))

api = {n for n, c in classes.items()
       if (n.startswith("bergdb.pub.") and n.count(".") == 2
           or n.startswith("bergdb.pub.util.") and n.count(".") == 3)
       and c["access"] & classfile.ACC_PUBLIC and "$" not in n}
suites = {"bergdb.dev.Unit", "bergdb.dev.F"}
mains = {n for n, c in classes.items() if has_main(c)}


def closure(roots):
    seen = set()
    todo = [r for r in roots if r in ours]
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        c = classes[n]
        nxt = set(c["refs"])
        # A nested class is loaded with its outer class's code paths; keep
        # the outer class too, so that a file is used when any part is.
        if "$" in n:
            nxt.add(n.split("$")[0])
        for r in nxt:
            if r in ours and r not in seen:
                todo.append(r)
    return seen


run = closure(api | script_mains | suites)
everything = closure(api | script_mains | suites | mains | {"bergdb.dev.Run"})
api_only = closure(api)

for n, c in classes.items():
    c["reach"] = ("api" if n in api_only else "run" if n in run
                  else "main" if n in everything else "none")
    c["main"] = n in mains

files = {}
for n, c in classes.items():
    f = c["file"] or ("?" + n)
    files.setdefault(f, []).append(c)

order = {"api": 0, "run": 1, "main": 2, "none": 3}
rows = []
for f, cs in sorted(files.items()):
    best = min((c["reach"] for c in cs), key=order.get)
    lines = 0
    path = os.path.join(repo, f)
    if os.path.exists(path):
        lines = sum(1 for _ in open(path, encoding="utf-8", errors="replace"))
    tops = sorted(c["name"] for c in cs if "$" not in c["name"])
    rows.append((f, best, lines, ",".join(tops),
                 "main" if any(c["main"] for c in cs) else ""))

os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "files.tsv"), "w") as w:
    w.write("file\treach\tlines\tclasses\tmain\n")
    for r in rows:
        w.write("\t".join(str(x) for x in r) + "\n")
with open(os.path.join(out, "classes.json"), "w") as w:
    json.dump({n: {k: (sorted(v) if isinstance(v, set) else v)
                   for k, v in c.items() if k in
                   ("file", "reach", "main", "kind", "refs", "super",
                    "interfaces", "strings")}
               for n, c in classes.items()}, w, indent=1, sort_keys=True)
with open(os.path.join(out, "roots.txt"), "w") as w:
    w.write("# script mains\n" + "\n".join(sorted(script_mains)) + "\n")
    w.write("# all mains\n" + "\n".join(sorted(mains)) + "\n")

count = {}
for f, best, lines, _, _ in rows:
    k = (f.split("/")[1] if f.startswith("java/") else "?", best)
    count.setdefault(k, [0, 0])
    count[k][0] += 1
    count[k][1] += lines
for k in sorted(count):
    print("%-10s %-5s %4d files %7d lines" % (k[0], k[1], count[k][0], count[k][1]))
print("script mains:", len(script_mains), "all mains:", len(mains))
