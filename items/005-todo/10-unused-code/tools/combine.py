"""Combines ProGuard's usage lists with the javac source index (005-10).

Usage: python3 -I combine.py <bergdb clone> <pg dir> <idx dir> <out dir>

For each configuration (api, run, noapi, all, keep) the set of unused
declarations is ProGuard's list, mapped onto the source index, less what a
used declaration refers to in the source (compile-time constants, types in
generic arguments): that is repeated until nothing changes.

Writes decls-status.tsv: each declaration with its status per
configuration (1 = unused), and file-status.tsv: per source file, its lines
and the lines of unused top-level code per configuration.
"""

import os
import re
import sys
from collections import defaultdict

repo, pgdir, idxdir, out = sys.argv[1:5]
repo = os.path.realpath(repo)
CONFIGS = [n for n in ("api", "run", "noapi", "all", "keep")
           if os.path.exists(os.path.join(pgdir, "usage-%s.txt" % n))]

decls = {}
bykey = {}
for line in open(os.path.join(idxdir, "decls.tsv"), encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    d = {"id": int(f[0]), "kind": f[1], "cls": f[2], "key": f[3],
         "file": os.path.relpath(os.path.realpath(f[4]), repo),
         "l1": int(f[5]), "l2": int(f[6]), "start": int(f[7]), "end": int(f[8]),
         "mods": f[9], "constant": f[10] == "true", "implicit": f[11] == "true",
         "enc": int(f[12])}
    decls[d["id"]] = d
    bykey.setdefault((d["cls"], d["key"]), d["id"])

children = defaultdict(list)
for d in decls.values():
    if d["enc"] >= 0:
        children[d["enc"]].append(d["id"])

refs = []
for line in open(os.path.join(idxdir, "refs.tsv")):
    a, b = line.split()
    refs.append((int(a), int(b)))


def member_key(cls, sig):
    """ProGuard's signature to the index's key: name(params) or field name."""
    sig = re.sub(r"^\d+:\d+:", "", sig)
    if "(" not in sig:
        return [sig.split()[-1]]
    head, params = sig.split("(", 1)
    params = params.rstrip(")")
    name = head.split()[-1]
    simple = cls.split(".")[-1]
    if name in (simple, simple.split("$")[-1], cls):
        name = "<init>"
        keys = ["<init>(%s)" % params]
        ps = params.split(",") if params else []
        if ps:
            keys.append("<init>(%s)" % ",".join(ps[1:]))
        if len(ps) >= 2 and ps[0] == "java.lang.String" and ps[1] == "int":
            keys.append("<init>(%s)" % ",".join(ps[2:]))
        return keys
    return ["%s(%s)" % (name, params)]


unmatched = defaultdict(list)


def read_usage(name):
    dead = set()
    cls = None
    for line in open(os.path.join(pgdir, "usage-%s.txt" % name)):
        line = line.rstrip("\n")
        if not line.strip():
            continue
        if not line.startswith(" "):
            if line.endswith(":"):
                cls = line[:-1]
            else:
                cls = None
                i = bykey.get((line, "<class>"))
                if i is None:
                    unmatched[name].append(line)
                else:
                    dead.add(i)
            continue
        sig = line.strip()
        if "synthetic" in sig.split("(")[0].split() or "$" in re.sub(r"\(.*", "", sig).split()[-1]:
            continue
        for k in member_key(cls, sig):
            i = bykey.get((cls, k))
            if i is not None:
                dead.add(i)
                break
        else:
            unmatched[name].append(cls + " " + sig)
    return dead


def close_dead(dead):
    """A declaration inside an unused class is unused too."""
    todo = list(dead)
    while todo:
        i = todo.pop()
        for c in children[i]:
            if c not in dead:
                dead.add(c)
                todo.append(c)
    return dead


def restore(dead):
    """Takes back what used code refers to in the source."""
    changed = True
    while changed:
        changed = False
        for a, b in refs:
            if a >= 0 and a not in dead and b in dead:
                # b is used: so are the classes that hold it.
                j = b
                while j >= 0 and j in dead:
                    dead.discard(j)
                    j = decls[j]["enc"]
                changed = True
        if changed:
            # A class that was taken back keeps its members' own status.
            pass
    return dead


status = {}
for name in CONFIGS:
    d = read_usage(name)
    d = close_dead(d)
    # Implicit constructors and anonymous classes follow their class.
    d = restore(d)
    status[name] = d

os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "decls-status.tsv"), "w") as w:
    w.write("id\tkind\tclass\tkey\tfile\tl1\tl2\tconstant\tmods\t" + "\t".join(CONFIGS) + "\n")
    for i in sorted(decls):
        d = decls[i]
        w.write("\t".join(str(x) for x in (
            i, d["kind"], d["cls"], d["key"], d["file"], d["l1"], d["l2"],
            int(d["constant"]), d["mods"]) + tuple(
            int(i in status[c]) for c in CONFIGS)) + "\n")

with open(os.path.join(out, "unmatched.txt"), "w") as w:
    for name, items in unmatched.items():
        for x in items:
            w.write("%s\t%s\n" % (name, x))

# Per file: lines, and unused lines of top-level declarations and members.
files = defaultdict(lambda: {"lines": 0, "api": set(), "run": set(), "all": set(),
                             "tops": [], "toplive": defaultdict(bool)})
for i, d in decls.items():
    f = files[d["file"]]
    if d["enc"] < 0:
        f["tops"].append(i)
    if d["l1"] < 0 or d["l2"] < 0 or d["implicit"]:
        continue
    for name in ("api", "run", "all"):
        if i in status[name]:
            parent = d["enc"]
            if parent >= 0 and parent in status[name]:
                continue
            f[name].update(range(d["l1"], d["l2"] + 1))

with open(os.path.join(out, "file-status.tsv"), "w") as w:
    w.write("file\tlines\twhole_dead_all\twhole_dead_run\tdead_all\tdead_run\tdead_api\n")
    for fn in sorted(files):
        f = files[fn]
        p = os.path.join(repo, fn)
        n = sum(1 for _ in open(p, encoding="utf-8", errors="replace"))
        whole_all = all(t in status["all"] for t in f["tops"])
        whole_run = all(t in status["run"] for t in f["tops"])
        w.write("%s\t%d\t%d\t%d\t%d\t%d\t%d\n" % (
            fn, n, whole_all, whole_run, len(f["all"]), len(f["run"]), len(f["api"])))

for name in CONFIGS:
    print(name, "unused declarations:", len(status[name]), "unmatched:", len(unmatched[name]))
