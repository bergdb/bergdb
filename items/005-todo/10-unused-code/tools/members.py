"""The members that 005-10 proposes to remove, from the 'keep' configuration.

Usage: python3 -I members.py <repo> <c dir> <idx dir> <config> <out.tsv> [skip.txt]

skip.txt, if given: more path prefixes whose files are skipped, one a line
(the groups that Frans decided to keep as they are).

Takes the unused declarations of the configuration (ProGuard's list less
what the source refers to, combine.py) and leaves out what should stay:

  fixture    test fixtures of nanotest, which its tests find by reflection;
  string     a name that the sources look up by reflection (getMethod("x"),
             getDeclaredField("x") and the like);
  guard      an empty private constructor (a class of static members only);
  implicit   a constructor that javac adds;
  main       a main method (a tool of its own; the groups decide on tools);
  field      a field that is not static and final: objects are stored by
             reflection over their fields;
  override   a method that overrides one that is used, or a library method;
  abstract   an abstract method that a used method implements;
  enum       an enum constant;
  skipped    a file in a group that is kept or left for Frans to decide;
  frans      a member that Frans decided to keep (KEEP);
  needed     what one of the above refers to.

Writes every unused declaration with 'remove' or the reason it stays.
"""

import csv
import os
import re
import sys

repo, cdir, idxdir, config, outpath = sys.argv[1:6]
repo = os.path.realpath(repo)
more_skip = ()
if len(sys.argv) > 6:
    more_skip = tuple(l.strip() for l in open(sys.argv[6])
                      if l.strip() and not l.startswith("#"))

SKIP_FILES = (
    "java/src-dev/frans/",
    "java/src-dev/bergdb/test/night/",
    "java/src-dev/bergdb/demo/",
    "java/src-dev/bergdb/dev/VizFigure.java",
    "java/src-dev/bergdb/dev/VizFigureSet.java",
    "java/src-dev/bergdb/dev/DagExamples.java",
    "java/src-dev/bergdb/dev/PrintableDagExamples.java",
    "java/stress/BryanRepro.java",
    # JMX: docs/level4-alignment.md names Jmx.DbMonitor as the way to read and
    # set the budget; register() is how it gets into JMX. A feature, kept.
    "java/src/bergdb/core/Jmx.java",
)
# Fields that are not static and final, checked by hand: nothing stores
# their objects by reflection, and nothing reads or writes them.
FORCE = {("bergdb.core.Jmx$DbMonitor", "mbs"), ("bergdb.core.Trans", "splitCount"),
         ("bergdb.core.PerfTool$Alert", "detail"), ("bergdb.core.PerfUtil$GcLog", "collectorLine"),
         ("bergdb.test.BryanIssue", "prevTransSeq")}
# Members that Frans decides to keep, as (class, key) like the tables'
# (for example ("bergdb.storage.StorageManager", "setD1(bergdb.storage.DurabilityRule)")).
KEEP = set()
FIXTURES = ("bergdb.nanotest.DummyTestClass", "bergdb.nanotest.MethodFilter$TestClassA",
            "bergdb.nanotest.SimpleTestEnvironment$ClassUnderTest")

status = {r["id"]: r for r in csv.DictReader(open(os.path.join(cdir, "decls-status.tsv")),
                                             delimiter="\t")}
decls = {}
for line in open(os.path.join(idxdir, "decls.tsv"), encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    decls[f[0]] = {"id": f[0], "kind": f[1], "cls": f[2], "key": f[3],
                   "file": os.path.relpath(os.path.realpath(f[4]), repo),
                   "l1": int(f[5]), "l2": int(f[6]), "start": int(f[7]), "end": int(f[8]),
                   "mods": f[9], "constant": f[10] == "true", "implicit": f[11] == "true",
                   "enc": f[12], "overrides": f[13].split(",") if len(f) > 13 and f[13] else []}

dead = {i for i, r in status.items() if r[config] == "1"}
overriders = {}
for i, d in decls.items():
    for o in d["overrides"]:
        overriders.setdefault(o, []).append(i)

strings = set()
texts = {}
for root in ("java/src", "java/src-dev", "java/src-icu", "java/stress"):
    for dp, _, fs in os.walk(os.path.join(repo, root)):
        for fn in fs:
            if fn.endswith(".java"):
                p = os.path.join(dp, fn)
                t = open(p, encoding="utf-8", newline="").read()
                texts[os.path.relpath(p, repo)] = t
                strings.update(re.findall(
                    r'get(?:Declared)?(?:Method|Field|Constructor)s?\(\s*"([A-Za-z_$][\w$]*)"', t))


def reason(i):
    d = decls[i]
    name = d["key"].split("(")[0]
    if d["file"].startswith(SKIP_FILES + more_skip):
        return "skipped"
    if (d["cls"], d["key"]) in KEEP:
        return "frans"
    if d["cls"].startswith(FIXTURES):
        return "fixture"
    if d["kind"] == "ENUM_CONSTANT":
        return "enum"
    if d["kind"] == "CONSTRUCTOR":
        if d["implicit"] or d["l2"] < 0:
            return "implicit"
        body = texts[d["file"]][d["start"]:d["end"]]
        if "private" in d["mods"] and re.search(r"\(\s*\)\s*\{\s*\}\s*$", body):
            return "guard"
    if d["kind"] == "METHOD" and name == "main":
        return "main"
    if name in strings and d["kind"] in ("METHOD", "FIELD"):
        return "string"
    if (d["kind"] == "FIELD" and not ("static" in d["mods"] and "final" in d["mods"])
            and (d["cls"], d["key"]) not in FORCE):
        return "field"
    if d["kind"] == "METHOD":
        for o in d["overrides"]:
            if o == "lib" or o not in dead:
                return "override"
        if "abstract" in d["mods"] or decls.get(d["enc"], {}).get("kind") == "INTERFACE":
            if any(x not in dead for x in overriders.get(i, [])):
                return "abstract"
    return "remove"


rows = []
for i in sorted(dead, key=int):
    d = decls[i]
    # Only the outermost unused declaration: its parts go with it.
    if d["enc"] in dead:
        continue
    if not os.path.exists(os.path.join(repo, d["file"])):
        continue
    rows.append((reason(i), d))

# What stays keeps what it refers to: an unused declaration that stays (a
# skipped file, a main method, a fixture) may call one that would go.
refs = []
for line in open(os.path.join(idxdir, "refs.tsv")):
    a, b = line.split()
    refs.append((a, b))


def outermost(i):
    """The outermost unused declaration that holds i, or None."""
    top = None
    while i in decls and i != "-1":
        if i in dead:
            top = i
        i = decls[i]["enc"]
    return top


# Repeated until nothing changes: what stays keeps what it refers to, an
# abstract method stays if one that implements it stays, and an override
# goes only with what it overrides.
changed = True
while changed:
    changed = False
    staying = {d["id"] for r, d in rows if r != "remove"}
    index = {d["id"]: k for k, (r, d) in enumerate(rows)}
    for a, b in refs:
        ta, tb = outermost(a), outermost(b)
        if ta in staying and tb in index and rows[index[tb]][0] == "remove" and ta != tb:
            rows[index[tb]] = ("needed", rows[index[tb]][1])
            staying.add(tb)
            changed = True
    for k, (r, d) in enumerate(rows):
        if r != "remove":
            continue
        if any(outermost(o) in staying for o in d["overrides"] if o != "lib"):
            rows[k] = ("override", d)
            staying.add(d["id"])
            changed = True
        elif any(outermost(x) in staying for x in overriders.get(d["id"], [])):
            rows[k] = ("abstract", d)
            staying.add(d["id"])
            changed = True

with open(outpath, "w") as w:
    w.write("action\tid\tkind\tclass\tkey\tfile\tl1\tl2\n")
    for r, d in rows:
        w.write("\t".join([r, d["id"], d["kind"], d["cls"], d["key"], d["file"],
                           str(d["l1"]), str(d["l2"])]) + "\n")

count = {}
for r, d in rows:
    count[r] = count.get(r, 0) + 1
print(count)
lines = sum(d["l2"] - d["l1"] + 1 for r, d in rows if r == "remove" and d["l1"] > 0)
print("lines to remove (declarations only, without comments):", lines)
