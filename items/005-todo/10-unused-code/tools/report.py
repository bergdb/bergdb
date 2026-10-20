"""Tables for 005-10's proposal, from the patch clone.

Usage: python3 -I report.py <patch clone> <plan dir> <work dir> <out dir>

Reads the deleted files' groups from delete-files.txt (the "# A1." style
headers), the removed members from the rounds' members.tsv (and the API
members of stage 2, group G1), and the lines from the clone's diff against
its origin (`git diff origin/HEAD`, or the staged changes if there are no
commits). Writes files.tsv, members.tsv and
lean.tsv to <out dir> and prints a summary per group.
"""

import csv
import glob
import os
import re
import subprocess
import sys
from collections import defaultdict

clone, plan, work, out = sys.argv[1:5]

# Deleted files and their groups.
group_of_file = {}
g = None
for line in open(os.path.join(plan, "delete-files.txt")):
    line = line.rstrip("\n")
    m = re.match(r"# ([A-Z]\d)\.", line)
    if m:
        g = m.group(1)
    elif line and not line.startswith("#"):
        group_of_file[line] = g

committed = subprocess.run(["git", "-C", clone, "rev-list", "--count", "origin/HEAD..HEAD"],
                           capture_output=True, text=True).stdout.strip() not in ("", "0")
BASE = ["origin/HEAD"] if committed else ["--cached"]

numstat = {}
for line in subprocess.run(["git", "-C", clone, "diff"] + BASE + ["--numstat"],
                           capture_output=True, text=True).stdout.splitlines():
    a, d, p = line.split("\t")
    numstat[p] = (a, d)

# Removed hunks of modified files: original line ranges.
hunks = defaultdict(list)
diff = subprocess.run(["git", "-C", clone, "diff"] + BASE + ["-U0", "--diff-filter=M"],
                      capture_output=True, text=True).stdout
cur = None
for line in diff.splitlines():
    if line.startswith("--- a/"):
        cur = line[6:]
    m = re.match(r"@@ -(\d+)(?:,(\d+))? ", line)
    if m and cur:
        start, n = int(m.group(1)), int(m.group(2) or 1)
        if n:
            hunks[cur].append((start, start + n - 1))

tests = set()
for p in glob.glob(os.path.join(work, "out-patch", "*round1", "pg", "tests.tsv"))[:1]:
    for line in open(p):
        c, name, _, _ = line.rstrip("\n").split("\t")
        tests.add((c, name))

DEBUG = re.compile(r"^(print\w*|assert\w*|check\w*|toDisplayString|toStringWithSubstitute|"
                   r"compareValueToString|summary)$")


API = set()
if os.path.exists(os.path.join(plan, "api-remove.txt")):
    for line in open(os.path.join(plan, "api-remove.txt")):
        if line.strip() and not line.startswith("#"):
            API.add(tuple(line.rstrip("\n").split("\t")))


def member_group(r):
    f, cls, key, kind = r["file"], r["class"], r["key"], r["kind"]
    if (cls, key) in API:
        return "G1"
    name = key.split("(")[0]
    base = os.path.basename(f)
    if base in ("KeyFactory.java", "DagNodeIterator.java"):
        return "B3"
    if f.startswith("java/src-dev/bergdb/test/") and base in (
            "Get.java", "GetThreaded.java", "PerfGetMany.java", "Set.java",
            "BigDb.java", "BigDbWithDeletes.java"):
        return "D2"
    if not f.startswith("java/src/"):
        return "A2"
    nested = cls.split("$")[1:]
    if (kind in ("METHOD", "CONSTRUCTOR") and "public" in r["mods"].split()
            and not nested
            and not cls.endswith(("Tester", "Comparison", "TestClock"))
            and "abstract" not in r["mods"].split()
            and (cls, name) not in tests and not DEBUG.match(name)
            and not f.startswith("java/src/bergdb/nanotest/")):
        return "A3"
    return "A2"


members = []
for p in sorted(glob.glob(os.path.join(work, "out-patch", "*round*", "members.tsv"))
               + glob.glob(os.path.join(work, "out-patch", "stage2-api", "members.tsv"))):
    status = {}
    sp = os.path.join(os.path.dirname(p), "c", "decls-status.tsv")
    if os.path.exists(sp):
        for r in csv.DictReader(open(sp), delimiter="\t"):
            status[r["id"]] = r
    for r in csv.DictReader(open(p), delimiter="\t"):
        if r["action"] != "remove":
            continue
        r["mods"] = status[r["id"]]["mods"] if r["id"] in status else "public"
        members.append(r)

# Attribute removed lines to members: a hunk to the members whose lines it
# holds (the first of them takes the hunk's comment and blank lines).
mlines = defaultdict(int)
for f, hs in hunks.items():
    ms = [m for m in members if m["file"] == f]
    for a, b in hs:
        inside = [m for m in ms if int(m["l1"]) >= a and int(m["l2"]) <= b]
        if not inside:
            continue
        for k, m in enumerate(inside):
            mlines[id(m)] += (int(m["l2"]) - int(m["l1"]) + 1)
        extra = (b - a + 1) - sum(int(m["l2"]) - int(m["l1"]) + 1 for m in inside)
        mlines[id(inside[0])] += extra

os.makedirs(out, exist_ok=True)
summary = defaultdict(lambda: [0, 0, 0])   # group -> files deleted, members, lines
with open(os.path.join(out, "files.tsv"), "w") as w:
    w.write("group\tfile\tlines\n")
    for f, g in sorted(group_of_file.items(), key=lambda x: (x[1], x[0])):
        a, d = numstat.get(f, ("-", "-"))
        n = int(d) if d != "-" else 0
        w.write("%s\t%s\t%s\n" % (g, f, d if d != "-" else "binary"))
        summary[g][0] += 1
        summary[g][2] += n
with open(os.path.join(out, "members.tsv"), "w") as w:
    w.write("group\tfile\tl1\tl2\tlines\tkind\tclass\tmember\n")
    for m in sorted(members, key=lambda m: (member_group(m), m["file"], int(m["l1"]))):
        g = member_group(m)
        n = mlines.get(id(m), int(m["l2"]) - int(m["l1"]) + 1)
        w.write("\t".join([g, m["file"], m["l1"], m["l2"], str(n), m["kind"],
                           m["class"], m["key"]]) + "\n")
        summary[g][1] += 1
        summary[g][2] += n

lean_lines = sum(int(d) for p, (a, d) in numstat.items() if p.startswith("lean/") and d != "-")
lean_files = sum(1 for p in numstat if p.startswith("lean/"))
summary["F1"] = [0, len([l for l in open(os.path.join(plan, "lean-remove.txt"))
                          if l.strip() and not l.startswith("#")]), lean_lines]

for g in sorted(summary):
    f, m, n = summary[g]
    print("%-3s files %3d  members %3d  lines %6d" % (g, f, m, n))
edited = sum(int(d) for p, (a, d) in numstat.items() if p not in group_of_file and d != "-"
             and not p.startswith("lean/"))
print("lines deleted in edited Java files and docs (members and references):", edited)
print("lean files", lean_files)
