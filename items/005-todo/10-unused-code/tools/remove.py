"""Removes declarations from Java sources by their positions (005-10).

Usage: python3 -I remove.py <repo> <decls.tsv> <members.tsv>

Removes every declaration that members.tsv marks 'remove': the span that
javac gives it, its Javadoc or block comment directly above, the rest of
its last line, and one blank line when it stood between two. Then removes
the imports that only the removed code used. decls.tsv must be the index
of the repo as it is (positions are javac's, in UTF-16 units).
"""

import csv
import os
import re
import sys
from collections import defaultdict

repo, decls_path, members_path = sys.argv[1:4]
repo = os.path.realpath(repo)

pos = {}
for line in open(decls_path, encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    pos[f[0]] = (os.path.relpath(os.path.realpath(f[4]), repo), int(f[7]), int(f[8]))

by_file = defaultdict(list)
for r in csv.DictReader(open(members_path), delimiter="\t"):
    if r["action"] == "remove":
        f, s, e = pos[r["id"]]
        assert f == r["file"], (f, r["file"])
        by_file[f].append((s, e, r["class"] + " " + r["key"]))


def to_py(text):
    """Maps UTF-16 offsets to indices of the Python string."""
    m = []
    for i, ch in enumerate(text):
        m.append(i)
        if ord(ch) > 0xFFFF:
            m.append(i)
    m.append(len(text))
    return m


def line_start(text, i):
    return text.rfind("\n", 0, i) + 1


def extend(text, s, e):
    # Back to the start of the line, if only whitespace is before.
    ls = line_start(text, s)
    if text[ls:s].strip() == "":
        s = ls
        # A comment that ends on the line just above, and starts a line.
        prev_end = s - 1
        if prev_end > 0:
            pls = line_start(text, prev_end)
            prev = text[pls:prev_end]
            if prev.strip().endswith("*/"):
                c = text.rfind("/*", 0, pls + prev.rfind("*/"))
                if c >= 0 and text[line_start(text, c):c].strip() == "":
                    s = line_start(text, c)
    # Forward: the rest of the line if it is blank or a line comment.
    j = e
    while j < len(text) and text[j] in " \t":
        j += 1
    if text.startswith("//", j):
        j = text.find("\n", j)
        j = len(text) if j < 0 else j
    if j < len(text) and text[j] == "\r":
        j += 1
    if j < len(text) and text[j] == "\n":
        e = j + 1
    return s, e


def tidy(text, s, e):
    # One blank line, if the declaration stood between two.
    before_blank = s >= 2 and text[line_start(text, s - 1):s - 1].strip() == ""
    k = e
    nl = text.find("\n", k)
    if before_blank and nl >= 0 and text[k:nl].strip() == "":
        e = nl + 1
    # No blank line before the closing brace of a class.
    nl = text.find("\n", e)
    if before_blank and nl >= 0 and text[e:nl].strip() == "}":
        s = line_start(text, s - 1)
    return s, e


IMPORT = re.compile(r"^import\s+(?!static\b)[\w.]+\.(\w+)\s*;[ \t]*\r?\n", re.M)


def used_names(text):
    body = IMPORT.sub("", text)
    return set(re.findall(r"\b\w+\b", body))


total = 0
for f, items in sorted(by_file.items()):
    p = os.path.join(repo, f)
    text = open(p, encoding="utf-8", newline="").read()
    m = to_py(text)
    spans = []
    for s, e, what in items:
        s, e = extend(text, m[s], m[e])
        spans.append((s, e, what))
    spans.sort()
    merged = []
    for s, e, what in spans:
        # Overlapping, or only blank lines between: one span.
        if merged and (s < merged[-1][1] or text[merged[-1][1]:s].strip() == ""):
            merged[-1] = (merged[-1][0], max(e, merged[-1][1]), merged[-1][2] + "; " + what)
        else:
            merged.append((s, e, what))
    merged = [tidy(text, s, e) + (what,) for s, e, what in merged]
    before = used_names(text)
    out = text
    for s, e, what in reversed(merged):
        out = out[:s] + out[e:]
    after = used_names(out)
    gone = before - after

    def drop(mt):
        return "" if mt.group(1) in gone else mt.group(0)

    out = IMPORT.sub(drop, out)
    # A file whose imports all went: one blank line after the package line.
    if not IMPORT.search(out):
        out = re.sub(r"^(package [\w.]+;\r?\n)(\r?\n)+", r"\1\n", out, count=1, flags=re.M)
    open(p, "w", encoding="utf-8", newline="").write(out)
    total += len(items)
    print("%s: %d removed" % (f, len(items)))
print("total", total)
