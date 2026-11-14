#!/usr/bin/env python3
"""025-02 step 5 (2026-11-14): stale names and paths in lean/README.md and in lean/'s comments.

Usage: python3 stale.py LEANDIR PRUNE_REPORT SUPERSEDED RENAMES [NAMESMD]

Removed = prune's DEAD names, superseded.txt's old names, the renames' old names, and the
backquoted names of names.md (all sections, old side). A name is stale when it is removed and
is not an identifier of code in lean/ (comments stripped; a reused name is live). Prints:
  README-STALE name line      a backquoted README name that is removed and not in code
  README-UNKNOWN name line    a backquoted README name in no code of lean/ (Java names and
                              the like show here too: for a look, not all are wrong)
  README-PATH path line       a .lean path or file name in README that does not exist
  COMMENT file:line name      a comment in lean/ that names a removed, not live, name
"""
import os, re, sys

lean, report, sup, ren = sys.argv[1:5]
namesmd = sys.argv[5] if len(sys.argv) > 5 else None
IDENT = r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*"


def strip_comments(s):
    """Return (code, comments) with line structure kept: each char either side."""
    code, com = [], []
    i, n, depth = 0, len(s), 0
    instr = False
    while i < n:
        c = s[i]
        if depth == 0 and not instr:
            if s.startswith("--", i):
                j = s.find("\n", i)
                j = n if j < 0 else j
                com.append(s[i:j]); code.append(" " * (j - i)); i = j; continue
            if s.startswith("/-", i):
                depth = 1; com.append("/-"); code.append("  "); i += 2; continue
            if c == '"':
                instr = True
            code.append(c); com.append(" " if c != "\n" else "\n"); i += 1; continue
        if instr:
            if c == "\\" and i + 1 < n:
                code.append(s[i:i + 2]); com.append("  "); i += 2; continue
            if c == '"':
                instr = False
            code.append(c); com.append(" " if c != "\n" else "\n"); i += 1; continue
        # in a block comment
        if s.startswith("/-", i):
            depth += 1; com.append("/-"); code.append("  "); i += 2; continue
        if s.startswith("-/", i):
            depth -= 1; com.append("-/"); code.append("  "); i += 2; continue
        com.append(c); code.append(c if c == "\n" else " "); i += 1
    return "".join(code), "".join(com)


files = []
for dp, dns, fs in os.walk(lean):
    dns[:] = [d for d in dns if d not in (".lake", "build", ".git")]
    for f in fs:
        if f.endswith(".lean"):
            files.append(os.path.join(dp, f))

live = set()
basenames = set()
comments = {}
for p in files:
    basenames.add(os.path.basename(p))
    code, com = strip_comments(open(p, errors="replace").read())
    comments[p] = com
    for t in re.findall(r"«[^»]*»|" + IDENT, code):
        parts = t.split(".")
        live.add(t)
        for k in range(len(parts)):
            live.add(".".join(parts[k:]))

removed = {}
for l in open(report):
    if l.startswith("DEAD "):
        n = l.split()[-1]
        n = n[len("SIS.Tree."):] if n.startswith("SIS.Tree.") else n
        removed.setdefault(n, "prune")
        if re.search(r"[A-Z0-9_]", n.split(".")[-1]):  # not a plain word ("given")
            removed.setdefault(n.split(".")[-1], "prune")
for l in open(sup):
    l = l.split("#", 1)[0].split()
    if l:
        removed.setdefault(l[0], "superseded")
for l in open(ren):
    l = l.split("#", 1)[0].split()
    if len(l) >= 2 and l[0] != "FILE":
        removed.setdefault(l[0], "renamed to " + l[1])
if namesmd:
    for l in open(namesmd):
        m = re.match(r"- `([^`]+)`", l)
        if m:
            removed.setdefault(m.group(1), "names.md")


def stale(n):
    if n in live:
        return None
    last = n.split(".")[-1]
    if n in removed:
        return removed[n]
    if last in removed and last not in live:
        return removed[last]
    return None


readme = os.path.join(lean, "README.md")
for ln, line in enumerate(open(readme), 1):
    for span in re.findall(r"`([^`]+)`", line):
        for t in re.findall(IDENT, span):
            if len(t) < 3:
                continue
            why = stale(t)
            if why:
                print(f"README-STALE {t} {ln} ({why})")
            elif t not in live and not os.path.exists(os.path.join(lean, t)):
                print(f"README-UNKNOWN {t} {ln}")
    for path in re.findall(r"(?<![\w/])((?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.lean)\b", line):
        if "/" in path:
            ok = os.path.exists(os.path.join(lean, path))
        else:
            ok = path in basenames
        if not ok:
            print(f"README-PATH {path} {ln}")

for p in sorted(files):
    for ln, line in enumerate(comments[p].split("\n"), 1):
        for t in set(re.findall(IDENT, line)):
            if len(t) < 4:
                continue
            why = stale(t)
            if why:
                print(f"COMMENT {os.path.relpath(p, lean)}:{ln} {t} ({why})")
