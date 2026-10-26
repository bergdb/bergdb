#!/usr/bin/env python3
"""Checks every relative Markdown link in the tracked .md files of a repository
(bergdb 006-07): prints how many there are and those whose target does not
exist.

    python3 -I items/006-2026-q4/07-docs-cleanup/linkcheck.py .
"""
import os, re, subprocess, sys
root = sys.argv[1]
files = subprocess.run(["git", "-C", root, "ls-files", "*.md"], capture_output=True, text=True).stdout.split()
link = re.compile(r"\]\(([^)\s]+)\)")
broken = []
total = 0
for f in files:
    p = os.path.join(root, f)
    try:
        text = open(p, encoding="utf-8").read()
    except Exception:
        continue
    for m in link.finditer(text):
        t = m.group(1)
        if re.match(r"^[a-z]+:", t) or t.startswith("#"):
            continue
        t = t.split("#")[0]
        if not t:
            continue
        total += 1
        if not os.path.exists(os.path.normpath(os.path.join(os.path.dirname(p), t))):
            broken.append((f, t))
print("relative links:", total, "broken:", len(broken))
for f, t in broken[:40]:
    print("  ", f, "->", t)
