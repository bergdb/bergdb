#!/usr/bin/env python3
"""The references of the docs/ cleanup (bergdb 006-07).

Run from the repository root, after the moves of the first commit (3b60dde),
as it was for the second:

    python3 -I items/006-2026-q4/07-docs-cleanup/relink.py            # the diff it would make
    python3 -I items/006-2026-q4/07-docs-cleanup/relink.py --write    # makes it

A tool for that one move: the tables below are its mapping.

What it changes:

* In every tracked text file, a relative Markdown link whose target moved,
  or whose file moved, so that it resolves again. A link text that is the
  old target path becomes the new path.
* In living text (java/, lean/, README.md, AGENTS.md, docs/ except log.md,
  items/readme.md), a plain mention of a moved document becomes its ID:
  `bergdb 001-08` in source files, `001-08` in Markdown; so does the text
  of a link that named the document by its old path or name.
* docs/levels.md stays the path of the current state. In living text, a
  mention that names a section of it (W1, "Level 3 cost", level 2, ...)
  becomes 011-04, the old text, and a bare mention stays. In history every
  link to it goes to 011-04.
* "level2-alignment.md, 9.N" becomes "docs/trace-format.md, N" in living
  text: section 9, the trace format, is docs/trace-format.md since 006-07.

History (the items, the moved documents, docs/log.md, releases/) keeps its
wording; only its links change.
"""

import difflib
import os
import re
import subprocess
import sys

DOCS = [
    ("docs/problem.md", "items/011-docs-archive/01-problem.md", "011-01"),
    ("docs/prior-art.md", "items/011-docs-archive/02-prior-art.md", "011-02"),
    ("docs/startup-invariants.md", "items/011-docs-archive/03-startup-invariants.md", "011-03"),
    ("docs/levels.md", "items/011-docs-archive/04-levels.md", "011-04"),
    ("docs/level4-plan.md", "items/011-docs-archive/05-level4-plan.md", "011-05"),
    ("docs/level3-plan.md", "items/011-docs-archive/06-level3-plan.md", "011-06"),
    ("docs/level3-durability.md", "items/011-docs-archive/07-level3-durability.md", "011-07"),
    ("docs/reference-theory.md", "items/011-docs-archive/08-reference-theory.md", "011-08"),
    ("docs/performance-harness.md", "items/011-docs-archive/09-performance-harness.md", "011-09"),
    ("docs/level3-performance.md", "items/011-docs-archive/10-level3-performance.md", "011-10"),
    ("docs/level2-alignment.md", "items/011-docs-archive/11-level2-alignment.md", "011-11"),
    ("docs/level3-alignment.md", "items/001-lean-model-levels-3-4/07-level3-alignment.md", "001-07"),
    ("docs/level4-alignment.md", "items/001-lean-model-levels-3-4/08-level4-alignment.md", "001-08"),
    ("docs/level3-soak.md", "items/001-lean-model-levels-3-4/09-level3-soak.md", "001-09"),
    ("docs/level4-evidence.md", "items/001-lean-model-levels-3-4/10-level4-evidence.md", "001-10"),
    ("docs/level4-performance.md", "items/001-lean-model-levels-3-4/11-level4-performance.md", "001-11"),
    ("docs/handles-alignment.md", "items/009-handles/05-handles-alignment.md", "009-05"),
]

# Moved directories: every file below moved with them.
DIRS = [
    ("docs/evidence/level3-soak", "items/001-lean-model-levels-3-4/09-level3-soak"),
    ("lean/References", "items/011-docs-archive/08-reference-theory"),
]

# Moved single files without an ID of their own.
FILES = [
    ("docs/evidence/reclaimgrid-before-summary.txt", "items/011-docs-archive/04-levels/reclaimgrid-before-summary.txt"),
    ("docs/evidence/reclaimgrid-step3-summary.txt", "items/011-docs-archive/04-levels/reclaimgrid-step3-summary.txt"),
    ("docs/evidence/reclaimgrid-pcut-summary.txt", "items/011-docs-archive/04-levels/reclaimgrid-pcut-summary.txt"),
    ("docs/evidence/reclaimgrid-items23-summary.txt", "items/011-docs-archive/04-levels/reclaimgrid-items23-summary.txt"),
    ("docs/evidence/level2-conformance-c3.txt", "items/011-docs-archive/11-level2-alignment/level2-conformance-c3.txt"),
    ("docs/evidence/level2-conformance.txt", "items/011-docs-archive/11-level2-alignment/level2-conformance.txt"),
    ("docs/evidence/level2-redlist-baseline.txt", "items/011-docs-archive/11-level2-alignment/level2-redlist-baseline.txt"),
    ("docs/evidence/level3-redlist-baseline.txt", "items/001-lean-model-levels-3-4/07-level3-alignment/level3-redlist-baseline.txt"),
    ("docs/evidence/level34-conformance.txt", "items/001-lean-model-levels-3-4/07-level3-alignment/level34-conformance.txt"),
    ("docs/evidence/level4-acopy.txt", "items/001-lean-model-levels-3-4/08-level4-alignment/level4-acopy.txt"),
]

LEVELS = "docs/levels.md"
FILEMAP = {old: new for old, new, _ in DOCS}
FILEMAP.update(dict(FILES))
IDS = {old: id_ for old, _, id_ in DOCS}
NEW2OLD = {new: old for old, new in FILEMAP.items()}

LINK = re.compile(r"\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\(([^()\s]+)\)")
SKIP_EXT = (".pdf", ".zip", ".jar", ".class", ".png", ".jpg", ".gif", ".gz", ".olean", ".ilean")


def tracked_files():
    out = subprocess.run(["git", "ls-files", "-z"], capture_output=True, check=True).stdout
    return [p.decode() for p in out.split(b"\0") if p]


def is_living(path):
    if path in ("README.md", "AGENTS.md", "items/readme.md"):
        return True
    if path.startswith("docs/"):
        return path != "docs/log.md"
    return path.startswith("java/") or path.startswith("lean/")


def is_markdown(path):
    return path.endswith(".md")


def old_path_of(path):
    """Where a file was before the moves."""
    if path in NEW2OLD:
        return NEW2OLD[path]
    for old, new in DIRS:
        if path.startswith(new + "/"):
            return old + path[len(new):]
    return path


def map_path(old_abs, living):
    """Where a file (or directory) that was at old_abs is now."""
    if old_abs == LEVELS and living:
        return LEVELS
    if old_abs in FILEMAP:
        return FILEMAP[old_abs]
    for old, new in DIRS:
        if old_abs == old or old_abs.startswith(old + "/"):
            return new + old_abs[len(old):]
    return old_abs


def rel(target_abs, from_dir):
    r = os.path.relpath(target_abs, from_dir or ".")
    return r


def fix_link(m, path, living, notes):
    text, target = m.group(1), m.group(2)
    if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", target) or target.startswith("#"):
        return m.group(0)
    tpath, sep, anchor = target.partition("#")
    if not tpath:
        return m.group(0)
    trailing = "/" if tpath.endswith("/") else ""
    old_dir = os.path.dirname(old_path_of(path))
    old_abs = os.path.normpath(os.path.join(old_dir, tpath))
    new_abs = map_path(old_abs, living)
    moved_file = old_path_of(path) != path
    if new_abs == old_abs and not moved_file:
        return m.group(0)
    new_rel = rel(new_abs, os.path.dirname(path)) + trailing
    if new_rel.rstrip("/") == tpath.rstrip("/") and not trailing:
        return m.group(0)
    new_target = new_rel + (sep + anchor if sep else "")
    new_text = text
    if (text == tpath or text == target) and "/" in tpath:
        new_text = new_rel
    else:
        # A text that is a relative path to the target or its directory,
        # such as [../lean/](../lean/README.md), follows the file too.
        t = text.strip("`")
        if t.startswith(("../", "./")) and " " not in t:
            t_old = os.path.normpath(os.path.join(old_dir, t))
            if t_old == old_abs or old_abs.startswith(t_old + "/"):
                t_new = rel(map_path(t_old, living), os.path.dirname(path))
                new_text = text.replace(t, t_new + ("/" if t.endswith("/") else ""))
    if living and old_abs in IDS and not (old_abs == LEVELS and new_abs == LEVELS):
        names = {tpath, os.path.basename(old_abs), old_abs, "../" + old_abs, "../../" + old_abs}
        if text.strip("`") in names:
            new_text = IDS[old_abs]
    if new_abs != old_abs and not os.path.exists(new_abs):
        notes.append(f"{path}: link to {new_abs}, which does not exist")
    return f"[{new_text}]({new_target})"


SECTION_AFTER = re.compile(r'^,?\s*(?:[*/#]+\s*)?(?:W\d|"|“|[Ll]evel\s+\d|section|Level|level)')


def plain_mentions(seg, path, notes, before_text):
    """Rewrite plain mentions of moved documents in a living segment."""
    source = not is_markdown(path)

    def id_text(id_, start, s):
        if source and not s[:start].endswith("bergdb "):
            return "bergdb " + id_
        return id_

    # The trace format: level2-alignment.md, 9.N is docs/trace-format.md, N.
    def tf(m):
        notes.append(f"{path}: {m.group(0)!r} -> trace-format.md")
        return "docs/trace-format.md, " + m.group(1)
    seg = re.sub(r"(?<![\w./-])(?:\.\./)*(?:docs/)?level2-alignment\.md,\s*9\.(\d)", tf, seg)

    for old, _, id_ in DOCS:
        name = re.escape(os.path.basename(old))
        pat = re.compile(r"(?<![\w./-])(`?)((?:\.\./)*(?:docs/)?" + name + r")\1(?![\w-])")
        out, pos = [], 0
        for m in pat.finditer(seg):
            if old == LEVELS and not SECTION_AFTER.match(seg[m.end():m.end() + 40]):
                continue
            out.append(seg[pos:m.start()])
            out.append(id_text(id_, m.start(), seg))
            notes.append(f"{path}: {m.group(0)!r} -> {id_} | {seg[m.end():m.end() + 30]!r}")
            pos = m.end()
        out.append(seg[pos:])
        seg = "".join(out)
    seg = seg.replace("lean/References/", "items/011-docs-archive/08-reference-theory/")
    return seg


def process(path, text):
    living = is_living(path)
    notes = []
    if not is_markdown(path):
        # Markdown links are only read in Markdown; elsewhere `a[i](x)` is code.
        return (plain_mentions(text, path, notes, None) if living else text), notes
    pieces, pos = [], 0
    for m in LINK.finditer(text):
        before = text[pos:m.start()]
        pieces.append(plain_mentions(before, path, notes, None) if living else before)
        pieces.append(fix_link(m, path, living, notes))
        pos = m.end()
    rest = text[pos:]
    pieces.append(plain_mentions(rest, path, notes, None) if living else rest)
    return "".join(pieces), notes


def main():
    write = "--write" in sys.argv
    changed, all_notes = 0, []
    diff_out = []
    for path in tracked_files():
        if path.endswith(SKIP_EXT) or not os.path.isfile(path):
            continue
        with open(path, "rb") as f:
            raw = f.read()
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            continue
        new, notes = process(path, text)
        all_notes += notes
        if new != text:
            changed += 1
            diff_out += difflib.unified_diff(text.splitlines(True), new.splitlines(True), "a/" + path, "b/" + path, n=0)
            if write:
                with open(path, "wb") as f:
                    f.write(new.encode("utf-8"))
    sys.stdout.writelines(diff_out)
    print(f"\n# {changed} files {'changed' if write else 'to change'}", file=sys.stderr)
    for n in all_notes:
        if "does not exist" in n:
            print("# " + n, file=sys.stderr)


if __name__ == "__main__":
    main()
