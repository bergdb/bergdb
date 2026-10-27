"""Removes the test code from a copy of BergDB Java sources (bergdb 006-08).

Usage: python3 -I strip.py <dir>

Edits the *.java files under dir in place; run it on a copy. The tester files
(*Tester*.java, Pack.java, PackForPub.java) and the nanotest package are for
the caller to delete first. In each file, this removes:

1. The Nano tests: the methods annotated @Nano, with their comments.
2. The other test code: methods named test* and main(), and nested classes
   named *Tester; then the imports of bergdb.nanotest and of the testers.
3. Until nothing changes: private methods, fields and nested classes that the
   rest of the file no longer uses (the helpers of the removed tests).

What remains of production code that uses nanotest, javac reports.
"""
import os
import re
import sys


def mask(src):
    """A copy of src with comments and string and char literals blanked (newlines
    kept), so that braces and names are found in code only."""
    out = list(src)
    i, n = 0, len(src)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2)
            j = n if j < 0 else j + 2
            blank(i, j)
            i = j
        elif src.startswith('"""', i):
            j = src.find('"""', i + 3)
            j = n if j < 0 else j + 3
            blank(i + 1, j - 1)
            i = j
        elif c in "\"'":
            j = i + 1
            while j < n and src[j] != c:
                j += 2 if src[j] == "\\" else 1
            blank(i + 1, j)
            i = j + 1
        else:
            i += 1
    return "".join(out)


def match_brace(m, open_pos):
    """The position of the brace that closes the one at open_pos."""
    depth = 0
    for k in range(open_pos, len(m)):
        if m[k] == "{":
            depth += 1
        elif m[k] == "}":
            depth -= 1
            if depth == 0:
                return k
    raise ValueError("unbalanced braces")


def member_start(src, m, start):
    """The start of the member's first line, before its comment and other
    annotations."""
    start = src.rfind("\n", 0, start) + 1
    while start > 0:
        prev = src.rfind("\n", 0, start - 1) + 1
        line = src[prev:start].strip()
        if line and not m[prev:start].strip():            # a comment line
            start = prev
        elif line.startswith("@") and not line.startswith("@Nano"):
            start = prev
        else:
            break
    return start


def line_end(src, pos):
    j = src.find("\n", pos)
    return len(src) if j < 0 else j + 1


def body_end(m, pos):
    """The end of the member whose declaration goes on at pos: its closing brace,
    or its semicolon if it has no body."""
    while m[pos] not in "{;":
        pos += 1
    return match_brace(m, pos) if m[pos] == "{" else pos


def remove_members(src, pattern):
    """Removes each member whose declaration matches pattern, one at a time."""
    while True:
        m = mask(src)
        mo = pattern.search(m)
        if not mo:
            return src
        end = body_end(m, mo.end())
        src = src[:member_start(src, m, mo.start())] + src[line_end(src, end):]


NANO = re.compile(r"@Nano\b(?:\s*\([^)]*\))?")

TEST_METHOD = re.compile(
    r"^[ \t]*(?:(?:public|private|protected|static|final|synchronized)\s+)*"
    r"[\w<>\[\].]+\s+(?:test\w*|main)\s*\(", re.M)

TESTER_CLASS = re.compile(
    r"^[ \t]*(?:(?:public|private|protected|static|final)\s+)*class\s+\w*Tester\b", re.M)

TEST_IMPORT = re.compile(
    r"^import (?:static )?bergdb\.(?:nanotest\.|\w+\.\w*Tester)[\w.*]*;\n", re.M)

PRIVATE = re.compile(
    r"^[ \t]*private\s+(?:(?:static|final|synchronized|transient|volatile|abstract)\s+)*"
    r"(?:(?:class|interface|enum)\s+(\w+)|[\w<>\[\],.? ]+?\s+(\w+)\s*(\(|=|;))", re.M)


def remove_unused_private(src):
    """Removes private members that the rest of the file does not use, until none."""
    while True:
        m = mask(src)
        for mo in PRIVATE.finditer(m):
            name = mo.group(1) or mo.group(2)
            if mo.group(1) or mo.group(3) == "(":
                end = body_end(m, mo.end() - 1)
            else:
                end = m.find(";", mo.end() - 1)                # a field
            rest = m[:mo.start()] + m[end + 1:]
            if mo.group(3) == "(":
                # A call or a method reference; not an enum's values(), say.
                use = r"(?<![A-Z]\w\.)(?<!\w)%s\s*\(|::%s\b" % ((re.escape(name),) * 2)
            else:
                use = r"\b%s\b" % re.escape(name)
            if not re.search(use, rest):
                src = src[:member_start(src, m, mo.start())] + src[line_end(src, end):]
                break
        else:
            return src


def strip(src):
    src = remove_members(src, NANO)
    src = remove_members(src, TEST_METHOD)
    src = remove_members(src, TESTER_CLASS)
    src = TEST_IMPORT.sub("", src)
    return remove_unused_private(src)


def main(root):
    for d, _, files in os.walk(root):
        for f in files:
            if f.endswith(".java"):
                path = os.path.join(d, f)
                src = open(path, encoding="utf-8").read()
                stripped = strip(src)
                if stripped != src:
                    open(path, "w", encoding="utf-8").write(stripped)


if __name__ == "__main__":
    main(sys.argv[1])
