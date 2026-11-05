#!/usr/bin/env python3
"""Checks each bergdb package's uses of other bergdb packages against the list
of allowed packages in its package.html (bergdb 005-56). A step of
before-commit.sh. 2026-10-27, from 006-08's deps.py (005-56's
check-deps.py).

Usage: python3 -I java/deps.py [JAVA_SRC] [--layer PKG [--list]]
  Under a second.

JAVA_SRC is java/src (the default: the one of this repository). A use is an
import, or a qualified name in code (bergdb.x.Y); comments and string literals
are left out.

Each package in JAVA_SRC must have a package.html with its list in one form,
"Depends on: a, b, c." with the packages in alphabetical order, or "Depends
on: nothing."; more text may follow the period. The list covers production
code and test code alike.

Each use is production code or test code. Test code is:
  * a file whose name contains "Tester" (DbTester.java, PubTesterIndex.java),
    or whose class implements IPack (each package's Pack, the list of its
    test classes for Nanotest);
  * the body of a nested class whose name contains "Tester" (Reclaim.Tester);
  * a method annotated @Nano, from the annotation to the method's last brace;
  * a static void method named test..., which Nanotest runs without @Nano;
  * a method or nested class of the file whose name is used only in test code
    (a helper of the tests), found again until nothing changes.
An import counts as test code if every use of its simple name in the file is in
test code (an import used nowhere counts as production code). Everything else
is production code.

With --layer PKG (such as core), only PKG and the packages it may use, directly
or not, according to the lists: for core, the Core Layer (bergdb 006-08). With
--list as well, prints only those packages, one per line (stress/core-build.sh).

Prints, per package, the packages its production code uses and the ones only
its test code uses, beside its list; then each use the list does not allow,
marked "production" or "test only", with the files, and each list that is
missing or not in the form ("BAD LIST"). The last line is the summary. Exit
status 1 if there is a use not allowed or a bad list.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SRC = os.path.join(HERE, "src")


def read_allowed(path):
    """(The packages that a package.html allows, or None; what is wrong with the list,
    or None)."""
    if not os.path.exists(path):
        return None, "no package.html"
    text = re.sub(r"<[^>]+>", " ", open(path, encoding="utf-8").read())
    m = re.search(r"Depends on:[ \t]*([^\n]*)", text)
    if not m:
        return None, "no line \"Depends on: ...\" in package.html"
    names = re.split(r"\.\s|\.$", m.group(1).strip())[0].strip()
    if names == "nothing":
        return set(), None
    listed = [n.strip() for n in names.split(",")]
    if not all(re.fullmatch(r"[a-z]\w*(?:\.[a-z]\w*)*", n) for n in listed):
        return None, "not in the form \"Depends on: a, b, c.\": %r" % m.group(1).strip()
    if listed != sorted(listed) or len(set(listed)) != len(listed):
        return None, "packages not in alphabetical order: %s" % ", ".join(listed)
    return set(listed), None


def strip(src):
    """The code with comments and string and char literals blanked out."""
    out = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2)
            j = n if j < 0 else j + 2
        elif src.startswith('"""', i):
            j = src.find('"""', i + 3)
            j = n if j < 0 else j + 3
        elif src[i] in "\"'":
            j = i + 1
            while j < n and src[j] != src[i]:
                j += 2 if src[j] == "\\" else 1
            j += 1
        else:
            out.append(src[i])
            i += 1
            continue
        out.append(re.sub(r"[^\n]", " ", src[i:j]))
        i = j
    return "".join(out)


def package_of(name):
    """bergdb.pub.util.Clock -> pub.util; bergdb.core.Db.Internal -> core."""
    parts = []
    for part in name.split(".")[1:]:
        if not part[:1].islower():
            break
        parts.append(part)
    return ".".join(parts)


def block_end(code, start):
    """The index after the brace that closes the first '{' at or after start."""
    i = code.find("{", start)
    if i < 0:
        return len(code)
    depth = 0
    for j in range(i, len(code)):
        if code[j] == "{":
            depth += 1
        elif code[j] == "}":
            depth -= 1
            if depth == 0:
                return j + 1
    return len(code)


def test_regions(code, filename, helpers=True):
    """The (start, end) ranges of test code in a stripped file; with helpers=False, without
    the helper rule (java/doubles.py, bergdb 005-79)."""
    if "Tester" in filename or re.search(r"\bimplements\s+IPack\b", code):
        return [(0, len(code))]
    regions = []
    for m in re.finditer(r"\bclass\s+\w*Tester\w*", code):
        regions.append((m.start(), block_end(code, m.end())))
    for m in re.finditer(r"@(?:bergdb\.nanotest\.)?Nano\b", code):
        # Past the annotation's own arguments, such as @Nano("f").
        k = m.end()
        if code[k:].lstrip().startswith("("):
            k = code.find(")", k) + 1
        regions.append((m.start(), block_end(code, k)))
    for m in re.finditer(r"\bstatic\s+(?:\w+\s+)*void\s+test\w*\s*\(", code):
        regions.append((m.start(), block_end(code, m.end())))
    if not helpers:
        return regions
    # Helpers: a method or nested class of the file, every use of whose name in the
    # file is in test code, is test code too; repeated until nothing changes.
    decls = []
    for m in re.finditer(r"^[ \t]*((?:(?:public|protected|private|static|final|synchronized|"
                         r"abstract)\s+)*)(?:class\s+(\w+)|(?:<[^>\n]*>\s*)?[\w.\[\]]+"
                         r"(?:<[^\n{;]*?>)?(?:\[\])*[ \t]+(\w+)\s*\([^;{}]*\))[^;{}]*\{",
                         code, re.M):
        name = m.group(2) or m.group(3)
        if name in ("if", "for", "while", "switch", "catch", "synchronized", "return"):
            continue
        decls.append((name, m.start(1), block_end(code, m.start(1))))
    words = {}
    for w in re.finditer(r"\b[A-Za-z_]\w*", code):
        words.setdefault(w.group(0), []).append(w.start())
    changed = True
    while changed:
        changed = False
        for name, a, b in decls:
            if in_regions(a, regions):
                continue
            uses = [u for u in words.get(name, ()) if not a <= u < b]
            if uses and all(in_regions(u, regions) for u in uses):
                regions.append((a, b))
                changed = True
    return regions


def in_regions(pos, regions):
    return any(a <= pos < b for a, b in regions)


def scan(src_dir):
    """Package -> (allowed or None, {used: {"prod": set(files), "test": set(files)}})."""
    packages = {}
    base = os.path.join(src_dir, "bergdb")
    for d, _, files in os.walk(base):
        pkg = os.path.relpath(d, base).replace(os.sep, ".")
        java = sorted(f for f in files if f.endswith(".java"))
        if not java:
            continue
        allowed, problem = read_allowed(os.path.join(d, "package.html"))
        uses = {}
        for f in java:
            code = strip(open(os.path.join(d, f), encoding="utf-8").read())
            regions = test_regions(code, f)
            found = []      # (name, is test code)
            body_start = 0
            for m in re.finditer(r"^\s*import\s+(?:static\s+)?(bergdb\.[\w.]+)\s*;", code, re.M):
                body_start = max(body_start, m.end())
            for m in re.finditer(r"^\s*import\s+(?:static\s+)?(bergdb\.[\w.]+)\s*;", code, re.M):
                name = m.group(1)
                simple = name.split(".")[-1]
                if simple == "*":
                    found.append((name, False))
                    continue
                spots = [u.start() for u in re.finditer(r"\b%s\b" % re.escape(simple),
                                                        code[body_start:])]
                test = bool(spots) and all(in_regions(body_start + s, regions) for s in spots)
                found.append((name, test))
            for m in re.finditer(r"\bbergdb(?:\.[a-z_]\w*)+\.[A-Z]\w*", code):
                if m.start() < body_start:
                    continue        # package and import lines
                found.append((m.group(0), in_regions(m.start(), regions)))
            for name, test in found:
                used = package_of(name)
                if used != pkg:
                    kind = "test" if test else "prod"
                    uses.setdefault(used, {"prod": set(), "test": set()})[kind].add(f)
        packages[pkg] = (allowed, problem, uses)
    return packages


def layer(packages, root):
    """root and the packages it may use, directly or not, by the lists."""
    result, todo = set(), [root]
    while todo:
        p = todo.pop()
        if p not in result:
            result.add(p)
            todo += sorted(packages.get(p, (None,))[0] or ())
    return result


def main():
    args = sys.argv[1:]
    root = None
    if "--layer" in args:
        i = args.index("--layer")
        root = args[i + 1]
        del args[i:i + 2]
    listing = "--list" in args
    args = [a for a in args if a != "--list"]
    src = args[0] if args else DEFAULT_SRC
    packages = scan(src)
    checked = sorted(layer(packages, root)) if root else sorted(packages)
    if listing:
        print("\n".join(checked))
        return 0
    checked = [p for p in checked if p in packages]    # the others: BAD LIST below
    bad = 0
    for pkg in checked:
        allowed, problem, uses = packages[pkg]
        prod = sorted(u for u in uses if uses[u]["prod"])
        test = sorted(u for u in uses if not uses[u]["prod"])
        print("%s" % pkg)
        print("    production code uses: %s" % (", ".join(prod) or "nothing"))
        print("    test code only uses:  %s" % (", ".join(test) or "nothing"))
        if allowed is None:
            bad += 1
            print("    BAD LIST: %s: %s" % (pkg, problem))
            continue
        unknown = sorted(allowed - set(packages))
        if unknown:
            bad += 1
            print("    BAD LIST: %s: no such package in %s: %s" % (pkg, src, ", ".join(unknown)))
        print("    package.html allows:  %s" % (", ".join(sorted(allowed)) or "nothing"))
        for used in sorted(uses):
            if used in allowed:
                continue
            bad += 1
            if uses[used]["prod"]:
                files = sorted(uses[used]["prod"])
                extra = sorted(uses[used]["test"] - uses[used]["prod"])
                print("    NOT ALLOWED, production: %s -> %s, in %s%s" % (
                    pkg, used, ", ".join(files),
                    "; test code also in " + ", ".join(extra) if extra else ""))
            else:
                print("    NOT ALLOWED, test only: %s -> %s, in %s" % (
                    pkg, used, ", ".join(sorted(uses[used]["test"]))))
    print("%d packages, %s" % (len(checked),
          "all as package.html allows" if bad == 0
          else "%d uses or lists not allowed" % bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
