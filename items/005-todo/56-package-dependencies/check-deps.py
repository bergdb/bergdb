"""Checks each bergdb package's uses of other bergdb packages against the list
of allowed packages in its package.html (bergdb 005-56). By Claude (Opus 5.5,
Claude Code), 2026-10-27, from 006-08's deps.py.

Usage: python3 -I check-deps.py [JAVA_SRC]

JAVA_SRC is java/src (the default: the one of this repository). A use is an
import, or a qualified name in code (bergdb.x.Y); comments and string literals
are left out. The allowed list is the package.html line "Depends on:",
"Dependencies:", "Package dependencies:" or "Allowed dependency:".

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

Prints, per package, the packages its production code uses and the ones only
its test code uses, beside its list; then each use the list does not allow,
marked "production" or "test only", with the files. Exit status 1 if there is
one.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SRC = os.path.normpath(os.path.join(HERE, "..", "..", "..", "java", "src"))


def read_allowed(path):
    """The packages that a package.html allows, or None if it has no such line."""
    text = re.sub(r"<[^>]+>", " ", open(path, encoding="utf-8").read())
    m = re.search(r"(?:Package dependencies|Depends on|Dependencies|Allowed dependency)"
                  r"\s*:\s*([^\n]*)", text)
    if not m:
        return None
    names = re.split(r"\(|\.\s|\.$", m.group(1).strip())[0].strip()
    if names.lower().startswith(("nothing", "none")):
        return set()
    return {n.strip() for n in names.split(",") if n.strip()}


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


def test_regions(code, filename):
    """The (start, end) ranges of test code in a stripped file."""
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
        html = os.path.join(d, "package.html")
        allowed = read_allowed(html) if os.path.exists(html) else None
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
        packages[pkg] = (allowed, uses)
    return packages


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_SRC
    packages = scan(src)
    bad = 0
    for pkg in sorted(packages):
        allowed, uses = packages[pkg]
        prod = sorted(u for u in uses if uses[u]["prod"])
        test = sorted(u for u in uses if not uses[u]["prod"])
        print("%s" % pkg)
        print("    production code uses: %s" % (", ".join(prod) or "nothing"))
        print("    test code only uses:  %s" % (", ".join(test) or "nothing"))
        if allowed is None:
            print("    package.html: no list of dependencies")
            continue
        print("    package.html allows:  %s" % (", ".join(sorted(allowed)) or "nothing"))
        for used in sorted(uses):
            if used in allowed:
                continue
            bad += 1
            if uses[used]["prod"]:
                files = sorted(uses[used]["prod"])
                extra = sorted(uses[used]["test"] - uses[used]["prod"])
                print("    NOT ALLOWED, production: %s, in %s%s" % (
                    used, ", ".join(files),
                    "; test code also in " + ", ".join(extra) if extra else ""))
            else:
                print("    NOT ALLOWED, test only: %s, in %s" % (
                    used, ", ".join(sorted(uses[used]["test"]))))
    print("%d packages, %s" % (len(packages),
          "all as package.html allows" if bad == 0 else "%d uses not allowed" % bad))
    return 1 if bad else 0


sys.exit(main())
