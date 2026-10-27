"""Checks the package dependencies of BergDB's java/src against package.html
(bergdb 006-08).

Usage: python3 -I deps.py <java/src> [PKG [--list]]

For each package: the bergdb packages its code uses (imports, and qualified
names in code; comments and string literals are left out) against the ones
its package.html allows (the line "Depends on:", "Dependencies:", "Package
dependencies:" or "Allowed dependency:"). Prints each package's uses and every
use that package.html does not allow, with the files.

With PKG (such as core), only PKG and the packages it may use, directly or
not, according to the package.html files: for core, the Core Layer. With
--list, prints only those packages, one per line.

Exit status 1 if a checked package uses a package that its package.html does
not allow.
"""
import os
import re
import sys


def read_allowed(path):
    """The packages that a package.html allows, or None if it has no such line."""
    text = re.sub(r"<[^>]+>", " ", open(path, encoding="utf-8").read())
    m = re.search(r"(?:Package dependencies|Depends on|Dependencies|Allowed dependency)"
                  r"\s*:\s*([^\n]*)", text)
    if not m:
        return None
    # Up to a parenthesis or the end of the sentence: "nanotest (only).",
    # "common, pub.util (not: core, ...).", "pub, core. Note that ...".
    names = re.split(r"\(|\.\s|\.$", m.group(1).strip())[0].strip()
    if names.lower().startswith(("nothing", "none")):
        return set()
    return {n.strip() for n in names.split(",") if n.strip()}


def strip(src):
    """The code with comments and string literals blanked out."""
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


def scan(src_dir):
    """Package -> (allowed or None, {used package: [(file, name)]})."""
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
            names = re.findall(r"^\s*import\s+(?:static\s+)?(bergdb\.[\w.]+)", code, re.M)
            for line in code.split("\n"):
                if not re.match(r"\s*(package|import)\b", line):
                    names += re.findall(r"\bbergdb(?:\.[a-z_]\w*)+\.[A-Z]\w*", line)
            for name in names:
                used = package_of(name)
                if used != pkg:
                    uses.setdefault(used, []).append((f, name))
        packages[pkg] = (allowed, uses)
    return packages


def closure(packages, root):
    result, todo = set(), [root]
    while todo:
        p = todo.pop()
        if p in result:
            continue
        result.add(p)
        todo += sorted(packages.get(p, (None, {}))[0] or ())
    return result


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    packages = scan(args[0])
    checked = sorted(closure(packages, args[1]) if len(args) > 1 else packages)
    if "--list" in sys.argv:
        print("\n".join(checked))
        return 0
    bad = 0
    for pkg in checked:
        if pkg not in packages:
            print("%s: allowed by a package.html, but there is no such package" % pkg)
            bad += 1
            continue
        allowed, uses = packages[pkg]
        print("%s uses %s" % (pkg, ", ".join(sorted(uses)) or "nothing"))
        if allowed is None:
            print("    package.html: no list of dependencies")
            bad += 1
            continue
        print("    package.html allows %s" % (", ".join(sorted(allowed)) or "nothing"))
        for used in sorted(uses):
            if used not in allowed:
                bad += 1
                files = sorted({f for f, _ in uses[used]})
                print("    NOT ALLOWED: %s, in %s" % (used, ", ".join(files)))
    print("%d packages checked, %s" % (len(checked),
          "all as package.html allows" if bad == 0 else "%d not as package.html allows" % bad))
    return 1 if bad else 0


sys.exit(main())
