#!/usr/bin/env python3
"""Checks that no double or float decides the stream's bytes or the memory in the
Core Layer (bergdb 005-79): the production code of the packages that
deps.py --layer core lists may use floating point only in the allowed places
below, each with its reason. A step of before-commit.sh.

Usage: python3 -I java/doubles.py [JAVA_SRC]
  Under a second. JAVA_SRC is java/src (the default: the one of this repository).

Why: the stream's bytes are a function of the transactions and the settings
(bergdb 010-01, P2), and a port must give the same bytes. Integer operations
are well defined on all targets; floating point is not (fused multiply-add,
80-bit registers, 32-bit doubles, -ffast-math, no FPU). Frans, 2026-11-03
(016-01, D3): "The Pub API can use doubles at the interface, then immediately
convert to integers (int, long) internally."

What is production code: everything but test code as deps.py's direct markers
find it (deps.test_regions with helpers=False): a Tester file or a Pack, a
nested Tester class, a method annotated @Nano, a static void test... method.
deps.py's helper rule (a method used only by tests) is left out here: it compares
names, not declarations, and until 015-04 it counted TransSeq.take, used only by
tests in its own file, as test code.

What is refused in production code, comments and string literals left out:
  * the words double, float, Double and Float, also as a part of a name in
    camel case (doubleValue, parseDouble, DoubleStream, floatToRawIntBits);
  * floating literals: a decimal number with a point, an exponent, or a d or f
    suffix (0.75, 1e-9, 2f), and a hexadecimal one with a p exponent (0x1.0p-53);
  * calls that take or return floating point without such a word: the methods
    of Math and StrictMath on doubles (MATH below), and NAMES below;
  * Math's and StrictMath's floating constants (PI, E, TAU), and static imports
    of their floating methods and constants, or of all their members;
  * the names of the allowed methods that return floating point (ALLOWED,
    guarded) outside the allowed places, so that an allowed getter cannot feed
    a decision.

Before the scan, a self-test checks the rules on snippets (SELF_TEST) and fails
if one is judged wrong.

Prints each package and file checked with floating point in allowed places,
then each use refused ("REFUSED file:line: reason: code"); the last line is the
summary. Exit status 1 if a use is refused or the self-test fails.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True     # no __pycache__ in java/
import deps  # noqa: E402  (java/deps.py)

# The allowed places: (path under bergdb/, kind, what, guarded, reason). kind is "package"
# (the directory), "file", "method" (each method or constructor of that name in the file,
# from its declaration to its last brace) or "line" (the lines that match the regex).
# guarded: the method returns floating point, so its name is refused outside the allowed
# places, and an allowed getter cannot feed a decision.
ALLOWED = [
    ("core/Db.java", "method", "setReclaimInternalFraction", False,
     "the API: checks the double and converts it to units of 2^-16 at once (005-79)"),
    ("core/Db.java", "method", "getInternalFraction", True,
     "the API: the units over 65,536, a statistic (005-79)"),
    ("core/Jmx.java", "file", None, False, "JMX: setters through Db, and statistics"),
    ("core/CacheStats.java", "method", "toString", False, "text of statistics"),
    ("common/Bytes.java", "method", "floatToBytesLE", False, "the users' values, as their bits"),
    ("common/Bytes.java", "method", "bytesToFloatLE", True, "the users' values, as their bits"),
    ("common/Bytes.java", "method", "doubleToBytesLE", False, "the users' values, as their bits"),
    ("common/Bytes.java", "method", "bytesToDoubleLE", True, "the users' values, as their bits"),
    ("common/StringUtil.java", "method", "oneDecimal", False, "text of statistics"),
    ("common/StringUtil.java", "method", "twoDecimals", False, "text of statistics"),
    ("common/StringUtil.java", "method", "wholeNumber", False, "text of statistics"),
    ("common/SeedGenerator.java", "method", "addRandomOffset", False,
     "randomness for ids and keys"),
    ("core/KeyFactory.java", "file", None, False, "keys for tests and src-dev's programs"),
    ("core/NodeCollection.java", "line",
     r"new LinkedHashMap<Long, Long>\(1024, 0\.75f, true\)", False,
     "the LinkedHashMap's load factor, a JDK parameter"),
    ("storage/BufferedStream.java", "method", "take", False,
     "text of statistics: Waits.take, the waits for room in the write buffer"),
    ("nanotest", "package", None, False, "the test framework"),
]

# Math's and StrictMath's methods that take or return floating point only (abs, max, min,
# and the exact integer ones such as floorDiv and multiplyHigh also take integers).
MATH = ("sqrt cbrt pow exp expm1 log log10 log1p floor ceil rint round random signum sin cos "
        "tan asin acos atan atan2 sinh cosh tanh hypot toRadians toDegrees ulp nextUp nextDown "
        "nextAfter scalb getExponent copySign IEEEremainder fma").split()

# Other calls that take or return floating point with no such word in their name.
NAMES = ("nextGaussian nextExponential doubles average getAverage averagingInt "
         "averagingLong").split()

# Math's and StrictMath's floating constants, and static imports of their floating methods
# or constants, or of all their members.
MATH_CONSTANT = re.compile(r"\b(?:Math|StrictMath)\s*\.\s*(PI|E|TAU)\b")
MATH_IMPORT = re.compile(r"\bimport\s+static\s+java\s*\.\s*lang\s*\.\s*(?:Math|StrictMath)"
                         r"\s*\.\s*(\*|%s|PI|E|TAU)\s*;" % "|".join(MATH))

# A name with double or float as a part in camel case: double, doubleValue, parseDouble,
# DoubleStream, floatToRawIntBits; not doubles, floating or Floater.
WORD = re.compile(r"\b\w*(?:double|float|Double|Float)\w*\b")
FLOAT_PART = re.compile(r"^(?:double|float)(?![a-z])|(?:Double|Float)(?![a-z])")
NUMBER = re.compile(r"(?<![\w.])(?:0[xX][0-9a-fA-F_]*(?:\.[0-9a-fA-F_]*)?(?:[pP][+-]?\d+)?"
                    r"[lLfFdD]?|\d[\d_]*(?:\.[\d_]*)?(?:[eE][+-]?\d+)?[lLfFdD]?"
                    r"|\.\d[\d_]*(?:[eE][+-]?\d+)?[fFdD]?)(?![\w.])")
MATH_CALL = re.compile(r"\b(?:Math|StrictMath)\s*\.\s*(%s)\s*\(" % "|".join(MATH))
NAME_CALL = re.compile(r"\b(%s)\s*\(" % "|".join(NAMES))


def is_float_literal(text):
    if text[:2] in ("0x", "0X"):
        return "p" in text or "P" in text
    return ("." in text or "e" in text or "E" in text
            or text[-1] in "fFdD")


def method_regions(code, name):
    """The (start, end) ranges of the methods or constructors named name in stripped code."""
    regions = []
    for m in re.finditer(r"^[ \t]*(?:(?:public|protected|private|static|final|synchronized|"
                         r"abstract)\s+)*(?:<[^>\n]*>\s*)?(?:[\w.\[\]<>, ]+\s+)?%s\s*\("
                         r"[^;{}]*\)[^;{}]*\{" % re.escape(name), code, re.M):
        regions.append((m.start(), deps.block_end(code, m.start())))
    return regions


def line_of(code, pos):
    return code.count("\n", 0, pos) + 1


def check(code_raw, rel, allowed=ALLOWED):
    """The refused uses in one file: [(line, reason, code line)]; and the count of uses
    in allowed places. rel is the path under bergdb/, as core/Db.java."""
    code = deps.strip(code_raw)
    lines_raw = code_raw.split("\n")
    pkg = os.path.dirname(rel)
    fname = os.path.basename(rel)
    tests = deps.test_regions(code, fname, helpers=False)
    ok_regions = []
    guarded = []          # names of allowed methods, refused elsewhere
    for path, kind, what, guard, _ in allowed:
        if guard:
            guarded.append(what)
        if kind == "package" and (pkg == path or pkg.startswith(path + "/")):
            ok_regions.append((0, len(code)))
        elif path != rel:
            continue
        elif kind == "file":
            ok_regions.append((0, len(code)))
        elif kind == "method":
            found = method_regions(code, what)
            if not found:
                raise SystemExit("doubles.py: the allowed method %s is not in %s; update ALLOWED"
                                 % (what, rel))
            ok_regions += found
        elif kind == "line":
            hits = 0
            for i, raw in enumerate(lines_raw):
                if re.search(what, raw):
                    hits += 1
                    a = sum(len(x) + 1 for x in lines_raw[:i])
                    ok_regions.append((a, a + len(raw)))
            if not hits:
                raise SystemExit("doubles.py: the allowed line %r is not in %s; update ALLOWED"
                                 % (what, rel))
    found = []
    for m in WORD.finditer(code):
        if FLOAT_PART.search(m.group(0)):
            found.append((m.start(), "floating point type or method: " + m.group(0)))
    for m in NUMBER.finditer(code):
        if is_float_literal(m.group(0)):
            found.append((m.start(), "floating literal: " + m.group(0)))
    for m in MATH_CALL.finditer(code):
        found.append((m.start(), "Math method on doubles: " + m.group(1)))
    for m in NAME_CALL.finditer(code):
        found.append((m.start(), "a method on floating point: " + m.group(1)))
    for m in MATH_CONSTANT.finditer(code):
        found.append((m.start(), "Math's floating constant: " + m.group(1)))
    for m in MATH_IMPORT.finditer(code):
        found.append((m.start(), "a static import of Math's floating point: " + m.group(1)))
    for name in guarded:
        for m in re.finditer(r"\b%s\b" % re.escape(name), code):
            found.append((m.start(), "an allowed method's name outside the allowed places "
                          "(it returns or takes floating point): " + name))
    refused, allowed_uses = [], 0
    seen = set()
    for pos, reason in sorted(found):
        if deps.in_regions(pos, tests):
            continue
        if deps.in_regions(pos, ok_regions):
            allowed_uses += 1
            continue
        n = line_of(code, pos)
        if (n, reason) in seen:
            continue
        seen.add((n, reason))
        refused.append((n, reason, lines_raw[n - 1].strip()))
    return refused, allowed_uses


# The self-test: (snippet, file, its allowed places, the reasons that must be refused, in
# order of position; [] for none).
DB_ALLOWED = [("core/Db.java", "method", "setReclaimInternalFraction", False, ""),
              ("core/Db.java", "method", "getInternalFraction", True, "")]
SELF_TEST = [
    # A double in a production method is found.
    ("class A {\n    long f(long x) {\n        double y = x;\n        return (long) y;\n    }\n}\n",
     "core/A.java", [], ["floating point type or method: double"]),
    # One in a @Nano method, or in a static void test method, is not.
    ("class A {\n    @Nano\n    public static void testF() {\n        double y = 0.5;\n    }\n}\n",
     "core/A.java", [], []),
    ("class A {\n    static void testF() {\n        float y = 0.5f;\n    }\n}\n",
     "core/A.java", [], []),
    # Math.sqrt(n) is found; Math's integer methods are not.
    ("class A {\n    long f(long n) {\n        return (long) Math.sqrt(n);\n    }\n}\n",
     "core/A.java", [], ["Math method on doubles: sqrt"]),
    ("class A {\n    long f(long n) {\n        return Math.floorDiv(n, 4) + Math.max(n, 1L) + 10L;\n"
     "    }\n}\n", "core/A.java", [], []),
    # Hexadecimal integers are not floating literals.
    ("class A {\n    boolean f(int ch) {\n        return ch <= 0x7f && ch != 0x1d && ch > 0xE5;\n"
     "    }\n}\n", "core/A.java", [], []),
    # 1e-9, 0.75f, 0x1.0p-53 and 2d are found, and nextDouble.
    ("class A {\n    long f(long n) {\n        if (n > 1e-9) return n;\n        return n;\n    }\n}\n",
     "core/A.java", [], ["floating literal: 1e-9"]),
    ("class A {\n    long f(long n) {\n        return (long) (n * 0.75f);\n    }\n}\n",
     "core/A.java", [], ["floating literal: 0.75f"]),
    ("class A {\n    long f(long n) {\n        return (long) (n * 0x1.0p-53);\n    }\n}\n",
     "core/A.java", [], ["floating literal: 0x1.0p-53"]),
    ("class A {\n    long f(java.util.Random r) {\n        return r.nextDouble() < 2d ? 1 : 0;\n"
     "    }\n}\n", "core/A.java", [],
     ["floating point type or method: nextDouble", "floating literal: 2d"]),
    # Math.PI and Math.E, static imports of Math's floating methods or of all of Math,
    # averagingLong and nextExponential are found; a static import of Math.max is not.
    ("class A {\n    long f(long n) {\n        return (long) (n * Math.PI) + (long) Math.E;\n"
     "    }\n}\n", "core/A.java", [],
     ["Math's floating constant: PI", "Math's floating constant: E"]),
    ("import static java.lang.Math.*;\nimport static java.lang.StrictMath.sqrt;\n"
     "import static java.lang.Math.max;\nclass A {\n}\n", "core/A.java", [],
     ["a static import of Math's floating point: *",
      "a static import of Math's floating point: sqrt"]),
    ("class A {\n    Object f(java.util.stream.Stream<Long> s, java.util.Random r) {\n"
     "        r.nextExponential();\n"
     "        return s.collect(java.util.stream.Collectors.averagingLong(x -> x));\n"
     "    }\n}\n", "core/A.java", [],
     ["a method on floating point: nextExponential",
      "a method on floating point: averagingLong"]),
    # Comments and strings are left out.
    ("class A {\n    // 0.25 of a double in a comment\n    String s = \"1.5 double\";\n}\n",
     "core/A.java", [], []),
    # The allowed methods are allowed; a production use of an allowed method's name is found.
    ("class Db {\n    public void setReclaimInternalFraction(double f) {\n"
     "        x = (int) Math.round(f * 65536);\n    }\n"
     "    public double getInternalFraction() {\n        return x / 65536.0;\n    }\n}\n",
     "core/Db.java", DB_ALLOWED, []),
    ("class Db {\n    public double getInternalFraction() {\n        return 1 / 65536.0;\n    }\n"
     "    long g() {\n        return 3 * getInternalFraction2();\n    }\n"
     "    long h() {\n        return (long) getInternalFraction();\n    }\n}\n", "core/Db.java",
     DB_ALLOWED[1:], ["an allowed method's name outside the allowed places (it returns or takes "
                  "floating point): getInternalFraction"]),
]


def self_test():
    failures = 0
    for i, (snippet, rel, allowed, expected) in enumerate(SELF_TEST):
        refused, _ = check(snippet, rel, allowed)
        got = [r for _, r, _ in refused]
        if got != expected:
            failures += 1
            print("SELF-TEST FAILED, snippet %d (%s): expected %s, got %s" % (i, rel, expected, got))
    return failures


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "src")
    failures = self_test()
    if failures:
        print("doubles.py: %d self-test failures" % failures)
        return 1
    print("Self-test: %d snippets judged right." % len(SELF_TEST))
    packages = sorted(deps.layer(deps.scan(src), "core"))
    base = os.path.join(src, "bergdb")
    refused_all, files, allowed_total = [], 0, 0
    for pkg in packages:
        d = os.path.join(base, pkg.replace(".", os.sep))
        if not os.path.isdir(d):
            continue
        names = sorted(f for f in os.listdir(d) if f.endswith(".java"))
        notes = []
        for f in names:
            rel = (pkg.replace(".", "/") + "/" + f)
            refused, allowed_uses = check(open(os.path.join(d, f), encoding="utf-8").read(), rel)
            files += 1
            allowed_total += allowed_uses
            if allowed_uses:
                notes.append("%s (%d)" % (f, allowed_uses))
            for n, reason, line in refused:
                refused_all.append("REFUSED %s:%d: %s: %s" % (rel, n, reason, line))
        print("%s: %d files; floating point in allowed places: %s" % (
            pkg, len(names), ", ".join(notes) or "none"))
    for r in refused_all:
        print(r)
    print("%d packages, %d files: %s" % (
        len(packages), files,
        "no floating point outside the allowed places (%d uses in them)" % allowed_total
        if not refused_all else
        "%d uses of floating point outside the allowed places" % len(refused_all)))
    return 1 if refused_all else 0


if __name__ == "__main__":
    sys.exit(main())
