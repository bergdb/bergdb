#!/usr/bin/env python3
"""Checks that no double or float decides the stream's bytes or the memory in
the C clone's library (bergdb 005-79, as java/doubles.py does for Java's Core
Layer since release 2026.2; bergdb 015-02): the code in src/ may use floating
point only in the allowed places below, each with its reason. A part of the
rules step of before-commit.sh.

Usage: python3 -I test/doubles.py [C_DIR]      (C_DIR: the C project, by default
                                               the one of this file)

Why: the stream's bytes are a function of the transactions and the settings
(bergdb 010-01, P2), and C must give Java's bytes on every target: integer
operations are defined the same everywhere, floating point is not (fused
multiply-add, x87, no FPU on a microcontroller). Frans, 2026-11-03 (016-01, D3):
"The Pub API can use doubles at the interface, then immediately convert to
integers (int, long) internally."

What is refused in src/*.c and src/*.h, comments and string and character
literals left out:
  * the words double and float;
  * floating literals: a decimal number with a point or an exponent (0.75, 1e9,
    2.f), and a hexadecimal one with a p exponent (0x1.0p-53);
  * <math.h> and its functions and macros (FUNCS below), which take or give
    floating point without such a word;
  * the names of the allowed functions that take or give floating point
    (GUARDED below) outside the allowed places, so that an allowed conversion or
    statistic cannot feed a decision.

Before the scan, a self-test checks the rules on snippets and fails if one is
judged wrong. Prints each use refused ("REFUSED file:line: reason: code"), then
one line: "doubles ok: ..." or "DOUBLES FAILED: ...". Exit status 1 if a use is
refused or the self-test fails.
"""
import os
import re
import sys

# The allowed places: (file under src/, kind, what, reason). kind is "file", "function"
# (the definition of that name, from its first line at column 0 to the next "}" at
# column 0) or "line" (the lines that match the regex).
ALLOWED = [
    ("jsem.h", "file", None,
     "Java's semantics: the conversions of a double (j_d2l, j_d2i, j_round) and the bits"),
    ("bytes.c", "function", "bytes_get_float_le", "Java's Bytes: the users' values, as bits"),
    ("bytes.c", "function", "bytes_put_float_le", "Java's Bytes: the users' values, as bits"),
    ("bytes.c", "function", "bytes_get_double_le", "Java's Bytes: the users' values, as bits"),
    ("bytes.c", "function", "bytes_put_double_le", "Java's Bytes: the users' values, as bits"),
    ("bytes.h", "line", r"\bbytes_(get|put)_(float|double)_le\(", "their declarations"),
    ("db.c", "function", "db_set_reclaim_internal_fraction",
     "the API's double: checked, and converted to units of 2^-16 at once (005-79)"),
    ("db.c", "function", "db_internal_fraction", "a statistic: the units over 65,536"),
    ("db.h", "line", r"\b(db_set_reclaim_internal_fraction|db_internal_fraction)\(",
     "their declarations"),
    ("api.c", "function", "bergdb_set_reclaim_internal_fraction",
     "the API: its double, to db_set_reclaim_internal_fraction"),
    ("api.c", "function", "bergdb_stats", "the API: the statistic internal_fraction"),
]

# Functions that take or give floating point: refused outside the allowed places.
GUARDED = ["j_d2l", "j_d2i", "j_round", "j_double_bits", "j_bits_double", "j_float_bits",
           "j_bits_float", "bytes_get_float_le", "bytes_put_float_le", "bytes_get_double_le",
           "bytes_put_double_le", "db_set_reclaim_internal_fraction", "db_internal_fraction",
           "bergdb_set_reclaim_internal_fraction"]

# <math.h>'s floating functions (and their f and l forms), refused as calls (a field
# named floor is not one), and its floating macros.
FUNCS = ["floor", "ceil", "round", "lround", "llround", "trunc", "rint", "lrint", "llrint",
         "nearbyint", "fma", "sqrt", "cbrt", "pow", "exp", "exp2", "expm1", "log", "log2",
         "log10", "log1p", "fabs", "fmod", "remainder", "modf", "frexp", "ldexp", "scalbn",
         "fmin", "fmax", "fdim", "hypot", "sin", "cos", "tan", "atan", "atan2", "copysign",
         "nextafter", "isnan", "isinf", "isfinite", "isnormal", "signbit", "fpclassify"]
MACROS = ["NAN", "INFINITY", "HUGE_VAL", "HUGE_VALF", "HUGE_VALL", "FLT_EVAL_METHOD"]

RULES = [
    ("a floating type", re.compile(r"\b(double|float)\b")),
    ("a floating literal", re.compile(
        r"(?<![\w.])(0[xX][0-9a-fA-F]*\.?[0-9a-fA-F]*[pP][+-]?\d+"
        r"|\d+\.\d*([eE][+-]?\d+)?[fFlL]?|\.\d+([eE][+-]?\d+)?[fFlL]?|\d+[eE][+-]?\d+[fFlL]?)")),
    ("<math.h>", re.compile(r"#\s*include\s*<(math|tgmath|float|fenv)\.h>")),
    ("a floating function of <math.h>", re.compile(
        r"(?<![\w.>])(" + "|".join(f + "[fl]?" for f in FUNCS) + r")\s*\(")),
    ("a floating macro of <math.h>", re.compile(r"\b(" + "|".join(MACROS) + r")\b")),
    ("a function of floating point, allowed only in its places", re.compile(
        r"\b(" + "|".join(GUARDED) + r")\b")),
]


def strip(text):
    """The text with comments, string literals and character literals blanked,
    line breaks kept."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif c in "\"'":
            j = i + 1
            while j < n and text[j] != c and text[j] != "\n":
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(c + re.sub(r"[^\n]", " ", text[i + 1:j - 1]) + c)
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


def allowed_lines(name, lines):
    """The line numbers (1-based) of 'lines' of src/NAME in an allowed place, with the
    places of the file that were found."""
    ok, used = set(), []
    for f, kind, what, _ in ALLOWED:
        if f != name:
            continue
        if kind == "file":
            ok.update(range(1, len(lines) + 1))
            used.append((f, kind, what))
        elif kind == "line":
            hit = [i + 1 for i, line in enumerate(lines) if re.search(what, line)]
            ok.update(hit)
            if hit:
                used.append((f, kind, what))
        else:
            start = None
            for i, line in enumerate(lines):
                if start is None:
                    if (re.match(r"[A-Za-z_]", line) and re.search(r"\b" + what + r"\s*\(", line)
                            and not line.rstrip().endswith(";")):
                        start = i
                elif line.startswith("}"):
                    ok.update(range(start + 1, i + 2))
                    used.append((f, kind, what))
                    start = None
                    break
    return ok, used


def check(name, text):
    """The uses refused in the file src/NAME with the contents 'text': (line, reason,
    code); and the allowed places used."""
    lines = strip(text).split("\n")
    ok, used = allowed_lines(name, lines)
    refused = []
    for i, line in enumerate(lines):
        if i + 1 in ok:
            continue
        for reason, rx in RULES:
            if rx.search(line):
                refused.append((i + 1, reason, text.split("\n")[i].strip()))
                break
    return refused, used


SELF_TEST = [
    # (file, code, refused?)
    ("x.c", "int64_t a = b * 3 / 4;\n", False),
    ("x.c", "double share = 0;\n", True),
    ("x.c", "int64_t a = j_d2l(b * 0.75);\n", True),
    ("x.c", "int64_t a = (int64_t) (b * 75e-2);\n", True),
    ("x.c", "int64_t u = x * 0x1.0p-53;\n", True),
    ("x.c", "int64_t a = llround(b);\n", True),
    ("x.c", "#include <math.h>\n", True),
    ("x.c", "if (isnan(x)) {\n", True),
    ("x.c", "int64_t a = floor (b);\n", True),
    ("x.c", "x = NAN;\n", True),
    ("x.c", "ev->floor = after; int64_t floor;\n", False),
    ("x.c", "s->f = db_internal_fraction(db);\n", True),
    ("x.c", "/* 0.25 exactly, a double before */ int32_t f = 16384;\n", False),
    ("x.c", "err(\"value, %.17g, 1.5 double\");\n", False),
    ("x.c", "int64_t a = J64(0x9E3779B97F4A7C15);\n", False),
    ("x.c", "int64_t a = INT64_C(1) << 52;\n", False),
    ("db.c", "enum err_code db_set_reclaim_internal_fraction(struct db *db, double f) {\n"
             "    if (isnan(f) || f < 0.001) {\n        return 1;\n    }\n}\n", False),
    ("db.c", "enum err_code db_set_reclaim_internal_fraction(struct db *db, double f) {\n"
             "    return 0;\n}\nint64_t other(void) {\n    return j_round(0.5);\n}\n", True),
    ("db.h", "enum err_code db_set_reclaim_internal_fraction(struct db *db, double f);\n", False),
    ("db.h", "double other(void);\n", True),
]


def self_test():
    bad = 0
    for name, code, want in SELF_TEST:
        got = bool(check(name, code)[0])
        if got != want:
            print("SELF-TEST: %s %s: refused %s, should be %s" % (name, code.strip(), got, want))
            bad += 1
    return bad


def main():
    c = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(
        os.path.abspath(__file__)))
    src = os.path.join(c, "src")
    if self_test():
        print("DOUBLES FAILED: the self-test")
        return 1
    files = sorted(f for f in os.listdir(src) if f.endswith((".c", ".h")))
    nrefused, places = 0, []
    for name in files:
        with open(os.path.join(src, name), encoding="utf-8") as fh:
            refused, used = check(name, fh.read())
        places.extend(used)
        for line, reason, code in refused:
            print("REFUSED src/%s:%d: %s: %s" % (name, line, reason, code))
            nrefused += 1
    unused = [a[:3] for a in ALLOWED if a[:3] not in places]
    for f, kind, what in unused:
        print("UNUSED allowed place: src/%s, %s %s" % (f, kind, what or ""))
    if nrefused or unused:
        print("DOUBLES FAILED: %d uses refused, %d allowed places unused, in %d files of src/"
              % (nrefused, len(unused), len(files)))
        return 1
    print("doubles ok: %d files of src/, floating point only in the %d allowed places "
          "(bergdb 005-79)" % (len(files), len(ALLOWED)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
