"""Writes the ProGuard configurations for 005-10's member-level analysis.

Usage: python3 -I pg.py <bergdb clone> <out dir> <jmods dir>

Three configurations, each a set of entry points; ProGuard's -printusage
then lists the classes and members that the entry points do not reach:

  api: the public API only (public and protected members of the public
       classes in bergdb.pub and bergdb.pub.util);
  run: api, the classes the scripts in java/stress start, and the unit and
       f-tests (bergdb.dev.Unit, bergdb.dev.F) with their test methods;
  noapi: run without the public API, to see what of the API nothing here
       uses;
  all: run, every main method, bergdb.dev.Run, and the test methods of
       every group (perf, night too);
  keep: all without the perf tests (005-10's proposal removes them).

It also writes tests.tsv: every test method of the packs, with its groups.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import classfile  # noqa: E402

repo, out, jmods = sys.argv[1], sys.argv[2], sys.argv[3]
java = os.path.join(repo, "java")

classes = {}
for base in ("build/classes", "build/stress"):
    for p in classfile.walk(os.path.join(java, base), skip=("bergdb/icu50",)):
        c = classfile.parse(p)
        classes[c["name"]] = c

S = classfile.ACC_STATIC
NANO = "Lbergdb/nanotest/Nano;"
ENV = "(Lbergdb/nanotest/TestEnvironment;)V"

packs = [n for n, c in classes.items()
         if "bergdb.nanotest.IPack" in c["interfaces"]
         and n.split(".")[-1] in ("Pack", "PackForPub")]
listed = set()
for p in packs:
    listed |= {r for r in classes[p]["refs"] if r in classes and r != p}


def groups_of(m):
    for t, vals in m["annotations"]:
        if t == NANO:
            if not m["access"] & S:
                return None
            return set((vals.get("value") or "unit").split())
    name = m["name"]
    if (name.startswith("test") and len(name) > 4 and m["access"] & S
            and m["desc"] in ("()V", ENV)):
        return {"unit"}
    return None


tests = []
for n in sorted(listed):
    for m in classes[n]["methods"]:
        g = groups_of(m)
        if g:
            tests.append((n, m["name"], m["desc"], g))


def java_type(d, i=0):
    """Returns (java type name, next index) for the descriptor at i."""
    dims = 0
    while d[i] == "[":
        dims += 1
        i += 1
    prim = {"B": "byte", "C": "char", "D": "double", "F": "float", "I": "int",
            "J": "long", "S": "short", "Z": "boolean", "V": "void"}
    if d[i] == "L":
        j = d.index(";", i)
        t = d[i + 1:j].replace("/", ".")
        i = j + 1
    else:
        t = prim[d[i]]
        i += 1
    return t + "[]" * dims, i


def method_spec(name, desc):
    params = []
    i = 1
    while desc[i] != ")":
        t, i = java_type(desc, i)
        params.append(t)
    ret, _ = java_type(desc, i + 1)
    return "%s %s(%s);" % (ret, name, ",".join(params))


def mains():
    return sorted(n for n, c in classes.items()
                  if any(m["name"] == "main" and m["desc"] == "([Ljava/lang/String;)V"
                         and m["access"] & S for m in c["methods"]))


script_mains = set()
for f in sorted(os.listdir(os.path.join(java, "stress"))):
    if f.endswith(".sh"):
        for line in open(os.path.join(java, "stress", f), encoding="utf-8"):
            if not line.lstrip().startswith("#"):
                for m in re.finditer(r"\b(?:bergdb(?:\.[a-z0-9]+)+\.)?[A-Z]\w*", line):
                    if m.group(0) in classes:
                        script_mains.add(m.group(0))

common = """
-injars '{java}/build/classes'(!bergdb/icu50/**,!META-INF/**)
-injars '{java}/build/stress'
-outjars '{out}/pg-{name}'
-libraryjars '{java}/in/icu-for-bergdb.jar'
{libs}
-dontobfuscate
-dontoptimize
-dontpreverify
-dontnote **
-dontwarn org.junit.**
-keepattributes *Annotation*,Signature,InnerClasses,EnclosingMethod,SourceFile,LineNumberTable
-printusage '{out}/usage-{name}.txt'
-printseeds '{out}/seeds-{name}.txt'

# The annotation that marks tests, read by reflection.
-keep @interface bergdb.nanotest.Nano {{ *; }}
-keepclassmembers enum * {{
    public static **[] values();
    public static ** valueOf(java.lang.String);
}}
-keepclassmembers class * implements java.io.Serializable {{
    static final long serialVersionUID;
    private void writeObject(java.io.ObjectOutputStream);
    private void readObject(java.io.ObjectInputStream);
    java.lang.Object writeReplace();
    java.lang.Object readResolve();
}}

{api}
# JMX reads an MBean interface by reflection, for a class that implements it.
-if class * implements **MBean
-keep interface <2>MBean {{ *; }}

# Reflection: OptionalIcuCollatorFactory loads this class by name.
-keep class bergdb.pubimpicu.IcuCollatorFactory {{ <init>(); }}
"""

libs = "\n".join("-libraryjars '%s/%s.jmod'(!**.jar;!module-info.class)" % (jmods, m)
                 for m in ("java.base", "java.desktop", "java.instrument",
                           "java.management", "jdk.management"))


def keep_main(n):
    return "-keep class %s { public static void main(java.lang.String[]); }" % n


def keep_tests(groups):
    by = {}
    for n, name, desc, g in tests:
        if groups is None or g & groups:
            by.setdefault(n, []).append(method_spec(name, desc))
    return "\n".join("-keep class %s {\n    %s\n}" % (n, "\n    ".join(ms))
                     for n, ms in sorted(by.items()))


configs = {
    "api": "",
    "run": "\n".join([keep_main(n) for n in sorted(script_mains | {"bergdb.dev.Unit", "bergdb.dev.F"})]
                     + [keep_tests({"unit", "f"})]),
    "all": "\n".join([keep_main(n) for n in mains()]
                     + [keep_tests(None)]),
    "keep": "\n".join([keep_main(n) for n in mains()]
                      + [keep_tests({"unit", "f", "night"})]),
}

configs["noapi"] = configs["run"]
os.makedirs(out, exist_ok=True)
for name, extra in configs.items():
    with open(os.path.join(out, "pg-%s.pro" % name), "w") as w:
        api = ("" if name == "noapi" else
               "# The public API.\n"
               "-keep public class bergdb.pub.*, bergdb.pub.util.* { public protected *; }\n")
        w.write(common.format(java=java, out=out, name=name, libs=libs, api=api))
        w.write("\n# Entry points of this configuration.\n" + extra + "\n")

with open(os.path.join(out, "tests.tsv"), "w") as w:
    for n, name, desc, g in tests:
        w.write("%s\t%s\t%s\t%s\n" % (n, name, desc, " ".join(sorted(g))))

print("packs", len(packs), "listed classes", len(listed), "test methods", len(tests))
print("script mains", len(script_mains), "mains", len(mains()))
count = {}
for _, _, _, g in tests:
    for x in g:
        count[x] = count.get(x, 0) + 1
print("tests per group", count)
