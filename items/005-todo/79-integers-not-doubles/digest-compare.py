#!/usr/bin/env python3
"""bergdb 005-79: compares the DIGEST lines of two StreamDigest outputs on the
fields that do not depend on timing: length, firstAvailablePos,
firstAvailableTime and sha256 (from the cut that reclaim decided). firstPos and
sha256all, the physical cut and the digest from it, wait for durability, and
differ between runs of the same jar in l3 configurations (005-79's log, 16:15:
l3-node62 restarts, firstPos 8000000 or 9000000 on the base); they are counted
apart. Prints DECIDED DIGESTS IDENTICAL or DECIDED DIGESTS DIFFER, exit status 1
if they differ.

Usage: python3 -I digest-compare.py FILE1 FILE2
"""
import re
import sys

KEYS = ("length", "firstAvailablePos", "firstAvailableTime", "sha256")


def read(path):
    out = {}
    for line in open(path, encoding="utf-8"):
        if line.startswith("DIGEST "):
            parts = line.split()
            fields = dict(p.split("=", 1) for p in parts[3:])
            out[(parts[1], parts[2])] = fields
    return out


def main():
    a, b = read(sys.argv[1]), read(sys.argv[2])
    same = differ = physical = 0
    for key in sorted(set(a) | set(b)):
        x, y = a.get(key), b.get(key)
        if x is None or y is None:
            differ += 1
            print("MISSING %s %s in %s" % (key[0], key[1], sys.argv[1] if x is None else sys.argv[2]))
            continue
        if all(x[k] == y[k] for k in KEYS):
            same += 1
        else:
            differ += 1
            print("DIFFERENT %s %s: %s" % (key[0], key[1], ", ".join(
                "%s %s -> %s" % (k, x[k], y[k]) for k in KEYS if x[k] != y[k])))
        if x["firstPos"] != y["firstPos"] or x["sha256all"] != y["sha256all"]:
            physical += 1
            print("  physical cut %s %s: firstPos %s -> %s" % (key[0], key[1], x["firstPos"], y["firstPos"]))
    print("%s (%d of %d; the physical cut differs in %d, timing)" % (
        "DECIDED DIGESTS IDENTICAL" if differ == 0 else "DECIDED DIGESTS DIFFER",
        same, same + differ, physical))
    return 1 if differ else 0


sys.exit(main())
