"""Compare StreamDigest's logical streams, reporting physical cuts separately.

Usage: python3 compare-digests.py MAIN.txt AFTER.txt
Physical reclaim timing is outside stream determinism (bergdb 005-72).
"""
import sys


def read(path):
    rows = {}
    with open(path) as source:
        for line in source:
            if line.startswith("DIGEST "):
                parts = line.split()
                key = " ".join(parts[1:3])
                assert key not in rows, key
                rows[key] = dict(part.split("=", 1) for part in parts[3:])
    return rows


a, b = map(read, sys.argv[1:])
assert len(a) == len(b) == 36 and a.keys() == b.keys(), "expected 36 matching cases"
fields = ("length", "firstAvailablePos", "firstAvailableTime", "sha256")
for key in a:
    for field in fields:
        assert a[key][field] == b[key][field], (key, field, a[key][field], b[key][field])
print("LOGICAL DIGESTS IDENTICAL (36 of 36)")
print("Compared length, firstAvailablePos, firstAvailableTime, sha256 from the decided cut.")
physical = [key for key in a if a[key]["firstPos"] != b[key]["firstPos"]]
print("Physical-cut differences:", len(physical))
for key in physical:
    print(key, a[key]["firstPos"], "->", b[key]["firstPos"])
