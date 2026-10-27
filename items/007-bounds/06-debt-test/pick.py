#!/usr/bin/env python3
"""007-06: where to lower the startup distance in a run like FILE.rec: the update puts before
the record with the largest debt in the update phase, from MIN puts on (a multiple of 1,000).
Usage: pick.py FILE.rec [MIN]"""
import struct
import sys

REC = struct.Struct(">biiiqqqqqqiqi")
data = open(sys.argv[1], "rb").read()
low = int(sys.argv[2]) if len(sys.argv) > 2 else 0
puts = 0
best = (-1, 0)
for r in REC.iter_unpack(data[: len(data) - len(data) % REC.size]):
    if r[0] == 0:
        continue
    if puts >= low and r[11] > best[0]:
        best = (r[11], puts)
    puts += r[1]
print(best[1] // 1000 * 1000, "%.0f MB" % (best[0] / 1e6))
