#!/usr/bin/env python3
# bergdb 024-17, section 5.2a: the node bound for keys of at most 112 bytes.
# Arithmetic only; Java's constants as in 024-21's branch (Db.checkDirtyNodes,
# Dag.dirtyNodeBound, Dag's thresholds 8/17/17). Run: python3 bound112.py
import math

R = 2**31 - 9                         # StoredTrans.MAX_RECORD_SIZE
DIRTY = R - R // 16                   # StoredTrans.dirtyLimit()
TOP = 2 * (40 + 16 * 64 + 16)         # Db.checkDirtyNodes' topBytes


def node_bytes(b):                    # Db.checkDirtyNodes' nodeBytes
    return 32 + 16 * (b + 1) + 16


def nodes_fit(b):
    return (DIRTY - TOP) // node_bytes(b)


def segs(k):                          # Keys.toSegments: k / 7 + 1
    return k // 7 + 1


def thresholds(b):                    # Dag.splitAbove, minFill, mergeCap
    h, m, c = 17 * b // 30, max(2, 8 * b // 30), 17 * b // 30
    q = max(2, min(b // 2, b - h, b - c) - 3)    # roomAfterReplacement
    return m, h, c, q


def height(m, log2k=60):              # 1 + log_m(K), K < 2^60 klongs (5.2)
    return math.floor(1 + log2k / math.log2(m))


def per_level(q):
    # Java's format-7 count, a delete, per node of its path, amortized:
    # 1 walked, 4 for the merges, overflows + 1 <= 2 + k / q with k = 4 +
    # the child's overflows + 1: x = 2 + (4 + x) / q.
    return 5 + 2 * (q + 2) / (q - 1)


def java_single_delete(s, H, q):
    # Java's dirtyNodeBound for one delete on a path of full nodes (no room),
    # s segment trees of height H, inner collapses H in each tree below a
    # segment leaf. Disjoint paths are the worst case per operation.
    path = s * (H + 1)
    klongs = [4] * path
    for i in range(s - 1):            # the segment leaf of tree i
        klongs[(i + 1) * (H + 1) - 1] += H
    count = path
    carry = 0
    for d in range(path - 1, -1, -1):
        k = klongs[d] + carry
        ov = 1 + k // q               # 1 + (k + 1 - 0 - 1) / q
        count += ov + 1
        carry = ov + 1
        if d == 0:
            count += ov               # new roots
    count += 4 * (path + 2)           # the merges
    return count


def row(label, per_op, fit):
    return "%-44s %8d %8d" % (label, per_op, fit // per_op)


print("dirtyLimit %d bytes; top nodes %d bytes" % (DIRTY, TOP))
print("segments: 111 B -> %d, 112 B -> %d, 251 B -> %d, 252 B -> %d, 256 B -> %d"
      % (segs(111), segs(112), segs(251), segs(252), segs(256)))
print()
print("Node size 30: nodes a record's 15/16 holds: %d" % nodes_fit(30))
print("%-44s %8s %8s" % ("count, a segment / key / H", "nodes/op", "most ops"))
fit = nodes_fit(30)
for k in (112, 111, 256):
    s = segs(k)
    for H in (22, 21, 19):
        print(row("TP26 2026.4, 8 (H+2)+2,   %3d B (s=%d) H=%d" % (k, s, H),
                  8 * s * (H + 2) + 2, fit))
        print(row("TP26 format 7, 20 (H+2)+14, %3d B H=%d" % (k, H),
                  20 * s * (H + 2) + 14, fit))
        print(row("q-aware, 8 (H+2)+14,      %3d B H=%d" % (k, H),
                  8 * s * (H + 2) + 14, fit))
        print(row("Java walk, one delete, full path, %3d B H=%d" % (k, H),
                  java_single_delete(s, H, 10), fit))
    print()

print("Every node size (keys of 112 bytes, s = 17; H = 1 + log_m(2^60)):")
print("%3s %5s %3s %3s %3s %3s %10s %3s | %7s %5s | %7s %5s | %7s %5s | %7s %5s"
      % ("B", "bytes", "m", "h", "c", "q", "nodes", "H", "TP26", "ops",
         "TP26f7", "ops", "q-aware", "ops", "walk", "ops"))
for b in (8, 14, 30, 62):
    m, h, c, q = thresholds(b)
    H = height(m)
    s = segs(112)
    fit = nodes_fit(b)
    pl = math.ceil(per_level(q))
    a = 8 * s * (H + 2) + 2
    f7 = 20 * s * (H + 2) + 14
    qa = pl * s * (H + 2) + 14
    w = java_single_delete(s, H, q)
    print("%3d %5d %3d %3d %3d %3d %10d %3d | %7d %5d | %7d %5d | %7d %5d | %7d %5d"
          % (b, node_bytes(b), m, h, c, q, fit, H, a, fit // a, f7, fit // f7,
             qa, fit // qa, w, fit // w))
    print("    per level (amortized) at q = %d: %.2f, rounded up %d" % (q, per_level(q), pl))
print()
print("The same with K < 2^48 klongs (a stream under 2 PiB):")
for b in (8, 14, 30, 62):
    m, h, c, q = thresholds(b)
    H = height(m, 48)
    s = segs(112)
    fit = nodes_fit(b)
    pl = math.ceil(per_level(q))
    qa = pl * s * (H + 2) + 14
    print("  B=%2d H=%2d q-aware %6d nodes/op, %5d ops" % (b, H, qa, fit // qa))
print()

# L3: the key bytes of a transaction, as a sum bound. S <= L3 / 7 + n.
print("L3, node size 30, n = 1,000: nodes <= a (H + 2) S + c n, S <= L3/7 + n")
fit = nodes_fit(30)
for name, a, c in (("TP26 2026.4", 8, 2), ("q-aware", 8, 14), ("TP26 format 7", 20, 14)):
    for H in (22, 19):
        smax = (fit - c * 1000) // (a * (H + 2))
        l3max = (smax - 1000) * 7
        print("  %-14s H=%d: S <= %6d, L3 <= %7d bytes (%.1f KiB)"
              % (name, H, smax, l3max, l3max / 1024))
for kib in (40, 64, 112, 120, 128):
    l3 = kib * 1024
    S = l3 // 7 + 1000
    for name, a, c in (("TP26 2026.4", 8, 2), ("q-aware", 8, 14), ("TP26 format 7", 20, 14)):
        n22 = a * 24 * S + c * 1000
        n19 = a * 21 * S + c * 1000
        print("  L3 %3d KiB: S %6d  %-14s H=22 %9d nodes (%5.1f %% under), H=19 %9d (%5.1f %%)"
              % (kib, S, name, n22, 100 * (1 - n22 / fit), n19, 100 * (1 - n19 / fit)))
print()
# The record: own bytes and one transaction's dirty set (5.3).
L5 = 64 * 2**20
own = L5 + 1000 * (8 + 44) + 112 * 1024 // 7
for kib in (112,):
    S = kib * 1024 // 7 + 1000
    dirty = (8 * 24 * S + 14 * 1000) * node_bytes(30) + TOP
    print("Record at L3 = %d KiB, q-aware, H = 22: own %d + dirty %d = %d of %d (%.1f %% under)"
          % (kib, own, dirty, own + dirty, R, 100 * (1 - (own + dirty) / R)))
print()
# 6.2 (a): index entries at L6.
for l6 in (64, 112, 128, 256):
    entry = 11 + 255 + 1 + 8 + l6 + 112
    print("L6 %3d: the largest entry %4d bytes, %3d segments; objects with one index at L3 = 112 KiB: %d"
          % (l6, entry, segs(entry), 112 * 1024 // (112 + 2 * entry)))
