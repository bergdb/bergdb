#!/usr/bin/env python3
# bergdb 024-17, section 5.2a: the node bound for Frans's limits of 17:41,
# L1 = 500 operations, L2 = 111 bytes (16 segments). Arithmetic only; the
# functions are bound112.py's. Run: python3 bound500.py
import math
import importlib.util, os, sys, io, contextlib
sys.dont_write_bytecode = True

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("b112", os.path.join(here, "bound112.py"))
b = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(b)

N, K = 500, 111
s = b.segs(K)
print("L1 = %d, L2 = %d bytes, %d segments" % (N, K, s))
print()
print("Per operation, node size 30 (3,700,852 nodes fit):")
fit = b.nodes_fit(30)
for H in (22, 21, 20, 19):
    f7 = 20 * s * (H + 2) + 14
    qa = 8 * s * (H + 2) + 14
    w = b.java_single_delete(s, H, 10)
    print("  H=%d: TP26 f7 %5d/op -> %4d ops (%+.1f %% over 500); with q %5d -> %4d (%+.1f %%);"
          " Java one delete %5d -> %4d"
          % (H, f7, fit // f7, 100 * (fit // f7 / N - 1), qa, fit // qa,
             100 * (fit // qa / N - 1), w, fit // w))
print()
print("Every node size, H = 1 + log_m(2^60) and BU1's 1 + log_m(2^59) (the second H):")
CQ = {8: 14, 14: 9, 30: 8, 62: 8}       # the count with q, nodes a level, restated
for B in (8, 14, 30, 62):
    m, h, c, q = b.thresholds(B)
    fit = b.nodes_fit(B)
    for H in (b.height(m), b.height(m, 59)):
        f7 = 20 * s * (H + 2) + 14
        qa = CQ[B] * s * (H + 2) + 14
        w = b.java_single_delete(s, H, q)
        print("  B=%2d H=%2d: TP26 f7 %6d -> %4d ops; with q (%2d a level) %6d -> %4d; Java one delete %6d -> %4d%s"
              % (B, H, f7, fit // f7, CQ[B], qa, fit // qa, w, fit // w,
                 "" if qa >= w else "  (q form BELOW Java's count)"))
print()
print("L3 (sum bound, S <= L3 / 7 + n, n = 500):")
for kib in (48, 52, 54, 56, 64):
    L3 = kib * 1024
    S = L3 // 7 + N
    row = "  L3 %2d KiB (%6d B, %3d keys of 111): S %5d;" % (kib, L3, L3 // K, S)
    for B in (8, 14, 30, 62):
        m, h, c, q = b.thresholds(B)
        fit = b.nodes_fit(B)
        H = b.height(m)
        f7 = 20 * (H + 2) * S + 14 * N
        qa = CQ[B] * (H + 2) * S + 14 * N
        row += " B%d f7 %+.0f%% q %+.0f%%;" % (B, 100 * (1 - f7 / fit), 100 * (1 - qa / fit))
    print(row)
fit = b.nodes_fit(30)
for kib in (56,):
    S = kib * 1024 // 7 + N
    for H in (22, 21, 20, 19):
        f7 = 20 * (H + 2) * S + 14 * N
        qa = 8 * (H + 2) * S + 14 * N
        print("  L3 56 KiB, B=30, H=%d: f7 %d nodes (%.1f %% under), with q %d (%.1f %% under)"
              % (H, f7, 100 * (1 - f7 / fit), qa, 100 * (1 - qa / fit)))
    Smax = (fit - 14 * N) // (20 * 24)
    print("  TP26 f7, H=22: S <= %d, L3 <= %d bytes" % (Smax, (Smax - N) * 7))
    Smax = (fit - 14 * N) // (20 * 22)
    print("  TP26 f7, H=20: S <= %d, L3 <= %d bytes" % (Smax, (Smax - N) * 7))
print()
L5, L3 = 32 * 2**20, 56 * 1024
own = L5 + N * (8 + 44) + L3 // 7
S = L3 // 7 + N
dirty = (8 * 24 * S + 14 * N) * b.node_bytes(30) + b.TOP
print("Record, B=30, H=22, with q: own %d + dirty %d = %d (%.1f %% of 2^31 - 9)"
      % (own, dirty, own + dirty, 100 * (own + dirty) / b.R))
dirty7 = (20 * 24 * S + 14 * N) * b.node_bytes(30) + b.TOP
print("Record, B=30, H=22, TP26 f7: own + dirty = %d (%.1f %%)"
      % (own + dirty7, 100 * (own + dirty7) / b.R))
print()
for l6 in (111, 112):
    e = 11 + 255 + 1 + 8 + l6 + K
    print("L6 %d: entry %d bytes, %d segments; objects with one index at the largest, L3 56 KiB: %d;"
          " two: %d" % (l6, e, b.segs(e), L3 // (K + 2 * e), L3 // (K + 4 * e)))
print()
mb = 8 * 2**20 / 1e6
print("8 MiB = %.2f MB: Fletcher-16 %.0f ms, CRC32C %.1f ms (F6: 5.7 and 0.13 ms a MB)"
      % (mb, 5.7 * mb, 0.13 * mb))
