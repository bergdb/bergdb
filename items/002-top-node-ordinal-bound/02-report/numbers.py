"""Bergdb item 002 (M46): the numbers of the report."""
import datetime
DAY = 86400.0
YEAR = 365.25 * DAY

def fmt(sec):
    if sec < 2 * DAY:
        return "%.0f hours" % (sec / 3600)
    if sec < 2 * YEAR:
        return "%.0f days" % (sec / DAY)
    return "%.0f years" % (sec / YEAR) if sec < 1e4 * YEAR else "%.1e years" % (sec / YEAR)

TOPS30 = 2 ** 30          # ordinals 0 .. 2^30 - 1
TOPS48 = 2 ** 48
print("2^30 =", TOPS30, " 2^48 =", TOPS48)
rates = [10, 100, 1000, 10000, 100000]
rows = [("one hot key, node size 30", 15), ("one hot key, node size 30, reclaim on", 14),
        ("10 keys, node size 30", 10), ("one hot key, node size 8", 4), ("one hot key, node size 8, reclaim on", 3),
        ("1,000 keys, node size 30, reclaim on", 654), ("1,000 keys, node size 30", 965),
        ("100,000 keys, node size 30", 7143)]
print("time to 2^30 top nodes")
for name, tpt in rows:
    print("%-40s %6d " % (name, tpt) + "  ".join("%12s" % fmt(TOPS30 * tpt / r) for r in rates))
# Full speed, measured (in memory, one writer, nice 19 on a loaded machine)
for name, tps, tpt in [("node 30, one key", 153003, 15), ("node 8, one key", 77508, 4), ("node 14, one key", 122065, 7),
                       ("node 62, one key", 149426, 31), ("node 30, 10 keys", 126008, 10)]:
    tops_s = tps / tpt
    print("full speed %-18s %7.0f tx/s %7.0f tops/s: 2^30 in %s, 2^48 in %s" % (name, tps, tops_s,
          fmt(TOPS30 / tops_s), fmt(TOPS48 / tops_s)))
# The database clock: 100 ns units, 2^56 - 1 at most (Klong.MAX_TIME).
end = datetime.datetime(1970, 1, 1) + datetime.timedelta(seconds=(2 ** 56 - 1) * 1e-7)
print("clock end:", end)
now = datetime.datetime(2026, 10, 17)
left = (end - now).total_seconds()
print("seconds from 2026-10-17 to the clock end: %.3e (%.0f years)" % (left, left / YEAR))
print("tops/s needed to use 2^48 before the clock ends: %.0f" % (TOPS48 / left))
# Today: heap per transaction, one hot key, node 30: 251 bytes (measured, 1M transactions)
for heap_gb in [8, 32, 128]:
    tx = heap_gb * 1e9 / 251
    print("heap %d GB: %.2e transactions, %.2e top nodes (2^%.1f) at 15 per top" % (heap_gb, tx, tx / 15,
          __import__('math').log2(tx / 15)))
print("heap for 2^30 tops at 15 tx/top and 251 B/tx: %.1f TB" % (TOPS30 * 15 * 251 / 1e12))
# Top node bytes: 40 + 16 per slot; height = bit length of the ordinal
for h in [15, 16, 30, 31, 40, 48]:
    print("height %d: %d bytes" % (h, 40 + 16 * h))

# The height decrease and set-only slots, in bytes written per transaction, for one hot key
# at ordinals 2^30 to 2^31 (height 31). Measured (M46Bytes, height 15 to 17): bytes per
# transaction besides top nodes, node size 30: 148.8 - 17.0; node size 8: 215.4 - 71.8.
# Average bytes per top node from height_decrease.py, age 2^30: full 536; dropped 328
# (window 2^16), 392 (2^20); set-only 297; both 184 (2^16), 216 (2^20).
print()
for node, tpt, rest in [(30, 15, 148.8 - 17.0), (8, 4, 215.4 - 71.8)]:
    full = 536 / tpt
    total = rest + full
    print("node %d: %.1f bytes per transaction at ordinal 2^30, top nodes %.0f%% of them" % (node, total, 100 * full / total))
    for name, b in [("dropped, window 2^16", 328), ("dropped, window 2^20", 392), ("set-only", 297),
                    ("both, window 2^16", 184), ("both, window 2^20", 216)]:
        saved = full - b / tpt
        print("   %-22s saves %5.1f bytes per transaction, %4.1f%%" % (name, saved, 100 * saved / total))
for w in [16, 20]:
    print("window 2^%d top nodes at 1,000 tx/s, one key, node size 30: %.0f minutes of transactions" % (w, (2 ** w) * 15 / 1000 / 60))
