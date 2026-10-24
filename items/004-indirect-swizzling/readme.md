004-indirect-swizzling
======================

Created 2026-10-18 by Frans Lundberg. Status: open.

Indirect swizzling for BergDB: memory pointers that go through a small
per-node handle (a descriptor, a mapping-table entry) instead of straight to
the node, so that a node can be evicted or replaced without finding the
pointers to it. The literature, measurements of what it would cost, and its
possible use in BergDB, with the pros and cons.


Files
=====

* [01-report.md](01-report.md). 004-01, the report: the literature with
  references, BergDB's caching in its terms, measurements (a microbenchmark
  of the pointer follow, a census of BergDB's index and the cost of its read
  path today), a design sketch for BergDB, pros and cons, the alternatives
  and a recommendation. Its tools and raw outputs are in
  [01-report/](01-report/).
* [02-scale-tests.md](02-scale-tests.md). 004-02, measurements at scale and on a second
  machine (Frans's VPS, s1): 004-01's benchmarks on x86 Linux, a handle's place after
  garbage collections, and BergDB's gets at 1M to 100M keys in memory, from the OS cache
  and from the device. Tools and scripts in [02-scale-tests/](02-scale-tests/).


Log
===

2026-10-18. Created the item, at Frans's request after a discussion of
Level 4's caching (the sweep, the multiple parents of the DAG, handles).
Claude studied the subject and wrote 004-01.

2026-10-18. At Frans's request, the measurements repeated on the quiet machine (16:30 to
16:53), with 8 threads added; 004-01 updated to the quiet figures, the first runs kept as
`busy-*.txt`. The conclusions held; the four-thread collapse of today's read path was
smaller than on the busy machine, the eight-thread one larger.

2026-10-23. Created 004-02 at Frans's request, after his comments on 004-01: tests on a
second machine (his VPS, s1) and at 1M to 100M keys. Claude wrote the plan; nothing run
yet. s1 was looked at read only (hardware, load, free disk).

2026-10-23. Frans approved 004-02's plan (10:18), with 24-byte keys. Claude installed
OpenJDK 27 on s1 (`/opt/bergdb-bench`), wrote the tools (ScaleBench, DiskBaseline, the
aging option of IndirectionBench) and started the runs: part A's first session on s1 at
10:24.

2026-10-23. 004-02's runs: s1 from 10:24 (parts A, B, C, then D at 0.1M to 10M keys; the
30M load stopped at 21:53 after 9 hours at 18.46M keys, under 100 puts a second); F53 from
17:03 to 21:51, once the other sessions were idle (the quiet rules changed at 14:10 and
14:40, see 004-02 section 4). Results in 004-02 section 10: in memory a get grows by about
0.5 µs per tenfold (0.38 µs at 0.1M keys, 1.92 at 50M on F53); from s1's disk 0.37 to 0.72
ms; the worst case is the sweep (0.5 s to 266 s); G1's evacuation puts handles next to their
objects.

2026-10-23 evening. On s1: reads of the stopped 30M load (its first 18.4M keys; p50 0.67 to
0.88 ms from the device), the repeats, part A's second session. A cold-cache startup takes
minutes on s1 (175 to 194 s at 10M keys): `DbStarter.linkD` reads one header per pointer of
D (004-02, 10.5.8). Part A's third session runs at 08:00 on 2026-10-24.

2026-10-24. 004-02 done: part A's third session on s1 (08:00 to 08:35; one-thread figures
out of cache vary by up to 14 percent between the three sessions), s1's databases deleted.
