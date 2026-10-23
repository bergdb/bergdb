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
