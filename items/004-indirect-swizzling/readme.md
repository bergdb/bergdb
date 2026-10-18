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


Log
===

2026-10-18. Created the item, at Frans's request after a discussion of
Level 4's caching (the sweep, the multiple parents of the DAG, handles).
Claude studied the subject and wrote 004-01.

2026-10-18. At Frans's request, the measurements repeated on the quiet machine (16:30 to
16:53), with 8 threads added; 004-01 updated to the quiet figures, the first runs kept as
`busy-*.txt`. The conclusions held; the four-thread collapse of today's read path was
smaller than on the busy machine, the eight-thread one larger.
