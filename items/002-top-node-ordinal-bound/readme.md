002-top-node-ordinal-bound
==========================

Created 2026-10-17 by Frans Lundberg. Status: open.

The top node ordinal bound, register row M46 of
[docs/level4-alignment.md](../../docs/level4-alignment.md): top node
ordinals are bounded by `TopNode.MAX_TOP_NODE_ID_VALUE`, 2^30 − 1, over the
database's whole life, and reclaim bounds the stream but not the ordinals.
Understand the bound and what Java does at it, and decide: a wider ordinal,
a clean refusal, or something else.


Files
=====

* [01-sources.md](01-sources.md). 002-01, the documentation gathered at the
  start: the current code, the 2026 findings, and the 2012 to 2015 design
  notes and history.
* [02-report.md](02-report.md). 002-02, the report: whether the bound is good
  enough, when it is reached, widening the ordinal to 48 bits (with a patch),
  and the 2012 idea of decreasing the height. Its probes, patches and outputs
  are in [02-report/](02-report/).


Log
===

2026-10-17. Created the item. Claude gathered the documentation (002-01).

2026-10-17. Claude studied the bound and wrote the report (002-02), working
unattended at Frans's request. Recommended: widen to 48 bits with a guard at
the end (no format change); register a related defect (a transaction that
throws in the middle is half committed); leave the height decrease.
