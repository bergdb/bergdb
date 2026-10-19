002-top-node-ordinal-bound
==========================

Created 2026-10-17 by Frans Lundberg. Status: done.

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

2026-10-17. Frans: left for later, not planned. The item stays open.

2026-10-19. Done: fixed as 002-02 recommends, in bergdb 005-02
([../005-todo/02-fix-m46-ordinal-bound.md](../005-todo/02-fix-m46-ordinal-bound.md)):
the ordinal is a `long` below 2^48, without a format change, and a user
transaction is refused before it changes anything 1,024 below the bound. M46
is closed. The height decrease (002-02, section 7) was left, as recommended.
