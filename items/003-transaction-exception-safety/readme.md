003-transaction-exception-safety
================================

Created 2026-10-17 by Frans Lundberg. Status: open.

A transaction that throws inside `Db.putKvs` is half committed: its time
becomes readable with some of its changes in memory, and the next
transaction writes its leftovers as its own. Register row M49 of
[docs/level4-alignment.md](../../docs/level4-alignment.md). Found in item 002
([02-report.md](../002-top-node-ordinal-bound/02-report.md), section 8).
Document it now; fix it later, before item 001's J3 (index nodes evicted, so
loads in the writer), without disturbing item 001's work on `Db`.


Files
=====

* [01-finding.md](01-finding.md). 003-01, the finding: the reproduction,
  the causes in the code, what can trigger it today and with Level 4, the
  fix options with a recommendation, and a test plan.


Log
===

2026-10-17. Created the item. Claude wrote 003-01. Item 001 had already
registered the defect as M49 (commit `530028d`), with "before J3".
