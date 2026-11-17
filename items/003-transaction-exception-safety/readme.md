003-transaction-exception-safety
================================

Created 2026-10-17 by Frans Lundberg. Status: done.

A transaction that throws inside `Db.putKvs` is half committed: its time
becomes readable with some of its changes in memory, and the next
transaction writes its leftovers as its own. Register row M49 of
[docs/level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md). Found in item 002
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
registered the defect as M49 (commit `1286297`), with "before J3".

2026-10-22. Done: fixed in bergdb 005-01
([../005-todo/01-fix-m49-exception-safety.md](../005-todo/01-fix-m49-exception-safety.md)),
as 003-01 recommends with reads refused too, and without 5.2, as Frans
decided: a transaction that throws after its go point fails the database,
which refuses every later transaction and read until it is restarted. M49 is
closed. Claude added notes of that day to 003-01's sections 3 to 5.
