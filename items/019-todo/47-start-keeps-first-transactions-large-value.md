019-47. Fix: a start keeps a large value of its section's first transaction in memory
=====================================================================================

Status: done 2026-11-09, night 006-15. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: `EvictionAccountingTester`'s recount (harness 6.5, 018-05) failed,
the same for every run, for some seeds of a longer shape than its unit
test's (300 batches of at most 4 transactions, 6 readers):

    seed 1075: batch 5: the recount: pointer 4 of node 5237 holds a value
    of 1126456 bytes (over 1 MiB: not kept)

and so did seeds 1133, 1249, 1267 and 1276 (at batches 37 to 247). With
and without 019-46's fix; found while 019-46 was being reproduced.

Why: the admission rule (bergdb item 009, step 3b; the class comment of
`Eviction`): with eviction on, a value over 1 MiB is not kept in memory
once its record is written, as a read does not cache one
(`Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES`). A value kept against it stays
until the database stops, outside what the capacity controller can take
(015-68's class).


Cause
-----

A start links the values of its startup section's first transaction into
the section's node versions, and the start's admission did not see them.

* A start (`DbStarter.doOrdinaryStartup`) reruns the section's
  transactions but its first (`rerunTransactions`). `createMaps` puts
  into `posMap` the newest version of each index node of the section and
  every value of the first transaction (a value of a later one, which the
  rerun makes again, is left out: `wasCreatedInRerunSection`).
  `createMemoryPointers` then makes every pointer of a section node
  version to a position in `posMap` a memory pointer: to a value of the
  first transaction, the value itself, whatever its size.
* The start's admission (`Db.startInner`, since 015-68:
  `eviction.recordWritten(this, emptyIterator)`) takes only the list of
  the large values that the rerun's pointer listener reported
  (`Eviction.largeValueCreated`). `createMemoryPointers` reports none. So
  a large value of the first transaction stayed in its leaf. In seed 1075
  the leaf 5237, canonical and clean, held the value of 1,126,400 bytes
  at position 7,984 that the restart before last had put (`restart()`
  puts a large value just before a close, half the time); it was not on
  the rerun's list, whose values the admission takes, so the start had
  linked it, and with the pass below it is admitted. In the unit test
  below the start's `StartInfo.startPos` is the large value's
  transaction's position (264, the next transaction at 1,229,992).
* The harness saw it only when the start's budget let it stay: the
  starts before had budgets of 807 and 214 bytes, whose controller took
  the value out with the rest; the start that kept it had no budget
  (`Long.MAX_VALUE`). The unit shape, with its 25 batches and longer
  sections, did not meet it in 900 seeds.

`Eviction.testStartAdmitsLargeValues` (015-68) did not show it: its start
reruns the large values' transaction (the section begins with the
database's creation), so the list has them.


Fix
---

What: the start's admission passes the resident key nodes as the record's
written nodes: `eviction.recordWritten(this, cache.nodes().iterator())`
in `Db.startInner`, in place of the empty iterator. `recordWritten`
already does, for the key nodes of a record that the running database
writes, what the start needs: each pointer to a value over 1 MiB whose
position is in the stream (not a vpos) becomes a stream pointer
(`unswizzleValue`, under the holder's monitor, with the resident bytes
lowered by `Residents.valueOut`), with eviction on; with the schedule
none, nothing, as before.

When and by whom: by the starting thread, under Db's write lock, once,
after `DbStarter` (the rerun, its recount and `linkD`), before the
controller's first batch (`afterTransaction`) and the start's audit; the
same place as 015-68's call.

Why it is enough and right: after the start, a value is resident only
through a pointer of a resident object: one of the node table's live
handles (`cache.nodes()`: the section's canonical objects, D's, the super
root), the objects that `createMemoryPointers` and the rerun changed. A
large value there is one of the first transaction's (now found by the
pass) or one of the rerun's (on the list, as before; the pass finds the
pointer already a stream pointer, and `unswizzleValue` changes nothing
twice). Every value it meets has its record in the stream (the section is
read from it), as `recordWritten` requires; it skips a vpos. A reader
that starts while the start holds the write lock does not keep a large
value either (its cache policy). The cost is one pass over the resident
objects' pointers, as the start's recount (`Residents.resync`) already
makes.

Not changed: `DbStarter.createMemoryPointers`, which could leave such a
pointer a stream pointer itself; the admission is one rule in one place,
and its pass also covers any other way a start makes a large value
resident.

How it is checked:

* `Eviction.testStartAdmitsLargeValuesOfTheSectionsFirstTransaction`
  (unit): a large value put, then, with a startup distance of 200 bytes,
  another transaction, so that the next start's section begins with the
  large value's transaction; the start, with a budget of 100 MB, keeps no
  pointer to a value over 1 MiB, the values read back, the audit at the
  start passes. Before the fix: 1 such pointer.
* `EvictionAccountingTester.testAccountingManyRestarts` (night): the
  longer shape, seeds 1070 to 1079, about 30 s; seed 1075 failed before
  the fix. Seeds 1133, 1249, 1267 and 1276 of that shape pass with it.
* `java/stress/level4.sh` (full, eviction with restarts and the audit):
  LEVEL 4 OK (EvictionInvariance, restarts, crashes and reclaim with the
  audit, 0 failed; ReclaimReaders, 0 failures; conformance C-P and C-H, 0
  of 10,353 transactions; LargerThanMemory). `BEFORE COMMIT OK`.


Log
---

2026-11-09. Found in night 006-15 by the agent of 019-46 (its "Also
found"); the number given by the night's coordinator. Cause found with
the harness's own seeds and recounts after each step of a run: the large
value appeared at a start with no budget, the third of three restarts in
a row; fixed, with the tests above. Status: done; the line in
`releases/next.md` is the coordinator's.
