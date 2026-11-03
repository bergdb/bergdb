015-todo
========

Created 2026-11-03 by Frans Lundberg. Status: open.

A list of things to do on BergDB: issues to fix, things to investigate,
decisions to make. Each entry is a subitem with its own ID and a short
definition: what, why, the questions, when it is done, the first step. An
entry that grows into real work gets an item of its own, linked from here.

It continues 005-todo with a new numbering: the next entry is 015-01, not
005-84. An entry closely related to a 005 entry may still be added to 005,
for now.


The list
========

Two tables: what is left to do, and what is closed. A subitem's own
`Status:` line is the source. When an entry closes (done, dropped or
moved), its row moves from Open to Closed in the same edit, with the date
it closed; Closed is newest first. Files stay where they are, so links to
them keep working.


Open
----

| ID | Kind | What | Status |
|---|---|---|---|
| [015-02](02-c-follows-2026-2.md) | Implement | The C clone follows 2026.2's Java changes | open |
| [015-03](03-lean-follows-005-79.md) | Implement | Lean follows 005-79's integer take | open |
| [015-04](04-deps-helper-rule.md) | Investigate | deps.py counts take and dither as test code | open |
| [015-05](05-empty-or-missing-directory.md) | Decide | A start on an empty or missing directory creates a database | open |
| [015-06](06-refused-start-leaves-file.md) | Fix | A refused start leaves an empty first stream file | in progress |
| [015-08](08-streamdigest-compare-cut.md) | Fix | StreamDigest's compare reports the physical cut, which depends on timing | open |
| [015-11](11-tempdircreator-tmp.md) | Fix | The tests' TempDirCreator writes to /tmp, whatever java.io.tmpdir says | open |
| [015-13](13-handles-not-counted.md) | Fix | The resident bytes count no handle, where 009-02, 4.7 counts them | open |
| [015-14](14-fast-path-jmm-argument.md) | Fix | The fast path's plain reads rest on the address dependency, not the JMM | open |
| [015-18](18-night-large-after-release.md) | Implement | Run night.sh large on the release, after 2026.2 | open |
| [015-19](19-tools-after-005-79.md) | Fix | Tools in items still use what 005-79 removed | open |
| [015-21](21-index-delete-twice.md) | Fix | A second delete job lets the first delete a replacement index | open |
| [015-23](23-refused-index-delete.md) | Fix | A refused index deletion leaves the index active and unmaintained | open |
| [015-25](25-evictor-failure.md) | Fix | An exception in the evictor strands its requests on a dead worker | open |
| [015-26](26-negative-append-length.md) | Fix | A negative append length corrupts FileStream's length | open |
| [015-27](27-failed-append-visible.md) | Decide | A failed append's transaction was already visible to readers | open |


Closed
------

| ID | Kind | What | Status | Closed |
|---|---|---|---|---|
| [015-20](20-filtered-scan-empty-page.md) | Fix | A filtered scan takes an empty page for the end of its range | done | 2026-11-03 |
| [015-22](22-index-build-after-delete.md) | Fix | A deleted index's build job writes into its replacement | done | 2026-11-03 |
| [015-24](24-lock-other-class-loader.md) | Fix | A refused open via another class loader drops the directory lock | done | 2026-11-03 |
| [015-10](10-capacity-test-under-load.md) | Fix | The eviction thread stops after a batch that frees nothing | done | 2026-11-03 |
| [015-16](16-powerloss-cleanup.md) | Investigate | PowerLossTest failed once in its cleanup, "cannot delete test file" | done | 2026-11-03 |
| [015-09](09-reclaim-test-timing.md) | Fix | Reclaim.Tester.testCrashBeforeIterationEnd depends on timing under load | done | 2026-11-03 |
| [015-17](17-read-during-close.md) | Investigate | A read during close fails with "File closed", and close reports it | done | 2026-11-03 |
| [015-15](15-resident-count-drift.md) | Fix | A batch subtracts values never counted; a count driven to 0 stays 0 | done | 2026-11-03 |
| [015-01](01-empty-directory.md) | Fix | A directory without its stream starts as a new one | done | 2026-11-03 |
| [015-12](12-keynode-growth-publication.md) | Fix | After a key node's growth, a reader can see its arrays without contents | done | 2026-11-03 |
| [015-07](07-node-fields-unchecked.md) | Fix | A node's inner fields unchecked; such a read does not fail the database | done | 2026-11-03 |

Status values: open, in progress, done, dropped, moved (to an item of its
own). Kinds: Fix (a known fault), Investigate (find out, then propose),
Decide (a question for Frans, prepared by an investigation), Implement (a
decided change).


Files
=====

* [01-empty-directory.md](01-empty-directory.md). 015-01, Fix: a database
  directory whose stream files are gone, or whose only file is empty,
  starts as a new, empty database; options A to G; A with A+ chosen.
* [02-c-follows-2026-2.md](02-c-follows-2026-2.md). 015-02, Implement: the
  C clone follows 2026.2's Java changes (005-79, 005-69, 005-78).
* [03-lean-follows-005-79.md](03-lean-follows-005-79.md). 015-03,
  Implement: Lean's take follows 005-79's fixed point (optional).
* [04-deps-helper-rule.md](04-deps-helper-rule.md). 015-04, Investigate:
  `deps.py`'s helper rule counts `TransSeq.take` and `dither` as test code.
* [05-empty-or-missing-directory.md](05-empty-or-missing-directory.md).
  015-05, Decide: 015-01's case 3, a start on an empty or missing
  directory; B1 (`createIfMissing()`) recommended for after 2026.2.
* [06-refused-start-leaves-file.md](06-refused-start-leaves-file.md).
  015-06, Fix: a refused start leaves an empty `00000000000000.bergdb`.
* [07-node-fields-unchecked.md](07-node-fields-unchecked.md). 015-07, Fix:
  the node parsers do not check their inner fields; a read that meets one
  throws an unchecked exception and the database stays active.
* [08-streamdigest-compare-cut.md](08-streamdigest-compare-cut.md).
  015-08, Fix: `StreamDigest compare` reports the physical cut's fields,
  which differ between runs.
* [09-reclaim-test-timing.md](09-reclaim-test-timing.md). 015-09, Fix: a
  test of `before-commit.sh` that fails under load (the physical cut's
  timing).
* [10-capacity-test-under-load.md](10-capacity-test-under-load.md). 015-10,
  Investigate: `CapacityTester.testBudgetLoweredAndRaisedUnderReads` fails
  under load on s1.
* [11-tempdircreator-tmp.md](11-tempdircreator-tmp.md). 015-11, Fix: the
  tests' `TempDirCreator` ignores `java.io.tmpdir`.
* [12-keynode-growth-publication.md](12-keynode-growth-publication.md).
  015-12, Fix: a key node's growth publishes its arrays before their
  contents (R1-F1).
* [13-handles-not-counted.md](13-handles-not-counted.md). 015-13, Fix:
  the resident bytes count no handle (R1-F2).
* [14-fast-path-jmm-argument.md](14-fast-path-jmm-argument.md). 015-14,
  Fix: the fast path's argument rests on the address dependency
  (R1-F3).
* [15-resident-count-drift.md](15-resident-count-drift.md). 015-15, Fix:
  the resident count drifts below the real bytes (R1-F4).
* [16-powerloss-cleanup.md](16-powerloss-cleanup.md). 015-16, Investigate:
  `PowerLossTest` failed once in its cleanup (F3, 016-08).
* [17-read-during-close.md](17-read-during-close.md). 015-17, Investigate:
  `InterruptStress` saw a get fail with "File closed" during a close (F3).
* [18-night-large-after-release.md](18-night-large-after-release.md).
  015-18, Implement: `night.sh large` on the release's commit, after it.
* [19-tools-after-005-79.md](19-tools-after-005-79.md). 015-19, Fix:
  tools in items still use `Eviction.LOW` and `TransSeq.dither`.
* [20-filtered-scan-empty-page.md](20-filtered-scan-empty-page.md). 015-20, Fix: a filtered scan takes an empty page for the end of its range (R3-F12).
* [21-index-delete-twice.md](21-index-delete-twice.md). 015-21, Fix: a second delete job lets the first delete a replacement index (R3-F1).
* [22-index-build-after-delete.md](22-index-build-after-delete.md). 015-22, Fix: a deleted index's build job writes into its replacement (R3-F2).
* [23-refused-index-delete.md](23-refused-index-delete.md). 015-23, Fix: a refused index deletion stops maintaining an index that stays active (R3-F9).
* [24-lock-other-class-loader.md](24-lock-other-class-loader.md). 015-24, Fix: a refused open through another class loader releases the active directory lock (R2-F1).
* [25-evictor-failure.md](25-evictor-failure.md). 015-25, Fix: an exception in the evictor strands its requests on a dead worker (R3-F3).
* [26-negative-append-length.md](26-negative-append-length.md). 015-26, Fix: a negative append length corrupts FileStream's length bookkeeping (R2-F5).
* [27-failed-append-visible.md](27-failed-append-visible.md). 015-27, Decide: a failed append's transaction was already visible to readers (R3-F8).


Log
===

2026-11-03. Created the item, at Frans's request, to continue 005-todo
with a new numbering. Entries closely related to a 005 entry may still go
to 005, for now.
