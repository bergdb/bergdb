015-todo
========

Created 2026-11-03 by Frans Lundberg. Status: open.

A list of things to do on BergDB: issues to fix, things to investigate,
decisions to make. Each entry is a subitem with its own ID and a short
definition: what, why, the questions, when it is done, the first step. An
entry that grows into real work gets an item of its own, linked from here.

It continues 005-todo with a new numbering: the next entry is 015-01, not
005-84. Since 2026-11-05, 005 is done; the entries still open in 005 then
moved here as 015-84 to 015-88.

Since 2026-11-05, new entries go to 019-todo, the list of short tasks, or
to 017-long-term; none are added here. The entries open here stay until
they close.


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
| [015-03](03-lean-follows-005-79.md) | Implement | Lean follows 005-79's integer take | open |
| [015-04](04-deps-helper-rule.md) | Investigate | deps.py counts take and dither as test code | open |
| [015-06](06-refused-start-leaves-file.md) | Fix | A refused start leaves an empty first stream file | in progress |
| [015-08](08-streamdigest-compare-cut.md) | Fix | StreamDigest's compare reports the physical cut, which depends on timing | open |
| [015-11](11-tempdircreator-tmp.md) | Fix | The tests' TempDirCreator writes to /tmp, whatever java.io.tmpdir says | open |
| [015-18](18-night-large-after-release.md) | Implement | Run night.sh large on the release, after 2026.2 | open |
| [015-19](19-tools-after-005-79.md) | Fix | Tools in items still use what 005-79 removed | open |
| [015-23](23-refused-index-delete.md) | Fix | A refused index deletion leaves the index active and unmaintained | open |
| [015-28](28-write-racing-index-create.md) | Fix | A write racing an index's creation is never indexed | open |
| [015-29](29-delete-primary-index.md) | Fix | deleteIndex(Database.PRIMARY) throws Bug and leaves the primary deleting | open |
| [015-30](30-build-scans-past-dir.md) | Fix | An index build step scans past its directory, over non-objects | open |
| [015-31](31-cut-at-length.md) | Fix | A cut at the stream's length throws an internal Bug | open |
| [015-32](32-failed-open-leaks.md) | Fix | An unchecked failure during an open leaks handles; an Error keeps the lock | open |
| [015-34](34-consumer-stop-interrupt.md) | Fix | A storage thread interrupted at its stop skips closing its stream | open |
| [015-35](35-background-write-failure.md) | Fix | A failed background write fails the database only at a caller's next storage call | open |
| [015-36](36-interrupted-delete-index.md) | Fix | An interrupted deleteIndex leaves the index deleting with no job | open |
| [015-37](37-interrupted-build-step.md) | Fix | An interrupted retry of a build step ends the build for this run | open |
| [015-38](38-jmx-monitor-interrupt.md) | Fix | JMX's monitor thread ends on an interrupt, and stop loses the caller's flag | open |
| [015-39](39-job-status-mutable.md) | Fix | An index build's status object reads the worker's changing counter | open |
| [015-41](41-object-key-two-maps.md) | Fix | A String or bytes and an object, or a delete, of one key: the call ... | open |
| [015-43](43-object-index-read-time.md) | Fix | Index work reads the indexes before the read time: a new or ... | open |
| [015-46](46-string-at-object-key-index.md) | Fix | A String or byte[] at an object key in an indexed directory breaks ... | open |
| [015-49](49-review-s2-faults.md) | Fix | Review S2's 27 faults of the indexes and the objects | open |
| [015-53](53-stop-during-step-committed.md) | Fix | A transaction that runs when `stop()` comes is committed, but ... | open |
| [015-50](50-reclaim-step-too-large.md) | Fix | A reclaim step that rewrites old values beyond the value limit ... | open |
| [015-51](51-transform-size-unchecked.md) | Fix | A value transformation's result is not size-checked: one above the ... | open |
| [015-52](52-warmup-read-expired.md) | Fix | `execute()` can be refused with `LookupTimeNotAvailableException`, ... | open |
| [015-57](57-resolve-ignores-timezone.md) | Fix | Time.resolve(TimeZone, String) ignores its time zone | open |
| [015-58](58-testclock-current-time.md) | Fix | TestClock.setTime() refuses the clock's current time, which its ... | open |
| [015-60](60-connections-per-thread-kept.md) | Fix | Database.connection() keeps a connection for every thread that ... | open |
| [015-61](61-deletion-job-done-at-stop.md) | Fix | A deletion job that stop() or close() ends early reports "Done! ... | open |
| [015-63](63-time-tostring-threads.md) | Fix | Time.toString() from several threads gives wrong strings and throws | open |
| [015-65](65-memory-builder-second-start.md) | Fix | A second start() of a memory() builder whose database runs is not refused | open |
| [015-69](69-resync-overwrites-readers.md) | Fix | A test-schedule resync overwrites concurrent readers' accounting | open |
| [015-70](70-budget-decrease-above-budget.md) | Fix | A budget decrease can settle above budget although the pins fit | open |
| [015-71](71-audit-empty-handle-cleanup.md) | Fix | The audit reports a valid empty-handle cleanup as a bad table entry | open |
| [015-76](76-startup-distance-clamp.md) | Fix | Db.setStartupDistance clamps to 400,000 to 10^9 bytes without ... | open |
| [015-78](78-close-ioexception-discarded.md) | Fix | The consumer discards the first storage-close IOException | open |
| [015-80](80-buffer-concurrent-writes.md) | Fix | The buffer issues concurrent writes to a single-writer underlying ... | open |
| [015-81](81-close-error-strands-sync.md) | Fix | An unchecked close error can kill the consumer before publishing a ... | open |
| [015-82](82-pending-cut-after-close.md) | Fix | A pending cut arriving during another cut can be left unapplied ... | open |
| [015-83](83-read-past-end-exception.md) | Fix | A read past the end throws IOException instead of the documented ... | open |
| [015-84](84-cap-pace-factor.md) | Investigate | Cap the pace's factor S/sd: a decrease's records grow with the keys | open |
| [015-86](86-gets-with-8-readers.md) | Investigate | Gets over 10 ms with 8 readers (005-65): the rise is the fix's (AB/BA); left: measurements, then Frans | open |


Closed
------

| ID | Kind | What | Status | Closed |
|---|---|---|---|---|
| [015-73](73-startup-pos-unchecked.md) | Fix | A startupPos on an earlier record's start: outside the fault model | done | 2026-11-05 |
| [015-55](55-database-time-margin.md) | Fix | A user transaction at the last database time failed the database | done | 2026-11-05 |
| [015-53](53-stop-during-step-committed.md) | Fix | A transaction committed at a stop threw DbStoppingException | done | 2026-11-05 |
| [015-75](75-start-checks-asserts.md) | Fix | Checks of stream data at a start that were asserts | done | 2026-11-05 |
| [015-72](72-record-size-unchecked.md) | Fix | A record whose size field is larger than its content is accepted | done | 2026-11-05 |
| [015-52](52-warmup-read-expired.md) | Fix | `execute()` can be refused with `LookupTimeNotAvailableException`, ... | done | 2026-11-05 |
| [015-51](51-transform-size-unchecked.md) | Fix | A value transformation's result is not size-checked: one above the ... | done | 2026-11-05 |
| [015-50](50-reclaim-step-too-large.md) | Fix | A reclaim step that rewrites old values beyond the value limit ... | done | 2026-11-05 |
| [015-68](68-startup-large-values-kept.md) | Fix | Startup leaves large values retained in the writer's admission list | done | 2026-11-05 |
| [015-67](67-batch-whole-map.md) | Fix | A batch processes a whole map even past its handle limit | done | 2026-11-05 |
| [015-66](66-evictor-failure-lock-window.md) | Fix | A failed batch releases the writer lock before failing the database | done | 2026-11-05 |
| [015-33](33-max2g-cap.md) | Fix | setMax2G(true) still allows files over two billion bytes | done | 2026-11-05 |
| [015-79](79-storage-negative-append.md) | Fix | A negative append is accepted and decreases StorageManager's length | done | 2026-11-05 |
| [015-26](26-negative-append-length.md) | Fix | A negative append length corrupts FileStream's length | done | 2026-11-05 |
| [015-87](87-retain-duration-in-stream.md) | Investigate | The retain duration kept in the stream | done | 2026-11-05 |
| [015-88](88-overload-and-retries.md) | Investigate | Transaction retries: sleep capped at 640 ms | done | 2026-11-05 |
| [015-05](05-empty-or-missing-directory.md) | Decide | A start on an empty or missing directory creates a database | done | 2026-11-05 |
| [015-44](44-cryptokey-null.md) | Fix | DatabaseBuilder.cryptoKey(CryptoKey.NULL) after a key keeps the key | done | 2026-11-05 |
| [015-45](45-cryptokey-hashcode.md) | Fix | CryptoKey has equals() and no hashCode() | done | 2026-11-05 |
| [015-47](47-bytes-shared-with-caller.md) | Fix | A byte[] value is shared with the caller: a change of the array ... | done | 2026-11-05 |
| [015-64](64-key-replace-last-only.md) | Fix | Key replace replaces only the last "${transactionTime}" of a key | done | 2026-11-05 |
| [015-42](42-rw-changes-frozen-time.md) | Fix | An rw() on a connection changes its frozen lookup time | done | 2026-11-05 |
| [015-48](48-exists-freezes-time.md) | Fix | freezeLookupTime(), then exists(): the frozen time is the read ... | done | 2026-11-05 |
| [015-59](59-new-connection-lookup-time.md) | Fix | Connection.getLookupTime() of a new connection throws ... | done | 2026-11-05 |
| [015-62](62-transactioninfo-after-miss.md) | Fix | transactionInfo() after a get() that found no entry throws ... | done | 2026-11-05 |
| [015-54](54-safe-pos-javadoc.md) | Fix | pSafe is not "the stream length now", as `markSafePositions`'s ... | done | 2026-11-05 |
| [015-27](27-failed-append-visible.md) | Decide | A failed append's transaction was visible to readers: intended | done | 2026-11-05 |
| [015-77](77-canonical-node-javadoc.md) | Fix | DbStarter.canonicalNode's Javadoc gives a reason for the stored ... | done | 2026-11-05 |
| [015-74](74-metablock-comment.md) | Fix | MetaBlock's format comment: the last byte is 10, not 1, and the ... | done | 2026-11-05 |
| [015-02](02-c-follows-2026-2.md) | Implement | The C clone follows release 2026.2 | done | 2026-11-05 |
| [015-85](85-written-not-forced.md) | Decide | "Written, not forced" (005-47): done, measured on s1 and F53 | done | 2026-11-05 |
| [015-56](56-second-start-closes-stream.md) | Fix | A refused second start() of one builder closes the running ... | done | 2026-11-04 |
| [015-40](40-two-writes-one-key.md) | Fix | Two writes of one key in a transaction: the later one can lose | done | 2026-11-03 |
| [015-25](25-evictor-failure.md) | Fix | An exception in the evictor strands its requests on a dead worker | done | 2026-11-03 |
| [015-13](13-handles-not-counted.md) | Fix | The resident bytes count no handle, where 009-02, 4.7 counts them | done | 2026-11-03 |
| [015-14](14-fast-path-jmm-argument.md) | Fix | The fast path's plain reads rest on the address dependency, not the JMM | done | 2026-11-03 |
| [015-20](20-filtered-scan-empty-page.md) | Fix | A filtered scan takes an empty page for the end of its range | done | 2026-11-03 |
| [015-22](22-index-build-after-delete.md) | Fix | A deleted index's build job writes into its replacement | done | 2026-11-03 |
| [015-21](21-index-delete-twice.md) | Fix | A second delete job lets the first delete a replacement index | done | 2026-11-03 |
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
  C clone follows release 2026.2 (005-79, 005-69, 005-73, 005-74, 005-75,
  015-07), and its cross tests compare with that release's Java; done.
* [03-lean-follows-005-79.md](03-lean-follows-005-79.md). 015-03,
  Implement: Lean's take follows 005-79's fixed point (optional).
* [04-deps-helper-rule.md](04-deps-helper-rule.md). 015-04, Investigate:
  `deps.py`'s helper rule counts `TransSeq.take` and `dither` as test code.
* [05-empty-or-missing-directory.md](05-empty-or-missing-directory.md).
  015-05, Decide: 015-01's case 3, a start on an empty or missing
  directory; decided and done: `create(p)` and `open(p)`, `dir(p)`
  removed (B1, `createIfMissing()`, superseded).
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
* [28-write-racing-index-create.md](28-write-racing-index-create.md). 015-28, Fix: a write racing an index's creation is never indexed.
* [29-delete-primary-index.md](29-delete-primary-index.md). 015-29, Fix: deleteIndex(Database.PRIMARY) throws Bug and leaves the primary deleting.
* [30-build-scans-past-dir.md](30-build-scans-past-dir.md). 015-30, Fix: an index build step scans past its directory, over non-objects.
* [31-cut-at-length.md](31-cut-at-length.md). 015-31, Fix: a cut at the stream's length throws an internal Bug (R2-F2).
* [32-failed-open-leaks.md](32-failed-open-leaks.md). 015-32, Fix: an unchecked failure during an open leaks handles; an Error keeps the lock (R2-F3).
* [33-max2g-cap.md](33-max2g-cap.md). 015-33, Fix: setMax2G(true) still allows files over two billion bytes (R2-F4).
* [34-consumer-stop-interrupt.md](34-consumer-stop-interrupt.md). 015-34, Fix: a storage thread interrupted at its stop skips closing its stream (R3-F6).
* [35-background-write-failure.md](35-background-write-failure.md). 015-35, Fix: a failed background write fails the database
  only at a caller's next storage call (R3-F10).
* [36-interrupted-delete-index.md](36-interrupted-delete-index.md). 015-36, Fix: an interrupted deleteIndex leaves the index deleting with no job (R3-F11).
* [37-interrupted-build-step.md](37-interrupted-build-step.md). 015-37, Fix: an interrupted retry of a build step ends the build for this run (R3-F5).
* [38-jmx-monitor-interrupt.md](38-jmx-monitor-interrupt.md). 015-38, Fix: JMX's monitor thread ends on an interrupt, and stop loses the caller's flag (R3-F4).
* [39-job-status-mutable.md](39-job-status-mutable.md). 015-39, Fix: an index build's status object reads the worker's changing counter (R3-F7).
* [40-two-writes-one-key.md](40-two-writes-one-key.md). 015-40, Fix: S1-F1.
* [41-object-key-two-maps.md](41-object-key-two-maps.md). 015-41, Fix: S1-F2.
* [42-rw-changes-frozen-time.md](42-rw-changes-frozen-time.md). 015-42, Fix: S1-F3.
* [43-object-index-read-time.md](43-object-index-read-time.md). 015-43, Fix: S1-F4.
* [44-cryptokey-null.md](44-cryptokey-null.md). 015-44, Fix: S1-F5.
* [45-cryptokey-hashcode.md](45-cryptokey-hashcode.md). 015-45, Fix: S1-F6.
* [46-string-at-object-key-index.md](46-string-at-object-key-index.md). 015-46, Fix: S1-F7.
* [47-bytes-shared-with-caller.md](47-bytes-shared-with-caller.md). 015-47, Fix: S1-F8.
* [48-exists-freezes-time.md](48-exists-freezes-time.md). 015-48, Fix: S1-F9.
* [49-review-s2-faults.md](49-review-s2-faults.md). 015-49, Fix: review S2's 27 faults.
* [50-reclaim-step-too-large.md](50-reclaim-step-too-large.md). 015-50, Fix: R7-F1.
* [51-transform-size-unchecked.md](51-transform-size-unchecked.md). 015-51, Fix: R7-F2.
* [52-warmup-read-expired.md](52-warmup-read-expired.md). 015-52, Fix: R7-F3.
* [53-stop-during-step-committed.md](53-stop-during-step-committed.md). 015-53, Fix: R7-F4.
* [54-safe-pos-javadoc.md](54-safe-pos-javadoc.md). 015-54, Fix: R7-F5.
* [55-database-time-margin.md](55-database-time-margin.md). 015-55, Fix: R7-F6.
* [56-second-start-closes-stream.md](56-second-start-closes-stream.md). 015-56, Fix: R8-F10.
* [57-resolve-ignores-timezone.md](57-resolve-ignores-timezone.md). 015-57, Fix: R8-F2.
* [58-testclock-current-time.md](58-testclock-current-time.md). 015-58, Fix: R8-F3.
* [59-new-connection-lookup-time.md](59-new-connection-lookup-time.md). 015-59, Fix: R8-F4.
* [60-connections-per-thread-kept.md](60-connections-per-thread-kept.md). 015-60, Fix: R8-F5.
* [61-deletion-job-done-at-stop.md](61-deletion-job-done-at-stop.md). 015-61, Fix: R8-F6.
* [62-transactioninfo-after-miss.md](62-transactioninfo-after-miss.md). 015-62, Fix: R8-F7.
* [63-time-tostring-threads.md](63-time-tostring-threads.md). 015-63, Fix: R8-F8.
* [64-key-replace-last-only.md](64-key-replace-last-only.md). 015-64, Fix: R8-F9.
* [65-memory-builder-second-start.md](65-memory-builder-second-start.md). 015-65, Fix: a second start of a memory() builder.
* [66-evictor-failure-lock-window.md](66-evictor-failure-lock-window.md). 015-66, Fix: R4-F1.
* [67-batch-whole-map.md](67-batch-whole-map.md). 015-67, Fix: R4-F2.
* [68-startup-large-values-kept.md](68-startup-large-values-kept.md). 015-68, Fix: R4-F3.
* [69-resync-overwrites-readers.md](69-resync-overwrites-readers.md). 015-69, Fix: R4-F4.
* [70-budget-decrease-above-budget.md](70-budget-decrease-above-budget.md). 015-70, Fix: R4-F5.
* [71-audit-empty-handle-cleanup.md](71-audit-empty-handle-cleanup.md). 015-71, Fix: R4-F6.
* [72-record-size-unchecked.md](72-record-size-unchecked.md). 015-72, Fix: R6-F1.
* [73-startup-pos-unchecked.md](73-startup-pos-unchecked.md). 015-73, Fix: R6-F2; decided 2026-11-05 (15:35): outside the fault model for 2026.3, option (a); a record header checksum is 019-07.
* [74-metablock-comment.md](74-metablock-comment.md). 015-74, Fix: R6-F3.
* [75-start-checks-asserts.md](75-start-checks-asserts.md). 015-75, Fix: R6-F4.
* [76-startup-distance-clamp.md](76-startup-distance-clamp.md). 015-76, Fix: R6-F5.
* [77-canonical-node-javadoc.md](77-canonical-node-javadoc.md). 015-77, Fix: R6-F6.
* [78-close-ioexception-discarded.md](78-close-ioexception-discarded.md). 015-78, Fix: R5-F1.
* [79-storage-negative-append.md](79-storage-negative-append.md). 015-79, Fix: R5-F4.
* [80-buffer-concurrent-writes.md](80-buffer-concurrent-writes.md). 015-80, Fix: R5-F5.
* [81-close-error-strands-sync.md](81-close-error-strands-sync.md). 015-81, Fix: R5-F6.
* [82-pending-cut-after-close.md](82-pending-cut-after-close.md). 015-82, Fix: R5-F7.
* [83-read-past-end-exception.md](83-read-past-end-exception.md). 015-83, Fix: R5-F8.
* [84-cap-pace-factor.md](84-cap-pace-factor.md). 015-84, Investigate:
  cap the pace's factor S/sd, so that a decrease's records stay near the
  steady ones: the issue from 007-07's runs at 50M keys, the two variants,
  the questions, when it is done; moved from 005-77 on 2026-11-05,
  untouched.
* [85-written-not-forced.md](85-written-not-forced.md). 015-85, Decide:
  a durability of "written, not forced": Frans's question, the options
  and the constraints, his decision (A, a setting), its implementation,
  the sync latency on s1 and on F53; moved from 005-47 on 2026-11-05;
  done 2026-11-05.
* [86-gets-with-8-readers.md](86-gets-with-8-readers.md). 015-86, Investigate:
  gets of 27 and 36 ms with 8 readers at 665 MB under ZGC: the issue,
  the test, the results of 2026-10-28 and 2026-11-04 nights, Frans's
  decision and the fix, the AB/BA step of 2026-11-05; moved from 005-65 on
  2026-11-05. Its scripts and results stay in
  [../005-todo/65-gets-with-8-readers/](../005-todo/65-gets-with-8-readers/).
* [87-retain-duration-in-stream.md](87-retain-duration-in-stream.md). 015-87,
  Investigate: the retain duration is not kept in the stream: the issue,
  the study (U1), the probe (U2) and the design (U3), Frans's questions
  F1 to F7; moved from 005-78 on 2026-11-05. The design, the probe and
  its output stay in
  [../005-todo/78-retain-duration-in-stream/](../005-todo/78-retain-duration-in-stream/).
  Done 2026-11-05: Frans's answers, and the change (the settings in
  reclaim's internal KV `/#i/dreclaim/-settings.txt`, no builder value);
  its StreamDigest digests and the restart probe are in
  [87-retain-duration-in-stream/](87-retain-duration-in-stream/).
* [88-overload-and-retries.md](88-overload-and-retries.md). 015-88, Investigate:
  transaction retries; moved from 005-81 on 2026-11-05. Decided by Frans
  that day (14:12): the retry sleep capped at 640 ms for release 2026.3,
  the contract unchanged; the investigation (the waits, the client
  contract, the retry variants, the harness and the baselines) moved to
  [017-06](../017-long-term/06-overload/retries.md), with Frans's question
  whether `rw()` should ever give up under overload. The harness and its
  results stay in
  [../005-todo/81-overload-and-retries/](../005-todo/81-overload-and-retries/).


Log
===

2026-11-03. Created the item, at Frans's request, to continue 005-todo
with a new numbering. Entries closely related to a 005 entry may still go
to 005, for now.

2026-11-05. 015-84, cap the pace's factor S/sd, moved from 005-77
untouched, at Frans's decision (decided 2026-11-04/05): "005-77 (cap
pace factor, about a day of F53) moves to 015 untouched."

2026-11-05. 015-85 to 015-88 moved from 005-47, 005-65, 005-78 and 005-81,
each with its contents as it was and a new Status line that says what is
left, at Frans's plan, approved 2026-11-05, 07:17: "By morning, every 005
entry still open, decisions or remaining runs, moves to 015 with its work
recorded, and 005 itself is marked done." Their support directories stay
in 005-todo.

2026-11-05, 08:35. 015-85 done: the sync latency on F53, in the
coordinator's second quiet block (p50 4.5 ms with forcing on, 0.0 ms off).
015-86: the AB/BA step run; the rise of the gets over 10 ms is the fix's,
so the Recommendation's measurements and Frans's decision are left.

2026-11-05, 09:38. New entries go to 019-todo from now on, at Frans's
request: the list here is getting full. 019 takes short tasks, done and
closed in about a day; open-ended, long-term and strategy topics go to
017. The entries open here stay.
