# 022-05 Java's tests in C: eviction, reclaim, the stream and the harnesses

Created 2026-11-09 by Frans Lundberg (worker t14 of the session
`022-bergdb-c`). A part of 022-05, the inventory of Java's Core tests in
C; the session writes its index.

Java's test classes of this part, as `bergdb.core` has them on `main` at
`e875a34` (2026-11-09 17:18): Eviction, Reclaim, NodeCollection,
NodeStreamTester, FileStreamPowerLossTester, CapacityTester,
EvictionReaderTester, Residents, ReclaimRetentionTester,
ReclaimReaderTester, InterruptTester, CorruptStreamTester,
StorageFaultTester, EvictionAccountingTester, LimitsTester, Cache3,
DbHelper, Tester. Each test method (each `@Nano`, the f-tests and night
tests too) is ported (P: a C test or a harness checks what it checks),
written now (W), not for C (N) or left (L). The C tests are in
`c/test/unit/t_*.c` and `c/test/func/f_*.c`.


# 1. In short

182 test methods: 82 P, 45 W, 53 N, 2 L.

One fault of C found (section 3.1): after a failed force, a sync or the
close with nothing left to write forced the files again and took a
success for the stream; `bergdb_sync` then gave `BERGDB_OK` on a database
that its storage had failed, and `bergdb_close` gave `BERGDB_OK`, not
`BERGDB_IO`. The part stream-storage found it too, and its fix, the same
change, landed first (`d694a0d`); this part's tests fail without it. No
fault of Java found. The 53 N are
threads (the eviction thread, the storage thread, reader threads,
interrupts, `stop()` from another thread), JMX, Java's resident
registry, Java's stream layer, and 015-67's bounded batches, which C
does not have (022-01's D4).

The 45 written now are 31 new C tests, each passing in both builds and,
for the unit and functional tests, under `leaks` in the gate:

* `t_limits.c` (new), `limits_seeds`: harness 6.4, LimitsTester, sizes and
  times at their limits. Random transactions at the edge of every limit:
  values whose nodes take the value limit (`db_value_limit`, 7/8 of the
  record limit) and a few bytes more or less, alone and together, long
  keys of up to 3,006 bytes, up to 1,550 keys in one transaction, value
  transformations that grow a value, the clock at the last user time and
  past it, out of range and going back, the four setters at and around
  their bounds, the top node ordinals' end (a second top ordinal near the
  last); with reclaim (a retain duration of one second), budgets from 1
  byte and restarts in a directory. The record limit is lowered as Java's,
  through `db_config`'s `record_limit` (012-18, section 3.2), to 240 kB,
  300 kB or 1 MB. Java's checks, each: a refusal is `ERR_LIMIT` with Java's
  `DbException` and a reason that holds, the database goes on and the
  stream does not grow; a commit is at a time after the last and at most
  `DBCLOCK_LAST_USER_TIME`, and every value reads back; after a restart
  every committed value and setting is there; a transformation's result
  above the value limit is the caller's fault (015-51), and a record that
  did not fit leaves nothing in the stream.
* `t_evict.c`, `evict_accounting` and `evict_accounting_many_restarts`:
  harness 6.5, EvictionAccountingTester, eviction's accounting. Batches of
  transactions (small values, now and then one over 1 MiB, deletes, a
  tenth of the keys 300 bytes long), a random budget from 1 byte to none
  changed between them, an eviction of every detachable object now and
  then, gets at random past times checked against the test's own history,
  restarts with a new budget, half of them right after a value over 1 MiB;
  after each batch the recount (every object's holders), the pins in the
  node table, no resident pointer to a value over 1 MiB (015-68, 019-47),
  the resident bytes within the trigger, and a decrease of the budget that
  must be reached when the pins fit it.
* `f_budget.c`, through `bergdb.h`: `budget_reads_without_writes` (a cold
  database six times the budget, every key read three times: the resident
  bytes at most the budget after every read, and a sweep stopping at the
  low watermark, not below it less a key node's worth),
  `budget_lowered_and_raised_under_reads` (every object just read, so every
  CLOCK bit set, and the budget lowered to 9/10 and to 1/4 of the
  resident bytes: reached in the setter's call and after every read;
  raised: kept, and grown by reads), `budget_large_puts` (values of 1.5
  MiB under a budget of 4 MB).
* `t_ncoll.c`: `ncoll_maintenance_follower` (reclaim's follower leaves the
  pointer, the node table and the CLOCK bit alone) and
  `lmap_large_ids_and_short_runs` (node ids from 2^31 to `INT64_MAX`; the
  writer's ids spread over the node table's slots, every id within 22
  slots of its own in 200,000).
* `t_reclaim.c`, 16 tests: ReclaimRetentionTester's six (the retain
  duration shrunk during an iteration, several done rows made cuttable at
  once, grown after a cut, another one at a restart, forever then finite,
  finite then forever during an iteration), one harness that checks that
  each cut kept the duration in force when it was decided, the first
  available time never moves back, also over restarts, and lookups from it
  on equal a model, a lookup before it refused; and Reclaim.Tester's
  restarts after cuts (the start after a cut, writes after it, the first
  available time, deleted keys, the meta block's transaction before the
  cut, a crash between an iteration's last step and its end, the
  iteration resumed from its row, the stream's startup distance, not the
  builder's), `test1`, `testPretruncate` and the cut made when the
  decision is durable.
* `t_rstream.c` and `t_sdb.c`: NodeStreamTester's corrupt sizes refused
  before their buffers (005-74, F3), read sizes that end at or cross a meta
  block, and a startup position at a failed transaction (005-28).
* `t_stream.c` and `t_iofail.c` (new): through the test build's I/O seam
  (`plat_io_set`), a failed force of a file or of the directory does not
  advance the durable length, and a sync and the close after it fail too
  (the fault of section 3.1); a cut's failed delete or directory force
  keeps the forced bytes; and StorageFaultTester's idea, a failure of each
  file call in turn on a new and on a reopened database
  (`iofail_each_call`: a sample of 29 calls in the gate,
  `BERGDB_IOFAIL_ALL=1` all 120 by hand): `BERGDB_FAILED` from then on (P7),
  a failed open leaves nothing, the close gives `BERGDB_IO`, a reopen has
  every synced transaction and a prefix of those executed.

Run times in the test build on F53 under a load of 15 to 37: each new
unit test 0.01 to 0.9 s (`limits_seeds` 0.9 s, three seeds of 40 steps;
`evict_accounting_many_restarts` 0.7 s;
`reclaim_cut_keeps_meta_block_transaction` 0.64 s), each new functional
test 0.2 to 0.4 s. The forces of the two harnesses' restarts and new
files are no-ops in the test build, through the I/O seam (what reaches
the disk is power.sh's part); in the release build they are real, and
under load take most of their time.


# 2. The classes

## 2.1 Eviction

The C tests are in `t_evict.c`, and `f_budget.c` for those named `budget_`.
Java's twin tests run a database under eviction beside one without and
compare the records and the answers; C's twins are `evict_twins` (budgets
from 1 byte up, the stream byte for byte after each transaction, reads at
past times), `budget_invariance` (restarts, getMany both ways, getOne
through the history) and cross.sh's budget runs (every quick workload,
reclaim's among them, under budgets of 1 and 20,000 bytes).

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testLowOfExact                       | P | `evict_low_of_exact` |
| testSharedChild                      | P | `evict_twins`, `budget_invariance` |
| testSharedChildF                     | P | as testSharedChild |
| testOldSnapshotAndNewerCanonical     | P | `evict_twins` (reads at past times) |
| testOldSnapshotAndNewerCanonicalF    | P | as testOldSnapshotAndNewerCanonical |
| testStartupUpdatesWriteoutEviction   | P | `budget_invariance`, `evict_accounting` |
| testStartupUpdatesWriteoutEvictionF  | P | as testStartupUpdatesWriteoutEviction |
| testSplitsAndRootChanges             | P | `evict_twins`; cross.sh's budgets |
| testSplitsAndRootChangesF            | P | as testSplitsAndRootChanges |
| testHistoricalParentsAndLongKeys     | W | `evict_accounting` (long keys) |
| testHistoricalParentsAndLongKeysF    | W | as testHistoricalParentsAndLongKeys |
| testReclaimWithMisses                | P | cross.sh quick, reclaim under budgets |
| testReclaimWithMissesF               | P | as testReclaimWithMisses |
| testValuesNotInTheTable              | N | by construction: a value has no handle |
| testValues                           | P | `evict_large_value`, `evict_twins` |
| testValuesF                          | P | as testValues |
| testEvictionThreadIdleUntilClose     | N | the eviction thread |
| testNoLostRequest                    | N | the eviction thread |
| testNoLostRequestF                   | N | the eviction thread |
| testSetBudgetAtBatchEnd              | N | the eviction thread |
| testInterruptWithRequestPending      | N | the eviction thread, interrupts |
| testLoweredBudgetAfterReads          | W | `budget_lowered_and_raised_under_reads` |
| testNothingToFree                    | N | loaders' handles (threads) |
| testBatchFailureFailsTheDatabase     | N | the eviction thread; C's sweep only frees |
| testBatchFailureBeforeTheLockGoes    | N | the eviction thread, the write lock |
| testBatchWithinItsHandlesInALargeMap | N | 015-67's bounded batches, not ported (D4) |
| testStartAdmitsLargeValues           | P | `evict_start_admits_large_values` |
| testWarmupKeepsNoLargeValue          | P | `evict_warmup_keeps_no_large_value` |
| testLoweredBudgetAfterPinsFell       | P | `evict_lowered_budget_after_pins_fell` |
| testInterruptedWhileAWriterWaits     | N | the eviction thread, interrupts |

Longer names:

* testStartAdmitsLargeValuesOfTheSectionsFirstTransaction, P:
  `evict_start_admits_first_transactions_large_values`


## 2.2 CapacityTester

In `f_budget.c`, through `bergdb.h`, unless named otherwise.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testReadsWithoutWrites               | W | `budget_reads_without_writes` |
| testReadsWithoutWritesF              | W | `budget_reads_without_writes`, at the unit's size |
| testBudgetLoweredAndRaisedUnderReads | W | `budget_lowered_and_raised_under_reads` |
| testBudgetLoweredWhileIdle           | P | `budget_setter`: C evicts in the setter's call |
| testWarmupDoesNotWait                | N | the eviction thread's waits |
| testSweepsStopNearLow                | W | `budget_reads_without_writes` |
| testScans                            | P | `budget_invariance` (a cold scan) |
| testLargePuts                        | W | `budget_large_puts` |
| testStalledReaders                   | N | reader threads |
| testPinnedAboveBudget                | P | `evict_twins`; `evict_lowered_budget_after_pins_fell` |
| testBudgetThroughJmx                 | N | JMX |
| testSameRecordsAsWithoutEviction     | P | `evict_twins`, `budget_invariance`, cross.sh |
| testSameRecordsAsWithoutEvictionF    | P | as testSameRecordsAsWithoutEviction |
| testBatchOnPinnedLeaf                | N | the resident registry (Residents) |
| testCountsWithHandles                | N | the resident registry (Residents) |


## 2.3 EvictionReaderTester

Its readers are threads; C has one caller, whose reads between the writes
and the evictions are `evict_accounting`'s.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testEvictionKeepsTheRecords            | P | `evict_twins` (the stream byte for byte) |
| testDeadHandleInAPointer               | N | a reader's steps between an eviction's (threads) |
| testDeadHandlesResolvedAgain           | P | `evict_table`, `evict_accounting` |
| testReaderPausedInsideAFollow          | N | reader threads |
| testReaderPausedInsideAFollowF         | N | reader threads |
| testChunkedScanAcrossEviction          | P | `budget_invariance`, `evict_accounting` |
| testReadersWhileSlotsAlternate         | N | reader threads |
| testReadersWhileSlotsAlternateF        | N | reader threads |
| testReadersUnderTheCapacityControllerF | N | reader threads, the eviction thread |
| testAuditWithReaderCleanup             | N | reader threads, the audit (015-71) |


## 2.4 Residents

Java counts estimates of its objects in a registry; C's resident bytes are
the allocator's counts (`evict.h`, 012-12; 012-18, section 3.3), so a count
can be neither stale nor below an object's bytes, and the recount
(`db_recount`) checks every object's holders in each eviction test.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testAccounting                    | N | the resident registry (Residents) |
| testHandlesCounted                | N | the resident registry |
| testCountedApartFromSize          | N | the resident registry |
| testResyncWithConcurrentLoad      | N | threads |
| testPinned                        | P | `evict_detachable`; `evict_twins`' pins |
| testReplacedNodeCounted           | N | the resident registry (019-20) |
| testSectionNodesCountedAfterRerun | N | the resident registry (019-21) |
| testLinkedHandlesCountedAtStart   | N | the resident registry (019-21) |


## 2.5 EvictionAccountingTester

Harness 6.5 (018-05), in `t_evict.c`; section 1 says how it maps to C.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testAccounting               | W | `evict_accounting` |
| testAccountingWideDropWindow | N | reader threads, `dropIfEmpty` (019-46) |
| testAccountingManyRestarts   | W | `evict_accounting_many_restarts` |
| testAccountingLong           | N | a batch's handle limit, 015-67's, not ported (D4) |


## 2.6 LimitsTester

Harness 6.4 (018-06), in `t_limits.c`; section 1 says how it maps to C.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testSeeds     | W | `limits_seeds` |
| testSeedsLong | W | `limits_seeds`, 20 seeds of 500 steps by hand |


## 2.7 Cache3

C's node table is one `lmap` (`ntable.h`); its tests are in `t_ncoll.c` and
`t_evict.c`.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testLargeIds      | W | `lmap_large_ids_and_short_runs` |
| testOneLiveHandle | P | `evict_table`, `ntable_rules` |
| testBinsStaySmall | W | `lmap_large_ids_and_short_runs` |


## 2.8 NodeCollection

In `t_ncoll.c`.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testFollowNewerVersion                  | P | `ncoll_follow_newer_version` |
| testFollowRuleR                         | P | `ncoll_follow_rule_r` |
| testLoaderTakesTheHandlesObject         | P | `ncoll_loader_takes_the_handles_object` |
| testDropIfEmptyKeepsTheWritersObject    | N | a reader's drop without the write lock (threads) |
| testWriterKeepsTheNodeWhateverItsPolicy | P | `ncoll_writer_keeps_the_node_whatever_its_policy` |
| testWriterDuringADropsDeadWindow        | N | threads |
| testMaintenanceFollower                 | W | `ncoll_maintenance_follower` |
| testAccessData                          | P | the CLOCK bit; C has no access clock |
| testNoCutBackAfterReconstruction        | P | `ncoll_no_cut_back_after_reconstruction` |
| testResolvePointers                     | P | `ncoll_resolve_pointers` |
| testResolvePointersUnpinned             | P | `ncoll_resolve_pointers_unpinned` |
| testLinkToCanonical                     | P | `ncoll_link_to_canonical` |
| testLinkToCanonicalByPosition           | P | `ncoll_link_to_canonical_by_position` |
| testLinkToCanonicalTopNode              | P | `ncoll_link_to_canonical_top_node` |
| testLinkToCanonicalCheck                | P | `ncoll_link_to_canonical_check` |
| testResolvePointersChecksTheType        | P | `ncoll_resolve_pointers_checks_the_type` |
| testLinkToCanonicalChecksTheType        | P | `ncoll_link_to_canonical_checks_the_type` |


## 2.9 DbHelper

C's `handle_still_dirty_nodes` (`db.c`) works on the record's nodes, as
Java's `Db` calls it; its passes decide which nodes each record holds, which
cross.sh and the vectors compare byte for byte.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testHandleStillDirtyNodes1 | P | cross.sh: Rule A's passes decide the records |
| testHandleStillDirtyNodes2 | P | as testHandleStillDirtyNodes1 |


## 2.10 Tester

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testSposNullCopy | N | Java's two copies of `Spos.NULL` |


## 2.11 Reclaim

In `t_reclaim.c` unless named otherwise.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testSerialize1                           | P | `reclaim_row_text` |
| testSerialize2                           | P | `reclaim_row_text`, `reclaim_table_text` |
| testDeserializeWithBadString             | P | `reclaim_row_parse` |
| test1                                    | W | `reclaim_test1` |
| testPretruncate                          | W | `reclaim_pretruncate` |
| testIterationInfo                        | N | an empty test in Java |
| testIterationsFollowSetStartupDistance   | P | `reclaim_iterations_spaced` |
| testUserTransactionLeavesTimesForReclaim | P | `reclaim_user_transaction_leaves_times` |
| testIterationRewritesAllOldValues        | P | `reclaim_iterations_rewrite_old_values` |
| testRestartAfterCut                      | W | `reclaim_restart_after_cut` |
| testTransIteratorAfterCut                | P | `rs_pos_of_trans_completed_before` |
| testFirstAvailableTimeAfterRestart       | W | `reclaim_first_available_time_after_restart` |
| testWritesAfterCut                       | W | `reclaim_restart_after_cut` |
| testDeletedKeysAfterCut                  | W | `reclaim_deleted_keys_after_cut` |
| testStepWithinValueLimit                 | P | `reclaim_step_within_value_limit` |
| testCutKeepsMetaBlockTransaction         | W | `reclaim_cut_keeps_meta_block_transaction` |
| testCrashBeforeIterationEnd              | W | `reclaim_crash_before_iteration_end` |
| testAllowanceCountsIndexNodes            | P | `reclaim_java_vectors` (Java's bytes) |
| testCutPointBeforeScan                   | P | `reclaim_iterations_rewrite_old_values` |
| testIterationsSpacedByRetention          | P | `reclaim_iterations_spaced` |
| testFractionOfExact                      | P | `reclaim_fraction_of_exact` |
| testRestartResumesIteration              | W | `reclaim_restart_resumes_iteration` |
| testLookupsFromFirstAvailableTime        | P | `reclaim_lookups_from_first_available_time` |
| testStepReserveSplitsSteps               | P | `reclaim_step_reserve_splits_steps` |
| testCutIsMadeAfterDecisionIsDurable      | W | `reclaim_cut_made_when_durable` |
| testCutIsMadeAfterDecisionIsDurableF     | P | `api_reclaim_directory` |
| testSafePosAfterTheCallsRecords          | P | `reclaim_safe_pos_after_the_calls_records` |
| testStopDuringStepCommits                | N | `stop()` from another thread; C has no `stop()` |

Longer names:

* testIterationsFollowTheStreamsStartupDistance, W:
  `reclaim_iterations_follow_stream_distance`


## 2.12 ReclaimRetentionTester

In `t_reclaim.c`; the six written share one harness (section 1).

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testShrinkDuringIteration          | W | `reclaim_retention_shrink_during_iteration` |
| testShrinkMakesSeveralRowsCuttable | W | `reclaim_retention_shrink_makes_rows_cuttable` |
| testGrowWithPendingCut             | W | `reclaim_retention_grow_after_cut` |
| testRestartWithOtherRetention      | W | `reclaim_retention_restart_with_other` |
| testForeverThenFinite              | W | `reclaim_retention_forever_then_finite` |
| testFiniteThenForeverMidIteration  | W | `reclaim_retention_finite_then_forever_mid_iteration` |
| testRetainDurationTooSmall         | P | `reclaim_settings_refused_change_nothing` |


## 2.13 ReclaimReaderTester

Each is of a reader thread that a cut overtakes; C's reads run within a
call, and a read before the first available time is refused (`check_lookups`
in `t_reclaim.c`).

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testCopiesAreCoherentDuringReaderSwizzling | N | threads: a reader's swizzle during a copy |
| testPointerPairIsCoherent                  | N | threads: a reader's swizzle racing the writer |
| testPointerPairIsCoherentF                 | N | threads |
| testReaderExpiresWhenCutOvertakesIt        | N | threads; C reads within a call |
| testLatestReaderExpiresWhenCutOvertakesIt  | N | threads |
| testReaderExpiresWhenFilesAreDeleted       | N | a paused reader (threads) |
| testWarmupReadOvertakenByCut               | N | the warmup before the lock (threads) |


## 2.14 NodeStreamTester

In `t_rstream.c` unless named otherwise.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testCorruptReadNodeSize             | W | `ns_corrupt_read_sizes` |
| testCorruptReadTransSize            | W | `ns_corrupt_read_sizes` |
| testCorruptIteratorSize             | W | `ns_corrupt_read_sizes` |
| testReadSizeNearMaxValue            | P | `ns_read_size_near_max_value` |
| testReadSizeExcludesMetaBlocks      | W | `ns_read_size_excludes_meta_blocks` |
| testReadSizeAtMetaBlock             | W | `ns_read_size_at_meta_block` |
| testSimpleRestart                   | P | `start_restart_every_transaction` |
| testSimpleRestart2                  | P | `start_restart_every_transaction` |
| testRestartWithMultipleTransactions | P | `start_restart_every_transaction` |
| tIterators1                         | P | `records_walk_and_reads` |
| testReadNodeHeader1                 | P | `records_walk_and_reads` (every node's header) |
| testReadNodeHeader2                 | P | `records_walk_and_reads` |
| testReadNodeHeader3                 | P | `records_walk_and_reads` |
| testTransIteratorAtFailedTrans      | P | `ns_walk` |
| testStartupPosAtFailedTrans         | W | `sdb_startup_pos_at_failed_trans` |
| testCrashInPrimordialTrans          | P | `sdb_refusals` (a cut creation) |


## 2.15 FileStreamPowerLossTester

In `t_stream.c` unless named otherwise; power.sh is run by hand
(c/readme.md, section 10).

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testUnforcedBytesCanBeLostAfterDeletion    | P | power.sh, `OMIT=file` |
| testSyncDoesNotAdvanceAfterFailedFileForce | W | `stream_failed_force_keeps_the_durable_length` |
| testDurableFrontierWaitsForForce           | W | `stream_failed_force_keeps_the_durable_length` |
| testPendingCutForceFailureFailsTheStream   | W | `stream_failed_cut_keeps_forced_bytes` |
| testRecoveryBetweenEveryPrefixDeletion     | P | power.sh (an image at each delete) |
| testUnorderedUnforcedDeletionsAreDetected  | L | a power.c model of deletes durable out of order |
| testColdRecoveryAtPersistenceBoundaries    | P | power.sh (C's forces, no per-append force) |
| testProcessCrashKeepsWhatWasWritten        | P | `durable_kill_after_execute_and_sync` |
| testColdRecoveryWithoutAppendForces        | P | power.sh |
| testWeakenedForceOrderingIsDetected        | P | power.sh `OMIT=file`, `OMIT=dir` |

Longer names:

* testMissingDirectoryForceLosesReplacementFile, P: power.sh,
  `NAMES=dirforce OMIT=dir`
* testSyncDoesNotAdvanceAfterFailedDirectoryForce, W:
  `stream_failed_force_keeps_the_durable_length`
* testPartialDeletionAndDirectoryFailureKeepForcedBytes, W:
  `stream_failed_cut_keeps_forced_bytes`
* testWeakenedForcesWithoutAppendForcesAreDetected, P: power.sh
  `OMIT=switch`


## 2.16 StorageFaultTester

In `t_iofail.c`.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testSample           | W | `iofail_each_call` (a sample) |
| testStopWhileReading | N | `stop()` and threads |
| testStreamLayerAll   | N | StrictStream's hook: the stream's Java layer |
| testIoLayerAll       | W | `iofail_each_call`, every call, by hand |


## 2.17 CorruptStreamTester

corruptset.sh's quick set is in the gate; its whole set by hand.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testFound019_32 | P | corruptset.sh quick (its found copies) |
| testFound021_11 | P | corruptset.sh quick; `sdb_found_021_11` |
| testFound021_12 | P | corruptset.sh quick; `sdb_found_021_12` |
| testSample      | P | corruptset.sh (`SEEDS=1`: 6,253 copies) |
| testFull        | L | CorruptSet.java's full mode, a night step |


## 2.18 InterruptTester

C has no threads to interrupt, and `plat.c` retries a call that a signal
interrupts (`EINTR`).

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testCommitsThatMakeCuts      | N | interrupts |
| testCommitThatWaitsForRoom   | N | interrupts, the storage thread's buffer |
| testSync                     | N | interrupts |
| testStartCommitAndClose      | N | interrupts |
| testStorageThreadInterrupted | N | the storage thread |
| testJmxMonitorInterrupted    | N | JMX |
| testJmxStopInterrupted       | N | JMX |


# 3. Findings

## 3.1 A fault of C: a sync or a close after a failed force

`stream.c`'s `stream_flush` returned at once when the write buffer was
empty, before its check of a failed stream (Java's
`FileStream.checkIOException`, which every operation makes first). So
after a force that failed in a sync, which leaves the buffer empty, the
next `stream_sync` forced the files again, and if that force succeeded
the call returned `ERR_OK` and set the durable length to the stream's
length; the close did the same. At the API, `bergdb_sync` on a database
that its storage had failed gave `BERGDB_OK`, not `BERGDB_FAILED`, and
`bergdb_close` gave `BERGDB_OK`, not `BERGDB_IO`, against `bergdb.h` and
c/readme.md, section 9, point 8; and a force retried after a failure
counts as durable what the failed force may have lost (the fsync error
that the kernel reports once). The same after a cut's failed delete or
directory force. `durable_write_fails` (`f_durable.c`) did not show it,
as a failed write leaves the buffer full. The fix: `stream_flush` gives
`ERR_IO` for a failed stream before it looks at the buffer. This part
made it and so did the part stream-storage, at the same time and the same
change; stream-storage's landed first (`d694a0d`, with its tests
`stream_failure_refuses_writes` and `stream_failed_force_fails_the_database`),
and this part's copy went at the rebase. Without the fix three tests of
this part fail:
`stream_failed_force_keeps_the_durable_length` (the sync after the failed
force gives `ERR_OK`, the durable length 200, not 100),
`stream_failed_cut_keeps_forced_bytes` (its sync and finish give
`ERR_OK`), and `iofail_each_call` (ten runs' closes give `BERGDB_OK`,
later syncs `BERGDB_OK` after `BERGDB_FAILED`); checked again by putting
back the old `stream.c`.

## 3.2 Departures of C, the tests adapted

* **A cut is made in the call that decides it** (c/readme.md, section 9,
  point 9), so no cut is pending between calls, which
  ReclaimRetentionTester.testGrowWithPendingCut and
  Reclaim.testCutIsMadeAfterDecisionIsDurable look at:
  `reclaim_retention_grow_after_cut` and `reclaim_cut_made_when_durable`
  check C's form, no cut pending after the deciding call, the stream
  durable past the decision, the first available time never moving back;
  a cut pending at an open is `api_reclaim_pending_cut_at_open`. C's runs
  need no syncs for their cuts.
* **A cut's failed delete or directory force** is returned by the cut's
  own call, where Java's cut thread leaves it to the stream's next
  operation (no thread in C): `stream_failed_cut_keeps_forced_bytes`.
* **The maintenance follower keeps no map** of the versions it read
  (`nc_follow_maintenance`: it saves reads only, 012-11), so a second
  pointer to a version reads it again, where Java's reads it once:
  `ncoll_maintenance_follower` counts two reads.
* **The harnesses in C's terms.** Harness 6.4: C's random numbers
  (`test_random`), so a seed makes other runs than Java's; no eviction
  schedules (`evictRandom`), the budget only. Harness 6.5: one caller, so
  its reader threads are reads between the transactions, its test
  schedules' evictions (`evictNow`) an eviction of every detachable
  object, its comparison of Residents' estimates with a recount the
  recount of every object's holders (C's counts are the allocator's), and
  no batch's handle limit (015-67, D4).
* **Shortened to stay fast**: `reclaim_cut_keeps_meta_block_transaction`
  3 seeds of 1,500 puts (Java 20 of 3,000);
  `reclaim_crash_before_iteration_end` stops 200 puts after the first cut
  after the crash;
  `evict_accounting_many_restarts` 100 batches with a restart after one
  in 5 (Java 300 and one in 25), about as many restarts.

## 3.3 Faults of Java

None found.

## 3.4 Left (L)

* FileStreamPowerLossTester.testUnorderedUnforcedDeletionsAreDetected: a
  mode of power.c's disk model in which deletes become durable out of
  order until the next force of the directory, with an `OMIT=dir`
  control; a few dozen lines. C's own order, a force of the directory
  after each delete, is checked by `stream_forces`.
* CorruptStreamTester.testFull: a full mode of `CorruptSet.java` (every
  cut of the streams under 100 KB, every byte flipped, every field, a
  seed of the day) and a night step; hours of dumps.

Of the P, the twins of Eviction are C's own (`evict_twins`,
`budget_invariance`, cross.sh's budgets) rather than Java's scenarios one
by one; a port of the scenarios (a shared child, an old snapshot and a
newer canonical object, splits and root changes) under a budget of one
byte would take about 150 lines in `f_budget.c`.


# 4. The long runs

By hand, in the test build (sanitizers), once each:

* Harness 6.4, Java's night size, 20 seeds of 500 steps
  (`BERGDB_LIMITS_SEEDS=1-20 BERGDB_LIMITS_STEPS=500 build/test/unit
  limits_`): all passed, 6,760 transactions committed; refused for their
  size 435, their index nodes 188, the time 338, the clock 194, the top
  node ordinals 1,190 (in the four runs with a second top ordinal); 23
  to 42 settings calls and 8 to 16 restarts a run; one run ended by the
  caller's fault (seed 9); 99 s on a loaded F53.
* Harness 6.5: 60 seeds of the unit shape (`BERGDB_ACCOUNTING_SEEDS=60`)
  and the many restarts' seed: all passed, no wrong answer, 11 s.
* `iofail_each_call` with `BERGDB_IOFAIL_ALL=1`: every file call of the
  workload made to fail in turn, 77 on a new database and 43 on a
  reopened one: all passed, 2 s (12 s under a load of 37).
