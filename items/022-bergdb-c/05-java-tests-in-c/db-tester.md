# 022-05 db-tester: Java's tests of `Db` in C

Created 2026-11-09 by Frans Lundberg. Status: done.

Worker t12's part of 022-05: every test method of `bergdb.core`'s
`DbTester`, `DbTesterFailure`, `DbTesterJavadoc`, `DbTesterLongKeys` and
`DbUtil` at `main`'s `e875a34` (2026-11-09 17:18, the Java that `int.git`'s
`2026.4` pins), classed as the brief says: **P** ported (C's test named,
or the harness), **W** written now, **N** not for C (the reason), **L**
left. A test method is what nanotest runs (its `MethodFilter`): a static
method with `@Nano`, or a static `void testX()` without parameters; so
`DbTester`'s `tGetFirst1`, `tGetFirst2` and `bug130403` count, and
`DbBuilder.testSetupExceptStream()`, a builder's method, does not. And the
five tests that `main` has had since (17:54, 020-27's Q2: null and range
arguments), in section 1.6, so that the next re-pin finds them done.

| Class | Methods | P | W | N | L |
|---|---|---|---|---|---|
| DbTester         |  97 | 29 | 54 | 14 | 0 |
| DbTesterFailure  |  38 |  9 | 11 | 18 | 0 |
| DbTesterJavadoc  |  15 | 11 |  1 |  3 | 0 |
| DbTesterLongKeys |   2 |  2 |  0 |  0 | 0 |
| DbUtil           |  14 |  1 |  0 | 13 | 0 |
| in all           | 166 | 52 | 66 | 48 | 0 |
| after the pin    |   5 |  0 |  4 |  1 | 0 |

The new tests are 28 unit tests in a new file, `c/test/unit/t_dbtester.c`
(`dbt_`), most through `bergdb.h` as a user calls it, two through `db.h`
for a lowered record limit, as `t_db.c`'s are; and one functional test,
`f_durable.c`'s `durable_write_fails_in_execute`. Each C test names the
Java tests it ports. All pass in both builds and under `leaks`, on C as
it was: no fault of C was found, and none of Java's. One difference is for
the session to decide: C's close reports a failure of the storage that a
call has already reported, where Java's close, since 019-09, returns
normally (section 3.1). Four tests of `DbTesterJavadoc` that this part
first wrote were ported meanwhile by 022-02's re-pin of 17:18 (`f_api.c`'s
`api_keys_and_values` and three more, `cd25a24`), and are P here; this
part's copies were dropped.

Not for C, by reason (48): no `stop()` or `start()`, a handle that ends
at its close (9); threads: the close's, the storage's, the buffer's, a
writer's (16); Java's exceptions and `Error`s, which C's callbacks and
stream cannot throw (6); Java's test tools `DbUtil.checksum` and
`getNodesOnPathToKv` (12); JMX, try-with-resources and `DbBuilder`'s
streams (4); and C's close after a reported failure, a difference (1,
section 3.1). Each row says which.


# 1. The classes

## 1.1 `DbTester`

The tests of results (puts, deletes and reads at times, keys of one to
eight segments, splits, the STM) had no C test of their own: `cross.sh`
compares C's reads with Java's on random workloads, but no C test checked
these cases against a known answer. They are written now, a C test for
one to eight Java tests of a kind. Java's `java.util.Random` draws
(`createRandomDB`'s keys, `KeyFactory.crazyKey`'s kinds) are
`test_random`'s draws of the same kind of input; Java's `checkNodes()` is
`bergdb_debug_check`. Checks of the index itself (a super root's
`rootTime`, a key node's delete bitmap, the nodes of D) are not in
`bergdb.h`; where C has them, `cross.sh` compares the bytes they decide.

| Method                                   | Class | C's test, or the reason |
|---|---|---|
| test0                                    | P | every test of `t_dbtester.c` |
| test1                                    | W | `dbt_test1` |
| test2                                    | W | `dbt_test2_and_test3` |
| test3                                    | W | `dbt_test2_and_test3` |
| test4                                    | W | `dbt_test4` |
| testT2                                   | W | `dbt_t2_and_versions` |
| testVersions                             | W | `dbt_t2_and_versions` |
| testVersionsReplaceValue                 | W | `dbt_t2_and_versions` |
| testLongKey                              | W | `dbt_long_keys` |
| testLongerKey                            | W | `dbt_long_keys` |
| testMultipleLongKeys                     | W | `dbt_long_keys` |
| testLongAndShortKeys                     | W | `dbt_long_keys` |
| testMultipleKeysWithSamePrefix           | W | `dbt_long_keys` |
| testDeleteTwoValues                      | P | `klong_delete_bits`; cross.sh (the nodes' bytes) |
| testDelete0                              | W | `dbt_delete` |
| testDelete1                              | W | `dbt_delete` |
| testDeleteOfNonExistingData0             | W | `dbt_delete_of_non_existing_data` |
| testDeleteOfNonExistingData1             | W | `dbt_delete_of_non_existing_data` |
| testRerun                                | W | `dbt_rerun` |
| testSame7BytesPrefix                     | W | `dbt_small_cases` |
| testGetSmallerKey                        | W | `dbt_small_cases` |
| testSplit0                               | W | `dbt_splits` |
| testSplit1                               | W | `dbt_splits` |
| testSpaceSplit1                          | W | `dbt_splits` |
| testSplitInSingleTransaction             | W | `dbt_splits` |
| testSplitTwoSplitsInOneTransaction       | W | `dbt_splits` |
| testSpaceSplitAddBackwards               | W | `dbt_splits` |
| testSpaceSplitOfRoot                     | W | `dbt_splits` |
| testTimeSplitOfRoot                      | W | `dbt_splits`, but the root's time (the index's) |
| testManyKeysInOneTransaction             | W | `dbt_small_cases` |
| testGet1                                 | W | `dbt_small_cases` |
| testGet2                                 | W | `dbt_long_keys` |
| testGetWithLongerKey                     | W | `dbt_long_keys` |
| testGetWithLongAndShortKeys              | W | `dbt_long_keys` |
| testGetBeforeFirstSet                    | W | `dbt_small_cases` |
| testWithRandomData                       | W | `dbt_with_random_data` |
| testWithMoreRandomData                   | W | `dbt_with_random_data` |
| testSplit3                               | W | `dbt_split3` |
| testSpecialCase                          | W | `dbt_special_case` |
| testPrintGraph1                          | W | `dbt_special_case` |
| testPrintGraph2                          | W | `dbt_special_case` |
| testTwoBinaryKeysInOneTransaction        | W | `dbt_two_binary_keys` |
| testManyOverwrites                       | W | `dbt_overwrites` |
| testCrazyKeys                            | W | `dbt_crazy_keys` |
| testSettingValueManyTimes                | W | `dbt_overwrites` |
| tGetFirst1                               | W | `dbt_get_first` |
| tGetFirst2                               | W | `dbt_get_first` |
| testCrash1                               | P | `start_crash_cuts`; `sdb_cut_stream` |
| testCrash2                               | P | `start_crash_cuts`; `sdb_cut_stream` |
| testCrash3                               | P | `start_crash_cuts`; `sdb_cut_stream` |
| testCrash4MetaBlock                      | P | `recover_crash_in_meta_block_header` |
| testCrash5InTransSize                    | P | `start_crash_cuts` (the size cut after 1 to 4) |
| testCrash6TornSizeBelowMin               | W | `dbt_crash6_torn_size_below_min` |
| testCrash7AtMetaBlockPosition            | W | `dbt_crash7_at_meta_block_position` |
| testCrash8InCreation                     | W | `dbt_crash8_in_creation` |
| testSyncAfterStreamFailure               | P | `durable_write_fails` |
| testKeyTransformation1                   | P | `api_transformations` |
| testKeyTransformation2                   | P | `api_transformations` |
| testValueTransformation1                 | P | `api_transformations` |
| testValueTransformation2                 | P | `api_transformations` |
| testStop1                                | N | no `stop()`; a handle ends at its close |
| testStopGetException1                    | N | no `stop()`; a handle ends at its close |
| testStopGetException2                    | N | no `stop()`; a handle ends at its close |
| testStopExecute                          | N | no `stop()`; a handle ends at its close |
| testStopMultipleStopCalls                | N | no `stop()`; a handle ends at its close |
| testSecondStreamRefused                  | N | one stream, no `DbBuilder.stream()` |
| bug130403                                | W | `dbt_bug130403` |
| testStartInfoReportsEffectiveDistance    | P | `settings_open_checks` |
| testStartupDistance1                     | P | `settings_setters` |
| testStartupDistance2                     | P | `settings_setters` |
| testSetStartupDistanceInForceOrRefused   | P | `db_set_startup_distance` |
| testSetStartupDistanceClamped            | P | `db_set_startup_distance`, `settings_setters` |
| testGetOp                                | P | `settings_and_status_as_java` (gets=) |
| testStartupPos1                          | P | cross.sh: each record's startup pos, in its bytes |
| testPaceHoldsTheStartupSection           | P | `transseq_take1` and on (the take); cross.sh |
| testDecreaseOfStartupDistance            | P | `transseq_take1` and on (the take); cross.sh |
| testDeleteOfMissingKeyMarksNothing       | P | `dag_delete_missing_key`; cross.sh |
| testReplacedNodeLeavesD                  | P | cross.sh: D decides the nodes written |
| testTouchTransactionReplacedNodes        | P | cross.sh: D decides the nodes written |
| testTransactionTooLarge                  | P | `db_refusals` |
| testTransformedValueBeyondRecordLimit    | P | `db_transformed_value_beyond_record_limit` |
| testTooManyDirtyNodes                    | W | `dbt_too_many_dirty_nodes` |
| testRecordsWithinLimit                   | W | `dbt_records_within_limit` (60 transactions) |
| testClockOutOfRange                      | P | `db_refusals`; `api_refusals` |
| testJmxRetainDurationInDays              | N | JMX |
| testGetTransOfEveryValue                 | W | `dbt_get_trans_of_every_value` |
| testGetTransRefusesBadPositions          | W | `dbt_get_trans_refuses_bad_positions` |
| testSyncWaitsForTheCommitByte            | N | the buffer thread; a sync writes all in the call |
| testStopWritesAll                        | N | threads: `stop()`'s close thread |
| testStopWithRunningTransaction           | N | threads: `stop()`'s close thread |
| testCloseWaits                           | N | threads: `stop()`'s close thread |
| testWriterWaitingForRoomAfterFailedFlush | W | `durable_write_fails_in_execute`, C's analog |
| testReclaimInternalFractionValidation    | P | `settings_setters` |
| testCloseReportsFinalFlushFailure        | P | `durable_write_fails` (`BERGDB_IO`) |
| testCloseFailureSuppressedByBlockFailure | N | try-with-resources |
| testTryWithResourcesCloses               | N | try-with-resources |
| testCloseAfterStopAndTwice               | N | no `stop()`; a second close is a use after free |

## 1.2 `DbTesterFailure`

A failure after the go point, of a read or of a sync, fails the database
(005-01, 005-30). C's NOMEM side is `api_alloc_failures` and
`db_alloc_failures`; the storage's side, a write that fails, is
`durable_write_fails`. A read that fails on the storage had one C test,
`api_refusals`'s getTrans of a position inside a record; the loads of
index nodes, in a get, a scan, a warm-up and a put, and getTrans of a
damaged record are `dbt_reads_that_fail_on_the_storage` now, 15 cases
(section 2.4). The rest of the class is threads (a stop, an interrupt, a
close beside a read, the storage's thread) and Java's `Error`s and
unchecked exceptions, which C's callbacks and stream cannot throw.

| Method                                           | Class | C's test, or the reason |
|---|---|---|
| testValueTransformationThrows                    | N | a transformation cannot fail (`bergdb.h`) |
| testErrorIsThrownAsItIs                          | N | Java's `Error` |
| testReadErrorInPut                               | W | `dbt_reads_that_fail_on_the_storage` |
| testCorruptNodeInPut                             | W | `dbt_reads_that_fail_on_the_storage` |
| testAppendErrorInStore                           | P | `durable_write_fails` |
| testWriterWaitingForTheLock                      | N | threads |
| testRefusedBeforeTheGoPoint                      | P | `db_refusals`; `api_refusals` |
| testReadErrorInGetOne                            | W | `dbt_reads_that_fail_on_the_storage` |
| testReadErrorInGetMany                           | W | `dbt_reads_that_fail_on_the_storage` |
| testCorruptNodeInGetOne                          | W | `dbt_reads_that_fail_on_the_storage` |
| testCorruptNodeInGetMany                         | W | `dbt_reads_that_fail_on_the_storage` |
| testUncheckedReadFailsTheDatabase                | N | a stream's unchecked exception or `Error` |
| testErrorInStopConditionFailsTheDatabase         | N | a stop function cannot fail |
| testBadKeyCountInGetOne                          | W | `dbt_reads_that_fail_on_the_storage` |
| testBadKeyCountInGetMany                         | W | `dbt_reads_that_fail_on_the_storage` |
| testBadKeyCountInPut                             | W | `dbt_reads_that_fail_on_the_storage` |
| testReadErrorInWarmup                            | W | `dbt_reads_that_fail_on_the_storage` |
| testSyncFails                                    | P | `durable_write_fails` |
| testInterruptedSync                              | N | threads: an interrupt |
| testReadDuringStop                               | N | threads: a read during the close |
| testGetDuringClose                               | N | threads: a read during the close |
| testGetTrans                                     | W | `dbt_reads_that_fail_on_the_storage` |
| testGetTransOfARecordBeingAppended               | N | the writer thread (021-13) |
| testGetTransBelowTheCut                          | P | `api_reclaim_directory` |
| testGetTransChecksum                             | P | `records_parse` (the parse); section 2.4 |
| testGetTransMalformed                            | P | `records_parse` (the parse); section 2.4 |
| testGetTransBadValueSize                         | P | `records_parse` (the parse); section 2.4 |
| testParseTransWraps                              | N | Java's wrap of a `RuntimeException` |
| testFailedStartClosesStorage                     | P | corruptset.sh (014-01's zero fill) |
| testErrorInFlushFailsSync                        | N | an `Error` in the buffer thread |
| testBackgroundWriteFailureFailsReads             | N | the storage thread |
| testUncheckedCloseErrorAfterFailedWriteFailsSync | N | the storage thread |
| testCloseWaitsForTheFailedStreamsClose           | N | threads |
| testCloseReportsBackgroundWriteFailure           | P | `durable_write_fails` (`BERGDB_IO`) |
| testCloseAfterStopReportsBackgroundWriteFailure  | N | no `stop()` |
| testCloseOfFailedDatabaseReturnsNormally         | N | C's close gives `BERGDB_IO`: section 3.1 |
| testStopWhoseCloserCannotStart                   | N | threads, `OutOfMemoryError` |
| testErrorInSyncOrCacheSizeFailsTheDatabase       | N | Java's `Error`; the eviction thread |

## 1.3 `DbTesterJavadoc`

| Method                                       | Class | C's test, or the reason |
|---|---|---|
| testGetOneAndTheTransaction                  | W | `dbt_get_one_and_the_transaction` |
| testTransBuilderOneOperationPerKey           | P | `db_trans_build` |
| testSecondStartRefused                       | N | no `start()`: `bergdb_open` is one call |
| testCallsBeforeStartAndAfterStop             | N | no `start()` or `stop()` |
| testOwnThreadsAreDaemons                     | N | threads |
| testGetManyAtMostN                           | P | `gm_at_most_n` (a count of 0: 11, point 4) |
| testEodOnceAtTheEnd                          | P | `gm_eod_once_at_the_end` |
| testBuilderRefusals                          | P | `settings_open_checks`, `api_refusals` |
| testBuilderCacheSizeIndicatorBelowOneRefused | P | `settings_open_checks` |
| testKeysAndValues                            | P | `api_keys_and_values` |
| testCoreWritesBergDbsKeys                    | P | `api_core_writes_bergdbs_keys` |
| testCountersAndListedDeletes                 | P | `api_counters_and_listed_deletes` |
| testOptimisticTransactions                   | P | `api_optimistic_transactions`, but its hash |
| testKvTimeIsTheEntrysTime                    | P | `api_kv_time_is_the_entrys_time` |
| testGetManyDefaultsAndOneCall                | P | `api_create_and_read` (the defaults) |

## 1.4 `DbTesterLongKeys`

| Method                   | Class | C's test, or the reason |
|---|---|---|
| testLongKeyRestart       | P | `api_long_keys` |
| testLongKeyAfterItsStart | P | `api_long_keys` |

## 1.5 `DbUtil`

`DbUtil.checksum` is a test tool of Java's tests: a hash of a database's
pairs. C's tests compare states their own way (`f_start.c`'s
`state_digest`, the check lines of `cross.sh`'s workloads), and C has no
such function to test.

| Method                        | Class | C's test, or the reason |
|---|---|---|
| testChecksumForEmptyDb        | N | `DbUtil.checksum`, a Java test tool |
| testChecksumForOneKv1         | N | `DbUtil.checksum`, a Java test tool |
| testChecksumForDiffInValue    | N | `DbUtil.checksum`, a Java test tool |
| testChecksumForDiffInKey      | N | `DbUtil.checksum`, a Java test tool |
| testChecksumForDiffInTime1    | N | `DbUtil.checksum`, a Java test tool |
| testChecksumForDiffInTime2    | N | `DbUtil.checksum`, a Java test tool |
| testChecksumWithMultipleKvs   | N | `DbUtil.checksum`, a Java test tool |
| testChecksumOfRange1          | N | `DbUtil.checksum`, a Java test tool |
| testChecksumOfRange2          | N | `DbUtil.checksum`, a Java test tool |
| testThatInternalKvNotIncluded | N | `DbUtil.checksum`, a Java test tool |
| testGetNodesOnPathToKv1       | N | `DbUtil.getNodesOnPathToKv`, a debug tool |
| testGetNodesOnPathToKv2       | N | `DbUtil.getNodesOnPathToKv`, a debug tool |
| testDbTimeToUtc               | P | `clock_time_to_utc` |
| testDbTimeToUtcFromThreads    | N | threads |

## 1.6 `DbTesterJavadoc` on `main` after the pin

`a848c62` and `f490cfa` (020-27, Q2, 17:54): the Core API refuses every
null argument, and every argument out of its range, with
`IllegalArgumentException`. C's API refuses a NULL and a negative count
with `BERGDB_ARG` already (`bergdb.h`, section B):
`dbt_null_and_range_arguments` checks every function that takes a pointer,
with nothing written and the database going on after. Java's other cases
have no counterpart in `bergdb.h`: `start(null)`, `DbBuilder`'s setters
(C's options are a struct; a NULL clock is the system clock), a key of no
segments (C's keys are bkeys, and the empty bkey is a key), a `GetMany`
used twice (C's read context serves any number of calls) and
`addReadHashes()` (the Pub API's).

| Method                        | Class | C's test, or the reason |
|---|---|---|
| testDbNullArguments           | W | `dbt_null_and_range_arguments`, but `start()` |
| testDbBuilderNullArguments    | N | `DbBuilder`'s setters; the options are a struct |
| testTransBuilderNullArguments | W | `dbt_null_and_range_arguments` |
| testGetManyNullArguments      | W | `dbt_null_and_range_arguments` |
| testRangeArguments            | W | `dbt_null_and_range_arguments`, in part |


# 2. The tests written now

`c/test/unit/t_dbtester.c`, its table `dbtester_tests` in
`test/unit/main.c`. A database is Java's `DbBuilder.testSetup()`: the
test clock, no eviction, `bergdb_test_id`, in memory; in a directory
under `TMPDIR` where a test restarts it or changes its files (a helper
reads and writes a directory's `.bergdb` files by name, and cuts the
stream at a position as a crash leaves it).

## 2.1 Results

`dbt_test1`, `dbt_test2_and_test3`, `dbt_test4`, `dbt_t2_and_versions`,
`dbt_long_keys`, `dbt_delete`, `dbt_delete_of_non_existing_data`,
`dbt_rerun`, `dbt_small_cases`, `dbt_splits` (node sizes 8, 14 and 30;
splits over transactions, in one transaction, backwards, of the root),
`dbt_with_random_data` (25 and 1,000 keys; Java's second is an f-test),
`dbt_split3`, `dbt_special_case`, `dbt_two_binary_keys`, `dbt_overwrites`,
`dbt_crazy_keys` (keys of up to 10,019 bytes), `dbt_get_first` and
`dbt_bug130403`: each value read back at the times Java reads it, and the
absent keys beside them.

## 2.2 getTrans

`dbt_get_trans_of_every_value` (005-34): records of 20 values of 500
bytes until three cross a meta block; every value's `tpos` from a get is
its transaction's, and `bergdb_get_trans` of it gives its time and last
byte; again after a restart, at the default startup distance (every
transaction rerun) and at 20,000 bytes. `dbt_get_trans_refuses_bad_positions`
(005-34, 005-43): eleven positions refused with `BERGDB_ARG` before any
read, the database going on.

## 2.3 Crashes and the record limit

* `dbt_crash6_torn_size_below_min`: the stream cut after the first byte of
  a record's size, that byte 8; the open takes the stream as before the
  record, a transaction after, and a second open has both.
* `dbt_crash7_at_meta_block_position` (005-27): a record sized, as Java's
  test sizes it, to end at the second meta block's position (C's record
  ends there too: its overhead is Java's); cuts at that position, after
  its block, and inside a record across the next block; each opens, takes
  a transaction and opens again.
* `dbt_crash8_in_creation` (005-33; an f-test in Java): every cut of the
  264-byte creation, and the creation with its commit byte 0, refused with
  `DatabaseNotCreatedException` and the stream unchanged, through the
  start on a stream in memory (`sdb_open`); eight of them through
  `bergdb_open` in a directory, whose open forces the directory's parent
  (as Java's `createDirIfNeeded`), about 10 ms each on F53: all 264 there
  took 3 to 4.5 s.
* `dbt_too_many_dirty_nodes` (005-31; an f-test in Java) and
  `dbt_records_within_limit` (005-17; an f-test in Java), through `db.h`
  with `db_config.record_limit` at 200 kB, as Java lowers
  `StoredTrans.recordLimit`, in a directory, read back through `bergdb.h`
  after a restart: the update of every 10th of 10,000 keys refused
  ("005-31"), nothing appended, the later updates taken, and the startup
  section under three startup distances after 500 more transactions;
  records of a 170 kB value and 50 small puts each at most the limit and
  two meta blocks, 60 transactions of Java's 300 (10 MB of stream), and
  every key after the restart as the run wrote it.

## 2.4 Reads that fail on the storage

`dbt_reads_that_fail_on_the_storage`: `DbTesterFailure`'s
`startEvicting` and `fill` (node size 8, a startup distance of 1,000
bytes, 2,000 keys ten a transaction) made once, its files copied for each
case and opened with a budget of 1 byte, so that every index node that
can leave memory has left at the end of each call, as Java's
`Eviction.Schedule.EVERY`. Then the files are damaged under the open
database, as Java's `FaultStream` and `KeyCountStream` damage its reads,
in three ways:

* cut at the creation's end: a read there is an `EOFException`, which the
  stream gives as a `StreamIoException` (Java: a read's `IOException`);
* the last byte of every 8-byte word flipped from there on, a node's
  checksum among them (Java flips each read's last byte):
  `StreamChecksumException`;
* every key node's count set to 0x7fff with its checksum made right
  (`KeyCountStream`): `StreamFormatException` "Bad key count" (015-07).

And five calls meet it: a get (`testReadErrorInGetOne`,
`testCorruptNodeInGetOne`, `testBadKeyCountInGetOne`), a scan (the
`GetMany` cases), a transaction's warm-up (`testReadErrorInWarmup`,
`testBadKeyCountInPut`), a put after its go point (`testReadErrorInPut`,
`testCorruptNodeInPut`: a key transformation damages the files and gives
the key a path that the warm-up did not read) and `bergdb_get_trans`
(`testGetTrans`; for the flipped bytes the record's commit byte is wrong,
"Bad lastByte", Java's `StreamFormatException` there too). In each of the
15 cases the call gives `BERGDB_FAILED`, a `DbFailedException` whose text
names the cause; a transaction, a read and getTrans after it are refused
with the same cause; the status works; nothing is appended; the close
gives `BERGDB_OK` or `BERGDB_IO`. A restart on the undamaged files has
every key, and a transaction.

## 2.5 The Javadoc's promises

`dbt_get_one_and_the_transaction`: no value for an absent key or before
its transaction; the value's `tpos` is its transaction's, whose getTrans
gives `tt`, `tpos` and `last_pos`; `next_pos` is the stream's length.
`dbt_null_and_range_arguments`: section 1.6.

## 2.6 A write that fails in an execute

`f_durable.c`'s `durable_write_fails_in_execute`: C's counterpart of
`DbTester.testWriterWaitingForRoomAfterFailedFlush` (005-35), whose writer
waits in Java's buffer thread for room after a failed flush. C writes the
full buffer within `bergdb_execute`: a child process with its files
limited to 150,000 bytes (`RLIMIT_FSIZE`, as `durable_write_fails`)
executes a transaction of 1,000 bytes and one of 11 MB, more than the
10 MB buffer; the second gives `BERGDB_FAILED` (the cause the write's
`IOException`, "File too large"), the next transaction too, and the close
`BERGDB_IO`, nothing left allocated; a restart finds the first and takes
one more. About 2 s of wall time, most of it the child's start and the
forces.

## 2.7 Time

The 28 unit tests take about 0.6 s of CPU in the test build (0.3 s in
the release build) and 3.5 to 5.5 s of wall time on F53 under a load of
18 to 27, most of it the forces (`F_FULLFSYNC`) of the eight tests in
directories; none takes a second of CPU. `dbt_reads_that_fail_on_the_storage`, `dbt_too_many_dirty_nodes`
and `dbt_records_within_limit` take 0.6 to 1 s of wall time each there,
0.1 s of CPU.


# 3. Findings

## 3.1 A difference: the close after a reported failure

`DbTesterFailure.testCloseOfFailedDatabaseReturnsNormally` (019-09,
Frans's option (a)): Java's `close()` of a database that a call has
failed with the storage's failure returns normally, as that call reported
it; `close()` throws `StreamIoException` only for a background write's
failure that no call reported (`testCloseReportsBackgroundWriteFailure`).
C's `bergdb_close` returns `BERGDB_IO` whenever the last write or force
failed, or the storage had failed before, reported or not (`bergdb.h`,
`bergdb_close`; `durable_write_fails` expects `BERGDB_IO` from the close
after the sync gave `BERGDB_FAILED`). C reports more, never less; no data
is at stake. `bergdb.h`'s "Java's close() does not report it (012-03,
6.8)" is from before 019-09. Options: (a) keep C's close, and say so in
`bergdb.h` and in `c/readme.md`, section 11, as a departure (a few
lines); (b) follow Java: `BERGDB_OK` from the close when a call has
returned `BERGDB_FAILED` for the storage's failure (a flag in `db.c`, the
test's expectation changed; about 20 lines). Recommended: (a), as a C
caller that closes after `BERGDB_FAILED` loses nothing by a second code,
and one that closes after an unreported failure needs it.

## 3.2 No fault

Every new test passed on C as it was; no fault of Java's was found. The
damage of section 2.4 gives the causes that Java's tests expect, also
"Bad lastByte" for a damaged record's getTrans, which Java's corrupt
reads give. Negative controls, in a copy of `c/`: without recovery's
completion of a torn size below the least record size (`recover.c`'s
`trans_header_fix_bytes`), `dbt_crash6_torn_size_below_min` fails, the
open refused; with the take's budget unbounded (`db.c`'s call of
`ts_take`), `dbt_records_within_limit` fails, a record over the limit and
then `db_execute`'s assert; with a failure that leaves the database
active (`db.c`'s `set_failed`), `dbt_reads_that_fail_on_the_storage`
fails, getTrans taken after the failure.

## 3.3 Notes

* `bergdb_open` of an existing directory forces its parent directory, as
  Java's `FileStream` does (`plat_mkdirs`), about 10 ms on a loaded F53: a
  test that opens many times pays it (section 2.3).
* Nanotest runs `@Nano` methods not named `test*`: here three, and about
  31 in the Core's packages in all, for 022-05's index.


# 4. Left

None. The one candidate, `testWriterWaitingForRoomAfterFailedFlush`'s
counterpart in C, was written (section 2.6).


# Log

2026-11-09. Written by worker t12 of the session `022-bergdb-c`, with
`c/test/unit/t_dbtester.c`.
