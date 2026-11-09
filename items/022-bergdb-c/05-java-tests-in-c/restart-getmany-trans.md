# 022-05 Java's tests in C: restarts, getMany, transactions and nodes

Created 2026-11-09 by Frans Lundberg (worker t13 of the session
`022-bergdb-c`). A part of 022-05, the inventory of Java's Core tests in
C; the session writes its index.

Java's test classes of this part, as `bergdb.core` has them on `main` at
`2566df1` (2026-11-09 17:18): DbTesterRestart, DbTesterGetMany,
DbTesterStream, StoredTrans, TransSeq, KeyModSet, Trans, TransNodes,
StoredTopNode, StoredValueNode, StoredKeyNode, NodeChecksum, DatabaseId,
DbStarter, DbClock, SystemClock, RerunException. Each test method is
ported (P: a C test or a harness checks what it checks), written now
(W), not for C (N) or left (L). The C tests are in `c/test/unit/t_*.c`
and `c/test/func/f_*.c`.


# 1. In short

185 test methods: 131 P, 38 W, 16 N, 0 L.

The 38 written now are 28 new C tests, each passing in both builds; none
failed before a fix, so they found no fault of C (section 3.4: some of
them fail when a fault they aim at is put into C). Most of them are
restarts: C's unit tests restarted a database only for reclaim's
settings and the eviction, its functional tests in `f_start.c`,
`f_budget.c` and `f_api.c`:

* `t_restart.c` (new, 19 tests): DbTesterRestart's restarts through
  `db.h`, a database in a directory restarted by `db_close` and
  `db_open`, as Java's tests start a `Db` on a copy of its
  `MemoryStream`. Values, deletes and their history; deletes of missing
  long keys (Java's bug of 2026-10-12); transactions that change nothing
  (011-11's M18); the meta block's last transaction; the startup distance
  kept; the STM's boundary over a restart, also after an empty commit
  (005-70); the top node ordinals across 2^30, 2^31, 2^32 and 2^47, at
  their end and with reclaim (005-02), each history checked before and
  after a restart; a record's time, another node size and a meta block
  without one refused at the start with Java's texts, nothing written;
  one object per node after restarts (D, the node table and the memory
  nodes); Level 2's runs of puts, deletes, short and long keys, every key
  checked at eleven times after each restart, and the stream with
  restarts the one without, byte for byte; getMany after a restart
  (DbTesterGetMany.test4); random database ids.
* `f_restart.c` (new, 3 tests, through `bergdb.h`): the stream after a
  decrease of the startup distance with restarts, byte for byte (Java's
  f-test, smaller); values of 1 MB and of 20 MB over a restart; a restart
  after 131,300 transactions, past top node 32,768 (Java's f-test).
* `t_snode.c` (3 tests): the node parsers' refusals with Java's exception
  and text: a top node's negative or too large pointer count, an ordinal
  field that does not fit the node's slots, another format version of
  each kind of node, a key count and a value's and a key's size beyond
  the node.
* `t_records.c` and `t_serial.c` (3 tests): a record's node sizes outside
  the record, its size field, its got-dirty count.

Run times in the test build on F53 under a load of 25 to 35: each unit
test of `t_restart.c` 0.1 to 1.3 s, about 6 s in all, nearly all of it
the forces of the opens and closes (CPU about 0.5 s); the three of
`f_restart.c` about 8 s; the others a few milliseconds.


# 2. The classes

## 2.1 DbTesterRestart

Written now, in `t_restart.c`, and in `f_restart.c` those named `func_`:

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testCorruptRecordTimesRefused                 | W | `restart_record_times_refused` |
| testStmAfterRestart                           | W | `restart_stm` |
| test0                                         | W | `restart_values` |
| testRestartOfEmptyDatabase                    | W | `restart_empty_and_startup_distance` |
| longerThanStartup                             | W | `restart_longer_than_startup` |
| dbShouldRememberStartupDistance1              | W | `restart_empty_and_startup_distance` |
| dbShouldRememberStartupDistance2              | W | `restart_empty_and_startup_distance` |
| testOtherNodeSizeRefused                      | W | `restart_other_node_size_refused` |
| testNoNodeSizeRefused                         | W | `restart_no_node_size_refused` |
| testDelete1                                   | W | `restart_deletes` |
| testDelete2                                   | W | `restart_deletes` |
| testDeleteMissingLongKey                      | W | `restart_delete_missing_long_key` |
| testOneObjectPerNodeAfterRestarts             | W | `restart_one_object_per_node` |
| testLevel2RestartsKeepAllValues               | W | `restart_level2_keep_all_values` |
| testLevel2SameStreamWithRestarts              | W | `restart_level2_same_stream` |
| testSameStreamAfterDecreaseWithRestartsF      | W | `func_restart_same_stream_after_decrease` |
| testLastTransPosAfterRestart                  | W | `restart_last_trans_pos` |
| testRestartAfterTransactionsThatChangeNothing | W | `restart_after_changing_nothing` |
| testRestartAfterManyTopNodes                  | W | `func_restart_after_many_top_nodes` |
| testOrdinalsAcrossBoundaries                  | W | `restart_ordinals_across_boundaries` |
| testEndOfOrdinals                             | W | `restart_end_of_ordinals` |
| testOrdinalsWithReclaim                       | W | `restart_ordinals_with_reclaim` |

`restart_record_times_refused` has Java's eight cases, `sdb_refusals` had
two; `restart_other_node_size_refused` has every pair of sizes, on a
database as created and on a torn one, and Java's text, where
`sdb_refusals` and `f_start.c`'s `start_refusals` had one pair and the
exception's name; `restart_no_node_size_refused` adds the text;
`restart_stm` adds to `f_api.c`'s `api_stm_after_restart` the empty commit
after the restart and the transaction without reads; `restart_end_of_ordinals`
adds to `t_db.c`'s `db_top_ordinals` the restart and the internal
transaction.

Ported before, in `t_sdb.c`, `t_records.c`, `t_rstream.c` and `t_reclaim.c`
but where another file is named; the corrupt-stream set
(`corruptset.sh`, CorruptSet.java) also starts the refusal tests' damaged
streams with Java's and C's dumpers and compares the texts byte for byte:

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testEnlargedRecordSizeRefused           | P | `sdb_refusals_2026_3`, `records_enlarged_size` |
| testCorruptStartupPosRefused            | P | `sdb_refusals_2026_3` |
| testCorruptGotDirtyIdRefused            | P | `sdb_refusals_2026_3` |
| testOlderTopPosRefused                  | P | `sdb_refusals_2026_3` |
| testMetaBlockLastTransPosRefused        | P | `sdb_refusals_2026_3`, `rs_last_trans_spos_refused` |
| testReclaimSettingsKeptOverRestarts     | P | `reclaim_settings_kept_over_restarts` |
| testRefusedReclaimSettingChangesNothing | P | `reclaim_settings_refused_change_nothing` |
| testReclaimSettingInForceWritesNothing  | P | `reclaim_settings_in_force_write_nothing` |
| testReclaimSettingsKeptAcrossRestart    | P | `reclaim_settings_kept_across_restart` |
| testReclaimSettingsSurviveCuts          | P | `reclaim_settings_survive_cuts` |
| testStreamWithoutSettingsHasDefaults    | P | `reclaim_settings_none_defaults` |
| testMalformedSettingsRefusedAtStart     | P | `reclaim_settings_malformed_refused_at_start` |
| testReclaimSettingRefusedAtGoPoint      | P | `settings_setters` (`f_settings.c`) |
| testReclaimSettingAtEndOfOrdinals       | P | `db_top_ordinals` (`t_db.c`) |
| testVersionHighBytesRefused             | P | `sdb_refusals_2026_3` |
| testLevel2RestartsKeepAllValuesF        | P | unit size: W; f size passed once (3.3) |
| testLevel2SameStreamWithRestartsF       | P | unit size: W; f size passed once (3.3) |

## 2.2 DbTesterGetMany

In `t_dbgetmany.c`, `t_getmany.c` (`gm_`, `mdb_`), `t_dagvec.c` and
`t_restart.c`. `gm_prefix_has_the_prefix_key` and `f_api.c`'s
`api_prefix_has_the_prefix_key` are worker t11's, with 021-18.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| test1                             | P | `dbgm_test1` |
| test1Backward                     | P | `dbgm_test1_backward` |
| test2                             | P | `dbgm_test2` |
| test2Backward                     | P | `dbgm_test2_backward` |
| test3                             | P | `dbgm_test3` |
| test3Backward                     | P | `dbgm_test3` (both ways) |
| test4                             | W | `restart_get_many` (a restart: `t_restart.c`) |
| testEndpoint1                     | P | `dbgm_endpoint1` |
| testEndpoint2                     | P | `dbgm_endpoint2` |
| testEndpoint3                     | P | `dbgm_endpoint3` |
| testEndpointBackward              | P | `dbgm_endpoint_backward` |
| testCrazyKeys                     | P | `mdb_model` (random keys against a model), `t_dagvec.c` |
| testDeepSegment                   | P | `dbgm_deep_segment` |
| testStart1                        | P | `dbgm_start1` |
| testStart1Backward                | P | `dbgm_start1` (both ways) |
| testStart2                        | P | `dbgm_start2` |
| testStart3                        | P | `dbgm_start3_and_4` |
| testStart4                        | P | `dbgm_start3_and_4` |
| testStart5                        | P | `dbgm_start5` |
| testStartWithLongerKeys           | P | `dbgm_start_with_longer_keys` |
| testStartWith7                    | P | `dbgm_start_with_7` |
| testStartWithCrazyKeys1           | P | `mdb_model` (random start keys), `gm_start_key_random` |
| testStartWithCrazyKeys2           | P | `mdb_model` (random start keys), `gm_start_key_random` |
| testGt1                           | P | `dbgm_gt1` |
| testInclusiveStartKeyWithDeepTree | P | `gm_inclusive_start_key_with_deep_tree` |
| testStartKeyRandom                | P | `gm_start_key_random` |
| testFromIndexing1                 | P | `dbgm_from_indexing` |
| testFromIndexing2                 | P | `dbgm_from_indexing` (backward) |
| bug130606                         | P | `dbgm_bug130606` |
| bug130606b                        | P | `dbgm_bug130606` |
| bug130606c                        | P | `dbgm_bug130606` |
| bug130606backwards                | P | `dbgm_bug130606` |
| testGetOpCount                    | P | `dbgm_get_op_count` |
| testPrefixHasThePrefixKey         | P | `gm_prefix_has_the_prefix_key` (t11, 021-18) |

## 2.3 DbTesterStream

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testMoreData2                          | P | `start_restart_every_transaction`, `t_restart.c` |
| testDbOnFileMultipleTransactions       | W | `restart_values` |
| testCreatedTxt                         | N | created.txt: not in C's options (012-03, 6.3) |
| testTwoKvsInOneTransaction             | P | `restart_deletes` (pairs of one transaction) |
| testLargeTransaction                   | W | `func_restart_large_values` (20 MB) |
| testLargeTransactions                  | W | `func_restart_large_values` (five of 1 MB) |
| testReadOnlyStream1                    | P | `sdb_java_stream` (`t_sdb.c`): a start for reads |
| testReadOnlyStream2                    | N | the stream's Java API (ReadOnlyStream) |
| testSyncAfterOneCommitWaitsForOneForce | N | the buffer thread's timer (005-48) |
| testFirstCloseFailureIsReported        | N | the storage thread's close (015-78) |

testMoreData2's 2,000 puts and a restart: `f_start.c`'s
`start_restart_every_transaction` and `t_restart.c`'s restarts. The three
N: C has no `ReadOnlyStream` (its start for reads, `sdb.c`, writes
nothing, and `bergdb_open` opens a directory to write); no buffer thread
and its timer, and a sync forces in its call (C's forces: `t_stream.c`'s
`stream_forces`); no storage thread, and a close is made in
`bergdb_close`'s call, after which the handle is gone (012-13, Q2).

## 2.4 StoredTrans

In `t_serial.c`, `t_records.c` and `t_sdb.c`. The vectors' `records.txt`
also has 359 records with one change that Java's parser refuses, with
the exception's name (`t_records.c`). `records_node_size_outside_record`
also has testNegativeNodeSize's -32, on Java's record.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testNegativeNodeSize              | P | `records_negative_node_size` |
| testNodeSizeOutsideRecord         | W | `records_node_size_outside_record` |
| testCorruptRecordSize             | W | `serial_corrupt_record_size` |
| testGotDirtyCountOutsideRecord    | W | `serial_got_dirty_count_outside_record` |
| testKvSanity                      | N | Java's Kv object |
| testCorruptGotDirtyCount          | P | `serial_corrupt_got_dirty_count` |
| testRecordAboveLimit              | P | `serial_record_above_limit` |
| testSerialize1                    | P | `serial_serialize1` |
| testSerialize2                    | P | `serial_serialize2` |
| testTopPosOfTopNodeInTransaction  | P | `serial_top_pos` |
| testTopPosOfEarlierTopNode        | P | `serial_top_pos` |
| testRefusesOldFormat              | P | `serial_refuses_other_formats` |
| testRefusesNewerFormat            | P | `serial_refuses_other_formats` |
| testSerializeWithGotDirtyIds      | P | `serial_got_dirty_ids` |
| testSerializeTransWithDelete      | P | `serial_delete_startup_pos_keys` |
| testSerializeWithNewStartupPos1   | P | `serial_delete_startup_pos_keys` |
| testSerializeWithNewStartupPos2   | P | `serial_delete_startup_pos_keys` |
| testSerializeAndCheckKey          | P | `serial_delete_startup_pos_keys` |
| testSerializeAndCheckKey2         | P | `serial_delete_startup_pos_keys` |
| testSameBytesFromReusedSerializer | P | `serial_same_bytes_reused` |
| testFindNode                      | P | `sdb_find_node` (`t_sdb.c`) |
| testGetValueNode                  | N | StoredTrans.getValueNode: no caller in Java but its test |

## 2.5 TransSeq and KeyModSet

In `t_transseq.c` and `t_keymod.c`.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| test0                            | P | `transseq_add` |
| testAddOne                       | P | `transseq_add` |
| testAddThree                     | P | `transseq_add` |
| testPosOfTransBefore             | P | `transseq_pos_of_trans_before` |
| testPosOfTransBeforeWithEmptySeq | P | `transseq_pos_of_trans_before` |
| testTake1                        | P | `transseq_take1` |
| testTakeWithBudget               | P | `transseq_take_with_budget` |
| testTake2                        | P | `transseq_take2` |
| testShare                        | P | `transseq_share` |
| testDeadline                     | P | `transseq_deadline` |
| testDeadlineAfterDecrease        | P | `transseq_deadline_after_decrease` |
| testDecrease                     | P | `transseq_decrease` |
| testSumsAfterTake                | P | `transseq_sums_after_take` |
| testDivluExact                   | P | `transseq_divlu_exact` |
| testShareFpExact                 | P | `transseq_share_fp_exact` |
| testShareFpClamp                 | P | `transseq_share_fp_clamp` |
| testDitherFp                     | P | `transseq_dither_fp` |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testStartupBoundary | P | `keymod_startup_boundary` |
| test1               | P | `keymod_test1` |
| test2               | P | `keymod_test2` |
| test3               | P | `keymod_test3` |
| testFutureTime      | P | `keymod_future_time` |
| testResize          | P | `keymod_resize` |
| testBins1           | P | `keymod_bins1` |
| testBins2           | P | `keymod_bins2` |

## 2.6 Trans, TransNodes, DatabaseId and RerunException

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testLoneSurrogateRefused | P | keys: `strutil_is_well_formed_utf8`, the vectors (3.2) |
| testNegativeHash         | N | no hash in C's API: a key read takes the key |
| testTransReuse           | P | `api_stm_after_restart` (`f_api.c`); another database's: 3.2 |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| test1                  | P | `transnodes_basics` (`t_serial.c`) |
| testLarge1             | P | `transnodes_basics` (the arrays grow; clear) |
| testLarge2             | N | Java's array length after 1,100 clears, a memory policy |
| testIndexNodeIterator1 | P | `transnodes_basics` (top nodes first, then key nodes) |
| testIndexNodeIterator2 | P | `transnodes_basics` (empty) |
| testIndexNodeIterator3 | P | `transnodes_basics` |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| twoRandomIdsShouldNotBeEqual     | W | `restart_random_ids` |
| testCreateLater                  | N | Java's CREATE_LATER_MARKER object |
| testThatNullBytesCannotBeCreated | N | C's option of zeros asks for a random id (3.2) |
| testEquals                       | N | Java's equals |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| test1 | N | Java's exception object; C's ERR_RERUN text names the key hash |

## 2.7 The nodes and their checksum

In `t_snode.c`, `t_tnode.c`, `t_nwrite.c` and `t_checksum.c`; the
corrupt-stream set has the node tests' changes on Java's streams.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testNegativePointerCount             | W | `snode_top_refusals` |
| testRefusesOtherVersion              | W | `snode_top_refusals` |
| testStreamPointerTimesKept           | P | `tnode_stream_pointer_times_kept` |
| testOrdinalsRoundTrip                | P | `tnode_ordinals_round_trip` |
| testParserRefusesSlotsThatDoNotFit   | W | `snode_top_refusals` |
| testOrdinalField                     | P | `tnode_ordinal_field` |
| testTopNodeToLongs2                  | P | `tnode_to_longs` |
| testTopNodeToLongs1                  | P | `tnode_to_longs` |
| testRefusesPointerCountBeyondTheNode | W | `snode_top_refusals` |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testToBytesAndBack                   | P | `nwrite_value_to_bytes_and_back` |
| testToBytesAndBackAndCheckKey        | P | `nwrite_value_to_bytes_and_back` |
| testRefusesOtherVersion              | W | `snode_value_refusals` |
| testThatSposIsSetWhenParsedFromBytes | P | `nwrite_value_to_bytes_and_back` |
| testOffsetFromTrans                  | P | `nwrite_offset_from_trans` |
| testOffsetFromTransAcrossMetaBlock   | P | `nwrite_offset_from_trans`, `nwrite_tpos_unsigned` |
| testRefusesSizesBeyondTheNode        | W | `snode_value_refusals` |
| testRefusesBadKey                    | P | `snode_refuses_bad_key`, corruptset |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testSerialize                    | P | `nwrite_key_serialize` |
| testRefusesOtherVersion          | W | `snode_key_refusals` |
| testRefusesKeyCountBeyondTheNode | W | `snode_key_refusals` |
| testRefusesBadKlongs             | P | `snode_refuses_bad_klongs`, corruptset |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| test0              | P | `checksum_example` |
| testWithLongArray1 | P | `checksum_with_long_array1` |
| testWithLongArray2 | P | `checksum_with_long_array2` |
| testZeroReplace    | P | `checksum_zero_replace` |

## 2.8 DbStarter and the clocks

In `t_sdb.c`, `t_restart.c`, `t_knode.c` and `t_clock.c`.

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testTransactionOrder             | P | `sdb_refusals`, `restart_record_times_refused` |
| testParsedKeyNodeTimeOrder       | P | `knode_validate_time_text` |
| testCheckStreamPointersOfKeyNode | P | `sdb_starter_node_texts` |
| testPrevMap1                     | N | DbStarter.PrevMap: no caller in Java but its tests |
| testPrevMap2                     | N | DbStarter.PrevMap |
| testPrevMap3                     | N | DbStarter.PrevMap |
| testEmptyPrevMap                 | N | DbStarter.PrevMap |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| test1                          | P | `clock_dbclock_test1` |
| testTime                       | P | `clock_dbclock_time` |
| testClockOutOfRange            | P | `clock_dbclock_out_of_range` |
| testTimeMarginForInternal      | P | `clock_dbclock_time_margin_for_internal` |
| testClockGoesBack              | P | `clock_dbclock_clock_goes_back` |
| testCurrentTimeLeavesTheMargin | P | `clock_dbclock_current_time_leaves_the_margin` |
| testLookupTime                 | P | `clock_dbclock_lookup_time` |

| Method | P/W/N/L | C test, or the reason |
|---|---|---|
| testStrictlyIncreasing | P | `clock_system_clock` |
| testClockSetBack       | P | `clock_system_clock` |

testTransactionOrder's non-increasing tpos: `starter.c`'s
`validate_transactions` is static, and a walk of a stream gives
increasing positions; the times are checked through a start.


# 3. Findings

## 3.1 Faults

No fault of C: every new test passed in both builds, the release build's
unit and functional tests too. No fault of Java.

Two things for the session, neither a fault: DbStarter.PrevMap and
StoredTrans.getValueNode have no caller in Java but their tests, and C
has neither.

## 3.2 Departures and adapted tests

No new departure; where Java's tests use the stream's Java API, the
tests take C's way:

* A restart is `db_close` and `db_open` on a directory, where Java's
  tests start a `Db` on a copy of a `MemoryStream`; C's memory stream is
  for a database that does not restart. Java's `CutStream` is the
  directory, which cuts whole files: `restart_ordinals_with_reclaim`
  checks reclaim's decided cut (the first available position and time).
* `func_restart_same_stream_after_decrease` is Java's f-test made
  smaller: 1,000,000 bytes lowered to 400,000, the least that
  `bergdb_set_startup_distance` sets (Java's 2,000,000 to 500,000), after
  1,200 puts and 300 more, restarts every 10.
* `restart_random_ids` reads the id from the meta block in memory:
  `db.c`'s `database_id` is the creation's only. C's options ask for a
  random id with all zeros, so no database has the id of zeros, which
  Java's DatabaseId.createFromBytes refuses.
* Trans.testLoneSurrogateRefused: C's keys are UTF-8 bytes, and a lone
  surrogate's (ED A0 80) are not well-formed, which `bergdb_ikey_to_bkey`
  refuses (021-05; `t_strutil.c` and the vectors' utf8 and ikey lines); C's
  values are bytes, not text.
* Trans.testTransReuse executes one `Trans` twice, and then on another
  database; a `bergdb_trans` belongs to its database (`bergdb.h`:
  BERGDB_ARG), C's API's design.

## 3.3 Java's f sizes, once

`restart_level2_keep_all_values` at Java's f size (1,000 transactions,
seeds 1 and 2, node sizes 30 and 8, restarts every 50 and 25) and
`restart_level2_same_stream` at its f size (seed 3, 600 transactions,
restarts every 40) were run once in the test build, the counts changed
and nothing else: both passed, in 3 s.


## 3.4 Negative controls

Each in a copy of `c/`, the test build:

* A start that leaves the meta block's last transaction as the meta block
  on disk has it (Java's bug of 2026-10-12): `restart_last_trans_pos` and
  `restart_level2_same_stream` fail, and `t_reclaim.c`'s
  `reclaim_settings_kept_over_restarts`.
* A top node's ordinal written with Java's int shift, as before its fix of
  StoredTopNode.toLongs: `func_restart_after_many_top_nodes` fails at the
  restart, as Java's test did.
* Java's comments say that its Level 2 tests fail without
  NodeCollection.resolvePointers() and without canonicalNode()'s use of
  the stored position. In C, `restart_level2_same_stream` and
  `restart_level2_keep_all_values` pass without either (`db.c`'s
  `nc_resolve_pointers` of the taken nodes; `starter.c`'s `canonical_node`
  with the stored position unused); other tests fail: `t_evict.c`'s
  `evict_twins` and `reclaim_settings_kept_over_restarts` without the
  first, `t_sdb.c`'s `sdb_refusals_2026_3` and `sdb_found_021_12` and
  `reclaim_settings_kept_over_restarts` without the second.


# 4. Left

None. testRestartAfterManyTopNodes, an f-test in Java, is
`func_restart_after_many_top_nodes`, about 2.6 s in the test build under
load.
