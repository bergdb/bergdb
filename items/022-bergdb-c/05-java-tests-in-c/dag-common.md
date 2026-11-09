# 022-05 dag and common: Java's tests of `bergdb.dag` and `bergdb.common` in C

Created 2026-11-09 by Frans Lundberg. Status: done.

Worker t15's part of 022-05: every test method of the classes in
`java/src/bergdb/dag/` and `java/src/bergdb/common/` at `main`'s
`2566df1` (2026-11-09 17:18), classed as the brief says: **P** ported (C's
test named, or the harness), **W** written now, **N** not for C (the
reason), **L** left. A test method is what nanotest runs (its
`MethodFilter`): a static method with `@Nano`, or a static `void testX()`
without parameters, private ones too; so `MyLongSet`'s ten and
`KeyNodeTester.testToPreviousState3` count, though they have no `@Nano`.

| Package | Methods | P   | W | N  | L |
|---|---|---|---|---|---|
| dag    | 111 | 105 | 2 | 4  | 0 |
| common | 82  | 21  | 0 | 61 | 0 |
| in all | 193 | 126 | 2 | 65 | 0 |

The dag's tests were ported test by test when C's modules were made
(012-04: `Klong`, `Keys`, `Spos`; 012-07: `KeyNodeTester`, `TopNode`,
`TopTester`; 012-08: `DagTester`), and 022-01 and 022-02 added those of
2026.3 and 2026.4 (021-05, 021-06, 021-15, 021-16). Each C test names the
Java test it ports in its comment; each was read beside its Java test for
this record, and checks what the Java test checks. Two were missing, the
in-place pointer changes of 015-14 (section 3). Of `bergdb.common`, C has
the classes the Core's bytes need (`Bytes`, `StringMap`,
`StringUtil.isWellFormedUtf8`, `MyChecksum`'s CRC-32 in `TransSeq`); the
rest are Java's helpers of Java's types, threads, files and the
encryption, which C leaves out (`c/readme.md`, section 11; 012-18,
section 3.3).

The two new tests pass in both builds, before any change: no fault of C
was found, none of Java's, and no departure.


# 1. `bergdb.dag`

## 1.1 `Klong`: `t_klong.c`

| Method                        | Class | C's test |
|---|---|---|
| testPrefixLength1             | P | `klong_prefix_length1`                         |
| testPrefixLength2             | P | `klong_prefix_length2`                         |
| testPrefixLength3             | P | `klong_prefix_length3`                         |
| testTime                      | P | `klong_time`, with the range's ends            |
| testLength                    | P | `klong_length`                                 |
| testHeader                    | P | `klong_header`                                 |
| testIntType                   | P | `klong_int_type`                               |
| testKey1                      | P | `klong_key_string`                             |
| testKey2                      | P | `klong_key_string`                             |
| testKey3                      | P | `klong_key_string`                             |
| testKey4                      | P | `klong_key4`                                   |
| testKey5                      | P | `klong_key5`                                   |
| testSortOrder1                | P | `klong_sort_order`, with the edge bytes        |
| testCreateKlongs              | P | `klong_create_klongs`                          |
| testCreateCompareValueTwoWays | P | `klong_compare_value_two_ways`, lengths 0 to 7 |
| tDeleteBits                   | P | `klong_delete_bits`                            |
| tDelete1                      | P | `klong_delete1`                                |
| testIsKey                     | P | `klong_is_key`                                 |

## 1.2 `Keys`: `t_keys.c`

| Method                | Class | C's test |
|---|---|---|
| testByteSize0         | P | `keys_byte_size`                                         |
| testConversion0       | P | `keys_conversion`                                        |
| testConversion1       | P | `keys_refused`                                           |
| testLoneSurrogate     | P | `keys_lone_surrogate`: the WTF-8 bytes of Java's Strings |
| testBkeyWithoutIkey   | P | `keys_bkey_without_ikey`                                 |
| testBkeyIkeyRoundTrip | P | `keys_bkey_ikey_round_trip`                              |
| testLongs             | P | `keys_compare_unsigned`                                  |
| testArrays            | P | `keys_compare_arrays`                                    |
| testPrefix1           | P | `keys_prefix1`                                           |
| testPrefix2           | P | `keys_prefix2`                                           |

Java's texts ("lone surrogate", "no ikey") have no counterpart: C's
conversions return false, and `bergdb_ikey_to_bkey` and
`bergdb_bkey_to_ikey` give `BERGDB_ARG` without a database to hold a text.

## 1.3 `Spos`: `t_spos.c`

| Method            | Class | C's test |
|---|---|---|
| testAlign1        | P | `spos_align1`         |
| testAlign2        | P | `spos_align2`         |
| testIsNull        | P | `spos_null_and_valid` |
| testIsValid       | P | `spos_null_and_valid` |
| testIsValidOrNull | P | `spos_null_and_valid` |
| testNextVpos1     | P | `spos_next_vpos1`     |
| testNextVpos2     | P | `spos_next_vpos2`     |

## 1.4 `KeyNodeTester`: `t_knode.c`

| Method                      | Class | C's test or the reason |
|---|---|---|
| testSanity1                 | P | `knode_sanity1`                             |
| testPrintKeysWithoutIkey    | N | `print`, debug text: C has none (`knode.h`) |
| testNodeTextsSameInEveryRun | P | `knode_node_texts_same_in_every_run`        |
| testSanity2                 | P | `knode_sanity2`                             |
| testEq                      | P | `knode_eq`                                  |
| testEqWithVersions          | P | `knode_eq_with_versions`                    |
| testEqWithVersionsAndDelete | P | `knode_eq_with_versions_and_delete`         |
| testEqBeforeFirstVersion    | P | `knode_eq_before_first_version`             |
| testLte1                    | P | `knode_lte1`                                |
| testLte2                    | P | `knode_lte2`                                |
| testLte3                    | P | `knode_lte3`                                |
| testLt1                     | P | `knode_lt1`                                 |
| testLt2                     | P | `knode_lt2`                                 |
| testLt3                     | P | `knode_lt3`                                 |
| testGt1                     | P | `knode_gt1`                                 |
| testGt2                     | P | `knode_gt2`                                 |
| testGte                     | P | `knode_gte`                                 |
| testFirst1                  | P | `knode_first1`                              |
| testCheckEmptyNode          | P | `knode_check_empty_node`                    |
| testCheck1                  | P | `knode_check1`                              |
| testCheck2                  | P | `knode_check2`                              |
| testGetPointers             | P | `knode_get_pointers`                        |
| testLastVersion1            | P | `knode_last_version1`                       |
| testLastVersion3            | P | `knode_last_version3`                       |
| testLastVersion4            | P | `knode_last_version4`                       |
| testFirstAndSecond2         | P | `knode_first_and_second2`                   |
| testFirstAndSecond3         | P | `knode_first_and_second3`                   |
| testFirstAndSecond4         | P | `knode_first_and_second4`                   |
| testFirstAndSecond5         | P | `knode_first_and_second5`                   |
| testFirstAndSecond6         | P | `knode_first_and_second6`                   |
| testDeleteBitmap1           | P | `knode_delete_bitmap1`                      |
| testPrint                   | N | `print`, debug text: C has none (`knode.h`) |
| testToPreviousState1        | P | `knode_to_previous_state1`                  |
| testToPreviousState2        | P | `knode_to_previous_state2`                  |
| testToPreviousState3        | P | `knode_to_previous_state3`                  |
| testToPreviousState4        | P | `knode_to_previous_state4`                  |
| testNewKeyNodeWithTime      | P | `knode_new_key_node_with_time`              |
| testGetFirstTime1           | P | `knode_get_first_time1`                     |
| testGetFirstTime2           | P | `knode_get_first_time2`                     |
| testGetFirstTime3           | P | `knode_get_first_time3`                     |
| testGetPointerCount0        | P | `knode_get_pointer_count0`                  |
| testGetPointerCount1        | P | `knode_get_pointer_count1`                  |
| testGetPointerCount2        | P | `knode_get_pointer_count2`                  |
| testGetPointerCount3        | P | `knode_get_pointer_count3`                  |
| testMaxValidTime0           | P | `knode_max_valid_time0`                     |
| testMaxValidTime1           | P | `knode_max_valid_time1`                     |
| testMaxValidTimeWithDelete  | P | `knode_max_valid_time_with_delete`          |
| testAddDeleteKlong          | P | `knode_add_delete_klong`                    |
| testPointerInPlace          | W | `knode_pointer_in_place` (section 3)        |

## 1.5 `DagTester`: `t_dag.c`

| Method                                 | Class | C's test or the reason |
|---|---|---|
| test0                                  | P | `dag_test0`                                     |
| test1                                  | P | `dag_test1`                                     |
| testPut0                               | P | `dag_put0`                                      |
| testPut1                               | P | `dag_put1`                                      |
| testDeleteMissingKey                   | P | `dag_delete_missing_key`                        |
| testTwoNewRootsInOneTransaction        | P | `dag_two_new_roots_in_one_transaction`          |
| testSplit0                             | P | `dag_split0`                                    |
| testTimeSplit1a                        | P | `dag_time_split1a`                              |
| testVisit0                             | P | `dag_visit0`, the counts by the test's own walk |
| testVisit1                             | P | `dag_visit1`, likewise                          |
| testWalksKeepTheirOrder                | N | the Dag's debug walks, left out of C (`dag.h`)  |
| testLongKeyWalks                       | P | `api_long_keys` (`f_api.c`), below              |
| testPointerCreationListener1           | P | `dag_pointer_creation_listener1`                |
| testPointerCreationListener2           | P | `dag_pointer_creation_listener2`                |
| testTransactionLeavesNoUnreachableNode | P | `dag_transaction_leaves_no_unreachable_node`    |

`testWalksKeepTheirOrder` checks that 021-16's loops visit
`visitMemoryNodes`, `visitMemoryPointersOnce` and `DagNodeIterator` in
the order of the recursions they replaced; C has none of the three (its
tests count with walks of their own). `testLongKeyWalks` puts and reads a
key of 400,000 bytes and walks its levels; C's walks of the nodes (the
recount, the close's walk) have no recursion, and `api_long_keys` (022-02,
the pin of 15:22) puts, syncs, checks, closes, opens and reads keys of
200,000 and 210,000 bytes through the API.

## 1.6 `TopNode` and `TopTester`: `t_tnode.c`

| Method                                       | Class | C's test |
|---|---|---|
| TopNode.testHeight1                          | P | `tnode_height1`                             |
| TopNode.testHeight2                          | P | `tnode_height2`, but the refusal (below)    |
| TopNode.testPointerInPlace                   | W | `tnode_pointer_in_place` (section 3)        |
| TopTester.test1                              | P | `tnode_top_tester1`                         |
| TopTester.testBeforeFirst                    | P | `tnode_before_first`                        |
| TopTester.testFindFirstNode                  | P | `tnode_find_first_node`                     |
| TopTester.testDS3                            | P | `tnode_ds3`                                 |
| TopTester.testDS4                            | P | `tnode_ds4`                                 |
| TopTester.testNewSuperRootFromStreamPointers | P | `tnode_new_super_root_from_stream_pointers` |

`TopNode.height` above 2^48 - 1 throws `IllegalStateException` in Java and
is an assert in C (`tn_height`); no input reaches it: a stored ordinal has
6 bytes, and the database refuses a user transaction once the super
root's ordinal reaches a margin of 1,024 below the bound (005-02;
`Db.LAST_TOP_ORDINAL`, C's `DB_LAST_TOP_ORDINAL`, `t_db.c`'s
`db_top_ordinals`).

## 1.7 The others

| Method              | Class | C's test or the reason |
|---|---|---|
| AccessData.test1    | N | C keeps `AccessData`'s two constants only (`node.h`) |
| Pointer.test1       | P | `knode_pointer_test1` (`t_knode.c`)                  |
| ValueNode.testDummy | P | `nwrite_value_node_dummy` (`t_nwrite.c`)             |


# 2. `bergdb.common`

## 2.1 What C has: `t_bytes.c`, `t_strmap.c`, `t_strutil.c`, `t_transseq.c`

| Method                          | Class | C's test |
|---|---|---|
| Bytes.testFloatLE               | P | `bytes_float_le`                                     |
| Bytes.testDoubleLE              | P | `bytes_double_le`                                    |
| Bytes.testShortLE               | P | `bytes_short_le`                                     |
| Bytes.testLongsToBytesLE        | P | `bytes_longs_to_le`                                  |
| Bytes.testLongsToBytesLE2       | P | `bytes_longs_to_le2`                                 |
| Bytes.testLongToBytesBE         | P | `bytes_long_vs_bytebuffer`                           |
| Bytes.testLongToBytesLE         | P | `bytes_long_vs_bytebuffer`                           |
| Bytes.testLongBE                | P | `bytes_long_be`                                      |
| Bytes.testLongBE2               | P | `bytes_long_round_trip`                              |
| Bytes.testLongLE                | P | `bytes_long_round_trip`                              |
| Bytes.testLongLE2               | P | `bytes_long_round_trip`                              |
| Bytes.testIntLE                 | P | `bytes_int_round_trip`                               |
| Bytes.testIntBE                 | P | `bytes_int_round_trip`                               |
| Bytes.testUShortLE              | P | `bytes_ushort_le`                                    |
| Bytes.testUShortLE2             | P | `bytes_ushort_le`                                    |
| Bytes.testUnsigned              | P | `bytes_unsigned`                                     |
| MyChecksum.test0                | P | `transseq_checksum`: CRC-32 of longs, zlib's         |
| StringMap.test1                 | P | `strmap_test1`                                       |
| StringMap.test2                 | P | `strmap_test2`, with HashMap's order                 |
| StringMap.testLong              | P | `strmap_long`, with Long.parseLong's edges           |
| StringUtil.testIsWellFormedUtf8 | P | `strutil_is_well_formed_utf8`; vectors `strutil.txt` |

Java's exact outputs of `Bytes`, `StringMap` and `isWellFormedUtf8` are
in the vectors too (`t_vectors.c`). `MyChecksum.updateWithBoolean` has no
counterpart: `TransSeq.checksum` takes longs and a node's type byte only.

## 2.2 Not for C

| Method                             | Class | The reason |
|---|---|---|
| AssertStatus.test0                 | N | the JVM's `-ea`; C's asserts are on in both builds |
| Bug.dummyToIncreaseCoverage        | N | Java's coverage                                    |
| ByteArrayComparator.test0          | N | a `Comparator<byte[]>`, for Klong's test only (a)  |
| ByteArrayComparator.test1          | N | as test0                                           |
| ByteArrayComparator.test2          | N | as test0                                           |
| ByteArrayComparator.testLengthDiff | N | as test0                                           |
| ByteArrayComparator.testEmptyFirst | N | as test0                                           |
| Create.testSet                     | N | Java's collections                                 |
| Create.testList                    | N | Java's collections                                 |
| EventToWaitFor.test1               | N | threads; the Pub layer's testers                   |
| EventToWaitFor.test2               | N | threads                                            |
| HashUtil.testMHashIndex1           | N | no caller in Java's Core                           |
| MyLongSet.test1                    | N | the Pub layer's (`RwEnvironmentImp`); (b)          |
| MyLongSet.test2                    | N | as test1                                           |
| MyLongSet.testClearingLargeSet     | N | as test1                                           |
| MyLongSet.testSize0                | N | as test1                                           |
| MyLongSet.testSize1                | N | as test1                                           |
| MyLongSet.testSize2                | N | as test1                                           |
| MyLongSet.testSize3                | N | as test1                                           |
| MyLongSet.test3                    | N | as test1                                           |
| MyLongSet.testIterator1            | N | as test1                                           |
| MyLongSet.testIterator2            | N | as test1                                           |
| NullOutputStream.testCount         | N | Java's streams, for nanotest                       |
| Pair.test0                         | N | Java's generics                                    |
| Salsa.testBasic                    | N | encryption, left out of C                          |
| Salsa.testStream7                  | N | as testBasic                                       |
| Salsa.testRandomAccess             | N | as testBasic                                       |
| Salsa.testInPlace                  | N | as testBasic                                       |
| Salsa.testNot64                    | N | as testBasic                                       |
| Salsa.testNot64b                   | N | as testBasic                                       |
| Salsa.testFirst3                   | N | as testBasic                                       |
| Salsa.testAppend1                  | N | as testBasic                                       |
| Salsa.testAppendOneByteAtATime     | N | as testBasic                                       |
| SeedGenerator.testSanity           | N | Java's seed of a random id; C's are `plat`'s bytes |
| StringUtil.testOneDecimal          | N | Java's text of a double                            |
| StringUtil.testTwoDecimals         | N | as testOneDecimal                                  |
| StringUtil.testSpaceFill           | N | Java's Strings                                     |
| StringUtil.testWholeNumber         | N | as testOneDecimal                                  |
| StringUtil.testUtf8Size            | N | UTF-16 Strings; C's keys and values are bytes      |
| StringUtil.testToBytesOfAKnownSize | N | as testUtf8Size; the Pub layer's (020-08)          |
| StringUtil.testIsPrintableAscii    | N | for `print` and display texts, which C has not     |
| StringUtil.testHasLoneSurrogate    | N | UTF-16; C's counterpart is `isWellFormedUtf8` (c)  |
| StringUtil.testToString            | N | Java's Strings                                     |
| StringUtil.testHex                 | N | Java's helper (d)                                  |
| Util.testDelete                    | N | Java's files; C's deletes are `plat`'s             |
| Util.testBytesToFileToBytes        | N | Java's files                                       |
| Util.testAreEqual1                 | N | arrays; C compares with `memcmp`                   |
| Util.testAreEqual2                 | N | as testAreEqual1                                   |
| Util.testToArray0                  | N | Java's `List<Long>`                                |
| Util.testToArray1                  | N | as testToArray0                                    |
| Util.testToArray2                  | N | as testToArray0                                    |
| Util.testIsPrefix0                 | N | byte arrays; no caller in Java's Core              |
| Util.testIsPrefix1                 | N | as testIsPrefix0                                   |
| Util.testIsPrefix2                 | N | as testIsPrefix0                                   |
| Util.testIsSuffix0                 | N | as testIsPrefix0                                   |
| Util.testIsSuffix1                 | N | as testIsPrefix0                                   |
| Util.testContains0                 | N | as testIsPrefix0                                   |
| Util.testContains1                 | N | as testIsPrefix0                                   |

(a) `ByteArrayComparator` (unsigned bytes, then the length) serves only
`Klong.testSortOrder1`; `t_klong.c` has its own copy for that test.

(b) C's Core has no set of longs; its maps of longs are `lmap`'s, tested
by its users (`t_ncoll.c`, `t_sdb.c`).

(c) Java refuses a key String with a lone surrogate (021-05); C's ikeys
are bytes, refused when not well-formed UTF-8 (`keys_lone_surrogate`).

(d) `toHex` writes two lowercase digits per byte; C writes the same in
the messages that use it (`NodeStream`'s "node header bytes",
`nstream.c`; the meta block's, `rstream.c`), which `corruptset.sh` and
`corrupt.sh` compare with Java's, byte for byte.


# 3. The tests written now

Both port Java's tests of 015-14 (the in-place pointer changes for a
reader beside the writer). C has one caller, so what they check is the
results, which C's single-threaded ports must give as well: a raised
reference is never lowered (`Spos.newer`), a swizzle changes a pointer
only when it holds what the caller read, the pointee is counted, and a
growth of a key node's arrays keeps pointer 0. No C test called
`kn_raise_ref`, `kn_set_pointer`, `tn_raise_ref`, `tn_swizzle` or
`tn_set_ref` before; the follows (`ncoll.c`), eviction (`evict.c`) and
the start (`starter.c`) call them, through `node.c`, and the tests of
those and the cross tests run them, but none checked them one by one.

* `t_knode.c`'s `knode_pointer_in_place` (`KeyNodeTester.testPointerInPlace`):
  a key node's pointer 0, a handle `a` swizzled to a handle `b` that holds
  a key node at 300; 29 klongs more grow the arrays (a capacity of 30 or
  more), and pointer 0 keeps `b` and 300; `searchEq` finds it (index 0,
  `b`'s object, 300); `setPointer(0, null, 400)`; then `b` without an
  object as the pointee, and no node for it. The fixture's end checks that
  the counts agree and nothing is left (`nfix.h`).
* `t_tnode.c`'s `tnode_pointer_in_place` (`TopNode.testPointerInPlace`):
  the root pointer and skip pointer 0 of a top node with ordinal 1, each
  set to `a` at 200, raised to 300 and not lowered to 100, swizzled to
  `b`, its reference set to 400.

Both pass in the test build (sanitizers, the allocator's checks) and the
release build, before any change of C's sources: 2 tests, 69 checks, in
under a millisecond. They found nothing to fix. The negative control:
with `kn_raise_ref` and `tn_raise_ref` made to lower a reference too (the
test of `spos_newer` taken out, in a build of its own), both fail ("100
!= 200"), and they are the only ones: the other 410 unit tests and the 31
functional tests pass.


# 4. Findings

* **C's faults**: none in these classes.
* **Java's faults**: none.
* **Departures**: none new. Two known differences of form, not of
  result: `TopNode.height` above the maximum is an assert in C where Java
  throws (section 1.6, unreachable), and the conversions of keys refuse
  without Java's texts (section 1.2).
* **Left (L)**: none. Nothing of these packages is worth porting that C
  has not: the 65 N are Java's helpers, debug texts and walks, threads,
  files and the encryption.
