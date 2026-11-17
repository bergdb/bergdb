# 022-05 stream and storage: Java's tests of `bergdb.stream` and `bergdb.storage` in C

Created 2026-11-09 by Frans Lundberg. Status: done.

Worker t16's part of 022-05: every test method of the classes in
`java/src/bergdb/stream/` and `java/src/bergdb/storage/` at `main`'s
`e875a34` (2026-11-09 17:18), classed as the brief says: **P** ported (C's
test named, or the harness), **W** written now, **N** not for C (the
reason), **L** left. A test method is what nanotest runs: a static method
with `@Nano` (`@Nano("f")` and `@Nano("night")` too); these classes have
no unannotated `testX()`.

| Package | Methods | P  | W  | N  | L |
|---|---|---|---|---|---|
| stream  | 75  | 27 | 10 | 36 | 2 |
| storage | 90  | 32 | 25 | 32 | 1 |
| in all  | 165 | 59 | 35 | 68 | 3 |

C's stream is internal and has one caller, the database (`c/readme.md`,
sections 2 and 8): `stream.c` is Java's `MemoryStream`, `FileStream` and
`BufferedStream` in one (the write buffer, written at a sync, a close or
when full, by the caller's thread), `meta.c` is `MetaBlock`, and
`rstream.c` and `recover.c` are `RecoverableStream`. So the tests of
Java's threads (the buffer's thread, the cut's thread, readers beside the
writer, interrupts), of the stream's Java API (ranges of arrays,
`seekFirstPos`, `setMax2G`, `StrictStream`, the class loaders' locks) and
of the encryption (`SalsaStream`) are not for C; their properties often
are, and are ported as C's stream and recovery tests: lengths, reads past
the end and below a cut, cuts, the forces, failures of writes, forces,
opens and deletes, the lock file, a torn tail and recovery.

Written now: 21 tests of Java's (section 3), in `t_stream.c` (11),
`t_recover.c` (4), `t_rstream.c` (4) and `t_append.c` (2), and one of
C's own. They found two faults of C, both fixed. A stream that an I/O
failure had failed still took a sync and a close when its buffer was
empty, so that through `bergdb.h` a sync after a failed sync gave
`BERGDB_OK` (the force tried again) and the close `BERGDB_OK`, where
`c/readme.md` (section 9, point 8) and Java give the failure (section
4.1). And a database in memory never freed its stream's bytes, also after
reclaim's cuts, where Java's drops them (section 4.2).


# 1. `bergdb.stream`

## 1.1 `FileStream`: `t_append.c`, `t_stream.c`

| Method | Class | C's test |
|---|---|---|
| test0                                     | P | `append_dir_test0`                        |
| test1                                     | P | `append_dir_test0`                        |
| testNoFileUntilFirstAppend                | P | `append_dir_first_file` (015-06)          |
| testUnlistableDirectory                   | P | `append_dir_unlistable` (a)               |
| testFileSizeRules0                        | P | `append_dir_size_rules`                   |
| testFileSizeRules1                        | P | `append_dir_size_rules` (a)               |
| testRestart0                              | P | `append_dir_test0`                        |
| testRestartMissingFile                    | P | `append_dir_refusals`                     |
| testBigAppend0                            | P | `append_dir_sizes`                        |
| testConstants                             | L | `FILE_SIZES` is static (section 5)        |
| testReopenPast214TB                       | W | `stream_reopen_past_214tb`                |
| testPretruncate0                          | P | `stream_forces`, `stream_seam`            |
| testReadBelowFirstPosDoesNotBreakStream   | W | `stream_read_below_first_pos`             |
| testReadPastEnd                           | W | `stream_read_past_end`                    |
| testMultiFileRead0                        | P | `stream_dir`, `stream_contract`           |
| testMultiFileRead1                        | P | `stream_dir`, `stream_contract`           |
| tFileSizeIncrease                         | P | `append_dir_sizes`                        |
| testFailedOpenClosesFileAndUnlocks        | W | `stream_failed_open`                      |
| testForcingOffWritesAppends               | P | `stream_new_file_forces`                  |
| testForcingOffForcesTheFileBeforeANewFile | P | `stream_forces`                           |
| testForcingOffForcesBeforeACutDeletes     | P | `stream_forces`, `stream_new_file_forces` |
| testForcingOffForcesAtClose               | W | `stream_forces_at_close` (a)              |
| testFailedDeleteOfACut                    | W | `stream_failure_refuses_writes`           |
| testLockFile                              | W | `stream_lock_file`                        |
| testLockAcrossProcesses                   | P | `f_durable.c`'s `durable_in_use`          |

(a) C has no `hasStreamBytes`, no `setMax2G` (015-33) and no second
close: those parts are N.

| Method | Class | The reason |
|---|---|---|
| testSeekFirstPos0                                | N | `seekFirstPos`, Java's API (019-04) |
| testSeekFirstPos1                                | N | as testSeekFirstPos0                |
| testCutThreadThatCannotStart                     | N | the cut's thread (019-39)           |
| testCutErrorRecordedAsMadeBefore                 | N | the cut's thread (019-39)           |
| testReadOfFileDeletedMeanwhileDoesNotBreakStream | N | a read beside the cut's thread      |
| testForcingOnForcesEveryAppend                   | N | per-append forcing (b)              |
| testReadOfLastFileDuringForce                    | N | a read beside a force (005-46)      |
| testReadDuringNewFile                            | N | a read beside a new file (005-46)   |
| testCutOnItsOwnThread                            | N | the cut's thread (005-46)           |
| testReadsAndInterrupts                           | N | Java's interrupts                   |
| testReadOfClosedFileFailsAlone                   | N | a read beside the close (015-17)    |
| testCutAndOpenByInterruptedThread                | N | Java's interrupts                   |
| testReadersBesideWriterAndCuts                   | N | readers beside the writer           |
| testSecondStreamRefused                          | N | one open per process (b)            |
| testOtherCopyRefusedFirst                        | N | two copies of the class             |
| testLockAcrossClassLoaders                       | N | two class loaders                   |

(b) C has no per-append forcing (`c/readme.md`, section 11, point 3); a
directory is opened once per process, by C's caller (section 9, point 10).

## 1.2 `MemoryStream`: `t_stream.c`

C's memory stream is the stream of a database in memory and of the tests:
one buffer from position 0, whose cut is `CutStream`'s, exact
(`stream_pretruncate`), and, for the tests, `MemoryStream`'s pretruncate
to a multiple of 1,000,000 (`stream_pretruncate_memory`).

| Method                    | Class | C's test or the reason |
|---|---|---|
| testSize1                 | P | `stream_contract` (length 0)                               |
| testCutPast2GB            | L | a cut past 2^31 bytes; with section 4.2's fix (section 5)  |
| testCopyAtArrayBoundaries | N | C's memory stream has no arrays and no `copy()`            |
| testRefusedArguments      | N | an append's ranges, Java's API; its cut: `stream_contract` |
| testOneByte               | P | `stream_contract` (appends and reads)                      |
| testSize2                 | P | `stream_memory` (2.5 MB)                                   |
| testArrays                | P | `stream_memory`                                            |
| testTruncate1             | P | `stream_memory`                                            |
| testTruncate2             | P | `stream_memory`                                            |
| testPretruncate1          | P | `stream_memory` (to 1,000,000; an earlier cut kept)        |
| testPretruncate2          | P | `stream_memory`                                            |

## 1.3 `StreamContractTester`: `t_stream.c`

| Method                  | Class | C's test or the reason |
|---|---|---|
| testFileStream          | W | `stream_contract`, the three directories                 |
| testFileStreamSizeLimit | N | `setMax2G` (015-33), the stream's Java API               |
| testMemoryStream        | W | `stream_contract`, the memory streams                    |
| testOneFileStream       | N | C has no `OneFileStream`                                 |
| testCutStream           | W | `stream_contract`: C's memory stream cuts as `CutStream` |
| testSalsaStream         | N | the encryption (020-28: 2026.4 has none)                 |
| testStrictCaller        | N | `StrictStream`, Java's checker of callers and threads    |
| testStrictWrapped       | N | as testStrictCaller                                      |

## 1.4 `ReadOnlyStream`, `DummyStream`, `SalsaStream`

C's counterpart of `ReadOnlyStream` is a directory opened read-only
(`stream_open_dir`), as a start and `bergdb-dump` open it.

| Method                        | Class | C's test or the reason |
|---|---|---|
| ReadOnlyStream.testRead             | P | `stream_dir`                                           |
| ReadOnlyStream.testAppend           | P | `append_dir_buffer` (ERR_ARG)                          |
| DummyStream.test1                   | N | C has no `DummyStream` (a test stream of 10,000 bytes) |
| DummyStream.testRead1               | N | as test1                                               |
| DummyStream.testRead2               | N | as test1                                               |
| DummyStream.testSize                | N | as test1                                               |
| SalsaStream.test0                   | N | the encryption                                         |
| SalsaStream.test1                   | N | the encryption                                         |
| SalsaStream.testMultiAppend         | N | the encryption                                         |
| SalsaStream.testReadPartOfBlock1    | N | the encryption                                         |
| SalsaStream.testNon64a              | N | the encryption                                         |
| SalsaStream.testNon64b              | N | the encryption                                         |
| SalsaStream.testLengthCountsAppends | N | the encryption                                         |
| SalsaStream.testOneForcePerAppend   | N | the encryption                                         |
| SalsaStream.testNon64c              | N | the encryption                                         |


# 2. `bergdb.storage`

## 2.1 `RecoverableStream`: `t_rstream.c`, `t_recover.c`, `t_append.c`

| Method                                 | Class | C's test |
|---|---|---|
| testGetRemainingTransBytes1           | P | `rs_positions`                                      |
| testGetRemainingTransBytes3           | P | `rs_positions`                                      |
| testGetRemainingTransBytes4           | P | `rs_positions`                                      |
| testThatConstantsMatch                | P | `rs_positions`                                      |
| testGetTransPos                       | P | `rs_positions`                                      |
| test1                                 | P | `append_rs_test1`, `rs_recovery_java_cases`         |
| testAppendOffset                      | W | `append_rs_offset`                                  |
| testGetPos1                           | P | `rs_get_spos`                                       |
| testGetPos2                           | P | `rs_get_spos`                                       |
| testGetStartSpos                      | P | `rs_get_start_spos`                                 |
| crashInFirstTransaction               | P | `recover_crash_in_first_transaction`                |
| crashInTransactionSize                | P | `recover_crash_in_transaction_size`                 |
| crashInThirdTransaction               | P | `recover_crash_in_third_transaction`                |
| largeTransaction                      | P | `recover_large_transaction`                         |
| crashInLargeTransaction               | P | `recover_crash_in_large_transaction`                |
| crashInMetaBlockHeader                | P | `recover_crash_in_meta_block_header`                |
| crashAtMetaBlockPosition              | P | `recover_crash_at_meta_block_position`              |
| testRecoverWithWrongKeyWritesNothing  | W | `recover_unreadable_meta_blocks_write_nothing` (a)  |
| testRecoverOtherVersionWritesNothing  | W | `recover_unreadable_meta_blocks_write_nothing`      |
| testIsIncompleteCreation              | W | `rs_incomplete_creation_java` (b)                   |
| crashInTransHeader1                   | W | `recover_crash_in_trans_header`                     |
| crashInTransHeader2                   | W | `recover_crash_in_trans_header`                     |
| testTransHeaderFixBytes1              | W | `rs_trans_header_fix_bytes`                         |
| testTransHeaderFixBytes2              | W | `rs_trans_header_fix_bytes`                         |
| testTransHeaderFixBytesBelowMin       | W | `rs_trans_header_fix_bytes`                         |
| testTransHeaderFixBytes3              | W | `rs_trans_header_fix_bytes`                         |
| testTransHeaderFixBytes4              | W | `rs_trans_header_fix_bytes`                         |
| recoverFromMiddleOfStream             | W | `recover_from_middle_of_stream`                     |
| testIterator                          | W | `recover_iterator`                                  |
| testPosOfTransCompletedBefore         | W | `rs_pos_of_trans_completed_before_java` (c)         |
| testPosOfTransCompletedBeforeAfterCut | W | `rs_pos_of_trans_completed_before_after_cut` (c)    |
| testConstantInFileStream              | W | `append_constants`                                  |
| testConstantMetaBlockDistance         | W | `append_constants`                                  |
| testConstantLastByte                  | W | `append_constants`                                  |
| testReadMetaBlock1                    | P | `rs_meta_blocks`                                    |
| testReadMetaBlock2                    | P | `rs_meta_blocks` (versions 155, 65,690, 16,777,370) |
| testReadMetaBlock3                    | P | `rs_meta_blocks`                                    |

(a) C has no encryption: the meta blocks that a wrong key reads are made
here by changing their magic bytes; the keys themselves are N. (b) With
`rs_incomplete_creation`, which made the cuts of a creation, a failed one, another magic, a
longer stream and the version's bytes 6 and 7; the new one makes Java's
other cases (zeros, version 155 cut at 10 and 4, an invalid first block, a
block that names a record, a large first record cut at 300 and 200, a short
first record with bytes after it). (c) The older `rs_pos_of_trans_completed_before`
checked a few positions of 40 records; the new ones are Java's, every 997th
position of 1,300 records, and the cut stream's positions before the first.

## 2.2 `MetaBlock`: `t_rstream.c`

| Method          | Class | C's test |
|---|---|---|
| time            | P | `meta_fields` |
| version         | P | `meta_fields` |
| startupDistance | P | `meta_fields` |
| maxNodeSize     | P | `meta_fields` |

## 2.3 `BufferedStream`: `t_stream.c`, `t_append.c`

C's write buffer is `BufferedStream` without its thread: written when
full, at a sync and at a close, in the caller's call.

| Method                                     | Class | C's test or the reason |
|---|---|---|
| testUptimeIsTheJvms                           | N | the JVM's clock                              |
| testQuarterWakesConsumer                      | N | the buffer's thread (005-76)                 |
| testCloseDuringAFlushDoesNotWaitForTheTimer   | N | the buffer's thread and timer                |
| testAppendWaitingForRoomWhenCloseBeginsThrows | N | an append beside the close                   |
| testQuarterBacklogDoesNotWait                 | N | the buffer's thread (005-76)                 |
| testQuarterAvoidsRoomWaits                    | N | the buffer's thread (005-76)                 |
| test1                                         | N | the timer's flush                            |
| testReadFromBufferOfNonEmptyStream            | W | `stream_read_from_buffer_nonempty`           |
| testReadOneBytePastEnd                        | P | `stream_storage`                             |
| testReadPastEndNearMaxValue                   | P | `stream_read_past_end_near_max_value`        |
| testPretruncateBeyondFlushed                  | N | a cut held for the thread (d)                |
| testPendingCutDuringACut                      | N | the thread's pending cut (015-82)            |
| testWriterCutBesideThreadsCutAndClose         | N | the writer beside the thread (015-80)        |
| testFirstPosAfterCuts                         | P | `stream_contract`, `stream_forces` (d)       |
| testIdleConsumerWaitsForAppend                | N | the buffer's thread                          |
| testStopAndCloseEndIdleConsumer               | N | the buffer's thread                          |
| testWaitCountStaysSmall                       | N | the buffer's thread                          |
| testNoFlushOfNothingWhenClosing               | P | `append_dir_first_file`                      |
| testClose                                     | P | `append_dir_test0`                           |
| testWriteAfterClose1                          | N | a handle ends at its close (012-13, Q2)      |
| testWriteAfterClose2                          | N | as testWriteAfterClose1                      |
| testReadAfterClose1                           | N | as testWriteAfterClose1                      |
| testReadAfterClose2                           | N | as testWriteAfterClose1                      |
| testWriteMuch                                 | P | `append_dir_buffer`: 1,000 bytes, buffer 100 |
| testWriteLittle                               | P | `stream_workload`: 1 to 3,000 bytes          |
| testWriteZero                                 | P | `append_dir_first_file`, `stream_contract`   |
| testCloseAfterFailedFlush                     | W | `stream_failure_refuses_writes`              |
| testCloseFailureKeptOnFlushFailure            | N | Java's suppressed exceptions                 |
| testCloseThrowsFlushFailureAgain              | N | Java's self-suppression (019-37)             |
| testAppendWaitIgnoresInterrupt                | N | Java's interrupts                            |
| testCloseIgnoresInterrupt                     | N | Java's interrupts                            |
| testConsumerIgnoresInterrupt                  | N | Java's interrupts                            |
| testStopWhileInterruptedClosesStream          | N | `stop()` and the thread                      |
| testFlushFailureMadeBefore                    | N | the thread, an `Error` kept unallocated      |
| testListenerErrorFailsTheStream               | N | the append listener                          |

(d) C cuts only the bytes in its files (`stream_pretruncate`: ERR_ARG past
them), and its callers force before a cut (reclaim's `cut_if_durable`, a
start's cut after its open), where Java's `BufferedStream` keeps a cut
beyond the flushed bytes for its thread. `stream_contract` cuts as the
database does, after a sync, and checks the first position after each
cut.

## 2.4 `StorageContractTester` and `StorageManagerTester`: `t_stream.c`

C's `stream_as_storage` is `StorageManager`'s reads (022-02, D6); its sync
is the write buffer's, written and forced in the call.

| StorageContractTester's | Class | C's test or the reason |
|---|---|---|
| testBufferedStream          | W | `stream_contract`                     |
| testStorageManager          | W | `stream_contract`, as storage         |
| testOneWriterBufferedStream | N | one writer beside the thread (015-80) |
| testOneWriterStorageManager | N | as testOneWriterBufferedStream        |
| testWorkloadBufferedStream  | W | `stream_workload`, seed 1             |
| testWorkloadStorageManager  | W | `stream_workload`, seed 2             |
| testWorkloadsLong           | L | 20 seeds, longer (section 5)          |

| StorageManagerTester's | Class | C's test or the reason |
|---|---|---|
| testReadBelowFirstPosIsNotAStreamError | W | `stream_read_below_first_pos`                   |
| testMultipleClose                      | N | a handle ends at its close                      |
| testWait1                              | N | the time of a sync, the storage thread          |
| testWait2                              | N | a sync beside an append (group commit)          |
| testSyncStartsTheFlush                 | P | `append_dir_buffer`: the sync writes and forces |
| testSyncWokenByAFailure                | N | a sync waiting for the thread (e)               |
| testReadFailureRecordedFirst           | N | an `OutOfMemoryError` at the message (e)        |

(e) A sync after a failure gives it: `stream_failure_refuses_writes`.
C's error is a fixed buffer, filled with nothing allocated.


# 3. The tests written now

Each passes in both builds, in well under a second in the test build
under F53's load (each measured; `stream_contract` 0.2 to 0.4 s, the
others 0.05 to 0.5 s). Where forces are not the subject (the contract,
the workload, the reads past the end and below a cut), the test build
runs them with writes and no forces, as Java's `StreamContract.NoForceIo`,
through the I/O seam (`NOFORCE`); the release build, which has no seam,
runs the contract on the memory streams and the workload with one seed.

* `t_stream.c`, the seam `INJ` (one call of a kind fails: an open of a
  stream file, a write, a force for a reason, the directory's force, a
  delete; 022-01's `plat_io_set`):
  * `stream_failed_open` (`testFailedOpenClosesFileAndUnlocks`): an open for
    writing whose open of its last file, OPEN force or directory force
    fails gives the failure and leaves no descriptor open (the lock with
    the file; each descriptor counted), no memory; the next open reads the
    byte.
  * `stream_failure_refuses_writes` (`testFailedDeleteOfACut`,
    `testCloseAfterFailedFlush`): a failed write, force at a sync, switch
    force, or a cut's second delete; then no sync, flush, append or cut is
    taken, the durable length stays, the close gives the failure and
    frees everything; the switch force's failure makes no new file; the
    cut's second delete failing leaves the first file deleted and the
    others; and what a start then opens. Failed before the fix (4.1).
  * `stream_failed_force_fails_the_database`: the same through `bergdb.h`:
    after a failed sync, the next sync `BERGDB_FAILED`, a transaction
    `BERGDB_FAILED`, the close `BERGDB_IO`. Failed before the fix.
  * `stream_read_below_first_pos`, `stream_read_past_end`,
    `stream_read_from_buffer_nonempty`: on directories (bytes in
    the files, in the buffer, after a sync; as storage) and the memory
    stream: refused alone, the stream goes on.
  * `stream_contract`: `StreamContract`'s checks (empty, length 0, appends
    and reads, reads past the end also where position + length overflows,
    a read below a cut, cuts within and at the length, a cut beyond it
    refused, the close) on five streams: the memory stream alone and as
    storage, a directory with a buffer of 10,000 bytes alone and as
    storage, and with the default buffer. Not the checks of negative or
    long ranges (Java's API).
  * `stream_workload`: `StorageContractTester.workload` with one caller:
    400 appends of 1 to 3,000 bytes, 16 cuts after syncs, two reads
    after each append compared with what was appended; the directory then
    opened again with its bytes from the last cut.
  * `stream_lock_file`, `stream_reopen_past_214tb` (the file made by hand
    at index 2^31, as C has no `seekFirstPos`; then the next file's name),
    `stream_forces_at_close` (the close's SYNC force; the bytes read after).
* `t_recover.c`: `recover_unreadable_meta_blocks_write_nothing` (blocks
  of version 155, and blocks with other magic bytes, as a wrong key reads
  them, cut 0, 3, 5 and 50 bytes into the block at 200,000: refused with
  the version named, nothing written; the stream as written recovers to its
  199 records), `recover_crash_in_trans_header` (the sizes 257 and 65,538
  that `transHeaderFixBytes` completes), `recover_from_middle_of_stream`,
  `recover_iterator`.
* `t_rstream.c`: `rs_incomplete_creation_java`, `rs_trans_header_fix_bytes`
  (Java's five cases, through the plan), `rs_pos_of_trans_completed_before_java`,
  `rs_pos_of_trans_completed_before_after_cut`.
* `t_append.c`: `append_rs_offset` (C's record is a pointer to its first
  byte: the slice's own size field is checked, 005-75), `append_constants`.
* C's own, for section 4.2: `t_stream.c`'s
  `stream_memory_database_frees_cut_bytes`.


# 4. Findings

## 4.1 C's fault, fixed: a failed stream took a sync and a close

`stream_flush` returned `ERR_OK` for an empty buffer before it checked
the stream's failure. So after an I/O failure that left the buffer empty,
a failed force at a sync or a failed delete of a cut, `stream_sync` forced
the files again (or nothing) and gave `ERR_OK`, with the durable length
set to the stream's, and `stream_finish` gave `ERR_OK`. Through
`bergdb.h`: after a sync whose force failed (`BERGDB_FAILED`, the database
failed), the next `bergdb_sync` forced the file again and gave
`BERGDB_OK`, and `bergdb_close` gave `BERGDB_OK`; after a cut whose delete
failed, the close gave `BERGDB_OK`. `c/readme.md`, section 9, point 8
says that every later sync gives `BERGDB_FAILED` and the close `BERGDB_IO`,
"as the stream takes no write after an error (Java's
`FileStream.checkIOException`)"; Java's `FileStream` throws its failure at
every later call and at `close()`, and forces nothing at the close of a
failed stream. A force tried again after a failed `F_FULLFSYNC` can
succeed though the bytes it failed to make durable are lost (the known way
a failed fsync goes), so the second sync's `BERGDB_OK` claimed durable what
may not be. A failed write was refused already: it left its bytes in the
buffer, and a flush of a non-empty buffer checked the failure.

The fix: `stream_flush` checks the failure first, also with nothing
buffered (`stream.c`, 4 lines and a comment; `stream.h` says so). The
tests: `stream_failure_refuses_writes` (before the fix, after the sync's
failed force: the second sync `ERR_OK`, the durable length 300, the flush
and the close `ERR_OK`; after the cut's failed delete: the sync, the flush
and the close `ERR_OK`) and `stream_failed_force_fails_the_database` (the
second `bergdb_sync` 0, `BERGDB_OK`, and `bergdb_close` 0, where 3 and 4
are expected); both pass with it. No other test changed, and the gate
passes with it (`allocfail`'s runs among them: a NOMEM in a new file fails
the stream with bytes still in its buffer, which a flush refused before as
now).

## 4.2 C's fault, fixed: a database in memory kept every byte of its stream

C's memory stream was one buffer from position 0, and its cut
(`stream_pretruncate`, `CutStream`'s exact cut) moved the first position
and freed nothing. Java's database in memory (`DbBuilder`'s default: a
`MemoryStream` under a `StorageManager`) drops each 1,000,000-byte array
below a cut. So a C database in memory with reclaim grew by every byte
it wrote, whatever the retain duration. A probe through `bergdb.h` (a
database in memory, the retain duration one second, 4,000 transactions of
10 kB, 0.1 s apart, on 50 keys): at 4,000, the stream 50.4 MB, its first
available position 49.3 MB (reclaim cuts), and the stream's buffer 67.2 MB
(`BERGDB_MEM_BUFFER`; the doubled allocation of 50 MB), where Java holds
about 2 MB of arrays. Not in `c/readme.md`, section 11, nor in 012-11
(which made the memory stream's cut `CutStream`'s, "the tests' stream").

The fix, in the second landing: the memory stream keeps the bytes from a
base, 0 until a cut, and a cut (`stream_pretruncate`) moves the base to
its 1,000,000-byte boundary, as `MemoryStream` drops its arrays, with a
`memmove` of the bytes kept; the room is the next appends', and the
allocation keeps its size, so a cut allocates nothing (no new NOMEM
path); reads and appends count from the base; the first position stays
the cut, exactly, as before. `stream_truncate_memory` refuses a length
below the base (`CutStream.truncate`'s rule). `stream_pretruncate_memory`,
the tests' `MemoryStream.pretruncate`, keeps its bytes, for the tests that
write into a cut stream. The test, `t_stream.c`'s
`stream_memory_database_frees_cut_bytes` (through `bergdb.h`: 1,200
transactions of 8,000 bytes, 0.1 s apart, the retain duration one second;
then each key's last value read again after an eviction to a budget of
100,000 bytes, from the bytes the cuts kept): the stream 12.3 MB, its first
available position 11.1 MB; the stream's buffer 4.2 MB with the fix (the
allocation's size at the first cut), 16.8 MB without it, which the test
refuses (more than 5 MB).

## 4.3 Notes

* **Java's faults**: none.
* **Departures, used by the tests, none new**: one caller and no thread;
  no per-append forcing (section 11, point 3); a cut only of the bytes in
  the files, after a sync (2.3, (d)); a handle ends at its close; one
  open of a directory per process, the caller's (section 9, point 10).
* **A difference of the stream alone, not of the database**: C's
  `stream_read` reads after the stream has failed, where Java's
  `FileStream.read` throws the failure; a failed database refuses every
  read (`db_check_active`), so a user of C sees Java's.
* `rstream.h`'s comment of `rs_append` said that Java reads a record's size
  at offset 0 whatever the record's offset; Java reads it at the record's
  offset since 005-75 (`testAppendOffset`). C's record is a pointer to its
  first byte, so C checked the right bytes; the comment now says so.


# 5. Left (L)

* `MemoryStream.testCutPast2GB`: a cut past 2^31 bytes of a memory stream,
  now that the cut frees (section 4.2): 2.2 GB of appends, a functional or
  stress test, not a unit test. The most valuable of what is left, and
  small: positions are `int64_t` throughout, and the base too.
* The memory stream's allocation could shrink at a cut, when it is much
  larger than the bytes kept (now it keeps the size it had at the first
  cut); a `mem_realloc` whose failure keeps the larger block.
* `StorageContractTester.testWorkloadsLong`: `stream_workload` with 20
  seeds and more operations, as a step of a stress script (seconds).
* `FileStream.testConstants`: `FILE_SIZES` (2 GB at index 6, the factors 5,
  4, 5) is a static table in `stream.c`; a function in `stream.h` would let
  a test check it. Low value: the table is a copy of Java's, and
  `append_dir_sizes` sees its first two sizes.
