012-09. Task: the write path
============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: part 1 done** (started 2026-10-28 17:14, done
18:07; section 6: the clocks, `KeyModSet`, the take, the append path,
`StringMap`, each checked against Java); 012-09 proper not started (after
012-07 and 012-08; 6.5). Approved with 012-01 by Frans's go (012-01, 9.1).
Phase C (012-01, section 8). Effort: max. After: 012-08.


# 1. The goal

C creates databases and executes transactions, and writes Java's bytes:
the creation, `execute` with everything before and after its go point,
the take of dirty index nodes into records, the record writer, the meta
blocks, and appends to a directory. Without restarts in this task (that is
012-10) and without reclaim (012-11). With it, C's databases open in Java.

Done when:

1. **Creation**: an empty directory gets the first meta block and the
   primordial transaction, 264 bytes (`Db.CREATION_LENGTH`), as Java's.
2. **`execute`**, as `Db.executeInner`: the transaction built and sorted
   as `Trans.Builder.build` does (in key order; of two puts of a key the
   later wins, and a put wins over a delete of the key in either order:
   "Non-deletes take precedence over deletes"); the checks before the go
   point (the read set against `KeyModSet`, refused as `RerunException`;
   the end of the top node ordinals, 005-02; the size, 005-17; the bound
   on dirty index nodes, 005-31; the clock, 005-18), which leave
   everything as it was; the warm-up; the puts with the key and value
   transformations; `store()`; the clock's end; the read set's record.
3. **The take**: `TransSeq` and `StartupPos`: which earlier transactions'
   dirty nodes a record takes, in what order, within what budget; the
   startup position stored in each record; the got-dirty lists; ids and
   vpos (`setIdOfNode`, `ExecuteData.increaseNextVpos`); `topPos` and the
   newest written top node.
4. **The record writer**: `StoredTrans.Serializer` (positions set before
   writing, `prevPos`, sizes, padding, the record limit) and
   `NodeStream.appendNodes`; `RecoverableStream`'s appends, with the meta
   blocks written where a record reaches them and their fields as Java
   sets them.
5. **`DbClock`**: transaction times, lookup times.
6. **`setStartupDistance`**, as since 005-53 (`fd8f513`): the state
   checked first, the clamp, nothing written for the value in force, else
   the dummy transaction, and the setting and the meta block's value put
   back if the dummy is refused or fails.
7. **Appends to the directory**: new files at the sizes and names of
   `FileStream`; the buffer, written when full, at `sync` and at close;
   `F_FULLFSYNC` at `sync` and close (012-01, 4.3).
8. **The bytes.** On every workload without restarts and without reclaim
   (`StreamDigest`'s Level 2 configurations in their first two modes,
   `CoreSame` without its retain duration and restarts, random seeds), C's
   directory equals Java's, file by file and byte by byte, and
   `bergdb-run` prints the same times and positions as `Run.java`.
9. **C to Java.** Java starts each of C's databases, with assertions and
   its audit on, and its dump equals C's.


# 2. Read first

* Java: `Db` (`executeInner`, `store`, `putKvs`, `warmup`, the checks,
  `fail`, `writePrimordialTransaction`, `setStartupDistance`, `start`'s
  creation branch), `Trans` (197 code lines), `TransNodes` (171),
  `TransSeq` (754 lines with tests since the paced take), `StartupPos`,
  `KeyModSet` (148), `DbClock` (65),
  `StoredTrans.Serializer`, `NodeStream` (241), `RecoverableStream` (the
  appends), `FileStream` (the appends and new files), `BufferedStream` and
  `StorageManager` for what the buffer does (not how its threads do it).
* `docs/sis-model.md` (the take, D, the startup position), 007-01 and
  007-03 (the take and its debt), 005-31, 005-17, 005-02, 005-18, 005-01
  (the go point), `docs/levels.md`, sections 3 and 4.
* 012-02, section 8.


# 3. The work

1. Port in the order the bytes depend on it: `DbClock`; `Trans` and its
   builder; creation; `TransNodes`; `StoredTrans.Serializer`; the appends
   with meta blocks; then `execute` with the take.
2. First byte check early: creation alone, then single puts, then larger
   transactions, then small startup distances (index writes on almost
   every transaction), then node size 8 (splits on almost every put).
   `cross.sh` with C as side B after each step; the scanners point at the
   first differing field.
3. The checks before the go point, each with a functional test that it
   refuses and leaves the database as it was.
4. P7: after the go point, a failure (an append that fails, memory) fails
   the database; every later call but close gets FAILED.
5. `bergdb-run`, C's workload runner, and its place in `cross.sh`.


# 4. Tests

The byte comparison (done items 8 and 9) on the quick and full sets;
unit tests of the serializer and the take on Java's vectors (records as
bytes); functional tests of refused transactions and of a failed
database; the allocation-failure runs of 012-01, 4.5 on small workloads
(before the go point the database as it was, after it failed); the Java
tests of `TransSeq` and `StoredTrans` ported where they apply.


# 5. Notes

* Here byte equality is won or lost. Port, do not redesign: the order in
  which nodes enter `TransNodes`, the order of the got-dirty list, when an
  id is given, how vpos advance. When a byte differs, find the Java line
  that decides it before changing C.
* The take is 005-49's paced take since `f89846d` (007-07, 2026-10-28):
  a record's share of D in proportion to its own bytes, whole
  transactions with a hashed dither, and the deadline at the span of the
  section's transactions (`TransSeq.take`, `span`, `dither`; `TransInfo`'s
  own bytes and the sums D and O). Its doubles follow 012-01, 3.2, point
  4. Read 007-07 before porting it.
* What C does in Java's threads (the buffer's writer) it does in the
  calls; that changes when bytes reach the file, not which bytes.


# 6. Progress

## 6.1 The split

012's conductor split this task in two on 2026-10-28, so that the parts
that need neither 012-07's index nodes nor 012-08's Dag start early:

* **Part 1** (a subagent, in the scratch clone
  `/Users/f/fl/bench/012/09-write-path/`, from `718e4d6`; started 17:14):
  1. the clocks: `DbClock` (transaction times, `currentTime`, lookup
     times, the range check of 005-18), the system clock as
     `SystemClock`'s code is (005-69), the test clock (`CoreTestClock`);
  2. `KeyModSet`, the STM's conflict set, as Java (with what 005-70 says
     it forgets at a start);
  3. the take: `TransSeq` and `StartupPos`, pure functions over the
     transactions' sizes and positions, with Java's doubles; checked by a
     replay of the take from C's parsed records on every record of the
     quick and full sets, and Java's tests of `TransSeq` ported;
  4. the append path below the index: `RecoverableStream`'s appends (the
     framing, the meta blocks with their fields as Java sets them, the
     padding and the last byte as given), `FileStream`'s appends and new
     files (names, sizes, the open rule at a restart, C1), the buffer
     written when full, at sync and at close, `F_FULLFSYNC` in `plat`;
     checked by re-appending the records of Java's streams through C and
     comparing the directories file by file and byte by byte, with the
     workloads' restart points;
  5. `StringMap`, reclaim's table text, if time allows.
* **012-09 proper** (after 012-07 and 012-08): `Trans` and its builder,
  `TransNodes`, `StoredTrans.Serializer` and `NodeStream.appendNodes`,
  `execute` with its checks, the creation's primordial transaction,
  `setStartupDistance`, `bergdb-run`, and done items 1, 2, 6, 8 and 9 of
  section 1, on part 1's modules.

## 6.2 Part 1's progress

* 17:14: started; read 012-01, this plan, 012-02 (sections 2 to 5, 8, 9,
  10.3, 15), 06's decisions, 007-07, and the Java classes (`DbClock`,
  `SystemClock`, `CoreTestClock`, `KeyModSet`, `TransSeq`, `StartupPos`,
  `RecoverableStream`'s appends, `FileStream`, `BufferedStream`,
  `StringMap`). Next: the clocks and `KeyModSet`.
* 17:21: `clock` (`DbClock`; `SystemClock` as its code is, 005-69; the
  API's test clock functions, `bergdb_test_clock_time` and `_set`) and
  `keymod` (`KeyModSet`, its bins as Java's, the empty first bin of a
  start, 005-70), with Java's tests and NOMEM runs; `plat`'s writes,
  forces (`F_FULLFSYNC`), lock and time; `err` gets `ERR_LIMIT` and
  `ERR_IN_USE` (Java's `DbException` of a limit, `DirectoryInUseException`).
* 17:26: `transseq` (`TransSeq`, `TransInfo`, `StartupPos`; the take
  hands its transactions to the caller, the cost through a function),
  Java's `TransSeq` tests ported (all of them, `testShare`'s mean of 2.5
  and `testDecrease` included), the vectors' share and dither bits on the
  module. `tools/takecheck.c` (`bergdb-takecheck DIR...`): the take
  replayed on C's parsed records, the startup position and the record's
  index nodes in the take's order (top nodes first) checked. Results, on
  012-02's kept directories (read only): quick set 10 directories, 3,572
  takes, 0 errors; full set 278 directories, 331,959 records, 331,193
  takes, 277,131 transactions taken, 2,277,271 index nodes in order, 0
  errors; `MakeStreams`' 14 whole streams (`deadline`, `setsd`,
  `reclaim`, `restarts`, `recovered-*`), 0 errors (the three incomplete
  creations are refused by the walk, as by Java's start). Mutations of
  the take: the dither's hash, the share times 1.01, u = 0.5, d_h = 3 sd
  give 100 to 237 errors on the full set; without the span term only
  `deadline` finds it (finding: the cross sets have no decrease of the
  startup distance, so their streams never use the span term); `<=` for
  `<` and the share times 1 + 1e-7 change no decision (ties of doubles).
  Next: the appends.
* 17:38: the append path. `stream`: `stream_open_dir_rw` (Java's
  `FileStream(dir)`: the directory made, `bergdb.lock` with `LOCK_TEXT`
  and its byte at 2^62 locked with `fcntl`'s `F_SETLK`, the files checked
  as before, the capacity index from the larger of the last two files,
  C1, the last file opened for writing, `00000000000000.bergdb` in an
  empty directory), `stream_append` into a write buffer (10,000,000 bytes
  by default, as `StorageManager.DEFAULT_BUFFER_SIZE`), written by
  `FileStream.append`'s loop when full, at `stream_flush` and
  `stream_sync`, which forces the files written and, after a new file, the
  directory, with `F_FULLFSYNC`; reads see the buffered bytes; an I/O
  error fails the stream (`ioException`); `newFile`'s names and
  `applyFileSizeChangeRules` (without the test setting `max2G`).
  `rstream`: `struct rs` (the stream and the in-memory meta block),
  `rs_append` (Java's framing, eager blocks, its checks), `rs_append_record`
  (the tail of `NodeStream.appendNodes`: lastTrans after the append),
  `rs_use_last_valid_meta_block` (recovery's steps 1 and 3, no fill).
  `t_append.c` ports `RecoverableStream`'s and `FileStream`'s tests that
  C has (test1, largeTransaction, appendNamedTransactions, test0,
  testRestart0, testRestartMissingFile, testBigAppend0, tFileSizeIncrease,
  testFileSizeRules0) and adds C1's layout (`FileLayoutProbe`'s, with and
  without the restart), the buffer, a file changed by someone else, and
  NOMEM runs (a leak at a failed listing found and fixed).
  `tools/reappend.c` (`bergdb-reappend [-run RUN.txt] SRC DST`): the
  records of Java's stream (C's walk and parser) appended through C's
  path, the in-memory block set as Java sets it (the creation's fields
  from Java's block at 0; lastTrans by C; at a restart, C's copy of its
  own last valid block; the startup distance from Java's block inside a
  `setStartupDistance` dummy, the only later input), the restarts at the
  lengths of Run's `end segment` lines, then the directories compared
  file by file and byte by byte, `bergdb.lock` included. Results: quick
  set 9 of 10 directories equal (1 cut by reclaim, skipped); full set
  (012-02's kept directories, read only) 232 of 278 equal, 46 skipped
  (cut by reclaim): 293,331 records, 1,953 restarts and closes, 3,302
  files, 916,668,584 bytes; `MakeStreams`' `big`, `deadline` (with its
  decreases of the setting), `setsd`, `restarts`, `n8`, `n30`, `fresh`
  equal, the crash cuts and recoveries skipped (012-10's). Mutations: no
  lastTrans after a record (226 directories differ), the open rule from
  the last file only (4), `size > distanceToMeta` (12), no lastTrans at a
  restart (6); the file size rule without its alignment test is found by
  the unit tests only (in the sets the stream from 0 is aligned anyway).
  The lock with Java, probed both ways (`/private/tmp/...scratchpad/
  lockprobe`): C holds it, Java's `FileStream` gets
  `DirectoryInUseException`; Java holds it, C gets `ERR_IN_USE`.
* 17:42: `test/cross/writecheck.sh [SETDIR] [C=DIR]`: both tools over a
  set's kept Java directories; the gate (`before-commit.sh`) now runs
  `cross.sh quick ... KEEP=1` and then this, step `write`: "WRITECHECK
  OK: 10 directories, 3584 records, 3572 takes replayed, 3151
  transactions taken, 21207 index nodes in order, 0 errors; reappend: 9
  directories equal, 1 skipped (a reclaim cut)".
* 17:47: `strmap` (`StringMap`, with `HashMap`'s order: `String.hashCode`
  over UTF-16 units, the table's resizes and `treeifyBin`'s resize of a
  small table; a tree bin, at a table of 64 or more, refused as not
  ported), Java's tests, reclaim's row in 012-02, 8.13's order, and
  Java's texts as vectors: `Vectors.java` writes `strmap.txt` (8 maps:
  reclaim's rows, 40 keys, 12 keys of one bucket, keys beyond ASCII,
  parsed texts), all equal; the other six vector files unchanged when
  written again (Java at `fd8f513`). Without `treeifyBin`'s resize the
  vector test fails.
* 17:52: `bergdb-takecheck` counts why each transaction was taken: on the
  full set 232,365 because they fit in the share, 42,794 by the dither,
  1,972 by the deadline alone, and no take stopped at a transaction that
  2 sd alone would have taken; on `MakeStreams`' `deadline` and `setsd`,
  1,323, 470, 45 and 9 such stops (012-02, 8.7's counts for those
  streams).
* 18:00: `tools/clockcheck.c` (`bergdb-clockcheck WORKLOAD DIR RUN.txt`):
  the workload's test clock (its `clock` and `t T` lines) replayed on C's
  `DbClock`, a new one at each segment's start (the creation reads the
  clock; a restart gets the last record's time, its last read time 0,
  C3), each `t` line's record, the internal records after it (reclaim's)
  and `setsd`'s dummy (a record of one value node, `/#i/-dummy`; reclaim
  rewrites that value too, among others) each at the clock as it is, and
  each `now` against Run's. Full set: 232 workloads equal (293,331
  transaction times, 4,309 `now`s), 46 skipped (cut by reclaim); quick
  set: all that are not cut. But mutations of `DbClock` (no last read time
  in `transactionBegin`, `currentTime` not keeping it, the last read time
  kept across a restart, i.e. C3 fixed) change nothing on the sets
  (finding F4); so `test/cross/workloads/clock.wl`, a hand-written
  workload (a `now` before transactions at an unchanged clock, before and
  after restarts), which the quick and full sets run, Java against Java
  until C has `bergdb-run`; its times are Java's 1000, 2001, 2002, 3000
  (not 3001: C3), 3001, 4000, 4001, 5000, 6000, and each of the three
  mutations makes `bergdb-clockcheck` report a difference there.
  `writecheck.sh` runs `bergdb-clockcheck` too. The gate: "WRITECHECK OK:
  11 directories, ... 0 errors; reappend: 9 directories equal, 2 skipped
  (a reclaim cut); clock: 9 workloads' times equal, 2 skipped" (in this
  run `coresame`'s physical cut had been made, C2, so it was skipped;
  in the runs before it had not). The full set's reappend again after the
  dummy's new rule: 232 equal, 46 skipped.
* 18:02: `KeyModSet` against Java's answers: `Vectors.java` writes
  `keymod.txt`, a sequence both sides make (xorshift64* from a seed, as
  the workloads' `r:` values): 200,000 adds of hashes below 50,000 at
  increasing times, six turnovers of the default set's four bins of
  32,000, and after every 1,000 adds `getFirstTime()` and 20 questions
  `modifiedAfter` (4,000 answers, 2,091 of them "modified"); C gives
  Java's answers and first times (`vectors_keymod`). Mutations: "too old"
  answered false (669 checks fail), three bins in place of four (105);
  the sub-bins' count changes no answer, as it should not. The other
  vector files are unchanged when Java writes them again.

* 18:03: a test of nested missing directories found that `plat_mkdirs`
  made only the deepest one (its search for the parent aliased its
  buffer); fixed.

* 18:07: `writecheck.sh` replays the take on the crash variants that side
  A recovered and ran on, too (`crash/W/CUT/a`). On 012-02's kept full
  set, the script's own line: "WRITECHECK OK: 278 directories, 331959
  records, 331193 takes replayed, 277131 transactions taken, 2277271
  index nodes in order, 0 errors; crash variants: 1262 directories,
  868192 records, 866930 takes replayed; reappend: 232 directories
  equal, 46 skipped (a reclaim cut); clock: 232 workloads' times equal,
  46 skipped" (77 s). The records not replayed are the creations and, in
  streams cut by reclaim, those before the first whose startup position
  is in the stream. The gate: "C BEFORE COMMIT OK (48 s)", its step
  `write` "WRITECHECK OK: 11 directories, 3594 records, 3581 takes
  replayed, ... 0 errors; crash variants: 64 directories, 9538 records,
  9474 takes replayed; reappend: 10 directories equal, 1 skipped (a
  reclaim cut); clock: 10 workloads' times equal, 1 skipped". **Part 1
  done.** Not done in part 1: a re-append of the streams cut by reclaim
  (from the decided cut it needs `pretruncate`, 012-11), and of crash
  cuts (recovery's fill, 012-10).

## 6.3 Findings of part 1

* **F1. The cross sets never use the take's span term.** No workload of
  the quick or the full set lowers the startup distance, so the span of
  D never exceeds 2 sd there, and a take without the span term (the
  deadline at 2 sd alone) gives the same records on all 278 directories;
  only `MakeStreams`' `deadline` (012-02's own stream, not in the sets)
  finds it. For 012-05 or 012-09 proper: a workload with `setsd` from a
  large value down to 400,000 after a few MB, in the full set (and a
  small one in quick), so that D4:B is compared between Java and C.
* **F2. `RecoverableStream.append` checks the size field at the
  buffer's start, not at `offset`** (`Bytes.bytesToIntLE(buffer, 0)`,
  `RecoverableStream.java:490`). Every caller passes offset 0, so nothing
  differs; with another offset the check refuses a right record and
  passes a wrong one. Probe (outside the repository,
  `/private/tmp/claude-502/-Users-f-fl-repos-f1/84ff067e-dce6-4c28-a354-b5d6389d3c5b/scratchpad/offsetprobe/src/OffsetProbe.java`,
  on `build/java/classes` at `fd8f513`'s `java/`): a record of 24 bytes
  at offset 8, "refused: Bad transactionSize in byte buffer, was 0,
  expected 24"; one whose own size field says 99 with 24 at the
  buffer's start, "appended". For the conductor to register in 005 (a
  slip of the kind of 005-75). C's `rs_append` takes the record's
  pointer, so it checks the record's own field, as Java does for every
  call Java makes.
* **F3. The directory's lock is the process's** (a question, 6.4).
* **F4. The cross sets never let a `now` move a transaction's time.** In
  none of the quick and full sets' workloads does a transaction follow a
  `currentTime()` at an unchanged clock, so `DbClock`'s last read time
  (012-01, 4.4) and C3 at a restart decide no time there: three
  mutations of it pass all 232 workloads. Part 1 adds
  `test/cross/workloads/clock.wl` for it (above); a Gen option that puts
  `now` before `t -` lines would cover it in the random workloads too
  (012-05's `Gen`, for the conductor).
* **F5. Whether `coresame` is cut depends on the run** (C2, 012-02, 10.3):
  the gate's quick set had `coresame-n1500`'s front file deleted by
  reclaim's physical cut in one run and not in the others, so the
  re-append and the clock replay skip it in some runs. Expected (C2); a
  re-append from the decided cut would need `pretruncate` (012-11).

## 6.4 A question for Frans: a second open in the same process

`bergdb.h` (012-03) says of `BERGDB_IN_USE`: "Another database holds
the directory, in this process or another". C takes Java's lock, an
`fcntl` lock of the byte at 2^62 of `bergdb.lock`, which excludes Java
and C in other processes both ways (probed, 6.2, 17:38). But a POSIX
lock belongs to the process: a second open of the directory in the same
process is not refused, and its close (any close of a descriptor of the
file) releases the first open's lock, so that another process could
then open the database beside it. Java avoids both with a JVM-wide set of
locked directories (`FileStream.LOCKED_DIRS`), checked before the lock
file is opened. C has no global state (P9; the gate refuses writable
data in the library).

* **A.** Document it: within one process, open a directory once; a
  second open is the caller's error and is not detected. `bergdb.h`'s
  text of `BERGDB_IN_USE` becomes "in another process". No global state.
* **B.** A process-wide table of open directories (by device and inode),
  guarded by a mutex, checked before the lock file is opened, as Java's.
  Keeps the promise, at the cost of global state and a lock, against P9
  and 012-01, 4.2, and an exception to the gate's rule.
* **C.** Detect only: an open compares the lock file's device and inode
  with those of the directories of the databases that the same caller
  passes in (an option), and refuses a match. Partial, and awkward.

Recommended: A, as one caller at a time (012-01, 4.2) and P9 already
make the process's use of the library the caller's to order; part 1
implements A's behaviour (`plat_lock` says so) and changes nothing else.
012-13, which writes the API's text, takes the decision.

## 6.5 For 012-09 proper: part 1's modules and what is left

What part 1 gives (all in `c/src/`, each header says which Java class it
ports and how):

* `clock`: `struct dbclock` for `Db.dbClock`: `dbclock_transaction_begin`
  in `execute` after `stmCheckConflicts` (its `ERR_LIMIT` before the go
  point), `dbclock_transaction_end` after the puts, `dbclock_current_time`
  for `currentTime()`, `dbclock_lookup_time`, and
  `dbclock_set_last_trans_time` at a start (012-10). The API's
  `bergdb_test_clock_time` and `bergdb_test_clock_set` are implemented in
  `clock.c`; 012-13 must not write them again.
* `keymod`: `struct kms` for `Db.keyModSet` (a new one at each start, as
  Java, 005-70), with `keys_hash` of the key's segments as the hash
  (`Db.stmCheckConflicts`, `stmRecordKeys`).
* `transseq`: `struct ts_seq` for D, `ts_take` for `Db.store`'s take. The
  caller gives `ts_own_bytes(valueRecordBytes)`, `maxBytes =
  ST_MAX_RECORD_SIZE (the record limit) - fixedBytes` with Java's
  `fixedBytes`, and a cost function that is `TransSeq.recordBytes` (each
  got-dirty node's `StoredTopNode.getByteSize` or
  `StoredKeyNode.getByteSize`, and 16); it gets the taken `TransInfo`s,
  oldest first, adds their nodes to `TransNodes` (top nodes to the top
  array, key nodes to the key array, each once) and frees them. After the
  append, a `ts_info` for the record (`tpos`, `lastPos`, `tt`,
  `startupPos`, own bytes, its got-dirty nodes with their ids and types)
  goes to `ts_add`; `struct ts_startup_pos` is `x.startupPos`.
  `ts_checksum` is `TransSeq.checksum`, for 012-10's comparisons.
* `rstream`: `struct rs` holds the in-memory meta block;
  `writePrimordialTransaction` sets its id, startup distance, node size
  and time before the creation's record; `rs_append_record` is
  `NodeStream.appendNodes` after the serializer (position from
  `rs_next_spos(stream_length)`, lastTrans after the append);
  `setStartupDistance` sets the block's startup distance and puts it back
  on a refusal.
* `stream`: `stream_open_dir_rw` for a database directory (a memory
  stream for tests: `stream_open_memory`, the same `stream_append`);
  `stream_sync` for `sync` (and `stream_durable_length` for
  `getDurableLength`); `stream_finish` at close.
* `strmap`: `struct sm` for reclaim's rows and table (012-11).

Left for 012-09 proper: `Trans` and its builder, `TransNodes`,
`StoredTrans.Serializer` and `prepareToSerialize` (positions, ids,
`prevPos`, sizes, the record limit), `execute` with its checks and the
go point, the got-dirty lists, `handleStillDirtyNodes`, `topPos`, the
creation, `setStartupDistance`, `bergdb-run` and its place in
`cross.sh`, and done items 1, 2, 6, 8 and 9 of section 1. The checks of
part 1 stay useful there: `writecheck.sh` on C's own directories (side
B) once `bergdb-run` writes them.

For the conductor, not written by part 1 (outside its files): rows for
`c/readme.md`'s module table (`clock` DbClock, SystemClock and
CoreTestClock, `clk_`/`dbclock_`; `keymod` KeyModSet, `kms_`; `transseq`
TransSeq and StartupPos, `ts_`; `strmap` StringMap, `sm_`), its tools
(`bergdb-takecheck`, `bergdb-reappend`, `bergdb-clockcheck`), the gate's
new step `write` in its section 1 (`before-commit.sh`'s header says it),
`plat`'s and `stream`'s rows (writes, forces, the lock, the time; the
directory for writing), and `tools/readme.md`'s list.
