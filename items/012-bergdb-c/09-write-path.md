012-09. Task: the write path
============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done** (part 1, 17:14 to 18:07: the clocks,
`KeyModSet`, the take, the append path, `StringMap`, each checked against
Java; part 2, 012-09 proper, 2026-10-28 20:55 to 22:14: `Trans`,
`TransNodes`, the record writer, `Db`'s creation and `execute`,
`setStartupDistance`, the API, `bergdb-run`; C writes Java's bytes on every
workload of the sets without restarts and reclaim, and Java starts C's
databases; sections 6.6 to 6.9). Approved with 012-01 by Frans's go
(012-01, 9.1).
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
6. **`setStartupDistance`**, as since 005-53 (`decc677`): the state
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
* The take is 005-49's paced take since `b8ac8a1` (007-07, 2026-10-28):
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
  `/Users/f/fl/bench/012/09-write-path/`, from `dd5c10f`; started 17:14):
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
  written again (Java at `decc677`). Without `treeifyBin`'s resize the
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
  on `build/java/classes` at `decc677`'s `java/`): a record of 24 bytes
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

## 6.6 Part 2, 012-09 proper: decisions

Taken in this task, as the plan left them to it (012-07's design and
012-08's modules followed as they are):

1. **Modules** (`c/readme.md`, section 2): `trans` (`Trans`,
   `Trans.Builder`, `Kv`), `transnodes` (`TransNodes`), `serial`
   (`StoredTrans.Serializer` as `ser_serialize`, and
   `NodeStream.appendNodes` as `ser_append_nodes`), `db` (`Db`'s write
   path, its reads, sync and close), `api` (`include/bergdb.h`'s
   functions and its handles' structs); `tools/run.c` (`bergdb-run`).
2. **Faithful line by line**: `executeInner`'s steps in Java's order, Db's
   listeners where Java calls them (the Dag's own pointer listener first,
   then the mark), `store`'s order (the take, `resolvePointers` before
   `clean`, `handleStillDirtyNodes` pass after pass, the newest written
   top node, the record, D), the serializer's `prepareToSerialize` before
   any byte (also before the record limit's check, as Java). The warm-up is
   ported (it reads, and counts the gets); the key and value
   transformations run as `bergdb.h` says (a key transformation's write
   hash is the new key's).
3. **No node table yet** (`Cache3`; 012-10 and 012-12 make it). An index
   object is held by the pointers that name it (its handle), by D's
   got-dirty lists, the record, `TopDs` and the newest written top node
   (012-07, 6.4.2). Without a start of index nodes and without eviction,
   every pointer to an index node holds a handle whose object is
   canonical: the writer's follower follows memory pointers only, and
   `NodeCollection.resolvePointers` changes nothing (its "continue" for a
   canonical object); a pointer that would need the table, a stream pointer
   or a version, is refused as unsupported (a bug in 012-09 if it came).
   Memory then follows Java's but for orphans (a node made and replaced in
   one transaction, `lastVersion`'s temporaries), which C frees at the
   next safe point and Java keeps in its table until eviction; no byte
   depends on them.
4. **The creation** as Java's: `writePrimordialTransaction` writes the root
   key node and the first top node through a `TransNodes` of its own and
   drops them; the start reads the record back (012-06's reader and
   parser, 012-07's constructors of parsed nodes) as `DbStarter`'s
   primordial startup, with recovery's steps 1 and 3 and
   `getStartupPosFromLastTransaction`. Any other start, of a database with
   records, is refused as unsupported (`UnsupportedOperationException`,
   `BERGDB_ARG` with the reason): 012-10.
5. **Memory** (012-01, 4.5): D's got-dirty entries count their nodes (the
   take releases them as their nodes go to the record, which counts them
   until `clear`); `replacedInTrans` counts its nodes too, with a flag,
   `OBJ_REPLACED`, as its identity set; `opMarks` borrows (cleared at
   `endOfOp`). Safe points after each put (after `endOfOp` and
   `clearFast`, as 012-07, 6.4.4 says) and at the end of `execute`.
   `x.transInfo` is cleared after `store`, where Java keeps an alias of
   D's newest entry (no listener reads it between transactions).
6. **Not yet, refused or left as Java's default**: reclaim (a retain
   duration other than forever is refused at the open and by
   `setRetainDuration`; 012-11), eviction (the cache size indicator is
   kept; 012-12), `bergdb_debug_print` and `bergdb_debug_check` (012-13).
7. **`bergdb-run`** uses `bergdb.h` only, as `Run` uses `Db`'s public API;
   a check's pairs are digested by a stop function that answers
   `BERGDB_CONTINUE`, so nothing is kept per pair; a workload that C cannot
   run yet (a restart, `-segments` from 1, a directory with a stream, a
   retain duration) exits 3 before anything is written. The names of
   Java's exceptions in its `refused` and `start error` lines come from
   `bergdb_errmsg`, whose text now begins with them (a header change,
   noted in 03-c-api.md).
8. **`cross.sh`**: side B's runs that C cannot do yet are Java's
   (`java-only.txt`, as 012-08's dumps), and the report counts C's.
9. **`getTrans` at a position inside a record** fails the database, as
   Java's does (005-34: the bytes there are not a committed record, which
   is corrupt data as for the other reads).

## 6.7 Part 2, 012-09 proper: progress

**Java's reference:** `main` at `8a7ceb9`, `java/` as of `decc677`.
**Clone:** `/Users/f/fl/bench/012/09-proper/`, a clone of `bergdb` at
`8a7ceb9` with 012-08's work merged (`b7ca7ef`, from 012-08's pause commit
`417102c`); committed locally, the conductor copies the files in.

* 20:55: started; read 012-01 (sections 1, 3, 4, 6), this plan with part
  1's progress, 012-02 (sections 2 to 8, 15), 012-07 (section 6), 012-08,
  012-05 (section 6), `c/readme.md`, and Java's `Db` (all), `Trans`,
  `TransNodes`, `StoredTrans.Serializer`, `NodeStream.appendNodes`,
  `DbHelper.handleStillDirtyNodes`, `NodeCollection`'s writer follower and
  `resolvePointers`, `DbStarter`'s primordial startup, `Run`, `Workload`.
  Next: `Trans` and its builder, `TransNodes`, the serializer, the
  creation with its first byte check.
* 21:16: the write path written, on part 1's modules and 012-07's and
  012-08's: `trans` (`Trans` and `Trans.Builder`, with `Kv`), `transnodes`
  (`TransNodes`), `serial` (`StoredTrans.Serializer` and
  `NodeStream.appendNodes`), `db` (`Db`: the creation and the start that
  reads it back as `DbStarter`'s primordial startup; `executeInner` with
  `checkSize`, `warmup`, the top node ordinals, `checkDirtyNodes`,
  `ExecuteData.begin`, the STM, the clock; `putKvs` with Db's listeners
  and the marking, `endOfOp`, `endOfTrans`; `store` with the take,
  `resolvePointers`, `handleStillDirtyNodes`, the newest written top node
  and the record; `setStartupDistance`; the reads, `sync`, `close`), `api`
  (`include/bergdb.h`'s functions on them) and `tools/run.c`
  (`bergdb-run`, Java's `Run` through `bergdb.h` only). **The first byte
  checks**: the creation alone (264 bytes) and single puts, deletes, an
  empty transaction and a `now`, Java's bytes and `Run`'s text at the first
  try (`7eb1518`).
* 21:23: `cross.sh`: side B's runs that C cannot do yet are Java's
  (`c_runs`: a workload with restarts or that may reclaim; the crash
  variants' runs after, `-segments 1`; side B's turns), and the report
  counts C's. New workloads that C runs: `coresame:plain` (Export: CoreSame's
  draws without its retain duration and restarts), Gen seeds with
  `restarts=0,retain=0` (quick: 5 and 6, the second with node size 8 and
  startup distance 100; full: 241 to 280, and 281 to 300 with node size 8
  and startup distance 100), `workloads/nowmoves.wl` (part 1's F4: a `now`
  that moves the next transaction's time, without restarts),
  `workloads/sdcut.wl` (F1: a decrease of the startup distance from
  2,500,000 to 400,000 after 3 MB; 3 takes stop at a transaction that 2 sd
  alone would take, the span term) and `workloads/full/sdcut-large.wl`
  (the full set only: 5,000,000 to 400,000 after 12 MB; 9 such stops).
  `cross.sh quick C=build/test`: **OK, 16 workloads, C's runs of 8, 0
  differences** (runs, files, scans, dumps; Java dumps C's directories with
  its audit on). `02ce175`. The full set started in a run-only clone
  (`c/build/fullrun/`, a `git clone` of this clone at `02ce175`, ignored by
  Git), so that the gate can run here meanwhile. Next: the unit and
  functional tests, the allocation-failure runs, the gate.
* 21:30: unit tests (`t_db.c`): Java's stream of `records.txt` (Java's
  `Db`, node size 8, startup distance 100, 14 transactions), its
  transactions read back from its records and executed again by C's `Db`,
  gives Java's stream byte for byte, record by record, with the recount
  after each; `Trans.Builder`'s order and its rules for a key given twice;
  the refusals before the go point (005-17's `checkSize`, 005-31's
  `checkDirtyNodes` under a lowered record limit, the STM, 005-18's clock),
  each leaving the stream and the state as they were, and the bytes after
  them those of a run without them; `setStartupDistance` (005-53: the
  clamp, the value in force writes nothing, a refused dummy puts the
  setting and the meta block's value back, a stopped database refuses);
  the allocation failures in turn over Java's transactions (235 runs: 20
  opens refused, 105 transactions refused with NOMEM and then executed
  again with Java's bytes, 108 failed databases; every close frees all).
  Functional tests (`test/func/f_api.c`, through `bergdb.h` only): a
  database in a directory (times, a `now` that moves a time, a delete of a
  missing key, `getOne` at times, `getMany` with a count, a prefix and
  backward, `getTrans` and its refusals, `sync`, the stats, the files), the
  start of an existing database refused until 012-10 with nothing written,
  the API's refusals, a callback that calls its database (`BERGDB_STATE`),
  `getTrans` inside a record failing the database as Java's (005-34), and
  the allocation failures in turn through the options' counts (21 opens,
  324 transactions refused, 611 failed databases). **C BEFORE COMMIT OK
  (91 s; 292 unit tests, 3 functional tests), with `bergdb-run` as side B
  of its quick cross set** (`8cb5706`, then `test/func` in the next
  commit).
* 21:34: `ser_serialize` split from `ser_append_nodes` (Java's
  `Serializer.serialize` and `NodeStream.appendNodes`), and Java's
  `StoredTrans` serializer tests that C has ported with `TransNodes`'
  (`t_serial.c`, 11 tests: empty and full records parsed back, the corrupt
  got-dirty count, the record limit, topPos of a top node in the record and
  of an earlier one, the formats refused, the got-dirty ids and positions,
  a delete node, the startup position, the keys, the same bytes from a
  reused serializer, a record across a meta block). A hand check of
  records larger than the write buffer: 12 MB and 25 MB values and values
  of 199,900 to 200,001 bytes, `bergdb-run` against `Run`, the same text
  and the same 40 stream files and lock file (37.6 MB).
* 21:36: the first `cross.sh full C=` run (the run clone, tools of the test
  build at `02ce175`): runs, files, scans and dumps of all 343 workloads
  compared, **0 differences**; C ran 104 of them (side B's runs: C's of
  104, Java's of 239, the workloads with restarts or reclaim): StreamDigest's
  eight Level 2 configurations in their plain and reads modes (16, the
  100 MB one included), `coresame-plain`, 84 Gen seeds (19 of 1 to 200, 5
  of 201 to 240, 40 of 241 to 280, 20 of 281 to 300 with node size 8 and
  startup distance 100), `nowmoves`, `sdcut` and `sdcut-large`; Java
  dumped each of C's directories with its audit on, and its dumps equal
  C's (C's dumper made 482 of side B's dumps). The crash variants, the
  corrupt variants and the turns follow.
* 21:44: beyond the sets, by hand (a script in the scratchpad: Export's
  Gen workloads, Java's `Run` in one JVM against `bergdb-run` of the
  release build, outputs and directories compared): 150 Gen seeds (1001 to
  1150, `restarts=0,retain=0`, the rest drawn: node sizes, startup
  distances, setters, large values, long keys, reads) **0 differences**
  (425 MB on each side); 150 seeds (2001 to 2150) with node size 8 and
  startup distance 100, **0 differences** (524 MB); and Export's scale
  workload of 1,000,000 keys without its restart line (10,207
  transactions, 98 MB), **the same output and files** (Java 5 s, C 4 s, on
  a loaded machine).
* 21:50: mutations of the write path, each against Java's outputs and
  directories on five workloads (`coresame-plain-n1500`, Gen 1003, Gen 2001
  with node size 8 and startup distance 100, `nowmoves`, `sdcut`; a script
  in the scratchpad, the tree restored after each): Rule A's still-dirty
  test in one pass (4 of 5 workloads differ), the replaced nodes left in
  the got-dirty list (4), `prevPos` written as the new position (5), the
  newest written top node never updated (5), ids from the record's
  position + 3 (5), the super root not marked when accessed (5), an
  operation's marks made dirty although it changed nothing (3). Unmutated:
  all 5 the same.
* 21:49: the first full run's end: `CROSS full OK: 343 workloads, 1262
  crash cuts, 498 corrupt variants, 6 in turns, the planted difference at
  1164 was found and explained; side B: .../build/fullrun/tools-c; 1514 s`
  (crash variants: 1,262 cuts, 0 differences; corrupt variants: 498, 0
  differences; runs in turns: 6 workloads, 0 differences). The gate on the
  final code (`ed454d1`): **C BEFORE COMMIT OK (68 s)**: 304 unit tests and
  4 functional tests, in both builds and under `leaks`; the quick cross
  set with `bergdb-run` as side B (16 workloads, C's runs of 8); the
  write checks. 21:50: the second and last full run started, with a copy
  of the final test build's tools (`build/fullrun/tools-c2`, the run clone
  at `ed454d1`).
* 22:14: **the second and last full run, on the final tools** (`ed454d1`,
  `build/fullrun/tools-c2`): `CROSS full OK: 343 workloads, 1262 crash cuts, 498 corrupt variants, 6 in turns, the planted difference at 1164 was found and explained; side B: build/fullrun/tools-c2; 1451 s` (compared in 624 s: 0 differences; crash variants: 1262 cuts, 0 differences, in 1146 s; corrupt variants: 498, 463 refused or with error lines, 0 differences, in 1418 s; runs in turns: 6 workloads, 0 differences, in 1441 s). **012-09 done**: section 6.8.

## 6.8 Done when, as it holds

Part 2's own, with part 1's (6.2) where it gave them:

1. **Creation** (`db.c`: `write_primordial_transaction`, the start that
   reads it back): Java's 264 bytes at the first try (21:16), and in every
   workload of the sets that C runs (8 in quick, 104 in full) and in
   `t_db.c` against Java's stream of `records.txt`.
2. **`execute`** as `executeInner` (decision 2): `Trans.Builder.build`'s
   order and rules (`db_trans_build`); the checks before the go point, each
   with a test that it refuses and leaves the stream and the state as they
   were, the later bytes those of a run without the refused transaction
   (`db_refusals`: 005-17, 005-31, the STM, 005-18; `db_top_ordinals`:
   005-02; `api_refusals` through `bergdb.h`); the warm-up; the puts with the
   key and value transformations (`api_transformations`); `store()`; the
   clock's end; the read set's record (a later read set conflicts).
3. **The take** (part 1's `transseq`, called by `store` as Java's
   `Db.store` calls `TransSeq.take`): which transactions, in what order,
   within what budget; the startup position of each record; the got-dirty
   lists (marking, `endOfOp`, `endOfTrans`, Rule A); ids and vpos;
   `topPos` and the newest written top node: Java's bytes on every
   workload below, and each of seven mutations of them found (21:50).
4. **The record writer** (`serial.c`, `rstream`'s appends): Java's
   `StoredTrans` serializer tests (`t_serial.c`), and Java's bytes with
   records across meta blocks and larger than the write buffer.
5. **`DbClock`**: part 1's, and `nowmoves.wl` (a `now` that moves a
   transaction's time) in both sets, Java's times.
6. **`setStartupDistance`** (005-53): `db_set_startup_distance` (the clamp,
   the value in force writes nothing, a refused dummy puts the setting and
   the meta block's value back, a stopped database refuses);
   `sdcut.wl` and `sdcut-large.wl` (decreases with the take's span term)
   and Gen's setters, Java's bytes.
7. **Appends to the directory**: part 1's `stream`; the files' names,
   sizes and bytes equal Java's in every workload that C runs, the 100 MB
   one included.
8. **The bytes.** Every workload of the sets without restarts and without
   reclaim: StreamDigest's eight Level 2 configurations in their plain and
   reads modes, CoreSame without its retain duration and restarts
   (`coresame:plain`), Gen's random seeds (84 in full), `nowmoves`,
   `sdcut`, `sdcut-large`: C's directory equals Java's, file by file and
   byte by byte, and `bergdb-run` prints `Run`'s text (`cross.sh quick` and
   `full` with `C=`, 0 differences). By hand: 300 more Gen seeds (150 with
   node size 8 and startup distance 100) and a million keys, 0
   differences.
9. **C to Java.** `cross.sh` dumps each of C's directories with Java's
   `Dump` with its audit on (`-audit 1`, assertions on): every start passed
   and every dump equals C's own and Java's of Java's directory.

The task's instructions: **the C gate prints C BEFORE COMMIT OK** (68 s)
with `bergdb-run` in its quick cross set; **`cross.sh full` with `C=` the
test build's tools passes** (21:49, 1,514 s, and the second run, on the
final tools, in the last entry of 6.7).

## 6.9 Notes for the conductor

* **Files** (all in `items/012-bergdb-c/`): `09-write-path.md`,
  `03-c-api.md` (its progress: the header's one change), `c/readme.md`,
  `c/include/bergdb.h` (`bergdb_errmsg`'s comment), new `c/src/api.c`,
  `api.h`, `db.c`, `db.h`, `serial.c`, `serial.h`, `trans.c`, `trans.h`,
  `transnodes.c`, `transnodes.h`; changed `c/src/err.c`, `err.h` (four
  codes), `obj.h` (`OBJ_REPLACED`), `plat.c`, `plat.h` (`plat_random`);
  `c/tools/run.c`, `c/tools/readme.md`; `c/test/unit/t_db.c`,
  `t_serial.c`, `main.c`; `c/test/func/f_api.c`; `c/test/cross/cross.sh`,
  `c/test/cross/java/Export.java`, `c/test/cross/workloads/nowmoves.wl`,
  `sdcut.wl`, `workloads/full/sdcut-large.wl`.
* **012-05's text** (not this task's file): 05-cross-harness.md, 6.5's
  table of the sets and Export's usage lack what this task added: Export's
  `coresame[:n=N][:plain]`; quick's `coresame:n=1500:plain`,
  `gen:5:n=300,restarts=0,retain=0`,
  `gen:6:n=300,maxnode=8,sd=100,restarts=0,retain=0`; full's
  `coresame:plain`, Gen 241 to 280 `restarts=0,retain=0` and 281 to 300
  `maxnode=8,sd=100,restarts=0,retain=0`; `workloads/full/` for the full
  set's own hand-written workloads; and that with `C=` side B's runs that C
  cannot do yet are Java's and counted (decision 8).
* **Part 1's findings F1 and F4** have their workloads now (`sdcut*.wl`,
  `nowmoves.wl`). F4's Gen option (a `now` before `t -` lines) is not
  added: Gen is 012-05's.
* **Findings in Java**: none in part 2.
* **For 012-10**: the start of an existing database goes where `db_open`
  now refuses it; it needs the node table (decision 3), the writer's
  `makeCanonical` and stream pointers in `follow`, Rule R in
  `resolve_pointers`, and the rerun through Db's listeners (with no
  running transaction they mark nothing, as Java's with `x.transInfo`
  null). `bergdb-run` then drops its exit 3 for restarts, and `cross.sh`'s
  `c_runs` its first condition.
* Part 1's question for Frans (6.4) stands; part 2 adds none.

