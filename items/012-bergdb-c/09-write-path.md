012-09. Task: the write path
============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
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
6. **`setStartupDistance`**: the clamp and the dummy transaction.
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

Not started.
