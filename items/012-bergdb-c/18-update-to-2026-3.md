# 012-18 Feasibility: the C clone brought to release 2026.3

Created 2026-11-09 by Frans Lundberg. Status: open.

Frans, 2026-11-09, 09:38: "012-bergdb-c is a C port of BergDB Core,
release 2026.2. Since we have plenty of usage today and this is
independent, unattended work. Would it be reasonable to update 012 to
match Java release 2026.3 in independent. Investigate the feasibility of
this using a new subagent at xhigh."

A feasibility study only: what changed in Java's Core between the tags
`release-2026.2` and `release-2026.3`, what of it the C clone (`c/`, 012)
needs, how C is tested against Java and what would show that it matches
2026.3, the work and its risks, and a recommendation. Made from reading
alone: the diff between the tags, the release notes
(`releases/2026.3/readme.md`), C's code and its cross harness. Nothing was
built or run (006-16's `QUIET-BLOCK` was in force, and another session
timed on F53 until 13:00). Where this file says that C has a fault, it
cites the C code that shows it; none was reproduced.


# 1. In short

* **Feasible, and well bounded: about a day of unattended work**, of which
  4 to 6 hours of an agent's coding and about 2 hours of runs on a quiet
  F53; about 1,500 to 2,000 lines of C, tests included, and about 100
  lines of the Java harness. 015-02, the port to 2026.2, was 1,691 lines
  in about 2 hours of coding.
* **One format change**: reclaim's settings in the stream, the internal KV
  `/#i/dreclaim/-settings.txt` (015-87), with `DbBuilder.retainDuration`
  removed. **One more byte change** with reclaim on: pSafe after the
  call's own records (015-54). Two more at limits only: a reclaim step
  within the value limit (015-50) and the last 1,024 database times kept
  for reclaim (015-55). StreamDigest's 8 configurations without reclaim
  give 2026.2's digests; its 4 with reclaim (`l3-*`) differ.
* **C has most of the Core's faults that 2026.3 fixed**, seen in its code:
  015-50, 015-54, 015-55, 015-72, 015-75 (in part), 019-01, 019-34, 019-32
  (C ports 2026.2's asserts line for line, and keeps them on, so a damaged
  node whose checksum is right stops it on an `assert`), 015-31 and
  015-06. And one C-only gap that 2026.3's 005-47 brings to light: C
  forces nothing at a file switch, so a power loss between syncs can leave
  a short file before a newer one, which both starts refuse.
* **Most of the diff is not for C.** Of 11,505 lines added in the Core's
  packages, 6,823 are testers and about 2,100 are in classes with no C
  counterpart (the storage thread, JMX, the stream contract's test
  classes, the resident registry); most of the rest is Javadoc and
  thread logic. Roughly 450 lines of Java's production code have a C
  counterpart to change.
* **The oracle is strong**: C's cross harness compares C with the
  release's Java byte for byte; it needs `JAVA_REF=2026.3` and four small
  fixes to compile against 2026.3 (`SyncLevel.STRONG`, `retainDuration`).
* **Suits unattended agents** in a scratch clone, as 012 and 015-02 did:
  only `items/012-bergdb-c/` changes, Java's code is untouched, and C's own
  gate and cross tests decide.
* **Recommended: do it now** (section 7), the coding today and the long
  runs in a quiet block of F53, after four decisions for Frans with
  defaults that go ahead (section 6). It goes against Frans's words of
  2026-11-05 that 012 stays a stable port of 2026.2 (012's readme); D1 is
  that choice.


# 2. What changed in Java's Core

From `release-2026.2` (`95bde62`, 2026-11-04) to `release-2026.3`
(`929fa33`, 2026-11-06): 93 commits touch `java/`, 67 of them the Core's
packages. The entries are those of the release notes, section "Changes
since 2026.2"; those of the Core were checked against the diff.


## 2.1 The size

| Part (`git diff --numstat`)                                  | Files | Added  | Deleted |
|---|---|---|---|
| `java/`                                                   | 161 | 15,158 | 3,545 |
| `core`, `stream`, `dag`, `storage`, `common`              | 64  | 11,505 | 2,756 |
| of them, the testers (`*Tester*.java`)                    | 17  | 6,823  | 785   |
| of them, production code                                  | 47  | 4,682  | 1,971 |
| production code with no C counterpart (26 classes, below) | 26  | 2,143  | 1,469 |

The classes with no C counterpart: `StorageManager` (replication removed,
−993 lines), `BufferedStream`, `StreamContract` and `StrictStream`
(harness 6.3's contract, test code in `src/`), the replication rules,
`DbHelper` (removed), `Residents`, `Jmx`, `Audit`, `DbUtil`, `Util`,
`FileStreamIo` and the other streams. In the ported classes, the code
added without comments: `Eviction` 401 lines (threads, batches, tests),
`FileStream` 372 (forcing, the cut thread, tests), `Reclaim` 309 (about
230 of them tests), `Db` 152, `Cache3` 62, `StoredValueNode` 41,
`StoredKeyNode` 37, `DbClock` 34, `NodeCollection` 23, `RecoverableStream`
21, `DbBuilder` 17, `DbStarter` 15, and a few lines each in `Dag`,
`Trans`, `StoredTrans`, `MetaBlock` and `NodeStream`. `TransSeq` (the
take), `KeyModSet`, `GetMany`, `Klong`, `Keys` and `Spos` are unchanged.


## 2.2 Bytes on disk

* **015-87, reclaim's settings kept in the stream** (the release's one
  format change, approved by Frans on 2026-11-05). `Db.setRetainDuration`
  and `Db.setReclaimInternalFraction` commit an internal transaction that
  puts `/#i/dreclaim/-settings.txt`, value exactly
  `retain=<time units>\nfraction=<units of 2^-16>\n` (forever is
  9223372036854775807, the default fraction 16384), and only when a value
  changes (`Reclaim.setSettings`). A start reads it before reclaim's table
  (`Reclaim.initFromDb`) and refuses any other form with an
  `InternalDataException` (`parseSettings`, byte for byte against
  `serializeSettings`). A setter is refused, and writes nothing, on a
  database that is not active and once the top node ordinals are used up
  (`Db.refuseIfTopOrdinalsUsed`). `DbBuilder.retainDuration` and
  `retainForever` are removed. A database whose settings were never
  changed has no such KV and runs with the defaults, so 2026.2's
  databases open as before. The bytes change wherever a setter changes a
  value: the settings' record, with its time and top node, and all after.
* **015-54, pSafe**: `Reclaim.markSafePositions` sets pSafe to
  `db.getStreamLength()` when it sets it, after the internal records that
  the same call appended (an iteration's table, a step), not to the end
  of the user transaction's record. With reclaim on, the table's pSafe
  values and where cuts come change.
* **015-50, a reclaim step within the value limit**: a step ends before a
  value that would take its value nodes past `StoredTrans.valueLimit()`
  (7/8 of the record limit, about 1.88 GB), and `Db.checkSize` no longer
  applies to internal transactions. The bytes change only where a step's
  old values reach the limit: huge values, or a lowered record limit in
  tests.
* **015-55, the last 1,024 database times kept for reclaim**:
  `DbClock.transactionBegin(boolean user)` refuses a user transaction
  after `LAST_USER_TIME = Klong.MAX_TIME − 1,024` with a `DbException`;
  internal ones go on to `Klong.MAX_TIME`. Only a clock near 2^56 units
  (about the year 2198) reaches it.

StreamDigest (release notes, Verification): the 8 configurations without
reclaim give 2026.2's digests; the 4 with reclaim (`l3-every1`,
`l3-node14`, `l3-node62`, `l3-node8`) differ, from 015-54 and 015-87. Its
new mode `restarts-once` sets the retain duration after the first start
only.


## 2.3 Algorithms

* **The start's checks** (refusals of damaged streams; valid streams read
  as before):
  * 015-72: a record whose size field is larger than its content is
    refused (`StoredTrans.Parser`: the content must fill the record).
  * 015-75: what were asserts are `StreamFormatException`s: a got-dirty
    entry whose id is not the node's at its position, a `topPos` that is
    not the newest version of its top node, and a record's startupPos that
    is negative, not a multiple of 8, in the first meta block, or after
    the record (`Db.checkStartupPos`, new).
  * 019-01: a meta block's version is read as an int, so a block with
    nonzero bytes 6 or 7 is refused (`VersioningStreamException`).
  * 019-34: a meta block whose last transaction's position is outside the
    stream is refused before recovery writes anything
    (`RecoverableStream.checkLastTransSpos`).
  * 019-32: a damaged node whose checksum is right: a key node's count
    must equal what its size holds, each klong must have a type, a key
    klong's pointer must be valid or null; a value node's key must be one
    that `Keys.toSegments` makes; a pointer must name a node of the right
    type (`NodeCollection.checkPointeeType`, in follows, installs and the
    start's linkage); one id has one type in the node table
    (`Cache3.checkType`); `NodeStream.readNode` checks the position; the
    Dag's put finds a klong in every non-leaf node (`Dag.checkFound`,
    a `DbException`). All were asserts or `ClassCastException`s.
* **Reclaim**: 015-50, 015-54 and 015-87 above; 015-53, a transaction
  that `stop()` overtakes in reclaim's work returns as committed; 015-52,
  a warmup read that a cut overtakes ends the warmup.
* **Eviction and the caches**: 015-66 (a failed batch fails the database
  before the write lock goes), 015-67 (a batch examines at most its
  handles, a node table map taken in parts), 015-68 (the start's rerun
  admits its large values: a value over 1 MiB is reached by a stream
  pointer), 015-69 (a resync of the test schedules), 015-70 (a lowered
  budget is reached when what must stay fits), 019-20 and 019-21 (the
  resident registry counts changed nodes with their bytes), 019-22 (a
  warmup keeps no value over 1 MiB), 005-52 (a warmup's load does not
  wait for eviction), 019-41 (an interrupted eviction thread).
* **Storage**: 005-47 (per-append forcing in `FileStream` a setting, on
  by default; with it off, the old last file is forced at a file switch
  and the stream up to a cut before the cut's deletes), 015-06 (the first
  file is made by the first append), 015-31 (a cut at the stream's length
  keeps the last file), 015-32 (a failed open closes its file and
  releases the directory, whatever it throws), 015-33 (`setMax2G`),
  015-26, 015-79 and 019-02 (lengths and ranges refused), 015-80, 015-82,
  015-83, 015-35, 015-81, 015-78, 015-34, 019-09, 019-37, 019-39 (the
  storage thread, its failures and its close), and 005-11: replication
  removed, `StorageManager` with one stream.
* **The error model** (019-10, 019-40): an `Error` in a read, a
  transaction (before its go point too) or a sync fails the database and
  is thrown as it is; an unchecked exception of a stream read fails it as
  an `IOException` does.


## 2.4 The API

* `DbBuilder.retainDuration` and `retainForever` removed (015-87);
  `getStreamCount()` became `hasStream()`, and a second stream is refused
  (005-11).
* `Db.setRetainDuration` and `setReclaimInternalFraction` commit, as
  above; they throw as a transaction does on a database that is not
  active.
* `Db.addReplica`, `removeReplica` and `getStorageInfos` removed (005-11);
  `getOneInternal` is no longer public (019-40). `SyncLevel.STRONG`
  removed (005-11). `AppendOnlyStream.seekFirstPos()` removed (019-04).
* Javadoc only: the error model (019-10), `setStartupDistance` clamps its
  value (015-76), a value transformation's result is the caller's to keep
  within the limit (015-51), the Core keeps the caller's arrays (015-47).
* The Pub API changed much (`dir(p)` gone, and more); C has no Pub API.

Four public methods of `Db` are gone (replication's three and
`getOneInternal`); none was added.


## 2.5 Refactors with no effect

Replication's removal (005-11: `DbHelper`, the four rule classes,
`StorageManager`'s replicas, `Db.syncStreams`), `Db.Internal.failByEviction`
renamed `fail`, `LoadListener.loaded(OpData)`, the tests' syncs from
`STRONG` to `ORDINARY`, and Javadoc throughout.


## 2.6 The testers

New harnesses by fault class (018-02 to 018-08): `CorruptStreamTester`
(harness 6.1, corrupt streams at a start; 1,284 lines), `StorageFaultTester`
(6.2, failures and interrupts in storage; 1,145), `StreamContractTester`
and `StorageContractTester` with `StreamContract` and `StrictStream`
(6.3), `LimitsTester` (6.4, sizes and times at their limits, the record
limit lowered to 240 kB, 300 kB or 1 MB; 1,035), `EvictionAccountingTester`
(6.5; 681), and jcstress (018-08). New tests in the existing testers, among
them those a port takes over: `DbTesterRestart`'s eight on reclaim's
settings (`testReclaimSettingsKeptOverRestarts`,
`testRefusedReclaimSettingChangesNothing`,
`testReclaimSettingInForceWritesNothing`,
`testReclaimSettingsKeptAcrossRestart`, `testReclaimSettingsSurviveCuts`,
`testStreamWithoutSettingsHasDefaults`,
`testMalformedSettingsRefusedAtStart`, `testReclaimSettingAtEndOfOrdinals`)
and its refusals (`testEnlargedRecordSizeRefused`,
`testCorruptStartupPosRefused`, `testCorruptGotDirtyIdRefused`,
`testOlderTopPosRefused`, `testMetaBlockLastTransPosRefused`,
`testVersionHighBytesRefused`); `Reclaim.Tester`'s
`testSafePosAfterTheCallsRecords`, `testStepWithinValueLimit` and
`testUserTransactionLeavesTimesForReclaim`; `DbClock`'s
`testTimeMarginForInternal`; `StoredKeyNode.testRefusesBadKlongs` and
`StoredValueNode.testRefusesBadKey`; `Eviction`'s tests of 015-68 and
015-70.


# 3. What the C clone needs

C as it is (the port of 2026.2, `be51a78`), checked against each change.
"Fault" means that C's code does what Java's did before the fix.

| ID       | Java's change                      | C today                             | For C    |
|---|---|---|---|
| 015-87   | reclaim's settings in the stream   | not kept; an option of the open     | needed   |
| 015-54   | pSafe after the call's records     | fault: `reclaim.c`, line 967        | needed   |
| 015-50   | a step within the value limit      | fault: `db.c` 1099, internal too    | needed   |
| 015-55   | last 1,024 times kept for reclaim  | fault: `clock.c`, no user flag      | needed   |
| 015-72   | record size must equal its content | fault: `strans.c` after line 162    | needed   |
| 015-75   | start's asserts become checks      | 3 of 6, as `AssertionError`         | needed   |
| 019-01   | meta block version an int          | fault: `meta.c` 53, `rstream.c` 139 | needed   |
| 019-34   | last trans position checked        | `IllegalArgumentException`, later   | needed   |
| 019-32   | damaged nodes refused              | fault: aborts, or casts unchecked   | needed   |
| 005-47   | old last file forced at a switch   | C-only gap: `stream.c` `new_file`   | needed   |
| 015-06   | first file at the first append     | fault: `stream.c` 406, at the open  | needed   |
| 015-31   | a cut at its length keeps the file | fault: `stream.c` 722, unreachable  | optional |
| 015-68   | rerun's large values admitted      | kept, counted in C's budget         | optional |
| 015-70   | lowered budget reached             | probably covered; a test to port    | optional |
| 015-67   | bounded batches                    | C's sweep is unbounded per call     | optional |
| 019-22   | warmup keeps no large value        | C does so already (`db.c`)          | no       |
| 019-10   | an `Error` fails the database      | C's NOMEM is a refusal (012-14)     | no       |
| `STRONG` | `SyncLevel.STRONG` removed         | `BERGDB_SYNC_STRONG` kept           | optional |


## 3.1 Needed

Needed because C must write the release's bytes, open its databases and
refuse what it refuses (`c/readme.md`, "Which Java"), and because the
cross tests against 2026.3 fail without them.

1. **015-87, reclaim's settings.** `reclaim.c`: `serialize_settings`,
   `parse_settings` (the exact form, else "InternalDataException"),
   `rc_set_settings` (an internal transaction through `db_execute`, the
   fields set after its commit, nothing written when in force, the top
   ordinals checked first), and `rc_init_from_db` reading the settings
   before the table. `db.c` and `api.c`: the two setters commit, refused
   on a database that is not active; their errors in `bergdb.h` gain a
   transaction's: `BERGDB_LIMIT` (the top ordinals), `BERGDB_FAILED` and
   `BERGDB_NOMEM`. `bergdb_options.retain_duration` goes, as Java removed the
   builder's (decision D2), with its uses: `db.c` 543 to 556, `api.c`,
   `tools/run.c`, `bench/cbench.c`, `test/stress/allocfail.c`, and the
   tests `f_settings.c` (17 uses), `f_reclaim.c`, `f_api.c`, `t_db.c`,
   `t_reclaim.c`, `t_evict.c`. Today C reads a 2026.3 stream with the KV
   and keeps it, but runs with its own options' values (release notes,
   Format).
2. **015-54, pSafe.** `mark_safe_positions(db, streamSize, e)` at
   `reclaim.c` 967 takes the length read before the call's own records;
   it becomes the stream's length when it is set. One line and a test.
3. **015-50.** `db_execute` calls `check_size` for every transaction
   (`db.c` 1099), reclaim's internal ones too, so a step whose old values
   pass the value limit fails the database inside a user transaction's go
   point, as Java's did; and `step()` (`reclaim.c` 630) has no stop at
   the limit. C has `record_limit` as a setting of its own (`db.h`), so
   Java's test with a limit of 100 kB ports directly.
4. **015-55.** `dbclock_transaction_begin` (`clock.c` 74) takes no
   user flag; its two callers (`db.c` 457, the creation, and 1134).
5. **015-72.** `st_parse` computes `transSize` (`strans.c` 162) but never
   compares it with the size field.
6. **015-75.** C refuses a negative startupPos, an older `topPos` and a
   got-dirty id that differs (`starter.c` 184, 594, 688), each as
   "AssertionError", 2026.2's assert; 2026.3 refuses them as
   `StreamFormatException`s with new texts, and three more startupPos
   cases (alignment, the first meta block, after the record).
7. **019-01.** `meta_version` (`meta.c` 53) and the header's check
   (`rstream.c` 139) read an unsigned short; `meta_fill_out_template` and
   `meta_begins_as_block` compare 4 + 2 bytes where Java now takes 4 + 4.
8. **019-34.** A last-transaction position past the end reaches
   `rs_remaining_trans_bytes`, which refuses it with
   "IllegalArgumentException" (`rstream.c` 66), as 2026.2 did; 2026.3
   refuses it with a `StreamFormatException` before recovery appends.
9. **019-32.** `snode.c` 255 checks `size > (nodeSize − 32) / 16` where
   Java now requires equality, and checks neither the klongs' types, nor a
   key klong's pointer, nor a value node's key. Where 2026.2's Java met an
   assert on such a node, C's line-for-line port meets the same assert,
   which is on in both of its builds (`c/readme.md`, section 3, rule 12),
   and the process aborts; where Java threw a `ClassCastException`, C
   casts the followed node to the type it expects with no check (`dag.c`
   325, 363, 372; `getmany.c` 373, 436) and reads it as that type. So a
   damaged node with its checksum right ends the application in C, or
   gives a read of wrong memory in the release build. The checks go
   into `snode.c`, `ncoll.c`, `nstream.c`, `ntable.c` (the install),
   `dag.c` (the put's search) and `starter.c` (the linkage).
10. **005-47's switch force (a C-only gap).** Java forced every append
    until 2026.3; C forces only at a sync, at a close and at a reclaim
    cut (`c/readme.md`, section 9), and `new_file` (`stream.c` 162)
    forces neither the old last file nor the directory. A power loss
    between syncs, after a switch, can leave the new file's name durable
    and the old file short; C's open, as Java's, then refuses the
    directory (`BadDirStateException`, a size that is not a multiple of
    100,000). 2026.3's `FileStream.newFile` forces the old last file first
    when per-append forcing is off, for this reason. C's power model
    (`test/stress/power.c`) never makes that image, as it takes a new
    name to be durable only after a force of its directory; it needs a
    mode where a name is durable at once, as a delete is.
11. **015-06.** `open_dir` makes the first file of an empty directory at
    the open (`stream.c` 406), and a refused creation (a clock out of
    range: `BERGDB_LIMIT`) leaves it empty on the disk; 2026.3 makes the
    first file at the first append and leaves `bergdb.lock` only.
12. **The harness** (`test/cross/`, `test/func/java/`, `bench/`): it does
    not compile against 2026.3. `Run.java` 244 and `StatsProbe.java` 76
    sync with `SyncLevel.STRONG`; `Run.java` 192, `MakeStreams.java` 74
    and 75, `StatsProbe.java` 100 and `JBench.java` 86 use the builder's
    `retainDuration` or `retainForever`. Beyond compiling: the workload
    header's `set retain` and `set fraction` (Gen, CoreSame) were applied
    at every start, the builder's way; in 2026.3 they become a
    `setRetainDuration` and a `setReclaimInternalFraction` after the
    creation's start only, as StreamDigest's `restarts-once` (decision
    D3). `Export.java` takes the new mode `restarts-once`. `java-build.sh`
    defaults to `JAVA_REF=2026.3` (`releases/2026.3/bergdb-2026.3-src.zip`
    and its `SHA256SUMS`); `examples/compare.sh` takes CoreDemo from it.
    Java's vectors are written again from 2026.3: the reclaim vectors
    (`Vectors.java`'s reclaim runs call `setRetainDuration`) change.

How each shows in the cross tests before it is ported: every workload
with a retain duration or a fraction differs (the settings' record and
pSafe: 181 of `cross.sh full`'s 446 have reclaim); the corrupt variants'
scans differ where Java's parser, which `StreamScan` calls, now refuses
(015-72, 019-32); `corrupt.sh`'s starts differ in the refusals' names and
texts (015-75, 019-01, 019-34, 019-32).


## 3.2 Optional

* **015-31**: a cut at the stream's length fails C's stream ("Bug",
  `stream.c` 722), as it failed Java's; reclaim never cuts there. A few
  lines.
* **015-68**: C's rerun creates the section's values with their stream
  positions and no admission list (`starter.c` 778: no pointer-created
  listener),
  so a value over 1 MiB stays in its leaf until eviction takes it. Unlike
  2026.2's Java, C counts it in its budget, so this is a difference of
  rule, not a leak: Java's rule is that such a value lives in the stream.
  Small; 019-47 (on `main` since 2026.3) is of the same class and would
  come with 2026.4.
* **015-70**: C's eviction at the end of a call resets its floor when D
  shrinks (`evict.c`, `ev_run`); it probably reaches a lowered budget,
  but only Java's test, ported, shows it.
* **015-67**: C's `ev_run` sweeps until the resident bytes are within the
  trigger, with no bound on one call's work: a latency property (010-01,
  P1), 012-16's proposal "a bounded eviction sweep", not a fault of the
  port. Its own task if wanted.
* **`BERGDB_SYNC_STRONG`**: Java removed `STRONG`; in C it is the same as
  `ORDINARY`. Remove it, or keep it as an alias (D2).
* **The new harnesses for C**: 6.1's corrupt streams, exported by a Java
  tool as directories and started by both dumpers (`corrupt.sh`'s way),
  would test steps 6 to 9 of section 3.1 beyond single-bit flips, which
  do not reach 019-32's damage (a checksum made right, or a byte changed
  between 0x00 and 0xff). 6.4's limits as workloads with a record-limit
  option (C has `record_limit`; Java's `StoredTrans.recordLimit` is a
  static field) would test 015-50 and 015-55. Each a few hundred lines.
* **Documentation** in `bergdb.h`: the startup distance's clamp (015-76),
  a transformation's result within the limit (015-51).


## 3.3 Not for C

* **Threads and the memory model**: 005-52, 015-34, 015-35, 015-52,
  015-53, 015-66, 015-69, 015-78, 015-80, 015-81, 015-82, 015-83, 019-08,
  019-09, 019-37, 019-39, 019-40, 019-41, 015-38 (JMX), 015-71 (the audit
  beside readers). C has one caller and no thread (`c/readme.md`, section
  8): no stop can overtake a transaction (015-53), no cut a warmup
  (015-52), no background write can fail unseen (015-35, 019-09).
* **The resident registry** (019-20, 019-21): C's resident bytes are the
  allocator's exact counts (012-12).
* **019-22**: C's warmup reads with `cache_all_except_large` already
  (`db.c`, `warmup`, through `dag_new_get_data`).
* **The stream's Java API** (015-26, 015-79, 019-02, 019-04, 015-33): C's
  stream is internal, takes no caller's ranges, and has no `setMax2G`.
* **015-32**: a failed `bergdb_open` leaves nothing open already
  (`bergdb.h`).
* **019-10's error model**: C's NOMEM before the go point and in a read
  is a refusal, by 012-14's decision, tested by the allocation-failure
  runs; Java's reason (an `Error` may be the application's, and the
  environment is unsound) does not hold for a checked NOMEM. Kept, and
  written as a departure.
* **Replication** (005-11) and **the Pub API**: C has neither.


# 4. How C is tested against Java

Today (`c/readme.md`, 015-02):

* **C's gate**, `c/before-commit.sh` (`C BEFORE COMMIT OK`, 179 s at
  015-02): the builds (release `-O2 -flto`; test with AddressSanitizer and
  UndefinedBehaviorSanitizer), the rules (no allocation outside `mem.c`, no
  global state, a `.h` for each `.c`, no double outside 11 places), 353
  unit and 26 functional tests in both builds and under macOS's `leaks`,
  `cross.sh quick` and `writecheck.sh`, 379 allocation-failure runs, and
  the examples against Java's `CoreDemo`.
* **Java's vectors**: `test/unit/vectors/*.txt`, what Java's own classes
  give for fixed inputs (codecs, checksums, keys, the take, reclaim runs,
  Java's arithmetic), written by `Vectors.java` from the release and
  committed; `t_vectors.c` checks every line.
* **The cross harness** (012-05), `test/cross/cross.sh`: workloads in a
  text format, run by Java's `Run` and C's `bergdb-run`; StreamDigest's
  configurations in its modes, exported with StreamDigest's own digest
  line, CoreSame, Gen's random seeds, and hand-written ones. Compared: the
  stream byte for byte (from the decided cut where reclaim cut), the run's
  text, the scans (Java's `StreamScan`, which also runs Java's record
  parser and walk, against `bergdb-scan`), the dumps (Java's with its
  audit), every crash cut recovered by both, corrupt variants' scans,
  turns (Java and C alternate on one directory), and C's runs under memory
  budgets. Sets: `quick` (in the gate), `full` (446 workloads, 1,357 crash
  cuts, 498 corrupt variants, 6 in turns, 1,784 budget runs; 2,262 s at
  015-02), `scale` (10M keys, 238 s), `random`. `JAVA_REF` chooses the
  Java: the release's source zip, checked against `SHA256SUMS`.
* **By hand** (`test/stress/`): `random.sh` (Gen's seeds by the
  thousand), `long.sh`, `corrupt.sh` (corrupt directories started by both
  dumpers: the same exit status and text; 656 variants at 015-02),
  `power.sh` (power-loss images of C's runs started by both, and Java's
  images by both), `allocfail.sh`, `gcc.sh`.
* **The Lean model**: not directly. C is held to Java's bytes, and Java to
  the model (the level scripts' conformance). A C trace exporter is
  012-16's next step 6, not made.

What would show that C matches 2026.3:

1. `c/readme.md`'s "Which Java" says 2026.3, and `java-build.sh` compiles
   2026.3's source zip by default.
2. `C BEFORE COMMIT OK`, with Java's vectors written again from 2026.3 and
   Java's new tests ported (section 2.6, the ones for C).
3. `cross.sh full C=build/test`: 0 differences, StreamDigest's `l3-*`
   configurations and the new `restarts-once` mode included, and their
   digests equal to the release's (`baseline.zip`, `f53/digests.txt`).
4. `cross.sh scale C=build/release`: the 10M-key database byte for byte.
5. `corrupt.sh`: the same exit status and text in every variant, the new
   refusals included; and the cases of 2026.3's refusal tests (section
   2.6) as variants, or 6.1's corrupt streams (section 3.2).
6. `power.sh`, both ways, with the model's new mode (section 3.1, step
   10): no acknowledged byte lost, and every image opens.
7. A negative control, as 015-02 had: C before the port against 2026.3
   differs on the `l3-*` workloads and on every workload with a retain
   duration, so the tests see the change.
8. `random.sh` over 1,000 seeds, `long.sh`, and `allocfail.sh` on a
   workload with the setters.


# 5. The work

## 5.1 The steps

| Step | What                                                    | Size, agent hours | Lines  |
|---|---|---|---|
| 0 | clone, `JAVA_REF=2026.3`, the harness compiles; baseline | S, 0.5          | 60  |
| 1 | 015-87, 015-54, 015-50, 015-55; the API; vectors         | M, 2 to 3       | 500 |
| 2 | 015-72, 015-75, 019-01, 019-34, 019-32, Java's texts     | M, 2 to 3       | 500 |
| 3 | the switch force, 015-06, 015-31; the power model        | S, 1            | 150 |
| 4 | optional: 015-68, 015-70's test, the corrupt-stream set  | S to M, 1 to 2  | 300 |
| 5 | the runs: gate, full, scale, corrupt, power, random      | M, 2 of machine | 0   |
| 6 | `c/readme.md`, 012's readme, the logs                    | S, 0.5          | 60  |

* **Step 0.** A scratch clone of `main` (section 5.3); C builds; the
  harness's fixes of section 3.1, step 12; `cross.sh quick` against
  2026.3, to list the differences before any change (the negative control
  of section 4, point 7).
* **Step 1.** Section 3.1, steps 1 to 4, each with Java's tests ported:
  `DbTesterRestart`'s eight on the settings,
  `testSafePosAfterTheCallsRecords`, `testStepWithinValueLimit` (C's
  `record_limit` at 100 kB),
  `testUserTransactionLeavesTimesForReclaim`, `testTimeMarginForInternal`.
  `tools/run.c` and `Run.java` take the header's settings once (D3).
* **Step 2.** Section 3.1, steps 5 to 9, with Java's exception names and
  texts, which the scans and `corrupt.sh` compare; Java's refusal tests
  ported as unit tests on crafted records and nodes (`t_records.c`,
  `t_snode.c`, `t_rstream.c`, `t_sdb.c`).
* **Step 3.** Section 3.1, steps 10 and 11, and 015-31; `power.c`'s mode
  where a new name is durable at once, shown to find the short-file image
  without the switch force.
* **Step 4.** By D4.
* **Step 5.** On a quiet F53, by the coordinator's plan: `cross.sh full`
  about 40 minutes, `scale` 4, `corrupt.sh` and `power.sh` some minutes
  each, `random.sh` over 1,000 seeds about 45 (012-14's 1,800 took 80
  minutes with their crash cuts and budget runs). C builds only on macOS
  (`plat`: `F_FULLFSYNC`; Linux is 012-16's next step 3), so s1 cannot
  take these runs.
* **Step 6.** "Which Java", the record of the 2026.2 state (its commit,
  as `c/readme.md` records `ae4aaf9` for the state before 015-02), 012's
  readme statement and index line (D1), and a subitem for the work's log
  (012-19).

In all, about 1,500 to 2,000 lines, half of them tests: 4 to 6 hours of
an agent's coding and about 2 hours of machine time, a day's unattended
work with waits for F53.


## 5.2 Risks

* **The format** (low): one new KV, its form fixed byte for byte by
  `serializeSettings`; the harness shows any slip at once, as every
  workload with reclaim writes it.
* **The harness's meaning** (medium): the header's retain duration
  applied once, where it was applied at every start, changes what Gen's
  and CoreSame's workloads test; a run that sets the header's value again
  at each restart would pass too (Java and C alike) but would write a
  record at each start that changed the value. D3 fixes the meaning.
* **Texts** (low, tedious): the scans and `corrupt.sh` compare exception
  names and messages, so each new refusal's text must be Java's; the
  tests point at each difference.
* **C-only consequences** (medium): where C's design differs from Java's
  (one caller, forces at a sync, eviction at the ends of calls), a fix of
  Java may hide a gap of C's own, as the switch force (section 3.1, step
  10) shows; it was found by reading, not by a test. The port's review
  should read 2026.3's crash contract (014-01, section 7: a crash leaves
  a prefix of what was appended) against C's stream.
* **Concurrency** (none for the port): 2026.3's thread fixes stay in Java;
  the risk is only of calling one Java-only that C has, and section 3.3
  gives the reason for each.
* **F53's time** (medium): the long runs need a quiet machine, which
  timing sessions and quiet blocks hold today; the builds of steps 0 to 3
  are small but are builds, so they too wait for 006-16's quiet block to
  end.
* **2026.4 coming** (low): the Core has 9 commits since 2026.3, none a
  format change (021-05 and 021-06 on keys, 019-46 a race, 019-47 the
  admission at a start); a later port to 2026.4 would be a small step
  after this one.


## 5.3 Unattended, in a clone

It suits unattended agents: a strong oracle (byte equality with the
release's Java, and the release's digests), changes confined to
`items/012-bergdb-c/`, and the pattern of 012 (unattended, 2026-10-28 to
29) and 015-02 (2 hours, 2026-11-05).

* **Clone and branch**: `git clone /Users/f/fl/repos/bergdb
  /Users/f/fl/bench/012-19/bergdb` at `main`'s head, a branch such as
  `012-19-c-2026-3`; `c/build/` stays in the clone. The release zips are
  in the repository (`releases/2026.3/`), so the clone has them.
* **Gates**: `c/before-commit.sh` must print `C BEFORE COMMIT OK`, and
  `cross.sh full` and `scale` pass against 2026.3. `java/` is not
  touched, so `java/before-commit.sh` is not needed (AGENTS.md); C stays
  out of `night.sh` and Java's gate (Frans, 2026-10-29: C a separate
  project, tests by hand).
* **Commits**: in the clone, in Frans's name, without AI attribution; the
  coordinator, who manages today's commits, brings them into `main` (a
  cherry-pick or `git am` of the branch). Nothing else edits
  `items/012-bergdb-c/`, so no conflict is expected; the index line in
  `items/readme.md` is the coordinator's.
* **Effort**: xhigh for steps 1 and 2 (exact bytes and texts), high for
  the rest; one agent at a time is enough, the steps being sequential but
  for step 4.


# 6. Decisions for Frans

Each has a default that goes ahead if Frans does not answer.

* **D1. Where.** (a) Update `items/012-bergdb-c/c/` in place, the 2026.2
  state kept by its commit, recorded in `c/readme.md`; 012's readme says
  "a port of release 2026.3", and the work is 012-19. (b) A new item with
  a copy of `c/` (its `src/` alone is 16,620 lines). (c) Another
  repository. Frans wrote on 2026-11-05 that a later release would most
  likely be another item or repository; his question of today names 012.
  **Default (a)**: one C clone, matching one release at a time, as
  015-02 already moved it from `main`'s Java to 2026.2.
* **D2. The C API.** (a) Remove `bergdb_options.retain_duration`, as Java
  removed the builder's from both layers: `bergdb_set_retain_duration`
  after the open is the one way, and it writes the settings; remove
  `BERGDB_SYNC_STRONG` as Java removed `STRONG`. (b) Keep the option, as
  a call of the setter after the open (it writes the settings at the
  first open only). **Default (a)**: C's API follows `Db`'s, as 012-03
  made it.
* **D3. The workloads' settings.** The header's `set retain` and
  `set fraction` are applied once, after the creation's start (as
  StreamDigest's `restarts-once`), where they were applied at every
  start. **Default: so.**
* **D4. The optional parts** (section 3.2). **Default**: 015-31, 015-68,
  015-70's test, the documentation, and the corrupt-stream set from
  2026.3's refusal tests in; the bounded sweep (015-67) and the limits
  harness out, each its own task if wanted; C's NOMEM refusal kept, as a
  departure.


# 7. Recommendation

**Do it now**: the coding today, unattended, in a clone, after Frans's D1
(or its default); the builds once 006-16's quiet block ends, and the long
runs (section 5.1, step 5) in a quiet block of F53 that the coordinator
plans, this afternoon after the timing ends at 13:00, or tonight.

Why:

* It is small and well bounded beside 012 itself: one format change, two
  byte changes with reclaim, and checks of damaged streams, against an
  oracle that compares every byte.
* C has real faults that 2026.3 fixed in Java: on damaged streams it
  aborts (019-32) or accepts what Java refuses (015-72, 019-01, 015-75 in
  part); 015-50 can fail a database at a huge value; and its reclaim
  settings are lost at a restart, the fault that 015-87 fixed. One gap is
  C's own (the switch force), worth closing whatever the release.
* The Core is stable after 2026.3 ("a bug-free Core"): 9 commits since,
  no format change, so the port stays current, and 2026.4's Core would be
  a small step.
* It restores what makes the clone useful: a second implementation that
  checks Java byte for byte at the current release. The port of 2026.2
  found seven faults of Java (005-69 to 005-75); 2026.3's new refusals and
  settings get the same second reading.
* The cost is mostly usage, plentiful today, and F53's time for about two
  hours of runs, which can wait for a quiet block.

Against it: Frans's words of 2026-11-05 that 012 stays a stable port of
2026.2 (D1); C is not used in production, so nothing waits for it; and
F53's quiet time is shared with 2026.4's work (020). If F53 cannot give
the runs a block this week, **later** is the alternative: the coding in a
clone now, the runs and the merge when F53 is free. Not doing it leaves C
as a port of 2026.2 whose reclaim differs from every later release.


# Log

2026-11-09. Created by c12 (Claude, Opus 5.5, Claude Code, effort xhigh),
started by coord-1109 at 09:39 at Frans's request of 09:38. A feasibility
study only: read the diff between `release-2026.2` and `release-2026.3`,
the release notes, and C's code and harness in `c/`; nothing built or run
(006-16's quiet block). No other file changed.
