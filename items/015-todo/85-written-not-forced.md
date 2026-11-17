015-85. Decide: a durability of "written, not forced"
=====================================================

Status: done (2026-11-05). Moved from 005-47 on 2026-11-05, with its
contents as they were in 005-47 (Frans's plan, approved 2026-11-05,
07:17). Decided by Frans 2026-11-04 (A, a setting) and implemented, see
"Frans's decision" and "Done"; the sync latency measured on s1 ("Sync
latency on s1") and on F53 ("Sync latency on F53", the second quiet block
of 2026-11-05). Holes in the unforced tail stay with 014-01 ("Left").
Kind: decide. Created 2026-10-26 as 005-47.

Frans's question, 2026-10-26, added as an entry at his request, by Claude
(Opus 5.5, Claude Code).


The question
------------

In Frans's words (2026-10-26): "Would the middle-ground be good to
support too? That is, ensuring the write left the process. This is a less
strong durability guarantee. Obviously. But still perhaps useful. With
replication for example, it is the total setup that counts."

The middle ground is between today's two: a commit that returns before
its bytes leave the process (no sync, NONE), and a sync that returns when
they are forced to the device (ORDINARY). "Written, not forced": the
bytes have been handed to the OS by `write()`.


Today: hard sync only
---------------------

* `FileStream.DbFile.append` (java/src/bergdb/stream/FileStream.java)
  writes and then forces the file (`io.forceFile`, which is
  `FileChannel.force(true)` in `FileStreamIo`: `F_FULLFSYNC` on macOS,
  `fsync` on Linux) before it returns. The class Javadoc's "Hard sync"
  paragraph says so (2026-10-26). `AppendOnlyStream.append`'s Javadoc makes it a contract:
  a persistent stream given to `StorageManager` must force the bytes, and
  any new file names, before `append` returns, as that completion
  advances the durable frontier.
* This came on 2026-10-14 (commit 2709e27,
  [docs/level3-durability.md](../011-docs-archive/07-level3-durability.md)). Before
  it, and in the 2013 to 2017 code, `FileStream` opened its files with
  mode `"rws"`, a synchronous write through the OS on every write, with
  no explicit force: on macOS that does not empty the drive's cache
  (docs/levels.md, Reclaim, small item c). So BergDB has never had a
  level of "written" only; the old code was between written and forced.
* A completed append is what `BufferedStream`'s append listener reports
  to `StorageManager` (`MyStorage.confirmedLength`). The main storage's
  confirmed length is d1Size, rule D1 (`MainConfirmedRule`), which
  `sync(ORDINARY)` waits for; STRONG waits for d2Size, rule D2
  (`OneActiveReplicaRule`): the main and one active replica. Reclaim cuts
  the stream only when `Db.getDurableLength()` (d1Size) has passed its
  decision (`Reclaim.java`, `pendingCutDurableAt`).
* What a force costs: on F53, `F_FULLFSYNC` of 100 bytes 4.2 to 5.2 ms,
  of 1 to 4 MB 7 to 12 ms (005-13, question 3); plain `fsync` there,
  which does not empty the drive's cache, 0.03 ms. On s1's virtual disk a
  force can take seconds: 1.4 to 2.7 s waits for a get and a commit
  (005-46, 009-03 section 4). There is one force per flush of the
  buffer, so a writer that does not sync pays little; a sync pays the
  buffer time (20 ms) plus one force, and readers of the last file wait
  for the force too (005-46).


What "written" gives
--------------------

* Bytes handed to the OS survive a crash of the process: the OS writes
  them out later, and a restart reads them from its cache or the disk.
  They do not survive a crash of the OS or a power loss: the OS may not
  have written them yet (on Linux the writeback of dirty pages runs about
  every 5 s and writes pages older than about 30 s; macOS has its own
  rules).
* Crashes of the process (a bug, an `OutOfMemoryError`, a kill, a
  restart of the service) are much more common than OS crashes and power
  losses, mostly on servers with a UPS.
* Other systems make this trade, many by default:
  * RocksDB: a write goes to the WAL with `write()` and returns; only
    `WriteOptions.sync = true` forces it. The default survives a crash of
    the process, not of the machine
    ([Basic operations](https://github.com/facebook/rocksdb/wiki/Basic-Operations#synchronous-writes)).
  * SQLite, WAL mode with `synchronous=NORMAL`: a commit is written to the
    WAL and not synced; the WAL is synced at checkpoints. A power loss can
    roll back the last commits but never corrupts the database
    ([PRAGMA synchronous](https://www.sqlite.org/pragma.html#pragma_synchronous)).
  * Kafka: by default the broker does not force per message (the
    `log.flush.interval.*` settings are off) and relies on replication,
    `acks=all` with `min.insync.replicas`, for durability
    ([broker configs](https://kafka.apache.org/documentation/#brokerconfigs_log.flush.interval.messages)).
  * PostgreSQL: `synchronous_commit = remote_write` waits until the
    standby has written the commit to its OS, not flushed it (005-11,
    "Elsewhere").
* With replication across machines, failures are mostly independent: a
  transaction written on two machines is lost only if both lose power or
  crash their OS before the writeback. That is Frans's point: the total
  setup counts. Today, though, BergDB has no replica on another machine;
  a replica is a stream in the same process, often on the same disk
  (005-11: "a copy on another machine, the code does not do").


The design rule
---------------

From 005-13 (Frans, 2026-10-20): `sync(level)` is the general, high-level
interface, and the storage layer defines what a level means, by medium,
replication and so on. A storage could be over a network. The options are
read against that rule.


Options
-------

**A. A property of the storage (recommended).** `FileStream` gets a
setting, per-append forcing on (the default, today's behaviour) or off.
With it off, `DbFile.append` writes and returns, and the storage's
confirmed length means "written". Nothing above the stream changes: D1
and D2 combine storages as today, and the levels keep their names. A main
storage with forcing off makes ORDINARY "written on the main"; a main
with forcing on and a replica with it off makes STRONG "forced here and
written there"; with a network replica (not there today) "written on two
machines" is STRONG with both off.

* The forces that must stay with it off (see "Constraints"): a new file
  and its directory entry, the old file's tail when the stream moves to
  a new file, and the stream before reclaim's cut and before file
  deletes. Add: a force at `close()`, so a clean stop is durable. Perhaps:
  a force at an interval (say every second), which bounds what a power
  loss costs, as SQLite's checkpoints do.
* Where the setting goes: `FileStream`'s constructor (the core API passes
  a stream to `DbBuilder.stream`); the Pub API's `DatabaseBuilderImp`
  and `DatabaseImp.addReplica` make their `FileStream`s themselves, so
  the Pub API needs a setting per storage too, a small API decision as
  the buffer time per storage in 005-13 (with 005-05).
* `AppendOnlyStream.append`'s contract changes: the storage says what its
  completion means, forced or written.
* Pros: follows the design rule; small and local, most of it in
  `FileStream`; no new level, no change in `StorageManager`, the rules or
  the Pub API's `SyncLevel`; a sync with forcing off costs the buffer time
  and a `write()`, not a force (on s1, milliseconds instead of seconds);
  with forcing off, 005-46's readers no longer wait for a force on every
  append; less wear on flash.
* Cons: the choice is per storage, not per transaction: an application
  that wants some transactions forced and others not cannot have both on
  one storage. The meaning of ORDINARY depends on the setup, so the
  application must know how its storage was built. On F53 the gain in
  latency is small, as the buffer time dominates (005-13: sync p50 35 ms
  at 20 ms, against a force of 5 ms). And a power loss now costs the
  recent transactions that a sync reported durable, which needs the test
  in "Constraints".

**B. A new sync level between NONE and ORDINARY,** say `WRITTEN`. Each
storage reports two confirmed lengths, written and forced; `FileStream`
splits its append into the write and the force and reports each step;
`StorageManager` keeps a third durable length beside d1Size and d2Size,
with its lock, and the rules compute each level from the right length.

* It lines up with 005-46's second option, to write under the file's
  monitor and force outside it: the write and the force become two
  steps, and B reports both.
* Pros: the choice is per transaction, as PostgreSQL's
  `synchronous_commit` (`SET LOCAL`) and SQL Server's delayed durability
  are (005-11, "Elsewhere"); hard sync stays for those who ask for it; a
  WRITTEN sync costs the buffer time and a `write()`.
* Cons: more API (a level in the Pub API's `SyncLevel`, to be documented
  and kept); more rules, and their combinations grow: with replicas,
  which of written-here, forced-here, written-there, forced-there is
  STRONG, and is a new level needed for "written on two"? Every storage
  needs two lengths, also those where they are the same (memory, a
  network stream that only confirms). The forces stay on every flush, so
  the I/O cost and the forces' share of readers' waits (005-46) stay;
  only the waiting sync is faster. It goes against the design rule's
  spirit, that a level's meaning is the storage's: B puts the medium's
  steps into the levels.

**C. Do nothing.** Keep hard sync only. An application that wants less
calls no sync, and gets NONE: its commits leave the process within the
buffer time (20 ms) anyway, without a guarantee.

* Pros: no work, no new guarantees to test; one meaning of a sync,
  simple to explain.
* Cons: the cost of a force stays in every sync, seconds on slow disks;
  a setup with replication pays forces it may not need; no answer for
  "written on two machines" when a network replica comes.

Proposed: A, after 005-46, and with the hole test below first. Questions
for Frans: A, B or C? With A, a force at an interval, and at what
interval? Is the setting in the Pub API now, or only in the core API
until 005-05 and 005-11?


Constraints
-----------

* **"No force" cannot mean no forces at all.** A power loss with forcing
  off may cost the recent transactions, never the database. Forces that
  must stay, from today's code in `FileStream`:
  * `openForRw`: a new file is forced, and its directory
    (`io.forceFile`, `io.forceDirectory(dir)`), before it takes appends.
    Without it, a power loss can lose all the files' names after an
    acknowledged commit (docs/level3-durability.md, negative controls).
  * `pretruncate` and `deleteAllFiles`: a directory force after each
    delete, so that an older name never survives a newer one; a hole
    there makes `FileStream` refuse to open the database before recovery
    can read reclaim's table (docs/level3-durability.md, "Production
    changes"). New with forcing off: `pretruncate` must also force the
    last file before it deletes, since reclaim cuts when d1Size has passed
    its decision (`Reclaim.java`, `pendingCutDurableAt`), and with forcing
    off d1Size means written; a power loss would otherwise keep the cut
    and lose the table.
  * New with forcing off: `newFile` (through `reopenForReadOnly`) must
    force the old file before the new one takes appends. Today every
    append is forced, so the old file is complete; without it, a power
    loss can leave a short old file and a newer one, and `checkDbFiles`
    refuses a file before the last that is not a whole number of index
    units (`BadDirStateException`).
  * `createDirIfNeeded`: the directory forces stay.
* **Holes in the unforced tail: untested, and likely not handled.**
  Without a force after each append, the OS may write later pages before
  earlier ones, so a power loss can leave a hole: zeros (or, through
  `SalsaStream`, garbage) inside the tail, with later bytes intact.
  `FileStreamPowerLossTester` does not model this. Its images keep the
  forced bytes of each file (loss of the unforced tail), and after each
  `write` one image `partial_write` that keeps the first half of the
  unforced bytes (`previous + (current - previous) / 2`): a prefix, never
  a hole. Recovery (`RecoverableStream.recover`) walks the transaction
  headers from the last valid meta block to the end, and records have no
  checksum. So a hole may make the start fail (a header of zeros is a
  "Bad transaction size" `StreamFormatException`), or accept a
  transaction whose commit byte survived with zeros inside it; the
  nodes' 16-bit checksums (`NodeStream`, `StreamChecksumException`) then
  fail the database at a read or at the startup rerun. From the code;
  not reproduced. The window exists today too, for the one chunk between
  its write and its force (up to half the buffer, 5 MB); forcing off
  widens it to everything not forced. Recovery must take the valid
  prefix; if the test shows it does not, the fix is likely a checksum per
  record, a format change (as 005-40's versions).
* **005-46 first.** It changes the same code, `DbFile.append` and its
  monitor, and one of its options (the force outside the monitor) is
  half of B. Do 005-46, then this.
* **Replication is experimental** (005-11; Frans, 2026-10-25: kept for
  release 2026.1, documented as experimental). The case for A with a
  replica rests on a replica on another machine, which BergDB does not
  have. A for the main storage alone does not need 005-11; anything for
  replicas waits for its decision.


Done when
---------

* Frans has decided A, B or C.
* For A: the setting in `FileStream` (and the Pub API, as decided), with
  forcing on by default; the forces at a new file, a new file's
  predecessor, a cut, a delete and `close()`; `AppendOnlyStream`'s and
  `FileStream`'s Javadoc, and docs/levels.md ("Durable commits"), say what
  a confirmed length means with forcing off.
* `FileStreamPowerLossTester` has a mode without per-append forces, with
  images that have holes in the unforced tail, and its negative controls
  (no force at the switch to a new file, none before a cut) fail as they
  should; recovery takes the valid prefix in every image.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `level3.sh` passes
  (a change to the stream's durability); the sync latency is measured
  with forcing on and off, on F53 and on s1 (`Perf`'s `d-1k-t1`).


First step
----------

A hole mode in `FileStreamPowerLossTester`, on a scratch clone, against
today's code: images where a later part of a written chunk survives and
an earlier part is zeros. It tells what recovery does with a hole, which
matters for today's one-chunk window as well as for A and B.


Size and order
--------------

S to M for A if recovery takes the valid prefix: the setting and the
forces are small, most of it is the power-loss tester's new mode and the
gates. M to L if it needs a checksum per record. B is M or more, through
`StorageManager`, the rules and the API. After 005-46; the replica side
after 005-11.


Follow-up: tail-hole experiment
-------------------------------

2026-11-02. The proposed hole experiment has been run with today's
per-append forces still enabled, as 005-83, "Power-loss tail experiment".
All 56 truncated-prefix or undamaged controls recover, while all 56
hole images fail the readable-prefix oracle at startup or a later read.
Every admissible image preserves the already-forced prefix and durable
names; these are modeled persistence images, not physical power cycles.
The one-unforced-write concern above is therefore reproduced in the
tested fault model. The new durability mode remains unimplemented; a
hole-tolerant recovery design is open before either mode changes. On
2026-11-03 the correction/contract investigation moved from 005-83 to
014-01; the experiment and evidence remain at their original location.


Frans's decision
----------------

2026-11-04. Frans: "Use A, a setting. No force at an interval. Nothing in
the Pub API for now."

* **A, a setting.** Per-append forcing is a setting of the storage,
  `FileStream`: on, the default and today's behaviour, or off. With it
  off, `DbFile.append` writes and returns, and the storage's confirmed
  length means written, not forced.
* **No force at an interval.** With forcing off, what a power loss costs
  is bounded only by the forces that stay, not by a time.
* **Nothing in the Pub API for now.** The setting is in the core API
  only, `FileStream`'s constructor; `DatabaseBuilderImp` keeps forcing on.

Replication was removed the same day (005-11, "A with C2 now"), so what
the options say about replicas, D2 and STRONG no longer applies: the
setting concerns the one storage, and ORDINARY is the only sync that
waits.


Done
----

2026-11-04, by Claude (Opus 5.5, Claude Code), at Frans's request.

* **The setting.** `new FileStream(dir, forceAppends)`, and for tests
  `FileStream(dir, io, forceAppends)`; `forcesAppends()` tells which.
  `FileStream(dir)` and `FileStream(dir, io)` force every append, as
  before, and so does the Pub API. Off, `DbFile.append` writes with
  `write()` (RandomAccessFile, no buffer in Java) and returns: its
  completion, the confirmed length that `BufferedStream` reports, the
  durable length and a returned `sync(ORDINARY)` mean written.
* **The forces that stay.** Each `DbFile` keeps its forced length, under
  its monitor, so a force is made only for bytes not yet forced: with
  forcing on, none of the new ones ever finds any, and the forces are
  today's.
  * `openForRw`: a file opened for appends, and the directory, before the
    file takes appends; as before.
  * `newFile`: the old last file, before the new file is opened. A power
    loss then cannot leave a short file before a newer one, which
    `checkDbFiles` refuses.
  * The cut's thread, `runCuts`: before each delete, the last file, if it
    starts before the stream's length at the cut (`cutForceTo`). Every
    file before the last is forced by `newFile`, so reclaim's decision,
    which the cut waits for (`Reclaim.java`, `pendingCutDurableAt`), is on
    the device before a file goes. `pretruncate` still returns at once
    (005-46); the directory force after each delete stays.
  * `close()`: the last file, unless the stream has failed, so that a
    clean stop is durable; a second `close()` finds nothing to force.
  * `deleteAllFiles` (`seekFirstPos`) removes the whole stream, so it
    needs no force of the data before it.
* **A reason for each force.** `FileStreamIo.forceFile(file, handle,
  why)`, with `FileStreamIo.Force`: APPEND, OPEN, SWITCH, CUT and CLOSE.
  It calls the two-argument `forceFile`, which stays the physical force,
  so the existing test boundaries are unchanged; a test can count the
  forces by reason or leave one kind out.
* **A crash of the process loses nothing written.** An append returns
  after `write()`; the bytes, the file's length and its name are the OS's,
  and a crash of the process alone keeps them. Nothing in the change
  weakens that.
* **Javadoc.** `AppendOnlyStream.append`: the completion advances the
  durable length, and the storage says what it means, forced or written.
  `FileStream`'s class Javadoc and its new constructor: both modes, the
  forces that stay, and the limit below. `Db.stop()`: with forcing off,
  the close forces.
* **docs/levels.md**, section 8: the setting, in the core API only; what a
  sync means with it off; the forces; the limit; `PowerLossTest`.
* **Unit tests**, in `FileStream`: `testForcingOnForcesEveryAppend` (the
  default; one force per append, none of SWITCH, CUT or CLOSE),
  `testForcingOffWritesAppends` (no append forced, the bytes in the file
  and readable), `testForcingOffForcesTheFileBeforeANewFile` (the old file
  forced, whole, before the new one is opened),
  `testForcingOffForcesBeforeACutDeletes` (the last file forced before the
  first delete, once; a cut with nothing unforced forces nothing),
  `testForcingOffForcesAtClose` (the force at close, none at a second
  close, the bytes after a restart). In `FileStreamPowerLossTester`:
  `testProcessCrashKeepsWhatWasWritten` (a synced commit, the files copied
  while the database runs, as a crash of the process leaves them, a new
  database on the copy finds it).
* **The power-loss tester without per-append forces.**
  `FileStreamPowerLossTester.runTraceWithoutAppendForces` runs the trace
  on a `FileStream` with forcing off. An image keeps what was acknowledged
  when the last file force began, not at the last sync, since a sync no
  longer forces. Its images also have holes (`hole_write`): after each
  write, the whole file with a random 4,096-byte page of the unforced tail
  zeroed, later bytes intact (in a tail too short for a page, its middle
  third); at most 4 per `perEvent`, by reservoir sampling, and a hole that
  changes no byte is not kept. Every image without a hole must recover,
  and so must one after `close()` with all that was acknowledged; the hole
  images are counted, recovered or failed, and do not fail the run. The
  trace must have made no APPEND force and at least one SWITCH, CUT and
  CLOSE force. f-tests: `testColdRecoveryWithoutAppendForces` (seed 17,
  exhaustive) and `testWeakenedForcesWithoutAppendForcesAreDetected`, the
  negative controls, no SWITCH force and no CUT force, both caught: the
  first by `checkDbFiles` ("Bad size of file ... should have been a
  multiple of 100000"), the second by a read below the first position at
  the start. `PowerLossTest`, in `level3.sh`, runs each seed in both modes
  and the four negative controls, and its line counts the hole images.
* **The oracle and an empty stream.** With forcing off, the images before
  the first force of a file with bytes (a switch, a cut or a close) have no
  stream byte, and a start makes a new database. The oracle took it for a
  lost history, in 14 of 24 runs of seeds 1 to 8, before it was taught
  that; such an image must have nothing acknowledged. The same holds for a
  real database: with forcing off, a power loss before the first such force
  loses the database's creation too, and the next start makes a new one,
  with a new ID unless the builder gives one. The Pub API, whose start
  refuses a directory that held a database and has no stream byte (015-01),
  forces.
* **Perf.** `-Dperf.noforce=1` (through `JFLAGS` in `performance.sh`)
  makes Perf's `FileStream` without per-append forces; in the workload ID
  only when given.
* **Gates**, on `bd77904` (005-11's removal) with this change:
  `java/before-commit.sh` printed `BEFORE COMMIT OK` (unit 1133, f 81
  tests); `java/stress/level3.sh` (full) printed `LEVEL 3 OK`, with
  PowerLossTest's line: "8 seeds, 440 cold recoveries; without per-append
  forces 448, and of 96 hole images 0 recovered, 96 failed (a known limit,
  bergdb 014-01); negative controls caught". Conformance: 25 traces, C-CUT
  0 of 305; InterruptStress 60 s.



Sync latency on s1
------------------

2026-11-04, 19:12 to 19:17, by Claude (Opus 5.5, Claude Code). s1 was
idle before (load 0.06, no JVM), and each run checked that no other JVM
ran. The jar of `9b67a82`, built on s1 from `git archive` with its
OpenJDK 27 (`/opt/bergdb-bench/jdk-27`; s1 has no `unzip`, so a Python
shim for `build.sh` in `/opt/bergdb-bench/005-47/bin`). `d-1k-t1` of
`performance.suite` run directly by `/opt/bergdb-bench/005-47/run.sh`:
`Perf write` with n=100000, valsize=1000, commit=durable, threads=1,
ops=100, warmup=100000, G1, a heap of 1 GB, assertions off; forcing on
and off (`-Dperf.noforce=1`) in turns, 10 runs each, 5 s apart. Every run
printed `PERF OK`. Outputs on s1 in `/opt/bergdb-bench/005-47/out/` and
`runs.txt`.

The durable commit's latency (execute() then sync(ORDINARY)), in ms: the
median of the 10 runs' p50 and p99, and the range of their maximum. The
append is Perf's time of an append to `FileStream` (Perf calls it a force;
with forcing off it is the `write()`).

| Forcing | p50 | p99  | max         | append             |
|---|---:|---:|---|---|
| on      | 4.2 | 12.3 | 13.8 to 39.0 | 4.5 (4.1 to 7.1) |
| off     | 0.1 | 1.1  | 1.0 to 3.2   | 0.01 to 0.03     |

* Forcing off takes the force out of a sync: a durable commit of 1 KB on
  s1 goes from 4.2 to 0.1 ms at the median, and from 12.3 to 1.1 ms at
  p99. A run's commits a second, in Perf's line of its appends, are 134 to
  226 with forcing on and 2,862 to 9,503 with it off.
* s1's forces were short this time, 4 to 7 ms; 005-46 and 009-03,
  section 4, saw waits of seconds there. The gain where a force takes
  seconds is larger, and not measured here.
* One thread and 100 commits a run, as the scenario has it; 16 and 64
  threads (`d-1k-t16`, `d-1k-t64`) not run.


Sync latency on F53
-------------------

2026-11-05, 08:08:51 to 08:11:47, in the coordinator's second quiet block
of the morning (`/Users/f/fl/bench/quiet-block-2026-11-05-2/block.sh`, a
copy of the first block's script with the limit 08:08; its log
`block.log` there). The block's marker was up from 08:00:48, the other
sessions held their builds, and macOS's `mediaanalysisd` was paused at
Frans's word (07:32) for the block, 08:00:48 to 08:31:41. Not quite
quiet: at the limit the 1-minute load was 1.77 (the block's rule: quiet
is below 1.5 twice; below 2.0 it runs, recorded as not quiet), with no
other JVM or gate. The loop of "Left" in the clone at `9b67a82`
(`/Users/f/fl/bench/005-47-f53-2026-11-05/clone/java`), OpenJDK 27,
forcing on and off in turns, 10 runs each, 5 s apart; every run printed
`PERF OK`. Full outputs in `/Users/f/fl/bench/005-47-f53-2026-11-05/out/`,
the summary lines in its `runs.txt`.

As for s1: the median of the 10 runs' p50 and p99, and the range of their
maximum, in ms; the append as Perf times it (the force with forcing on,
the `write()` with it off).

| Forcing | p50 | p99 | max         | append              | commits a second |
|---|---:|---:|---|---|---|
| on      | 4.5 | 6.0 | 5.7 to 14.9 | 4.66 (4.46 to 4.72) | 205 to 220       |
| off     | 0.0 | 0.1 | 0.1 to 0.2  | 0.01                | 16,547 to 18,925 |

* On F53 a force (`F_FULLFSYNC`) of a 1,243-byte append takes about
  4.7 ms, as 005-13 found (4.2 to 5.2 ms for 100 bytes), and it is nearly
  all of a durable commit's time: with forcing off the commit takes under
  0.1 ms at p99, about 80 times more commits a second with one thread.
* F53's forces are steadier than s1's (p99 6.0 against 12.3 ms with
  forcing on); with forcing off both machines are under about 1 ms.
* One thread, 100 commits a run, as on s1.


Left
----

* **Holes in the unforced tail: a known limit, 014-01's.** With forcing
  off, a power loss or a crash of the OS can leave a hole in the unforced
  tail, and recovery does not handle it (005-83: all 56 hole images
  failed; here, in level3.sh, all 96 hole images failed, at the start or
  at a read). The database may then refuse to start or fail reads, which is
  more than a loss of its last transactions. "Done when"'s "recovery takes
  the valid prefix in every image" holds for every image without a hole,
  not for these; hole-tolerant recovery is open in 014-01. Said in
  `FileStream`'s Javadoc and docs/levels.md, section 8.
* **The sync latency on F53**, with forcing on and off, in a quiet block
  (not measured on 2026-11-04: the 005-52 agent's gates and timing runs
  had the machine). The same runs as on s1, in a clone at `9b67a82` or
  later, from its `java/`, after `JAVA_HOME=/opt/homebrew/opt/openjdk
  ./build.sh`:

      for i in 1 2 3 4 5 6 7 8 9 10; do for x in "" -Dperf.noforce=1; do
        rm -rf build/perf/d47 build/perf/d47-out; mkdir -p build/perf/d47-out
        $JAVA_HOME/bin/java -XX:+UseG1GC -da -Xms1g -Xmx1g $x \
          -Dperf.n=100000 -Dperf.valsize=1000 -Dperf.commit=durable \
          -Dperf.threads=1 -Dperf.ops=100 -Dperf.warmup=100000 \
          -Dperf.scenario=d-1k-t1 -Dperf.out=build/perf/d47-out \
          -Dperf.dir=build/perf/d47 -cp build/bergdb.jar:build/stress \
          bergdb.core.Perf write | grep -E 'durable p50|forces,|PERF OK'
        sleep 5; done; done

  About 4 minutes. Then the table above for F53, and this entry done.

  **2026-11-05: not run, F53 not quiet.** The quiet block of the morning,
  by Claude (Opus 5.5, Claude Code): the marker
  `/Users/f/fl/bench/coord/2026-11-05/QUIET-BLOCK` from 07:22, then a
  wait for quiet (the 1-minute load below 1.5 in two checks 30 s apart,
  no other JVM or gate) until 07:55, the limit set for the block. macOS's
  `mediaanalysisd`, at 51 to 146 percent of a core in the block's
  samples, was paused by the coordinator at Frans's word from 07:32:35
  to 07:56:17 (`kill -STOP`, then `-CONT`; launchd then started a new
  one). The load still stayed up: from 07:33 to 07:55 the 1-minute load
  was 1.33 to 3.11, below 1.5 only at 07:34:52, 07:47:56 and 07:48:56,
  never twice in a row (VS Code's peaks of about 80 percent; from 07:50
  another session's C build, `clang` and `ld`). At 07:55:59 it was 3.02,
  not below 2, so both of the block's runs were skipped, as the block's
  rule says. Nothing ran; nothing to compare with s1.

  Ready for the next quiet block: the clone at `9b67a82`, built
  (`build/bergdb.jar` and `build/stress`), in
  `/Users/f/fl/bench/005-47-f53-2026-11-05/clone/java`, so the loop above
  can run there without `build.sh`; and the block's script
  `/Users/f/fl/bench/quiet-block-2026-11-05/block.sh`, which waits for
  quiet, runs this loop (each run's full output in
  `005-47-f53-2026-11-05/out/`, the summary lines in its `runs.txt`) and
  then 005-65's AB/BA step, with its log `block.log`; the time limit in
  it (07:55) is to be changed for another block.

  **2026-11-05, 08:08 to 08:12: run** in the second quiet block; see
  "Sync latency on F53". With it the entry is done.
