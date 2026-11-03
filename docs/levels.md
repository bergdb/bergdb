# BergDB feature levels: what works

The current state of BergDB, level by level: what each level does, how the
Java code does it, what checks it, its limits, and where the evidence is.
This file is kept up to date; the evidence and the history are in the
items, cited by their IDs. Until 2026-10-26 this file also held its history
(drafts 1 to 8, the reviews of 13 and 14 October, the measurements, the
bugs found and fixed): that text is
[011-04](../items/011-docs-archive/04-levels.md), where the code and the
items cite its sections (W1, "Level 3 cost" and so on). [log.md](log.md) is
the dated log.

The sections are numbered, and a number is not reused: "levels.md, 6" stays
Level 3.


## 1. Levels

| Level | Features | Status, 2026-10-26 | Evidence |
|---|---|---|---|
| 0 | Multiversion map in memory: puts, deletes, latest and historical lookups, scans; no restart | Passes the tests run | 011-04, "Evidence" |
| 1 | + restart by replaying the whole stream | Passes the tests run | `level1.sh`; 011-04, "The level 1 bugs" |
| 2 | + bounded startup: startup reads only the tail of the stream | Passes the tests run, also under load and with crashes; aligned with the proved Lean model | [011-11](../items/011-docs-archive/11-level2-alignment.md); 011-04, "Level 2 under load", "Bounds, measured", "Crash tests" |
| 3 | + reclaim: cut the front of the stream | Passes the tests run, a two-hour disk soak and the power-loss ordering checks; aligned with the proved Lean model of reclaim | [001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), [001-09](../items/001-lean-model-levels-3-4/09-level3-soak.md), [011-07](../items/011-docs-archive/07-level3-durability.md); 011-04, "Level 3 cost" |
| 4 | + eviction: data larger than memory | Passes the tests run; on by default; with handles since 2026-10-26, eviction in bounded steps, without a stop-the-world of its own; a database six times its memory budget runs on disk; aligned with the proved Lean model, with handles | [009-05](../items/009-handles/05-handles-alignment.md), [001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), [001-10](../items/001-lean-model-levels-3-4/10-level4-evidence.md), [009-03](../items/009-handles/03-measurements.md) |

Each level includes the ones before it; Level 3 needs Level 2, as startup
cannot replay a stream whose front is cut. Replication is in no level
(section 9). What BergDB is to do, the requirements R1 to R7 and the
invariants INV-LOOKUP, INV-RESTART, INV-CRASH, INV-RECLAIM and INV-EVICT,
is the problem statement, [011-01](../items/011-docs-archive/01-problem.md);
its design principles are [010-01](../items/010-principles/01-principles.md).
The Lean proofs concern the abstract model, which includes reclaim and
eviction; Java's runs are checked against it, not proved, and concurrency
and resource bounds are not in it.


## 2. Checks

* `java/before-commit.sh`, the unit tests and the f-tests (about 2
  minutes), must print `BEFORE COMMIT OK` before a change to the Java code is
  committed. Since 2026-10-20 it is the only requirement (006-03).
* The level scripts in `java/stress/` are deeper checks, run after larger
  changes; each prints `LEVEL n OK`, and its header lists its steps.
  `level2.sh` to `level4.sh` need Lean (elan) for their conformance steps.
  * `level1.sh`: the unit tests, DagFuzz, RestartStress with restarts by
    full replay, RestartInvariance (the same stream, byte for byte, with and
    without restarts: T2), and the Props limits (MEM and SS).
  * `level2.sh`: RestartStress with bounded startup in random
    configurations, RestartInvariance, CrashTest (INV-CRASH), BryanRepro
    (the bug report ISSUE151111 of November 2015), and the conformance with
    the Lean model: A2A3Check2, and the trace checker on the small set.
  * `level3.sh`: the unit and f-tests, ReclaimStress, RestartInvariance and
    CrashTest with reclaim, ReclaimReaders (readers while cuts are made),
    LoadTest with reclaim (full only), PowerLossTest, and the conformance
    with reclaim.
  * `level4.sh`: the eviction tests, EvictionInvariance (the same stream
    and answers with every eviction schedule), RestartInvariance, CrashTest
    and ReclaimStress under eviction, ReclaimReaders, `conformance.sh evict`
    (C-P and C-H), and LargerThanMemory, on disk in a capped JVM.
* `java/night.sh` runs at 02:10 on a clone of the committed code: the check
  before a commit, the Core Layer built alone (`stress/core-build.sh`), the
  four level scripts, the night tests and the medium conformance set. Its
  report is in `java/build/night/`.
* `cd lean && lake build` checks every proof of the model. The trace
  checker reads traces in the format of [trace-format.md](trace-format.md).


## 3. A transaction or a read that fails

Since 2026-10-22 (005-01) and 2026-10-23 (005-30). The design is Frans's,
from the start: no rollback of in-memory state, and a database whose
environment has failed, or that has a bug, does not run on.

* `Db.executeInner` has a go point. Before it, everything that may refuse
  the transaction is checked, and nothing is changed: the STM check
  (`RerunException`), the end of the top node ordinals (005-02), the size of
  the transaction (005-17), the index nodes it can make dirty (005-31) and
  the clock (005-18). The Pub API runs the application's code before it too.
  A refused transaction leaves the database as it was, and it goes on.
  The STM also refuses a read set whose snapshot predates the last
  recovered commit at startup: its in-memory write history cannot validate
  it (005-70). A snapshot at that commit is covered. RW read dependencies
  must be collected on the same running `Db` instance as the commit;
  after reopening, reread and recompute. Normally the reads are within
  about one second of the current time (guidance, not an enforced timeout;
  010-P2). The timestamp check does not establish the read set's origin.
* After the go point nothing refuses the transaction and nothing is undone.
  When something throws there (the environment or a bug: a read error or a
  corrupt node when a put loads an index node, an append error, an `Error`,
  reclaim's work after the transaction), the database fails
  (`DbState.FAILED`). The call throws a `DbFailedException` (an `Error` is
  thrown as it is), the transaction's time never becomes a lookup time,
  every later transaction and read throws a `DbFailedException` with the
  first failure as the cause, and nothing more is appended. `sync()` still
  works for the transactions before the failure, and so do `stop()` and
  `close()`.
* A read that fails on the storage fails the database in the same way: an
  I/O error, or corrupt data (a checksum or format error), in `getOne`,
  `getMany`, `getTrans` (`transactionInfo()`) and `sync()`. Not failures: a
  read that a cut has overtaken expires with a
  `LookupTimeNotAvailableException` (section 6), and so does `getTrans` of
  a transaction that reclaim has removed; the database goes on. A read or a
  sync while the database stops throws as it did.
* Interrupts (since 2026-10-27, 005-46): an interrupt never fails the
  database or hangs it. Three calls only wait, and an interrupt ends the
  wait: `sync()` throws a `StreamIoException` with an
  `InterruptedIOException` as its cause, and the transaction stays
  committed; a job's `join()` returns its status; the Pub API's wait to run
  a transaction again after a conflict throws a `DbException`, the
  transaction not run. Every other call ignores an interrupt until it is
  done, and BergDB's own threads go on when interrupted. The thread's
  interrupt flag stays set. Before, an interrupt failed the database in a
  commit that waited for room in the write buffer or made a physical cut,
  and hung it when it reached the storage thread (005-46, "Interrupts";
  `InterruptTester`, `InterruptStress` in `level3.sh`).
* The application restarts the database. The stream holds whole records
  only, so the restart rebuilds the state as after a crash at the failure:
  without the failed transaction, or with it if its record was appended
  before the failure (it is then committed, although the call threw). An
  in-memory database is lost, as in a crash. The Lean model needs no
  change: the stream after a failure is the stream of a run without the
  failed transaction, or with it.

The details, the tests, and what happened before 005-01: 011-04, "A
transaction or a read that fails".


## 4. Level 1: restart by full replay

A multiversion ordered map from (key, time) to value, with all data in
memory. The stream is a log of the user transactions, and startup replays
the whole log, so startup time and memory grow with the stream. It is what
the code does when the stream never grows past the startup distance: the
startup pos never moves, and no index node is ever written. To get it, set
the startup distance larger than the stream will ever be
(`DbBuilder.startupDistance()`; the Pub API allows up to 1000 MB).

It rests on the persistent Dag (INV-LOOKUP at every time, from the Dag
invariants of 2015-algos) and on replay determinism (rerunning the stored
transactions rebuilds the same Dag, with the same node ids); neither is
written down as a proof. Two bugs of the 2017 code were fixed on
2026-10-12: 011-04, "The level 1 bugs".


## 5. Level 2: bounded startup

The database as designed, the self-indexed stream: index nodes are written
lazily to the stream, and startup reads only the startup section, the tail
of the stream, and reruns the transactions in it. This is the default
(startup distance 50 MB). Existing databases keep the startup distance
stored in their stream; `Database.setStartupDistanceInMb` changes it while
the database runs, with one call, and the stream keeps the new value
(005-53).

Theory: [sis-model.md](sis-model.md), an abstract model with Rule A and
Rule R and the theorems T1 (recovery) and T2 (restart invariance), proved in
Lean ([../lean/](../lean/README.md)), with BergDB's bookkeeping and its
virtual root, and with the physical layer of lazy reading (lemma M, T1-L,
CC, T2-L). They prove the model, not the Java code.

How it works in Java:

* Each commit writes index nodes of D, the dirty set, in whole
  transactions, oldest first (`TransSeq.take`): its share of D, in
  proportion to the stream it adds, so that the startup section stays near
  the startup distance's setting, its target size; and, the deadline,
  every transaction that begins twice the setting or more before the end
  of the stream (005-49; 007-03, step 3). After a decrease of the setting,
  the share follows the new setting at once, and while the section's
  transactions span more than twice the new setting, the deadline is at
  that span, which shrinks with every commit, instead of writing what lies
  past twice the new setting at once (007-03, D4; 007-07). D is what
  startup rebuilds.
* One canonical object per index node: the one that holds the node's whole
  history and can change. The writer, D and the still-dirty test (Rule A)
  use canonical objects only, and decide by node id, never by whether a
  pointer is in memory or in the stream.
* Nodes are read lazily, at a pointer's first touch: the canonical object,
  or exactly the version the pointer names after Rule R. Lemma M says why
  that is enough: a newer version serves every time an older one serves.
  Since item 009 a pointer reaches its node through a handle (section 7).
* Startup (`DbStarter`): Rule R from the startup section by node id; the
  super root at the startup time from the last record's topPos (record
  format 5); the rerun of the section's transactions; D rebuilt from the
  stored got-dirty ids, and its pointers linked to the canonical objects
  (rule 4). Rule 4 finds a pointer's node by its position, without reading
  the stream: by the section's versions and the versions before them, or
  the canonical objects' positions; before 005-57 it read a header for each
  pointer, most of a cold startup. The Lean model proves, for its startup,
  that this links what rule 4 by node id links (005-58, `Rule4Pos_handles`),
  also after a safe cut, where Java skips the pointers below the stream's first
  position (005-62, `Rule4PosCut_handles`). A cold start still reads the nodes on
  the rerun's paths that have no version in the section: about 46 s on s1
  at 10M keys and a startup distance of 50 MB (005-57; 214 s before).
  Before replay it validates record order and the 56-bit range of record
  times in the startup section, and increasing times within its stored
  key nodes; violations are refused as stream format errors (005-75).
* Marking: the index nodes that an operation (a put or a delete) follows,
  creates or changes get dirty when the operation ends, and only if it
  changed something; a node that the transaction replaced leaves D at its
  end. These are the nodes that the model marks (T13).

Alignment: [011-11](../items/011-docs-archive/11-level2-alignment.md)
maps Java's state to the model's (section 2) and keeps the register of
where they differ. The trace checker runs the model's own `init` and `step`
on traces of Java runs: every transaction must be a step of the model with
its assumptions met (A2 to A5, TREE, A6', A-COPY), every restart invisible,
and every first touch after a restart must follow the model's rule (C-L).
`level2.sh` runs it on the small set, `night.sh` on the medium set.

Limits:

* The bound on the startup section is proved in Lean for a startup pos
  policy that keeps up with a distance (T3,
  [007-01](../items/007-bounds/01-startup-bound.md)), and for BergDB's own
  take, with any share (`T3_take`,
  [007-08](../items/007-bounds/08-step4-take-in-lean.md)): the section
  without its last record stays below twice the startup distance, and
  after a decrease of it, it never grows and shrinks with every commit
  until it is below twice the new one, by the deadline at the span
  ([007-03](../items/007-bounds/03-plan.md), step 3 and D4). The proof
  leaves out the record limit, which can stop a record from taking what is
  due. It leaves out the stream's meta blocks too, but they make no
  difference to the take: when it runs, the stream's length (`getLength()`)
  is where the new record begins (`getNextPos()`), as a meta block is written
  with the record that ends at its position
  ([005-68](../items/005-todo/68-fix-take-stream-length.md)). The model's
  take gives Java's startup pos on 300 generated cases. T3 is not all of
  bounded startup: the records at the ends of the section (T4) and a cold
  start's reads through references into older records are not bounded by a
  proof. The take's pace
  held the section at 1.00 to 1.14 times the startup distance in 005-49's
  runs with 10M and 50M keys, and in 007-06's and 007-07's with 10M keys,
  for updates, deletes and single puts, where the take before step 3 reached 2.75 times at 50 MB, 1.9
  times at 200 MB and 1.3 times at 1000 MB.
* A transaction whose dirty index nodes could not be written in one record
  is refused before its go point (005-31); larger updates must be split by
  the application, as a transaction of values over 7/8 of the record limit
  must (005-17).
* Write overhead: with uniform random updates of 10M keys in transactions
  of 1,000 puts, a put of a 24-byte key and an 8-byte value costs 867, 524
  and 190 bytes of stream at 50, 200 and 1000 MB, against 699, 384 and 219
  with the take before 007-03's step 3 in the same runs: 24 and 36
  percent more at 50 and 200 MB, since the section no longer goes past the
  startup distance, and 13 percent less at 1000 MB
  ([007-06](../items/007-bounds/06-debt-test.md), sections 1 and 4;
  [007-07](../items/007-bounds/07-step3-paced-take.md), section 10). Its
  own record is 68 bytes of it (005-38). With 50M keys it is measured only
  with the take before step 3: 1,013, 673 and 299 bytes (005-38).
* The largest record in those runs: 0.34 to 1.9 MB, against 2.6 to 4.6 MB
  with the take before step 3, and 0.23 to 0.29 MB with transactions of
  one put, against 0.73 to 0.96 MB (007-06, 007-07). A small commit after a
  large transaction can still write that transaction whole (007-07,
  sections 7.1 and 7.2). After a decrease of the startup distance,
  `setStartupDistance`'s own transaction, with the share of its 200 kB
  value, writes the largest record: 3.3 to 5.4 MB from 1000 to 100 MB and
  from 200 to 50 MB at 10M keys, where a deadline at twice the new
  distance at once wrote 87 to 486 MB in one record (007-07, section 10;
  007-06).
* The conservative still-dirty test writes index nodes that are no longer
  current: 20 to 46 percent of those written at 50 MB (011-04, "Bounds,
  measured").
* Argued, not proved (011-11): the mapping α itself; that Java's
  references are the latest versions (M5, checked on every record); the
  order within a record (M6, M9); bytes as a function of the stream (M10);
  the physical layer's assumptions (M47).


## 6. Level 3: reclaim

Reclaim cuts the front of the stream, so that the stream does not grow
forever. It is on when a retain duration R is set
(`DbBuilder.retainDuration`, `Db.setRetainDuration`); the default is to
retain forever, as since 2013. Lookups work for every time in [now - R,
now]; the first available lookup time is the API's actual frontier, and
increasing R cannot restore history already cut.

How it works (`Reclaim`; the class comment has the details):

* An iteration starts at an external transaction when the stream has grown
  by more than twice the startup distance since the last one started, and a
  quarter of R has passed (`ITERATION_SPACING`). pStart and tStart are the
  stream length and the time then; the cut point pCut is the previous
  iteration's pStart.
* Each external transaction allows a step while the bytes charged so far
  are below a quarter (`internalFraction`) of the stream's growth since
  pStart; the charge counts the value nodes rewritten and the index nodes
  made dirty. A step scans at most about 16 KB of KVs at tStart, with
  maintenance reads that swizzle nothing; in one internal transaction it
  touches its key range at the current time (making its index nodes dirty,
  also those of deleted keys) and rewrites each live value stored before
  pCut.
* When the scan ends, the iteration is done; tEnd and pEnd are the time and
  the position of its last step. The cut at pCut waits until tEnd is older
  than R, the startup pos has passed pEnd and then pSafe, and the last valid
  meta block names a transaction at pCut or later. Then the reclaim table
  records the cut, the first available lookup time becomes tEnd, and the
  physical cut waits until the table is durable.
* A read admitted before a cut may expire: a read that the cut overtakes
  throws `LookupTimeNotAvailableException`, and the database goes on
  (decision D1 = A, 2026-10-13; 011-04, W1). The retain duration may change
  while the database runs and at restarts; every cut keeps the guarantee of
  the duration in force when it was decided (011-04, W2).

Evidence: the Lean model of reclaim is proved (recovery, reads and restarts
after safe cuts) and Java's reclaim is aligned with it,
[001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md); a
two-hour soak on disk passes
([001-09](../items/001-lean-model-levels-3-4/09-level3-soak.md)); the
power-loss ordering of section 8; and the steps of `level3.sh`. The cost:
011-04, "Level 3 cost" and W4.

Limits:

* That Java's scheme gives safe cuts (T-SCHEME) is checked at every cut
  Java decides, not proved; the register rows M32, M33, M36, M41 and M48 of
  001-07 are argued or checked, not proved.
* Reclaim added 26 to 38 percent of all stream writes in the cells
  measured (011-04, W4), and in the grids of 2026-10-13 the stream kept was
  the retention window plus one or two iteration spans. The bound on the
  stream (R5, Q8) is measured, not derived (005-54).
* `FileStream` cuts whole files: the disk holds 6 to 9 percent more than the
  kept stream on average (011-04, W5d).
* Protected long-lived snapshots, which a cut would not overtake, are not
  built.


## 7. Level 4: eviction

Since 2026-10-18 the database keeps only part of its index and values in
memory: eviction is on by default. The budget is `cacheSizeInMb`
(`DbBuilder.cacheSizeIndicator`; by default a fifth of the JVM's maximum
heap); `DbBuilder.noEvict()` turns it off. `Database.setCacheSizeInMb`
(`Db.setCacheSizeIndicator`) changes it while the database runs, for that
run: after a decrease the call wakes the eviction thread, which evicts in
its batches until the resident bytes are at most the budget, also when no
other call follows (005-52).

How it works, with handles since 2026-10-26 (item
[009](../items/009-handles/readme.md); `dag/Handle.java`,
`core/Cache3.java`, `core/Eviction.java`, `core/Residents.java`). Until
then eviction unswizzled pointers and released what no resident pointer
named, with a sweep that walked every resident object (item 004).

* **Handles.** A memory pointer of a key node or a top node holds its
  pointee's handle; a pointer to a value holds the value. One live handle
  per index node, in the node table (4,096 maps, each its own lock), with
  the node's one object, canonical or a version read, or none. A pointer's
  reference (`pos[i]`) is what its record names: the record rule
  (`Handle.serializedRef`) takes a canonical object's position, else the
  newer of the reference and the position its dead handle's canonical
  object had when it was evicted.
* **What is in memory.** The objects of the live handles and the values
  that their pointers hold. `Residents` counts their bytes exactly, without
  walks: each object with its values, from when it enters a handle until it
  leaves it.
* **What is pinned** (never evicted): the super root, the canonical objects
  of D (the nodes dirty since the startup position) and of the record being
  written, and the newest written top node.
* **Evict.** The object leaves its handle, which dies (`Cache3.evict`):
  nothing asks which pointers hold it, and no record changes. A pointer
  that holds a dead handle is resolved again by the node's id; the slow
  path raises the pointer's reference to the dead handle's written position
  and writes it back. The values of a pinned leaf become stream pointers.
* **The capacity controller.** CLOCK over the node table: when the resident
  bytes pass the trigger (the budget, or the pinned bytes plus the gap
  between the watermarks if that is more), a batch of CLOCK steps runs, at
  most 2 ms, 4,096 handles (65,536 under pressure) and two rounds of the
  hand: in the writer at a transaction's end, and after a reader's load in
  the database's eviction thread, which takes the write lock between
  transactions and gives way to a waiting writer. A load that finds the
  resident bytes far over the trigger waits up to 2 ms for that thread.
* **Readers** follow a pointer without a lock when its handle holds an
  object that may serve it (`Handle.usable`): a plain read of a pointer to
  a handle, an acquire read of a pointer to a value (the barriers of
  009-02, section 3.4, and their jcstress tests, `java/stress/jcstress/`).
  Else the slow path reads the pointer under the node's monitor and loads
  under the handle's, so two readers do not read the same node; its swizzle
  is a compare-and-set, and its write-back of the reference only raises it.
* **Reclaim** reads with the maintenance follower, which loads but swizzles
  nothing; a step's dirty index nodes stay pinned until written, and a
  reserve (4 MiB) splits a step that would pin more.

Evidence: the Lean model proves that with any eviction schedule the
records, D and the answers are those without eviction (T-CACHE, T-READ,
T2-C, T-PIN; [001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md),
section 5), for handles (`tc_handles`, `tr_handles`, `t2_handles`,
`tr_handles_restarts`, `tp_handles`; the mapping and its register in
[009-05](../items/009-handles/05-handles-alignment.md)), also with reclaim's
cuts (`t9_handles`, `t12_handles`; 005-62, which removed the model and the
proofs of the design before handles). Java is checked
against it: the audit (INV-CAN, the pins, INV-SLOT; test-only), the
checker's C-P on Java's physical states and its C-H on Java's handle state
(`conformance.sh evict`; 009-05, section 4), and `EvictionInvariance`.
A database of 20 million keys, six times its memory budget, runs on disk
([001-10](../items/001-lean-model-levels-3-4/10-level4-evidence.md)).
Against release 2026.1
([009-03](../items/009-handles/03-measurements.md)): with ZGC the longest
get from the OS cache at 10M keys is 3.45 ms (7.3 s before), and the heap
holds 130 bytes per KV (191).

Limits:

* The pause target of item 009, about 20 ms for a get or a commit, is for
  BergDB's own code; the collector's pauses come on top (009-01, target 2).
  With G1 they reach hundreds of milliseconds under eviction, and full
  collections happen (004-04, 009-03). Use ZGC (pauses below 0.1 ms) or
  Shenandoah in its default mode, without generations (at most 4.1 ms in
  P4's soak with an 8 GB heap; not run at 10M keys; 009-04, section 7).
  Generational Shenandoah stopped for 821 ms in P4's soak with an 8 GB
  heap, its old generation full of garbage it had not reclaimed (009-04).
* No read waits for the stream's writer since 2026-10-27 (005-46): a read
  takes no lock (positional reads on a channel of the file's own, the list
  of files replaced, never changed), a new file is made outside the
  stream's monitor, and a cut's files are deleted by a thread of their own;
  an encrypted database's reads no longer wait for each other. Before, a
  read of the last file waited for the writer's append and its force,
  seconds on a slow disk, and every read for a new file's forces and a
  cut's deletes, up to 171 ms in P4's soak (009-04, section 7.3). On s1,
  under ZGC, the longest gets were the forces; since, a force of 2,500 ms
  left every get at 12.1 ms at most (005-46, "Measured after the change").
  In P4's soak under ZGC on F53 the longest read is 3.6 ms and the
  longest commit 5.1 ms, and the cuts are no longer the slowest (006-09's
  quiet block; 005-46, "Confirmed in the quiet block"). A writer that fills
  the write buffer still waits for the disk; that does not count against
  item 009's pause target (Frans, 2026-10-27), and the test reports show it
  apart.
* So the waits above 20 ms left in item 009's runs are not BergDB's own,
  but for one case: the collector's (G1's pauses; ZGC's allocation stalls,
  129 and 300 ms on s1 when its heap ran short), s1's disk (gets from the
  device of 64 to 74 ms, where single random reads take up to 58 ms, and
  one get of 2,760 ms under the kernel's memory reclaim;
  [009-03](../items/009-handles/03-measurements.md), section 9), and a
  writer's waits for room in the write buffer when the disk stalls. Item
  009's target 2 is met in P4's soak and the pause probe (009-01, section
  1). The case: in ScaleBench from the OS's cache on F53 with 8 readers at
  665 MB under ZGC, gets of 27 and 36 ms, with readers' loads waiting for
  the eviction thread over 10 ms (with 4 readers at most 6 ms; before
  005-46, 2.1 ms), not yet explained
  ([005-65](../items/005-todo/65-gets-with-8-readers.md)).
* Loads in memory, with no eviction, are 8 to 20 percent slower than before
  handles.
* D, which cannot be evicted, is bounded only loosely by the startup
  distance: its nodes' stream bytes reached 2.9 times the startup distance
  at 50 MB, 2.3 times at 200 MB and 1.6 times at 1000 MB, in runs with 10M
  and 50M keys (005-38); in memory they take more.


## 8. Durability

* `FileStream`, the file storage, forces every append to the device before
  the append returns (`FileChannel.force(true)`: `F_FULLFSYNC` on macOS,
  `fsync` on Linux), and a new file and its directory entry before the file
  takes appends. Its power-loss ordering (the file and directory forces, a
  force between the prefix removals of reclaim's cuts, the failures of
  deferred cuts passed on) is tested under a fault model, and native audits
  confirm `F_FULLFSYNC` on macOS/APFS and `fsync` in a Linux VM
  ([011-07](../items/011-docs-archive/07-level3-durability.md);
  `PowerLossTest` in `level3.sh`). Not established: physical power cycling,
  other storage providers and Windows, replication.
* Recovery tolerates the tested truncated prefixes of an unforced write,
  but holes in that write (later bytes surviving while earlier ones are
  missing) can refuse startup or fail a later read after startup succeeds.
  The experiment preserves every already-forced byte and name; recovery
  for this fault class is open (005-83, "Power-loss tail experiment").
* `BufferedStream`, above it, collects the database's appends and writes
  them in chunks from a thread of its own, when the buffer time (50 ms by
  default since 005-64; 20 ms from 005-13) has passed or its buffer is
  a quarter full: an append that reaches the quarter wakes the thread,
  which also continues without a timer wait when a flush leaves a quarter
  ready (005-76). One force per chunk, not one per transaction. `execute()` only
  appends to that buffer.
* `sync()` waits until the transaction's last byte, its commit byte, is
  durable (005-44). The transactions of many threads share one force: on
  F53, one thread that syncs after every transaction gets 29 durable
  commits a second (35 ms each), 64 threads about 1,800 (005-13).
* `stop()` returns at once, and the buffered transactions are written in
  the background; `close()` waits for them. Call `sync()` before `stop()`
  when the transactions must be durable when it returns.
  A failed final flush or storage close throws `StreamIoException` from
  `close()`, also after `stop()` or an earlier `close()` (005-73).
* An idle database does not wake: when nothing has been buffered for a
  buffer time, the storage thread waits for the next append (005-14).
* A physical cut only takes its files off the stream's list; a thread of
  the stream's own, which runs only while there is something to delete,
  deletes them in the same order, each followed by a directory force
  (005-46). A crash before it has deleted them leaves them, and the next
  start cuts again. A failed delete fails the stream at its next operation;
  the flushes before it, whose bytes are forced, stay acknowledged (Frans,
  2026-10-27), where until then a failed pending cut kept its flush from
  being acknowledged (011-07).
* Open: group commit (005-48), and a durability of "written, not forced"
  (005-47).


## 9. Replication

Replication is in no level, and no check of the levels has a replica. It is
experimental, with known faults (005-11; Frans, 2026-10-25: kept as it is
for release 2026.1, documented as experimental): with reclaim, a crash can
leave a replica that does not start or gives wrong answers; a replica whose
storage fails fails the database at reclaim's next cut; a start without a
replica that was ahead of the main mixes two histories; a replica is written
in plain text when the database is encrypted. The Javadoc of
`DatabaseBuilder.replica` and `Database.addReplica` lists them.


## 10. Open work

What is left to do is in the items, not here: the index of
[items/readme.md](../items/readme.md), the open entries of
[005-todo](../items/005-todo/readme.md), and bounded startup in
[007](../items/007-bounds/readme.md), the top priority since 2026-10-23.
Where BergDB departs from its design principles is in
[010-01](../items/010-principles/01-principles.md).
