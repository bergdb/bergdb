BergDB feature levels: what works
=================================

Draft 7, 2026-10-14. Originally written by Claude for Frans Lundberg.
Codex consolidated the independent review, added the validation plan and
implemented and tested FileStream power-loss ordering.
Draft 8, 2026-10-18 (bergdb item 001, by Claude): Level 4, eviction, in Java,
and Levels 3 and 4 aligned with the Lean model. Draft 1, 2026-10-12, tested
the 2017 code as is. Draft 3 added level 2 under load and
crash tests, and the four bugs they found. Draft 4 adds level 3, reclaim.
Draft 5 adds "Level 3 follow-up": readers and cuts, changes of the retain
duration, the removal of `Kv.time()`, the attribution of the stream bytes.

The current status of each level of the problem in
[problem.md](problem.md), in theory and in implementation. This is the
place for the status and for how level 2 works in the Java code;
[log.md](log.md) has the history.

Historical reviewed status: committed snapshot `ebe5f77`, 2026-10-13 18:02 CEST.
This includes index-aware reclaim budgeting and the 16 KB scan target.
The "Level 3 follow-up" section describes the evening's completed W1–W5
plan (in Git at `5650ed7`); earlier sections retain their baseline scope.
The initial documentation review checked existing logs rather than running
Java again. Earlier measurements are labeled by reclaim version; they must
not be read as final tuned performance. The table and "Next" now include the
14 October validation plan.

"Independent review, 13 October" below records the later Lean and full
Level 1–3 gates, the reviewed source manifest, and further copy/oracle/test
repairs committed in `0319caf`. It supersedes the earlier follow-up gate
snapshot; performance measurements retain their stated versions. The next
[Level 3 plan](level3-plan.md) covers power loss, a longer disk soak and a
reproducible performance reference before Level 4. Task 1 results are below;
the soak and performance reference remain pending. Java gates were rerun for
the storage work; the abstract Lean model is unchanged.


Power-loss ordering, 14 October
-------------------------------

The current FileStream ordering work is in
[level3-durability.md](level3-durability.md): explicit file and namespace forces,
a force between prefix removals, propagated deferred-cut failures, and handle
cleanup after errors. The fault model separates readable/forced bytes and
persistent names; omitted forces and unordered deletions are negative controls.
Native audits confirm F_FULLFSYNC on the tested macOS/APFS JDK and fsync in the
Linux VM. Physical power cycling, other providers/Windows and replication are
not established by these checks. Final gate results are recorded in that report.
The longer soak and performance reference of [level3-plan.md](level3-plan.md)
remain pending. Earlier sections retain their historical source scopes.


Levels
======

| Level | Features | Status, 2026-10-18 |
|---|---|---|
| 0 | Multiversion map in memory: puts, deletes, latest and historical lookups, scans; no restart | Passes the tests run |
| 1 | + restart by replaying the whole stream | Passes the tests run; two bugs fixed |
| 2 | + bounded startup: the startup pos moves, startup reads only the tail | Works in all tests run, also under load and with crashes; the defects of the 2017 code fixed; aligned with the Lean model, which is proven (2026-10-16, F1-008-11) |
| 3 | + reclaim: cut the front of the stream | Passes the recorded exact-cut, restart, crash, load, concurrent-reader and changing-retention tests; infinite retention is the default, finite retention schedules reclaim; retention pacing, older cut point, index-aware allowance and 16 KB scan target implemented; an overtaken read may expire without harming the database; FileStream power-loss ordering is implemented and audited on the tested platforms; the Lean model of reclaim is proved (2026-10-18, bergdb item 001: recovery, reads and restarts after safe cuts; that Java's scheme gives safe cuts is checked at every cut, not proved), and Java's reclaim is aligned with it, a step of `level3.sh` ([level3-alignment.md](level3-alignment.md)); a two-hour disk soak passes ([level3-soak.md](level3-soak.md)) |
| 4 | + eviction: data larger than memory | Works in all tests run, on by default (2026-10-18, bergdb item 001): values and index nodes evicted under a capacity controller whose budget is `cacheSizeInMb`; a database six times the budget, its index three times, runs on disk in a capped JVM ([level4-evidence.md](level4-evidence.md)); within the item's performance targets against Level 3 ([level4-performance.md](level4-performance.md)); the Lean model with eviction is proved (any eviction schedule gives the model's records, D and answers), and Java is checked against it ([level4-alignment.md](level4-alignment.md)); `level4.sh` |

Level 3 needs level 2: once the front of the stream is cut, startup can no
longer replay from the beginning.

Checks of the levels:
[level1.sh](../java/stress/level1.sh),
[level2.sh](../java/stress/level2.sh),
[level3.sh](../java/stress/level3.sh) and, since 2026-10-18 (bergdb item
001, K4), [level4.sh](../java/stress/level4.sh). Until 2026-10-20 all four
had to pass before a change to the code was committed; since then the only
requirement is [before-commit.sh](../java/before-commit.sh), the unit tests
and the f-tests (bergdb 006-03). They print `LEVEL 1 OK`,
`LEVEL 2 OK`, `LEVEL 3 OK` and `LEVEL 4 OK`. Runtime depends on the cost of the storage
forces; the old pre-force timing estimates no longer describe these runs.

Since 2026-10-18 (bergdb item 001, WP J9), [level4.sh](../java/stress/level4.sh)
checks Level 4, eviction, and prints `LEVEL 4 OK`: the unit tests (quick: the
eviction tests); `EvictionInvariance`, the same transactions with every
eviction schedule (none, values, every, random, and the capacity controller
with a small budget) giving the same stream byte for byte, the same D and
right answers, on three configurations quick and nine full, with and
without restarts and reclaim, the audit (INV-CAN, the pins, INV-SLOT) on;
`RestartInvariance`, `CrashTest` and `ReclaimStress` with the schedules every
and random and the audit; `ReclaimReaders` with forced schedules, on a
`CutStream` and a `FileStream`; `conformance.sh evict`, the checker's C-P on
Java's physical states (so it needs Lean too); and `LargerThanMemory`, on disk
in a capped JVM (quick: 500,000 keys, a budget of 20 MB, `-Xmx384m`; full: 2
million keys, 50 MB, `-Xmx768m`). It takes about 16 minutes full and 4
quick.

`level2.sh` also runs [BryanRepro.java](../java/stress/BryanRepro.java), the
program attached to a bug report of November 2015 (ISSUE151111): start,
delete all objects, create 10,000, stop, repeated, with a retain duration of
10 s. Checked 2026-10-14: on the unmodified 2017 source it fails when the
database starts in cycle 12 ("A ValueNode cannot be dirty"); with the current
code 40 cycles pass, also with the original 10 s pause between cycles (8
cycles).

The logs of the gates after the follow-up work (see its last paragraph) report
896 unit tests and 35 f-tests. The reviewed logs of the baseline in ignored
`java/build/level1/`, `java/build/level2/` and
`java/build/level3/` reported 886 successful unit tests, 29 successful f-tests,
zero failures in 200 random level 2 configurations and 200 random reclaim
configurations (all with cuts), identical streams in the restart-invariance
checks, and `LOADTEST OK` in the reclaim load check. Historical counts below
belong to the corresponding earlier fixes, including the 885-test
`b70fe6b` snapshot. These directories are reused and later runs can replace
their logs. The scripts and configurations are the reproduction route.


A transaction or a read that fails
==================================

Since 2026-10-22 (bergdb 005-01; register M49 of
[level4-alignment.md](level4-alignment.md), found in bergdb item 002 and
studied in item 003). The design is Frans's, from the start: no rollback of
in-memory state ("Support for rollback? Answer: No. If transactions are
deterministic, we don't need this, we can always check input data before we
start to modify data", 2008-08-02), and a database whose environment has
failed, or that has a bug, does not run on (`FatalDBException`, 2012-08; a
note of 2013-01). The notes are in the f1 repository's F1-007.

`Db.executeInner` has a go point. Before it, everything that may refuse the
transaction is checked, and nothing is changed: the STM check
(`RerunException`), the end of the top node ordinals (005-02), the size of
the transaction (005-17), the index nodes it can make dirty (005-31) and the
clock (005-18). The Pub API runs the
application's code before the transaction too: the action, the index
functions, the conversion of objects. A refused transaction leaves the
database as it was, and the database goes on. After the go point nothing
refuses the transaction and nothing is undone. What can still throw there
is the environment or a bug: a read error or a corrupt node when a put loads
an index node (evicted, or not loaded since startup), an append error in
`store()`, an `Error` (out of memory, an assertion), or reclaim's work after
the transaction.

When something throws after the go point, the database fails
(`DbState.FAILED`):

* The call throws a `DbFailedException` with what was thrown as the cause;
  an `Error` is thrown as it is.
* When the puts throw, the transaction's time never becomes a lookup time:
  `dbClock.transactionEnd()` is no longer in a `finally`.
* Every later transaction and read throws a `DbFailedException` with the
  first failure as the cause: `Db.execute`, `getOne` and `getMany`, and so
  the Pub API's writes, gets and index queries. A writer that waited for the
  write lock is refused when it gets it.
* Nothing more is appended. `sync()` still works for the transactions
  before the failure; `stop()` and `close()` work.

The application restarts the database: stops it and starts it again. The
stream holds whole records only, so the restart rebuilds the state as after
a crash at the failure: without the failed transaction, or with it if its
record was appended before the failure (it is then committed, although the
call threw). An append that fails part way is a torn record at the end of
the stream, which recovery drops (T1). An in-memory database is lost, as in
a crash. The Lean model needs no change: its runs have no failing
transactions, and the stream after a failure is the stream of a run without
the failed transaction, or with it.

Since 2026-10-23 (bergdb 005-30) a read that fails on the storage fails the
database in the same way: an I/O error, or corrupt data (a checksum or
format error). Before, the read threw a `StreamIoException` or a
`StreamFormatException`, and the database stayed active, half dead: after
an I/O error the storage below refuses all I/O (`FileStream` remembers the
error, and `StorageManager` closes the main stream), so reads of nodes in
memory still answered, reads that needed the stream failed, and writes
failed until one of them failed the database after its go point. Corrupt
data fails it too: it means lost data or a bug, and a database that serves
around the damage is worse than one that stops; after a restart, the next
read of that node fails it again, until the stream is repaired or restored.

* The reads: `Db.getOne` (`getOneInternal`, which the warm-up of a
  transaction also uses, before its go point), `getMany`, `getTrans` (the
  Pub API's `transactionInfo()`), and `sync()`, whose failure is a failure
  of the storage too. The writer's loads and reclaim's reads, after a
  transaction's go point, fail it as 005-01 says.
* The call throws a `DbFailedException` with what the read met as the
  cause, and every later transaction and read throws one with the first
  failure as the cause. Nothing has changed in memory: a load that fails
  registers nothing. A transaction that runs at the time ends as it would
  anyway, committed or failed, as after a crash at that point.
* Not failures: a read that a cut has overtaken expires with a
  `LookupTimeNotAvailableException`, and the database goes on (W1, Level 3);
  so does `getTrans` of a transaction that reclaim has removed. A read or a
  sync while the database is stopping throws as it did (`stop()` closes the
  storage under running reads), and so does a sync whose thread is
  interrupted (`StorageManager` throws an `InterruptedIOException`).
  `getTrans` refuses a position that cannot start a transaction, before it
  reads (`IllegalArgumentException`; since 005-43 also one at or past the
  end of the stream, which was a `DbException`); a format error at a
  transaction's position fails the database, as in the other reads, since
  005-34 made the positions that a get gives right.
* The state changes in one step under `readSync`, which the writer and the
  readers both take (`Db.setFailed`), and `stop()` and `close()` set
  `STOPPING` under it too: the first failure is the one kept, and no failure
  comes after a stop.

Nothing is added on the path of a read that does not fail: `getOne` and
`getMany` checked the state and caught `StreamIoException` already, and the
lock is taken only after a failure; `getTrans` checks the state.

Before 005-01 such a transaction was half committed: its time became
readable with its first puts in memory, its new nodes stayed in the node
table and in the writer's node list, and the next transaction wrote them as
its own and reused their ids. In a probe of the code before the fix, a
corrupt index node loaded by a put, with the storage healthy, let the next
transaction commit with the failed one's nodes in its record; after a
restart neither the failed put nor the next transaction's own value could be
read. Tests: `DbTesterFailure` (a value transformation that throws, an
`Error`, a read error and a corrupt node in a put after eviction, an append
error in `store()`, a writer waiting for the write lock, a refusal before
the go point; since 005-30, a read error and a corrupt node in a get and in
a scan, a read error in the warm-up, a failed sync, an interrupted sync, a
read while the database stops, and `getTrans`),
`DbTesterStream.testReadOnlyStream2` and `DbTester.testSyncAfterStreamFailure`.


Level 1: restart by full replay
===============================

A multiversion ordered map from (key, time) to value, with all data in
memory. The stream is a log of the user transactions; startup replays the
whole log. Startup time and memory grow with the stream, and the stream
grows forever.

This is the transaction-only stream of v5 (section 2.2) combined with the
persistent Dag. It is what the code does when the stream never grows past
the startup distance: the startup pos never moves, no index node is ever
written, and startup reruns every transaction from the primordial one. To
get it, set the startup distance larger than the stream will ever be
(DbBuilder.startupDistance(); the Pub API allows up to 1000 MB).

Theory needed for level 1:

* The persistent Dag: INV-LOOKUP for every time, from the Dag invariants in
  2015-algos (inv-tree, inv-walk, splits, TopDs). TopDs needs strictly
  increasing top node times (the second bug below).
* Replay determinism, INV-RERUN: rerunning the stored transactions from the
  primordial state rebuilds the same Dag, with the same node ids.

Not needed: dirty nodes, the Clean Rule, startup pos, reconciliation.
Neither is written down as a proof yet.


Level 2: bounded startup
========================

The database as designed: index nodes are written lazily to the stream,
and startup reads only the startup section, the tail of the stream, and
reruns the transactions in it. This is the default (startup distance 20
MB). Self-indexed streams.

Theory: [sis-model.md](sis-model.md), an abstract model with Rule A and Rule
R, and the theorems T1 (recovery) and T2 (restart invariance), proven in
Lean ([../lean/](../lean/README.md)). They prove the model, not the Java
code. Since 2026-10-16 the model has BergDB's bookkeeping and its virtual
root, and Java's runs are checked against it, step by step
([level2-alignment.md](level2-alignment.md), F1-008-11): see "Alignment with
the model" below.

How it works in the Java code. Reads of nodes in memory follow Java
references, as before; the extra work is at startup, at the first touch of
a node, and when index nodes are written.

* Lemma M (monotonicity): a suitable newer version, or the complete node in
  memory, preserves every lookup time served by an older version. This is
  the completeness obligation behind swizzling a stream pointer once and
  then following the Java reference directly. Proved for the model since
  2026-10-16 (bergdb item 001: `LM_newer`, `LM_ruleR`, `LM_cutTo`), with a
  model of Java's lazy reading in which reads after a lazy startup give P
  (T1-L), the writer's canonical objects hold their nodes' whole histories
  (CC) and restarts change no record (T2-L); Java's first touches are
  checked against that model's rule (C-L), and since 2026-10-17 against the
  Level 4 loader's (C-L4, a diagnostic). See "Alignment with the model".
* One node table (Cache3, shared by Db and NodeCollection), with one
  canonical object per node: the one that holds the node's whole history
  and can change. Other objects of a node are snapshots read from older
  versions, in pointers that named those versions. The writer, D and the
  still-dirty test only use canonical objects, and decide by node id, never
  by whether a pointer is in memory or in the stream.
* First touch (NodeCollection, following a stream pointer): the node
  table's canonical object if there is one; else exactly the version the
  pointer names after Rule R (the node's newest version in the startup
  section, if it is newer; also for a vpos), read as a snapshot that the
  node table does not get (since 2026-10-17, bergdb item 001, R8: M27 of
  [level4-alignment.md](level4-alignment.md); before, the newest of that
  version and a snapshot in the node table, and the version read was
  entered in the table). During startup's
  reconstruction, a version from the startup section is cut back to the
  startup time; at runtime never (2026-10-17, bergdb item 001, R8: M22 of
  [level4-alignment.md](level4-alignment.md)). The pointer listener is
  called on every follow. Puts and the rerun use a writer follower that
  makes every node it reaches canonical.
* Writing (Db.store): before index nodes are written, their pointers to
  index nodes in the pinned set (D, and the record being written) are
  resolved by node id (NodeCollection.resolvePointers), so that a node
  written in the same record is named by its new position and the
  still-dirty test sees every node in D; every other pointer keeps its slot,
  which names the latest version (since 2026-10-17, bergdb item 001, R8:
  before, any canonical object or a newer snapshot in the node table was
  taken, M21 of [level4-alignment.md](level4-alignment.md)). Startup links
  the stream pointers of D's canonical objects to canonical objects by node
  id (rule 4, `DbStarter.linkD`, M44), as the writer did at every write
  before.
* Startup (DbStarter): Rule R from the startup section by node id, for all
  index nodes; the section's nodes registered as canonical; the super root
  at the startup time from the last record's topPos (below); the rerun; and
  D rebuilt from the stored got-dirty ids. A node in D that the rerun does
  not reach is read from the position stored with its id. Before 2026-10-16
  such nodes came from deletes of keys that do not exist: such a delete put
  the nodes on its path in D, but it is not stored, so it is not rerun. Now
  it marks nothing (below).
* A transaction is one transaction of the Lean model (2026-10-16,
  [level2-alignment.md](level2-alignment.md), M1). A transaction applies its
  keys one at a time; a later key may split a node that an earlier key
  created or changed. A node that the transaction created is split in place
  (Dag.handleFullNode): no reader can reach it before the transaction ends.
  A node that existed before is replaced, as before, and then loses its
  klongs of the transaction, which its replacement has. So no node that a
  transaction created is unreachable at its time, and no node that is not
  reachable at that time has a klong of it (A2 and A3).
* Marking, step 3 (2026-10-16, M2): the index nodes that an operation (one
  put or delete) follows, creates or changes get dirty when the operation
  ends, and only if it changed something; a delete of a key that does not
  exist marks nothing. At the end of the transaction, a node that the
  transaction replaced and that got dirty in it is clean again and leaves D:
  it is not current, and its latest version is good for every earlier time.
  These are exactly the nodes that the model marks (T13). In a reclaim
  step, the nodes that its touch marked stay in D, also those that the
  step's puts then replace, as the model's step 3 has it (T13'); before
  2026-10-17 (bergdb item 001, R8: register M17 of
  [level3-alignment.md](level3-alignment.md)) a touch transaction kept every
  mark, the puts' too. Before, every node an operation reached got
  dirty at once; the change writes 1.4 to 13.7 percent fewer stream bytes in
  five workloads (level2-alignment.md, 10.4).
* The super root (2026-10-15, [level2-alignment.md](level2-alignment.md),
  M18): every record stores topPos, the position of the latest version of the
  newest written top node, which is the super root at the record's startup
  time (record format 5; streams of the older format 2 are refused).
  Before, startup scanned the section for the newest top node; transactions
  that change nothing (no KVs; with 10's change also deletes of missing keys)
  could move the startup pos past every top node version, and the database
  could not start.

Alignment with the model (F1-008-11, 2026-10-16;
[level2-alignment.md](level2-alignment.md), sections 10.5 and 11):

* Proved, in Lean, for the model: T1 (recovery, also after a crash after
  any transaction) and T2 (restart invariance), with BergDB's bookkeeping:
  marking in step 3, BergDB's still-dirty test (Rule A over all pointers),
  Rule R from R(s), a startup pos policy that sees the transaction, and a
  virtual root with top nodes as in Java; and T13 (marking is exact). Under
  the assumptions A1 to A5 and, for the virtual root, R1 to R4. No `sorry`,
  only Lean's standard axioms. Since 2026-10-16 (bergdb item 001, stage 1)
  also the physical layer of lazy reading, Java's objects, node table and
  first touch (`lean/SIS/Phys.lean`): lemma M, T1-L (after a lazy startup,
  also after a crash, reads at any time give P), CC and T2-L (with lazy
  restarts, canonical objects hold their nodes' whole histories and the
  records are the same), under two more assumptions of each transaction
  (`PhysStep`, M47, argued from α, TREE and A5).
* Checked, on Java runs: the trace checker runs the model's own `init` and
  `step` on traces of Java runs, and every transaction of 59 traces is a
  step of the model: the same record and the same D, with the assumptions
  met, and restarts and lookups as the model says. The Java tier checks
  A2, A3, A5 and Java's marking against the model's on 68,901 transactions,
  and `RestartInvariance` the same bytes with and without restarts, also
  with transactions that change nothing. The gates. Since bergdb item
  001's L5 also every first touch after a restart (C-L: 252,539 of the small
  set and 43,873 of the medium set follow the model's rule), the top nodes'
  skip slots and cached times, and the root at every time.
* Argued, not proved: the mapping α itself (level2-alignment.md, section
  2); that Java's references are the latest versions (M5; checked on every
  record); the order within a record (M6, M9); bytes as a function of the
  stream (M10); the physical layer's assumptions (M47). Lazy reading after a
  restart (M8) is proved for the model and checked on Java since bergdb item
  001 (level2-alignment.md, 13).
* Not modeled: bytes, torn records, durability, concurrency and the bounds
  (T3, T4). The gates cover the first four. Reclaim (Level 3) and eviction
  (Level 4) are modeled and proved since bergdb item 001 (2026-10-18;
  sis-model.md, section 15), except that Java's scheme gives safe cuts
  (T-SCHEME), which is checked at every cut, not proved.

Since 2026-10-16, `level2.sh` checks the alignment too (its step 7, and
mostly idle runs in step 4): `A2A3Check2` and the trace checker on the small
set, so the gate needs Lean (level2-alignment.md, 12). Since 2026-10-18
(bergdb item 001, K3), so does `level3.sh`, with reclaim (its step 8): the
small reclaim set, every record on the cut stream, `CutOK` at every cut
Java decides, the probes after restarts from the cut stream
(level3-alignment.md, 8). Since 2026-10-20 (bergdb 005-04) both tiers also
require TREE, A6' and A-COPY, the model's assumptions of stage 2:
`A2A3Check2` in `level2.sh`'s step 7, and the checker's C-A on every set the
gates run; the small and evict sets have a configuration with A6's kind, a
segment root that a transaction makes and splits in place
(level4-alignment.md, section 4).

The startup bug M18, found 2026-10-15 (transactions that change nothing
could move the startup pos past every top node version, and the database
then could not start), is fixed by topPos (above, bergdb `01f386a`).

Open:

* Bounds: the startup section can grow beyond the startup distance when many
  index nodes wait to be written (problem.md, R3 and Q4). The conservative
  still-dirty test may make dead nodes be written again and again. To
  measure.
* Bounds, one transaction: `TransSeq.take` takes transactions whole, so a
  transaction whose index nodes, those it makes dirty or creates, could not
  be written in one record stopped the startup pos for good: the startup
  section, startup, D and the stream grew without end (bergdb 005-31, item
  007's 007-02). Since 2026-10-24 such a transaction is refused before its
  go point, with a `DbException`, when a bound on those nodes at the largest
  node size passes 15/16 of the record limit (`Db.checkDirtyNodes`,
  `Dag.dirtyNodeBound`): a cheap test from the keys first, then, for a large
  transaction, a walk of the paths of its keys under the write lock. At the
  real limit that is updates of some millions of keys spread over as many
  key nodes; a larger update must be split by the application, as a
  transaction of values over 7/8 of the limit must (005-17). Reclaim's
  internal transactions are not checked; their steps have their own reserve.


Level 3: reclaim
================

Alignment with the Lean model: [level3-alignment.md](level3-alignment.md)
(bergdb item 001, in progress).

Reclaim cuts the front of the stream (pretruncate), so that the stream does
not grow forever. It is on when a retain duration R is set
(DbBuilder.retainDuration, Db.setRetainDuration); the default is to retain
forever, as since 2013. The retention requirement is that lookups work for
every time in [now - R, now]. Increasing R cannot restore already cut
history; the first available lookup time remains the API's actual frontier.

Tested 2026-10-13. The 2017 code had never been tested with restarts after
a cut. With a stream that refuses reads below the cut (CutStream), it failed
in 20 of 20 random configurations; after the fixes below, 0 of 200, and the
other checks pass. Reclaim.java was reworked; the class comment describes
it.

How it works in the reviewed baseline (including items 2 and 3 below):

* An iteration starts at an external transaction when the stream has grown
  by more than twice the startup distance since the last iteration started,
  and at least R/4 has passed since that start (ITERATION_SPACING = 0.25).
  pStart and tStart are the stream length and time then. pCut is the
  previous iteration's pStart; the first iteration uses its own pStart.
* Each external transaction allows a step while the charged bytes so far
  are below internalFraction (default 0.25) times the growth of the stream
  since pStart. The charge estimates rewritten value-node bytes and the
  stream sizes of index nodes made dirty by the step. It is not a cap on
  total reclaim traffic: table/record overhead and later still-dirty
  rewrites remain outside it, and stream growth includes reclaim itself.
  A step starts when the remaining allowance exceeds 10 KB and scans at
  time tStart with a target of the smaller of that allowance and 16 KB;
  the final KV can exceed the target. The scan and the step's reads of each
  KV are maintenance reads (since 2026-10-17, bergdb item 001, R8: M28 of
  [level4-alignment.md](level4-alignment.md)): they swizzle nothing into
  the slots, the node table gets nothing, and a step reads a version once
  (`NodeCollection.maintenance`); before, they swizzled what they read,
  the values too, which then stayed in memory. In one internal transaction
  it first touches the range at the current time (Trans.touch), dirtying its index
  nodes, including deleted-only branches; then rewrites each still-live
  value stored before pCut. A value transformation stores progress and the
  index-byte charge under `dreclaim/-current.txt`. The full table is stored when an
  iteration starts, ends, becomes safe or is selected for a cut. Startup
  merges the current row into the matching unfinished table row.
* When the scan reaches the end, the iteration is done; tEnd and pEnd are
  the time and the position of its last rewrite/touch step. A following
  table transaction stores done, tEnd and pEnd together; a crash before it
  leaves a resumable unfinished row. The safety argument requires every
  value reachable from tEnd on to be at pCut or later, and index nodes at
  pStart or later or dirty pending writeout. The tests support this
  argument; there is no reclaim proof yet.
* The cut at pCut waits until: tEnd is older than R; the startup pos has
  passed pEnd (every touched node written), and then passed pSafe, the
  stream length at that moment (a parent written before its child, and kept
  dirty by the still-dirty test, written once more); and the last valid
  meta block names a transaction at pCut or later, where recovery starts.
  Then the row is marked cut, the table is stored, the first available
  lookup time becomes tEnd, and the physical cut waits until the table is
  durable. This protects recovery metadata; elapsed time waiting for
  durability does not establish that all older readers have finished.
* Reclaim progress is stored in the table and current row or derived from
  stream positions. The recorded checks give the same stream byte for byte,
  cut and first available lookup time with and without restarts, including
  a restart after every transaction. This is test evidence for restart
  invariance with reclaim, not an extension of Lean's T2 theorem.

The bugs, fixed 2026-10-13, each with a test that fails without the fix
(all in the 2017 code, except 6):

1. Old values were not rewritten (Reclaim.Tester.testIterationRewritesAllOldValues).
   A value was rewritten if its time was before tStart, but the time
   reported for a value (gd.kvTime) is the time of the last time split of
   its key node, not of the write. Now the position of the value decides.
2. The first available lookup time was tStart, but values not changed
   since tStart are rewritten later in the iteration; until then lookups
   found the old versions, below the cut (Q6 in problem.md;
   testLookupsFromFirstAvailableTime). Now it is tEnd, the time of the last
   step. Also: the end of the scan set done before the last rewrite was
   stored, so a RerunException ended the iteration without it.
3. Nodes with deleted keys only, and the segment subtrees of deleted long
   keys, were never rewritten, and lookups and scans still pass through
   them (Q7; testDeletedKeysAfterCut). Now each step touches its key range.
4. Startup after a cut searched meta blocks down to position 0, and started
   its scan of transactions from a meta block that could be cut
   (testRestartAfterCut).
5. After a restart, the first available lookup time came from the last
   completed iteration, also when the stream was not cut there yet, so
   lookups in the retention window failed
   (testFirstAvailableTimeAfterRestart). Now the table marks the cut.
6. After a cut, writing an index node failed: NodeCollection.resolvePointers,
   from the level 2 work of 2026-10-12, read the headers of dead pointers
   to cut versions (testWritesAfterCut).
7. The cut checked that the last valid meta block came after the cut, but
   recovery starts at the transaction the meta block names, which could be
   before it (f-test testCutKeepsMetaBlockTransaction).
8. A pretruncate position still in the write buffer was passed on to the
   stream at once (BufferedStream.testPretruncateBeyondFlushed).
9. Reclaim starved with small startup distances: its table was stored every
   2 x startup distance, and these internal transactions, with the index
   nodes they carried, used the whole allowance, so iterations stopped. The
   allowance now counts the bytes rewritten.
10. The cut was not limited by the startup pos, or by the writing of the
   rewritten nodes; a restart after such a cut failed in the rerun (found
   with LoadTest, see Evidence).

Also found, with CrashTest, in the rework before it was kept: the last step
stored done, and tEnd and pEnd followed in the next transaction; a crash
between them left a done row with tEnd 0, and a cut there made 0 the first
available lookup time (testCrashBeforeIterationEnd). And the 20 ms sleep
before the cut, meant for readers with earlier lookup times, is replaced by
the wait for durability.

Evidence from the initial reclaim repair, before the later cost tuning:

* ReclaimStress (random configurations, retain 1 to 5 s, startup distances
  1000 to 20,000 bytes, node sizes 8 to 62, deletes, long keys, restarts
  between sessions, CutStream): 0 of 200 fail, all with cuts.
* RestartInvariance with reclaim: the same stream, the same cut and first
  available lookup time, with and without restarts, in 5 configurations,
  one with a restart after every transaction.
* CrashTest with reclaim: 0 of 50 fail.
* LoadTest with reclaim, 100,000 keys, the default startup distance and a
  retention of 1 s, a restart and a check of every key at each of 7 cuts:
  passes. Without the wait for pEnd it fails at a restart; this is the only
  test that needs that wait. No test needs pSafe; it is kept from the
  argument above.

Under load (LoadTest, 1M keys, 2M single-put updates, retain 1 s, on disk):

These measurements precede retention pacing, separate current-row storage
and the older cut point. They are an initial repair baseline.

| | No reclaim | Reclaim, uniform | Reclaim, hot set |
|---|---|---|---|
| Updates per second | 102,000 | 56,000 | 92,000 |
| Bytes appended per user byte | 6.0 | 7.6 | 4.1 |
| Stream kept after the cut | (all, 1.6 GB) | 0.8 to 1.2 GB | 1.1 GB |
| Live data | 104 MB | 104 MB | 104 MB |
| Commit p99.99 / max | 0.7 / 122 ms | 19 / 220 ms | 1.1 / 142 ms |
| Most index nodes in one commit | 392 | 4019 | 2964 |

Findings:

* Reclaim works under load (every key checked after a restart), but it is
  expensive. The stream after the cut is 8 to 12 times the live data: an
  iteration scans every KV and rewrites old live values, with an allowance
  of a quarter of stream growth, so it spans about 1 GB here, and one or two
  iterations are kept.
  This is Q8: about L/f to 2L/f plus the retained history, where L is what
  an iteration rewrites. A larger internalFraction gives a smaller stream
  and more writes. This estimate describes this earlier version, not a
  proven bound or the final cost of the tuned baseline.
* Commits of up to 4019 index nodes show that deferred per-node writes can
  still form bursts (prior-art.md, 5.5). The touch was initially blamed;
  later counts found few additional dirty nodes after the value rewrites.
  Those counts do not isolate total reclaim-induced index work. The cause
  was open at the earlier `b70fe6b` cutoff. The tuning report below attributes
  the bursts to large reclaim steps and reports a step cap ("Level 3 cost",
  items 2 and 3).
* Q9, Kv.time() after a rewrite: decided 2026-10-13 (Frans): no exact value
  time; `Kv.time()` and `Connection.time()` were removed from the Pub API.
  Found on the way: Kv.time() was already wrong without reclaim; after a time
  split of a key node, it was the time of the split, not of the write. See
  "Level 3 follow-up".
* Concurrent readers with a lookup time before a new first available lookup
  time (at this baseline the cut waited for durability, about 100 ms, without
  a reader-lifetime guarantee, and a read that reached the cut stopped the
  database): fixed 2026-10-13 evening, a read that a cut overtakes expires;
  see "Level 3 follow-up". Open: FileStream cuts whole files only (measured,
  the disk holds on average 6 to 9 percent more than the kept stream); the
  bound on the stream (R5) is measured, not proven.


Level 3 cost
============

Measured 2026-10-13 with [ReclaimCost.java](../java/stress/ReclaimCost.java)
and [reclaimgrid.sh](../java/stress/reclaimgrid.sh), to decide how often
iterations should run and what they should rewrite. Question from the
discussion with Frans: with a long retention, little is gained by
reclaiming often.

The first grid is the initial repair baseline; step 3 adds pacing and
current-row storage; option 3 adds the older cut point (`b70fe6b`); items
2 and 3 add index-aware budgeting and the scan target (`ebe5f77`). The
summaries are kept in `evidence/`:
[reclaimgrid-before-summary.txt](evidence/reclaimgrid-before-summary.txt),
[reclaimgrid-step3-summary.txt](evidence/reclaimgrid-step3-summary.txt),
[reclaimgrid-pcut-summary.txt](evidence/reclaimgrid-pcut-summary.txt) and
[reclaimgrid-items23-summary.txt](evidence/reclaimgrid-items23-summary.txt). Their `RESULT` rows retain the
workload, value size, K, f and measured quantities. The earlier H-based
experiment in [log.md](log.md) used a different setup.

Measures (Frans, 2026-10-13):

* WE, write efficiency = user bytes written / stream bytes appended, over
  a run of transactions. User bytes are keys and values as the user gives
  them; reclaim's rewrites are overhead.
* SE, store efficiency = user bytes accessible / stream kept. Accessible
  means every version that a lookup can return. SE counts what the user
  asked for, from now - R; "SE offered" counts from the first available
  lookup time, which reclaim leaves earlier. The stream kept is from the
  cut that reclaim decided (on disk, FileStream cuts whole files only).
* K, the retention: updates per key within R, so the user bytes written
  during R are K times the live user data.

Setup: 30 MB of live user data, 4-byte keys and values of 100, 1000 or
10,000 bytes (288,000, 30,000 or 3000 keys), startup distance 6 MB (0.2
times the live data), single-put transactions, simulated time. Workloads:
uniform; hot (90% of the puts on 1% of the keys); cold (all puts on 10% of
the keys, so 90% of the data never changes). Measured from the first cut
over six more, with internalFraction 0.25; WE without reclaim from the
same workload. Every run ends with a restart and a check of every key.
For reference, SE right after the load: 0.32, 0.89 and 0.99.

| Values | Workload | WE without reclaim | WE, K = 0.01 / 0.1 / 1 / 10 | SE, K = 0.01 / 0.1 / 1 / 10 | SE offered, K = 0.01 / 10 | Updates/s without / with (K = 1) |
|---|---|---|---|---|---|---|
| 100 B | uniform | 0.158 | 0.126 / 0.124 / 0.123 / 0.110 | 0.119 / 0.126 / 0.123 / 0.116 | 0.162 / 0.119 | 105,000 / 58,000 |
| 100 B | hot | 0.330 | 0.227 / 0.227 / 0.226 / 0.214 | 0.092 / 0.100 / 0.133 / 0.193 | 0.167 / 0.207 | 163,000 / 94,000 |
| 100 B | cold | 0.359 | 0.236 / 0.236 / 0.235 / 0.221 | 0.088 / 0.096 / 0.130 / 0.197 | 0.166 / 0.212 | 158,000 / 97,000 |
| 1000 B | uniform | 0.744 | 0.521 / 0.521 / 0.516 / 0.452 | 0.273 / 0.297 / 0.379 / 0.448 | 0.471 / 0.472 | 83,000 / 53,000 |
| 1000 B | hot | 0.824 | 0.610 / 0.610 / 0.608 / 0.588 | 0.168 / 0.183 / 0.274 / 0.485 | 0.382 / 0.535 | 98,000 / 65,000 |
| 1000 B | cold | 0.878 | 0.638 / 0.638 / 0.637 / 0.619 | 0.156 / 0.170 / 0.261 / 0.494 | 0.379 / 0.551 | 100,000 / 69,000 |
| 10 kB | uniform | 0.969 | 0.710 / 0.711 / 0.708 / 0.668 | 0.309 / 0.337 / 0.464 / 0.622 | 0.601 / 0.664 | 11,600 / 10,600 |
| 10 kB | hot | 0.975 | 0.725 / 0.725 / 0.724 / 0.713 | 0.185 / 0.201 / 0.309 / 0.574 | 0.441 / 0.636 | 11,800 / 11,000 |
| 10 kB | cold | 0.986 | 0.730 / 0.730 / 0.729 / 0.719 | 0.171 / 0.186 / 0.289 / 0.563 | 0.426 / 0.631 | 12,300 / 10,900 |

Values rewritten per iteration: 47 to 70% of the KVs (uniform), 87 to 92%
(hot), 95 to 96% (cold). Commit p99.9: 50 to 70 us without reclaim, 0.15
to 1 ms with (1.4 ms without reclaim for 10 kB values).

Findings:

* In this initial grid reclaim lowers WE by about 20 to 35% (relative) at
  K up to 1, and up to 39% at K = 10. That is one rewrite of most KVs per
  iteration, with iterations back to back, whatever K: the gap between cut points depends
  on the live data and f, not on the retention.
* At K = 0.01, SE is 0.09 to 0.31: the stream is 3 to 11
  times what the user can access, though a compacted stream would give
  0.32, 0.89 and 0.99. The stream kept is the window plus one to two
  iteration spans. At K = 1, SE reaches 0.46 in the best cell. With K = 10
  it is 0.45 to 0.62 for values of 1000 bytes
  and more. SE offered is higher: reclaim keeps history well beyond R
  (the first available lookup time lags by an iteration and more).
* An iteration rewrites most KVs, also in the uniform workload. A value is
  rewritten when it is stored before pStart, and the scan starts at pStart,
  so only the keys updated since the iteration began are spared.
* The reclaim table gets a row per iteration until the first cut, and every
  step stores the whole table: 0.5 to 2.6 MB per iteration with K up to 1,
  1.3 to 7.6 MB with K = 10. The allowance (f times the growth, which includes
  reclaim's own writes) then speeds up the iterations. This is most of the
  extra loss at K = 10. In the first grid (100-byte values, 100,000 keys,
  over 2.4 GB) the bytes appended per user byte rose from 8.0 to 10.3 as
  the rows accumulated, with the same work per iteration, and stayed flat
  without reclaim and with a short retention.
* The measured additional dirtiness of the touch is small: a few hundred
  index nodes per iteration, after the value rewrites have already dirtied
  nearly every leaf. This count measures the extra touch after those puts,
  not all index work caused by a step. It does not establish that reclaim's
  range traversal or later writes are cheap.
* In the uniform workload with
  100-byte values, user commits during an iteration write 200 to 1100
  index nodes (at most 18 without reclaim for that uniform workload); in the
  other cells at most 23. At the earlier cutoff the cause was unresolved;
  the subsequent report attributes it to large reclaim steps (items 2 and 3).
* internalFraction 0.5 instead of 0.25 (first grid, 100-byte values): the
  stream is 22 to 32% smaller, but reclaim's extra writes are 3 to 5 times
  larger and updates per second fall by about 45%. 0.25 is the better
  default for that comparison; broader tuning remains open.

Options considered after the initial grid (the first three were subsequently
implemented as step 3 and option 3):

* Pace iterations by the retention: start one when a quarter or so of R
  has passed since the last one started, and let f be only the highest
  rate. With a long retention, several times fewer rewrites, for about 12%
  more stream in the early estimate; use the measured grids below for results.
* Store the table so that a step writes only its own row, not every row
  kept until the cut.
* Separate the cut point from the start of the scan: rewrite what is
  stored before a cut point c older than the scan, so that the users have
  overwritten more of the hot data by then. Helps uniform and hot data;
  cold data can also benefit by skipping the previous iteration's rewrites.
* A front-cut stream must eventually copy unchanged live data past the cut.
  A second stream or generations for cold data is a possible later change,
  not an implemented feature.

Step 3, 2026-10-13: iterations paced by the retention, and steps store only
their own row.

* An iteration starts only when a quarter of the retain duration has
  passed since the last one started (Reclaim.ITERATION_SPACING), besides
  the stream having grown by twice the startup distance.
* A step stores the row of its iteration under its own internal key
  (dreclaim/-current.txt); the table is stored when an iteration starts,
  ends, gets safe or is cut. At startup the row replaces the table's row
  with the same pStart, while that row is not done.
* Tests that fail without the change: Reclaim.Tester.testIterationsSpacedByRetention,
  testRestartResumesIteration. level1.sh, level2.sh and level3.sh pass,
  RestartInvariance with reclaim gives the same stream byte for byte.

The same grid again (WE / SE, before → after):

| Values | Workload | K = 0.01 to 1 | K = 10 |
|---|---|---|---|
| 100 B | uniform | +0.000 to 0.003 / unchanged | WE 0.110 → 0.147, SE 0.116 → 0.136 |
| 100 B | hot | +0.002 / unchanged | WE 0.214 → 0.251, SE 0.193 → 0.213 |
| 100 B | cold | +0.003 / unchanged | WE 0.221 → 0.263, SE 0.197 → 0.220 |
| 1000 B | uniform | +0.009 to 0.014 / +0.004 | WE 0.452 → 0.623, SE 0.448 → 0.547 |
| 1000 B | hot | +0.005 / unchanged | WE 0.588 → 0.622, SE 0.485 → 0.503 |
| 1000 B | cold | +0.006 / unchanged | WE 0.619 → 0.644, SE 0.494 → 0.506 |
| 10 kB | uniform | +0.007 / +0.004 | WE 0.668 → 0.814, SE 0.622 → 0.710 |
| 10 kB | hot | +0.004 / unchanged | WE 0.713 → 0.729, SE 0.574 → 0.582 |
| 10 kB | cold | +0.004 / unchanged | WE 0.719 → 0.734, SE 0.563 → 0.570 |

The table now costs 0.2 to 0.8 MB per iteration, independent of K (before:
up to 7.6 MB). Updates per second: up to 64% higher at K = 10 (uniform,
100-byte values), otherwise about the same.

Findings:

* The extra loss at K = 10 is gone; WE at K = 10 is now at least WE at
  K = 1. The uniform workload gains most (WE 0.45 → 0.62 for 1000-byte
  values): its iterations are short, and now start R/4 apart.
* Where an iteration takes R/4 or longer, nothing changes: iterations
  still run back to back, at the rate f allows. That is every cell with K
  up to 1, and the hot and cold workloads at K = 10 (cold, 1000 bytes: an
  iteration spans 125 MB, a quarter of the 466 MB window). There WE stays
  20 to 33% below WE without reclaim: reclaim writes at f, all the time.
* What remains is mostly copying data that does not change. A stream cut
  only at the front must copy every live byte once per cut point; with
  cut points a quarter of R apart that is 4 copies per retention period,
  and with a short retention, one copy per iteration span (about L / f of
  growth). The choices left: fewer cut points (a larger spacing: fewer
  copies, a longer stream), a lower f with a short retention (better WE,
  worse SE), a cut point older than the scan (fewer rewrites of hot data:
  uniform still rewrites about half the KVs), and later a second stream
  for cold data.

Option 3, 2026-10-13: a cut point older than the scan. Each iteration has a
cut point pCut, the pStart of the iteration before (the first iteration:
its own pStart). A value is rewritten if stored before pCut, and the stream
is cut at pCut. The values the users write between pCut and pStart need no
rewrite, and neither do those that the iteration before rewrote, so data
that never changes is copied every other iteration. Correctness is as
before with pCut for pStart: values reachable from tEnd on must be at pCut
or later, while index nodes are at pStart or later or remain dirty until
writeout. The cut still waits for pEnd and pSafe. Test that fails without it:
Reclaim.Tester.testCutPointBeforeScan. All three level checks pass, with
the same stream byte for byte with and without restarts.

The grid again, WE and SE, step 3 → option 3:

| Values | Workload | K = 0.01 to 1: WE | K = 0.01 to 1: SE | K = 10: WE | K = 10: SE |
|---|---|---|---|---|---|
| 100 B | uniform | 0.126 → 0.117 | about the same | 0.147 → 0.152 | 0.136 → 0.124 |
| 100 B | hot | 0.229 → 0.220 | about the same | 0.251 → 0.272 | 0.213 → 0.210 |
| 100 B | cold | 0.239 → 0.230 (K = 1: 0.237) | about the same | 0.263 → 0.300 | 0.220 → 0.225 |
| 1000 B | uniform | 0.530 → 0.520 | +0.02 (0.27 → 0.29 at K = 0.01) | 0.623 → 0.716 | 0.547 → 0.573 |
| 1000 B | hot | 0.615 → 0.615 | about the same | 0.622 → 0.708 | 0.503 → 0.528 |
| 1000 B | cold | 0.644 → 0.655 | about the same | 0.644 → 0.737 | 0.506 → 0.533 |
| 10 kB | uniform | 0.717 → 0.714 | +0.03 to 0.04 | 0.814 → 0.940 | 0.710 → 0.752 |
| 10 kB | hot | 0.729 → 0.739 | +0.003 to 0.01 | 0.729 → 0.832 | 0.582 → 0.615 |
| 10 kB | cold | 0.734 → 0.757 | about the same | 0.734 → 0.836 | 0.570 → 0.598 |

WE without reclaim: 0.158, 0.330, 0.359 (100 B); 0.744, 0.824, 0.878 (1000
B); 0.969, 0.975, 0.986 (10 kB). Relative to the initial repair, the
fraction rewritten per iteration is roughly halved or lower: uniform
47 to 70% → 24 to 35% (10 to 13% at K = 10), hot 87 to
92% → 43 to 46%, cold 94 to 96% → 45 to 50%. Updates per second at K = 10:
+10 to 16%.

Findings:

* With a long retention (K = 10) WE rises by about 0.005 to 0.126 from
  step 3, and SE by up to 0.04 (it falls for 100-byte uniform and hot).
  Against no reclaim, WE is about 3 to 18% lower there
  (uniform, 10 kB: 0.940 of 0.969).
* With a short retention (K up to 1) the WE changes are mixed: about 0.01
  lower for 100-byte values and uniform 1000-byte values, but higher for
  some hot/cold workloads (up to about 0.023 for cold 10 kB). Rewriting
  fewer values per iteration does not translate into a proportional gain.
  There an iteration takes longer than R/4, so iterations run back
  to back and reclaim writes at the rate f allows, all the time: cheaper
  iterations just run more often (and each touches the whole index, which
  the allowance does not count). With a short retention, f strongly
  influences WE; excluded index/table traffic also matters, as the small
  WE regressions demonstrate.
* So the choice left with a short retention is WE against SE, through f
  (or a target for one of them).

Committed tuning, 13 October: ebe5f77
-----------------------------------

The following tuning is included in `ebe5f77` and the log
snapshot of that day. Source, numerical summaries and existing regression logs were
checked for consistency; Java gates were not independently rerun by this
reviewer. The logs report 886 unit tests, 29 f-tests and successful Level
1–3 checks. Grid source: [evidence/reclaimgrid-items23-summary.txt](evidence/reclaimgrid-items23-summary.txt).

Items 2 and 3, 2026-10-13: the allowance counts the index nodes, and the
cause of the large commits.

* The allowance counted each rewritten value as its bytes plus 100 for the
  index; the index nodes a step makes dirty were not counted. Now a step
  counts the value nodes (key, value and 28 bytes) and the stream size of
  every index node it makes dirty (Trans.dirtiedBytes, counted in
  Db.makeDirtyIfNeeded). That size is known only while the step runs, so
  the row of the iteration is stored by a value transformation, and the
  touch now comes before the puts (the puts then make dirty only new nodes
  and nodes outside the range). Test:
  Reclaim.Tester.testAllowanceCountsIndexNodes.
* The large commits. The allowance is a budget for the whole iteration,
  and the stream grows in bursts (the writes of nodes made dirty a startup
  distance earlier), so a step could scan up to a megabyte of KVs and make
  800 index nodes dirty. The implementation report says a step's own record
  then took about 1000 dirty
  nodes from the queue, and the still-dirty test added 100 to 250 parents
  back to that step's transaction. The writer takes the dirty nodes of a
  transaction together (TransSeq.take), so a user commit later wrote that
  whole set, up to 1100 index nodes. Seen with logging of the transactions
  whose dirty list exceeded 100 nodes. A step now uses a 16 KB scan target
  (Reclaim.MAX_STEP_SIZE). With 40 KB, user commits still wrote up to
  280 nodes. The 16 KB cap is a scan target, not a strict byte maximum:
  `ADD_AND_STOP` can exceed it by the final KV. Index writes, table writes
  and transaction-level dirty batches still need separate budgets.

The grid again, option 3 → items 2 and 3:

* Most index nodes in one user commit, 100-byte values: 16 to 1134 → 17 to
  125 (without reclaim at most 31 across workloads, 18 for uniform).
  Other value sizes: at most 19 before,
  at most 10 now.
* WE changes: 100-byte values -0.013 to +0.001 (the smaller steps cost; without
  the cap, counting the index raised WE from 0.118 to 0.122 for uniform at
  K = 1); 1000 bytes -0.009 to +0.001; 10 kB -0.003 to +0.012.
  SE changes range from -0.015 to +0.011.
* Relative WE loss against no reclaim at K up to 1 is about 23 to 38%,
  with f = 0.25 (1 - WE / WE without reclaim). This is a workload comparison,
  not a direct measurement of reclaim's share of all writes. Rows, record
  headers and later still-dirty rewrites remain outside the allowance.

Level 3 follow-up
=================

Done 2026-10-13 in the evening, after commit `61a45a0`, as planned in the
completed W1–W5 plan (in Git at `5650ed7`). Decisions of Frans: a read admitted before a
cut may expire (D1 = A), no exact value time in the product (D2 = A), f stays
0.25 (D3 = A). Everything below was run after the work; the counts of the
gates are at the end of this section.

Readers and cuts (W1)
---------------------

Reproduced first, with a read that is held after its first KV (a stop condition
of a GetMany scan, which holds no pointer lock) while the writer drives the next
cut. The old code failed in more ways than the plan assumed:

* `FileStream.read` of a deleted file, or of a file closed by `pretruncate`
  under the reader, stored a permanent `IOException`: every later read and
  append of the stream failed.
* `StorageManager.read` treated every `IOException` of the main stream as a
  fault: it closed the stream and set an error state ("Main storage not
  active"). So even with `CutStream`, which only throws for the read, one late
  reader stopped the database. In the new stress test (`ReclaimReaders`) the
  old code failed 2 of 10 rounds this way, with `CutStream`.

The fix, in the order of the layers:

* `bergdb.stream.ReadBelowFirstPosException` (an `IOException`): thrown by
  `FileStream` (a position below `firstPos`, and `DbFile.read` of a file that
  `pretruncate` deleted), `MemoryStream` and `CutStream`. It is not remembered
  as a fault.
* `StorageManager.read` rethrows it without closing the stream or setting an
  error state.
* `Db.getOneInternal` and `Db.getMany` turn a `StreamIoException` caused by it
  into `LookupTimeNotAvailableException` when the lookup time is now before the
  first available lookup time (the read has expired); otherwise it stays a
  failure (since 2026-10-23 one that fails the database, bergdb 005-30; see
  "A transaction or a read that fails"). Expiry is documented in the Pub API
  (`Database.getFirstAvailableLookupTime`, `setRetainDuration`,
  `Connection.setLookupTime`, `freezeLookupTime`).

Tests, each failing without the fix (checked by removing it):
`ReclaimReaderTester` (`CutStream`, unit; `FileStream`, f-test: after the
expiry the database accepts a write, reads it back and passes `checkNodes()`),
`FileStream.testReadBelowFirstPosDoesNotBreakStream`,
`testReadOfFileDeletedMeanwhileDoesNotBreakStream`,
`StorageManagerTester.testReadBelowFirstPosIsNotAStreamError`. The stress
`ReclaimReaders` (step 5 of level3.sh): 2 to 4 reader threads, one half with
slow scans of 200 KVs, on a cold cache after each restart, `CutStream` and
`FileStream`; an operation must equal the model or expire. In the runs before
the gate: 18 rounds with `CutStream` and 8 with `FileStream`, 0 failures, 3
operations expired during the run with a cut overtaking them, and 150
expired at admission (the rest ran to the end, 40 million operations).
Protected long-lived snapshots (option B of the completed plan) are not built
and remain optional. Level 4 needs safe object and cold-load lifetimes while
preserving the accepted expiry contract; see [level4-plan.md](level4-plan.md),
section 6.

The retain duration may change (W2)
-----------------------------------

`ReclaimRetentionTester` (unit and f-tests) and `ReclaimStress` with random
changes of the duration at restarts and during sessions (1, 2, 5 s, or forever).
Checked: every cut keeps the guarantee of the duration in force when it was
decided (`Stats.Cut.retain`), the first available lookup time never moves
back, also over a restart, lookups from it give the model's answer (and, for up
to 50 keys, every key at every transaction time from it: W5a), a lookup before
it throws. Cases: shrink during an iteration; shrink with several done
iterations waiting (the newest is cut); grow after a cut is decided and before it
is made (the cut is made, the first available lookup time stays); restart with
another duration (also forever); forever and then finite with a long history;
finite and then forever in the middle of an iteration (it ends, no new one
starts); a duration below 1 s is refused. The weakened cut condition
`now - R/2` is caught by the first test. 200 random configurations with
changes: 0 failures. Nothing needed fixing.

`Kv.time()` and `Connection.time()` removed (W3, Q9)
----------------------------------------------------

Removed from the Pub API with their tests (`testKvTime1`, `testKvTime2`). The
time was the time of a key-node entry, wrong after a time split and changed by
reclaim. `TransactionInfo.time()` stays (the transaction time). `GetData.kvTime`
and `Kvt.time` stay as internal, marked inexact. Q9 is answered in
[problem.md](problem.md). An exact write time would be stored in the value node
(a format change); not planned.

Where the bytes go (W4)
-----------------------

`Reclaim.Stats` counts the records in the stream by who wrote them (user
transactions, reclaim steps, table stores) and what they hold (value nodes,
index nodes, the rest); `ReclaimCost` prints them per user put (`BYTES`) and in
the `RESULT` line (`uB`, `uVal`, `uIdx`, `sB`, `tB`). Index nodes are counted in
the record that writes them; most of those that reclaim makes dirty are written
in its own step records, which is why the user records of a run with reclaim
hold fewer index nodes than without it. Total stream bytes per user put, no
reclaim against reclaim at K = 1 (K = 0.1 is the same), 10 MB of live user
data, startup distance 2 MB, f = 0.25, single puts:

| Values | Workload | No reclaim | With reclaim | of which steps | Extra | Extra: values | Extra: index | Extra: other | Extra / total | WE |
|---|---|---|---|---|---|---|---|---|---|---|
| 100 B | uniform | 662 | 923 | 612 | 261 | 139 | 115 | 6 | 28% | 0.157 → 0.113 |
| 100 B | hot | 312 | 464 | 84 | 152 | 74 | 75 | 4 | 33% | 0.333 → 0.224 |
| 100 B | cold | 290 | 466 | 85 | 176 | 75 | 96 | 5 | 38% | 0.359 → 0.223 |
| 1000 B | uniform | 1349 | 1930 | 525 | 581 | 474 | 96 | 11 | 30% | 0.744 → 0.520 |
| 1000 B | hot | 1223 | 1644 | 400 | 421 | 384 | 32 | 5 | 26% | 0.821 → 0.611 |
| 1000 B | cold | 1143 | 1555 | 360 | 412 | 350 | 57 | 5 | 27% | 0.879 → 0.646 |

Reclaim adds 26 to 38 percent of all stream writes in these cells (bytes per
user put, a user put is 104 or 1004 bytes). It is half to four fifths value
rewrites, the rest mostly index nodes written again because the touch made them
dirty (as much as the values for small values and the hot or cold workloads).
The table and record overhead are small (table: under 1 byte per put). The
allowance f = 0.25 limits the sum of value bytes and index bytes made dirty to a
quarter of the stream growth; the measured share, 26 to 38 percent, is within
a factor 1.5 of it, the larger for small values. So the allowance tracks the real
cost well enough that a controller for WE or SE (D3, options B and C) is not
needed now. Raw output: `java/build/w4/grid/` (ignored).

Tail latency (4.2). The target is at most 200 index nodes in one user commit
(`ReclaimCost` prints `TAIL TARGET`). Measured in the cells above: at most 100
(K = 1; 122 at K = 0.1) for 100-byte values with the uniform workload, 17 or 18
for the hot and cold workloads, and 8 to 10 for 1000-byte values, against 6 to
20 without reclaim. Met; no cap on the dirty batch of a transaction
(`TransSeq.take`) was added. The p99.9 commit latency is 0.14 to 0.86 ms with
reclaim, 0.04 to 0.06 ms without, since a step runs inside the external
transaction. Not measured: GC pauses with reclaim, and ZGC. The space bound of
Q8 for the algorithm as built is not derived; the measured SE is the answer.

Small items (W5)
----------------

* a. `ReclaimStress` checks, for up to 50 keys and at most 200,000 (key, time)
  pairs, every key at every transaction time from the first available lookup
  time, before and after each restart (a cold cache: every surviving old
  version is read from a stream that refuses reads below the cut). The 200 rounds of the
  gate do this about 3,000 times (900 to 1,200 per 60 rounds); 0 failures.
* b. `pSafe`. The wait for `startupPos >= pSafe` was removed in a copy and run:
  180 random rounds of `ReclaimStress` (with the exhaustive check and changes of
  the duration) and 30 rounds of `CrashTest`, 0 failures. No case that needs
  the wait has been found. It is kept, as the safety argument requires it
  (it costs about one startup distance of stream).
* c. Durable at the 13 October source. `StorageManager.getDurableLength()` is the length confirmed
  appended to the underlying stream, and `FileStream` writes with mode "rws"
  (synchronous). So a cut that waits for it waits for the data to be written
  through the OS; on macOS that is not `F_FULLFSYNC` (drive cache), a
  hardware question at that cutoff. The later explicit-force work and native
  audits are in [level3-durability.md](level3-durability.md).
  `Reclaim.Tester.testCutIsMadeAfterDecisionIsDurable` fails when the wait is
  removed. `CutStream.truncate` (used by `CrashTest`) never cuts the stream shorter than it was at
  the last cut, which is the model of this.
* d. Disk. `FileStream` deletes whole files; a new file's size is the largest
  allowed size not above a quarter of the kept stream. Measured with `ReclaimCost`
  on disk (K = 1, uniform, 20 MB live data): bytes on disk divided by the stream
  kept: mean 1.06 to 1.09, at most 1.55 to 1.62 (sampled every 1000 transactions,
  including the time between a decision and the cut, and right after the first cut,
  when the files were sized for a larger stream).
* e. `Reclaim` runs in the writer thread under the write lock
  (`transactionCompleted`), so a cut decision does not race with a user
  transaction; the reader stress did not find otherwise.

Found on the way, and fixed: a data race between readers and the writer.
`ReclaimReaders` failed one round in about 100, in the writer, with "Bad stream
pointer of KeyNode, spos -10000" from the check of the serializer (with -ea; the
same read is what writes the pointers). A reader that follows a stream pointer
replaces it with a memory pointer, setting the node and then the position (access
data in place of a stream position). The writer read the node, then the position;
it could see a null node and the new position, and took the access data for a
stream position. Without `-ea` that is a wrong pointer written to the stream. It
exists without reclaim, whenever readers touch cold nodes while the writer
serializes the same key node (after a restart); it is the interleaving that
[level4-plan.md](level4-plan.md), section 4.5, predicted from the source. Fix:
`KeyNode.getPointer()` and `TopNode.getPointer()` read the pair coherently (a
memory pointer without a lock, a stream pointer under the monitor of the node,
which `setPointer()` holds), and the serializer of the top node and the check of
the serializer use them. The original design comment of `KeyNode.pos` ("used
atomically with pointers") asked for this. Test:
`ReclaimReaderTester.testPointerPairIsCoherent` fails without the fix after
about 3600 reads. Level 4 (eviction) must revisit it: it assumes that a memory
pointer stays one. Since 2026-10-17 (bergdb item 001, R8, change 4: M23 and
M24 of [level4-alignment.md](level4-alignment.md)) both read the reference
once and decide on that read; access data is written only into a memory
pointer (`setPointerAccessData` checks it, under the pointer's lock, which
every change of a pointer holds), so a position that an unswizzle writes
will survive a reader that saw a memory pointer; and the access clock is a
field of its own (`Cache3.accessClock`), advanced at every node read from
the stream and every node the writer makes.

Found on the way, and fixed: GetMany with an inclusive start key (the default)
did not return the start key when the tree of its segment had more than one node
level (more than about 30 keys): `GetMany.Chain.eqMatch` compared the number of
links with the number of key segments. And a backward scan from a start key in
such a tree began at the wrong key (for 120 keys, backward from `/k/0` returned
`/k/106` first, also exclusive): above the leaf the setup searched for the first
klong at or after the start key, which is the next child, not the one that holds
the start key. Both fixed in `GetMany.Chain.setup()`/`eqMatch()`; tests
`DbTesterGetMany.testInclusiveStartKeyWithDeepTree` (failed before) and
`testStartKeyRandom` (random trees, both directions, inclusive and exclusive,
against a sorted list). The Pub API (`from(key)` is inclusive by default) was
affected by the first.

A read of the latest state (lookup time `Long.MAX_VALUE`) is a read of a finite
snapshot, the last transaction at its start, and it can be overtaken by a cut too:
`Db` decides the expiry by the actual lookup time, not the requested one
(`ReclaimReaderTester.testLatestReaderExpiresWhenCutOvertakesIt`; the stress reads
the latest state too).

Gates after the work, 2026-10-13 21:41 to 21:53 CEST, run on a copy of the tree
(source fingerprint `73eb1ea7038e`, the SHA-1 of the SHA-1s of the `.java` and `.sh`
files under `bergdb/p` and `stress`, sorted by path), because another session was
running gates in the shared `java/build/` at the same time: `level1.sh`, `level2.sh`
and `level3.sh` (full) print `LEVEL 1 OK`, `LEVEL 2 OK` and `LEVEL 3 OK`. The
first run of `level3.sh` failed once, in the f-test `DeleteIndexTester.deleteIndexWhileAddingMore`
("time1, expected 10, got 0"), which depends on the speed of a background thread and
ran while the machine was loaded by the other gates; alone it passes (4 of 4), and the
second run of `level3.sh` passed. Unit tests: 896 successful. F-tests: 35 successful.
ReclaimStress: 200 random configurations (with changes of the retain duration and the
exhaustive check), 0 failures, all with cuts. ReclaimReaders in the gate: 12 rounds each
of CutStream (2 runs) and FileStream, 0 failures. Before that, 160 rounds (120 CutStream, 40
FileStream, reads of the latest state included), 0 failures, 13 operations expired
with a cut overtaking them. CrashTest 25 rounds, 0 failures; RestartInvariance: same
stream, cut and answers; LoadTest: 6 restarts with a full check. Logs in ignored `java/build/`.
Level 3 takes about 4 minutes.


Independent review, 13 October
------------------------------

Codex independently reviewed the subsequent source and ran full Java gates
from an isolated source copy, after checking Lean. The implementation and
review repairs were committed in `0319caf`. Later `5650ed7` changes to Java
and the stress harness are comment corrections, not a new validation run.
The detailed review is available with:

```sh
git show 5650ed7:b/007-bergdb-261012/theory/level3-review.md
```

The full gates ran **21:45:42–21:55:29 CEST, 2026-10-13**, using Homebrew
OpenJDK 27, build 27, the 64-Bit Server VM, `JAVA_HOME=/opt/homebrew/opt/openjdk`,
the `--release 8` build and assertions enabled. The collector was not recorded;
do not treat this run as a GC comparison or controlled performance reference.

The reviewed source manifest SHA-256 was
`187234ed377a90ecb4e1b547b7e6775f99cbb992c8ef10ceca21bf5d6b6e95d4`, covering
414 files in `java/{src,src-dev,src-icu}`, `java/stress/` and `build.sh`.
Raw evidence was copied to ignored `java/build/level3-review/`. This identifies
the reviewed historical input, not the current source after later comments.
After whitespace-only cleanup, 1,044 database/test classes and 21 stress
classes matched the gated build byte for byte. A subsequent functional-test
repair changed only `DeleteIndexTester.class`; all 35 functional tests passed
again, with production and stress bytecode still matching the full gates.

| Check | Independently observed result |
|---|---|
| Clean Lean build | 27 build jobs passed |
| `lake exe sistest 20 40` | Eight variants: assumptions, T1 and T2 pass 20/20 seeds each |
| Four public theorem axiom checks | Only `propext`, `Classical.choice`, `Quot.sound`; no shortcuts in checked sources |
| Full Level 1–3 gates | All three passed; 896 unit tests in each gate; 35 functional tests, also rerun after the fixture repair |
| Reclaim with changing retention | 200 configurations, all with cuts, zero failures; 3,528 exhaustive small-state checks |
| Reclaim restart invariance | Four configurations: stream bytes, cuts, dirty sets, identities and lookup results equal |
| Reclaim crashes | 25 rounds, zero failures in the complete-record model |
| Concurrent readers | 36 rounds, all with cuts, zero failures; 81,481,857 gets and 27,403,141 scans; 56 admission expiries and 6 in-flight expiries |
| Reclaim load check | Six restarts after cuts, each with a full value check; `LOADTEST OK` |

Further repairs from the independent review:

* `KeyNode.lastVersionGivenDel` and actual array growth now share the
  pointer setter's node monitor; top-node inheritance uses coherent
  `getPointer` reads. A one-way reader swizzle previously copied `-10000`
  as a stream position. The permanent regression failed on the handoff
  binary; a standalone version-copy reproduction passed 1,000,000 trials
  after repair. Resident traversal still uses direct Java references.
* Latest-request expiry was verified against the actual finite snapshot,
  not the requested `Long.MAX_VALUE`. The regression forces a read of old
  backing bytes after a cut even if rewriting warmed the graph. A correct
  warm read may finish after expiry; expiry is permitted, not mandatory.
* The corrected deep-tree backward start and the sorted-key oracle tests
  passed in both directions with inclusive/exclusive bounds.
* `ReclaimReaders` waits for model publication through the actual returned
  snapshot, including internal reclaim times, rather than racing publication
  or skipping latest results. This changes the test oracle, not production
  read synchronization.
* `DeleteIndexTester` no longer requires ten internal entries at a time
  sampled after asynchronous deletion started. Historical, immediate logical
  disappearance and final cleanup checks remain.

The completed review does not establish hardware power-loss safety, a
reclaim safety proof, hard storage/memory bounds, GC or worst-case latency,
or replication with cuts. The 200-index-node measurement target is not an
enforced cap. These proof/measurement limits and the API's expiry contract
survive the document consolidation. Archived .NET/release documentation
still needs an API-removal check before release. The new
[Level 3 plan](level3-plan.md) addresses the next three validation gaps; the
older cost grids remain historical measurements.


Evidence
========

With [RestartStress.java](../java/stress/RestartStress.java) (model check of
latest and historical lookups, before and after every restart),
[RestartInvariance.java](../java/stress/RestartInvariance.java) (the same
transactions with and without restarts, compared) and
[DagFuzz.java](../java/stress/DagFuzz.java) (the Dag alone).

Level 0, no restarts:

* Random settings with deletes, 100 to 200 rounds per node size 14, 30 and
  62: no failures.
* Node size 8: 12 of 200 rounds gave a wrong historical lookup, and 1 of
  200 at level 1. This was the second level 1 bug; after its fix, 0 of 200.
* DagFuzz, up to 50 keys per transaction, every key checked at every time:
  before the second fix, 4 to 12 of 300 rounds failed for node sizes 8, 14
  and 30; after it, none.

Level 1, restarts by full replay:

* 25 restarts per round, deletes, 7-byte keys (3000 keys): 100 of 100
  rounds failed before the first fix, 100 of 100 pass after it; also node
  sizes 8, 14 and 62, and on disk.
* About 100 MB, restart every 4,000 transactions: the same stream, byte
  for byte, as without restarts (since value node padding is written,
  2026-10-12), with the same dirty set and correct lookups.

Level 2, bounded startup:

* Before the repairs (2017 code): 68 of 100 random configurations failed,
  and all 5 seeds of the default case on disk past 20 MB. Details in
  [startup-invariants.md](startup-invariants.md), section 5.
* After the repairs: random configurations 0 of 200
  fail (startup distances 100 bytes to 20 MB, node sizes 8 to 62, deletes,
  transactions of up to 40 keys); the default case on disk past 20 MB, 0 of
  10 with deletes and 0 of 5 without. RestartInvariance gives the same
  stream byte for byte, with node identity and lookups correct, in every
  run: startup distances from 100 bytes to 20 MB, node sizes 8 to 62, long
  keys, transactions of up to 40 keys, a restart after every transaction,
  and about 100 MB.
* Read and write speed as before the repairs (bergdb.test.Get, 100,000 and
  1,000,000 keys, alternating builds).


Level 2 under load
==================

Measured 2026-10-13 with [LoadTest.java](../java/stress/LoadTest.java) on a
FileStream on the Mac (10 cores, SSD, JDK 27, G1, one writer thread). Keys
are 4 bytes and values 100 bytes. A load of n keys in random order, 100
per transaction; then single-put transactions on uniformly random keys;
then sync, stop, start, reads, and a check of every key. Default settings
(startup distance 20 MB then; 50 MB since 2026-10-13, see below) unless
noted. All runs passed the full check.

| | 1M keys, 2M updates | 1M, hot set | 1M, sd 200 MB | 1M, full replay | 10M keys, 10M updates |
|---|---|---|---|---|---|
| Stream at the end | 1.6 GB | 1.0 GB | 0.7 GB | 0.5 GB | 18.5 GB |
| Startup | 0.62 s | 0.61 s | 5.6 s | 15.7 s | 0.70 s |
| Transactions rerun at startup | 20,000 | 64,000 | 627,000 | 2,010,000 | 14,000 |
| Updates per second | 102,000 | 155,000 | 115,000 | 113,000 | 68,000 |
| Bytes appended per user byte | 6.0 | 2.9 | 2.6 | 1.65 | 9.9 |
| Index nodes written per update | 1.20 | 0.32 | 0.22 | 0 | 2.40 |
| Startup section, max | 1.36 x sd | 1.07 x sd | 1.00 x sd | (all) | 2.21 x sd |
| Dirty set D, max (sampled) | 63,000 nodes | 31,000 | 215,000 | 394,000 | 111,000 |
| Commit latency p50 / p99.9 | 4.3 / 135 us | 3.3 / 52 us | 3.9 / 90 us | 3.9 / 38 us | 12 / 104 us |
| Get, warm | 0.87 us | 0.73 us | 0.88 us | 0.75 us | 1.0 us |
| Get, first after restart | 4.6 us | 4.4 us | 2.7 us | 0.75 us | 52 us |
| Heap after updates | 1.1 GB | 1.1 GB | 1.2 GB | 1.3 GB | 7.3 GB |

"Hot set": 90 percent of the updates on 1 percent of the keys. "Full
replay": startup distance 2e9, so no index node is written (level 1). The
load of 10M keys ran at 95,000 puts per second (186,000 for 1M); with 10
puts per transaction, 1M keys, 115,000 puts per second.

Findings:

* Startup stayed near 0.6 to 0.7 s for 20 MB in the measured 1.6 GB and
  an 18.5 GB stream; it grows with the startup distance, about 30 ms per
  MB (5.6 s for 200 MB). Full replay of 0.5 GB took 15.7 s. This is evidence
  of practical tail-limited recovery in these workloads, not a worst-case
  bound independent of tree size or transaction mix.
* The startup section stays near the startup distance: at most 1.36 x sd
  with single puts, 1.51 x with 10 puts per transaction, 2.21 x during the
  10M run. The fairness limit in TransSeq.take() lets it lag, but it
  caught up in every run (problem.md, Q4). Not a proven bound.
* Write overhead is the main cost. With uniform random updates, most
  updates hit a key node that is not yet dirty in the current section, so
  about one index node (about 360 bytes) is written per update of 104
  user bytes: 6 bytes appended per user byte at 1M keys and 9.9 at 10M
  keys, against 1.65 without index writes. A hot set or a larger startup
  distance brings it down (2.9 and 2.6). This is R4 and Q5 in problem.md,
  now measured: the overhead grows with the number of key nodes that one
  section touches once only.
* Throughput: index writes cost about 10 percent at 1M keys (102,000
  against 113,000 updates per second).
* Commit latency: the slowest commits, 120 ms with 1M keys and 260 ms with
  10M, are GC pauses, not index writes (they wrote 0 to 4 index nodes; G1
  log: a 119 ms young pause at the same time). With ZGC
  (`-XX:+UseZGC`), 1M keys: max 4.75 ms, p99.99 2.4 ms, 11 percent lower
  throughput. Commits that write many index nodes (at most 392 at 1M keys,
  923 at 10M) are not among the slow ones.
* Durable commits: one writer thread that syncs after every transaction
  gets 29 transactions per second, p50 35 ms each (9 a second, 116 ms,
  with the buffer time of 100 ms that was the default until 2026-10-20;
  bergdb item 005-13). This is the 2017 design, kept on purpose (Frans,
  2026-10-13): execute() only appends to a buffer, BufferedStream writes
  the buffer about every 20 ms (the buffer time, set per stream; the
  default is `StorageManager.DEFAULT_BUFFER_TIME`), and a sync waits for
  that write, so the transactions of many threads share one durable write
  (64 threads: 1,800 synced transactions a second). Writers that do not
  sync are as fast with 10 to 100 ms; one `F_FULLFSYNC` costs about 5 ms
  on F53 (005-13). An idle database does not wake: when nothing has been
  buffered for a buffer time, the storage thread waits for the next
  append (bergdb item 005-14; at 20 ms it woke about 160 times a second,
  0.3 percent of a core). The application chooses when to
  sync, and how (ORDINARY: the main storage; STRONG: also a replica, if
  there is one). Neither level flushes at once. For comparison, a sync that
  flushed at once (tried and reverted 2026-10-13) gave 13,000 to 18,000
  synced transactions per second, p50 47 us. These tests did not exercise
  power loss. Validate the OS, filesystem and device flush path on macOS
  and Linux, including whether the macOS path invokes F_FULLFSYNC when
  that drive-cache guarantee is required.
* Memory: all versions stay in memory, so the heap grows with the
  history, not with the live data: 1.1 GB for 1M keys after 2M updates,
  7.3 GB for 10M keys after 10M updates. After a restart, the heap is
  small (80 to 190 MB) and nodes are read on first touch, which is slow
  until the cache is warm (52 us per get at 10M keys, the stream in the
  OS cache). Level 4 (eviction) is needed for data larger than memory, and
  for long histories.
* Reads: about 1 us per get, warm, also at 10M keys; historical gets the
  same.

Default startup distance 50 MB (was 20 MB), 2026-10-13. Measured with
LoadTest as above, single-put transactions on uniformly random keys, and
the startup also timed in a fresh JVM (the same within a few percent; the
OS file cache was warm):

| Values, keys, updates | Startup, 20 → 50 MB | WE, 20 → 50 MB | Updates/s, 20 → 50 MB | Dirty set D, max nodes |
|---|---|---|---|---|
| 100 B, 1M, 1M | 0.78 → 1.35 to 1.45 s | 0.175 → 0.236 | 101,000 → 112,000 | 63,000 → 100,000 |
| 1000 B, 100,000, 400,000 | 0.30 to 0.33 → 0.63 s | 0.76 → 0.83 | 79,000 → 85,000 | 9800 → 14,000 |
| 10 kB, 10,000, 40,000 | 0.15 → 0.36 s | 0.97 → 0.98 | 15,000 both | 1100 → 1500 |

* Startup time follows the transactions rerun more than the bytes: about
  29 ms per MB with 100-byte values, 13 with 1000 bytes, 7 with 10 kB (15
  to 25 us per transaction rerun). A default given as a target startup
  time would fit all value sizes better than a byte count.
* Costs of 50 MB: startup about 2.1 to 2.4 times longer, the dirty set
  about 45% larger, and with reclaim the stream keeps roughly 60 MB more
  (the cut waits for the startup pos). A slower machine or disk may be 2
  to 5 times slower. Small devices need a much smaller value (1 to 5 MB).
* Existing databases keep the startup distance stored in their stream.


Bounds, measured
================

Measured 2026-10-17 for bergdb item 001, WP P3 (problem.md, R3 and Q4;
sis-model.md, sections 10 and 11; input for the reserve of Level 4's
capacity controller, J7), with [LoadTest.java](../java/stress/LoadTest.java)
as above: 1M keys of 4 bytes, values of 100 bytes, a load of 100 keys per
transaction, then 2M single-put transactions (uniform, or 90 percent on 1
percent of the keys) or 100,000 transactions of 40 puts, on a FileStream,
the default node size. Counted: the startup section, its length after each
transaction; D, sampled every 10,000 transactions, in nodes and in bytes in
memory (`Node.getMemSize`), the memory that eviction must keep (Level 4's
pinned set); and the index nodes written that are no longer current
(replaced by a split or a new super root, seen through `Db`'s test hooks),
and of those, the ones written again after a write since they were
replaced. The machine was not quiet (other checks ran), so the times here
are not a reference; the counts do not depend on it. All runs passed the
full check.

| Workload | Startup distance | Startup section, max | D, max | D in memory, max | Index nodes written per transaction | Of them no longer current | Written again since replaced |
|---|---|---|---|---|---|---|---|
| uniform, 1 put | 50 MB | 1.00 x sd | 90,000 nodes | 72 MB | 0.68 | 20.0 % | 11.0 % |
| hot, 1 put | 50 MB | 1.00 x sd | 72,000 | 49 MB | 0.28 | 46.0 % | 10.6 % |
| uniform, 40 puts | 50 MB | 1.22 x sd | 119,000 | 95 MB | 22.9 | 22.9 % | 10.2 % |
| uniform, 1 put | 5 MB | 1.67 x sd | 20,000 | 16 MB | 1.97 | 5.3 % | 4.6 % |
| hot, 1 put | 5 MB | 1.22 x sd | 7,600 | 5.6 MB | 0.40 | 32.9 % | 9.0 % |

Findings:

* The startup section stayed at the startup distance with single puts and
  the default 50 MB (at most 1.00 x sd), and went past it with 40-put
  transactions (1.22 x) and with a small distance (1.67 x at 5 MB, uniform):
  the take catches up a few transactions late, which matters more when the
  distance is small. Not a proven bound (problem.md, Q4).
* D, the memory that Level 4 cannot evict, follows the startup distance:
  at most 72 MB (uniform) to 95 MB (40-put transactions) at 50 MB, and 5.6
  to 16 MB at 5 MB, that is 1.0 to 3.2 times the startup distance in
  memory. A reserve of twice the startup distance covers the runs at 50 MB,
  not the uniform run at 5 MB (3.2 times): J7's reserve needs a floor in
  bytes, or a measure of D itself.
* The conservative still-dirty test (Rule A over all pointers,
  sis-model.md, section 11) writes nodes that are no longer current: 20 to
  46 percent of the index nodes written at 50 MB, most with a hot set, whose
  dead nodes share hot children. About 10 percent of all index node writes
  (4.6 percent at 5 MB, uniform) are of a dead node that had been written
  already since it died: its history no longer changes, and only its
  references to newer versions of its children do, which the reads it
  serves do not need (lemma M). The exact test (the model's `exactTest`,
  proved for structures without a virtual root) would skip them, but it
  changes the records; BergDB keeps the conservative test (`javaTest`).


Crash tests
===========

[CrashTest.java](../java/stress/CrashTest.java), INV-CRASH in
[problem.md](problem.md): random transactions with a small startup
distance (2000 bytes, so that index nodes are written and the startup pos
moves), then for each of 100 cuts per round: the stream cut at a random
position, or at, just before or just after the end of a transaction; the
database started from the cut stream and checked against a model, latest
and historical; 50 more transactions; a restart; the check again. Part of
level2.sh since 2026-10-13. The first run failed 2 of 3 rounds; after the
fixes below, 0 of 25. Since 2026-10-23 (bergdb item 005-27) also 20 cuts per
round at or next to meta block positions, and one at the end of each
transaction that ends where a meta block starts.


Bugs found by the load and crash tests
======================================

Fixed 2026-10-13, each with a unit test that fails without the fix. None
is in the level 2 work of 12 October; all are in the 2017 code.

1. Streams longer than 2.1 GB failed. Cache3.mapIndex() cast the hash of
   a node id to int before taking it modulo 256, which is negative for
   some ids of 2^31 and more, and node ids are stream positions:
   ArrayIndexOutOfBoundsException (without -ea) once the stream passed 2.1
   GB. Test: Cache3.testLargeIds.
2. Reads of bytes still in the write buffer returned other bytes, after a
   restart. BufferedStream started its buffer offsets at 0, but reads take
   stream positions, so for a stream that was not empty when opened, a
   read of the last bytes appended (before the flush, up to 100 ms) read
   the wrong part of the buffer. Found through crash recovery, which reads
   back the bytes it has just appended. Test:
   BufferedStream.testReadFromBufferOfNonEmptyStream.
3. A crash within the first bytes of a transaction's size could make the
   database fail to start ("Bad transaction size"). Recovery completes a
   torn size; it accepted a size of 6 or more, but NodeStream rejects a
   transaction shorter than 17 bytes. Test:
   DbTester.testCrash6TornSizeBelowMin, and
   RecoverableStream.testTransHeaderFixBytesBelowMin.
4. A sync could return although the data was not written. When an append
   to the underlying stream failed (an I/O error, a full disk, a closed
   file), BufferedStream counted the bytes as appended and told the
   storage manager so; a sync then returned normally, and the failure
   showed only at the next transaction. Frans's 2015 test
   DbTesterStream.testReadOnlyStream2 noted it ("why does sync() work?").
   Now the stream stops, the storage manager is told, and the sync throws.
   Also: a flush of exactly one byte wrote the wrong bytes. Test:
   DbTester.testSyncAfterStreamFailure.

Fixed 2026-10-21 (bergdb item 005-14), also in the 2017 code, each with a
unit test that fails without the fix:

5. A close could append the whole write buffer to the stream, and the
   database then failed to start ("Bad transaction size"). close() sets
   flushAndClose before it stops the storage thread; when the thread woke
   in between with nothing buffered, it flushed 0 bytes, and for 0 bytes
   BufferedStream.flushToStream wrote the whole ring buffer: stale bytes
   after the last transaction, 10 MB for the main stream. 34 of 24,000
   closes in a test of BufferedStream alone at a buffer time of 10 ms; the
   chance goes with how often the thread wakes, so at 100 ms it is about a
   quarter of that at 20 ms. Now nothing is flushed when nothing is
   buffered. Test: BufferedStream.testNoFlushOfNothingWhenClosing.
6. The storage thread's count of its wakes overflowed after 2^31 wakes
   without a write: 124 to 189 days at the buffer time of 20 ms, 1.7 to 2.2
   years at the former 100 ms. After it, the timer flushed nothing for as
   long again, and a sync waited until 2.5 MB were buffered. Now the count
   stops at 4. Test: BufferedStream.testWaitCountStaysSmall.

Fixed 2026-10-23 (bergdb item 005-27), also in the 2017 code, with unit
tests that fail without the fix; found by item 005-11's probes, in a
replica's crash image:

7. A crash that ended the stream exactly at a meta block's position, after
   a transaction that ended there, left a database that did not start
   ("spos >= streamSize"). The transaction's bytes and the meta block are
   two appends, and a flush can come between them. Recovery filled out a
   meta block that was partly written, not one that had not begun, and
   then stepped past the block, beyond the end of the stream. Now it fills
   out that block too; the block is invalid, as a partly written one is,
   and recovery takes the one before it. Tests:
   DbTester.testCrash7AtMetaBlockPosition and
   RecoverableStream.crashAtMetaBlockPosition; CrashTest cuts there too.

Fixed 2026-10-25 (bergdb item 005-40), also in the 2017 code from 1 to 127
bytes into a meta block (at 0 bytes since 005-27), with unit tests that
fail without the fix; found by that item's probes, from a TODO on the
format version:

8. A start with a wrong crypto key, or with none on an encrypted database,
   or with one on a database that is not encrypted, after a crash that
   ended the stream at or just inside a meta block, left a database that
   the right key could not start either ("Likely, the wrong crypto key was
   used", or a meta block of a version such as 60826). Recovery filled out
   the cut meta block, through the key it was given, before it read a meta
   block and found the magic bytes wrong; the right key then read garbage
   there. Now recovery reads the meta blocks first, and a stream that it
   cannot read, for its key or its version, is refused as it is. Tests:
   RecoverableStream.testRecoverWithWrongKeyWritesNothing and
   testRecoverOtherVersionWritesNothing, and
   PubTester.testWrongKeyAfterCrashAtMetaBlock.

Fixed 2026-10-25 (bergdb item 005-44), in the 2017 code, with a test that
fails without the fix; found by reading the code, in item 005-41:

9. A sync could return before the transaction's last byte, its commit
   byte, was written, and a crash then lost the transaction. A sync waited
   until the durable length reached the position of that byte; but a
   durable length counts the bytes before it, so the byte itself could
   still be in the write buffer. It was right only while the buffer wrote
   in parts that end at even positions, as it does when its size is a
   multiple of 4, as the Pub API's sizes are; with another size, set
   through the core API, a part could end just before a commit byte. Now a
   sync waits until the durable length is past that byte. Test:
   DbTester.testSyncWaitsForTheCommitByte, with a buffer of 2 S − 2 bytes
   for a record of S bytes; in 005-44's probe, a crash right after the sync
   lost the transaction in 10 runs of 10 before the fix, and in none after
   it.



The level 1 bugs
================

Both fixed 2026-10-12. [level1.sh](../java/stress/level1.sh) checks level 1,
including these bugs; it must pass before any change to the code is
committed.


1 A delete of a missing long key
--------------------------------

Deleting a key that does not exist broke the next restart
if the key is 7 bytes or longer. Reproduction:
[DeleteRepro.java](../java/stress/DeleteRepro.java), three transactions:

    java -cp build/bergdb.jar:build/stress bergdb.core.DeleteRepro /k/1000
    -> FAILED: StreamIoException: Cannot read 199631 bytes at position 369

Cause: a key of 7 bytes or more has two or more key segments
(Keys.toSegments). Dag.putKv() called setNode() for each segment but the
last, which created a missing segment key node before the delete found that
there was nothing to delete. The delete is a no-op, so no value node is
stored and the rerun does nothing; but the original run created a node and
used up an id. After the restart, ids differed from the original run ("A
ValueNode cannot be dirty"), and the empty node was later written to the
stream ("Key node with size 0").

Fix: a delete does not create segment nodes. Dag.putKv() calls setNode()
with create = false for a delete, and returns if a segment node is
missing: the key does not exist, and the delete is a no-op, as it already
was for keys of one segment. Two unit tests, both failing before the fix:
DagTester.testDeleteMissingKey (a no-op delete creates or changes no
node) and DbTesterRestart.testDeleteMissingLongKey (two restarts after
such deletes). All 857 unit tests pass with the fix.

The fix also removes the "Key node with size 0" failures at level 2 with
the experimental patches E1, E4 and E6 (startup-invariants.md, section 5).


2 Two new space roots in one transaction
----------------------------------------

A historical lookup could miss part of a transaction, or all of it, after
a transaction that replaced the space root twice: for example a time split
of the root, and then, when later keys of the same transaction fill the new
root, a space split of it. Found as "the node size 8 bug": with 8 klongs per
node, a transaction of a few keys is enough. With the default size 30, a
transaction of about 20 keys among few distinct keys is enough (DagFuzz);
RestartStress, with at most 40 keys per transaction, found it only for
sizes 8 and 14.

Cause: each new space root gets a new top node in TopDs, with the
transaction time as its root time. Two new roots in one transaction gave
two top nodes with the same time; the first points to the root as it was
before the rest of the transaction. TopDs.findSuperRootAtTime() assumes
strictly increasing times: it follows the skip list to the right-most top
node with time >= t, and with equal times this can be the first of the two.
It shows only after a later top node has a skip pointer past the second one.

Example (DagFuzz seed 1666, node size 8, 10 keys, no deletes): in T3, time 30, the
root is time split (top node 1, time 30) and then space split (top node 2,
time 30). Lookups at time 30 use top node 2 until T6 adds top node 3,
whose skip pointer leads to top node 1, whose root lacks /k/0, put by T3
after the first split.

Fix: TopDs.newSuperRoot() checks whether the super root has the same time
as the new root. It was then created by this transaction, so it is not yet
written and no reader uses its root pointer (readers have lookup times
before the transaction). Its root pointer is set to the new root instead of
creating a top node. Top node times are now strictly increasing (asserted).
Unit test, failing before the fix: DagTester.testTwoNewRootsInOneTransaction
(one seed each for node sizes 8, 14 and 30). All 858 unit tests pass with
the fix.

A stream written by the old code with two top nodes of the same time gets
other node ids on a rerun with the new code, so it may not restart
correctly with it (not tested). No such streams are in use.


The level 2 bugs
================

Fixed 2026-10-12 and 13, each with a unit test that failed before the fix.
Of the 2017 code: the cache, keyed by id, could return an older version
than a pointer named; cache hits skipped the pointer listener; startup
forwarded pointers only along prevPos chains; D could hold a copy of a
node; the still-dirty test did not see nodes in D through stream pointers;
a parent could be written with an old position of a child written in the
same record; top nodes lost skip pointer times when written again, and a
new top node depended on whether skip pointers were in memory; and value
node padding was not written. Found while fixing them: Db and
NodeCollection had a node table each; nodes created in the startup section
got their vpos as spos at startup; nodes in D that the rerun does not
reach; and the meta block's last transaction position after a restart. See
[log.md](log.md).


Bugs found by the alignment of Levels 3 and 4
=============================================

Bergdb item 001 (`items/001-lean-model-levels-3-4/`). Each fix has a unit
test that fails without it.

1. Top node ordinals from 32,768 on were written wrong (fixed 2026-10-16,
   WP A3; found by F1-008-13, section 5.1, in the f1 repository, and
   measured end to end by its review). `StoredTopNode.toLongs` shifted the
   ordinal as an `int` before widening it, so the stored ordinal was its low
   16 bits, read as a signed number. A database whose newest written top
   node had an ordinal with bit 15 set could not start ("Bad TopNode ID");
   from 65,536 on, with bit 15 clear, it started silently wrong, with the
   ordinal modulo 65,536 and the wrong height, lost most of its history, and
   went on writing wrong ordinals. One key updated in every transaction
   makes a new top node about every 15 transactions at the default node
   size: 32,768 top nodes in about nine days at one update a second. Now the
   ordinal is widened first, and the parser refuses a top node whose skip
   pointers do not fit its ordinal (as many as its height, set exactly at
   its set bits), so a stream that was written wrong is refused, not read
   wrong; such streams are not repaired. Streams whose top node ordinals are
   all below 32,768 are unchanged, byte for byte. Startup also checks,
   without `-ea`, that the newest written top node is the super root at the
   startup time. Tests: `StoredTopNode.testOrdinalsRoundTrip` and
   `testParserRefusesSlotsThatDoNotFit`;
   `DbTesterRestart.testRestartAfterManyTopNodes`, about 131,000
   transactions past ordinal 32,768 and a restart, 1.5 s.
2. Top node ordinals were bounded by 2^30 − 1 over a database's life
   (fixed 2026-10-19, bergdb item 005-02; register M46, found in WP A2 from
   review-13-claude; studied in bergdb item 002, 002-02). Every change of the
   space root makes a top node, at most one per transaction, and reclaim does
   not bound the ordinals. With eviction on, memory no longer stops a
   database first: a few hot keys at 1,000 transactions a second would reach
   the bound in about six months at node size 30 and in five to seven weeks
   at node size 8, a soak at full speed in 15 to 29 hours. At the bound
   `TopNode` threw in the middle of a root split: wrong reads, and once one
   more transaction committed, the database could not start again. Now the
   ordinal is a `long` in the 48 bits that the stream already had for it
   (bytes 10 to 15 of a top node; the reader read 32 of them): no format
   change, the same bytes for every ordinal below 2^30, and older code
   refuses a top node with a larger ordinal with an error. 2^48 lasts
   centuries at the fastest rate measured, past the end of the database
   clock (2198). Near the end, a user transaction is refused before it
   changes anything (`DbException`, when the super root's ordinal is 1,024
   below the bound; reclaim's internal transactions use that margin), and
   the database can still be read and restarted. Tests:
   `DbTesterRestart.testOrdinalsAcrossBoundaries` (2^30, 2^31, 2^32 and
   2^47, with restarts that read the top nodes or make them again, and with
   eviction), `testOrdinalsWithReclaim` (across 2^32 and to the end, with
   cuts and restarts) and `testEndOfOrdinals`;
   `StoredTopNode.testOrdinalField`. A test-only option,
   `DbBuilder.secondTopOrdinal`, starts the ordinals near a boundary.
3. The node table could get back an object that eviction had just released
   (fixed 2026-10-20, bergdb item 005-09; register M31; found in 005-02,
   where `EvictionReaderTester.testReaderPausedInsideAFollow` failed about
   once in 600 runs under load). A reader that follows a stream pointer to
   a canonical object enters it in the node table (`Cache3.pointerCreated`).
   It read the canonical flag before it took the table's lock, and a sweep,
   which readers do not wait for, could release the object in between: the
   flag cleared, the entry removed. The reader then entered the released
   object, a snapshot, which INV-CAN forbids. The audit failed ("INV-CAN:
   the node table names a snapshot of node N"); readers that followed a
   stream pointer to the node loaded it from the stream again, as the
   table's object was not canonical, until the writer made an object of the
   node canonical again. The records, the answers and the one canonical
   object per node were as without eviction. Now the flag is read again
   under the table's lock, and a release clears it under the same lock
   (`Cache3.released`), so that the check and the entry are one step
   against a release. No record changes. Test:
   `EvictionReaderTester.testReleaseBeforeTheTableEntry`, in which a hook
   (`Cache3.EntryListener`) runs a sweep just before the reader takes the
   lock.
4. A transaction that threw after it began was half committed (fixed
   2026-10-22, bergdb item 005-01; register M49, found in bergdb item 002,
   002-02, section 8, and studied in item 003): its time became readable
   with its first puts, and the next transaction wrote its nodes as its own.
   Now the database fails, and a restart rebuilds it from the stream; see
   "A transaction or a read that fails" above.


Level 4: eviction
=================

Alignment with the Lean model: [level4-alignment.md](level4-alignment.md)
(bergdb item 001: the model, sections 5 and 6; the Java work, section 7).
Evidence of a database larger than memory:
[level4-evidence.md](level4-evidence.md); performance:
[level4-performance.md](level4-performance.md).

Since 2026-10-18 the database keeps only part of its index and values in
memory: eviction is on by default. The budget is `cacheSizeInMb`
(`DbBuilder.cacheSizeIndicator`; by default a fifth of the JVM's maximum
heap); `DbBuilder.noEvict()` turns it off.

How it works (`core/Eviction.java`, `core/Residents.java`):

* **What is in memory.** The resident objects: the canonical object of a
  node (the one in the node table, which holds the node's latest version),
  the snapshots that slots of resident objects name (versions read), and
  the values. `Residents` counts their bytes (`Node.getMemSize()`), exactly
  after each sweep (a walk from the super root, the node table and D).
* **What is pinned** (never evicted): the super root, the canonical objects
  of D (the nodes dirty since the startup position) and of the record being
  written, and the newest written top node. Everything else has been
  written and may be evicted.
* **Unswizzle and release.** A memory slot to an object that may be evicted
  becomes a stream slot naming the object's position, under the slot's
  pointer lock; the slot's serialized reference does not change, so no
  record does. An object that no resident memory slot names is released:
  it leaves the node table and the registry, and a canonical object's flag
  is cleared. A later read loads the version from the slot's position (the
  Level 4 loader, R8), and the writer makes it canonical again.
* **The capacity controller.** When the resident bytes pass the budget, at
  a transaction boundary or after a reader's load (the reader takes the
  write lock for it, holding no pointer lock), a sweep takes what only the
  node table holds, then values (those over 1 MiB first), then index nodes,
  the slots least recently followed first, down to three quarters of the
  budget, counting the objects that leave memory with those it takes; if
  that is not enough, every object that may be evicted. Pinned state above
  the budget is kept and counted; the next sweep then waits for growth.
* **Readers** (the plan's Q8) take a slot's pointer lock for a whole follow,
  so they see a slot as a memory slot or as a stream slot, never half of
  one; a reader may finish with an object that was released meanwhile, as
  it is the version at its position, but enters it in the node table only
  if it is still canonical under the table's lock (bergdb item 005-09).
* **Reclaim** reads with the maintenance follower, which loads but
  swizzles nothing; a step's dirty index nodes stay pinned until written,
  and a reserve (4 MiB) splits a step that would pin more.

Evidence: the Lean model proves that with any eviction schedule the
records, D and the answers are those without eviction (T-CACHE, T-READ,
T2-C, T-PIN; level4-alignment.md, section 5). Java is checked against it:
the audit (INV-CAN, the pins, INV-SLOT, test-only), the checker's C-P on
Java's physical states (`conformance.sh evict`), and `EvictionInvariance`
(the same stream byte for byte with every schedule, on the configurations
of the plan's 8.4, with restarts and reclaim). `level4.sh` runs them, with
stress under eviction and a larger-than-memory run.

Limits (level4-evidence.md, level4-performance.md): writes when the index
does not fit cost several times as much (each load reads the node's header
and then the node); a sweep walks every resident object under the write
lock, so when readers load a working set above the budget the sweeps stall
the writer (P2's soak with eviction: 35 percent of the time, the paced
writer at 62 percent of its rate) and G1 needs full collections; the node
table's entries are not in the budget; D is bounded only loosely by the
startup distance.


Next
====

Keep level1.sh, level2.sh and level3.sh passing. The first goal is a
working, performant database (2026-10-13); theory where it reduces risk.
Index-aware budgeting and the 16 KB scan target are now part of the
reviewed `ebe5f77` baseline; the remaining work is below.

1. Levels 3 and 4 are done for now (bergdb item 001, 2026-10-18): the
   power-loss ordering ([level3-durability.md](level3-durability.md)), the
   disk soak ([level3-soak.md](level3-soak.md)), the performance reference
   ([level3-performance.md](level3-performance.md)), eviction, and both
   levels aligned with the proved Lean model
   ([level3-alignment.md](level3-alignment.md),
   [level4-alignment.md](level4-alignment.md)). Infinite retention remains
   the default; eviction is on by default. Protected snapshots and an expert
   f controller remain optional work; that Java's reclaim scheme gives safe
   cuts is checked at every cut, not proved (T-SCHEME).
2. Level 4's limits ([level4-evidence.md](level4-evidence.md)): a load reads
   the node's header and then the node (the id could be kept in the
   unswizzled slot); a sweep walks every resident object, which under read
   churn costs a third of the time (P4: incremental sweeps, or Q9's
   incoming-reference lists); the node table's entries are not in the
   budget; D is bounded only loosely by the startup distance (R6, Q5).
3. Write overhead with uniform random updates (6 to 10 bytes per user
   byte): measure where the bytes go (key node size, time splits, the
   conservative still-dirty test), and what a larger default startup
   distance would cost in startup time. `Reclaim.Stats` now counts the
   records by writer and content (user, reclaim steps, table; values, index
   nodes); the same counters can answer this for the user records.
4. Theory: extend the Lean model to the Java algorithm; the bound on the
   startup section (Q4).
