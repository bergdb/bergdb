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

| Level | Features | Status, 2026-11-04 | Evidence |
|---|---|---|---|
| 0 | Multiversion map in memory: puts, deletes, latest and historical lookups, scans; no restart | Passes the tests run | 011-04, "Evidence" |
| 1 | + restart by replaying the whole stream | Passes the tests run | `level1.sh`; 011-04, "The level 1 bugs" |
| 2 | + bounded startup: startup reads only the tail of the stream | Passes the tests run, also under load and with crashes; aligned with the proved Lean model | [011-11](../items/011-docs-archive/11-level2-alignment.md); 011-04, "Level 2 under load", "Bounds, measured", "Crash tests" |
| 3 | + reclaim: cut the front of the stream | Passes the tests run, a two-hour disk soak and the power-loss ordering checks; aligned with the proved Lean model of reclaim | [001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), [001-09](../items/001-lean-model-levels-3-4/09-level3-soak.md), [011-07](../items/011-docs-archive/07-level3-durability.md); 011-04, "Level 3 cost" |
| 4 | + eviction: data larger than memory | Passes the tests run; on by default; with handles since 2026-10-26, eviction in bounded steps, without a stop-the-world of its own; a database six times its memory budget runs on disk; aligned with the proved Lean model, with handles | [009-05](../items/009-handles/05-handles-alignment.md), [001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), [001-10](../items/001-lean-model-levels-3-4/10-level4-evidence.md), [009-03](../items/009-handles/03-measurements.md) |

Each level includes the ones before it; Level 3 needs Level 2, as startup
cannot replay a stream whose front is cut. BergDB has no replication
since 2026-11-04 (section 9). What BergDB is to do, the requirements R1 to
R7 and the invariants INV-LOOKUP, INV-RESTART, INV-CRASH, INV-RECLAIM and
INV-EVICT, is the problem statement, [011-01](../items/011-docs-archive/01-problem.md);
its design principles are [010-01](../items/010-principles/01-principles.md).
The Lean proofs concern the abstract model, which includes reclaim and
eviction; Java's runs are checked against it, not proved, and concurrency
and resource bounds are not in it.

The levels are the Core's. The Pub API's other part, objects (values
that are neither a `String` nor a `byte[]`) and user indexes, with the
primary scan, is section 11: experimental in 2026.3
([018-01](../items/018-release-2026-3/01-plan.md), D2 and D6), redone for
2026.4 as part of the API that a release promises.

The Core Layer is a simple key-value datastore: both keys and values are
byte arrays, with transactions and history. It knows nothing of objects or
user indexes: to it an object is a byte array, and an index's definitions
and entries are keys like any other, under `/#i/`. Objects and indexes are
the Pub layer's (`pubimp`), built on the Core's four data methods
([010-01](../items/010-principles/01-principles.md), P12).


## 2. Checks

* `java/before-commit.sh`, the unit tests and the f-tests (about 2
  minutes), must print `BEFORE COMMIT OK` before a change to the Java code is
  committed. Since 2026-10-20 it is the only requirement (006-03). Before
  the tests it checks the packages' dependencies against their
  `package.html` (`deps.py`, 005-56) and that no double or float decides
  anything in the Core Layer (`doubles.py`, 005-79). With the tests it runs
  the demos of `src-dev` on small sizes (since 2026-11-09).
* The level scripts in `java/stress/` are deeper checks, run after larger
  changes; each prints `LEVEL n OK`, and its header lists its steps.
  `level2.sh` to `level4.sh` need Lean (elan) for their conformance steps.
  * `level1.sh`: the unit tests, DagFuzz, RestartStress with restarts by
    full replay, RestartInvariance (the same stream, byte for byte, with and
    without restarts: T2), and the Props limits (MEM, the keys' shape of
    section 4, and SS).
  * `level2.sh`: RestartStress with bounded startup in random
    configurations, RestartInvariance, CrashTest (INV-CRASH), BryanRepro
    (the bug report ISSUE151111 of November 2015), and the conformance with
    the Lean model: A2A3Check2, and the trace checker on the small set.
    Since 024-09 both also run draining configurations (mostly deletes on
    few keys, and many small segment trees that come and go), which must
    reach the delete path's take-back: one that takes back no node fails
    the step. The trace checker's are `conformance.sh drain`. The step
    also compares Java's take with the model's (`TakeCheck check`).
  * `level3.sh`: the unit and f-tests, ReclaimStress, RestartInvariance and
    CrashTest with reclaim, ReclaimReaders (readers while cuts are made),
    LoadTest with reclaim (full only), PowerLossTest, and the conformance
    with reclaim.
  * `level4.sh`: the eviction tests, EvictionInvariance (the same stream
    and answers with every eviction schedule), RestartInvariance, CrashTest
    and ReclaimStress under eviction, ReclaimReaders, `conformance.sh evict`
    (C-P and C-H), and LargerThanMemory, on disk in a capped JVM.
* `java/night.sh` runs on a clone of the committed code: the check before
  a commit, the Core Layer built alone (`stress/core-build.sh`), the four
  level scripts, the night tests, the fuzzers (`stress/fuzz.sh` of the
  readers of bytes; since 024-09 `stress/unlinkfuzz.sh`, UnlinkFuzz on the
  Dag's delete path, which no level script runs) and the medium conformance
  set. It has no fixed time; it is started when the machine has room for
  it. Its report is in `java/build/night/`.
* `cd lean && lake build` checks every proof of the model. The trace
  checker reads traces in the format of [trace-format.md](trace-format.md).


## 3. A transaction or a read that fails

Since 2026-10-22 (005-01) and 2026-10-23 (005-30); the error model since
2026-11-06 (019-10). The design is Frans's, from the start: no rollback of
in-memory state, and a database whose environment has failed, or that has a
bug, does not run on.

**Errors.** BergDB assumes a sound environment: correct storage, a stream
that returns the bytes appended to it, and enough memory and stack for its
work. Its checksums and checks find some damage of the stored bytes, not
all: they are a best effort, and damage that passes them gives wrong values
with no error. Only a cut tail, as after a crash or a power loss, is
recovered. BergDB does not try to recover when the environment fails; the
database fails instead. That happens on:

* an I/O error or corrupt data in the storage;
* an unexpected exception from the storage's stream;
* an `Error`, such as `OutOfMemoryError` or `StackOverflowError`, thrown
  during a read, a transaction or a sync, also in the application's code
  that it runs, or on one of the database's own threads;
* any exception after a transaction's go point, as nothing there is undone;
  and an exception of a Core API key transformation, which must not throw:
  it runs just before the go point, after the transaction's time is taken
  (024-16), and fails the database as when it ran after it.

A failed database does no more work. The call that met the failure throws
it: an `Error` as it is, anything else as a `DbFailedException`. Every later
read and transaction throws a `DbFailedException` with the first failure as
its cause, and nothing more is appended. Transactions that a `sync()` has
returned for are safe; `stop()` and `close()` still work, and so does
`sync()` while the storage does. The application should then end its
process; the next start recovers the database as after a crash. For
`OutOfMemoryError`, the JVM option `-XX:+ExitOnOutOfMemoryError` ends the
process at once, and that is the advice: while the heap stays full, BergDB
cannot promise even to fail cleanly (the JVM itself may need memory to
record the failure), so a `sync()` or `close()` may then wait (019-39).

Everything else the database throws fails only that call, and the database
goes on: a transaction refused before its go point, a lookup time no longer
available, a bad argument. The conversion of a read value to the
application's object (the Pub API) is not the database's read: what it
throws, an `Error` too, fails only that call.

The details:

* `Db.executeInner` has a go point. Before it, everything that may refuse
  the transaction is checked, and nothing is changed: the STM check
  (`RerunException`), the end of the top node ordinals (005-02), the size of
  the transaction (005-17), the index nodes it can make dirty (005-31), the
  clock (005-18), whose last 1,024 times are kept for reclaim's internal
  transactions after a user transaction (015-55), and, last, two of its keys
  that its key transformations (the Pub API's key replace) make one key
  (024-16: a `DbException`; the transaction's KVs, its time and the clock
  are given back). The Pub API runs the application's code before it too.
  A refused transaction leaves the database as it was, and it goes on.
  The size check counts a Core API value transformation's input: its
  result, made after the go point, must keep the transaction within the
  limit, and one whose record does not fit fails the database, as a
  transformation that throws does (015-51).
  The STM also refuses a read set whose snapshot predates the last
  recovered commit at startup: its in-memory write history cannot validate
  it (005-70). A snapshot at that commit is covered. RW read dependencies
  must be collected on the same running `Db` instance as the commit;
  after reopening, reread and recompute. Normally the reads are within
  about one second of the current time (guidance, not an enforced timeout;
  010-P2). The timestamp check does not establish the read set's origin.
* After the go point nothing refuses the transaction and nothing is undone.
  Whatever throws there (the environment or a bug: a read error or a
  corrupt node when a put loads an index node, an append error, an `Error`,
  reclaim's work after the transaction) fails the database
  (`DbState.FAILED`), as above.
* What a read may see of a transaction that fails after its go point
  (015-27; the same in 2026.1). The transaction's time becomes a lookup
  time when its changes are in memory (`dbClock.transactionEnd()`), before
  its record is appended (`store()`) and before the steps after it: the
  statistics, eviction, the audit and reclaim's work. A failure while the
  changes are made (`putKvs()`: a read error or a corrupt node when a put
  loads an index node) comes before that, so the time never becomes a
  lookup time, and a read sees the state before the transaction. After a
  failure in a later step, an append error above all (in practice while
  the append waits for room in the write buffer and the storage then
  fails): until the database has failed, a read at the latest lookup time
  can return the transaction's values, and after a restart they are gone
  unless the record was appended before the failure. A read of a
  transaction that is not synced risks the same in a crash (section 8);
  no transaction that a sync has returned for is lost. This is intended
  (015-27, Frans, 2026-11-05): durability is `sync()`'s promise, not
  visibility's.
* A read or a sync that fails on the storage fails the database too (since
  005-30): an I/O error, an unchecked exception of the stream's read
  (019-10), or corrupt data (a checksum or format error), in `getOne`,
  `getMany`, `getTrans` (`transactionInfo()`) and `sync()`. Not failures: a
  read that a cut has overtaken expires with a
  `LookupTimeNotAvailableException` (section 6), and so does `getTrans` of
  a transaction that reclaim has removed; the database goes on. A read or
  a sync while the database stops throws as it did.
* An `Error` (019-10, Frans, 2026-11-06): the calls that read, write or
  sync (`getOne`, `getMany` with its `StopCondition`, `getTrans`,
  `execute`, `sync`, `setCacheSizeIndicator`; in the Pub API also a
  transaction, whose `Action` runs before the Core's `execute`) catch it at
  their edge, fail the database, and throw it as it is. BergDB's own
  threads (the storage thread, eviction, the cut's file deletion, index
  jobs) fail the database on anything that ends their work; the cut's file
  deletion fails the stream, and the database fails when the storage next
  uses it (a flush, a read of the stream, a sync), so reads served from
  memory go on until then (019-40). An index job's
  refused transaction or expired read is not a failure: the job waits as
  after a conflict and takes its step again (019-38). Any other exception
  of an index build that is not an `Error`, such as an object it cannot
  index (a null indexed `String`), ends the build as failed, its status
  says so, and the database goes on; a start takes the build again, and
  the index can be deleted (019-42). A start that
  throws stops the database instead (005-32). Before, an `Error` before a
  transaction's go point, as in a read, passed through, and the database
  went on.
* A write of the storage thread that fails (a background flush) fails the
  database at the next call (015-35, 2026-11-05): a transaction, a read or
  a sync throws as above, also a read served from memory. Before, the
  database stayed active until a call met the failure on the storage.
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
* The next start recovers the database. The stream holds whole records
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

**The keys' shape and the heap** (024-08; 024-15). A key is cut into
segments of 7 bytes (`Keys.toSegments`; a key of exactly 7, 14 or 21
bytes ends with an empty segment, so that a klong of 7 bytes points to a
tree and a shorter one to a value), and the keys that share their first j
segments are in one segment tree, whose root is a key node. So the index
holds a tree for each distinct prefix of 7, 14, 21 bytes that keys of
that length or more have, and a prefix that only one key has, the whole
key included when it is that long, is a key node for that key alone:
about 226 bytes of heap (the node, its three arrays of 2 places, its
handle and its entry in the node table), where a KV whose key shares its
prefixes costs about 130 in all with an empty value. With everything in
memory (`noEvict()`) and keys put in key order, the heap above the empty
database's is at most 131 K + 230 T + V bytes: K the KVs, T the segment
trees beyond the first segment's, V the values' byte arrays; in random
key order K's constant is about 181, the splits' history. A random key of
L bytes, such as a UUID, has L / 7 such trees, rounded down: at 1M keys
of 36 random characters 1,305 bytes a KV, of 6 random characters 181.
With eviction the heap stays near the budget for any key shape, and the
one-key nodes cost stream bytes and reads instead: at 3M keys of 32
random hex digits, 3.6 times the stream a put of keys that share their
start, and 5.6 nodes read a get against 1.2 (024-08, section 8). `level1.sh` checks the two constants with
`bergdb.dev.props.Mem`: MEM, 1M keys of 1 to 6 bytes, at most 131; SEG,
MEM with 1M keys of exactly 7 bytes minus MEM, at most 230; and, in its
full run, MEM with 10M keys `/k/%010d`, which share their first 7 bytes,
at most 131, so that no term grows with the count. Frans counts this cost
within release 2026.5's aim 3 (024-04, log of 2026-11-11), so it is
documented and bounded, not fixed; `Connection` and `Db` give users the
advice: keys that share their prefixes.


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
  format 7 since release 2026.5, which refuses the format 6 of 2026.4
  and the format 5 of 2026.1 to 2026.3; 024-21, 023-07, section 5.8);
  the rerun of the section's transactions;
  D rebuilt from the
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
  Since format 7 it also reads the siblings that the rerun's merges read,
  up to two a level of a delete's path (024-21; not measured: 024-11's
  TU9).
  Before replay it validates record order and the 56-bit range of record
  times in the startup section, and increasing times within its stored
  key nodes; violations are refused as stream format errors (005-75).
* Marking: the index nodes that an operation (a put or a delete) follows,
  creates or changes get dirty when the operation ends, and only if it
  changed something; a node that the transaction replaced leaves D at its
  end. These are the nodes that the model marks (T13). A sibling that a
  merge reads is not marked (format 7, 024-21): it is left out, or stays as
  it is.
* A delete (`Dag.deleteUpward`, since format 6; 023-07, sections 5.1 to 5.3;
  023-09, section 2): if the key's segment leaf keeps a live key, the delete
  is a delete bitmap of the transaction, as before. Else the writer climbs
  to the first node above that keeps a live key, changing nothing until it
  is found, and unlinks each node below it on the path: a node that a split
  of the same transaction made is taken back (its parent's klongs of the
  transaction that name it, deleted ones too, point again to the node it
  replaced, and it leaves D, the record and the node table); an older one is
  unlinked. In every inner node the smallest live klong is the empty key
  (LE-b): a space split of an inner node gives its second half the empty key
  first, and where the climb stops at the empty key's klong, the next live
  child takes its place, so no node off the path changes. Then root
  collapse: while a segment tree's root is an inner node with one live
  klong, its child takes its place. A space split in place of a segment root
  that the transaction made points the segment leaf's klong to the new root,
  without a second klong (023-09, section 2, fault 12).
* Merges at the delete (`Dag.mergeAfterDelete`, since format 7; 024-21;
  024-11, section 5): after the delete has changed a node, while that
  node is not the root of its segment tree and holds fewer than m live
  keys or children (8 at node size 30), it is merged with a sibling
  under the same parent (the left one if both fit in c, 17 at 30, else
  the right one, or the left one if there is none): their live klongs
  make one new node, or two of half each if they are more than c, and
  the parent's klongs point to them (a bitmap of the transaction deletes
  the right one's klong, unless a second new node starts at its compare
  value, behind the parent's time klong); the two nodes are left out as
  a split's replaced node, or taken back if the transaction made them.
  A merge into one node takes a live klong from the parent, which is
  checked in turn; then root collapse. So after every transaction every
  key node but a root holds at least m live klongs (024-11, BU1), and the
  key nodes are at most S + (n + S - 1) / (m - 1) for n live keys in S
  segment trees: a function of the live keys, with any retain duration.
  A delete therefore empties only a root; the climb above starts there.
  The thresholds are constants of format 7 (024-14, QT1: m = 8, c = 17,
  and a split keeps a last version of up to h = 17 klongs, 2026.4's 15,
  at node size 30; v B / 30 at another node size, m at least 2, no
  merges below 8; `Dag.minFill`, `mergeCap`, `splitAbove`). The rerun of
  a record does the same.
* At most theta dead klongs a key node (option 2 of 024-18, since format
  7; 024-23): a klong is dead when the node's last bitmap deletes it or a
  later klong of its compare value follows it. Before each write to a
  key node (a put's klong, a delete's bitmap, the transaction's own
  bitmap changed in place, a split's or a merge's klongs in the parent,
  LE-b, root collapse) the writer counts the dead klongs the write adds;
  if the node would then hold more than theta (`Dag.deadFull`), it is
  full, and rule O replaces it by its last version with the write
  applied: one node always (a time split, in place for a node of the
  transaction), as the node had room for the write; a node without room
  is full by its size first. So after every write a node holds at most
  theta dead klongs (024-23, TP39; checked by `Dag.checkFill`), where the
  merges alone allow B, and reclaim's rewrites, which are puts, compact
  the cold leaves that they take above theta. A compaction keeps every
  live klong, so the fill (m, BU1) does not change. theta is 7 at node
  size 30, 7 B / 30 at the others, at least 1, none below 8 (`Dag.theta`;
  024-14's QT2 open).
  `Dag.dirtyNodeBound` counts one overflow at least for a node that its
  klongs can take above theta. The rerun of a record does the same; no
  field.

Alignment: [011-11](../items/011-docs-archive/11-level2-alignment.md)
maps Java's state to the model's (section 2) and keeps the register of
where they differ. The trace checker runs the model's own `init` and `step`
on traces of Java runs: every transaction must be a step of the model with
its assumptions met (A2 to A5, TREE, A6', A-COPY), every restart invisible,
and every first touch after a restart must follow the model's rule (C-L).
Since 024-09 the gates require A6 itself, not only the model's A6': no
trace and no run of A2A3Check2 may adopt a node below its old parent.
`level2.sh` runs it on the small set, `night.sh` on the medium set.

The key tree itself (puts with their splits, the delete path, gets, scans,
reclaim's touch) is a Lean definition since 2026-11-11 (`lean/SIS/Tree`,
[024-12](../items/024-release-2026-5/12-tree-model.md)): `treeSpec`, an
instance of the model's structure whose transaction is the tree's own, where
the trace checker takes each transaction's change from the trace. The tree
checker (`lake exe treecheck`, `java/stress/treeconf.sh`; step 8 of
`level2.sh`) runs it against traces of Java runs: each transaction's change
(every node made, with its id, and every klong of every changed key node),
the answers of gets and scans and the touch must be the model's, and the
tree's invariants must hold; and the model's own run from R(0), its `step`
with the tree's change, given of Java's run only the operations, each
transaction's first node id and the startup positions, must write Java's
records and keep Java's D. Its properties (the invariants, the multiversion
map, the model's assumptions for the tree, `dirtyNodeBound`) are stated in
Lean, and not proved but for four small ones.

Limits:

* The bound on the startup section is proved in Lean for a startup pos
  policy that keeps up with a distance (T3,
  [007-01](../items/007-bounds/01-startup-bound.md)), and for BergDB's own
  take, with any share (`T3_take`,
  [007-08](../items/007-bounds/08-step4-take-in-lean.md)): the section
  without its last record stays below twice the startup distance, and
  after a decrease of it, it shrinks with every commit until it is below
  twice the new one, and then stays below it, by the deadline at the span
  ([007-03](../items/007-bounds/03-plan.md), step 3 and D4). The proof
  leaves out the record limit, which can stop a record from taking what is
  due. It leaves out the stream's meta blocks too, but they make no
  difference to the take: when it runs, the stream's length (`getLength()`)
  is where the new record begins (`getNextPos()`), as a meta block is written
  with the record that ends at its position
  ([005-68](../items/005-todo/68-fix-take-stream-length.md)). The model's
  take gives Java's startup pos on 300 generated cases. Its share and
  dither are Java's, in integers, in units of 2^-16 (005-79; in the model
  since 024-09, which did 015-03), and `level2.sh` compares the two sides
  on the 300 cases and on the share's and the dither's numbers
  (`TakeCheck check` with `lake build`). Until 005-79 both were the double
  rule of 2026-10-28, which over 3 million of TakeCheck's cases differs
  from the integer take in 13, each taking one transaction fewer
  ([lean/README.md](../lean/README.md)).
  `T3_take` holds for any share, so the bound covers both. T3 is not all of
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
  order within a record (M6, M9); bytes as a function of the stream (M10).
  The physical layer's assumptions (M47) were argued too until 024-09:
  they are proved from the assumptions that C-A checks on every trace
  (A2 to A5, TREE) and from the checker's reading of a node's entries
  ([lean/README.md](../lean/README.md)).


## 6. Level 3: reclaim

Reclaim cuts the front of the stream, so that the stream does not grow
forever. It is on when a retain duration R is set
(`Db.setRetainDuration`, `Database.setRetainDuration`); the default is to
retain forever, as since 2013. R and the internal fraction are kept in the
stream (015-87): a setter call that changes one commits both in reclaim's
internal KV `/#i/dreclaim/-settings.txt`, a start reads it, and the steps
rewrite it like any live value; a stream without it has the defaults
(forever, and a quarter). There is no builder value. Lookups work for
every time in [now - R, now]; the first available lookup time is the API's
actual frontier, and increasing R cannot restore history already cut.

How it works (`Reclaim`; the class comment has the details):

* An iteration starts at an external transaction when the stream has grown
  by more than twice the startup distance since the last one started, and a
  quarter of R has passed (R / `ITERATION_DIVISOR`, in integers since
  005-79). pStart and tStart are the stream length and the time then; the
  cut point pCut is the previous iteration's pStart.
* Each external transaction allows a step while the bytes charged so far
  are below a quarter (`internalFraction`, 16,384 units of 2^-16;
  `fractionOf`) of the stream's growth since pStart; the charge counts the
  value nodes rewritten and the index nodes made dirty. A step scans at
  most about 16 KB of KVs at tStart, with maintenance reads that swizzle
  nothing; in one internal transaction it rewrites each live value
  stored before pCut: a put of the same key and value, which makes the
  index nodes on the key's path dirty, so that they are written again.
  A step makes dirty the nodes on the paths of its own puts only
  (`Db.touchPaths`, 024-07): since format 6 a delete unlinks the nodes it
  empties, and since format 7 merges those it leaves underfull, so every
  index node that a lookup reaches has a live key below it, and a put of
  that key after pCut, the user's or a step's, has made
  the node dirty (a leaf with a live key keeps its deleted keys' entries).
  Until 024-07 a step visited every index node of its key range at the
  current time, and an iteration's last step every node to the end of the
  key space: with 10M keys in time order, a record of 191 to 206 MB and a
  commit of 21 s (024-03, section 7). Its value nodes stay
  within 7/8 of the record limit, as a user transaction's: a value that
  would pass it ends the step before it and starts the next one, where it is
  within the limit alone, with the step's row (015-50).
* When the scan ends, the iteration is done; tEnd and pEnd are the time and
  the position of its last step. The cut at pCut waits until tEnd is older
  than R, the startup pos has passed pEnd and then pSafe, and the last valid
  meta block names a transaction at pCut or later. Then the reclaim table
  records the cut, the first available lookup time becomes tEnd, and the
  physical cut waits until the table is durable.
* A read admitted before a cut may expire: a read that the cut overtakes
  throws `LookupTimeNotAvailableException`, and the database goes on
  (decision D1 = A, 2026-10-13; 011-04, W1). The retain duration may change
  while the database runs, and a restart keeps it (015-87); every cut keeps
  the guarantee of the duration in force when it was decided (011-04, W2).

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
  001-07 are argued or checked, not proved. Since 024-07 the argument for
  the index nodes rests on the delete's upward unlink: no index node
  without a live key below it, but an empty space root (024-07, section 4).
* Reclaim added 26 to 38 percent of all stream writes in the cells
  measured (011-04, W4), and in the grids of 2026-10-13 the stream kept was
  the retention window plus one or two iteration spans. The bound on the
  stream (R5, Q8) is measured, not derived (017-04).
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
other call follows (005-52), or until what is left cannot go (015-70).

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
* **What is in memory.** The objects of the live handles, the values
  that their pointers hold, and the handles. `Residents` counts their
  bytes without walks: each object with its live handle and the handle's
  entry in the node table (79 bytes), 32 bytes for each of its pointers
  that holds a handle, live or dead, and its values, from when it enters
  a handle until it leaves it (009-02, section 4.7; since 015-13: before,
  no handle was counted, 34 to 49 percent more than the counted bytes in
  R1's probe). A handle that several pointers hold, or a pointer and the
  table, is counted for each: an upper bound. The count is exact but for
  the objects that the writer changed since their last count, D's above
  all: each is counted with its size at its last count (when it entered
  its handle, or its last write) until its next write, so the growth of
  its arrays and the values and handles that the writer put into it are
  not counted meanwhile, and the resident bytes are below the bytes in
  memory by those (015-15; in R1's probe with the default startup
  distance of 50 MB, 1,896 bytes counted of 72,726 after 50 transactions
  of 1,000-byte values). A batch that takes a pinned leaf's values takes
  its count down to the leaf's bytes without them (its own, its entry and
  its handles), no further.
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
  between the watermarks if that is more; pinned bytes counted by a round
  of the hand that began after the last decrease of the budget, 015-70),
  a batch of CLOCK steps runs, at most 2 ms, 4,096 handles (65,536 under
  pressure) and two rounds of the hand, a map with more handles than a
  batch has left taken in parts (015-67): in the writer at a transaction's
  end, and after a reader's load in the database's eviction thread, which
  takes the write lock between transactions and gives way to a waiting
  writer. A reader's load that
  finds the resident bytes far over the trigger waits up to 2 ms for that
  thread. A transaction's own reads of its keys before the write lock
  (`Db.warmup`) wake it and do not wait (005-52), so the resident bytes may
  rise by what they load (the paths of the keys and their present values)
  until the transaction's end runs a batch.
* **Readers** follow a pointer without a lock when its handle holds an
  object that may serve it (`Handle.usable`): an acquire read of the
  pointer, then its reference and the handle's object, ordered by it;
  edges of the Java Memory Model, not the hardware's address dependency
  (the barriers of 009-02, section 3.4, since 015-14, and their jcstress
  tests, `java/stress/jcstress/`).
  Else the slow path reads the pointer under the node's monitor and loads
  under the handle's, so two readers do not read the same node; its swizzle
  is a compare-and-set, and its write-back of the reference only raises it.
* **Reclaim** reads with the maintenance follower, which loads but swizzles
  nothing; a step's dirty index nodes stay pinned until written, and a
  reserve (4 MiB) splits a step that would pin more.
* **The dead hand** (since 2026.4; 023-07, section 5.6): after a cut has
  moved the first available position, the writer, at each transaction's end,
  evicts in steps of at most 4,096 units of work and 2 ms
  (`Eviction.deadStep`) every object stored before the cut that is not
  pinned, whatever its CLOCK bit and the budget, and makes each value stored
  before the cut in a kept node a stream pointer. Not with `noEvict()`:
  there the memory of ended versions is released only at a restart.

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
  stream's monitor, and a cut's files are deleted by a thread of their own.
  Before, a read of the last file waited for the writer's append and its force,
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
* So the waits above 20 ms left in item 009's runs are not BergDB's own:
  the collector's (G1's pauses; ZGC's allocation stalls, 129 and 300 ms on
  s1 when its heap ran short), s1's disk (gets from the device of 64 to 74
  ms, where single random reads take up to 58 ms, and one get of 2,760 ms
  under the kernel's memory reclaim;
  [009-03](../items/009-handles/03-measurements.md), section 9), a
  writer's waits for room in the write buffer when the disk stalls, and
  readers' waits for a core. Item 009's target 2 is met in P4's soak and
  the pause probe (009-01, section 1). Readers' waits for a core: in
  ScaleBench from the OS's cache on F53 at 665 MB under ZGC, 8 readers and
  ZGC's workers fill F53's 8 performance and 2 efficiency cores, and gets
  take up to 89 ms, 99.7 percent of their time off core: the operating
  system's scheduling, outside the target (Frans, 2026-10-29 and
  2026-11-06). With 7 readers 0.4 gets in a million take over 10 ms, the
  longest 33 ms, off core too. So use at most as many readers as the
  cores less the collector's workers
  ([015-86](../items/015-todo/86-gets-with-8-readers.md), Results, Q-A of
  night 006-12).
* Loads in memory, with no eviction, are 8 to 20 percent slower than before
  handles.
* D, which cannot be evicted, is bounded only loosely by the startup
  distance: its nodes' stream bytes reached 2.9 times the startup distance
  at 50 MB, 2.3 times at 200 MB and 1.6 times at 1000 MB, in runs with 10M
  and 50M keys (005-38); in memory they take more.
* A start needs more heap than the database it starts, by an amount that
  the startup distance bounds and the budget does not: until it returns,
  it holds the startup section's records as read and its maps of their
  node versions, besides D, which it rebuilds.
  The rerun's loads are evicted to the budget as a running database's
  are, and within seconds of the start the heap is the running
  database's. In 019-45's probe the start's live heap peaked at 3.3 to
  4.9 times the startup distance, D included, whatever the budget, and
  0.9 to 2.1 times the section's bytes above the running database's: at
  2M keys, a startup distance of 200 MB and a budget of 133 MB, 663 MB
  against 288 MB, so that a database that ran in a 600 MB heap did not
  start in it (W7's failure on F53 and s1, 016-10) and started in 700 MB.
  So give the heap about twice the startup distance above what the
  running database needs.


## 8. Durability

* `FileStream`, the file storage, by default forces every append to the
  device before the append returns (`FileChannel.force(true)`: `F_FULLFSYNC` on macOS,
  `fsync` on Linux), and a new file and its directory entry before the file
  takes appends. Its power-loss ordering (the file and directory forces, a
  force between the prefix removals of reclaim's cuts, the failures of
  deferred cuts passed on) is tested under a fault model, and native audits
  confirm `F_FULLFSYNC` on macOS/APFS and `fsync` in a Linux VM
  ([011-07](../items/011-docs-archive/07-level3-durability.md);
  `PowerLossTest` in `level3.sh`). Not established: physical power cycling,
  other storage providers and Windows.
* The crash contract (014-01, section 7; Frans, 2026-11-05): BergDB
  assumes that its stream's bytes are read back exactly as written, and
  that a crash leaves a prefix of what was appended, at least up to what
  was forced; the storage provider ensures this, not BergDB. A transaction
  is then seen whole or not at all, and `sync()` adds durability. A start
  recovers only a truncated tail: it completes a torn last record as an
  aborted one, by appending (005-83's 56 truncation cases all recover).
  It cannot tell a crash's cut from a cut that took more, as nothing
  outside the stream records the stream's length: a last stream file
  deleted, emptied or cut while the database is stopped gives a start
  without an error that has lost the transactions in it, synced ones too
  (020-24-08, U8-1; `Database`'s Javadoc, "The files", says so).
  Other damage is an integrity failure outside the contract: a start may
  refuse it, or a read fail the database. Holes in an unforced write
  (later bytes surviving while earlier ones are missing; 005-83,
  "Power-loss tail experiment") are such damage. POSIX does not promise a
  prefix for writes that are not forced, though common file systems keep
  appends in order: `FileStream` relies on a file system that does. A
  broader crash model is open in 014-01.
* `BufferedStream`, above it, collects the database's appends and writes
  them in chunks from a thread of its own, when the buffer time (50 ms by
  default since 005-64; 20 ms from 005-13) has passed or its buffer is
  a quarter full: an append that reaches the quarter wakes the thread,
  which also continues without a timer wait when a flush leaves a quarter
  ready (005-76). One force per chunk, not one per transaction. `execute()` only
  appends to that buffer.
* `sync()` waits until the transaction's last byte, its commit byte, is
  durable (005-44). A sync that waits has the buffer written at once, and
  the transactions that arrive during a force go out together (group
  commit, 005-48, since 2026-10-27): on s1, one thread that syncs after
  every transaction went from 38 to 213 durable commits a second (the
  sync's median from 24.8 to 3.8 ms), 64 threads from 2,364 to 6,429.
  Before group commit, on F53, one thread got 29 a second (35 ms each) and
  64 threads about 1,800 (005-13); F53 is not measured with it.
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
* Per-append forcing can be turned off, in the core API only: `FileStream`'s
  constructor, `new FileStream(dir, false)` (005-47; Frans, 2026-11-04). The
  Pub API keeps it on. Off, an append is written to the OS and not forced:
  a completed append, the durable length and a returned `sync()` then mean
  "written", which survives a crash of the process, not one of the OS or a
  power loss. The forces that keep the database whole stay: a file opened
  for appends and its directory entry, the last file before a new one, the
  last file before a cut's deletes, and the last file at `close()`, so a
  clean stop is durable. On a file system that does not keep appends in
  order, a power loss or OS crash can leave a hole in the unforced tail,
  outside the contract (the second point above): the database may then not
  start, or fail reads, more than a loss of its last transactions.
  `PowerLossTest` runs each seed in this mode too, with its negative
  controls, and counts the hole images.


## 9. Replication

None since 2026-11-04 (005-11, "Frans's decision": "A with C2 now"). A
database writes one stream, its main storage; `SyncLevel` has NONE and
ORDINARY, and a sync waits for the main storage only. The Pub API's
`DatabaseBuilder.replica`, `Database.addReplica`, `removeReplica`,
`getStorageInfos` and `SyncLevel.STRONG` went, with `StorageManager`'s
replicas and the startup's copying between streams. Until then replication
was in no level, experimental, with the faults of 005-11's study (releases
2026.1 and 2026.2 have it so).

Copies are left to the OS and the file system (005-11, option C2): a
mirrored disk or volume (RAID 1, a ZFS or btrfs mirror) for the loss of a
disk, and a copy of the stream's files for a backup. As the stream is
append-only, a copy of its files in their order, made while the database
writes, is expected to be a prefix and so to start as the database, if no
cut deletes a file during the copy; not tested. The stream and its meta
blocks never recorded replicas: a directory that was a replica is a
database of its own, with the same database ID, which nothing writes any
more. Ways to implement replication in the future, and the removed design,
are a long-term topic, 017-03.


## 10. Open work

What is left to do is in the items, not here: the index of
[items/readme.md](../items/readme.md), the open entries of
[015-todo](../items/015-todo/readme.md) and
[019-todo](../items/019-todo/readme.md), and bounded startup in
[007](../items/007-bounds/readme.md) (T4).
Where BergDB departs from its design principles is in
[010-01](../items/010-principles/01-principles.md).


## 11. Objects and user indexes

The part of the Pub API beside the Core's `String` and `byte[]` values,
redone for 2026.4 from 2026.3's experimental code (item 020): what it
promises, where each rule is written, and what checks it. The decisions
are Frans's of 2026-11-08 and those taken under his delegation of that
evening, each with its record:
[020-02](../items/020-release-2026-4/02-objects-design.md), sections 4 and
5.1b, and [020-01](../items/020-release-2026-4/01-inventory.md), section
14.1. The Javadoc of `bergdb.pub` states the promises for users (the
package's "Objects" and "Null and absent fields", `IndexBuilder`,
`UseIndexBuilder`, `UsePrimaryBuilder`).

**The API.** The packages `bergdb.pub` and `bergdb.pub.util`, and the
Core's `Db` with the types of its signatures; everything else,
`bergdb.pubimp` included, is not API, whatever is public in it
([020-10](../items/020-release-2026-4/10-indexes-design.md), section 7).
`java/build.sh` makes `build/bergdb-release.jar`, the jar a release ships:
the classes of `src` only. The stored object is API since 020-10's step
B3: `DbObject`, its `Builder`, `DbArray`, `DbValue` and the value classes
(`DbBoolean`, `DbLong`, `DbDouble`, `DbString`, `DbByteArray`) are in
`bergdb.pub`; the codec (`ObjectFormat`) and the conversion
(`DataObjects`) stay in `bergdb.pubimp`, public there for them only. Both
jars seal `bergdb.pub` and `bergdb.pubimp`, so no class of another jar or
directory joins them. A `DbObject` is immutable: `getBytes()` gives a copy,
and a put checks a user's `DbObject` by the full check and stores a copy.

**Writes through the Core.** The Core is root: `Db` writes any key, the
Pub API's too, and refuses none (010-01, P12). The rules are in `Db`'s
Javadoc
([020-22](../items/020-release-2026-4/22-core-writes-and-pub-integrity.md),
section 5; Frans, 2026-11-09): keys that start with neither `/d`, `/-` nor
`/#` are the Core user's; the Pub API's keys may be written, but only the
Pub API's writes keep its indexes, so a Core put at an object key of an
indexed directory can be left out of its scans until the key is written again
through the Pub API or the index is made again; keys under `/#` are
BergDB's. Malformed internal data is refused with `InternalDataException`
at a start or at the read that meets it (with 020-16's fixes F16-1 and
F16-2); a scan never returns a value that does not match its query,
whatever was written; a well-formed Core write of BergDB's keys is
undefined (020-22, section 5.4).

**Stored objects, format 2.** The spec is
[020-07](../items/020-release-2026-4/07-object-spec.md), under 018-01's
rule that Frans approves a change of the stored format (020-02, section
4.12). A stored object is the header byte `0x82` and an object: a table of
its fields' ends and the fields in the order of their names' unsigned
bytes, each value in Binson's encoding. Seven types (boolean, integer of
64 bits, double, string, bytes, array, object); one integer type, so Java's
`byte` to `long` are the same values; one NaN, and −0.0 kept; names of 1
to 255 bytes of well-formed UTF-8; at most 16 levels of objects and arrays
and 32,767 fields an object; at most 2^31 − 1 bytes. One object has one
byte string: a writer writes the canonical bytes, and the full check
refuses any other, naming the rule it breaks (`BadFormatException`; at a
get `ObjectCreationException`). A field is found by a binary search on the
table. There is no null: a field without a value is absent (020-02,
section 4.1). Objects of 2026.3 and before (format 1) are refused, named so:
a get and a scan refuse them, a `byte[]` put of one in an indexed
directory is refused, a build over one fails, and a start that meets an
index definition of format 1 is refused; such a database is made again
from its data (020-02, section 4.11). A put over one and a delete of one
work, in an indexed directory too: it has no index entries.

**Data Objects and the conversion.** The rules are
[020-09](../items/020-release-2026-4/09-conversion-rules.md); the code,
two layers (020-02, section 5.1b): `DbObject` and its stored bytes, exact,
and `DataObjects`, the binding of Java's classes to them. A Data Object
class is public, with a public no-argument constructor; it stores its
public, non-static, non-transient fields and those of its superclasses,
none of the Java platform, each of a type on a closed list (primitives,
their wrappers, `String`, `byte[]`, arrays, Data Object classes), and
every other instance field is transient (020-09, section 3, V1 to V10). A
put is exact: each field by its declared type, a null field left out
(020-04's (c)); it refuses, with `IllegalArgumentException` before
anything is written and naming the place, a class that is not a Data
Object, a null array element, a value of another class than its field's,
a cycle, nesting deeper than 16 levels. A get is best effort: by name,
the nearest value, integers clamped, a double into an integer cut toward
zero (020-09, section 5.4), the type's zero where no conversion makes
sense, never a throw for the data; `ObjectCreationException` for a
class that is not a Data Object, checked first also at a key without a
value, and for a constructor that throws. `put(Object)`, the field `key`
and `MissingKeyFieldException` are gone: a field named `key` is an
ordinary field. The plan and its record, step by step:
[020-08](../items/020-release-2026-4/08-implementation-plan.md), section 8.

**User indexes.** The design is
[020-10](../items/020-release-2026-4/10-indexes-design.md). An index has
one directory (its own values, not its subdirectories'), 1 to 8 levels,
and one field per level, a name or a nested path; a level is of type
`long`, `double`, `string` (code-point order) or `bytes` (unsigned byte
order). An index is a function: each value has one entry or none, and a
field that is absent, of another stored kind, or NaN gives none; a value
that is not an object has none (020-10, section 3.3). No language's order
and no ICU: an application that needs one stores its own collation key in
a `byte[]` field and indexes it as `bytes`.

* **Creation and deletion**: `Database.indexBuilder(name)`, then `dir()`,
  `type()` and `field()` or `nestedField()` per level, and `start()`,
  which writes the definition in one transaction and returns the build's
  `Job`; `start().join()` waits until the index is active. A build's
  status is a snapshot: building with a count, active, or failed with a
  reason; a failed build leaves the database running and is taken again
  at the next start (019-42), and its `join()` throws an
  `IndexBuildException` with the status and the cause (since 2026-11-09,
  020-10, section 3.2). `Database.indexJob(name)` gives an index's
  job; `deleteIndex(name)` is one transaction, and the old entries are
  removed in the background. `createFast()`, `Database.PRIMARY` and
  `StartupInfo.getStartupJobs()` are gone.
* **Maintenance**: every put and delete at an object key of an indexed
  directory, of any value, removes the old value's entry and writes the
  new one, read at the transaction's read time, with the index manager's
  lock rule between writes and index definitions (020-10, section 5).
* **Scans**: `Connection.useIndex(name, type)`: `eq()` on levels 1 to k,
  then `from()` and `to()` or `prefix()` on level k + 1, and `backward()`,
  each call checked at once (020-10, section 3.4). At the scan's lookup
  time, each entry's value is read and checked against the entry, so a
  stale entry is skipped, never returned, and the value is converted as a
  get converts it. No scan in `rw()` in 2026.4.
* **The primary scan**: `Connection.usePrimary(type).dir(dir)` lists a
  directory's own keys in order, each value by the kind the type takes
  (020-10, section 3.5): every value as `byte[]` or `Object`, the values
  that are not objects as `String`, the objects as `DbObject` or a class.
* **Stored** under `/#i/`, a definition per name and entries per index
  generation (020-10, section 4), under 018-01's rule.

**Checks.** Each against a reference written apart from the code, with a
seed, a size in `before-commit.sh` and a larger run in the night group:

* H0, the format: `ObjectFormatTester`, the codec against a second codec
  written in the test from 020-07, random values and every mutation of ten
  samples; the conformance vectors,
  `java/src/bergdb/pubimp/doc-files/object-vectors.txt` (020-07, section
  13), made and checked by two programs written apart from the spec, and
  run by the codec; `DbObjectFormatTester`, the same through `DbObject`
  and its Builder.
* H1, the conversion: `DataObjectsTester`, 020-09's 176 cases (G1 to G122,
  K1 to K18, W1 to W36) and three properties: R1 the round trip, R2 the
  get against a reference of 020-09, section 5, R3 the constructor's part
  (principle 4).
* H2, an index is a function of the data (`IndexHarness`, 020-10, section
  9.1: its reference and generators; its run against BergDB comes with
  020-10's step H2); the races of maintenance and definitions
  (`PubTesterIndexRaces`, 9.2); H3, jobs under faults (9.3, with step I2's
  second part); H4, the primary scan (`PrimaryHarness`, 9.4). The
  encodings of the index keys and the definition: `IndexKeysTester`,
  `IndexDefinitionTester`.
* The unit tests of the Pub API (`PubTester`, `PubTesterIndex` and its
  siblings), and the night tests with objects and indexes (`PayTest`,
  `CcDbNightTest`); `level2.sh`'s BryanRepro puts objects through restarts
  and reclaim.

**Limits.** The cost of format 2's full check at each read and the writer
are measured against 2026.3's format in 020-08's step 4, which waits for a
quiet machine. A `byte[]` put at an object key whose bytes happen to be a
stored object of format 2 is read as an object by a get as `Object` and by
a scan, as the format's header is a guess there (020-08, section 3; 020-01,
N4). Format 1 is told by its structure (`bergo`, the version 1, a field
count and a field table that fits the value), not by its first six bytes:
a `String` put is never taken for it, but a stored value whose bytes happen
to be a whole object of format 1, a `String`'s too, is read as one: a get
refuses it, and a build fails over it.

