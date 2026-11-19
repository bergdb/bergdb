028-18. Change: one startup transaction, the startup distance in the primordial record
=======================================================================================

Status: done (option C, gated and merged into `main` 2026-11-19; below,
"Option C: what was made"). Kind: Change. Frans: decided (2026-11-18,
21:37); C (2026-11-19, 09:53 and 09:59).
Created 2026-11-18 by Frans Lundberg.

Frans, 2026-11-18, 21:30, on 028-15's creation in two records: ""a new
database is created with two records". Why not combine them into one
transaction. Seem better. Either we have a fully initialized database or
not." 21:37: "Document this work in a todo item. Start it now. One
startup transaction."

What: since 028-15 a new database's creation writes two records: the
primordial record (the empty tree), then the creating start's internal
transaction that puts the startup distance at `/#i/-sd` (028-15, decision
1). The reason was a test tool, not the database: the Lean trace checkers
require record 0 to be the model's empty initial tree. 028-17 then made
the creating start sync its second record, so that a Pub database's
creation is durable when `start()` returns; a crash inside the creating
start can still leave the primordial record alone, and the next start
then writes the startup distance with its own builder's value.

The change: one startup transaction. The primordial record holds the
startup distance's KV, so a creation is one record:

* a crash leaves either no database or a fully initialized one (a torn
  record is dropped whole);
* the path "primordial record alone: write the KV at the next start" goes,
  with its tests, and 028-17's second sync;
* a new database's first transaction is no longer one time unit later.

Done when:

* `java/`: the creation writes the KV in the primordial record; a start
  refuses a stream whose primordial record lacks it (a damaged stream),
  as 028-15 refuses a missing KV; 028-17's extra sync and the
  "primordial record alone" path removed; tests: a creation is one record
  holding the KV, a crash during creation leaves no database or a whole
  one, a change of the startup distance later, restarts.
* The trace export and the Lean checkers (`lean/`'s `tracecheck` and
  `treecheck`, `lean/contract/`'s `contractcheck` and `bridgecheck`)
  accept a record 0 that holds that KV, as a transaction from the empty
  tree. **If a pinned statement of `lean/contract/` must change** (such as
  the history's initial state), the agent stops before changing it and
  writes the proposed change here for Frans (statements change only on
  his word, 030's rules).
* 027-03 (sections 3, 6, 14.2, 15), 027-02 (record 0), 027-11, 028-15 and
  028-17 follow the code; `releases/next.md` if users see a change.
* Gates: `java/before-commit.sh`, `java/stress/core-build.sh unit f`,
  `java/stress/kill-restart.sh 1000` with seeds 20261118, 20261117 and
  20261119, `java/stress/level1.sh` to `level4.sh` full, and
  `lean/contract/gate.sh` (and `pin.sh` if pins move).

Sources: 028-15 (decision 1), 028-17, 027-03 (sections 6, 14.2, 15),
027-02.



Found: a pinned statement must change
-------------------------------------

By an agent of coord-1118, 2026-11-18, 21:40 to 23:30, in a clone on the
branch `028-18-one-startup-tx`.

A creation in one record, with the KV in it, is outside what the pinned
statements of `lean/contract/` (030's rules) and the model say of Java,
whichever way the trace shows it. Two ways were tried, each with the Java
change made and traces exported and checked:

* **One record at one time, the KV in R(0)** (Java: the primordial
  structure and the KV put by the Dag's own put at the creation's time,
  one record of 272 bytes, `Db.CREATION_LENGTH` 400; the exporter
  unchanged: TX 0 is Java's record, with the KV's nodes and entries at
  time 0).
  * `tracecheck` (the SIS model, lean/Check/Trace.lean): passes, with no
    change of the checker; it takes the initial structure from TX 0.
    `java/stress/conformance.sh` small, reclaim and evict (2 seeds each,
    runs B and E, handles): CONFORMANCE OK.
  * `treecheck` (lean/Check/TreeRun.lean, not pinned): fails one check
    in each trace, "R(0): Java's primordial structure is not the model's
    `initStruct`" (`treeconf.sh small`: 14 of 14 traces, nothing else).
  * `contractcheck`: "TX 0: C2, the start tree is not empty". The
    contract's `Start` (Contract/Statement.lean) is "at time 0 it meets
    the invariants and is empty", `contents (s.at 0) = []`; `get_right`
    and `scan_right` say a read gives `refMap` of the transactions from
    the empty map.
  * `bridgecheck`: "TX 0: the start" and "TX 0: TB, the start's top":
    `startCheck` (Contract/BridgeHeap.lean) is the primordial structure
    exactly, the root, the super root and one key node with one time
    klong.
* **One record at two times, R(0) virtual** (Java: the primordial
  structure at t0 and the KV put at t1, one record at t1; the exporter
  writes TX 0, the primordial structure, which is in no record of Java's,
  and TX 1, Java's record, its startup pos R(1) itself).
  * `contractcheck` and `bridgecheck`: pass (CONTRACT OK, BRIDGE OK): the
    start is empty, and T(1) puts the KV.
  * `tracecheck` (C-S) and `treecheck` (C-T9) fail at T(1): "sp: model
    0, Java 1", and then the versions, top and D. The model's step 4
    (lean/SIS/Algorithm.lean, `startupPos`, pinned) clamps the startup
    pos to s(i) < i: a record never holds every node that its own
    transaction made dirty, which this record does (the stream has no
    R(0) to read them from).

So a pinned statement must change for one record: the contract's start,
or the model's step. The agent stopped before changing either, as the
task says, and wrote the options below.


For Frans
---------

How should the contract and the model see a new database whose creation
writes one record that holds the startup distance's KV?

* **A. The start holds the creation's KV** (recommended). The creation
  is one record at one time, R(0), the whole tree with `/#i/-sd`. The
  model's R(0) is that tree, all of it written (the model's T(0) already
  writes its whole initial structure); a new database is never empty.
  What changes:
  * `lean/contract/` (pinned, statements): `Start` says the start tree
    meets the invariants and holds the creation's KVs (its contents are
    `refMap` of the creation's operations, a put of `/#i/-sd`), not that
    it is empty; `get_right`, `scan_right` and the theorems built on
    `Meets` (the top's, the shape's, the bridge's) read from those
    contents; the bridge's start (`startCheck`, `startTopOk`) is the
    primordial structure with the KV's two nodes, the key node of its
    last segment and the value; the checkers' TX 0 checks follow, and
    the format's TX 0 gets the creation's operation (an `OP` line, which
    `Complete.lean` now refuses in TX 0) or the checker reads the
    start's contents from its tree.
  * `lean/` (not pinned): `treecheck`'s R(0) check: `initStruct` with
    the creation's put at time 0, in place of `initStruct` (made on the
    prepared branch); `tracecheck` needs no change.
  * Java: as tried (above); the exporter unchanged; and a check that a
    damaged stream's test found (below, "Prepared for option A").
  * Costs: a prover's work on the contract package (the start and the
    theorems that use it), the pins moved by Frans's word; the format's
    TX 0. Gains: the model says what Java does: a database is created
    whole, at one time; the first user transaction is one time unit after
    it, not two.
* **B. A record may be its own startup pos.** The creation is one record
  at two times: the primordial structure at t0 and the KV at t1; the
  trace's R(0) is virtual. What changes: `lean/SIS/Algorithm.lean`'s
  step 4 (pinned) lets s(i) = i (for the first transaction, or always),
  and the model's proofs that use s(i) < i (`step_s_le` in
  lean/SIS/Proof/StepFacts.lean and what rests on it) are redone; the
  exporter writes a TX 0 that no record of
  Java's holds, and maps Java's first record to R(1). The contract
  package's statements stay. Costs: a change of the model's algorithm
  for one case that Java's writer otherwise never has (a take never
  takes the record it writes), and a trace whose R(0) is in no stream.
  Not recommended.
* **C. Keep two records; make the creation whole by refusing the
  primordial record alone.** A stream that holds the primordial record
  and no KV (a crash inside the creation) is refused as a creation that
  did not complete (`DatabaseNotCreatedException`, as 005-33 refuses a
  part of the primordial record), and the Pub API writes `created.txt`
  after both records are synced. No statement changes; it can be made
  and gated in a night. A crash still leaves either no database or a
  whole one, but in two records, and the first user transaction is two
  time units after the creation. It is not "one startup transaction".

Recommended: A. If Frans takes A, the Java side is ready on the branch
`028-18-prepared` (below), and the contract package's change is a
prover's task (030), with this item's tests and gates after it.


Frans's choice: C
-----------------

Frans, 2026-11-19, 09:53: "Option C seems like the way forward." 09:59:
"Can you start option C now? I want it. We may add things to this first
non-primordial transaction later. But start with this."

So the creation stays two records, and "Done when" above is replaced by
option C's: the primordial record alone refused, `created.txt` after
both records are synced, the path that completed a lone primordial
record and its tests removed; no change of the Lean model, the trace
format or the contract (no pinned statement moves). The branch
`028-18-prepared` (option A) is not taken.


Option C: what was made
-----------------------

On the branch `028-18-option-c` (from `main` c458bfea, `main` merged
again at b03dcea7), by an agent of coord-1118, 2026-11-19, from 10:00.

* **The refusal.** `RecoverableStream.holdsFirstTransactionAlone`
  (only reads): the stream is not cut, shorter than a meta block
  distance (no second meta block), its first block valid and naming no
  record, its first record of the creation's length (`Db.CREATION_LENGTH`,
  272 bytes with the block) and committed, and after it nothing, a part
  of a record (its size too), or one record failed (its last byte 0, as
  recovery's zero fill leaves it) that ends the stream. `Db.refuseIncompleteCreation`,
  before recovery, throws `DatabaseNotCreatedException` for such a
  stream ("holds the creation's first record and not its second, the
  startup distance"), as for a part of the primordial record (005-33):
  the start writes nothing. Not on the creating start, which wrote the
  primordial record itself (`handleEmptyStream` now says whether it
  did).
* **The creation's order.** `handleEmptyStream` writes the primordial
  record only. At the end of the creating start (`startInner`) the
  internal transaction puts the builder's startup distance at `/#i/-sd`
  (as since 028-15); with `created.txt` (the Pub API) one sync of both
  records (`syncCreation`, rule D1), then `created.txt`, then the start
  returns. Until now `created.txt` came after the primordial record's
  sync, and the second record had a sync of its own after it (028-17):
  one sync less per creation. `writeCreatedTxtIfMissing` is not called
  by the creating start.
* **Removed.** The path in which a start that found the primordial
  record alone wrote the KV itself, with its own builder's value
  (`primordialOnly` in `startInner` and `readStartupDistanceKv`, now
  `creating`: no KV is an SFE on every start but the creating one).
* **Javadoc and comments.** `Db.start()`'s `@throws
  DatabaseNotCreatedException`; `DatabaseNotCreatedException` (the
  creation's first two records); `DatabaseBuilderImp.refuseMissingStream`;
  `NodeStream.holdsPrimordialRecordAlone`.
* **Not changed.** The Lean model, the trace format, the contract, the
  writer (PE), the record format and the meta version; the kill-restart
  harness (below).

**Tests.**

* `DbTesterRestart.testCrashInCreationsSecondRecord` (replaces
  `testCrashInCreatingStartsKv`, the removed path's test): the primordial
  record alone, it with the second record cut at every 8th byte, and it
  with the second record failed: each refused with
  `DatabaseNotCreatedException`, the stream unchanged, at two starts (a
  Core API start, without `created.txt`); the whole creation keeps the
  creator's startup distance at two starts with other builder values,
  counters 0.
* `DbTesterStream.testCreatedTxtAfterBothRecords` (new): with
  `created.txt` on files, every force of the creating start is recorded
  with the file's length and whether `created.txt` existed: no force saw
  it, one force covered the whole stream as `start()` left it (both
  records), and `created.txt` is there when `start()` returns; then a
  restart keeps the creator's setting, a change of the startup
  distance, and a restart with it. On `main`'s `Db.java` it fails
  ("created.txt at a force of the start").
* `DbTesterStream.testCreationDurableWhenStartReturns` (028-17's) kept:
  a copy taken after `start()` returned has both records.
* `RecoverableStream.Tester.testHoldsFirstTransactionAlone` (new): the
  method's cases, and that it only reads.
* Changed: `DbTester.testCrash8InCreation` (f) also refuses the
  primordial record whole and alone, and starts the whole creation;
  `PubTester.testCrashInCreation` cuts at 272, 273, 280 and the whole
  creation less one byte too, with and without a crypto key, each
  refused with nothing written.
* The kill-restart harness (`KillRestartHarness.open`) is unchanged: it
  allows `DatabaseNotCreatedException` only before a start of the
  database succeeded (its journal's `ST` line, written by
  `DatabaseImp.testHookAfterStart` after the Core's start returned), then
  removes the files and creates the database again. Since a start
  returns only after both records are synced, a kill during the creation
  is that case: no committed transaction is lost.
* Before the change (`main`'s `Db.java` with the new tests):
  `testCrashInCreationsSecondRecord` ("started, length 272"),
  `testCreatedTxtAfterBothRecords` and `PubTester.testCrashInCreation`
  ("started, cut at 272") fail; after it they pass.

**Descriptions.** 027-03 (sections 7, 14.2 steps 1, 6 and 8, 15, and
its log), 027-11 (1.2, 1.9, log), 028-15 (decision 1, a note), 028-17 (a
note), `releases/next.md` (a crash during the creation gives
`DatabaseNotCreatedException`, also between the two records).


**Gates of option C** at 6ce83269 (`main` b03dcea7 merged; 2026-11-19,
10:10 to 10:50, with `java/night.sh` running on the machine):

* `java/before-commit.sh`: BEFORE COMMIT OK (at d2b8d4b7 and again at
  6ce83269).
* `java/stress/core-build.sh unit f`: CORE BUILD OK.
* `java/stress/level1.sh`: LEVEL 1 OK.
* `java/stress/level2.sh` full: LEVEL 2 OK.
* `java/stress/kill-restart.sh 1000` with seeds 20261118, 20261119 and
  20261120: KILL RESTART OK each (1000 kills; 54, 50 and 52 exits; 2451,
  2538 and 2400 s), beside `night.sh` at a load near 55.


Prepared for option A (not taken)
---------------------------------

On the branch `028-18-prepared` (this branch and its commits on top), by
an agent of coord-1118, 2026-11-18, 22:00 to 23:15. Not for `main` until
Frans decides; nothing in `lean/contract/` changed, no pin moved.

* **Java.** `Db.writePrimordialTransaction` writes the creation as one
  record at one time: the super root and the first key node, and in them
  the startup distance's KV, the builder's, put by the Dag's own put on
  the nodes in memory (ids as an ordinary transaction's, from the
  record's position); every node in the record, startup pos 0, no node
  got dirty; `Db.CREATION_LENGTH` 400 (272 before). `DbStarter` reads it
  as any section's first record (its primordial startup of two nodes is
  gone). Gone: the "primordial record alone" path of `Db.startInner`
  and 028-17's second sync (`syncCreation` syncs the one record, before
  `created.txt`, as 015-01 had it). `readStartupDistanceKv` refuses a
  stream without the KV in every case (an SFE, "the stream is damaged").
* **A check found on the way.** CST's found cases, relocated in the new
  streams, showed a new one: the creation's root key node, now with a key
  klong, its leaf flag cleared by damage, was taken by the start, whose
  rerun threw a `Bug` from `Dag.merge` (seed 729001 of the configuration
  ALL, where the startup section begins at the creation). Until 028-18
  the primordial root had no key and such a copy was refused.
  `StoredKeyNode.parse` now refuses an inner key node whose first key
  klong is not the empty key's (compare value 0: a split makes an inner
  node with its leftmost child first; every inner node of the traces has
  it). A test-made inner node in `NodeCollection.testResolvePointers` was
  changed to keep the rule.
* **Tests.** `DbTesterRestart.testCreationIsOneRecord` (the stream is
  `CREATION_LENGTH`, one record holding a top node, two key nodes and the
  value at `/#i/-sd` with the builder's 1,000,000; a cut at every 8th
  byte of the record refused as not created, writing nothing; the whole
  record kept by two starts with other builder settings, counters 0) in
  place of `testCrashInCreatingStartsKv`;
  `DbTesterRestart.testPrimordialRecordAloneRefused` (the 272 bytes that
  `main`'s code leaves after a crash before its second record, refused as
  damaged, nothing written);
  `DbTesterStream.testCreationDurableWhenStartReturns` kept, as a test of
  the one record; `DbTester.testCrash8InCreation` now cuts the KV's record
  too. Changed with the format: the
  creation's length and times (`testStartupPos1`, `testDeleteTwoValues`,
  `testKvTimeIsTheEntrysTime` 26 keys, `tIterators1`, the Pub API's
  `testTransactionTimes` t0 + 1 and `testClockOutOfRangeRefused`,
  `PubTester.testCrashInCreation`), the eviction test
  `testLoweredBudgetAfterPinsFell` 550 transactions (of 480 to 600 by
  tens, 520, 540 to 560 and 580 reach its state), CST's eight found
  cases re-located (the same kinds of damage; seeds 20807 and 20778 now)
  and a row for the root's flag.
* **The checkers.** `tracecheck`: no change (it takes the initial
  structure from TX 0). `treecheck` (lean/Check/TreeRun.lean, not
  pinned): R(0) must be `initStruct` with the puts of the KVs that R(0)
  holds made at time 0 by the tree's `exec` (`creationStruct`); it
  passes `main`'s traces too. The exporter: unchanged but its comments.
* **Descriptions** on the branch: 027-02 (TX 0), 027-03 (sections 7,
  14.2, 15, 18), 027-11 (1.2, 1.9), 028-15 (decision 1), 028-17, and
  `releases/next.md`.

**Gates of `028-18-prepared`** at `33a9adb8` (2026-11-18, 22:20 to 23:09;
after it only texts, a Javadoc and `main`'s items merged, with
`java/before-commit.sh` BEFORE COMMIT OK again at `3107fd48`):

* `java/before-commit.sh`: BEFORE COMMIT OK.
* `java/stress/core-build.sh unit f`: CORE BUILD OK.
* `java/stress/kill-restart.sh 1000` with seeds 20261118, 20261117 and
  20261119: KILL RESTART OK each (1000 kills, 54, 53 and 50 exits).
* `java/stress/level1.sh`, `level3.sh`, `level4.sh` full: LEVEL 1, 3 and
  4 OK.
* `java/stress/level2.sh` full, with step 8b's two verdicts reported, not
  failed (a copy of the script in the gate's clone): every other step OK
  (treeconf small, drain, reclaim; conformance 70 and 50 traces,
  TRACECHECK OK; A2A3; TAKECHECK). Step 8b: `contractcheck` and
  `bridgecheck` on its 180 traces (21,000 transactions) fail each trace
  once, at its start, and nowhere else: "TX 0: C2, the start tree is not
  empty" (contract) and "TX 0: the start" with "TB, the start's top"
  (bridge). That is what option A changes.
* `lean/contract/gate.sh`: GATE OK (statements pinned, no pin moved).

**What is left for A** after Frans's word: the contract package's start
(the "For Frans" list under A: `Start`, `get_right`, `scan_right` and
what rests on `Meets`, `startCheck`, `startTopOk`, `java_start`, the
checkers' TX 0, `Complete.lean`'s TX 0 rule or the start's contents read
from its tree), `pin.sh`; `lean/contract/bridge-faults.sh`, whose faults
moved from TX 2 to TX 3 with 028-15, back by one; then the gates above
with level 2 as it is, and this item's State.




State
-----

2026-11-19, 10:56. Option C done: gated (the three kill-restart runs
passed) and merged into `main` by coord-1118. The rest of this State,
below, is of 2026-11-18 and is history.

2026-11-18, 23:15. Waits for Frans: option A, B or C ("For Frans").
Nothing of 028-18's code is on `main` or on this branch,
`028-18-one-startup-tx`, which holds the findings and the options. Option
A's Java side, the tree checker's change and the descriptions are on
`028-18-prepared`, gated but for the contract package, whose start is
what A changes (pinned statements; not changed). On A: a prover changes
the contract's start (030's rules, Frans's word for the statements),
then `028-18-prepared` merges and is gated again. On C: a new branch
from `main`, without `028-18-prepared`. 028-15's and 028-17's code
stays on `main` until then: a creation in two records, the second
synced.

Log
===

2026-11-18. Registered by coord-1118 at Frans's word (21:37); started the
same evening by an agent of coord-1118.

2026-11-18, 23:30. An agent of coord-1118: one record tried both ways;
each needs a pinned statement changed (the contract's start, or the
model's step 4); stopped before changing one, as the task says; options
A, B and C for Frans, A recommended.

2026-11-18, 23:15. An agent of coord-1118: option A's Java side and the
tree checker's R(0) check made on `028-18-prepared`, with a check of the
inner node's first klong that a damaged stream showed; gated there but
for the contract package's start (above). State written.

2026-11-19, 09:53 and 09:59. Frans: option C. Started by an agent of
coord-1118 in a clone, on the branch `028-18-option-c`.

2026-11-19, 10:50. An agent of coord-1118: option C made (the lone
primordial record refused with `DatabaseNotCreatedException`, the
completing path removed, `created.txt` after one sync of both records);
tests; 027-03, 027-11, 028-15, 028-17, `releases/next.md`; gates OK but
kill-restart, still running.
2026-11-19, 10:56. The three kill-restart runs passed (KILL RESTART OK);
merged into `main` by coord-1118.
