028-18. Change: one startup transaction, the startup distance in the primordial record
=======================================================================================

Status: open, waits for Frans: a pinned statement (below, "For Frans").
Kind: Change. Frans: decided (2026-11-18, 21:37); a decision on the
contract's start.
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
    the creation's put at time 0, in place of `initStruct`.
  * Java: as tried (above); the exporter unchanged.
  * Costs: a prover's work on the contract package (the start and the
    theorems that use it), the pins moved by Frans's word; the format's
    TX 0. Gains: the model says what Java does: a database is created
    whole, at one time; the first user transaction is one time unit after
    it, not two.
* **B. A record may be its own startup pos.** The creation is one record
  at two times: the primordial structure at t0 and the KV at t1; the
  trace's R(0) is virtual. What changes: `lean/SIS/Algorithm.lean`'s
  step 4 (pinned) lets s(i) = i (for the first transaction, or always),
  and the model's proofs that use s(i) < i (freshness, the bounds, the
  startup) are redone; the exporter writes a TX 0 that no record of
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



Log
===

2026-11-18. Registered by coord-1118 at Frans's word (21:37); started the
same evening by an agent of coord-1118.

2026-11-18, 23:30. An agent of coord-1118: one record tried both ways;
each needs a pinned statement changed (the contract's start, or the
model's step 4); stopped before changing one, as the task says; options
A, B and C for Frans, A recommended.
