# 030-38. The guarantees of release 2026.6

Created 2026-11-23 by Frans Lundberg. Status: open.

030-26's "What it means for a user" made a closed, numbered list, G1 to
G14 (006-32, section 6; 026-27, step 2). Each guarantee is marked
**proved**, with its theorem and the statement's assumptions, or
**tested on purpose**, with its assumption in 030-26, section 5, its check
and the script that runs it. The list describes `main` of 2026-11-23
(004382f9), the code planned for release 2026.6. An independent review
against the pinned statements (030-39; 026-27, step 3) found nine places
where it said more than is proved or checked; each is corrected here, in
the checks or in 030-26, or accepted with its reason (030-39, "Actions";
026-27, step 5).

# 1. How to read the list

- **Closed.** What is not on the list is not guaranteed by a proof or by
  a check made for it. Outside it (030-26, section 4): the Pub layer
  (objects, user indexes, index jobs), threads beyond G14, costs, time,
  memory and pauses, damaged bytes (detected on a best-effort basis
  only), and release 2026.5 and earlier, whose writer is another.
- **The Pub API.** The Pub API stores its objects and indexes as keys and
  values of the Core, BergDB's key-value store of byte arrays. The
  guarantees are the Core's: a Pub API user has them for the Core
  operations the Pub layer makes; that the Pub layer makes the right ones
  is tested (unit tests, randomized harnesses, user apps, kills), not
  modelled.
- **Proved** means proved in Lean for a model of BergDB and checked by
  Lean's kernel (030-26, section 3). A claim about the Java code follows
  from it with facts that are tested, not proved: the links of section 3,
  named by their item numbers in 030-26, section 5.
- **Theorem names** are the Lean names in full. Each one is among the
  main theorems of `lean/contract/Axioms.lean`, a file pinned in
  `lean/contract/statements.pin`, whose axioms the gate checks
  (`lean/contract/gate.sh`); Axioms.lean writes those of the namespace
  `Contract` without the prefix, under `open Contract`. The files of
  their statements and definitions are pinned there too. "With" joins
  theorems that give the guarantee together.


# 2. The guarantees

## 2.1 The writer and the reads

**G1. Every transaction is applied whole.** After a transaction that
BergDB accepts, the database holds the contents before it with exactly
the transaction's puts and deletes: each key put has its new value, each
key deleted is gone, every other key is as it was. A crash never shows a
part of a transaction (G3, G12).

- Proved: `Contract.PE.pe_meetsTop_start`. Every history that PE, Java's
  writer, writes from the empty database meets the writer's contract at
  every transaction (`MeetsTop`); the contract's clause 2, computed in
  `contractOk` (`Contract/Statement.lean`), is this guarantee.
- Assumptions: the writer's parameters meet `Cfg.Ok`, as Java's do. A
  history is made of accepted transactions; a refused one is no step of
  it (G11).
- To Java: links 1, 7, 10 and 12.

**G2. Reads at the latest time and at every earlier time.** A get or a
scan at time t, the latest or an earlier one, at a transaction's time or
between two, returns what a plain sorted map of the keys and values
written by the first t transactions returns. Scans go forward or
backward, with or without a start key, with a limit, and with an end key
when they go forward (the API refuses a backward scan with an end key).

- Proved: `Contract.PE.pe_meetsTop_start` with `Contract.jget_right` and
  `Contract.jscan_right`, the model of Java's readers, which find the
  tree of time t through the top nodes' skip pointers; for the model's
  plain reader, `Contract.get_right` and `Contract.scan_right`.
- Assumptions: as G1; a scan's start and end keys are as
  `Keys.toSegments` makes them (`ScanReq.wf`).
- To Java: links 1, 6 and 7.

## 2.2 Crashes, restarts and eviction

The theorems of G3 to G7 add these assumptions to G1's, called **the
history's bounds** below: the keys of a transaction are distinct (Java's
writer gets one operation per key); the history has fewer than 2^48 − 1
transactions, a premise of the proof that Java does not check (030-26,
2.6); the top nodes' base level is at most 2^62 (1,040,512 at the model's
parameters G = 8,192 and H = 126); the model's run decides which nodes
are still dirty by Java's test and, with eviction, marks as Java does.
`Contract.PE.pe_full` proves that every history PE writes with distinct
keys, fewer than 2^48 − 1 transactions and that base level meets every
clause that ties the DAG to the model of the stream (`MeetsFull`) and
K-LEVEL (`KindsOK`), the premises of the theorems on the stream named
below.

**G3. After a crash, the database is as it was after the last whole
record.** If the stream keeps the records of the first k transactions
whole and nothing after them, a start gives back the database after
transaction k with its whole history: every get and scan at every time up
to k is as G2 says.

- Proved: `Contract.PE.pe_full` with `Contract.full_recovery` (the start
  gives back every node after transaction k, with its history) and
  `Contract.crash_java_reads` (Java's get and scan); for Java's lazy
  start, which reads older nodes when a read first reaches them, with any
  reads and writer follows the model admits (`OpsOK`),
  `Contract.lazy_java_reads`; for the model's reader,
  `Contract.PE.pe_crash_reads`.
- Assumptions: G1's and the history's bounds; Java's tree after the start
  holds what the model's start gives back at the time read, with the top
  nodes the start's structure holds (`HoldsView`, `TopFrom`).
- To Java: links 1, 6, 10, 12 and 13. What a crash leaves in the storage
  is G12.

**G4. Restarts change nothing.** A run with restarts after any
transactions writes the same records as the run without them, and the
reads after restarts and a crash are as G3 says.

- Proved: `Contract.PE.pe_full` with `Contract.full_restart` and
  `Contract.restart_java_reads`.
- Assumptions: as G3.
- To Java: as G3, and link 9.

**G5. Eviction changes nothing.** When BergDB drops nodes from memory and
reads them back from the stream through handles, with any reads,
evictions and restarts: the records written are those of the run without
eviction, a read at a time t reaches exactly the nodes reachable at t,
each as it was then, and Java's get and scan are as G2 says.

- Proved: `Contract.PE.pe_full` with `Contract.full_eviction`,
  `Contract.evict_java_reads` and `Contract.handles_java_reads`.
- Assumptions: as G3, for the tree that the reads through the handles
  give.
- To Java: as G4.

## 2.3 Reclaim

**G6. Reads are right after reclaim's cuts, from the first available time
on.** With a finite retain duration, reclaim deletes the front of the
stream. After any run with handles, reads and evictions in which every cut
is followed by a start from the cut stream, a get or a scan at any time
from the first available time to the latest returns what the plain map of
all transactions written up to that time returns, reclaim's own
transactions included.

- Proved: `Contract.PE.pe_reclaim_reads_steps`.
- Assumptions: G3's; each iteration's steps follow the model of reclaim's
  steps (`StepsOK`: each step scans the live keys at its own time from
  where the step before stopped, puts again every key whose value
  predates the planned cut, with the value it had just before the step,
  and its row; the last step's scan reaches the end); each cut is at or
  after the earlier cuts and its iteration's last step at or before the
  first available time (RC1); Java's two waits hold (RC4); the policies
  that choose each transaction's startup position and first available
  time choose the same on a stream cut at or before its first available
  time (`PolicyCutOK`; it holds for every pair of policies that read no
  stream, `Contract.policyCutOK_of_blind`, as the trace checker's, which
  take Java's choices from the trace); between cuts, reads are made only
  at times from the first available time on.
- The theorem's run starts again from the cut stream at every cut, with
  its memory, the handles and the nodes in the cache, made anew
  (`SIS.runHandlesCut`). Java cuts while it runs and keeps its memory.
  That case is proved for the abstract model of the stream, for any
  structure that meets that model's assumptions (`SIS.T9_handles`, proved
  as `SIS.t9_handles` in `lean/SIS/Proof/HandleCutRun.lean`, which `lake
  build` in `lean/` checks); it is not among the gate's theorems and is
  not tied to PE. For Java it is tested: ReclaimStress, ReclaimReaders and
  the reclaim traces (link 11).
- No theorem says that reclaim makes progress or bounds the stream's
  size: the theorems take iterations that end as a premise. That the
  stream stays within a bound is tested (section 4, item 9).
- To Java: link 11, and as G4.

**G7. Reclaim keeps the users' values.** At every time from the first
available time on, a get of a user key returns the value of the plain map
of the users' operations alone, as if reclaim had written nothing, and so
does a scan whose range holds no reclaim key, at every limit. A scan whose
range includes reclaim's namespace can also return reclaim's rows; with
them removed, it returns the start of the users' scan, every user entry
in order and none skipped, and reclaim's rows count towards the limit.
User keys are those outside reclaim's namespace, `/#i/dreclaim/`, where
the Core refuses a caller's writes.

- Proved: `Contract.PE.pe_reclaim_user_reads_steps`.
- Assumptions: G6's; every maintenance transaction is a step of the model
  or writes only reclaim's namespace (`MaintenanceOK`); each step puts
  nothing else than its rewrites and its row, at the row's key
  `Contract.reclaimRow` (Java's `-current.txt` under `/#i/dreclaim/`), and
  deletes nothing (`StepTx`, in `StepsOK`).
- To Java: as G6. C-STEP checks the row at that key since 2026-11-23
  (030-39, F1; link 11).

## 2.4 Admitted transactions

**G8. Every transaction BergDB admits is one the proved writer accepts.**
The proofs of G1 to G7 speak of the transactions that PE accepts; at a
user database's node size, PE accepts every transaction that Java admits
(at most 500 operations, keys of at most 111 bytes).

- Proved: `Contract.PE.pe_accepts_java`: at node sizes 8, 14, 30 and 62
  (30 is the only node size of a user's database), from a state PE keeps
  whose tree meets the writer's fill rules and has fewer than 2^63 nodes,
  PE accepts every transaction of at most 2^20 operations whose puts' keys
  are well formed and have at most 8,193 segments of 7 bytes. A put of
  any other key PE refuses (`Contract.PE.pe_refuses`).
- Assumptions: the model's G = 8,192 and H = 126, which Java does not
  have; the writer's fill rules, `Contract.PE.FillOk`: the walk
  `shapeFaults` (`Contract/Shape.lean`) finds no fault in the tree, under
  five rules: RootsOK (an inner root of a segment tree has two live
  entries), FillOK (every other key node at least m), LeftmostOK (an
  inner node's smallest live entry is the empty key's), DeadOK (at most
  theta dead entries a key node) and BalancedOK (a segment leaf exactly
  at height 0, an inner node's children one level below it). Tested: the
  tree checker's C-T6 (`faultsAt`, `lean/SIS/Tree/Inv.lean`) checks the
  first four by name, and BalancedOK's levels as KindsOK (each child of
  an inner node one height below it; a node is a segment leaf by its
  height), on Java's tree after every traced transaction, and fails a
  trace that breaks one (link 1's tree sets, `java/stress/level2.sh`, and
  the day's seeds in `java/night.sh`). The contract checker runs
  `shapeFaults` itself on its traces and reports the count apart, without
  failing on it (0 faults on every set of `java/night.sh` of 2026-11-23).
  That PE keeps `FillOk` is not proved; that it keeps the two rules of
  occupancy, RootsOK and FillOK, after every history from the empty
  database is (`Contract.PE.pe_rootFilled_hist`, 030-37, section 9; not
  among the gate's theorems).

**G9. An admitted transaction's index nodes fit the count Java checks
before its go point, for puts and for joins up to one level above the
leaves.** Before a transaction's go point, Java counts the index nodes it
can write (`Dag.dirtyNodeBound`) and refuses the transaction if they could
take its record past the record limit; after the go point, a failure
would fail the database. The key nodes PE writes are at most that count:

- Proved, for transactions of puts: `Contract.PE.pe_dirtyNodeBound_puts`,
  and for the next transaction after every history PE writes,
  `Contract.PE.pe_dirtyNodeBound_puts_hist`.
- Proved, for transactions of puts and deletes that join no inner nodes at
  height two or more (`Contract.PE.NoHigherJoins`; every join of leaves
  and of the inner nodes just above them, repeated joins included):
  `Contract.PE.pe_dirtyNodeBound_twoJoinLevels`, and after every history,
  `Contract.PE.pe_dirtyNodeBound_twoJoinLevels_hist`; and after every
  history PE writes from the empty database, with no fill premise,
  `Contract.PE.pe_dirtyNodeBound_twoJoinLevels_history` (among the gate's
  theorems since 2026-11-23; section 4, item 5).
- Assumptions: node size at least 8; a state PE keeps; the fill rules,
  `FillOk` (tested, as G8), but in
  `pe_dirtyNodeBound_twoJoinLevels_history`, which proves for PE's
  histories the fill it needs; every key of the transaction well formed,
  within the model's segment limit. Java's count is modelled in Lean
  function for function (`Contract/DirtyBound.lean`); that the model is
  Java's rests on reading the two side by side (030-29).
- The theorems count the transaction's operations as the model has them,
  each key once, as a put or a delete (`Contract.DNB.opsKd`). Java's
  admission check (`Db.checkDirtyNodes`) counts otherwise in three cases,
  whose link to the theorems is argued, not proved, and not tested on
  purpose: where Db's cheap estimate (three nodes a level of a put's path,
  twenty of a delete's) fits, Db does not call the count (028-21); a key
  with a key transformation is counted only by that estimate; and a key
  with a value transformation, which may give a put or a delete, is walked
  twice, as a put and as a delete (023-11, review B, B2), where the
  theorems count the one operation it gives.

**G10. The same for joins of inner nodes at height two and above,
tested.** The rest of G9's count: transactions that join inner nodes at
height two or more. (Db's cheap estimate and the transformations, G9, are
argued, not tested on purpose.)

- Tested on purpose: C-T8 of the tree checker (`lean/Check/Tree.lean`)
  checks that its copy of Java's count, on Java's tree before the
  transaction and with the trace's operations, bounds the key nodes each
  traced transaction marks: the tree sets of `java/stress/level2.sh` (in
  `java/night.sh`) and the day's seeds in `java/night.sh`; and
  `DagTester.testDirtyNodeBoundOfPe` (a unit test, `java/before-commit.sh`;
  028-21): random histories and transactions of runs of puts and deletes
  at node sizes 8, 14, 30 and 62, and purpose-made deletes of most keys
  under several inner nodes at node sizes 8, 14 and 30, each with at
  least ten joins. The test counts joins, not the heights at which they
  happen: that these checks reach joins of inner nodes at height two or
  more is not checked.
- 030-26, section 5, item 14 (since 2026-11-23; section 4, item 7).

## 2.5 Tested on purpose

**G11. A refused transaction changes nothing.** A transaction that BergDB
refuses, by a limit or by a check before its go point, writes nothing and
leaves the database as it was.

- Tested on purpose: 030-26, section 5, item 8. DbTesterLimits,
  `DbTesterDelete.testRefusedTransUnchanged` and
  `DbTesterRestart.testEndOfOrdinals`, unit tests in
  `java/before-commit.sh`.

**G12. A crash keeps every synced transaction and leaves at most a torn
tail.** With hard sync, the storage's default (`FileStream(dir)`: every
append is forced to the device before it returns), a transaction whose
record was synced survives a crash of the process, a crash of the
operating system or a power loss; what a crash leaves after the last
whole record is a partly written record at most, which a start leaves
out. With G3 this gives 030-26's "after a crash, the database is as it
was after the last transaction whose record the storage kept whole".
With per-append forcing off (`FileStream(dir, false)`), a synced
transaction survives a crash of the process only: a crash of the
operating system or a power loss can lose it, and can leave a hole in the
tail that was not forced, which recovery does not handle (014-01): the
database may then refuse to start, or fail reads.

- Tested on purpose: 030-26, section 5, items 2 and 3. CrashTest
  (`java/stress/level2.sh` to `level4.sh`), PowerLossTest
  (`java/stress/level3.sh`: a model of the storage's persistence
  boundaries, not a physical power cycle; each seed with forcing on,
  where every image must recover with every acknowledged sync, and with
  forcing off, where an image must keep only what a file force made
  durable and the images with a hole are counted, not failed),
  `java/stress/kill-restart.sh` (1,000 kills in `java/night.sh`, more on
  other seeds in `java/week.sh`).

**G13. A value read back has the bytes that were put.** The proofs treat
a value as an opaque token and the traces carry a 63-bit hash of it
(030-26, section 4); that its bytes are the bytes put is tested.

- Tested on purpose: 030-26, section 5, item 5. Every restart test reads
  back what was written: RestartStress (`java/stress/level1.sh`,
  `level2.sh`), RestartInvariance (`java/stress/level1.sh` to
  `level4.sh`), `java/stress/kill-restart.sh` (`java/night.sh`,
  `java/week.sh`); and the tests that compare whole values: the unit
  tests and the f-tests (`java/before-commit.sh`), the user apps
  (`java/stress/apps.sh`, in `java/week.sh`).

**G14. Readers beside the writer.** One transaction writes at a time
(Java's write lock); readers, eviction and storage threads run beside it.
That their races leave G2 to G7 true for every read that returns is
tested; threads are not modelled. A read that returns gives what G2 says
at its own time; a read of the latest state, at the last transaction
when it began. A read can instead throw `LookupTimeNotAvailableException`
when reclaim's cut overtakes it, also a read of the latest state or of a
time that was still available when it began.

- Tested on purpose: 030-26, section 5, item 4. ReclaimReaders, readers at
  old times while reclaim cuts (`java/stress/level3.sh`, `level4.sh`):
  each read gives the model's answer at its time or throws that exception,
  which it allows only once the read's time is before the first available
  time, and for a read of the latest state only when the cut overtook it;
  the eviction readers' tests (`java/stress/level4.sh`); InterruptStress
  (`java/stress/level3.sh`); jcstress's tests of how nodes are published
  to readers (by hand, before a release; 026-27, D4).


# 3. The links to Java

The proved guarantees speak of the model; these tested facts carry them to
the Java code (030-26, section 3.3). Each is an item of 030-26, section 5,
which names its checks in full; the scripts are `java/stress/level2.sh` to
`level4.sh`, all run by `java/night.sh`, with sets on new seeds each day
in `java/night.sh` and the large set in `java/week.sh`.

- **Link 1, item 1: Java's writer is PE.** The tree checker compares
  Java's writes with the model's PE, node for node, on every traced
  transaction; the contract checker checks Java's DAG after every traced
  transaction (its pass is proved to mean the contract holds,
  `Contract.contractVerdict_sound`); `pecmp` compares the tree checker's
  copy of PE with the proved one; Java's own partial check (`TransCheck`)
  in the unit tests (`java/before-commit.sh`), the f-tests
  (`java/night.sh`) and parts of `java/week.sh`.
- **Link 6, item 6: Java's readers are the model's.** Java's answers to
  the gets and scans of every traced transaction.
- **Link 7, item 7: the trace's operations are the user's transaction.**
  Lookups after restarts against the workload (`conformance.sh`); the
  unit tests and f-tests; `TransCheck` (partial).
- **Link 9, item 9: what the traced run shows holds in every run.** The
  same stream, byte for byte, with and without restarts or eviction
  (RestartInvariance, EvictionInvariance, `conformance.sh`'s runs B and
  E).
- **Link 10, item 10: Java's records and dirty nodes are the model's.**
  The trace checker's step on every traced transaction, the user apps'
  workloads included (`java/stress/apptraces.sh`, in `java/night.sh` and
  `java/week.sh`).
- **Link 11, item 11: RC1 and RC4 at each cut, and Java's steps are the
  model's.** RC1 and RC4 checked at every cut of the reclaim traces;
  C-STEP checks every step against the model of the steps, the values it
  writes back, its row at the model's key (since 2026-11-23, 030-39, F1)
  and no other write (030-27, 030-34), also across restarts and crashes
  (STEP-resume, 030-31); ReclaimStress (`level3.sh`, `level4.sh`). What
  stays tested only is 030-26, section 4.
- **Link 12, item 12: a trace's lines are Java's change.** The trace's
  completeness checks and the trace and tree checkers.
- **Link 13, item 13: Java's start builds what the stream holds.**
  Lookups after a restart and at random times under eviction
  (`conformance.sh`); ReclaimReaders on a cold cache; probes after
  restarts from the cut stream (`level3.sh`).


# 4. Differences from 030-26

Places where 030-26 (as of 2026-11-20) says more than a statement or a
check gives; this list says the narrower thing. Items 1 to 8 are this
list's own; items 9 to 14 were added from the review, 030-39. 030-26 is
corrected for each of them on 2026-11-23 (026-27, step 7), and item 5 also
in the gate (030-39, "Actions").

1. **The user section's one condition.** 030-26's "What it means for a
   user" makes its guarantees depend on one condition, that Java does
   what the model does. They also rest on the platform (section 5, items
   2, 3 and 5: G12, G13) and on threads tested, not modelled (item 4:
   G14); and its crash sentence joins a proved part (G3) and a tested
   part (G12).
2. **The history's bounds.** The user section says "every transaction";
   the theorems of G3 to G7 hold for histories of fewer than 2^48 − 1
   transactions with distinct keys in each (030-26, 2.6, states them; the
   user section does not).
3. **Scans with an end key** (030-26, 2.2: "forward or backward, with or
   without a start key and an end key"). The statements cover an end key
   with forward scans only (`ScanReq.wf`), and start and end keys as
   `Keys.toSegments` makes them. Java refuses a backward scan with an end
   key, so no scan the API allows is left out.
4. **Scans across reclaim's namespace** (030-26, 2.5: "without them it
   gives the users' scan"). With reclaim's rows removed, a raw scan gives
   the start of the users' scan: the rows count towards the limit, so it
   can hold fewer user entries than the limit (`JUserReadsRight`, G7).
5. **The dirty-node bound with no fill premise** (030-26, 2.7,
   `pe_dirtyNodeBound_twoJoinLevels_history`). That theorem is proved in
   `Contract/Proof/DnbMain.lean`, a pinned file, but was not among the
   main theorems of `Axioms.lean`, so the gate did not check its axioms
   and the pin's walk did not start from it. It is since 2026-11-23
   (030-39): `Axioms.lean` lists it, and G9 cites it beside the gated
   `Contract.PE.pe_dirtyNodeBound_twoJoinLevels_hist`, whose fill rules are
   a tested premise.
6. **Db's cheap estimate and the transformations** (030-26, 2.7). Where
   the estimate fits, Db does not call `Dag.dirtyNodeBound`; a key with a
   key transformation is counted only by the estimate; and a key with a
   value transformation is walked as a put and as a delete, where the
   theorems count the one operation it gives (030-39, F7). That these
   counts bound PE is argued (028-21; 023-11, review B, B2), not proved,
   and no check is made for them. 030-26 says that Java refuses by its
   count, without these cases (G9).
7. **The tested part of the dirty-node bound has no item in section 5.**
   030-26, 2.7, says the higher inner joins are tested (028-21; 030-29,
   section 3); the tree checker's C-T8 checks the bound on every traced
   transaction and `DagTester.testDirtyNodeBoundOfPe` on purpose-made
   deletes (G10), but section 5 lists no assumption for them. It is
   section 5's item 14 since 2026-11-23.
8. **RestartStress's scripts** (030-26, section 5, item 5: "RestartStress,
   RestartInvariance (`level2.sh` to `level4.sh`)"). RestartStress runs in
   `level1.sh` and `level2.sh`; RestartInvariance in `level1.sh` to
   `level4.sh`. All four run in `night.sh`, so what runs each night is
   unchanged.
9. **The stream's size** (030-26, 2.5: "reclaim keeps the stream from
   growing without end"). No theorem says that reclaim makes progress or
   bounds the stream's size: the theorems of G6 and G7 take iterations
   that end as a premise (030-39, F9). That the stream stays within a
   bound is tested: `java/stress/large.sh` checks a fixed bound on the
   kept bytes over a long history at 10 million keys (in `java/week.sh`;
   028-43).
10. **The premises of the theorems on the stream** (030-26, 2.3 to 2.5).
    The theorems of G3 to G7 also assume that Java's tree after a start
    holds what the model's start gives back, with its top nodes
    (`HoldsView`, `TopFrom`; tested as 030-26, section 5, item 13), and
    those of G6 and G7 that the policies choose the same on a cut stream
    (`PolicyCutOK`) and that reads between cuts are at times from the
    first available time on (030-39, F9).
11. **A start at every cut** (030-26, 2.5: "after any run with handles,
    evictions and restarts from the cut streams"). The theorem's run
    starts again from the cut stream at every cut; a cut while the
    process runs, keeping its memory, as Java's, is proved for the
    abstract model only (`SIS.T9_handles`) and tested for Java (G6;
    030-39, F4).
12. **Durability and the storage's forcing** (030-26, section 4, "The
    platform", and section 5, items 2 and 3). A synced append is durable
    through a power loss with hard sync, the default; with per-append
    forcing off, through a crash of the process only, and a power loss
    can leave a hole that recovery does not handle (G12; 030-39, F2).
13. **Reads that reclaim overtakes** (030-26, section 5, item 4). A read
    beside reclaim can throw `LookupTimeNotAvailableException` when a cut
    overtakes it, also a read of a time still available when it began;
    the reads that return are right (G14; 030-39, F3).
14. **The fill rules** (030-26, 2.1 and 2.7: "an inner root has two live
    entries, every other node at least m"). The premise `FillOk` has five
    rules: those two, LeftmostOK, DeadOK and BalancedOK (G8; 030-39, F6).


# Log

2026-11-23. Written, from 030-26 and the statements in `lean/contract/` at
004382f9, each guarantee's theorem read in its Lean file (026-27, step 2).

2026-11-23. Corrected after the review, 030-39 (026-27, step 5): G6 (the
start at every cut, `PolicyCutOK` as it is stated, no bound on the
stream's size), G7 and link 11 (the row's key, checked by C-STEP since
this day), G8 and G9 (`FillOk` in full; the value transformations;
`pe_dirtyNodeBound_twoJoinLevels_history`, among the gate's theorems since
this day), G10 (the node sizes of the purpose-made deletes, the joins'
heights not checked), G12 (hard sync, the default, and forcing off), G14
(reads that reclaim overtakes); section 4's items 5 to 7, and items 9 to
14 added.
