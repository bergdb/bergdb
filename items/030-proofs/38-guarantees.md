# 030-38. The guarantees of release 2026.6

Created 2026-11-23 by Frans Lundberg. Status: open.

030-26's "What it means for a user" made a closed, numbered list, G1 to
G14 (006-32, section 6; 026-27, step 2). Each guarantee is marked
**proved**, with its theorem and the statement's assumptions, or
**tested on purpose**, with its assumption in 030-26, section 5, its check
and the script that runs it. The list describes `main` of 2026-11-23
(004382f9), the code planned for release 2026.6. An independent review against the
pinned statements follows (026-27, step 3).


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
stream. After any run with cuts, handles, evictions and restarts from the
cut streams, a get or a scan at any time from the first available time
to the latest returns what the plain map of all transactions written up
to that time returns, reclaim's own transactions included.

- Proved: `Contract.PE.pe_reclaim_reads_steps`.
- Assumptions: G3's; each iteration's steps follow the model of reclaim's
  steps (`StepsOK`: each step scans the live keys at its own time from
  where the step before stopped, puts again every key whose value
  predates the planned cut, with the value it had just before the step,
  and its row; the last step's scan reaches the end); each cut is at or
  after the earlier cuts and its iteration's last step at or before the
  first available time (RC1); Java's two waits hold (RC4); the cache's
  choice of nodes reads nothing of a cut stream (`PolicyCutOK`); between
  cuts, reads are made only at times from the first available time on.
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
  nothing else than its rewrites and its row and deletes nothing
  (`StepTx`, in `StepsOK`).
- To Java: as G6.

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
  have; the fill rules (an inner root has two live entries, every other
  key node at least m), tested: the tree checker's `RootsOK` and `FillOK`
  on Java's tree after every traced transaction (link 1's tree sets,
  `java/stress/level2.sh`, and the day's seeds in `java/night.sh`). That
  PE keeps the fill rules is not proved.

**G9. An admitted transaction's index nodes fit the count Java checks
before its go point, for puts and for joins up to one level above the
leaves.** Before a transaction's go point, Java counts the index nodes it
can write (`Dag.dirtyNodeBound`) and refuses the transaction if they could
take its record past the record limit; after the go point, a failure
would fail the database. The key nodes PE writes are at most that count:

- Proved, for transactions of puts: `Contract.PE.pe_dirtyNodeBound_puts`,
  and for the next transaction after every history PE writes,
  `Contract.PE.pe_dirtyNodeBound_puts_hist`.
- Proved, for puts and deletes, when the deletes join no inner nodes at
  height two or more (every join of leaves and of the inner nodes just
  above them, repeated joins included):
  `Contract.PE.pe_dirtyNodeBound_twoJoinLevels`, and after every history,
  `Contract.PE.pe_dirtyNodeBound_twoJoinLevels_hist`.
- Assumptions: node size at least 8; a state PE keeps; the fill rules
  (tested, as G8); every key of the transaction well formed, within the
  model's segment limit. Java's count is modelled in Lean function for
  function (`Contract/DirtyBound.lean`); that the model is Java's rests
  on reading the two side by side (030-29). Where Db's cheap estimate
  (three nodes a level of a put's path, twenty of a delete's) fits, Db
  does not call the count, and a key with a key transformation is counted
  only by that estimate; that the estimate bounds PE is argued (028-21),
  not proved.

**G10. The same for joins of inner nodes at height two and above,
tested.** The rest of G9's count: transactions whose deletes join inner
nodes at height two or more. (Db's cheap estimate, G9, is argued, not
tested on purpose.)

- Tested on purpose: C-T8 of the tree checker (`lean/Check/Tree.lean`)
  checks that its copy of Java's count, on Java's tree before the
  transaction, bounds the key nodes each traced transaction marks: the
  tree sets of `java/stress/level2.sh` (in `java/night.sh`) and the day's
  seeds in `java/night.sh`; and `DagTester.testDirtyNodeBoundOfPe`, with
  deletes that join on several levels, at node sizes 8, 14, 30 and 62 (a
  unit test, `java/before-commit.sh`; 028-21).
- 030-26, section 5, has no item for these checks (section 4, item 7).

## 2.5 Tested on purpose

**G11. A refused transaction changes nothing.** A transaction that BergDB
refuses, by a limit or by a check before its go point, writes nothing and
leaves the database as it was.

- Tested on purpose: 030-26, section 5, item 8. DbTesterLimits,
  `DbTesterDelete.testRefusedTransUnchanged` and
  `DbTesterRestart.testEndOfOrdinals`, unit tests in
  `java/before-commit.sh`.

**G12. A crash keeps every synced transaction and leaves at most a torn
tail.** A transaction whose record was synced survives a crash or a power
loss; what a crash leaves after the last whole record is a partly written
record at most, which a start leaves out. With G3 this gives
030-26's "after a crash, the database is as it was after the last
transaction whose record the storage kept whole".

- Tested on purpose: 030-26, section 5, items 2 and 3. CrashTest
  (`java/stress/level2.sh` to `level4.sh`), PowerLossTest
  (`java/stress/level3.sh`), `java/stress/kill-restart.sh` (1,000 kills in
  `java/night.sh`, more on other seeds in `java/week.sh`).

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
That their races leave G2 to G7 true is tested; threads are not
modelled.

- Tested on purpose: 030-26, section 5, item 4. ReclaimReaders, readers
  at old times while reclaim cuts (`java/stress/level3.sh`, `level4.sh`);
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
  writes back and no other write (030-27, 030-34), also across restarts
  and crashes (STEP-resume, 030-31); ReclaimStress (`level3.sh`,
  `level4.sh`). What stays tested only is 030-26, section 4.
- **Link 12, item 12: a trace's lines are Java's change.** The trace's
  completeness checks and the trace and tree checkers.
- **Link 13, item 13: Java's start builds what the stream holds.**
  Lookups after a restart and at random times under eviction
  (`conformance.sh`); ReclaimReaders on a cold cache; probes after
  restarts from the cut stream (`level3.sh`).


# 4. Differences from 030-26

Places where 030-26 (as of 2026-11-20) says more than a statement or a
check gives; this list says the narrower thing. 030-26 is brought up to
date in 026-27, step 7.

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
   `Contract/Proof/DnbMain.lean`, a pinned file, but is not among the
   main theorems of `Axioms.lean`, so the gate does not check its axioms
   and the pin's walk does not start from it. G9 cites the gated
   `Contract.PE.pe_dirtyNodeBound_twoJoinLevels_hist`, with the fill rules
   as a tested premise.
6. **Db's cheap estimate** (030-26, 2.7). Where the estimate fits, Db
   does not call `Dag.dirtyNodeBound`, and a key with a key transformation
   is counted only by the estimate; that the estimate bounds PE is argued
   in 028-21, not proved, and no check is made for it. 030-26 says that
   Java refuses by its count, without this case (G9).
7. **The tested part of the dirty-node bound has no item in section 5.**
   030-26, 2.7, says the higher inner joins are tested (028-21; 030-29,
   section 3); the tree checker's C-T8 checks the bound on every traced
   transaction and `DagTester.testDirtyNodeBoundOfPe` on purpose-made
   deletes (G10), but section 5 lists no assumption for them.
8. **RestartStress's scripts** (030-26, section 5, item 5: "RestartStress,
   RestartInvariance (`level2.sh` to `level4.sh`)"). RestartStress runs in
   `level1.sh` and `level2.sh`; RestartInvariance in `level1.sh` to
   `level4.sh`. All four run in `night.sh`, so what runs each night is
   unchanged.


# Log

2026-11-23. Written, from 030-26 and the statements in `lean/contract/` at
004382f9, each guarantee's theorem read in its Lean file (026-27, step 2).
