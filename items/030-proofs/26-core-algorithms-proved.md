# 030-26. BergDB's core algorithms are proved

Created 2026-11-19 by Frans Lundberg. Status: done.

The public statement of what BergDB's proofs cover: the claim, what is
proved, the model, its limits, and the assumptions that are tested instead
of proved. It is written for a reader outside the project, a developer who
decides whether to trust BergDB or a contributor, and describes `main` as
of 2026-11-20. The details are in the items it links.


# 1. The claim

**BergDB's core algorithms are proved.**

Frans chose these words for publication on 2026-11-19. The core
algorithms are those of the Core layer, BergDB's key-value store of byte
arrays (`bergdb.core` and the packages it uses): the writer, which applies
a transaction to the index; the reads, at the latest time and at earlier
times; crash recovery and startup; eviction; and reclaim, which cuts the
front of the stream. Each is proved in Lean, for a model of BergDB, given
a short list of assumptions, each of which is tested (section 5). The Pub
layer, threads and costs are outside the model (section 4).

The claim is for the code on `main` since 2026-11-19 (record format 8).
Release 2026.5 and earlier have an older writer, which these proofs do not
cover. The coming release, 2026.6, has the theme "proven algorithms"
(026).

What it means for a user. If Java does what the model does, which the
tests check transaction by transaction, then:

- every transaction is applied whole: the database after it holds the
  contents before it with exactly the transaction's puts and deletes;
- a get or a scan, at the latest time or at any earlier time still kept,
  returns what a plain sorted map of the keys and values written up to
  that time returns;
- this holds after a crash, after restarts, while data is dropped from
  memory and read back, and after reclaim has cut the front of the
  stream. After a crash, the database is as it was after the last
  transaction whose record the storage kept whole.


# 2. What is proved

Some words first:

- **Transaction, time.** A transaction is a set of puts and deletes,
  applied at once. Each one makes a new time; a read is made at a time.
- **The stream.** BergDB's only durable storage, appended to and never
  changed: one record per transaction, with the nodes it wrote.
- **The key tree.** BergDB's index, a tree of key nodes stored in the
  stream. A transaction never removes or changes what a node held; it
  only adds entries marked with its time, so every earlier state stays
  readable.
- **The plain map.** A sorted map from keys to values, with the
  transactions applied in order. The reads are compared with it.

The theorems are in `lean/contract/`, in the namespace `Contract`.

## 2.1 The writer

BergDB's writer since 2026-11-19 is PE, "plan, then emit": it plans a
transaction's changes over the tree as a whole, then writes each changed
node once ([026-24](../026-release-2026-6/24-pe-trial.md); in Java,
[026-25](../026-release-2026-6/25-pe-java.md)). Every history (a sequence
of transactions) that PE writes from the empty database meets the
writer's contract ([030-04](04-contract-fresh-start.md), section 3.2) at
every transaction:

1. the tree meets its invariants: the keys in order, each node of the
   right kind, a live entry in every node but an empty root, at most M
   entries in a node (the node size, 30 in Java), every pointer naming a
   node that exists, no node reached twice;
2. the tree holds the old contents with exactly the transaction's change:
   each key put has its new value, each key deleted is gone, every other
   key is as it was;
3. every node that existed is still there and of the same kind: a value
   is unchanged, a key node keeps its entries and gets new ones only after
   a mark of the new time; a node that is not dirty (not in D, the nodes
   still to be written to the stream) is unchanged; every key node made
   is dirty. That every node made, values among them, is in the
   transaction's change, which its record writes, is a clause of the
   bridge to the model of the stream (`MeetsFull`, 2.3).

`Contract.PE.pe_meetsTop_start` ([030-21](21-pe-proof.md)), with the top
nodes that readers use to find the tree of an earlier time. PE does not
meet the contract by refusing work: it accepts every transaction whose
keys the tree can hold (`Contract.PE.pe_accepts`), given two bounds of
the proof, on the tree's height and on the program's steps, and refuses a
put of a key the tree cannot hold (`Contract.PE.pe_refuses`). The two
bounds are premises of the proof, on the model's parameters G and H (the
most key segments and the most node heights, less one), which Java does
not have. For G = 8,192 and H = 100, every transaction that Java admits
meets them, on every tree a stream can hold
([030-28](28-writer-copy-checked.md), section 5). That argument is
arithmetic on paper, not in Lean, and uses how full PE keeps its nodes,
which the tree checker checks on Java's tree after every traced
transaction. Java's PE itself refuses nothing; its one guard, a descent
of more than 1,000 nodes in one segment tree, cannot be reached on an
undamaged stream (the same section).

## 2.2 Reads

For every history that meets the contract, a get and a scan at time t,
the latest or an earlier one, give what the plain map after the first t
transactions gives: `get_right`, `scan_right`
([030-05](05-contract-spike.md)). Scans go forward or backward, with or
without a start key and an end key, with a limit. The same holds for
Java's way of finding the tree of an earlier time, a search through the
top nodes' skip pointers: `jget_right`, `jscan_right`
([030-08](08-shape-top.md)). By 2.1, all of it holds for PE.

## 2.3 Crash recovery and restarts

A start reads the tail of the stream and builds the tree from it; older
nodes are read when a read first reaches them (a lazy startup). PE's
histories meet the clauses that tie the key tree to the model of the
stream (`MeetsFull`, by `Contract.PE.pe_full`). For such a history:

- after a crash that keeps the stream up to the record of transaction
  k, a start gives back the tree after transaction k with its whole
  history (`full_recovery`, [030-07](07-bridge.md)), and every get and
  scan at every time up to k is right (`Contract.PE.pe_crash_reads`;
  Java's readers, `crash_java_reads`, [030-14](14-reads-after-crash.md));
- a restart changes nothing: a run with restarts writes the same records
  as one without (`full_restart`), and Java's reads after restarts and a
  crash are right (`restart_java_reads`).

## 2.4 Eviction

When the cache's budget is reached, BergDB drops nodes from memory and
reads them back from the stream through handles. With any reads,
evictions and restarts, the records written are those of the run without
eviction, and a read through the handles at any time reaches exactly the
nodes reachable then, each as it was (`full_eviction`). Java's get and
scan are right under eviction and after a lazy startup
(`evict_java_reads`, `lazy_java_reads`,
[030-17](17-readers-eviction-cut.md)).

## 2.5 Reclaim's cuts

With a finite retain duration, reclaim keeps the stream from growing
without end. In each iteration it walks the live keys in steps, each step
a small transaction that writes again the values written before the
planned cut. Then the part before the cut is deleted, and reads are
possible from the first available time on.

Proved, for every history PE writes: if each iteration's steps follow the
model of reclaim's steps, and each cut meets RC1 (it is at or after the
earlier cuts, and its iteration ended no later than the first available
time) and RC4 (Java's two waits, so that a start no longer reads the part
that is cut), then Java's get and scan, after any run with handles,
evictions and restarts from the cut streams, are right at every time from
the first available time on: `Contract.PE.pe_reclaim_reads_steps`
([030-22](22-reclaim-contract.md) to [030-25](25-iteration-ok.md)).

In the model, each step scans the live keys at its own time, from where
the step before stopped up to the greatest key live when the iteration
began, may stop before or after any key by any rule, and writes again
every value it met that was written before the cut; the last step's scan
reaches the end. Such an iteration writes again every key whose value
predates the cut (`iterationOK_of_stepsOK`), and a cut that meets
reclaim's contract is safe: nothing a read from the first available time
on can reach lies before it (`cutOK_of_rc`,
[030-24](24-reclaim-step2.md)).

## 2.6 The bounds the theorems carry

The theorems about PE's histories have these premises:

- writer parameters (the node size and its thresholds) that meet
  `Cfg.Ok`, as Java's do;
- distinct keys within a transaction (Java's writer gets one operation
  per key);
- the base level of the top nodes (`cf.topBase`, the start top node's
  level, which the parameters give) at most 2^62: it is 827,494 for
  G = 8,192 and H = 100 (030-28, section 5);
- a history of fewer than 2^48 − 1 transactions. This is a premise of
  the proof, not a limit Java checks: Java bounds the top nodes'
  ordinals (005-02), not the number of transactions, and a transaction
  that leaves the tree's root as it was makes no top node.

`pe_accepts` adds its two bounds (2.1).


# 3. The model, and what "proved" means

## 3.1 The model

The model is written in Lean 4, a programming language and proof
assistant, in two packages:

- `lean/`: the abstract model of a self-indexed stream (027-01,
  [sis-model.md](../027-algorithms/01-docs-2026-11-12/sis-model.md)):
  records, startup from the stream's tail, eviction with handles,
  reclaim's cut, proved for any structure that meets its assumptions; and
  the executable model that the trace checkers run.
- `lean/contract/`: the key tree, the writer's contract, PE as Lean
  functions that run (`Contract/PeWriter.lean`), the bridge from the key
  tree to the abstract model, reclaim's contract, the model of its steps,
  and the proofs. It uses Mathlib, Lean's library of mathematics. 131
  files, about 48,000 lines; the gate checks 191 theorems.

The writer's contract is the centre. It says what must hold when a
transaction ends, not how the writer gets there. Reads, recovery,
restarts, eviction and cuts are proved from it, for any writer that meets
it; that PE meets it is proved apart.

## 3.2 What "proved" means here

- **Checked by machine.** Lean's kernel checks every step of every proof.
- **No extra axioms.** The 191 theorems of `lean/contract/Axioms.lean`
  rest only on Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`): no `sorry` (a step left unproved),
  no `admit`, no `native_decide` (which trusts compiled code), no axiom of
  the project's own.
- **Statements pinned.** What a theorem says depends on its statement and
  on the definitions it uses. The files that hold them, with the
  toolchain's and the gate's own, and since 030-28 the tree checker's copy
  of PE and the tool that compares it with the proved writer, are listed
  with their hashes in `lean/contract/statements.pin` (106 files). A
  change to one must change that file in the same commit, so that it
  shows in review; `lean/contract/pins.sh` checks the hashes every night
  (`level2.sh`, step 0).
- **Not vacuous.** A theorem of the form "if these premises hold, then
  ..." is vacuous when its premises can never all hold at once: it is
  true but promises nothing, and with many premises that is easy to miss.
  Examples in Lean show that the main theorems' premises can hold: a
  history PE writes (`Contract.PE.Example.meetsTop`), one that meets every
  statement of the bridge (`Contract.BridgeExample4.meetsAll`), one with a
  reclaim iteration of two steps (`Contract.StepsExample.stepsOK`).
- **Reviewed.** Independent reviews read the statements and their
  definitions against Java; the kernel checks the proofs. Those of 17
  November (030-06, 030-11, and those that 030-14, 030-15 and 030-19
  answer) found faults in the trace checkers and gaps in what was stated;
  each was fixed or added to the tested assumptions. The reviews of 030-24
  and of 030-25 (2026-11-19) found no defect in a statement; their
  qualification, that Java's reclaim steps were checked only through
  their consequence at each cut, is answered by a check of every step
  (030-27; section 4). An independent review of 030-21's
  statements (2026-11-19) found PE's top statements substantive and not
  vacuous within their premises, and the two Lean writers, the proved one
  and the tree checker's copy, making the same choices of tree. It found
  prose that said more than the Lean: the frame's rule for new values, the
  acceptance bounds called limits of Java, the bound on transactions
  taken for Java's, and the top nodes' level where the premise is on
  their base level. These are corrected here and in dated notes in
  030-04 and 030-21. Its other two findings are fixed: the copy was
  neither pinned nor compared with the proved writer as a routine step,
  and is both since 030-28 (section 5, item 1); PE's short way in Java
  reported its dirty nodes in another order than emit's (028-25).

`lean/contract/gate.sh` checks the first three.

## 3.3 From the model to Java

A theorem speaks of the model. A claim about Java follows from it with
facts that are tested, not proved: that Java's writer makes PE's tree,
that Java's readers are the model's, that Java writes the model's records
and that its startup builds what the stream holds (section 5, items 1, 6,
10 and 13). They are tested on traces: logs that test runs of Java write,
with each transaction's operations, the nodes it wrote, its record and
Java's answers to reads ([027-02](../027-algorithms/02-trace-format.md)).
Checkers in Lean check every traced transaction with the theorems' own
definitions; that the contract checker's pass means the contract holds is
proved (`contractVerdict_sound`). The Java code itself is not proved.


# 4. The limits

- **Java is tested against the model, not proved.** The traces are
  generated workloads (node sizes 8 to 62, short and long keys, deletes,
  drains, restarts, eviction, reclaim). A case no trace reaches is covered
  only by the other tests, among them Java's own check of the contract
  after every transaction of its unit tests and f-tests (`TransCheck`).
  That PE accepts every transaction that Java admits rests on an
  argument on paper, not in Lean (2.1); a transaction that the model
  refuses on a trace fails the tree checker.
  An independent review of Java's PE writer (2026-11-19) found one fault,
  in reclaim's accounting, not in the tree; it is fixed (028-26).
- **The platform.** The model assumes that a synced append is durable,
  that a crash leaves at most a torn tail (a partly written last record),
  and that bytes read back are the bytes written. Covered by the crash,
  power-loss and kill tests (section 5, items 2, 3, 5). Damaged bytes are
  detected on a best-effort basis only.
- **One writer; threads are not modelled.** Java's write lock lets one
  transaction write at a time, with readers beside it. Races between
  readers, the writer, eviction and storage threads are outside the
  model; covered by tests with threads (item 4).
- **The Pub layer is not modelled:** objects, user indexes, index jobs.
  It is built on the Core and tested (unit tests, randomized harnesses,
  user applications, kills). A separate Lean model of the user indexes'
  protocol of release 2026.4
  ([020-29](../020-release-2026-4/29-index-proof/readme.md)) has proofs of
  its own, not part of this claim.
- **Reclaim's arithmetic and Java's steps are tested.** RC1 and RC4 are
  checked at every cut of the reclaim traces, and so is the cut's safety
  as a whole. Every step of every iteration in those traces is checked
  against the model of the steps ([030-27](27-step-check.md)): the chain
  of steps, the range each scans, the values it writes again, and the cut
  at the iteration's last step. Still tested only: that the trace's line
  for a step is what Java's step holds in memory, Java's end key itself,
  the steps of runs with restarts and crashes (argued in 030-25, section
  2, and covered by the reclaim tests), and configurations the traces do
  not reach (30 to 200 keys, node sizes 8 and 14).
- **No cost, time or memory statement is proved:** not the work of a
  start (bounded startup, [007](../007-bounds/readme.md), is measured and
  tested), not the size of records or of the stream, not the heap, not
  pauses. The tree's shape rules that only costs depend on (how full the
  nodes are, balance, dead entries) are not in the contract. These are
  measured and tested: the count gates in `night.sh`, `timing.sh`.


# 5. The tested assumptions

[030-04](04-contract-fresh-start.md), section 3.5, listed 13
assumptions, each tested. Two of them, 1 and 11, are now proved in part;
what is left of them follows "Left". Beside each is its test and where it
runs: `before-commit.sh` before every commit to `java/`; the level
scripts (`java/stress/level2.sh` to `level4.sh`) in full in `night.sh`,
about once a day while there is development; `week.sh`, with more kills,
fuzzing and the large trace set, before every release.

1. ~~The writer meets the contract~~, proved for PE (030-21). Left:
   **Java's writer is PE.** The tree checker compares Java's tree with
   the model's PE, node for node, on every traced transaction of the
   small, drain and reclaim sets (`level2.sh`). The contract checker
   checks Java's tree after every traced transaction (`level2.sh`; the
   medium set in `night.sh`). Java checks the contract itself
   (`TransCheck`: the unit tests in `before-commit.sh`, the f-tests in
   `night.sh`). The tree checker's PE (`lean/SIS/Tree/Pe.lean`) is a copy
   of the proved one, rule for rule; `pecmp` compares the two at every
   transaction of the same three sets: the writes in their order, the
   trees and the top nodes (`level2.sh`, step 8c; 030-28). The copy is
   pinned, and its hash is checked every night (`level2.sh`, step 0). So
   on those traces Java writes what the proved writer writes.
2. **A synced append is durable.** CrashTest (`level2.sh` to
   `level4.sh`), PowerLossTest (`level3.sh`), `kill-restart.sh`
   (`night.sh`: 1,000 kills; `week.sh`: 3,000 more).
3. **A crash leaves at most a torn tail.** The same tests.
4. **One writer.** ReclaimReaders, readers at old times while reclaim
   cuts (`level3.sh`, `level4.sh`); the eviction readers' tests
   (`level4.sh`); InterruptStress (`level3.sh`); jcstress's tests of how
   nodes are published to readers (by hand, before a release).
5. **The bytes decode to what was written.** Every restart test reads
   back what was written: RestartStress, RestartInvariance (`level2.sh`
   to `level4.sh`), `kill-restart.sh`. Damaged bytes: best effort only.
6. **Java's readers are the model's.** Java's answers to the gets and
   scans of every traced transaction (`level2.sh`; the medium set in
   `night.sh`), and Java's own searches of every node and of the top
   nodes in the traces with LIVE lines (`level2.sh`).
7. **The trace's operations are the user's transaction**, after the key
   and value transformations. Lookups after restarts, against the
   workload (`conformance.sh`, in `level2.sh` to `level4.sh`); the unit
   tests and f-tests; `TransCheck`.
8. **A refused transaction changes nothing.** DbTesterLimits,
   `DbTesterDelete.testRefusedTransUnchanged`,
   `DbTesterRestart.testEndOfOrdinals` (unit tests, `before-commit.sh`).
9. **What the traced run shows holds in every run**, after restarts and
   with eviction and reclaim. The same stream, byte for byte, with and
   without restarts or eviction (RestartInvariance, EvictionInvariance,
   and `conformance.sh`'s runs B and E: `level2.sh` to `level4.sh`);
   `TransCheck` in every unit test and f-test.
10. **Java's records and dirty nodes are the model's.** The trace checker
    runs the model's step on every traced transaction and compares the
    record and the nodes to write (`level2.sh` to `level4.sh`; the medium
    set in `night.sh`, the large one in `week.sh`).
11. ~~A cut is safe~~, proved from reclaim's contract and the model of its
    steps (030-24, 030-25). Left: **RC1 and RC4 at each cut**, checked at
    every cut of the reclaim traces (`level3.sh`); and **Java's steps are
    the model's**: every step of the reclaim traces checked against the
    model of the steps, after the check's own fault test (C-STEP, 030-27:
    `level3.sh`), and the reclaim tests (ReclaimStress: `level3.sh`,
    `level4.sh`). Still tested only: section 4.
12. **A trace's lines are Java's change.** The trace's completeness checks
    (030-09) and the trace and tree checkers (`level2.sh` to `level4.sh`).
13. **Java's startup builds what the stream holds.** Lookups after a
    restart and at random times under eviction, against the workload
    (`conformance.sh`, in `level2.sh` to `level4.sh`); ReclaimReaders on a
    cold cache (`level3.sh`, `level4.sh`); probes after restarts from the
    cut stream (`level3.sh`).


# 6. How it stays true

- **The gate.** Every change to the proofs passes `lean/contract/gate.sh`
  before it lands on `main` (030, "The rules"): the build, no `sorry`, the
  standard axioms only, the pinned statements. A statement changes only
  by Frans's decision, and the change shows in `statements.pin`. The gate
  runs on changes to the proofs, with a build that needs Mathlib.
- **The pins and the copy, every night.** `level2.sh`, in `night.sh`,
  checks the hashes of `statements.pin` without a build (step 0), so a
  pinned file changed outside proof work fails that night; and it
  compares the tree checker's copy of PE with the proved writer on its
  traces (`pecmp`, step 8c; 030-28).
- **The checks.** The tests of section 5 run as the code changes, in
  `before-commit.sh`, the level scripts, `night.sh` and `week.sh`.
- **A change to the writer or to reclaim** must keep Java equal to the
  model on the traces, which the level scripts check. So the change is
  made in the model too: in PE (`Contract/PeWriter.lean`) with its proof
  and in the tree checker's copy, or in the model of reclaim's steps with
  its proof and in the step check. A change the proofs do not cover is a
  change of this claim.
- **This page** states the claim as of 2026-11-20, with the theorems and
  items of that day.


# 7. History

- Until 17 November 2026: the abstract model of the stream (001;
  027-01), and a model of the key tree that followed Java's old writer
  step by step; its last premise stayed open, and that line was stopped
  on 17 November and removed from `main` on 18 November (030, D1; 030-18).
- 17 November: the contract approach
  ([030-04](04-contract-fresh-start.md)); reads, recovery, restarts,
  eviction and cuts proved from the contract (030-05 to 030-17).
- 18 to 19 November: PE, a simpler writer, proved to meet the contract
  ([030-21](21-pe-proof.md)); Java's writer replaced by it, record format
  8 ([026-25](../026-release-2026-6/25-pe-java.md)).
- 19 November: reclaim's contract and safe cuts (030-22 to 030-24), and
  its iteration proved from a model of its steps
  ([030-25](25-iteration-ok.md)). The aim of 030 was reached. The same
  day, every reclaim step on the traces checked against that model
  ([030-27](27-step-check.md)), and the tested writer compared with the
  proved one every night ([030-28](28-writer-copy-checked.md)).


# Log

2026-11-19. Written, from 030-04, 030-21 to 030-25 and `lean/contract/`
at 3b85b7e6 (191 theorems), on the branch `030-26-core-proved`; it lands
on `main` when Frans has read it.

2026-11-19. Corrected after an independent review of 030-21's statements,
each point checked against the Lean: the frame's clause 3 as `Frame`
states it (2.1), the acceptance bounds as premises of the proof (2.1,
section 4), the bound on transactions and the top nodes' base level
(2.6), the copy of PE in the tree checker (section 5, item 1), and the
review itself (3.2). Dated notes in 030-04, section 3.2, and 030-21.

2026-11-20. Brought up to date with 030-27 (every reclaim step checked on
the traces), 030-28 (the copy of PE compared with the proved writer and
pinned, the pins checked every night, `pe_accepts`' premises met for
Java's G and H) and 028-27 (`night.sh` and `week.sh` disjoint), on main
7d02a8ef, each against those items and the scripts.

2026-11-20. Landed on `main` by coord-1118: Frans decided to land it and
then read it there, and to decide afterwards how it is kept.
