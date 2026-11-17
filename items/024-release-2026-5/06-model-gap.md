# 024-06. The model gap: the Lean model against release 2026.4's code

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11), a
study: its A made in 024-09, its B in 024-12 and 024-22; questions 5 and
8 not answered (024-28, section 6).

For aim 4 of 024-04, "the model matches": what the Lean model in `lean/`
describes, how the Java code of release 2026.4 is tied to it, where the
two differ, mechanism by mechanism, and what closing the gap would take.
A study by reading: `lean/`, `java/`, the items, `git log` and `git diff
release-2026.3..release-2026.4`. Nothing was built or run.


## 1. Summary

* **The model is the theory of the stream and of memory, not of the
  tree.** 52,271 lines of Lean, 3,624 of them trusted definitions and
  statements, 43,595 proofs; no `sorry` and no axiom by grep. It proves
  recovery, restart invariance, lazy reading, eviction with handles,
  safe cuts and the startup section's bound, all for an abstract
  structure: nodes with histories of entries, where a transaction's
  change is an opaque function (`Spec.exec`). It has no key, no put, get,
  scan, delete or split.
* **The tie is a check of runs.** The trace checker runs the model's own
  `step` on traces of small Java runs and compares records, D, first
  touches, cuts and the handle state. It sees a transaction's net change;
  it does not see keys, bytes, costs, threads or the take's choice.
* **2026.4 changed no Lean source.** `lean/SIS` was last changed on
  2026-10-29, `lean/Check` on 2026-10-28; the release's diff in `lean/` is
  README.md alone, an edit of form. Nothing had to change: the whole
  delete path (UP, LE-b, RC, the take-back) is inside `exec`. What changed
  instead: A2A3Check2 counts a taken-back node as not made, and
  `conformance.sh` requires no adoption in the a6 traces where it
  required one (section 4.3).
* **So the answer depends on what "matches" means.** In the sense used
  until now, every Java transaction is a step of the model and no proof
  is broken: 2026.4 matches, as far as the traces reach. In Frans's sense
  ("The internal core algorithms of the database must be right. This is
  what we want to prove correct."; 024-04, section 2)
  the gap is everything the Core does with keys (`Dag`, `KeyNode`,
  `GetMany` and `TopDs`, 5,215 lines of Java with their tests), reclaim's
  scheme (checked at each cut, not proved), and every cost property but
  the startup section's.
* **Four weak points found in the tie itself** (section 4.4): the
  physical layer's assumption `PhysStep` is argued in a text older than
  the delete path and checked nowhere; the argument for reclaim's scheme
  rests on "a key range only shrinks", false since 2026.4; the gates'
  standing configurations barely reach the take-back, and P5's branch
  passed level1 to level4 in full with fault 12 in its head; Lean's take
  is the rule before 005-79.
* **Proposed order** (section 5): repair the tie (small, now); decide
  the algorithm changes; then the key tree as a Lean definition that the
  checker runs against Java (days); then its proofs (large, hard); then
  reclaim's scheme and the costs. Merges and compaction change the tree,
  the last touch and P8 change the scheme: each is modelled after its
  change, or with it, not before.
* **Questions for Frans** (section 7): which sense of "matches" 2026.5
  aims at; one rerun path or two; compaction never in place; keys in the
  trace; which cost statements go to Lean.


## 2. The Lean model today

Lean 4.34.1, no Mathlib (`lean/lean-toolchain`). `lake build` checks
every proof; the level scripts run it.

### 2.1 Sizes

| Part                                       | Files | Lines  |
|---|---|---|
| Trusted: definitions and statements        | 15    | 3,624  |
| Proofs, `SIS/Proof/` (1,542 theorems)      | 89    | 43,595 |
| Examples, run by `#guard` (110 of them)    | 6     | 2,705  |
| The trace checker, `Check/`, TraceCheck    | 5     | 2,065  |
| Test programs and the two library roots    | 5     | 282    |
| All                                        | 120   | 52,271 |

By grep over `lean/SIS`, `lean/Check` and the top-level files: the word
`sorry` 0 times, `axiom` 0, `native_decide`, `admit`, `unsafe`,
`implemented_by`, `extern` and `opaque` 0. Four `@[csimp]` theorems in
Check/Fast.lean replace model functions by faster ones in the compiled
checker, each proved equal. `#print axioms` was not run here; the
release night ran it (020-31, section 2, the step "checks").

### 2.2 The trusted files, by level

| File in `lean/SIS`         | Lines | What it defines or states                              |
|---|---|---|
| Basic.lean                 | 151   | entries, histories, P, `Changes`, `Spec`, reachability |
| Stream.lean                | 108   | versions, records, lv(x), `good`, `dirty`              |
| Algorithm.lean             | 224   | <P, D, S>, `Algo`, `javaTest`, marking, `step`, `run`  |
| Startup.lean               | 127   | Rule R (`follow`), `readFrom`, `rerun`, `startup`      |
| Assumptions.lean           | 136   | `SpecOK`, `StepOK` (A2 to A5), `VirtStep`, `RunOK`     |
| Theorems.lean              | 95    | T1, T2, T13                                            |
| Phys.lean                  | 670   | objects, the first touch, `lazyStartup`, `PhysStep`,   |
|                            |       | TREE (`treeAt`), A6' (`adoptAt`), A-COPY (`CopyStep`)  |
| PhysTheorems.lean          | 152   | lemma M, T1-L, CC, T2-L, T15                           |
| Handle.lean                | 873   | handles, `HMem.followR`, the record rule, `HMem.evict`,|
|                            |       | `handleStartup`, rule 4 by position                    |
| HandleTheorems.lean        | 311   | the invariants; T-CACHE, T-READ, T2-C, T-PIN           |
| Reclaim.lean               | 171   | `cutStream`, `ReadsPhys`, `CutOK`, `SameFrom`          |
| ReclaimTheorems.lean       | 94    | T13', T8, T12                                          |
| HandleReclaimTheorems.lean | 149   | T9 and T12 over handles; rule 4 after a cut            |
| Bound.lean                 | 170   | `Stream.cost`, `KeepsUp`, `takePolicy`, `javaTake`     |
| BoundTheorems.lean         | 193   | the T3 family                                          |

Level 0 and Level 1 have no file: of the multiversion map and the replay
of the whole log, "neither is written down as a proof" (docs/levels.md,
section 4). Level 2 is the first six files and, for lazy reading, the two
Phys files; Level 4 the two Handle files, on Phys.lean's assumptions;
Level 3 the three on reclaim; the bounds of 007 the last two.

### 2.3 The theorems, in plain words

* **T1** (`T1_recovery`, `T1_crash`, `T1_nodes`). After any run and a
  crash anywhere, startup from the stream gives back every node with its
  whole history, and the same D.
* **T2** (`T2_restart`). A run with restarts after any transactions
  appends the records of the run without restarts.
* **T13** (`T13_markExact`; with reclaim's touch `T13_markTouch`).
  Marking the access path of a change finds exactly the index nodes that
  got dirty.
* **Lemma M** (`LM_newer`, `LM_ruleR`, `LM_cutTo`). A newer version of a
  node serves every time an older one serves.
* **T1-L, CC, T2-L** (`T1_lazy`, `CC_canonical`, `T2_lazy`). With nodes
  read from the stream at first touch, reads at every time give P, each
  canonical object holds its node's whole history, and the records are
  those of the run without restarts. `T15_closed`: D is closed upward.
* **T-CACHE, T-READ, T2-C, T-PIN** (`tc_handles`, `tr_handles`,
  `t2_handles`, `tr_handles_restarts`, `tp_handles`). With any reads and
  evictions between transactions, the writer with handles appends the
  model's records and leaves the model's D; reads at every time give P;
  restarts change nothing; every object that is not pinned may be
  evicted.
* **Rule 4 by position** (`rule4Pos_handles`, `runPos_handles`; after a
  cut `rule4PosCut_handles`, `runPosCut_handles`). Java's startup since
  005-57 links what the model's startup links.
* **T8, T9, T12** (`T8_recoverCut`, `t9_handles`, `T12_restartCut`,
  `t12_handles`). After a safe cut (`CutOK`), startup from the cut
  stream, and reads in the running process, give the lookups from the
  first available time on, and the records stay those of the run without
  cuts.
* **T3** (`T3_section`, `T3_take`, `T3_take_decrease` and nine more).
  The startup section without its last record costs less than twice the
  startup distance, for BergDB's take with any pace.

### 2.4 What the theorems assume of the structure

Every theorem is about any `Spec` that meets these; none is proved for
BergDB's tree, which is not in Lean.

| Assumption                           | Lean                      | Held for Java by             |
|---|---|---|
| A2 to A5, ids, data nodes            | `StepOK`, `RunOK`         | C-A on traces; A2A3Check2    |
| The virtual root, R1 to R4           | `VirtInit`, `VirtStep`    | C-A on traces                |
| New live children, no child moved    | `PhysStep`, `PhysRunOK`   | argued (011-11, 13.3; M47)   |
| TREE, A6', A-COPY                    | `EvictRunOK`              | C-A on traces; A2A3Check2    |
| The root seen by its live children   | `ExecRootOK`, `VirtLiveOK`| argued (001-07, 2.8, 2.9)    |
| The take ignores what a cut removed  | `PolicyCutOK`             | argued (001-07, 2.8, 2.10)   |
| Each cut is safe (T-SCHEME)          | `CutOK`                   | C-CUT at every cut of traces |
| The take keeps up; no record limit   | `takePolicy`, any `Pace`  | TakeCheck, 300 cases, once   |


## 3. How the code is tied to the model

### 3.1 The steps

| Script, step      | What runs                                           | Traces (full)   |
|---|---|---|
| `level2.sh`, 7    | A2A3Check2, 3 configurations; `lake build`;         | 70 (7 x 10)     |
|                   | `conformance.sh small`                              |                 |
| `level3.sh`, 8    | `lake build`; `conformance.sh reclaim`              | 25 (5 x 5)      |
| `level4.sh`, 5    | `lake build`; `conformance.sh evict` (C-P, C-H)     | 45 (15 x 3)     |
| `night.sh`, 4, 9  | `lean-tests.sh` (sistest, phystest, reclaimtest);   | 9               |
|                   | `conformance.sh medium`                             |                 |
| `night.sh large`  | `conformance.sh large`                              | 12              |

* A trace is 40 to 800 transactions on 1 to 3,000 keys at node sizes 8
  to 30; the large set goes to 5,000 transactions and node size 62.
* A2A3Check2 is Java only: it checks A2, A3, A5, TREE, A6' and A-COPY on
  the Dag, and Db's marked nodes against the model's rule.
* None of this runs in `before-commit.sh`, the only requirement for a
  commit.

### 3.2 What a trace holds, and what the checker compares

`TraceExport` (`java/stress`, 1,513 lines) writes, for each transaction,
its net change (NEW and ADD lines), its record (REC, VER, H, F, GD) and D
(docs/trace-format.md). An entry is one of six kinds: a key klong `K c y`
with a compare value and a child, a delete bitmap `D` by compare values,
a top node's pointers, a value's hash. The checker makes the model's
`Spec` from the trace: `exec` returns the trace's change, and `live` is
`blive` (Check/Trace.lean, 15 lines), the only place where a key node's
meaning is written in Lean.

* **C-A**: the assumptions of 2.4's rows 1, 2 and 4 hold for every
  transaction.
* **C-S**: the model's `step`, from Java's state and with Java's startup
  pos, gives Java's record and D.
* **C-V**: Java's live children are `blive`'s (in three configurations).
* **C-R**: the exporter's own probes passed: lookups after restarts, and
  the stream of the run with restarts equal to the run without.
* **C-L**: every first touch after a restart follows Phys.lean's rule.
  **C-CUT**: `CutOK` at every cut Java decides, the physical cut at or
  below it.
* **C-P, C-H**: Java's pointers and handle state, under forced eviction
  schedules, meet the model's invariants with handles.

### 3.3 What the tie cannot see

* **Keys and values.** A trace has compare values and hashes. Key order,
  routing, a node's lower bound, the empty key, the segments of a long
  key and the answer of a get or a scan are not in it. Lookups are
  checked by Java against the workload, and reported as `PROBE ok`.
* **Inside a transaction.** Only the net change: a node made and taken
  back is in no line, and neither is an entry added and removed again.
* **The take.** C-S takes each record's startup pos from Java.
* **Bytes and costs.** The record format, the record limit, checksums,
  meta blocks, a torn tail; time, bytes written, memory.
* **Threads.** One writer, no readers beside it; the eviction thread is
  held off while the state is exported.
* **Size.** A fault that needs a larger transaction or tree than the
  sets make. P5's branch passed level1 to level4 in full (023-07, section
  3.3), and its head has fault 12, which leaves a database that cannot be
  opened (023-08, section 4); a review found it.
* **Reclaim's scheme.** The trace has the touches, the first available
  time and the cuts, not why the scheme chose them.
* **The Pub layer.** Objects and indexes; 020-29's index proof is on a
  branch, not merged.

What it did find in 023: three of the delete path's faults that every
other gate had passed (023-05 P1, section 5): a bitmap after its klong
(C-A), a follow that marked an unchanged node (C-S), a taken-back node
left in the node table (C-H).


## 4. The gap, mechanism by mechanism

### 4.1 The table

Status: **P** modelled in Lean and proved, with Java checked against it;
**M** modelled, not proved; **C** not modelled as a rule, its effect on
each traced run is checked (the model takes it as given); **N** not in
the model and not seen by the checker.

| Mechanism                                | Status | Changed in 2026.4            | Lean followed |
|---|---|---|---|
| Put: the path, the klong, the value node | C      | no                           | -             |
| Get: the walk at a time                  | P      | no                           | -             |
| Get: the search by key                   | N      | LE-b's lower bound           | no model      |
| Scan: order, range, the end key (SE)     | N      | SE, new                      | no model      |
| Delete: the bitmap in the leaf           | C      | the bitmap before its klong  | Java fitted   |
| The upward unlink (UP)                   | C      | new                          | not needed    |
| The empty key first (LE-b)               | N      | new                          | no model      |
| Root collapse (RC)                       | C      | new                          | not needed    |
| The take-back, fault 12's fix            | C      | new                          | checks changed|
| Space splits, in place and not           | C      | LE-b's half; the repoint     | not needed    |
| Time split                               | C      | no                           | -             |
| Long keys, segment trees                 | C      | RC of a segment root         | not needed    |
| Top nodes, the virtual root              | P      | no                           | -             |
| The skip list's search                   | N      | no                           | -             |
| Marking, step 3                          | P      | the quiet follow             | not needed    |
| The take, the startup pos                | P      | no                           | -             |
| Rule A, the record, the references       | P      | no                           | -             |
| `dirtyNodeBound`, the record limit       | N      | counted by node (K4)         | no model      |
| The sort, one operation a key            | N      | new                          | no model      |
| Startup: Rule R, D, rule 4 by position   | P      | validations, format 6        | not needed    |
| The rerun repeats the first run (A1)     | C      | it redoes UP and take-backs  | not needed    |
| Handles: follow, evict, the pins         | P      | `Cache3.dropNode`            | not needed    |
| CLOCK, the budget, `Residents`           | N      | no                           | -             |
| The dead hand                            | P      | new                          | not needed    |
| Reclaim: the touch                       | P      | no                           | -             |
| Reclaim: iterations, scan, rewrites      | C      | no (P8 left out)             | -             |
| The cut, when it is safe                 | P      | no                           | -             |
| The physical cut; a read that expires    | C, N   | no                           | -             |
| The first available time                 | M      | no                           | -             |
| Failure, the go point, threads, the clock| N      | several fixes                | no model      |

### 4.2 Notes on the rows

* **Put, splits, time split, long keys.** The model has none of their
  rules. What Java does is a `Changes` value to it, and C-A and C-S check
  that the value meets the assumptions and gives Java's record.
* **Get and scan.** `tr_handles` covers the walk: every pointer a read
  follows, at any time, gives the node as P has it. That the search picks
  the right klong for a key, and that a scan returns a range in order, is
  in no Lean file and no trace.
* **Delete.** `blive` reads a bitmap as "the key entries before it with
  these compare values"; Java's bitmap deletes by index. In 023 Java was
  changed to fit (fault 1: the bitmap precedes a new klong of the same
  compare value; 023-07, section 5.1). The rule is now Java's for the
  checker's sake.
* **UP and RC.** Net effect: entries at tt in the nodes on the path,
  older nodes no longer reachable, one new top node for a collapsed
  space root. A5, TREE, A6' and A-COPY hold in A2A3Check2's eight
  configurations (023-09, sections 5.1 and 7.3) and on the gates' traces.
* **LE-b.** A rule about keys: the smallest live klong of an inner node
  is the empty key. The trace cannot state it. Java's UnlinkFuzz checks it
  (invariant I1), and UnlinkFuzz is in no script (4.4).
* **The take-back.** To the model the node was never made. The exporter
  never sees it, as it is reachable from nothing and in no record. Its id
  is used up, which the model allows (ids need only be fresh). Java
  drops its object from the node table (`Cache3.dropNode`), which the
  model's table never held; C-H found a missing drop (fault 3).
* **The rerun.** T2 needs `exec` to be a function of the transaction and
  the state (A1). That Java's rerun of a format 6 record redoes the climb,
  the take-backs and the ids is checked by the run with restarts (C-R)
  and RestartInvariance, byte for byte; not proved.
* **The dead hand.** An eviction schedule: it evicts only objects that
  are not pinned and are written, which `tp_handles` allows at any time,
  and `t9_handles` covers the reads after the cut. Its trigger and its
  purpose, memory released after a cut, are not statements of the model.
* **Reclaim's scheme.** `Reclaim.java` is unchanged in 2026.4 but for a
  comment and two liveness tests. T-SCHEME, that the scheme gives safe
  cuts, is checked at every cut (C-CUT 0 of 305 on `023-core`; 023's
  log), not proved (001-07, section 5).

### 4.3 What the release changed on the Lean side

* **In `lean/`:** README.md only (commit `9413319e`, 021-02 and 021-03:
  its dated log moved to 011-12, tables made lists). No definition, no
  statement, no proof, no checker line. The trace format and
  `TraceExport` are unchanged too.
* **A2A3Check2** (13 lines, `f4c469d3`): a node made and taken back in a
  transaction counts as not made (Z18; 023-07, D11).
* **`conformance.sh`** (`80105ef1`, Q9 of 023-08): the a6 and e-a6 traces
  must show 0 adoptions below the old parent. Until then they had to
  show at least one, to prove that the weaker A6' was needed. Fault 12's
  fix removed the adoption, so A6 itself may now hold (024-01, LM1).
* **docs/sis-model.md:** a paragraph in 3.4 on the delete path ("The
  Lean model is not changed") and a point in 11: the rerun's rule is part
  of the record.

### 4.4 Weak points in the tie, found here

1. **`PhysStep` is argued, and the argument is older than the delete
   path.** `tc_handles`, `tr_handles`, `T1_lazy`, `t9_handles` and
   `t12_handles` assume `PhysRunOK`. 011-11, section 13.3, argues it from
   a klong being live until a later klong of its key, and from "no path
   moves a child from one current node to another" (M43), written before
   UP, LE-b, RC and the take-back; the checker has no check of it
   (lean/README.md, "Not done"). By reading it still holds: `liveNew` is
   a property of `blive`, and `adopt` follows from TREE and A5, which C-A
   checks. Neither step is a Lean lemma.
2. **T-SCHEME's argument has a false premise.** 001-07, section 5, step
   3: "A key range only shrinks when a node splits". Since 2026.4 a range
   also grows: the next child takes the empty key's range (LE-b), a left
   sibling takes an emptied child's, a child takes its root's (RC). A
   grown range contains the old one, so the conclusion looks unharmed,
   but that is a reading, not an argument on file. C-CUT is the evidence.
3. **The standing configurations barely reach the take-back.**
   `level2.sh`'s three A2A3Check2 configurations take back 0 nodes; the
   five that do (12 to 559) were run by hand (023-09, section 5.1). The
   draining trace configurations that 023-07, section 6.2, asked for are
   not in `conformance.sh`, and UnlinkFuzz is in no script. How often the
   70 standing traces reach UP, RC and the take-back could not be
   determined by reading; the traces in `java/build` are of 2 November.
4. **Lean's take is not Java's arithmetic.** `javaTake` in Bound.lean is
   the double rule before 005-79 (015-03, open), and no gate compares
   Java's startup pos with it. Harmless for T3: `T3_take` holds for any
   pace.


## 5. What "the model matches" would take

### 5.1 The pieces

| Id | Piece                                                     | Size  | Hard proof |
|---|---|---|---|
| A1 | Draining configurations in the gates; UnlinkFuzz at night | small | no         |
| A2 | `PhysStep` as two Lean lemmas, or a C-A check             | small | no         |
| A3 | T-SCHEME's step 3 argued again, for ranges that grow      | small | no         |
| A4 | A6 for A6' checked (LM1); 015-03 done or closed           | small | no         |
| B0 | Keys in the trace; the checker checks I1 and the lookups  | days  | no         |
| B1 | The key tree as a Lean `Spec` with its own `exec`         | days  | no         |
| B2 | The checker runs B1's `exec` against Java's change        | days  | no         |
| C1 | B1 meets every assumption of 2.4 but `CutOK`              | large | yes        |
| C2 | B1 is a multiversion map: get and scan at every time      | large | yes        |
| C3 | `dirtyNodeBound` is a bound, on B1                        | days  | yes        |
| D1 | Reclaim's scheme on B1: iterations, steps, waits          | days  | no         |
| D2 | T-SCHEME proved                                           | large | yes        |
| E  | The cost statements of section 6                          | large | yes        |

* **A1 to A4** repair the tie as it is. They need no decision, and no
  algorithm change invalidates them.
* **B0** makes LE-b and the lookups visible to Lean: a trace format 3
  with each klong's key and each transaction's operations, and a
  reference map in the checker.
* **B1** is the piece that makes the model "describe the algorithm the
  code runs": search, put, the splits, the delete with UP, LE-b, RC and
  the take-back, segment trees, top nodes. It must give Java's entries
  and ids exactly, as the C clone gives Java's bytes (012). Perhaps
  1,500 to 2,500 lines of definitions; the work is the exactness.
* **B2** replaces "the model takes the change as given" by "the model
  computes the change": C-S then covers the tree. From here on, a Core
  change can be made in Lean first and Java held to it.
* **C1** removes the assumptions: T1 to T12 then hold for BergDB's tree,
  not for "any structure that meets A2 to A5". **C2** is the statement
  that is missing today: the database answers right. Both are B-tree
  proofs without Mathlib, with time splits and long keys; the existing
  43,595 lines of proofs took from 12 to 29 October. A guess: one to two
  weeks of agent work each, at the highest effort, with an uncertain end.
* **D2**: 001-07, section 5, judged it "several days with an uncertain
  outcome". With B1 the touch's coverage can be proved, not assumed.

### 5.2 The planned changes, and what each would invalidate

| Change planned for 2026.5         | Invalidates, if done before it | Today's proofs |
|---|---|---|
| Merges at the delete              | B1's delete, C1, C2, C3        | none           |
| Dead klongs, by a new node        | B1's cases, C1, C2             | none           |
| Dead klongs, in place             | everything                     | all            |
| The last touch (CL7)              | D1, D2; A3's argument          | none           |
| P8, a step scans at its own time  | D1, D2                         | none           |
| Fix (a) of the window (dropped)   | everything on INV-1            | T1, T2 and on  |
| `maintain()`                      | D1 (one more trigger)          | none           |
| The builder's rule; cache tables  | nothing                        | none           |
| Two rerun paths by record format  | B1, C1, C2 twice               | none           |

* **Merges** change `exec` and nothing else: P5 met A2 to A5, TREE, A6'
  and A-COPY in its runs (023-07, section 5.9). They also make the
  proportional bounds true (section 6), so the tree is worth proving
  only once the merge decision is taken.
* **Compaction in place** would remove entries from a node's history.
  The model's base is that histories only grow (Basic.lean; a version
  holds its node's whole history; lemma M). Compaction must replace the
  node, as a time split does.
* **The last touch.** Any fix must keep the touch closed upward
  (`StepOK.touchUp`, checked by C-A) and safe cuts (C-CUT). Whether
  "mark only the rewrite paths" (023-08, section 4) keeps `CutOK` could
  not be determined by reading.
* **Fix (a)** changes step 5 and INV-1, on which every proof rests
  (023-07, section 5.10). 023-10 found that the window does not grow, and
  024's log drops the fix. It should stay dropped, or come before any
  new proof. `maintain()`'s forced take is a pace: `T3_take` holds.

### 5.3 The order

1. **A1 to A4**, now. Days in all.
2. **The algorithm decisions**: merges and their format (024-02, Q1), the
   form of compaction, the fix of the last touch, P8 or not.
3. **B0, then B1 and B2**, beside the Java changes of step 2, each
   change written in the Lean tree first. Model the tree with merges, not
   2026.4's tree, if merges are decided.
4. **C1**, then **C3**, when the tree has stopped moving.
5. **D1**, after the reclaim changes; then **C2** and **D2**.
6. **E**, as far as section 6 says.

Steps 1 to 3 fit a release. Steps 4 to 6 are the proofs; they pay only
on algorithms that stay (024-04, section 3).


## 6. The cost properties

**What Lean states today.** Only the T3 family (BoundTheorems.lean, 12
theorems): the cost of the startup section, for any cost of a record.
Not T4 (the size of D and of the records at the section's ends; 007),
nothing on a transaction's work, the stream's length, memory, or a
deleted KV. T-PIN is the nearest to a memory statement: everything but
the pinned objects can leave memory. 017-04 holds the open bounds (Q1,
Q3, Q5, Q8), measured, not derived; 023-02, section 7.1, chose tests,
not proofs, for the deletes' bounds.

**What stating aims 2 and 3 of 024-04 would need.**

* **Sizes, keys and a fill rule.** `Stream.cost` takes any size of a
  record; a bound in KVs needs the sizes of versions and values, and
  keys, so B1. Without merges the true statement is the weaker one, in
  the keys ever put (023-07, section 3.2, R10); 024-04's CL2 is the
  counterexample to the strong one.
* **Operations (aim 2).** The versions a transaction writes, bounded by
  its operations times the height: C3's `dirtyNodeBound` is this
  statement, and it was wrong three times in Java (024-01, LM2). The
  take's share needs T4. A reclaim step's work needs D1; CL7 is today's
  counterexample, so the statement says what the fix must meet.
* **Storage (aim 3).** After a cut at c with first available time f:
  the kept stream is `cutStream c S`, and what a lookup may reach is
  `ReadsAt`, both defined. Missing: the scheme (D1), its pacing, and a
  bound of the records between c and the end by the live data plus the
  writes within the retain duration (017-04, Q8).
* **A deleted KV costs nothing, eventually.** Statable on B1 and D1: once
  f has passed the delete and the cut is made, no version that a lookup
  from f on may read holds an entry of the key, and no record at or after
  c holds its value. False today for dead klongs in live nodes (023-08,
  Q5), which is the case for compaction.

So: T4 and C3 are the two cost theorems within reach; the rest wait for
B1, D1 and the merge decision. 024-05's tests are the faster way to hold
the aim; Lean adds the cases that tests missed.


## 7. Questions for Frans

1. **Which sense of "the model matches" does 2026.5 aim at?** (a) The
   tie repaired: A1 to A4. (b) Also the tree as a Lean definition that
   the checker runs against Java: B0 to B2. (c) Also its proofs: C1 to
   C3, D2. **Recommended: (b) in 2026.5, (c) started only when the
   algorithms of 5.3, step 2, are in the code.** (a) alone leaves the
   delete path outside the model, which is what the aim names.
2. **One rerun path or two?** 024's readme plans merges "switched on by
   the record's format", so that 2026.4's databases open. Two paths are
   two trees to model and prove. 2026.5 need not open 2026.4's databases
   (024-04, section 5). **Recommended: one path, a new record format
   that refuses 2026.4's.**
3. **Compaction never in place?** **Recommended: yes, as a design rule:**
   dead klongs go by a new node, as at a time split (5.2).
4. **Keys in the trace (trace format 3)?** It adds each klong's key and
   each transaction's operations to docs/trace-format.md. **Recommended:
   yes;** B0 and B2 need it, and the checker keeps reading format 2.
5. **Which cost statements go to Lean?** **Recommended: T4 (007) and
   `dirtyNodeBound` (C3) only; the rest of aims 2 and 3 as 024-05's
   tests** until B1 and D1 exist.
6. **The gates.** A1 adds minutes to `level2.sh` and a night step, and
   B2's check would join `level2.sh` to `level4.sh`. **Recommended: yes;**
   `before-commit.sh` stays as it is.
7. **A6 for A6'** (024-01, LM1)? **Recommended: check it in A4; change
   the model only after the merge decision** (P5 was checked with A6').
8. **025-01**, the model-first rewrite (not started), would replace the
   tree that B1 and C1 describe. C2's statement, the map, and section
   6's statements carry over to it; C1's proof does not. **Recommended:
   (a) and (b) either way; weigh (c) against 025-01 when it is due.**


## 8. State

2026-11-11. Written by reading `lean/` and `java/` at `main` (`9bda4019`;
its `java/` and `lean/` are release 2026.4's but for `BuildInfo.java`),
023-04 to 023-09, 001-07, 011-11, 007 and 024-01 to 024-04. Nothing built
or run: no `lake`, no level script. Not determined by reading: how often
the standing traces reach the delete path (4.4, point 3); whether a
narrower last touch keeps `CutOK` (5.2); whether ranges that grow leave
T-SCHEME's argument whole (4.4, point 2); the sizes of 5.1, which are
guesses from the model's history. Not read in full: `SIS/Proof/` (its
statements through lean/README.md), `KeyNode.java`, `Reclaim.java`.
Open: Frans's answers to section 7.

2026-11-13. Status set after the release (coord-1113).
