# 023-07. The proposal for 2026.4

Created 2026-11-10 by Frans Lundberg. Status: open.

The proposal for the resource cleanup of release 2026.4, written down
before any production code so that independent reviewers can check it
against the code: a simple core and a full set side by side, every
mechanism's rule stated exactly, the plan to production, and the
decisions left (Frans, 14:26 to 14:36: "Is there any simpler solution?
Principle KISS? [...] write this down in 023-07").


## 1. Summary for Frans

**Proposed: the KISS core (section 3) as what 2026.4 must hold.** Five
mechanisms, each prototyped and gated on its own branch, never together:

* **The delete cleans up at once.** An emptied node is unlinked upward
  at the delete (UP); every inner node starts with the empty key, so an
  emptied leftmost child costs one klong in its parent (LE-b); a node the
  transaction made and emptied is taken back as if never made; a root
  left with one child gives way to it (RC). P4, with P5's fix of the
  take-back.
* **Reclaim keeps up after a mass delete.** Each reclaim step scans at
  its own time, up to an end key E (P8).
* **Memory follows the cut.** After each cut, the objects stored before
  it leave memory, whatever the budget (P6's dead hand).
* **Scans end at their range's end**, also over deleted keys (021-28, SE).
* **Record format 6**; 2026.3's databases are refused.

Two fixes the prototypes showed are needed: `dirtyNodeBound` counted by
node (P4's count refuses transactions of more than about 150,000 deletes
that `main` takes), and a refusal message that names 2026.3.

**What the core meets.** The scan bound at every available time (T3);
T1 at 1M with the fixed drive in three orders (P8); the stream back to the
live data one retain duration after a mass delete; memory released after
each cut; no change of the Lean model; about 1,200 lines of Java
(the prototypes' main code, without tests).

**What it leaves, all bounded:** sparse nodes after scattered deletes
("sparse": 4,036 nodes against the twin's 270 at N = 100,000), chains of
single children below a root ("inter": 14 against 6), dead klongs in live
nodes until the node's next time split, the dirty top-node window (in the
twin too, also on `main`; P8 removed its trigger in T1), and the memory of
replaced nodes before the cut.

**The full set (section 4) adds**, each separable: merges (P5: strict but
"sparse" at 1.44 times), the top-node write-ahead (a) (P7: closes the
window) and (b') (P7: an efficiency), the replaced queue (P6, off by
default under Frans's Z15 conditions), and `maintain()` (P3, without the
rebuild). Its costs: about 1,200 lines more, a change of the Lean
model's take and INV-1 for (a) and of the physical theorems' test for
(b'), and about 300 more lines of C for merges alone.

**Two answers reopened, presented, not decided** (section 9.1):

* **Z12, merges** ("as recommended", 13:42). P5 met the three conditions,
  so by that answer merges go in. Out of format 6, they need a later
  format that refuses 2026.4's databases, or two rerun paths.
* **Z13, the window** ("solve this now"). (a) can come in any later
  release without refusing databases.
* Also **Y10**, `maintain()` ("yes"): the core leaves it out; it can come
  later with no format change.

**Risks of either tier:** the mechanisms never ran together; no
performance run (T10) on any branch; startup at 50 MB with the rerun's
path reads not measured; C9 over by a few objects at small N (a phase of
the measure); `IndexJobsHarness` flakes on a loaded F53.

**Decisions for Frans** (section 9): the tier (Z12, Z13, Y10), and
twelve smaller ones, each with a recommendation.


## 2. Terms, sources and branches

Terms as in 023-01 and 023-02: tt, the transaction's time; B, the node
size in klongs; live, at the latest time; D, the dirty index nodes; Rule
A, the still-dirty test (`javaTest`, sis-model.md 6.1, step 7); pCut, pStart,
tStart, tEnd, pEnd, pSafe as in reclaim's class comment (023-01, section
9). Invariants: 023-06's I1 to I8 (section 13.1); sis-model.md's INV-1 to
INV-4 (section 8), lemma M (`LM_newer`), and the model's assumptions A1
to A5, TREE, A6' and A-COPY (sections 3.4 and 15.2). Tests and measures:
023-03 (T1 to T12, M1 to M14, C1 to C12, a_n).

All branches start from `main`'s Java at `1901394c` (no Java commit since),
in `/Users/f/fl/bench/2026-11-10/<p>/clone`, except SE.

| Name | Branch                | Head       | On                     | Report        |
|---|---|---|---|---|
| P4   | `023-p4-empty-key`  | `0e66d1c9` | P1's `0f16daae`             | p4-empty-key |
| P5   | `023-p5-merge`      | `71e386de` | P4's `5466e153`             | p5-merge     |
| P6   | `023-p6-memory`     | `c46d607d` | P4's `0e66d1c9`             | p6-memory    |
| P7   | `023-p7-topnodes`   | `cd81d789` | P4's `0e66d1c9`             | p7-topnodes  |
| P7a  | `023-p7-fix-a`      | `f7d521e3` | (a) alone                   | p7-topnodes  |
| P7/5 | `023-p7-on-p5`      | `d45894e6` | P5's `71e386de`, in p5clone | p7, 6.2      |
| P8   | `023-p8-steptime`   | `f56dca40` | P4's `0e66d1c9`             | p8-steptime  |
| P3   | `023-p3-compact`    | `7b2cf1ec` | `main`                      | p3-compact   |
| SE   | `scan-deleted-keys` | `eebeb39d` | `5f176575` (2026-11-09)     | 021-28       |

SE's clone is `/Users/f/fl/bench/2026-11-09/clone-q34`. The reports are in
023-05. Code places below are on the named head, in `java/src/bergdb/`.


## 3. The KISS core for 2026.4

### 3.1 Is the set coherent?

* **One base.** P6, P7 and P8 were built on P4's `0e66d1c9`; P5 on P4's
  `5466e153` with `0e66d1c9` picked. SE is on an older base but touches
  only the read path (`GetMany`, 6 lines of `Dag`, two Pub scans), and
  P4 checked it against LE-b (P4, 1.5: no pruning lost).
* **P4 needs two pieces of P5.** The take-back's retarget (K1's fault
  6) and `dirtyNodeBound` without P1's off-path count (K4). Both are in
  P5's commits mixed with merge code (`4c6bea65`, `429b56d3`, `71e386de`)
  and must be separated.
* **P8 and P6 use the same guarantee.** The dead hand frees what is
  stored before pCut by reclaim's guarantee (P6, 1.1); P8 keeps that
  guarantee with the scan at the step's time (P8, 2.3 and 2.4). P6's
  argument for values ("a value live from f on was put after tStart or
  rewritten by its step") holds under P8 by P8's 2.3. Not run together.
* **Each piece is a rerun rule or not.** UP, LE-b, the take-back and RC
  are rules of the delete that the start reruns: they define format 6.
  P8 changes what a step rewrites, not the rerun (the scan is not stored;
  P8, 2.6); the row gains a line `endKey=`. The dead hand and SE change
  no byte. So the core's format 6 is P4's rules with P5's retarget.
* **What the core does not need.** No Lean model change (only the Java
  check A2A3Check2 counts a taken-back node as not made, Z18); no change
  of the take, of Rule A, of the got-dirty entry.

### 3.2 What it meets and what it leaves

Against 023-02's requirements:

| Req.           | Core                                               | Evidence          |
|---|---|---|
| R1, R16      | lookups and readers unchanged                      | every gate, T6    |
| R2, R13      | the stream back to the live data after R           | P8, 5.1 (C1)      |
| R3, R5       | deleted keys' nodes unreachable at the delete      | P4, 3.2 (M4 6)    |
| R4, R14      | memory after each cut (dead hand)                  | P6, 4.1 (292/263) |
| R6           | the iteration in progress ends with the deletes    | P8, 5.2           |
| R7           | replaced versions go at the cut; dead klongs later | X4 (a), K up to B |
| R9, F3       | the scan bound at every available time             | P4, 3.3 (T3)      |
| R10, R12 (a) | height and nodes in the keys ever put              | P4, 3.2           |
| R12 (b)      | no: underfill stays ("sparse")                     | P5, 4.1           |
| R11          | O(H) a delete, with K4's bound                     | P5, section 6     |
| R15          | the rerun reads each delete's path; not measured   | 023-06, 14        |
| R17, R18     | restarts and crashes                               | gates (3.3)       |
| R22, R23     | format 6; 2026.3 refused                           | K8                |
| R24          | no model change; checker as Z18                    | 023-06, 15        |
| R25          | C port after the release, about 500 lines          | section 6.4       |
| R26          | not measured (T10)                                 | open              |
| R27          | the expected values of 3.4                         | Z19               |

Against 023-03's tests:

* **T1, bounded allowance.** P4: 17 of 18 rows at 1,000 and 100,000
  (1,000 descending misses C9, 118 against 85 + 26). P8: at 1M in
  ascending, descending and random order, C1 to C3 and C5 to C10 pass
  with the fixed drive of 4,000; at 1,000 and 100,000 C9 is over by 1 and
  6 (+15 against a_n 14, +22 against 16), a longer startup section at the
  drive's end whose rerun leaves replaced leaves resident (P8, 5.1, Q4).
  Not run on the combination.
* **T2's "sparse"** (P5's `keep=30`, not one of T1's 18 rows): P4 4,036
  key nodes against the twin's 270. Within a_n = 10 + L h_fill when L is
  read as the N / 30 live keys; not within the strict a_n, nor within
  `judge.py`'s fixed 10 + 4 h_fill. Which reading gates is Frans's (9.2,
  D9).
* **T3**: right after the deletes, R forever, a scan of each shape at
  100,000 follows 1 key node, as the twin's (P4, 3.3); 023-03's sum over
  1,000 rounds and R = 1 s were not run as such.
* **T4**: reach 117 at 1M ordered, steady; with P8 11 to 12 % fewer steps
  (P8, 5.3). Memory: with the dead hand 712 to 858 resident objects,
  steady (P6, 4.3); without it, growing to 24,113.
* **C11** (no value of a deleted key once dead): not in any prototype.

What the core leaves, each bounded:

| Left                          | Size measured                     | Taken by (full set) |
|---|---|---|
| sparse nodes ("sparse")       | 4,036 against 270 at 100,000      | merges (P5)         |
| single-child chains ("inter") | 14 against 6 at 100,000           | merges (P5)         |
| dead klongs (M5), live nodes  | at most B a node; next time split | merges, in part     |
| the dirty top-node window     | see below                         | (a) (P7)            |
| replaced nodes' memory        | until CLOCK or the cut            | replaced queue (P6) |

The window: on P4 at 1M with a drive of 12,000, D 178 against the twin's
94 and 184 objects after a restart against 83 (P7, 6.1). With P8 at 1M and
a drive of 4,000, D 90 against 83 and 91 objects against 83: C6 and C9 pass,
because the long lag after the deletes is gone; D still holds 58 top nodes
against the twin's 51 (P8, 5.1). The twin has the run too, on P4's code
(50 to 61 dirty top nodes, 10 or 11 inversions; P7, 1.1) and on `main`
(P1, 5). Its length is what a disturbance left; a later disturbance can
lengthen it (P6, section 5; 023-06, 11.1). Not measured on P8: 023-06's
ratchet test (18.6, item 3).

### 3.3 Gates run, by mechanism

| Branch, head  | Gates passed                                              |
|---|---|
| P4 `0e66d1c9` | before-commit; level1 full; level2 full (70 traces); level3 quick; level4 quick |
| P5 (P4 part)  | UnlinkFuzz with the retarget check; level1 to level4 full at P5's heads         |
| P6 `c46d607d` | before-commit; level4 full (45 traces, C-P, C-H); level1 on `411ae3d1`          |
| P8 `f56dca40` | before-commit; level1; level3 full (C-CUT 0 of 303); level4 quick               |
| SE `eebeb39d` | before-commit (280 s, 269 s); level1; a review, no high or medium               |

Not run on any: StreamDigest (its digests change with format 6),
`night.sh large`, T10. Not run on the combination: anything.

### 3.4 Tests whose expected values change (core)

* StreamDigest's 12 digests: format 6 (every branch).
* `Reclaim`'s `testUserTransactionLeavesTimesForReclaim`: a margin of
  100 bytes, not 150 (P8, 3.2; P8's Q3).
* `CorruptStreamTester.testFound019_32`: passes on P4, P6 and P8 alone;
  P5's merges moved one row. To be checked on the combination.


## 4. The full set

Each addition is separable from the others, but (b') gives most with
P5's left-out nodes (P7's Q2) and does not close the window without (a),
and the replaced queue's Z15 condition needs P8.

| Addition      | Adds                                   | Costs                               |
|---|---|---|
| F1 merges     | "inter" 6; "sparse" 1.44 x; R12 (b)   | ~545 lines; sibling reads; a format  |
| F2 (a)        | the window closed at every N; -27 %   | ~100 lines; model step 5, INV-1      |
| F3 (b')       | P5's left-out nodes 248 to 150; -15 % | 16 B a got-dirty entry; theorems     |
| F4 queue      | 152 objects at 100,000 (twin 89)      | reloads at earlier times; ~260 lines |
| F5 maintain() | "eventually" without user writes      | two API methods; a forced take       |

In more words:

* **F1, merges (P5).** Adds strict in all T1 rows (M4 6 in "inter") and
  a constant factor in "sparse" (390 against 270; 1.20 with a 3 B/4 cap,
  not committed, thrash not measured). Costs: one or two sibling reads a
  merge, about one merge in 5 deletes in key order, 2 % from the stream
  under eviction; up to 32 % more resident objects after the deletes
  under `noEvict()`; deletes' bytes 0.94 to 1.07 of P4's but "inter" 2.1
  times (explained, P5's section 6, and gone within 10,000 drive
  transactions, P7's 6.3); `dirtyNodeBound`'s merge count is an argument
  and a probe, not a proof; about 300 more lines of C. It is a rerun
  rule: in format 6, or in a later format that refuses 2026.4's
  databases (023-06, 11.1).
* **F2, (a) (P7).** Adds: the window closed at 1,000, 100,000 and 1M (D
  35 / 34, objects 25 / 33 at 1M, twin / emptied); 27 % fewer drive
  bytes in the emptied database at 1M, 8 % in the twin; top node versions
  written per top node made 7 against 40. Costs: the Lean model's step 5
  and INV-1 (a start drops a got-dirty id with a later version), the trace
  checker's C-S fails at a record that writes ahead until the checker
  follows (`e-m-mixed-1`); 3 unit tests' values; records up to 1.5 kB
  larger. Not a rerun rule, and a stream without write-ahead starts as
  before: it can come in any release without a refusal.
* **F3, (b') (P7).** Adds: P5's left-out nodes leave D sooner (248 to 150
  right after the deletes; 71 with r and e in memory only), "inter"'s
  delete bytes -15 %, T4's queue -5 % (P7, 6.2 and 6.3). Not needed for
  the rule: with (a) alone the 259 left-out nodes leave D within 10,000
  drive transactions and D then holds 1 to 16 unreachable key nodes, none
  still there at the next checkpoint (with (b') 1 to 13). Costs: every
  got-dirty entry 32 bytes instead of 16 (a change of the record syntax:
  later, a format that reads format 6's entries with e unknown, which
  P7's rule treats as `javaTest`, or refuses them), the physical theorems
  re-proved for a test that is not `javaTest`, no level script run with
  it on, 4 unit tests' values.
* **F4, the replaced queue (P6).** Adds: memory of replaced nodes before
  the cut and with R forever (T1 100,000: 152 objects against the dead
  hand's 292, twin 89; T4 151 to 185 against 712 to 858). Costs: lookups
  at earlier times reload what it evicted (not measured); under P4
  reclaim's scan at tStart loaded 190,272 versions at 100,000, which P8
  should remove (not measured on P6's branch). Z15: on by default only
  if both are shown small, else kept off by default.
* **F5, `maintain()` (P3).** `Db.maintain()` and `Database.maintain()`
  without P3's rebuild: one reclaim step or an iteration's start, a forced
  take of at most 1 MiB, the cut when due; returns whether more is due.
  No new record kind, no format change. Never needed by the user (Y10).


## 5. The mechanisms, exactly

Each entry: the rule (what, when, by whom); the invariants it keeps; the
code; gates; faults found; tests changed; Lean; C; bytes and memory; open
risks. K are the core's, F the full set's.

### 5.1 K1. UP, the upward unlink, with the take-back (X5 (a))

* **Rule.** In the deleting transaction, by the writer, for each delete
  (`Dag.deleteUpward`, P5 `Dag.java:1084`). If the leaf keeps a live
  klong after the delete, the delete is a delete bitmap of tt
  (`appendDeleteKlong`), as today. Else the
  writer finds `stop`, the first node above that keeps a live klong (a
  klong of the empty key in an inner node counts as deleted in this test:
  `allKeysIn` with `bitsOf(s, 0)`), changing nothing until it is known.
  Each node from the leaf up to below `stop`: if it was made by tt as a
  split's node (`canTakeBack`: `PutData.replacedBy` and a live klong of
  its parent to it), it is taken back; if it existed before tt, it is
  unlinked (`unlink`, `Dag.java:1405`: `toPreviousState(tt - 1)` if it has
  klongs of tt, then `keyNodeReplaced`). At `stop`: a segment leaf gets a
  delete bitmap of tt for the segment's compare value; an inner node gets
  one for the child's compare value c, or LE-b if c is the empty
  key (K2). An inner space root left with no live klong is replaced by an
  empty segment leaf through a new super root (and taken back if tt made
  it). A node made by tt that is not a split's node is not taken back:
  it stays linked, and the first segment leaf at or below it keeps the
  delete (X5 (c)). Then RC (K3).
* **The bitmap rule.** A bitmap of tt sets the bits of every klong of the
  compare value, and precedes any new klong of the same compare value in
  that transaction (Java deletes by index, the model by compare value).
* **The take-back** (`takeBack`, `Dag.java:1447`). The parent's live klong
  of tt to the node is pointed to the node it replaced (`repointKlong`),
  and **every** KEY klong of tt in the parent, behind its time klong of
  tt, that names the node, deleted ones too, is pointed there as well
  (`retarget`, P5 `Dag.java:1946`). The node is reported taken back
  (`keyNodeTakenBack`): it leaves D, the record and the node table
  (`Cache3.dropNode`, `Cache3.java:371`, called from `Db.java:1149`, and
  in the rerun at once, `DbStarter.java:402`). Its id is consumed in
  creation order.
* **Invariants.** I1 (no bit of the empty key), I2 (no reachable node
  without a live key below it), I3 and A2 (entries of tt only, in place
  only behind tt's time klong), A3 and I5 (no node of tt left unreachable;
  a taken-back node named by no klong, live or deleted, in no record),
  A5 (an unlinked node is reachable before tt only), I7 (marking as the
  model's), I8 (ids in creation order, taken-back ones included).
* **Gates.** P4's (3.3); P5's UnlinkFuzz checks that no pointer of a node
  reachable at any time names a taken-back node.
* **Faults found.** (1) P1: the bitmap after the new klong; the model
  deleted the new klong too (C-A). (3) P1, P2, P4: a taken-back node left
  in the node table (C-H with eviction; `e-mixed` seed 3). (6) P5: the
  take-back pointed only the live klong; a deleted klong of tt (the next
  child's own klong after `emptyKeyNext`) still named the node. P4's head
  lacks the fix.
* **Lean.** No model change. A2A3Check2 counts a taken-back node as not
  made (Z18). sis-model.md, 3.4: a sentence on transient nodes.
* **C.** `deleteUpward`, the climb, `unlink`, `takeBack`, `retarget`,
  `dropNode`: most of P1's 400 lines.
* **Bytes, memory.** "after" at 100,000, R forever: 4.82 MB against
  `main`'s 6.78; R = 1 s 6.16 against 10.9. Objects as `main` (+0.1 %).
* **Risks.** X5 (c) and an empty space root replaced by a leaf were never
  reached by a run (P1, 5); the rerun reads each delete's path (startup
  time not measured).

### 5.2 K2. LE-b, the empty key first

* **Rule, the split.** A space split of an inner node gives its second
  half `Klong.EMPTY_KEY` as its first klong while the parent gets the
  half's first compare value; a klong being inserted by the split with
  that compare value goes to the second half as the empty key too, so
  that it shadows the copied one (`KeyNode.firstAndSecond`, P5
  `KeyNode.java:1357`, called from `Dag.spaceSplit` and
  `spaceSplitInPlace`, P5 `Dag.java:2217`, `2347`).
* **Rule, the delete.** When UP stops at an inner node `s` whose klong to
  the emptied child is the empty key (`emptyKeyNext`, P5 `Dag.java:1478`):
  the next live child j (smallest live compare value c_j but 0) is
  deleted by a bitmap of tt (bits of every klong of c_j), then a new
  klong of the empty key with a copy of pointer j shadows the old one
  (`addKlongCopyPointer`). If the latest klong of the empty key is of tt,
  its pointer is set in place instead (`copyPointer`). A full `s` is
  replaced by its last version through `handleFullNode` with the empty key
  in c_j's place. The empty key never gets a delete bit. If `s`'s smallest
  live klong is not the empty key, the writer throws `Bug`.
* **Invariants.** I1: in every inner node the smallest live klong is the
  empty key at every time; A-COPY (the pointer is copied while the node
  is current); every reader takes 0 as a lower bound (P4, 1.5, a table of
  every reader).
* **Gates.** P4's; UnlinkFuzz checks I1 after every transaction.
* **Faults found.** (4) P4: the split's inserted klong (a mutation test
  found that a scan would visit both children).
* **Lean, C.** No model change (the model has no keys). C: the split rule
  in `firstAndSecond`, a few lines; `emptyKeyNext`.
* **Bytes.** 2 to 6 % below P1's relabel; no node off the path changes.
* **Risks.** Shadowed klongs of 0 are dead klongs until the next time
  split. A future reader that takes a node's lower bound from its own
  first klong would get 0 (P4, 5).

### 5.3 K3. RC, root collapse

* **Rule.** After a delete's change, by the writer (`collapseRoot`, P5
  `Dag.java:1223`): while the root of the segment tree is an inner node
  with one live klong, its child takes its place: the space root through a
  new super root, a segment root through a klong of the same compare
  value in the segment leaf above that shadows the old one. The old root
  is unlinked. A root that a split of tt made (`PutData.replacedBy`) is
  taken back instead (`takeBackRoot`, `Dag.java:1256`): the klong of tt
  that links it, in the top node of tt (`TopDs.newSuperRoot` updates it
  in place) or in the segment leaf above (`repointKlong`), is pointed to
  the child. The child is followed without marking (`descendToRootQuietly`,
  `followQuietly`).
* **Invariants.** I2 (no root at the latest time is an inner node with
  one live klong), I1 (the child's first klong is the empty key, or it is
  a leaf), I5, I7.
* **Faults found.** (2) P1: the descent after a collapse marked an
  unchanged node (C-S, Java only). (5) P4: RC stopped at a root made by
  tt ("hashed" kept 3 levels of single children).
* **Lean, C.** No model change. C: `collapseRoot`, `takeBackRoot`.
* **Risks.** Collapses roots only: chains of single children below a
  root stay ("inter").

### 5.4 K4. `dirtyNodeBound` by node of the paths

* **Rule.** Before a transaction changes anything, `Dag.dirtyNodeBound`
  (P5 `Dag.java:477`) bounds the nodes it can make dirty, so that a
  record stays under the record limit (005-31). P1's count, kept by P4,
  adds 4 nodes a level and 2 for each delete for off-path changes that
  LE-b no longer makes: at node size 30 a bound of 25,000 to 29,000 for
  1,000 deletes against `main`'s 158 to 854, so more than about 150,000
  deletes in one transaction are refused (P5, 6). The core takes P5's
  count without merges: 2 klongs a delete on its path, no off-path nodes
  (UP, LE-b and RC change none off the path), the splits from those
  klongs. `Db.checkDirtyNodes`'s cheap test with it.
* **Fault found.** (8), by P5's probe (`BoundProbe`, `LimitProbe`).
* **Required.** A test of the bound against counted nodes at node sizes 8,
  14 and 30 for transactions of 1,000 and 100,000 deletes (023-06, 15).
* **Risk.** An undercount lets a record outgrow the limit.

### 5.5 K5. Each reclaim step scans at its own time, up to E (P8)

* **Rule.** When an external transaction t starts an iteration
  (`Reclaim.transactionCompleted`, under the write lock), reclaim reads
  E, the last key live at t's time (`lastKeyAt`, `Reclaim.java:534`: a
  backward `GetMany` of one KV at `t.tt` with the maintenance follower),
  and stores it in the iteration's row (`endKey=`; `NO_KEY` if none). A
  step, at a later external transaction under the write lock, scans with
  `lookupTime = Long.MAX_VALUE` (`Reclaim.java:589`), the latest state,
  and its stop condition stops at the first live key after E
  (`IterationInfo.pastEnd`, `Reclaim.java:1324`), which ends the
  iteration as the end of the data does. Reads, rewrites (each
  live value stored before pCut), the touch of (lastKey, L] at the step's
  transaction time (to the end of the key space in the last step), tEnd,
  pEnd, pSafe and the cut are as today.
* **Invariants.** I6 (the cut's guarantee): values by P8's 2.3 (a value
  stored before pCut and live at t >= tEnd was live from tStart to t, so
  at most E, so the step whose range holds its key rewrites it); index
  nodes by 2.4 (today's argument, for any boundaries). INV-RESTART: the
  scan and its time are not stored or rerun; E is computed once from the
  state at tStart and stored.
* **Code.** `edb8e14d`, all in `Reclaim`; tests `1d6494f0`.
* **Gates.** P8's (3.3); its own 14 traces with heavy deletes, bulk puts
  after E, long keys and eviction: C-CUT 0 of 163.
* **Faults found.** (10) Without E an iteration need never end: ordered
  puts after the scan of more than a step's 16 KB a transaction keep it
  going (`testEndKeyBoundsTheScan` fails without E).
* **Tests changed.** `testUserTransactionLeavesTimesForReclaim` (3.4).
* **Lean.** None: the model has no scan; C-CUT checks each cut. T-SCHEME
  stays checked, not proved.
* **C.** The scan's time and E, where the C port has reclaim.
* **Bytes.** Ascending mass delete at 1M: deletes 85.0 MB against 68.4
  (+24 %, steps work just ahead of the deletes), the drive 5.5 MB against
  13.9 (-61 %); within the internal fraction.
* **Risks.** Random puts before E faster than the scan lengthen an
  iteration (P8, 7; not seen in T4 hashed). The scan still reads each live
  KV's value (a keys-only scan is P8's production item). With SE in, the
  step could set `GetMany.endKey` to E, inclusive, instead of the stop
  condition's test: the same keys, and no path to the next live key (not
  built).

### 5.6 K6. The dead hand (P6, half)

* **Rule.** By the writer's thread at the end of every transaction
  (`Eviction.afterTransaction`, P6 `Eviction.java:332`), in the budget
  schedule (not `noEvict()`) and the test schedule `random`: when the
  decided cut position (`Reclaim.getFirstAvailablePos`) has moved since
  the last round began, a round over the node table starts; each step
  (`deadStep`, `:549`) examines at most 4,096 handles (`DEAD_BATCH`) and 2
  ms (`BATCH_NANOS`). Each handle's object stored before the cut is
  evicted if detachable (`Eviction.detachable`: not the super root, the
  newest written top node, D's or the record's), whatever its CLOCK bit
  and the budget (`Cache3.kill`); in each key node kept, a pointer holding
  a value stored before the cut becomes a stream pointer
  (`unswizzleValue`). Records do not change.
* **Invariants.** I6: an object stored before pCut is reached by no lookup
  at an available time (P6, 1.1, top nodes included); a reader holding one
  finishes with it, one that follows again reads at pCut or later or
  expires (D1 = A).
* **Code.** `83e1cb86`, tests `411ae3d1` (`Eviction.testDeadHand`,
  `ReclaimReaderTester.testHeldReadersAndTheDeadHand`).
* **Gates.** before-commit, level1, level4 quick on `411ae3d1`; level4
  full on the head with the queue.
* **Faults.** None; the held-reader test's first version needed two cuts.
* **Lean.** None: an eviction schedule (T-CACHE, T-READ, `tc_handles`,
  `t9_handles`, `t12_handles`).
* **C.** In C's own memory scheme, after the release.
* **Memory.** T1 "after" at 100,000, 1 GB budget: 292 objects against
  P4's 11,612 (twin 263); T4 steady at 712 to 858.
* **Risks.** Timing on a quiet machine with 10M nodes not done (a step's
  wall time reached 104 ms on a loaded F53, CPU 6.7 ms). Readers before
  the cut may make dead objects resident until the next round. Under
  `noEvict()` nothing is freed but at a restart (Z15, Javadoc).

### 5.7 K7. SE, the end key of forward scans (021-28)

* **Rule.** `GetMany.endKey` and `endInclusive`, checked in
  `GetMany.Chain.next()` on each klong before its pointer is followed: a
  klong past the end, live or deleted, ends the scan as the end of the
  database does. Forward only; `Dag.getMany` and the Chain refuse a
  backward scan with an end key (`IllegalArgumentException`). Set by the
  Pub API's index scan (`UseIndexBuilderImp.Scan.readPage`) and listing
  (`UsePrimaryBuilderImp.Scan.readPage`, after(prefix), exclusive).
* **Invariants.** R1: results equal the stop condition's
  (`testEndKeyAsEndpoint`, 1,500 random scans at every time). No byte.
* **Faults found.** (11) The review: the stop set a local copy of the
  link count, not the field (`eebeb39d`).
* **Lean, C.** None; C when the Pub layer is ported.

### 5.8 K8. Format 6 and the refusal

* **Rule.** `StoredTrans.RECORD_FORMAT = 6` (P1's); a start refuses a
  record of another format with a `VersioningStreamException`.
* **Needed.** `StoredTrans.formatRefused` names format 2 only ("format 2
  was written until 2026-10-15"); Y8 asks for a message that names
  2026.3: format 5 was written by 2026.3 and earlier.
* **Tests.** StreamDigest's digests; a test of the message.

### 5.9 F1. Merges at the delete (P5)

* **Rule.** In the deleting transaction, by the writer, after each change
  a delete makes (`mergeAfterDelete`, P5 `Dag.java:1626`): the changed
  node X, if not a segment root and with fewer than m = B / 4 live
  klongs (at least 2), merges with a sibling under its parent P: the
  previous live child if both fit in B / 2, else the next, else the
  previous (`merge`, `:1694`; `sibling`, `:1843`, read with
  `followQuietly`, unmarked). The live klongs of both last versions at tt,
  in order, make one new node if at most B / 2, else two halves; each
  starts with tt's time klong; in inner nodes R's empty key becomes cR's
  klong and a second node starts with the empty key. P (`mergeParent`,
  `:1864`): a bitmap of tt deletes cR (every klong of it) before any new
  klong; cL's klong points to the first new node (in place if of tt); a
  second node gets a klong; a full P through `handleFullNode`. L and R
  get no entry of tt: unlinked if they existed, else retargeted and taken
  back. A merge into one node goes on with P; then RC.
* **Invariants.** I2 with merges (every reachable node but a root has at
  least B / 4 live klongs after any transaction), I1, I3, I5, I7, I8,
  A-COPY, TREE, A6' (P5, 1.2).
* **Gates.** level1 to level4 full, A2A3Check2 on 7 configurations,
  UnlinkFuzz strict (P5, 3).
* **Faults found.** (7) The climb gave up after a space split during the
  delete (`PutData.newRootsMade`). (8) `dirtyNodeBound` (K4), with
  `mergeBound`'s count of merges for the transaction.
* **Tests changed.** `testFound019_32` (one row moved; skipped).
* **Lean.** No model change. **C.** About 300 lines (`merge`,
  `mergeParent`, `sibling`).
* **Risks.** The merge count of `mergeBound` (`:579`) is an argument and a
  probe; thrash at a boundary not measured; merges of a leaf with klongs
  to segment roots only reached by the fuzz.

### 5.10 F2. (a), the take writes the chain of dirty top nodes (P7)

* **Rule.** In `Db.store`, under the write lock, after `TransSeq.take` and
  before `resolvePointersOfTakenNodes` (`writeAheadTops`, P7
  `Db.java:2896`): for each top node in the record, in order, and each of
  its skip pointers 1 to h by index, a dirty top node that is not in the
  record is added if the record stays within the record limit, counted as
  `store()` counts it; added nodes are examined in turn. Roots and key
  nodes are never added. An added node leaves its got-dirty list
  (`TransSeq.takeAhead`, `TopNode.dirtyIn`). Rule A then runs unchanged;
  a node still dirty joins the running transaction's list.
* **The start's rule** (`DbStarter.rerunTransaction`): a got-dirty id of
  record j whose newest version in the section lies after j is dropped.
* **Invariants.** INV-1 becomes: D holds the nodes of gd(j), s(i) < j <=
  i, with no version in a record after j. L-OUT, L-SEC unchanged (023-06,
  18.7). `javaTest` kept.
* **Gates** (on `ca949e5e` and `e2f13dc9`, 14:29): level1 full, level2
  quick, level4 quick steps 1 to 4, conformance evict 14 of 15 (the C-S
  difference of the take, `e-m-mixed-1`), StreamDigest's modes agree,
  CrashTest 25 rounds, RestartInvariance identical on 5 configurations;
  level2 full and level3 full were running.
* **Tests changed.** `CorruptStreamTester.testFound021_11`, `_12`;
  `Eviction.testLoweredBudgetAfterPinsFell`.
* **Lean.** The model's step 5 (the closure over skip pointers) and INV-1;
  T1 and T2 rechecked; the checker's step. **C.** The take's addition and
  the start's rule.
* **Risks.** 88 to 95 % of pulled nodes stay dirty (a root below them is
  dirty); the pull still keeps the chain in one list (P7, 6.5).

### 5.11 F3. (b'), Rule A by the time the child last went dirty (P7)

* **Rule.** r(x), the time x stopped being current (set in `Db.endOfTrans`
  for a node that stays in D: a split, the unlink, a merge's left-out node,
  RC, a new super root); e(y), the time y last went from clean to dirty
  (`makeDirtyIfNeeded`, untouched by Rule A's refile). After a taken node
  x is written, x is dirty again iff it points to a dirty y and (x has no
  r(x), or e(y) < r(x)). A node without a known e counts as `javaTest`.
  Each got-dirty entry is (id, position, r, e), 32 bytes (`07b9e954`,
  switch `bergdb.p7.ruleb=true`); stored and rerun values must agree.
* **Soundness.** 023-06, 18.7: with e(y) >= r(x), y was clean at e(y) - 1,
  its version then good for every t < r(x); lemma M carries that to newer
  versions. Rule (b), by d(y), is unsound: `testRuleBCounterexample`
  (`92cda0be`) fails with (b) and passes with today's rule, (a) and (b').
* **Gates.** RestartInvariance on 5 configurations; no level script.
* **Lean.** The physical theorems assume `javaTest` (`CutHist.lean`,
  `CutLazyStart.lean`, `EvLogic.lean`, `CutRestart.lean`): re-proved for
  the weaker closure; the checker's test with r and e.

### 5.12 F4. The replaced queue (P6)

* **Rule.** At a transaction's end the objects of the nodes it replaced
  or unlinked (`keyNodeReplaced`, `topNodeReplaced`) are queued
  (`Eviction.nodesReplaced`, `:496`); after each transaction a step
  (`replacedStep`, `:508`) evicts the queued objects that are clean,
  written and still their handles' objects, at most 4,096 a transaction;
  a dirty one goes to the back; the newest written top node waits.
* **Code.** `6451d774`; `c46d607d` lowers `DbTesterJavadoc`'s budget to
  10 kB (an expected value). **Lean.** None.

### 5.13 F5. `maintain()` (P3, without the rebuild)

* **Rule.** `Db.maintain()` (P3 `Db.java:643`), under the write lock:
  `Reclaim.maintain` (an iteration starts when R / 4 has passed, else one
  step, with its touch), then, if D is not empty or a done iteration waits
  for the startup pos, an internal transaction with no keys whose take is
  forced (`Trans.maintainTake`, at most 1 MiB), then the cut. Returns
  whether more is due. `Database.maintain()` calls it.
* **To separate.** P3's step calls its rebuild (RB); the core's step is
  P8's. An iteration that `maintain()` starts must find and store E as
  P8's start does (`lastKeyAt`), or its scan is unbounded. A cut still
  waits for a meta block after pCut (P3, 1.4).

### 5.14 The faults found, as rules to keep

| #  | Found by      | Rule a production version keeps                          |
|---|---|---|
| 1  | P1, C-A      | the bitmap precedes a new klong of the same compare value  |
| 2  | P1, C-S      | a follow that changes nothing below does not mark          |
| 3  | P1, P2, C-H  | a taken-back node leaves the node table, also in the rerun |
| 4  | P4, mutation | the split's inserted klong of that value is the empty key  |
| 5  | P4, T3       | RC takes back a root that a split of tt made               |
| 6  | P5, review   | the take-back retargets every klong of tt naming the node  |
| 7  | P5, fuzz     | merges follow the depth through new roots of the delete    |
| 8  | P5, probe    | `dirtyNodeBound` counts nodes of the paths, no off-path    |
| 9  | P7, test     | Rule A for a replaced node: by e(y), never by d(y)         |
| 10 | P8, test     | an iteration's scan stops at E                             |
| 11 | SE review    | the end key's stop clears the Chain's field                |


## 6. How the chosen tier becomes production code

### 6.1 The integration branch

`023-2026-4`, from `main`, in a clone; each step a commit that passes
before-commit; then the gates of 6.3 on the head. The core, in order:

1. P4's branch, P1's four commits and P4's three, squashed by mechanism;
   P1's relabel code is gone at P4's head (check none is left).
2. From P5: `retarget` and its call in `takeBack`; UnlinkFuzz's pointer
   check. Hand-separated from `4c6bea65`.
3. `dirtyNodeBound` (K4): P5's `429b56d3` and `71e386de` without
   `mergeBound`. Conflicts in `Dag` only.
4. P8's `edb8e14d` and `1d6494f0`: `Reclaim` only; no conflict expected.
5. SE's `2bfeb3e3`, `240f2b3e`, `eebeb39d`: `GetMany`, `Dag` (6 lines in
   `getMany`), the Pub scans, tests. Its base `5f176575` is an ancestor
   of `1901394c` with no Java commit between in these files.
6. P6's `83e1cb86` and `411ae3d1`, without the queue; conflicts in
   `Db.endOfTrans` (P4's `keyNodeTakenBack` beside P6's hooks). Remove the
   CPU-time probe (`ThreadMXBean` in `deadStep`) and the switches.
7. The refusal message (K8); the format entry (018-01, section 2).
8. P7's `testRuleBCounterexample` (`92cda0be`) without its (b) mode: a
   guard of today's Rule A after a restart.

`java/stress/CleanupRule.java` is changed by every branch: merged by hand,
once, as `CleanupTester` and `cleanup.sh` (6.2). The full set adds, after
step 3: P5's merges (`163fed3f`, `5dfee887`, `mergeBound`); after step 6:
P7's (a) (`7fd16455`, `f7d521e3`), then (b') (`ca949e5e`, `07b9e954`),
the queue (`6451d774`, `c46d607d`), and P3's `maintain()` without RB.
Expected conflicts: `Db.store` and `DbStarter` ((a), (b')), `Dag`
(merges against the core's bound), `Db.endOfTrans` (r(x), the queue).

### 6.2 Tests to write

* **One per fault** of 5.14 that has none yet: DagTester for LE-b in
  place, in a full parent and across a split; the take-back with a
  deleted klong of tt naming the node; RC of a space root and of a
  segment root, made by tt or not; the empty space root replaced by a
  leaf; X5 (c). KeyNodeTester for `firstAndSecond` of an inner node. A
  unit test that every bitmap's new bits cover every earlier klong of
  their compare value and precede its new klong. With merges: a merge of a
  node of tt as left and as right node; a full parent (023-06, 15).
* **`dirtyNodeBound`** against counted nodes (K4).
* **C11**: 023-03's record walker H2, so that no value of a deleted key
  is kept once dead (R2); no prototype has it.
* **023-03's tests as code**: `CleanupTester` in before-commit (T1 at
  1,000 and the checks C1 to C11 that are fast), `cleanup.sh` in
  `night.sh` (T1 to T4 at 100,000 and 1M); allowances revised: C9 at a
  fixed phase of the startup pos or with a tolerance of the section's
  nodes (P8's Q4); "sparse" by D9; the window named in C6 and C9 if (a)
  is not in.
* **The ratchet test** (023-06, 18.6, item 3), core and full set alike:
  T4's queue, 1M transactions, a mass delete every 200,000, a restart
  after each; D's top nodes at every checkpoint.
* **The counterexample** (`testRuleBCounterexample`), in both tiers: it
  guards Rule A against a future change.
* **UnlinkFuzz** (strict with merges) as a `level1.sh` step; the
  draining A2A3Check2 and trace configurations in `level2.sh` and
  `conformance.sh`.

### 6.3 Gates

* before-commit; `level1.sh` to `level4.sh` in full; `night.sh large`.
* StreamDigest with new digests, its four modes equal.
* Performance before and after on a quiet F53 (T10): `performance.sh`
  suites, CORE, MEM (Props MEM 129 to 130 today, at most 131); a cold
  start at sd 50 MB (007).
* For the full set also: the conformance with (a) once the checker has
  its step; (b') with the level scripts on.

### 6.4 Lean, documents, C

* **Lean.** Core: A2A3Check2's transient nodes (Z18); sis-model.md 3.4
  (transient nodes, the empty key first). Full set: (a)'s step 5 and
  INV-1 in `lean/SIS` and `lean/Check`; (b')'s test in the checker and
  the physical theorems re-proved (a task at effort xhigh, size unknown).
* **Documents.** docs/levels.md sections 4 to 7 (the delete's climb, the
  empty key, merges, reclaim's scan and E, the dead hand); README's
  bounds; the release notes: the bounds, format 6, the refusal; the
  `noEvict()` Javadoc (Z15).
* **C port** (022, after the release): core about 500 lines (P4's 400,
  P8's step, the dead hand); full set about 300 more for merges, plus
  (a), (b'), the queue; `cross.sh full` with a new pin.

### 6.5 Size and order

| Step                         | Core        | Full set         |
|---|---|---|
| Java, main code (prototypes) | ~1,200 lines | ~2,400 lines           |
| Integration and clean-up     | 1 day        | 2 to 3 days            |
| Tests of 6.2                 | 1 to 2 days  | 2 to 3 days            |
| Gates and performance        | 1 day        | 1 to 2 days            |
| Lean                         | checker only | model and proofs, days |

Lines are the prototypes' diffs of `java/src` without tests (P4 785, P5's
merges about 545, P6 430, P7 (a) 100 and (b') 113, P8 123, SE about 90;
P3's `maintain()` not counted apart from its rebuild).


## 7. Open risks, either tier

* The pieces never ran together; each gate above is per branch.
* No T10 on any branch; F53's timings today were unreliable.
* Startup: the rerun reads each delete's path (and siblings with
  merges); cold start at 50 MB not measured.
* C9 over by a few objects at small N (P8, P7): a phase of the measure, to
  be settled before T1 gates.
* `IndexJobsHarness` races on a loaded machine (P5, 3).
* The bound of `dirtyNodeBound` is not proved in either form.


## 8. Questions for the reviewers

Each review should first check, against the branches' code:

1. **UP's rule and the take-back** (5.1): is every node of tt that the
   climb leaves out either taken back with no klong naming it, or linked?
   Is X5 (c) reachable? Does the rerun make the same choices (I8)?
2. **LE-b** (5.2): does any reader, writer or split rely on a node's
   first klong being tight? Is the inserted-klong rule complete for every
   split (`spaceSplit`, `spaceSplitInPlace`, the three space splits)?
3. **The bitmap rule** in every place that adds a klong after a bitmap of
   tt in the same node: `emptyKeyNext`, `mergeParent`, `appendDeleteKlong`.
4. **P8's argument** (P8, 2.3 and 2.4): the values' claim with UP and
   merges, where a key's routing node changes; E with keys put before E.
5. **The dead hand with P8** (5.6): does any reader or the writer reach an
   object stored before pCut once the cut is decided but not made?
6. **K4's bound**: can a transaction of deletes dirty more nodes than the
   bound without merges? With merges?
7. **(a)'s start rule** (5.10): can a start drop an id that is still
   dirty? **(b')** (5.11): is e(y) exact after a restart?
8. **Interactions**: merges with the take-back and RC in one
   transaction; P8's touch with merges; the dead hand with the replaced
   queue and readers at earlier times.
9. **Anything simpler** that meets 3.2's table with fewer rerun rules.


## 9. Decisions

### 9.1 For Frans: the tier

* **D1. The KISS core or the full set, or a middle.** The core reopens:
  * **Z12** (merges in format 6 if P5's gates pass and two points close:
    "as recommended", 13:42). P5's report says all three conditions are
    met. Out of format 6, merges come with a format that refuses 2026.4's
    databases (as 2026.4 refuses 2026.3's) or with two rerun paths.
  * **Z13** (the window, "solve this now", 13:42). Out, the window stays
    in 2026.4, named in C6 and C9; (a) can come later with no refusal.
  * **Y10** (`maintain()`, "yes", 12:31). Out, it can come later with no
    format change.

  A middle: the core plus merges (the one addition that costs a refusal
  if late), or plus (a) (the one asked for now). Not decided here: the
  choice is Frans's; section 4 gives each addition's gain and cost.

### 9.2 For Frans: smaller ones

* **D2. (b')** (P7's Q2: with merges, yes). Recommended here: not in
  2026.4, even with merges. The rule holds without it (P7, 6.3); it costs
  16 bytes a got-dirty entry and the largest Lean item (the physical
  theorems); later it is a change of the record syntax (section 4, F3).
* **D3. The replaced queue**: as Z15; recommended: kept off by default in
  2026.4 unless P8's removal of the loads and a measure of reads at
  earlier times are done before the release's gates.
* **D4. E** (P8's Q1): keep; recommended.
* **D5. Work during a mass delete** (P8's Q2): accept; recommended.
* **D6. `dirtyNodeBound`** (P5's Q6): by node of the paths, checked
  against counted nodes; recommended.
* **D7. The refusal message** names 2026.3; recommended.
* **D8. C9's measure** (P8's Q4): M11 at a fixed phase of the startup
  pos; recommended.
* **D9. "sparse"'s allowance**: 10 + L h_fill with L the live keys for the
  core; recommended, with strict only if merges are in.
* **D10. Z16** (with merges: left sibling first, cap B / 2, "sparse" at
  1.44): accept; recommended.
* **D11. Z18** (A2A3Check2's transient nodes): approve; recommended.
* **D12. Z19** (new expected values of 3.4 and 5.10): approve each in the
  format entry; recommended.
* **D13. Z20** (the take-back's form: the klong of tt pointed to the node
  it replaced, with the retarget of every klong of tt): approve;
  recommended.

### 9.3 Taken already

| Decision                                      | When, where              |
|---|---|
| F9 (a): earlier databases refused                   | 10:30, 023-02 7.2         |
| F10: a format change in 2026.4                      | 10:30, 023-02 7.2         |
| F5: bounded enough; strict if good                  | 10:38, 023-02 7.2         |
| F2: every ended version                             | 10:41, 023-02 7.2         |
| F3: the scan bound at every available time          | 10:44, 023-02 7.2         |
| F1: dead klongs go, eventually (implied)            | 10:44, 023-02 7.2         |
| F7: user writes drive it; `maintain()` good         | 10:49, 023-02 7.2         |
| Y2: root collapse at the delete                     | 12:31, 023-04 7           |
| Y7: SE in 2026.4; TE optional                       | 12:31, 023-04 7           |
| Y8: one format 6; 2026.3 refused by name            | 12:31, 023-04 7           |
| Y10: `maintain()` yes, optional                     | 12:31, 023-04 7           |
| Y6 (b): memory follows the rule                     | 12:35, 023-04 7           |
| Z12: merges in format 6, on conditions              | 13:42, 023-06 16          |
| Z13: the window solved now                          | 13:42, 023-06 16          |
| Z14: each step scans at its own time                | 13:42, 023-06 16          |
| Z15: dead hand on; queue on conditions; `noEvict()` | 13:57 to 13:59, 023-06 16 |


## 10. State

2026-11-10, 14:50. Written from 023-01 to 023-06, the eight reports of
023-05 (P7's a draft of 14:30 and its numbers of 14:29) and the code at
the heads of section 2; nothing built or run. Open: Frans's D1 to D13;
the three independent reviews (section 8); P7's level2 full and level3
full results.
