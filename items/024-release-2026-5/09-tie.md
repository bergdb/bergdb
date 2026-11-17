# 024-09. The tie repaired: A1 to A4 of the model gap

Created 2026-11-11. Status: done (2026-11-11): on `main` since
`773c2105` (024-13), the follow-up since `01b14c68`.

The first step towards aim 4 of release 2026.5 (024-04: "the model
matches"): the four weak points that 024-06, section 4.4, found in the
tie between the Lean model and the code of release 2026.4, repaired as
its section 5.1 proposes (A1 to A4). Not here: B to E of 024-06 (keys in
the trace and the key tree in Lean are 024-12's).

**A3's verdict: T-SCHEME's argument holds for 2026.4's code. No
counterexample.** Step 3 of 001-07, section 5, is written again in
section 4: its premise "a key range only shrinks" is replaced by the one
that 2026.4 has, "a node that stays current and gets no entry loses no
key" (ranges only grow), and the conclusion is the same: every index
node reachable from the first available time on is new, changed or in a
step's touch since the iteration began. Checked directly on 90 traces:
183,375 of 183,375 nodes that are not new are in a step's touch (4.6).
The argument is by reading, not a proof.

**On `main` since 10:08 (024-07 landed, `36924319`) the touch of a key
range is gone**, and with it step 3: T-COVER and T-LATEST (024-07,
section 4) take its place, with no key range in them. Section 4.8 reads
their two premises against the delete path: nothing found against them.
Sections 4.1 to 4.7 are the argument for release 2026.4 as tagged.

Cite the parts as "024-09, A1" to "A4", the facts of section 4 as
"024-09, F1" to "F3".


## 1. In short

* **A1, the gates reach the take-back.** `level2.sh` runs seven draining
  configurations of A2A3Check2 and a new conformance set `drain`, and a
  configuration that takes back no node fails; `night.sh` runs UnlinkFuzz
  (`stress/unlinkfuzz.sh`). P5's head with fault 12 passes its own
  `level2.sh` and fails the new one (A-COPY, 16 transactions), the night
  step (5 s for the configuration that finds it) and the set `drain`
  (section 2).
* **A1 answers 024-06's open count.** Of the 70 standing traces of
  `level2.sh`, 8 take back a node (27 nodes in all, 24 of them in the a6
  configuration); the new set `drain` takes back 1,366 in 50 traces.
* **A2, `PhysStep` is a theorem.** Proved in Lean, for any structure,
  from TREE, A5 and a property of `live` (`LiveAppend`) that is proved
  for the checker's `blive`: `PhysRunOK` follows from what C-A checks on
  every trace. Nothing in 2026.4's delete path contradicts it (section
  3).
* **A3, T-SCHEME's argument holds** for 2026.4's code, with a new
  premise (above; section 4). On `main` since 024-07 its step 3 is two
  theorems of the model; their premise about the tree, that no reachable
  key node is without a live key below it, is what the delete path keeps
  (section 4.8).
* **A4, A6 itself holds in every run checked**: 0 adoptions below the
  old parent in 42,500 transactions of A2A3Check2 and in 201 traces. The
  model is not changed for it. **Lean's take is Java's again** (015-03):
  `javaTake` has the integer share and dither of 005-79, and a new gate
  compares the two, `TakeCheck check` in `level2.sh` (section 5).
* **No expected value of a Java test changed.** In Lean, the `#guard`s of
  the double rule's bits are replaced by those of the integer rule's
  numbers (section 5.2).
* **Something 024-06 has wrong:** P5's head does not pass `main`'s
  gates. `main`'s `conformance.sh small` fails it since 023-09 (the a6
  traces must show no adoption below the old parent). P5 passed its own
  scripts, which asked for the opposite (section 2.4).


## 2. A1: the gates reach the take-back

The weak point (024-06, section 4.4, point 3): `level2.sh`'s three
A2A3Check2 configurations take back 0 nodes; the draining trace
configurations and UnlinkFuzz were in no script.

### 2.1 What is new

* **A2A3Check2** has a property `shape=long`: UnlinkFuzz's long key
  shape (keys of 1 to 3 and more segments that share prefixes, so many
  small segment trees come and go). Without the property nothing changes.
* **`level2.sh`, step 7** runs, after its three configurations, seven
  draining ones, in quick and in full: 023-09's five and two with
  `shape=long` (300 seeds of 30 transactions, 40 operations each; one
  sorted, one with `unsorted=1`). Each must meet every rule (A2, A3, A5,
  marking, TREE, A6', A-COPY) and take back at least one node: with 0
  the step fails and says that the configuration no longer reaches the
  take-back. On 2026.4's code they take back 26, 12, 559, 307, 324,
  2,658 and 903 nodes; 11 s in all.
* **`conformance.sh drain`**, a new set, run by step 7 after `small` (2
  seeds quick, 10 full): five configurations with 50 to 65 % deletes on
  25 to 200 keys. Three use TraceExport's new `long=2` (the same long
  key shape). `r-drain` joins the set `reclaim`, `e-drain` and
  `e-r-drain` the set `evict`. A configuration named *drain* that takes
  back no node over its seeds fails the set.
* **TraceExport** prints the Dag's counters as its last output line (not
  in the trace), and every set's summary sums them.
* **`stress/unlinkfuzz.sh`**, a step of `night.sh` after `fuzz`:
  UnlinkFuzz on 16 configurations (023-09's gate runs, P4's draining
  ones, three fifo ones, and four with 40 operations a transaction on long
  keys), each on a fixed block of seeds from 1 and on a block of the
  day's seeds; 4 JVMs at once; 3,226 rounds in 294 s. Not in
  `before-commit.sh`.

Take-backs of the set `drain` over 10 seeds (segment roots among them):
drain 58 (18), drainlong 132 (4), drainbig 381 (227), drain14 58 (34),
drainroots 737 (398).

### 2.2 How often the traces reach the delete path

024-06 could not determine this by reading. Summed over the exports of a
set (each JVM's runs A, B and E together):

| Set, seeds      | Traces | Unlinked | Taken back (roots) | Collapses | LE-b  |
|---|---|---|---|---|---|
| small, 10       | 70 | 1,524  | 27 (18)     | 71    | 159   |
| reclaim, 5      | 30 | 1,533  | 23 (2)      | 2     | 184   |
| evict, 3        | 51 | 2,420  | 53 (9)      | 36    | 324   |
| drain, 10 (new) | 50 | 66,389 | 1,366 (681) | 2,225 | 3,360 |

* In `small`, 8 of the 70 traces take back a node: 24 of the 27 nodes
  are a6's, 3 are mixed's; long, big, bulk, idle and hot take back none.
* Without the new configurations `reclaim` takes back 2 nodes in 25
  traces and `evict` 16 in 45.
* LE-b: the times the empty key was pointed to the next child.

### 2.3 The test: P5's head with fault 12

The branch `024-09-p5-fault12` (in the worktree `wt-p5`, head
`57c352c4`) is P5's head `71e386de` with its own UnlinkFuzz plus 023-08's
options `order` and `dup`, and the six gate files of this work.

| Gate                              | On P5's head                                 |
|---|---|
| P5's own `level2.sh quick`        | LEVEL 2 OK (86 s)                            |
| the new `level2.sh quick`         | LEVEL 2 FAILED: draining configuration 6,    |
|                                   | A-COPY, 16 new pointers in 16 transactions   |
| the new `unlinkfuzz.sh`           | UNLINKFUZZ FAILED: 7 blocks; the first at    |
|                                   | seed 41, "klong 4 points to taken-back node" |
| the new `conformance.sh drain`    | CONFORMANCE FAILED: drainroots-1 and -2      |
| `main`'s `conformance.sh small 2` | CONFORMANCE FAILED: the a6 rule (2.4)        |

* **A2A3Check2 sees fault 12 as a failure of A-COPY:** the klong left in
  the segment leaf names a node that the transaction took back, so it is
  neither made by the transaction nor on the writer's paths. With
  A2A3Check2's own keys (`long=1`) P5 passes all eight configurations
  and six more with 320 seeds: the fault needs a segment root made, split in
  place and emptied in one transaction, which `shape=long` gives.
* **UnlinkFuzz** finds it in 5 s when the failing configuration runs
  alone, 76 s into the script.
* **The trace checker does not see it in the gate:** the two drainroots
  traces stop in TraceExport, on the writer's assertion under -ea
  (`spos of index node pointer ... is vpos`). The other 13 traces are
  TRACECHECK OK. In the search for configurations one P5 trace with the
  fault in its last transaction failed the checker itself (C-A: A4 and
  A-COPY). Plain draining traces (1,800 transactions with `long=2` and
  40 operations) do not reach the fault; drainroots puts 120 operations
  on 90 keys in every transaction.
* On the branch's head all of these pass (2.5).

Outputs: `/Users/f/fl/bench/2026-11-11/tie/a1/` (`p5-*.txt`,
`tie-*.txt`, `tune/` for the search).

### 2.4 A correction of 024-06

024-06 says (sections 1 and 3.3) that P5's branch passed level1 to
level4 in full with fault 12 in its head. It did, with its own scripts.
`main`'s scripts fail it: since 023-09 (`80105ef1`) `conformance.sh`
fails an a6 trace that shows an adoption below the old parent, and P5's
head shows one (the second klong of fault 12's source). P5's
`conformance.sh` asked for the opposite, at least one adoption. So the
standing gate would have stopped P5's head, by the symptom's cause, not
by the fault. The new checks fail it by the fault.

### 2.5 Gates and times

| Gate, on the branch                 | Result                         |
|---|---|
| `before-commit.sh` (`ce1043cf`)     | BEFORE COMMIT OK (268 s)       |
| `level2.sh` full (`472d7716`)       | LEVEL 2 OK (685 s)             |
| `level2.sh quick` (`ce1043cf`)      | LEVEL 2 OK (128 s)             |
| `conformance.sh reclaim`, 30 traces | CONFORMANCE OK; C-CUT 0 of 321 |
| `conformance.sh evict`, 51 traces   | CONFORMANCE OK                 |
| `unlinkfuzz.sh`, by itself          | UNLINKFUZZ OK (294 s)          |

Step 7 of `level2.sh` full took 33 s before and 125 s after: 11 s for
the seven A2A3Check2 configurations, 81 s for `drain` with 10 seeds.
`ce1043cf` differs from `472d7716` in a message and two comments.

After A4 and the merge of `main` (the head `43cebf22`), each in its own
hold of the lock:

| Gate, on `43cebf22`                 | Result                                |
|---|---|
| `lake build`                        | completed successfully (151 jobs)     |
| `sorry`, `axiom`, `native_decide`   | 0 by grep; `#print axioms` standard   |
| `before-commit.sh`                  | BEFORE COMMIT OK (82 s)               |
| `level2.sh` full                    | LEVEL 2 OK (734 s)                    |
| r-drain, e-drain, e-r-drain, singly | 11 of 11 TRACECHECK OK; C-CUT 0 of 25 |

`level2.sh`'s step 7 there: 70 of 70 and 50 of 50 traces, the seven
draining A2A3Check2 configurations, TAKECHECK OK (300 cases, 8 dithers,
11 shares). `#print axioms` of the A2 theorems, and of 024-07's
`T_cover` and `T_latest`: propext, Classical.choice, Quot.sound.

Decisions taken: `e-r-drain` has 10 operations and 65 % deletes (P4's 6
and 60 take back no node at seeds 1 and 2, and `level4.sh quick` runs one
seed); P4's two fifo fuzz configurations are smaller (theirs take 150 to
206 s a round); `level2.sh`'s old loop is left as it is, so its six
greps exist twice.


## 3. A2: `PhysStep` is a theorem

The weak point (024-06, section 4.4, point 1): the handle theorems and
lazy reading assume `PhysRunOK`; it was argued in a text older than the
delete path (011-11, section 13.3) and nothing checked it.

**Which, and why.** Lean lemmas, not a conformance check: both fields
follow from what the model already assumes, so a check on traces would
only have repeated what C-A checks.

* **`adopt`** (a node's new live child, not made by the change, was the
  live child of a node that the change changes or that is no longer
  reachable): from TREE after the transaction and A5, for any `Spec`.
  TREE before the transaction is not needed: every reachable node but
  the root has a reachable parent by the definition of reachability.
* **`liveNew`** (a node's new live children are pointees of its new
  entries): from a property of `live` alone, `LiveAppend`: a live child
  of a history h ++ h' is a live child of h or a pointee of an entry of
  h'. Proved for the checker's `blive` (`blive_append`).
* **Together:** `PhysRunOK` from `RunOK`, TREE after every transaction
  and `LiveAppend`.

The statements (`lean/SIS/Proof/PhysAssumptions.lean`,
`lean/Check/Live.lean`; no trusted file changed):

```lean
def LiveAppend (sp : Spec V T) : Prop :=
  ∀ (h h' : History V) (y : NodeId), y ∈ sp.live (h ++ h') →
    y ∈ sp.live h ∨ ∃ e ∈ h', y ∈ sp.ptrs e.val

theorem physRunOK_of_tree (hok : RunOK sp al ts) (hla : LiveAppend sp)
    (htree : ∀ j < ts.length,
      treeAt sp (run sp al (ts.take (j + 1))).P (j + 1)) :
    PhysRunOK sp al ts

theorem physRunOK_of_evict (hok : RunOK sp al ts) (hla : LiveAppend sp)
    (hev : EvictRunOK sp al ts) : PhysRunOK sp al ts

theorem blive_append (h h' : History BVal) (y : NodeId)
    (hy : y ∈ blive (h ++ h')) :
    y ∈ blive h ∨ ∃ e ∈ h', y ∈ bptrs e.val
```

Also `blive_sub` (`SpecOK.liveSub` for `blive`, which was "by
construction" only), `bspec_physRunOK` and `bspec_physRunOK_evict` (the
two above for a trace's instance), `without_physRunOK` (any theorem that
assumes `RunOK`, `PhysRunOK` and `EvictRunOK` holds without `PhysRunOK`,
given `LiveAppend`) and one use of it, `bspec_tr_handles`. `#print
axioms` of all of them: propext, Classical.choice, Quot.sound, or the
first and last only.

**What remains assumed for a trace, and where it is checked:**

| Hypothesis                         | Checked on a trace by                   |
|---|---|
| `RunOK`: `SpecOK` but `liveSub`    | C-A, `initFailures`, for R(0)           |
| `SpecOK.liveSub`, `LiveAppend`     | proved now: `blive_sub`, `blive_append` |
| `StepOK`: A2 to A5, ids, the touch | C-A, `stepFailures`, `touchFailures`    |
| TREE after every transaction       | C-A, `treeFailures`                     |

Not theorems, as for every C-A check: that the checker's Bool functions
equal the Lean Props, and that the checker's P is the model run's P.
That is the next gap of this kind; `treeFailures` and A5 would be the
first two to prove, and it is not small.

**Against 2026.4's delete path.** The upward unlink deletes a klong, the
empty key first adds a klong whose pointee is the next child, root
collapse makes a top node or a klong to the child, a node taken back is
in no entry: each new live child is a pointee of a new entry, and TREE
and A5 are checked on every trace, the draining ones included (section
2). Nothing 2026.4 does is outside the lemmas' hypotheses.

**Left for a decision** (section 7, question 1): the trusted statements
still name `PhysRunOK`. Replacing it by `LiveAppend` (and TREE in
`T1_lazy`, `T2_lazy` and `CC_canonical`, which do not assume
`EvictRunOK`) changes the trusted part.


## 4. A3: T-SCHEME's step 3, for 2026.4's code

The weak point (024-06, section 4.4, point 2): step 3 of the argument
that Java's reclaim gives safe cuts (001-07, section 5) says "A key
range only shrinks when a node splits". Since 2026.4 a range also grows.

### 4.1 What step 3 must give

An iteration starts at stream position pStart and time tStart; its
steps are internal transactions at times t_1 < ... < t_m = tEnd; the cut
is at pCut, at or before pStart; f is tEnd.

**S3.** Every key node x that is reachable at some time t at or after
tEnd is (a) made by a transaction after pStart, or (b) in the touch of
a step of the iteration, or (c) given an entry by a transaction of the
iteration's time, from its first step on.

In each case x is made dirty by a record after pStart, so it is written
at pCut or later once the startup pos has passed that record (step 5 of
001-07, section 5, unchanged). Top nodes are step 4's.

### 4.2 The three facts

* **F1. The steps' ranges tile the key space.** Step j touches the keys
  after `it.lastKey`, up to and including the last key of its own scan;
  the next step's `lastKey` is that key; the first step starts at the
  first key (`touchFrom` null) and the last one has no end (`touchTo`
  null at the end of the scan). `Reclaim.java`, where the step's
  transaction is built. A step that throws a `RerunException` is tried
  again with the same range.
* **F2. A step's touch visits every key node on the search path of
  every key of its range, in the tree as it is when the step runs.**
  `Db.touchRange` is a forward scan at the step's time without an end
  key, before the step's puts: `GetMany.Chain.setup` descends along the
  search path of the start key (`searchLte` at each node), and `next`
  goes on to every later live klong and into every child, in key order,
  until the first live KV after the range's end is delivered. No child
  is pruned (021-28's pruning needs an end key, which the touch does not
  set). Every pointer it follows marks the node. So it visits a superset:
  also the nodes up to the first live key after the range.
* **F3 (new). A key node that stays current and gets no entry loses no
  key.** Let T be a transaction at time tt and x a key node that is
  current before T and at tt, with no entry of time tt. Then every key
  whose search path passed through x before T passes through x at tt.

F3 by cases, over every way `Dag.java` changes what a klong of an inner
node or a segment leaf leads to (the list of 023-08's take-back check,
section 4, without P5's merges):

| Change at tt                         | Whose range changes, and how            |
|---|---|
| a split links its second half        | only the split node's: it is replaced,  |
| (`appendKlongs`, new root)           | or made by tt and split in place        |
| a time split's klong                 | none: the last version takes the range  |
| UP: a klong deleted (`deleteUpward`) | the left sibling's grows by the         |
|                                      | emptied child's; that child is unlinked |
| LE-b (`emptyKeyNext`)                | the next child's grows down to the      |
|                                      | node's lower bound                      |
| RC (`replaceRoot`, `takeBackRoot`)   | none: the only child had the whole      |
|                                      | range of its root                       |
| take-back (`takeBack`, `retarget`)   | as UP: the klong goes back to the       |
|                                      | replaced node and is then deleted       |
| a split or time split of an ancestor | none: the klongs are divided at a       |
|                                      | klong, the second half's first klong    |
|                                      | becomes the empty key below the same    |
|                                      | klong in the parent                     |
| a klong of tt pointed in place       | only nodes made by tt                   |

* A klong is added between two live klongs of a node only by the split
  of the child at the lower one. A node that existed before tt is never
  split in place (`handleFullNode`: `newInTrans`): it is replaced, so it
  is not current at tt. So no node that stays current loses the upper
  part of its range, and none loses the lower part, as nothing raises a
  live klong's compare value.
* A node "made by tt" in `handleFullNode`'s sense includes the first,
  empty root, filled by its first transaction and split in place there:
  it gets entries of tt, which F3 excludes.
* So in 2026.4 the range of a node that stays current only grows: UP and
  LE-b are the two cases, and both give a superset.

### 4.3 The argument

Let x be a key node reachable at a time t at or after tEnd, and not made
after pStart. Then:

1. x is current when each step runs. It was made before the first step
   and is reachable at t; a node that is not current at one time and
   current at a later one would be a resurrection, which A5 excludes
   (checked by C-A on every trace and by A2A3Check2).
2. If some transaction from the first step on, up to tEnd, gives x an
   entry, that is (c): x is changed, so dirty, in a record after pStart.
   Else:
3. Take a key k whose search path passes through x when step 1 runs;
   there is one, as a current node's klong and the next live klong of
   its parent are a non-empty range. By F1, k is in the range of exactly
   one step j.
4. By F3, applied to every transaction between step 1 and step j, the
   search path of k still passes through x when step j runs.
5. By F2, step j's touch visits x. That is (b).

In the traces of 4.6 every such x is in a step's touch; (c) alone did not
occur.

### 4.4 Where the old premise was used, and why its loss does no harm

The old text took a key of x's range at the end, at t, and needed the
range to be no larger then than at each step's time: "only shrinks".
With UP and LE-b that is false: at t the range may hold keys that x did
not have when their step ran, so the step whose range they are in may
not have visited x.

The new argument takes the key at the start, at step 1, and needs the
range to be no smaller later: "only grows", which is F3. What would
break S3 is a node whose range does both: it would have to be ahead of
the scan when a step passes and behind it at the next, so lose its lower
part. Nothing in 2026.4 takes keys from a node that stays current.

For the code before 2026.4 both premises held: the range of a node that
stays current did not change at all.

### 4.5 The other steps of 001-07, section 5

Read against 2026.4's changes; none needs a new premise.

* **Step 2, the values.** The scan is at tStart, the read of each key at
  the latest time; a delete since tStart means no rewrite, and a put
  since tStart is after pStart. Unchanged, and UnlinkFuzz checks scans at
  every earlier time across UP, LE-b and RC.
* **Step 3's second sentence**, on nodes that hold deleted keys only:
  since format 6 an emptied node is unlinked at the delete, and so is an
  emptied segment tree; what stays is an empty space root that is a
  segment leaf, on every search path. The touch does not depend on live
  keys anyway (F2).
* **Step 4, the root chain.** Root collapse of a space root makes a new
  top node, as a time split does: made after pStart if the collapse is.
* **Step 5, written after the mark.** An unlinked node leaves D only if
  it got dirty in that transaction alone (`Db.endOfTrans`); a node that
  a step touched and a later delete unlinks stays in D and is written at
  pCut or later, which the reads at the times between tEnd and the
  delete need.
* **Step 6, the references.** LE-b's klong of the empty key holds a copy
  of the next child's pointer in a node that the delete changes. A
  parent written while a child is in D stays in D (Rule A) and is written
  again after it, as for a split's klong to an old child. Nothing new.
* **Step 7** is proved in the model (T12).

### 4.6 Checked by running

`09-tie/cover.py` reads a reclaim trace and checks S3 directly: for
every cut, with the iteration's steps the records of kind step since the
cut before, every index node reachable at f (by the model's reading of
the entries) and made before the iteration's first step must be in a
step's TOUCH line.

| Traces                                    | Cuts  | Old nodes | Not touched |
|---|---|---|---|
| `conformance.sh reclaim`, 30 (5 seeds)    | 321   | 13,791  | 0 |
| 60 more, draining, reclaim on (`more.sh`) | 1,893 | 169,584 | 0 |

* "Old nodes": index nodes reachable at f and made before the first
  step; 46,148 more were made in their iteration.
* The 60 more: 5 configurations, 12 seeds, 600 to 800 transactions,
  52 to 60 % deletes, three with long keys; their JVMs unlinked 32,810
  nodes, pointed the empty key to the next child 2,778 times, collapsed
  337 roots and took back 218 nodes. No trace had an error.
* The check can fail: with the first step's TOUCH left out, 10,126 of
  the 13,791 are reported.
* C-CUT, the conclusion of the whole argument: 0 of 321 cuts fail in
  the set `reclaim` with r-drain (section 2.5).
* Results: `09-tie/cover-results.txt`.

### 4.7 Limits, and what changes it

* **By reading, not proved.** F1 to F3 are about keys, which the model
  does not have. F3's table is this section's reading of `Dag.java`.
* **Merges** (023-05 P5) move klongs between nodes that stay current:
  F3 must be read again for them. A node that receives klongs gets
  entries; a node that gives klongs up and stays current would break F3.
* **024-07's fix** removes the range touch: a step then makes dirty
  only the paths of its own puts. Step 3, F2 and F3 no longer apply
  there; its T-COVER takes their place (4.8). It landed on `main` while
  this was written; sections 4.1 to 4.7 are the argument for release
  2026.4 as tagged.

### 4.8 Against `main` after 024-07: the touch on a step's own paths

`main` at `36924319` has no `Db.touchRange`: a step makes dirty the
index nodes on the paths of its own puts. 024-07, section 4, replaces
step 3 by two theorems of the model, T-COVER and T-LATEST, with two
premises that are Java's: REWRITES (every data node reachable at the
iteration's end is at the cut or later) and LIVEBELOW (every index node
reachable then has a data node below it).

**Result: nothing in the delete path is against either premise.**

* **No key range is left** in the argument for the index nodes. S3, F2
  and F3 are not needed on `main`; F1's scan half is REWRITES, step 2 of
  001-07, section 5, unchanged.
* **LIVEBELOW is the premise that the delete path carries.** Read from
  `Dag.deleteUpward` and the functions of F3's table: every node that a
  delete empties is unlinked, across segment trees; LE-b is taken only
  with a next live child; root collapse, the take-back, a split's halves
  and a time split's last version leave no node empty. The two
  exceptions are the ones 024-07 names, and no third was found: an empty
  space root that is a segment leaf, which reclaim's own rows keep
  non-empty while reclaim is on, and a node made fresh by a transaction
  and emptied in it, a `Bug` since 2026-11-10.
* **Evidence on the merged tree** (the branch with `main` merged in):
  the checker checks LIVEBELOW at every cut (CUT-live, in C-CUT). The
  draining configurations r-drain, e-drain and e-r-drain: 11 of 11
  traces TRACECHECK OK, C-CUT 0 of 25 cuts, no CUT-live line; they take
  back 58 nodes. `level2.sh`'s traces, the set `drain` among them: 120
  of 120 TRACECHECK OK.
* **`cover.py` is for 2026.4's touch**: on `main` a TOUCH line holds the
  paths of the step's puts, so 4.6's check does not apply there.

Not done, for a later agent: the 60 draining reclaim traces of 4.6 made
again on the merged tree and run through the checker
(`/Users/f/fl/bench/2026-11-11/tie/a3/more2.sh`, about 5 minutes under
the heavy lock): 1,900 more cuts for CUT-live.


## 5. A4: A6 for A6', and Lean's take

### 5.1 A6 for A6' (024-01, LM1)

A6: no index node reachable at a time is pointed to, by a klong that is
not live, from another reachable node. The model assumes the weaker A6',
which allows it below the old parent, for the one place where Java did
that: a segment root made and split in place in one transaction
(005-04). Fault 12's fix points that klong in place instead (023-09).

**Checked now: A6 holds in every run of the gates.**

* A2A3Check2, the ten configurations of `level2.sh`: 42,500
  transactions, adoptions below the old parent 0, not below it 0.
* The trace checker, the sets small, drain, reclaim and evict: 201
  traces, "C-A adoptions below the old parent: 0 transactions" in each
  set's summary.
* By reading, with the list of F3's table: a klong that is not live
  names a node that is unlinked, replaced or taken back, or, after LE-b,
  the next child, which is the node's live child by the empty key.

**The model is not changed** (024-06, question 7): A6' is weaker than
what Java does, not wrong, and P5's merges were checked against A6'
only. On P5's head A2A3Check2 counts adoptions below the old parent (1,
11 and 2 in three configurations), from fault 12's source. Two lines
would make the gates require A6 everywhere (section 7, question 2).

### 5.2 Lean's take is Java's again (015-03)

The weak point (024-06, section 4.4, point 4): `javaTake` in
`lean/SIS/Bound.lean` was the double rule that Java had from 2026-10-28
until 005-79, and no gate compared Java's take with it.

That was plainly wrong as a description of Java, so it is changed:

* **`Bound.lean`** (trusted, definitions only; no theorem uses them):
  `share` and `dither` on `Float` are replaced by `shareFp` and
  `ditherFp` on `Nat`, in units of 2^-16, and `javaPace` uses them with
  Java's test, `((taken + count) << 16) > share && share - (taken << 16)
  <= u * count`. `shareFp` is floor(D o L 2^16 / (O sd)), at most
  D 2^16, and `Long.MAX_VALUE` outside Java's bounds: the expression
  that Java's unit test `testShareFpExact` compares `TransSeq.shareFp`
  with.
* **`BoundExample.lean`**: the `#guard`s of the double rule's bits are
  replaced by `#guard`s of Java's numbers: 8 dithers, 11 shares (5 of
  them outside the bounds) and `TransSeq.testShare`'s cases with its
  tie, where the two rules differ. The 300 generated cases keep their
  expected numbers: Java's integer take of 2026.4 gives the same 300
  (`TakeCheck 300`, run today), and so does the model's.
* **`java/stress/TakeCheck.java`** (from 007-08, where it no longer
  compiled, 015-19): the build compiles it now. `TakeCheck check`
  compares Java's take on the 300 cases, and `ditherFp` and `shareFp`,
  with the same numbers as the `#guard`s; `level2.sh` runs it in step 7,
  beside `lake build`. So a change of the take's arithmetic on either
  side fails `level2.sh` until both lists are changed.
* T3 is untouched: `T3_take` holds for any pace.

What the gate does not compare: the take inside a traced run (C-S still
takes each record's startup pos from Java).


## 6. What B0 and B1 would need, as this work shows it

* **The take-back in B1's `exec`.** A node made and taken back is in no
  line of a trace; its id is used up. Fault 12 was a klong of the
  transaction's time that named such a node. The checker saw it once
  (C-A: A4, a pointee that does not exist), but in the gate TraceExport's
  own assertion stops the export first. B1's `exec` must make and take
  back the node as Java does, so that the ids agree and "every pointee of
  a new entry exists" is a property of the model's own change.
* **Workloads.** Plain draining traces did not reach fault 12; it took
  120 operations on 90 keys a transaction with the long key shape. B2's
  comparison needs the set `drain`, drainroots above all.
* **For reclaim, on `main` since 024-07: two properties of `exec`
  (B1).** T-COVER's premises are Java's today. LIVEBELOW, no reachable
  key node without a live key below it, is a statement about the tree's
  `exec` for deletes (UP, LE-b, RC, the take-back), with the empty space
  root as its exception; REWRITES needs the scan at an earlier time.
  With both proved for B1, T-COVER and T-LATEST hold for the tree with
  no premise left (024-07, section 4.4, says the same).
* **Key ranges (B0), for 2026.4's touch only.** With each klong's key in
  the trace a node's key range can be computed, and F2 and F3 of section
  4 would be checks. `main` no longer needs them. F3, "routing is
  preserved for a node that a change leaves current and without an
  entry", is still what a merge must keep if any later argument uses key
  ranges.
* **`live` (B1).** `LiveAppend` and `SpecOK.liveSub` must hold for the
  tree's `live`; `blive_append` and `blive_sub` are the proofs for
  `blive`. `PhysRunOK` then follows from TREE (024-06's C1).
* **A6 (B1).** 2026.4 meets A6; a tree model can be written for A6, and
  merges checked against it.


## 7. Questions for Frans

1. **`PhysRunOK` out of the trusted statements?** `tc_handles`,
   `tr_handles`, `T1_lazy` and the others would assume `LiveAppend` in
   its place (and TREE where `EvictRunOK` is not assumed). A change of
   the trusted part, small. **Recommended: yes, as its own commit, when
   024-12's model has landed.**
2. **A6 required by the gates now?** Two lines: `conformance.sh`'s a6
   rule for every trace, and A2A3Check2's count of adoptions below the
   old parent required to be 0 in `level2.sh`. The model's A6' becomes A6
   after the merge decision (024-06, question 7). **Recommended: yes.**
3. **015-03 and 015-19** are done by this branch (section 5.2).
   **Recommended: close both when it lands.**
4. **The gates' time** (024-06, question 6): `level2.sh` full 92 s
   longer, the night 5 minutes. **Recommended: accept.**
5. **TakeCheck's 300 numbers are held twice**, in Java and in Lean, by
   design: each side is compared with constants. **Recommended: keep.**
6. **Where the current T-SCHEME argument lives.** Settled by 024-07's
   landing: docs/levels.md, section 6, cites 024-07, section 4, for
   `main`. Section 4 here is the argument for release 2026.4 as tagged;
   nothing to add to docs/levels.md.


## 8. State

2026-11-11, 10:33. Written by the agent "tie". A1 and A2 were done by two
helpers of it; this file was started late (09:47), because each helper
call blocked its caller until the helper ended.

* **Done:** A1, A2, A3 (the argument for 2026.4's code and its check;
  section 4.8 for `main`'s new touch), A4 (the check of A6; the take in
  integers with its gate). Everything is committed, `main` is merged in,
  the gates passed on the head.
* **The head to merge:** `43cebf22`, branch `024-09-tie`, clone
  `/Users/f/fl/bench/2026-11-11/tie/clone`. It is `main`'s `16759d36`
  (with the day's first integration, `36924319`) merged into the branch
  without a conflict (`b205dc5e`), and one docs commit after it. The
  branch's own commits:
  - `9284b3d6` A2, lean only; `66b98455` A2, docs/levels.md only;
  - `472d7716` A1, harness and scripts; `ce1043cf` A1, messages and
    comments;
  - `27bad788` A4, lean only: the take in integers, with the `#guard`s
    that replace the double rule's (the one commit that changes expected
    values, in Lean; section 5.2);
  - `b2b459d3` A4, `java/stress/TakeCheck.java` and three lines of
    `level2.sh`;
  - `43cebf22` A4, docs/levels.md only (the take in integers).
  None changes `java/src`. No expected value of a Java test changed.
* **Gates on `43cebf22`** (section 2.5): `lake build` OK, no `sorry`, no
  `axiom`; BEFORE COMMIT OK; LEVEL 2 OK (full). Before the merge, on
  `472d7716`: `conformance.sh reclaim` and `evict` as whole sets, and
  `unlinkfuzz.sh` by itself.
* **Not done, for a later agent:**
  - `conformance.sh reclaim` and `evict` as whole sets, `level3.sh`,
    `level4.sh` and `unlinkfuzz.sh` on the merged head: the lock was
    held by another agent and the coordinator asked to end. Their three
    draining configurations ran one trace at a time (11 of 11 OK).
    `main` changed UnlinkFuzz.java (024-10), so `unlinkfuzz.sh` has not
    run with it.
  - `night.sh` as a whole (its new step ran by itself, before the
    merge).
  - The 60 more draining traces through the merged checker (4.8).
  - The questions of section 7: 1 and 2 are small pieces of work that
    wait for an answer.
  - 024-06's sections 1, 2.4, 3.3 and 4.4 are stale where this item
    answers them (`PhysStep` argued; P5 passed the gates; the take);
    not edited, the file is not this item's.
* **Other branches, local in the clone:** `024-09-p5-fault12`
  (`57c352c4`, worktree `/Users/f/fl/bench/2026-11-11/tie/wt-p5`), the
  test of section 2.3; `024-09-tie-a2` (the helper's, in
  `/Users/f/fl/bench/2026-11-11/tie/a2/clone`), cherry-picked.
* **Files changed by the branch, for the agents that touch the same
  ones** ("tree", 024-12):
  - `lean/`: new `SIS/Proof/PhysAssumptions.lean` and `Check/Live.lean`,
    one import line each in `SIS.lean` and `Check.lean`; `SIS/Bound.lean`
    and `SIS/BoundExample.lean` (the take only); `README.md`. No checker
    line changed.
  - `java/stress/A2A3Check2.java`: `shape=long`, `longShapeKey`.
  - `java/stress/TraceExport.java`: `long=2` (one line in `key()`) and
    the last stdout line "Dag counters: ..."; the trace format is
    unchanged. 024-12's `shape=long3` is the same key rule in the same
    method: a two-line conflict in `key()`, one property should remain.
  - `java/stress/conformance.sh`: the set `drain`; one line at the end
    of `reclaim()` and two at the end of `evict()`; a "Dag counters"
    line in every summary; the rule for configurations named *drain*.
  - `java/stress/level2.sh`: step 7 only (a second A2A3Check2 loop,
    `conformance.sh drain`, `TakeCheck check`) and its header.
  - New: `java/stress/unlinkfuzz.sh`, `java/stress/TakeCheck.java`.
    `java/night.sh`: one step and the header's list. `docs/levels.md`:
    the lines on level2.sh, night.sh, M47 and the take.
* **Files of this item:** `09-tie/cover.py`, `09-tie/more.sh`,
  `09-tie/cover-results.txt`. Outputs of the runs:
  `/Users/f/fl/bench/2026-11-11/tie/` (`a1/`, `a3/`, `gates/`).


## 9. Follow-up (Q1, Q2)

2026-11-11, 15:00 to 15:37 and the gates after. Written by the agent "fu"
for the coordinator (coord-1111). Frans answered section 7's questions 1
and 2 with yes; this is that work, on `main` after 024-12's tree model
(`ab1b9e42`).

**In short.** The 15 trusted statements that assumed `PhysRunOK` assume
`LiveAppend` in its place, and the three that do not assume `EvictRunOK`
(T1-L, CC, T2-L) also TREE after every transaction (`TreeRunOK`, new).
Every conclusion is word for word as before. The gates require A6 in every
trace and every A2A3Check2 run. The trusted statement lines: 15 removed, 18
added, and two new definitions of 5 lines of code (section 9.2).

### 9.1 The commits

Branch `024-09-followup` in `/Users/f/fl/bench/2026-11-11/fu/clone`, from
`main`'s `ab1b9e42`, four commits in Frans's name:

* `74edb208`: comments only. The Lean comments that named `Db.touchRange`
  as Java's touch (`Changes.touch` in Basic.lean, `touchOf` in
  Algorithm.lean, `StepOK`'s touch rules in Assumptions.lean, `pathOf` in
  Phys.lean) name `Db.touchPaths`, the paths of the step's own puts since
  024-07. The two that say "until 024-07 ... `Db.touchRange`"
  (ReclaimTheorems.lean, Tree/Read.lean) are history and stay. And
  `java/stress/unlinkfuzz.sh` gets mode 755.
* `d1ebe55f`: Q1, `PhysRunOK` out of the trusted statements (9.2); the
  proofs, `Check/Live.lean`, `lean/README.md`, docs/sis-model.md, section
  15.2.
* `886b7a4b`: TP15 of the tree model (024-12, section 6) is `LiveAppend`
  of `treeSpec` (`LiveAppendTree`, was `PhysRunOKTree`), proved
  (`liveAppendTree`, Check/TreeLive.lean, from `blive_append`), as 024-12's
  plan asks once `LiveAppend` takes `PhysRunOK`'s place. Its own commit, so
  that it can be left out.
* `74cb07b5`: Q2, the gates require A6 (9.4), and docs/levels.md, section
  5, says so in two lines.

### 9.2 The trusted diff (Q1)

The statement lines only, before (-) and after (+); a line that starts
with neither names the statement. Docstrings and file headers changed with
them to say the same (in the commit).

```diff
SIS/PhysTheorems.lean
 theorem T1_lazy (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
-    (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (k : Nat) (hk : k ≤ ts.length)
+    (hla : LiveAppend sp) (htree : TreeRunOK sp al ts)
+    (hj : al.stillDirty = javaTest sp) (k : Nat) (hk : k ≤ ts.length)
 theorem T2_lazy (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
-    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
+    (hok : RunOK sp al (ts.map (·.1))) (hla : LiveAppend sp)
+    (htree : TreeRunOK sp al (ts.map (·.1)))
 theorem CC_canonical (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
-    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
+    (hok : RunOK sp al (ts.map (·.1))) (hla : LiveAppend sp)
+    (htree : TreeRunOK sp al (ts.map (·.1)))

SIS/HandleTheorems.lean
 def TC_handles, T2_handles, TR_handles, TR_handles_restarts, TP_handles,
     RunPos_handles (six lines, each):
-    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
+    RunOK sp al (ts.map (·.1)) → LiveAppend sp →
 def Rule4_positions, Rule4Pos_handles (two lines, each):
-  ∀ ts : List T, RunOK sp al ts → PhysRunOK sp al ts → EvictRunOK sp al ts →
+  ∀ ts : List T, RunOK sp al ts → LiveAppend sp → EvictRunOK sp al ts →

SIS/HandleReclaimTheorems.lean
 def T9_handles:
-    RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
+    RunOK sp al (ts.map (·.1)) → LiveAppend sp →
 def T12_handles, RunPosCut_handles (two lines, each):
-    RunOK sp al (cs.map (·.1)) → PhysRunOK sp al (cs.map (·.1)) →
+    RunOK sp al (cs.map (·.1)) → LiveAppend sp →
 def Rule4PosCut_handles:
-  ∀ ts : List T, RunOK sp al ts → PhysRunOK sp al ts → EvictRunOK sp al ts →
+  ∀ ts : List T, RunOK sp al ts → LiveAppend sp → EvictRunOK sp al ts →

SIS/Phys.lean, new (LiveAppend moved here from SIS/Proof/PhysAssumptions.lean, unchanged)
+def LiveAppend (sp : Spec V T) : Prop :=
+  ∀ (h h' : History V) (y : NodeId), y ∈ sp.live (h ++ h') →
+    y ∈ sp.live h ∨ ∃ e ∈ h', y ∈ sp.ptrs e.val
+def TreeRunOK (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
+  ∀ j < ts.length, treeAt sp (run sp al (ts.take (j + 1))).P (j + 1)

SIS/Tree/Props.lean, TP15 (commit 886b7a4b)
-def PhysRunOKTree (p : Params) : Prop :=
-  ∀ (al : Algo BVal Tx) ts, Within p ts → PhysRunOK (treeSpec p) al ts
+def LiveAppendTree (p : Params) : Prop := LiveAppend (treeSpec p)
```

`PhysStep` and `PhysRunOK` stay in SIS/Phys.lean, assumed by no trusted
statement now; the proofs use them, and its comment says so. The size of
the change in the trusted files, comments included: `git diff --stat` 74
lines added, 36 removed, in 8 files (the four of `74edb208` among them).

### 9.3 Why each change keeps the meaning

* **The conclusions are the same, word for word**, in all 15: only
  hypotheses changed. So what each theorem promises when it applies is
  unchanged; the question is only when it applies.
* **The old hypothesis follows from the new ones, by a proof.** With
  `RunOK`, `LiveAppend` and `EvictRunOK`, `physRunOK_of_evict` gives
  `PhysRunOK`; with `RunOK`, `LiveAppend` and `TreeRunOK`,
  `physRunOK_of_tree` does (section 3, A2). Each proof gets `PhysRunOK`
  that way in its first line and then runs the old proof unchanged, or
  passes `LiveAppend` on to the theorem it uses (`runPos_handles`). So
  wherever the new statement's hypotheses hold, the old one applied too.
* **For BergDB nothing is lost, and an unchecked assumption is gone.**
  `LiveAppend` is a property of the function `live` alone, proved for
  `blive`, the `live` of both BergDB instances: a trace's (`bspec`,
  `bspec_liveAppend`) and the tree model's (`treeSpec`, `liveAppendTree`).
  TREE after every transaction is checked by C-A on every trace
  (`treeFailures`, R(0) included) and by A2A3Check2, and is part of
  `EvictRunOK` (TP16 for the tree). `PhysRunOK` was argued in a text
  (011-11, section 13.3) and checked on no Java trace. Now every
  hypothesis of the 15 is either proved for BergDB's instances or checked
  on every trace.
* **What a reader could see as narrower:** for a `Spec` that met
  `PhysRunOK` on some run but not `LiveAppend`, or not TREE (T1-L, CC and
  T2-L), the old statements applied and the new ones do not. No instance
  in the repository is such: BergDB's `blive` has `LiveAppend`, and the
  examples are checked by running (`physRunOKB`), not through the
  theorems.
* **`TreeRunOK` asks the least that `physRunOK_of_tree` needs:** TREE after
  transactions 1 to n, not R(0). `EvictRunOK` asks it with R(0), so the
  twelve theorems with handles need no TREE of their own.
* **Order:** `LiveAppend sp` stands where `PhysRunOK` stood, so the shape
  of each statement is as before.
* **TP15** asked the tree to meet `PhysRunOK`; what the theorems now need
  of a structure besides `RunOK` and TREE is `LiveAppend`, so TP15 asks
  that, and it is proved (`PhysRunOK` for the tree follows from TP14, TP15
  and TP16 by `physRunOK_of_evict`).
* `collectAxioms` (`#print axioms`) of the 15 proofs, of the bridge
  theorems and of `liveAppendTree`: propext, Classical.choice, Quot.sound
  (`blive_append`, `blive_sub`, `liveAppendTree`, `specOKTree`: propext and
  Quot.sound). No `sorry`, `axiom`, `admit` or `native_decide` in lean/.

### 9.4 Q2: A6 in the gates

* **`conformance.sh`:** the rule "the checker's count of adoptions below
  the old parent is 0" (`C-A adoptions below the old parent ...: 0 of`)
  was for the traces of a6 and e-a6 only; it is for every trace of every
  set now (small, medium, large, reclaim, evict, drain). A trace without
  the count fails too, as before.
* **`level2.sh`, step 7:** A2A3Check2's count of adoptions below the old
  parent ("... does not (bergdb 005-04), 0 (transactions 0)") must be 0 in
  the three configurations and in the seven draining ones; the line it
  printed with the count says "TREE, A6 and A-COPY OK".
* The model is not changed: it still assumes A6' (section 5.1; 024-06,
  question 7). The gates check more than the model assumes.
* Before 023-09 (fault 12's fix, 2026-11-10) these rules would have failed:
  the night of 2026-11-09 had 11 such transactions in `level2.sh`'s small
  set and 3 in `level4.sh`'s evict set; the medium and large sets had
  none.

### 9.5 Gates and results

On the branch's head `74cb07b5`, each run in its own hold of a slot, from
15:34 to 15:58:

| Gate                                       | Result                                      |
|---|---|
| `lake build` (lean/)                       | completed successfully (179 jobs, 67 s)     |
| `sorry`, `axiom`, `admit`, `native_decide` | 0 by grep (whole words)                     |
| `#print axioms`, 34 theorems               | all standard (9.3)                          |
| `test-traces/run.sh`                       | ok 41, FAIL 0                               |
| `before-commit.sh`                         | BEFORE COMMIT OK (86 s)                     |
| `level2.sh` full                           | LEVEL 2 OK (807 s)                          |
| `conformance.sh medium`, 9 traces          | CONFORMANCE OK (159 s)                      |
| `conformance.sh reclaim`, 30 traces        | CONFORMANCE OK (158 s); C-CUT 0 of 326      |
| `conformance.sh evict`, 51 traces          | CONFORMANCE OK (65 s); C-P, C-H 0 of 11,965 |

* `small` (70 traces) and `drain` (50) ran in `level2.sh` full, 10 seeds
  each: TRACECHECK OK in all; in step 7 the ten A2A3Check2
  configurations, 42,500 transactions, "TREE, A6 and A-COPY OK", and
  TAKECHECK OK; treeconf small, drain and reclaim OK (step 8).
* **Adoptions below the old parent: 0 everywhere**: in each of the five
  sets' summaries (210 traces) and in all ten A2A3Check2 outputs.
* **The new rules can fail:** the checker's output for
  `test-traces/adopt.trace` ("1 of 3 transactions") fails the
  conformance rule, and A2A3Check2's output on P5's head (section 2.3;
  `tie/a1/tune/a2a3-p5-10.txt`, "4 (transactions 4)") fails `level2.sh`'s.
* The Lean gates ran on the tree of `74cb07b5` before the four commits
  were made from it; the intermediate commits were not built alone.
  `d1ebe55f` without `886b7a4b` builds by reading (TP15 still names
  `PhysRunOK`, which stays).
* Outputs: `/Users/f/fl/bench/2026-11-11/fu/gates/` (`chain-1.txt`,
  `lean-gates-1.txt`, and one file a run); the scripts' own in the clone's
  `java/build/level2/` and `java/build/traces/`.

### 9.6 What remains

* **`conformance.sh large`** (12 traces, 4.8 hours on 2026-11-09) did not
  run: it is started by hand with `night.sh large`. Its traces had no
  adoption below the old parent even before 023-09.
* The checker's Bool functions against the Lean Props (section 3, "Not
  theorems"): unchanged by this; `LiveAppend` was never a check.
* `night.sh` as a whole, `level3.sh` and `level4.sh` on the head: not run
  (scripts and Lean only; `level4.sh` runs `conformance.sh evict`, which
  ran here by itself).
* 024-12's item (12-tree-model.md, section 6 and its next steps) still
  names `PhysRunOKTree`; it is that item's file.

### 9.7 State

2026-11-11, 15:59.

* **Done:** Q1, Q2, the comments that named `Db.touchRange`, the mode of
  `unlinkfuzz.sh`, and TP15: four commits on `024-09-followup`, head
  `74cb07b5`, clone `/Users/f/fl/bench/2026-11-11/fu/clone`. Every gate of
  9.5 passed on that head. Not on `main`: the coordinator lands it (a
  fast-forward of `main`'s `ab1b9e42`, or a merge if `main` moved; the
  files it touches are listed in 9.1).
* **Not done:** 9.6 (`conformance.sh large`, `level3.sh`, `level4.sh`,
  `night.sh`).
* **How to continue:** a missing gate runs with
  `sh /Users/f/fl/bench/2026-11-11/fu/gates/chain.sh NAME` (NAME:
  before-commit, level2, conf-medium, conf-reclaim, conf-evict), the Lean
  gates with `gates/lean-gates.sh`.

2026-11-13. Status set after the release (coord-1113).
