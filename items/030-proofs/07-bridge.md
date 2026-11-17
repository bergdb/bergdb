# 030-07. The bridge from the contract to the abstract model

Created 2026-11-17 by Frans Lundberg. Status: open.

Step 4 of 030-04, its first part: recovery, restarts, lazy reading, eviction
and reclaim's cut proved for BergDB's key tree from the writer's contract, by
the abstract model's existing proofs (`lean/SIS`, 006-26, sections 2.1 and
3.1 to 3.3). The old proofs are not redone; the contract is connected to
them. Written by the bridge's agent of coord-1117 (the night of 17 to 18
November, brief s4a), "I" below. The Lean is in `lean/contract/`: the
statements in `Contract/Bridge.lean` and `Contract/BridgeTop.lean` (the
clauses), `Contract/BridgeTheorems.lean` and `Contract/BridgeFull.lean`
(the theorems).


# 1. The result

Kept current; the Log has the times.

- **Proved** (Lean theorems, the standard axioms only), for any history that
  meets the writer's contract and the bridge's clauses (`MeetsFull`, section
  3; every clause is about Java's tree, its top and the transaction's change,
  none in the abstract model's words):
  - the abstract model's assumptions hold for BergDB's key tree:
    `RunOK` (`bridge_runOK`; TP14 of the old line, 006-26, section 5.2), TREE
    after every transaction, and with A6' and A-COPY `EvictRunOK`
    (`bridge_treeRunOK`, `bridge_evictRunOK`; TP16);
  - the model's structure is the tree, klong for entry (`bridge_rep`);
  - **recovery, T1:** after any run, and after a crash that keeps a prefix
    of whole records, startup from the stream gives back every node of the
    tree with all its entries, and D (`bridge_recovery`, `bridge_crash`);
  - **restart invariance, T2:** restarts after any transactions change no
    record (`bridge_restart`);
  - **lazy reading:** after a startup that reads nodes at first touch, a
    read at any time gives the structure, and the records are those of the
    run without restarts (`bridge_lazy_read`, `bridge_lazy_restart`);
  - **eviction with handles:** under any reads and evictions between
    transactions, and restarts, the writer appends the same records and
    leaves the same D; a read at any time gives the structure; every object
    that is not pinned may be evicted; Java's startup by position is the
    startup by node id (`bridge_handles_records`, `bridge_handles_read`,
    `bridge_handles_evict`, `bridge_handles_pos`);
  - **reclaim's cut:** after a safe cut, startup from the cut stream gives
    every lookup from the first available time on, and the records stay
    those of the run without cuts, with eviction too (`bridge_cut_recover`,
    `bridge_cut_restart`, `bridge_cut_handles`). "A safe cut" (`CutOK`) stays
    a premise: that BergDB's waits give one is tested (006-26, section 3.3).
- **What the model assumes of the top is proved, not assumed.** With
  030-08's top in the contract (`TopStep`) and one more computed clause
  (TB), R1 to R4 and the dead top nodes are a theorem
  (`MeetsBridgeTop.meetsBridge`). So are the model's touch rules, A6' and
  A-COPY, from the same clauses said of the tree (`MeetsFull.meetsBridge`,
  `MeetsFull.meetsEvict`).
- **Java's readers too.** A history that meets `MeetsFull` meets 030-08's
  `MeetsTop` (`MeetsFull.meetsTop`), so the reads' theorems with Java's top
  search hold for the same history.
- **D is state** (030-06, finding 5): the frame holds with the model's D in
  place of the contract's free D (`frame_modelD`).
- **Not vacuous.** `Contract/BridgeExample3.lean`: 030-06's three
  transactions, with a top node made, its skip pointer and a delete by a
  bitmap, meet every clause (`meetsFull`). `Contract/BridgeExample.lean`:
  the empty tree and one put meet the clauses in the model's words.
- **Tested.** Every clause holds for every traced transaction of the level 2
  sets and the reclaim set: 195 traces, 29,735 transactions, 335,902 nodes
  made, 831,317 entries, 7,368 touched nodes; no failure
  (`lean/contract/bridge-check.sh small drain reclaim`). What the checker
  computes for a whole trace is proved to give `MeetsFull`
  (`fullHistoryOk_meets`). Faults made by hand in a trace fail it
  (`lean/contract/bridge-faults.sh`).
- **Not proved, and stays tested:** that Java's writer meets the clauses
  (the checks above); that Java's records are the model's (`tracecheck`, on
  the same instance of the model, section 2, decision 2); the cut's safety.
- **Open:** bounded startup's premises (section 6); the State note.

Proved means a Lean theorem with no premise but the ones named. A history
"meets the clauses" by assumption; nothing here proves that a writer does.


# 2. Decisions

1. **The abstract model is reached by a Lake dependency on the old package**
   (`lean/contract/lakefile.toml`: `sis`, path `..`), not by copying.
   Reason: the theorems wanted (T1, T2, lazy reading, handles, the cut) with
   their proofs are 99 files and 45,800 lines by import closure; a copy
   would be a second proof base to keep in step. The toolchains are the same
   (v4.34.1), the two libraries build together with Mathlib with no name
   clash, and the first build of the old files from the new package takes
   about 80 seconds. No file of `SIS/Tree` with proofs is in the closure: the
   bridge imports the abstract model's theorems and `lean/Check`'s
   `Trace.lean`, `Live.lean` and `R4.lean` (the trace checker's instance and
   proved facts about it), and of `SIS/Tree` only `Val.lean`, the entry
   values, through them.
2. **The model's instance is the trace checker's own** (`SIS.Check.bspec`,
   `lean/Check/Trace.lean`): entries `BVal`, pointers `bptrs`, live children
   `blive`, a virtual root, the transactions 1, 2, ..., each with its change
   as given. Reason: `tracecheck` tests on Java's traces that the model's
   step, for this instance, writes Java's records and leaves Java's D; the
   bridge proves the model's assumptions for the same instance, so the two
   meet with no translation between them.
3. **A history carries each transaction's change in the model's terms**
   (`BTx.c`: the nodes made, the entries added, the touch; the trace's NEW,
   ADD and TOUCH lines), and clause K says that the entries added are those
   of the klongs added. Reason: the contract's tree is a function from ids,
   so the nodes made cannot be listed from it; and the change given is then
   the trace's, line for line.
4. **The clauses about key nodes and values are in the contract's words**
   (on the tree, computed: N, K, F4, W, A4, A2, A3, A5). The top's were
   first one premise in the model's words (`TopOK`, as the brief said, until
   030-08 landed); since 16:15 they are 030-08's own (`TopStep`) and clause
   TB, and `TopOK` is derived. The touch, A6' and A-COPY were first in the
   model's words (`TouchOK`, `MeetsEvict`), each computed by a function
   proved to give it; since 16:45 they are said of the tree and its top
   (`touchOk`, `adoptOk`, `copyOk`) and the model's are derived. The
   statements in the model's words stay, as the step between: `MeetsFull`
   gives `MeetsBridgeTop`, which gives `MeetsBridge`; the theorems are
   proved from `MeetsBridge` and `MeetsEvict`.
5. **TREE is 030-08's clause** (`TreeOk`, no node reached twice), as the
   coordinator said at 15:45, and "reached" in A2, A3 and A5 is 030-08's
   `reach`: one definition of the walk for the contract. The model's TREE
   (`treeAt`) is proved from it.
6. **W5 is added to the rules of a node's bitmaps** (restated; section 3.1).
   Shown in Lean before it was added: klongs that meet W1 to W4 and whose
   entries have other live children than the klongs (`w4_not_enough`).
7. **A-COPY is a sufficient form** (`copyOk`, and `copyB` in the model's
   words): of the nodes of the writer's paths it takes those that the
   change itself changes, touches or leaves unreached, not their ancestors.
   Reason: the model's own definition walks the subtree of every reachable
   node, which is too slow to run on a trace; the form is proved to give
   A-COPY, and every traced transaction meets it. One more case came from
   030-06's example, which failed the first form: a transaction that makes
   a top node may name the space root before it (the pointee of the super
   root that it replaces).
8. **R4 is checked by the trace checker's chain of skip pointers**
   (`r4Fast`, `lean/Check/R4.lean`, proved there). Reason: the model's
   `topClosure` walks every path between top nodes and is exponential in
   their number (three small traces ran for minutes).


# 3. The clauses

For the transaction at time i, from the tree s to the tree s', with the
change c. `Contract/Bridge.lean` and `Contract/BridgeTop.lean` have the Lean
beside the English.

## 3.1 About key nodes and values, in the contract's words

- **The start.** Java's primordial structure: the root, one key node (a
  segment leaf with one time klong of time 0), one top node that names it.
- **N.** The nodes made have distinct ids, none a node of s. A key node made
  is an index node with its level; a value made is a data node on level 0;
  a node made that is no node of s' is a top node. Every node of s' that is
  no node of s is made by c.
- **K, the map.** The entries added to a node are the entries of the klongs
  it got: a key klong is the entry `K c y`; a bitmap is the entry `D` with
  the compare values of its new bits; a time klong is no entry, and gives
  the entries after it their time (027-02, section 1). 030-06's "the klongs
  as entries".
- **F4.** A key node of s is unchanged, or got a time klong of i and then at
  least one klong, none a time klong; a key node made has a time klong of i
  and then no time klong. So every klong added or made has the time i
  (030-06, finding 4).
- **W.** The klongs of every key node of D are well formed (W1 to W4), and
  W5: for every compare value of a new bit of a bitmap, the bitmap deletes
  every key klong before it of that compare value. W4 (030-05) asks this of
  the klongs before the new bit only; the map needs W5, which the old
  model's `klongsWf` had and `treecheck` tests.
- **A4.** Every key klong of a key node of D, live or dead, names a node of
  s' on a lower level.
- **A2.** An entry is added only to a node that s' reaches at time i.
- **A3.** Every node made, key node or value, is reached by s' at time i.
- **A5.** Every node that s' reaches at time i was reached by s at time
  i - 1 or is made: no node comes back.
- **TREE** (030-08). The walk from the space root reaches no node twice.

## 3.2 The top

- **030-08's clauses** (`TopStart`, `TopStep`): at most one top node made a
  transaction, the old ones fixed, the skip pointers as
  `TopDs.newSuperRoot` makes them; the tree's space roots are the top
  nodes' root pointers.
- **TB.** No node made has the root's id or a top node's; a node of the tree
  made is below the top nodes' level. If no top node is made, every node
  made and every entry added is a node's of the tree. If the top node z is
  made, the change makes exactly one node that is no node of the tree, z, on
  a level above every earlier top node's and below the root's; z's entries
  are its root pointer and then its skip pointers; the root's entries are
  the one for z.
- From these, proved: the model's `TopOK` (R1 to R4 and the dead top nodes,
  `VirtStep`; for the root and the top nodes the model's assumptions on a
  transaction; the link: at time i the root's one live child is a top node
  whose one live child is the space root of s').

## 3.3 The touch, A6' and A-COPY

Said of the tree and its top (`Contract/BridgeTop.lean`). "Below x" is the
walk from x; the super root is the last top node.

- **The touch** (`touchOk`), before the transaction: a touched node is the
  super root or a key node that the tree reaches; if any node is touched,
  the super root is; every key node reached with a touched node below it is
  touched.
- **A6'** (`adoptOk`), after the transaction: for every key node x reached
  and every key klong of x, live or dead, its pointee is a live pointee of
  x, or a value, or not reached, or below x.
- **A-COPY** (`copyOk`): a key entry added, or the root pointer of a top
  node made, names a node made, a node of the writer's paths (reached
  before, and given an entry, touched or left unreached), the pointee of a
  key klong of such a node, or the space root before when a top node is
  made; a skip pointer of a top node made names the super root before it or
  the pointee of one of its skip pointers.

From these, proved: the model's `TouchOK`, `adoptAt` and `CopyStep`
(`touch_of`, `adopt_of`, `copy_of`).


# 4. What the proof is

About 5,100 lines in `Contract/Proof/Bridge*.lean`:

- `BridgeMap.lean`: the map keeps the live children
  (`mem_blive_entriesOf`): for well-formed klongs with W5, the model's live
  children of the entries are the pointees of the live klongs.
- `BridgeInv.lean`: after every transaction the model's structure holds the
  tree, every klong has a time up to now, every key node is well formed,
  every key klong names a node on a lower level (`BInv`, `binv_step`).
- `BridgeReach.lean`: what the model reaches at the latest time is the root,
  the top node, and what the tree reaches (`mem_reach_model`, `reach3`).
- `BridgeStep.lean`: `StepOK` for every transaction, `SpecOK` for the start,
  the model's run has the history's structures, `RunOK`.
- `BridgeTree.lean`: the model's TREE from 030-08's (`BInv.treeAt`).
- `BridgeTop.lean`: the model's `TopOK` from 030-08's top and TB
  (`top_step`), the longest part, about 1,000 lines.
- `BridgeWords.lean`: the model's touch rules, A6' and A-COPY from the
  clauses said of the tree; below a node of the tree, the model reaches what
  the walk reaches (`walk_reachFrom`, `reachFrom_walk`).
- `BridgeDirty.lean`: D as state (`frame_modelD`).
- `BridgeModel.lean`, `BridgeHistory.lean`: the computed clauses in the
  model's words give the clauses; the checker's verdict on a trace gives
  `MeetsFull` (`fullHistoryOk_meets`), and in the model's words
  `MeetsBridge` and `MeetsEvict` (`bridgeHistoryOk_meets`).

The old proofs are used as they stand: the theorems of
`lean/SIS/Theorems.lean`, `PhysTheorems.lean`, `HandleTheorems.lean`,
`ReclaimTheorems.lean` and `HandleReclaimTheorems.lean` are applied to the
model's instance of the history.


# 5. The check

`lake exe bridgecheck [--model] TRACE...` (`BridgeCheck.lean`), run by
`lean/contract/bridge-check.sh [SET ...]`:

- for every traced transaction alone, on Java's tree and top before and
  after it and its NEW, ADD and TOUCH lines: N, K, F4 with W and A4
  (reported as L), A2, A3, A5, TREE, TB with 030-08's step of the top,
  TOUCH, A6', COPY; for TX 0 the start with its top;
- then the verdict on the whole trace as one value (`fullHistoryOk`, with
  the writer's contract for every transaction), the one that the theorem
  `fullHistoryOk_meets` speaks of;
- with `--model` also the clauses in the model's words on the model's
  structure (`topOkB`, `touchB`, `adoptB`, `copyB`) and their verdict
  (`bridgeHistoryOk`).

The computed clauses are the definitions of `Bridge.lean` and
`BridgeTop.lean`, run on the checker's heap as they stand; `Made`, 030-08's
`TopStep` and TREE are computed by functions proved to give them
(`madeCheck_sound`, `topStepB_sound`, `treeOkB_sound`). The three sets take
about two minutes, with `--model` about eight. `bridge-faults.sh`: faults
made by hand (an entry with another compare value, a delete entry with
another one, a value without its NEW line, a key node on level 0, a skip
pointer left out, another root pointer, a node left out of a TOUCH line,
another primordial root pointer) each fail the checker.

Gaps: how the checker builds Java's tree and top from a trace's lines is
030-09's and 030-08's (`applyTx`, `applyTop`). The model's levels of the top
nodes come from the NEW lines (clause TB reads them from the model's
structure).


# 6. Bounded startup (030-04, step 4; the brief's item 5)

`Contract/BridgeBound.lean`.

- T3 (the startup distance bounds the startup section) and T4's record
  assume nothing of the structure: they hold as they stand.
- T4's debt (`bridge_debt`): every node of D reaches, through pointers live
  or dead, a node changed or touched in the last few startup sections. It
  was reduced to `RunOK`; for the key tree it is now proved from the
  clauses.
- The live height (`bridge_liveHeight`): if the space root's level is at
  most K after every transaction, the model's root has live height at most
  K + 2. This is the premise H of T4's count and of `bounded_startup`, as a
  bound by the level's number, not by the tree's height.
- Open, and not reached from the contract as it is: the fit of D in a
  record; Hp and Q (not known to stay bounded as the database ages, 006-26,
  section 5.1); what a transaction removes (K), the siblings its merges
  read (B), the size of its change (A), a top node's pointers (Pt). The
  contract left the fill and the balance out (030-05, section 3), and these
  are costs of the writer's steps.


# State

2026-11-17: see the Log's last lines for the last gated commit. The brief's
work list is done (items 1 to 5). Open, in the order I would take them:

1. The checker as a step of `level2.sh` (with 030-05's note on `check.sh`:
   Lake fetches Mathlib to resolve the package).
2. Java's own check (030-09's `TransCheck`) could take the bridge's clauses
   that are local to the changed nodes: F4, W5, A4, TB.
3. The top nodes' levels in the contract's top (030-08's `TopNode` has no
   level; TB reads the model's), so that TB speaks of the tree and its top
   alone.
4. Bounded startup's open premises (section 6).
5. The old proofs of the tree (`lean/SIS/Tree`) are not used by the bridge;
   030-04's step 4 says to delete them when the new package covers what
   they claimed. Not done here: it is the coordinator's and Frans's call.

To build and check: `cd lean/contract && lake build`; the traces as 030-05's
State note says (`java/build.sh`; `cd lean && lake build treecheck`;
`java/stress/treeconf.sh small`, `drain`, `reclaim`);
`lean/contract/check.sh`; `lean/contract/bridge-check.sh small drain
reclaim`; the gate `lean/contract/gate.sh BASE`.


# Log

2026-11-17, 15:09. Started, on the branch `030-07-bridge` from fc183148.
15:32 the statements and the checker; the clauses pass on the traces.
15:45 merged main 9a6692cf (030-08's TREE, 030-09's trace checks).
15:52 `RunOK`, T1 and T2 for the tree, proved.
GATED 7acde0f3: `RunOK`, T1 (recovery, crash) and T2 (restarts) for the key tree from
`MeetsBridge`; the tree's clauses pass on 195 traces; `gate.sh 9a6692cf` GATE OK.
15:56 the model's TREE from 030-08's `TreeOk`; `EvictRunOK`; lazy reading, the handles and the
cut for the tree, proved.
GATED 44734190: lazy reading, eviction with handles and reclaim's cut for the key tree from
`MeetsBridge` and `MeetsEvict`; TREE is 030-08's clause; `gate.sh 9a6692cf` GATE OK.
16:10 the clauses in the model's words computed (`topOkB`, `touchB`, `adoptB`, `copyB`, each
proved to give its clause) and passing on the 195 traces; D as state (`frame_modelD`); T4's debt
and the live height.
GATED 541d2036: every clause of `MeetsBridge` and `MeetsEvict` checked on the level 2 and reclaim
traces by `bridgecheck` (195 traces, 29,735 transactions, no failure); `frame_modelD`,
`bridge_debt`, `bridge_liveHeight`; `gate.sh 9a6692cf` GATE OK.
16:15 merged main 79678f4e (030-08's top, 030-09's Java check). The checker's verdict on a whole
trace (`bridgeHistoryOk_meets`), the checker's own test, `w4_not_enough`.
16:30 the top's premise from 030-08's top and clause TB (`MeetsBridgeTop.meetsBridge`); the
three-transaction example (`BridgeExample3`).
16:46 the touch, A6' and A-COPY in the contract's words, the model's proved from them
(`MeetsFull.meetsBridge`, `MeetsFull.meetsEvict`); the checker's verdict gives `MeetsFull`
(`fullHistoryOk_meets`); Example3 meets `MeetsFull`; `MeetsFull.meetsTop`. The gate's base is
863b69cb, main as merged (79678f4e and the coordinator's 006-30 line).
GATED 50feb1f2: `MeetsFull`, every clause in the contract's words (the top by 030-08's
`TopStep` and TB; the touch, A6', A-COPY said of the tree), gives `MeetsBridge` and `MeetsEvict`,
so T1, T2, lazy reading, the handles and the cut; `fullHistoryOk_meets`; Example3 meets it;
195 traces, 29,735 transactions pass `bridge-check.sh`, `check.sh` CONTRACT OK;
`gate.sh 863b69cb` GATE OK (67 theorems).
16:58 `bridgecheck --model` on the 195 traces: the clauses in the model's words pass too (TOP,
TOUCH, A6', COPY: 0 failures), with both verdicts. Merged main 0b316ceb (no change to the tree).
