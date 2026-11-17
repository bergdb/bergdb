# 030-07. The bridge from the contract to the abstract model

Created 2026-11-17 by Frans Lundberg. Status: open.

Step 4 of 030-04, its first part: recovery, restarts, lazy reading, eviction
and reclaim's cut proved for BergDB's key tree from the writer's contract, by
the abstract model's existing proofs (`lean/SIS`, 006-26, sections 2.1 and
3.1 to 3.3). The old proofs are not redone; the contract is connected to
them. Written by the bridge's agent of coord-1117 (the night of 17 to 18
November, brief s4a), "I" below. The Lean is in `lean/contract/`: the
statements in `Contract/Bridge.lean` and `Contract/BridgeTheorems.lean`.


# 1. The result

Kept current; the Log has the times.

- **Proved** (Lean theorems, no premise but the ones named, the standard
  axioms only), for any history that meets the writer's contract and the
  bridge's clauses (`MeetsBridge`, section 3):
  - the abstract model's assumptions on a run hold for BergDB's key tree
    (`bridge_runOK`: `RunOK`, which is TP14 of the old line, 006-26, 5.2);
  - the model's structure is the tree, klong for entry (`bridge_rep`);
  - recovery, T1: after any run, and after a crash that keeps a prefix of
    whole records, startup from the stream gives back every node of the tree
    with all its entries, and D (`bridge_recovery`, `bridge_crash`);
  - restart invariance, T2: restarts after any transactions change no record
    (`bridge_restart`).
- **Not vacuous:** `Contract/BridgeExample.lean` is a history (the empty tree
  and one put, with the model's changes) that meets `MeetsBridge`.
- **Tested:** the bridge's clauses in the contract's words hold for every
  traced transaction of the level 2 sets and the reclaim set: 195 traces,
  29,735 transactions, 335,902 nodes made, 831,317 entries; no failure
  (`lean/contract/bridge-check.sh small drain reclaim`).
- **Open:** see the State note.


# 2. Decisions

1. **The abstract model is reached by a Lake dependency on the old package**
   (`lean/contract/lakefile.toml`: `sis`, path `..`), not by copying.
   Reason: the theorems wanted (T1, T2, lazy reading, handles, the cut) with
   their proofs are 99 files and 45,800 lines by import closure; a copy
   would be a second proof base to keep in step. The toolchains are the same
   (v4.34.1), the two libraries build together with Mathlib with no name
   clash, and the first build of the old files from the new package takes
   about 80 seconds. No file of `SIS/Tree` with proofs is in the closure: the
   bridge imports `SIS.Theorems`, `SIS.Phys`, `SIS.Assumptions`,
   `Check.Trace` and `Check.Live` (the trace checker's instance and the two
   facts about its `blive`), and of `SIS/Tree` only `Val.lean`, the entry
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
   (on the tree, computed: N, K, F4, W, A4, A2, A3, A5); **the ones about
   the root and the top nodes are in the model's words**, on the model's
   structure, as one premise named for 030-08 (`TopOK`); so are the touch
   rules (`TouchOK`). Reason: the contract's tree has no top nodes until
   030-08 adds them, and the brief says to take the top as a premise.
5. **TREE is 030-08's clause** (`TreeOk`, no node reached twice), as the
   coordinator said at 15:45, and "reached" in A2, A3 and A5 is 030-08's
   `reach`: one definition of the walk for the contract.


# 3. The clauses

For the transaction at time i, from the tree s to the tree s', with the
change c (`Contract/Bridge.lean`, sections 3.1 to 3.6, has the Lean beside
the English):

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
  every key klong before it of that compare value. Restated: W4 (030-05)
  asks this of the klongs before the new bit only; the map needs W5, which
  the old model's `klongsWf` had and `treecheck` tests.
- **A4.** Every key klong of a key node of D, live or dead, names a node of
  s' on a lower level.
- **A2.** An entry is added only to a node that s' reaches at time i.
- **A3.** Every node made, key node or value, is reached by s' at time i.
- **A5.** Every node that s' reaches at time i was reached by s at time
  i - 1 or is made: no node comes back.
- **The top (for 030-08), `TopOK`.** R1 to R4 and the dead top nodes
  (`VirtStep`); for the root and the top nodes, the model's assumptions on a
  transaction; and the link: at time i the root's one live child is a top
  node whose one live child is the space root of s'.
- **The touch, `TouchOK`.** The model's three rules for the nodes that a step
  of reclaim touches.


# 4. What the proof is

About 1,900 lines in `Contract/Proof/Bridge*.lean`:

- `BridgeMap.lean`: the map keeps the live children
  (`mem_blive_entriesOf`): for well-formed klongs with W5, the model's live
  children of the entries are the pointees of the live klongs.
- `BridgeInv.lean`: after every transaction the model's structure holds the
  tree, every klong has a time up to now, every key node is well formed,
  every key klong names a node on a lower level (`BInv`, `binv_step`).
- `BridgeReach.lean`: what the model reaches at the latest time is the root,
  the top node, and what the tree reaches (`mem_reach_model`,
  `model_reach_cases`).
- `BridgeStep.lean`: `StepOK` for every transaction, `SpecOK` for the start,
  the model's run has the history's structures, `RunOK`.


# State

2026-11-17, 15:52. GATED once (the Log). Next, in this order:

1. `MeetsEvict`: the model's TREE (`treeAt`) from 030-08's `TreeOk`, then
   `TreeRunOK` and `EvictRunOK`, and with them lazy reading, the handles and
   the cut's theorems for the tree.
2. The clauses in the model's words (`TopOK`, `TouchOK`, A6', A-COPY)
   computed and checked on the traces by this package's checker.
3. A longer example (030-06's three transactions, with a top node made).
4. D as state (030-06, finding 5).
5. What of bounded startup follows the same way.

To build and check: `cd lean/contract && lake build`; the traces as 030-05's
State note says; `lean/contract/check.sh`, `lean/contract/bridge-check.sh
small drain reclaim`; the gate `lean/contract/gate.sh 9a6692cf`.


# Log

2026-11-17, 15:09. Started, on the branch `030-07-bridge` from fc183148.
15:32 the statements and the checker; the clauses pass on the traces.
15:45 merged main 9a6692cf (030-08's TREE, 030-09's trace checks).
15:52 `RunOK`, T1 and T2 for the tree, proved.
