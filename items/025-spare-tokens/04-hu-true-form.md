# 025-04. The true form of hU: the plan

Created 2026-11-15 by Frans Lundberg. Status: steps 1 to 5 done
2026-11-15, 09:50 (route (b)): the joint route's top theorem without `hU`,
`invGetScanOK_merges_noU`; section 9. Step 6 open.

`hU` (`UpUnlinkTreeOK`), a premise of the key tree's top theorem, is false
as stated (`upUnlinkTreeOK_false`, SIS/Tree/PremisesFalse.lean): it speaks
of every writer state with `PutInv` and the upward loop's end, and those
carry none of the writer's books. Its true form, at the states that runs
reach, is open: it needs an invariant on the nodes a transaction leaves
out (024-22, section 11.1). This entry is the plan for it.

Frans, 2026-11-15, 08:33, to 006-25, section 7, decision 1 (a planning
agent for that invariant before more provers): "as you recommend. [...]
The planning for hU, run it with Fable 5.2 High."


## 1. In short

Written 2026-11-15 by the planning agent of coord-1114. Nothing is proved
here; sections 4 and 5 say what was tested on runs.

- **`hU` can go the way of `hHL` and `hCoU`,** the two sister premises
  that left the top theorem last night: out, with no statement change.
  The recommended route is (b) of section 4, a change of the consumer.
  The invariant on left-out nodes is then not needed.
- **What `hU` says.** A delete that empties its leaf climbs: the emptied
  nodes below the first node that keeps a live klong (the stop node) are
  taken back or set back to their versions before the transaction. `hU`
  says that the writer's tree is still a tree at that moment, before the
  stop node gets its bitmap. The nodes set back are P's again, and may
  name nodes of P that the transaction has linked elsewhere. That is why
  no proof was found.
- **Where it is used.** In one case only: the stop node has no room for
  the bitmap, so it is split. The split's lemmas ask for a tree at the
  split's start.
- **Why it is not needed.** The split never reads the stop node's klong
  to the emptied nodes. It reads three things of the stop node: its first
  time, its leaf flag and its version before the transaction. The klongs
  it copies come from a last version that the caller has made, with the
  bitmap applied. So the split runs the same, to the same end state, from
  a state where the stop node no longer names the emptied nodes. The tree
  of that state is the tree at the delete's start without the emptied
  nodes: a tree, by what is proved already.
- **Tested on runs** (section 5): at all 173 loop ends with a full stop
  node, of 2,529 loop ends, the split from the changed state gave the
  same end state; and at all 408 of 1,868 with Java's theta. 0 failures.
- **Size:** 5 steps of 1.5 to 3 hours, 700 to 1,200 lines, 8 to 13
  prover hours. It lands `invGetScanOK_merges_joint7`: the current top
  theorem, joint6, without `hU`. An addition.
- **The invariant** (route (a)) has a candidate that held on runs, but it
  is a walk over the whole writer, 5,000 to 9,000 lines. It stays in
  reserve. Route (c), a checked copy, needs a statement change and proves
  nothing.
- **After the route** no premise of the top theorem is known to be false.
  `hMSF` and `hCoF` (the tree fits the fuel after a merge and after root
  collapse) are likely false as stated (cost2); they are the next doubt
  on whether the theorem says anything.


## 2. What hU says and where it is used

### 2.1 The upward delete, in the model

`deleteUpward` (SIS/Tree/Exec.lean) deletes a key in its segment leaf. If
the leaf keeps a live klong, it gets a bitmap. If not:

- **The climb.** From the leaf up the key access path, to the first node
  that keeps a live klong after the delete: the stop node, at depth
  `stop`. The nodes below it on the path are the chain, X (stop + 1) to
  X depth.
- **The loop**, over the chain, lowest first. A chain node that the
  transaction made is taken back (`takeBack`): the klongs of the
  transaction in its parent that name it name the node it replaced (its
  made-for id), and its id is no node of the transaction. A chain node of
  before the transaction is unlinked (`unlink`): it loses its klongs of
  the transaction, so it is its node in P again.
- **The stop node's step.** The stop node gets a bitmap that deletes its
  klong to the chain (`appendDeleteKlong`). With room, the bitmap is
  added. Without room, the node is split (`handleFull`), from its last
  version with the bitmap applied; the split may cascade upward.

With the merges on, no node that a delete empties is below an inner
node (proved, `stopLeaf_of_liveCounts`). So the stop node is a segment
leaf, and each chain node is the root, and the only node, of its segment
tree.

### 2.2 The premise

`UpUnlinkTreeOK c base` (SIS/Tree/DelStepsUnlinkTree.lean), the top
theorem's `hU`: for every writer state w with the writer's invariant
between steps (`PutInv`: the writer's tree is a tree, klongs well formed,
ids below the next id), every chain in it, and every state w2 that the
loop can leave (`UpLoopEnd`: only the chain and the stop node changed;
each chain node taken back or unlinked), the writer's tree at w2 is a
tree (`TreeOK`: nothing names the root, and every reached node has one
holder).

At w2 the stop node still names the chain's top, or the node the top
replaced. Below that klong hangs what the loop brought back: nodes of P,
as P has them.

### 2.3 The use sites

The current top theorem is `invGetScanOK_merges_joint6`
(SIS/Tree/CollapseCommuteTop.lean). It passes `hU` to four lemmas of
HeightsFillHolder.lean, one for each thing it proves about a delete:

- `delStepsOKJ_of_open`: what get and scan read after the delete;
- `delStepsJ2OKJ_of_openR`: the take-back's facts, in the run's
  induction;
- `delStepsQdLJ_of_openR`: the tree, the invariant and the ranges, in the
  joint induction (`jointHtJ_reachedJ`);
- `delStepsJ2OKS_of_openR`: the take-back's facts, in the joint
  induction.

Each of the four passes `hU` on, through one lemma per case
(`delStepsCaseOK_emptyCascLHGJ` and three like it), to one of two
lemmas. Only these two apply `hU` to a state:

- `upCascOKHGJ_of` proves the reading's obligation `UpCascOKHGJ`: the
  stop node's bitmap into a full node keeps the delete's invariant
  (`DelInv`). It uses `hU` when the stop node is below the space root
  (`writerWP_upCasc_below_delT`). At the space root it does not
  (`writerWP_upCasc_root_del`).
- `upCascJ2OKHGJ_of` proves the take-back's obligation `UpCascJ2OKHG`:
  the same step keeps the take-back's node facts (`TakeJ2`: a node with a
  klong of the transaction is reached; klongs of before the transaction
  name ids below the transaction's first id; and four more). It uses
  `hU` at the space root (`writerWP_upCasc_root_j2`) and below it
  (`writerWP_upCasc_below_j2T`).

So `hU` is used at three lemma calls, all in one case: the stop node is
full. On runs that case is 173 of 2,529 loop ends. With room the tree
after the bitmap comes from the tree at the delete's start, and `hU` is
not used.

Older lemmas use `hU` too (`upCascOKHG_of`, `upCascJ2OKHG_of` in
DelStepsGh.lean, with `hHL`), for the older top theorems
(`invGetScanOK_merges` and the NoOutside ones). They are not on joint6's
path. The plan leaves them, but for the optional step in section 7.


## 3. What the consumer needs

At each of the three calls the tree at w2 is handed on, unchanged, as
"the tree at the split's start" to a lemma of the split:

- `writerWP_handleFull_lastV` and `writerWP_delSplit_chainGRangeV` (the
  reading, below the space root);
- `writerWP_handleFull_root_j2U` (the take-back, at the space root);
- `writerWP_handleFull_last_j2U` (the take-back, below it).

The same lemmas also take a second tree: the state's tree with the stop
node's content replaced by its last version (`hV`). That tree does not
reach the chain. The consumers prove it from the tree at the delete's
start, without `hU` (`treeOK_up_tr`). The ranges were moved to that tree
earlier, which is why `hU` asks for a tree only, and no longer for its
ranges.

So the consumer needs a tree at the state where the split starts, and
that state names the chain only because the bitmap is not yet in the
stop node. What the split does with the stop node x, read from
`handleFullWith`:

- it reads x's first time (was x made by the transaction?) and x's leaf
  flag;
- it writes x: the first half or the last version in place, for a node
  the transaction made; else x's version before the transaction, at the
  end;
- every klong it copies comes from `last`, the last version that
  `appendDeleteKlong` computed before the call, with the bitmap applied;
- the cascade above x (`appendKlongs` on x's parent) does not read x.

So the end state is the same from any state that differs from the
writer's only in x's node, as long as that node has the same first time,
leaf flag and version before the transaction.


## 4. The routes

### 4.1 Route (a): an invariant on the nodes left out

**What it would state.** The candidate found here, PREFIX: every node or
value of before the transaction that the writer's tree reaches is
reached with the key prefix it has in P. The key prefix of a node is the
list of compare values of the segment leaves' klongs on the way from the
space root: the key's segments above the node's segment tree. A
companion, MF-PREFIX: a reached node that was made in place of a node o
(its made-for id) has the prefix that o has in P.

**Why it should hold.** Every step of the writer moves klongs within one
segment tree. A split and a merge copy live klongs to new nodes of the
same segment tree. Root collapse puts a child in its root's place. A
take-back points a klong at the node its target replaced. A put only
adds nodes.

**Why it would give `hU`** (an argument, not a proof):

- What the loop brings back hangs below the stop node's klong K. Its top
  has, in P, the stop node's prefix with K added (PREFIX for a chain
  node of before the transaction, MF-PREFIX for a made-for id).
- Every node below it in P has a longer prefix. If the writer's tree
  reached such a node before the loop, PREFIX puts it below the stop
  node's klong K, which is the chain and the emptied leaf's value. So
  nothing that comes back is reached from elsewhere.
- A node of before the transaction that is not reached holds P's node:
  it has no klong of the transaction (`TtReachedN`), and a cached node is
  P's node with klongs of the transaction added (the books' `Good`). So
  what comes back is P's subtree, and P is a tree.

**Against the counterexample.** `upUnlinkTreeOK_false`'s state fails the
books already: its leaf 11 is no node of P. putinv2 found that the books
alone do not suffice, since a reverted node may name a node of P linked
elsewhere. PREFIX excludes exactly that.

**Against the runs.** PREFIX and MF-PREFIX held at all 2,529 states
before the loop and at all 56,404 states between operations. What the
loop brought back was P's, and out of reach before, at every loop end.
Section 5 has the counts.

**Size and risk.** PREFIX and MF-PREFIX need a walk over every writer
step (the split's cascade, the bitmap, the empty key's move to the next
child (LE-b), the merge and its parent, root collapse, the loop), then a
place in the joint induction, then the argument above with a lemma that
a prefix names one klong of one segment leaf (from the ranges). For
scale: the made-for walk for one simpler fact is 1,900 lines, the
ranges' files 12,900. Estimate 5,000 to 9,000 lines, 4 to 6 prover
nights. Risk: medium to high. It would also add a member to the joint
induction while cost2's work changes it.

### 4.2 Route (b): the split from a state without the chain

**The consumer change.** Let S be the stop node at the loop's end, and
S' the same node with the bitmap applied as if it had room (`BitmapOf`,
SIS/Tree/TakeDeadDelete.lean, names it). S' has S's first time, leaf
flag and version before the transaction, and its live klongs are those
of `last`, the last version that the split copies. Then:

- **The swap** (new): every successful run of `handleFull` on x from the
  state with x's node S is a run from the state with x's node S', with
  the same result and the same end state.
- **The tree** (at hand): the state with S' is a tree. It reaches what
  the delete's start reached, without the chain. `treeOK_up_tr` gives
  it, as it gives `hV` today.
- **The use:** the split's lemmas are applied at the state with S'.
  Their conclusions speak of the end state, which is the same.

This is `hCoU`'s way, one step weaker. There the two steps commute. Here
they do not: the loop's take-back looks for the klong that the split has
removed, so "the bitmap first, then the loop" does not run. The swap
asks less, and it is enough.

**What is at hand for the swap.** coll's relational walk
(SIS/Tree/CollapseCommute.lean): `XWP` and `xwp_appendKlongs` say that
the cascade runs the same from a state whose node x is changed, when x
is not on the path above. That covers the cascade above the stop node.
New is the split of x itself, a walk of `handleFullWith`'s branches with
x as its subject: after x is written the two states are equal. The
overlay holds one entry per id (`CacheUnique`, from the books), which the
transfer needs.

**Against the counterexample.** The route never claims that w2 is a
tree. Its lemmas hold for every state with their hypotheses, reached or
not. In the counterexample's state the stop node is the space root 10;
with the bitmap applied it names nothing, and its tree is one node.

**Against the runs.** Section 5: 173 of 173.

**Size and risk.** 700 to 1,200 lines. Risk: low to medium. The risk is
a hypothesis of the split's lemmas that does not carry over to the state
with S'. Those read so far carry over: the path, the nodes above, the
next id, well-formed klongs, the take-back's node facts (the same facts
are proved for S' in the room case).

### 4.3 Route (c): a checked copy

As with `hchk`: a copy of the delete that checks, at the loop's end,
that the tree is a tree, and a premise that the delete runs as its copy
from the states that the joint induction reaches. The premise speaks of
reached states only, so the counterexample does not touch it, and the
runs' 2,529 loop ends are its test. But:

- it is a statement change (a premise replaced), for Frans;
- the check is of the whole tree, not of a node and its parent as
  `hchk`'s checks, so no local argument proves it: proving it is
  route (a);
- it only moves the open fact from a false premise to a tested one.

Size: 300 to 600 lines. Worth it only if (b) fails.


## 5. The run checks

One script, the upward loop's check of 14 November
(`12-tree-model/up-loop-end-check.lean.txt`) with notes added:
/Users/f/fl/bench/2026-11-15/hu/stop-swap-check.lean, run from the
lean/ of a built clone with `lake env lean`, about 15 minutes. Its first
16 runs are the families of 14 November, with theta 0. Its last 10 are a
part of them with Java's theta (2 at node sizes 8 and 10), so that a node
also gets full by its dead klongs. `agg.py` beside it sums the output,
`stop-swap-check.out`. As on 14 November, the counts include runs flagged
as not within reach.

**Tested, 0 failures in each:**

- **The tree at the loop's end** (the check of 14 November, `uchk`):
  2,529 loop ends with theta 0, and 1,868 with Java's theta.
- **Route (b), the swap** (`frame`). At every loop end whose stop node is
  full, the script runs the writer's `appendDeleteKlong` from the loop's
  end, and `handleFull` with the same last version from the state with
  S' in the stop node, and compares the end states: every node, the
  segments and heights, the nodes taken back, the next id, the values,
  the path, the top node, the made nodes and the made-for ids. It also
  checks that S' has S's first time, leaf flag and version before the
  transaction, that its live klongs are the last version's, that the
  state with S' is a tree, and that it reaches only what the state
  before the loop reached, without the chain. And three facts that the
  split's lemmas ask of the stop node: the klongs of S' are well formed,
  its links are below the next id, and each of its klongs to a key node
  of the transaction is live.
  - Theta 0: 173 full stop nodes of 2,529 (109 at the space root, 64
    below it). 173 the same.
  - Java's theta: 408 full stop nodes of 1,868 (339 full by dead klongs,
    69 by size; 189 at the space root, 219 below it). 408 the same.
- **Route (a), PREFIX** (`pref`, `pfs`): at the 2,529 and the 1,868
  states before the loop, and at all 56,404 states between operations
  (theta 0).
- **Route (a), MF-PREFIX** (`mfp`, `mfs`): at the same states.
- **What the loop brings back** (`sub`): at the 2,529 and the 1,868 loop
  ends, everything reached below the stop node's klong to the chain is
  of before the transaction, holds P's node, and was out of reach before
  the loop unless the chain reached it. It is 2 to 10 nodes and values
  in these runs.

**Not tested:** node sizes above 10; the merges off (outside the top
theorem); Java's traces.

**A check that was wrong first.** The first form of `sub` asked that
only chain nodes were in reach before the loop. It failed at 504 loop
ends: the emptied leaf's value is in reach too. The form above is the
corrected one.


## 6. The recommended route: (b), step by step

No statement changes: every step adds lemmas, and the last adds a top
theorem. Where a lemma loses a hypothesis, the new lemma gets the proof
and the old one becomes a corollary of it under its old statement, so
that no proof is kept twice. That is the 700 to 1,200 lines. A prover
who copies the proofs instead adds about 2,500. A change in
TakeUpCasc.lean or DelStepsUnlinkTree.lean rebuilds most of the route
above it, so the new lemmas are best written in a new file first and
moved when they build.

1. **The swap** (1.5 to 2.5 hours). A new file, StopSwap.lean, which
   imports CollapseCommute.lean only (so TakeUpCasc.lean and
   DelStepsUnlinkTree.lean can import it). It lands:
   - `setX_self`: with one overlay entry per id, setting x to the node
     it has changes nothing;
   - `handleFull_swap`: the split of x from the state with x's node set
     to m is a run from the state as it was, same result and state, if
     the two nodes agree in first time, leaf flag and version before the
     transaction;
   - `writerWP_handleFull_swap`: the transfer of a postcondition.

   The statements are type-checked in
   /Users/f/fl/bench/2026-11-15/hu/SwapStmt.lean, their proofs `sorry`.
   The run script goes to 024-22's `12-tree-model/` with this step, as
   `stop-swap-check.lean.txt`.
2. **The take-back at the space root** (2 to 3 hours):
   `writerWP_upCasc_root_j2` without its tree hypothesis
   (TakeUpCasc.lean, 230 lines, the shortest of the three). It proves
   the pattern: the facts of S' (from the room case's lemmas), the tree
   with S', the split's lemma at that state, the swap. If a hypothesis
   of the split's lemma fails at the state with S', the prover stops
   here and reports.
3. **The reading below the space root** (1.5 to 2.5 hours):
   `writerWP_upCasc_below_delT` without its tree hypothesis, then
   `upCascOKHGJ_of` without `hU`.
4. **The take-back below the space root** (1.5 to 2.5 hours):
   `writerWP_upCasc_below_j2T` without its tree hypothesis, then
   `upCascJ2OKHGJ_of` without `hU`.
5. **The top theorem** (1.5 to 2.5 hours): the eight lemmas of
   HeightsFillHolder.lean of section 2.3 without `hU`, and
   `invGetScanOK_merges_joint7`: joint6's proof with premises `hp`,
   `hth`, `hchk5`, `htb`, `d4`, `l4`, `hMSF`, `hCoF`. The paragraphs in
   024-12, section 1, and 024-22, section 11.1; lean/README.md. The
   gate as for joint6.

Steps 3 and 4 do not depend on each other, but for step 4's last lemma,
which uses step 3's. One prover can do the route in a night; two can
share it after step 2.


## 7. How it fits with the other open work

- **cost2's plan** (024-12, section 1): state `DelInvJ` (the delete's
  invariant with the take-back's facts) at the delete's calls of
  `afterDelete`; from it the two holder checks left in `hchk` (the
  merge's `checkFree`, root collapse's `checkRoot`); then true forms of
  `hMSF` and `hCoF`. The state at `afterDelete`'s call after a full stop
  node is the end state of the obligation `UpCascJ2OKHG`. Route (b) does
  not change the two obligations, only how they are proved. So the two
  works meet in no statement.
- **No shared invariant is needed.** cost2's holder checks are about the
  nodes a transaction made, and `TakeJ2` in the joint induction covers
  them. Route (b) uses nothing new at the delete's start. Route (a)
  would have added PREFIX to the joint induction; with (b) nobody adds
  to it.
- **Where they touch:** HeightsFillHolder.lean. cost2's prover will state
  more in the delete's step lemmas there; step 5 adds the eight lemmas
  without `hU` there. Rule for cost2's prover: new step lemmas take the
  obligations as hypotheses, as `writerWP_del_emptyAnyMKLHGJ` does, and
  not `hU`.
- **The close step** (006-25, section 7, decision 3: one top theorem
  again, the superseded variants removed). It keeps joint6 and the
  NoOutside theorem (`invGetScanOK_merges_noOutside'`, 025-03). After
  step 5 it keeps joint7 in joint6's place. The NoOutside theorem is on
  the older route and still has `hU`, `hHL` and `hCoU`. Steps 2 to 4
  prove their lemmas for every state, so `hU` can leave that theorem
  too: the older twins `upCascOKHG_of` and `upCascJ2OKHG_of`
  (DelStepsGh.lean) without `hU`, and the six lemmas of
  NoOutsideRun3.lean that pass it on. That is a sixth step of 1 to 2
  hours. It is optional: with `hHL` and `hCoU` left, that theorem stays
  vacuous. The close step is the place to decide it.
- **Order.** Steps 1 to 4 are new lemmas in files that cost2's work does
  not touch (StopSwap.lean, TakeUpCasc.lean, DelStepsUnlinkTree.lean and
  the first 130 lines of HeightsFillHolder.lean); they can run beside
  cost2's prover from the start. Step 5 goes in when cost2's prover is
  between two landings; whoever lands second merges main first. The top
  theorem after both is one theorem: joint7 with cost2's weaker `hchk`.


## 8. What stays open, and the size of the whole

**Open after the route:**

- **The top theorem's premises:**
  - `hchk5` (`OpDelChk5OKL`): a delete runs as its copy with the two
    holder checks that are left; cost2's plan;
  - `htb` (`TakeBelowFuelDelOK`): a delete takes back no node of the
    fuel's height or more;
  - `d4` and `l4`: the dead klongs and the live counts at the deletes
    that split, empty a leaf or merge;
  - `hMSF` and `hCoF` (`MergeFitsOK`, `CollapseFitsOK`): the tree fits
    the fuel after a merge and after root collapse. These two are likely
    false as stated (cost2; not refuted), so the theorem may still hold
    vacuously until they have true forms.
- **Whether the tree at the loop's end is a tree** stays tested only
  (2,529 loop ends, 0 failures). Nothing needs it then. If it is wanted
  for its own sake, route (a) is the way, with section 5's evidence.
- **`UpUnlinkTreeOK`** and its counterexample stay in the Lean code, with
  the older top theorems that name it. Removing those is a clean-up for
  later.
- **The upward delete with the merges off** is outside the top theorem,
  whose parameters (`MergeParamsOK`) have the merges on, as before.

**Size of the whole:** 700 to 1,200 lines in 5 steps, 8 to 13 prover
hours, one night for one prover. No decision of Frans's is needed to
start: every step is an addition.


## 9. Log

2026-11-15. The plan written (sections 1 to 8) by the planning agent of
coord-1114; the run checks of section 5 made; step 1's statements
type-checked. No Lean file of the repo changed. No step started.

2026-11-15, 09:20 to 09:50, prover "hu" of coord-1115 (plan 006-27).
Steps 1 to 5 of section 6 proved, on branch proofs-hu. No statement
changed; no premise changed. The stop rule of step 2 did not apply: every
hypothesis of the split's lemmas holds at the state with S'.

- **Step 1, the swap** (StopSwap.lean, 341 lines). `SWP x m f c u`: every
  successful run of f from u with x's node set to m is a run from u, with
  the same result and the same state. The walk is root collapse's (`XWP`)
  until x is written, then the states are equal (`swp_putNode_bind`,
  `upsert_upsert`); x's node is read at the start for its first time and
  leaf flag (`swp_getNode_bind`, the rest of the split rewritten to the
  other node) and at the end for its version before the transaction
  (`swp_final`). `handleFull_swap` and `writerWP_handleFull_swap` (any
  depth, the cascade above by `xwp_appendKlongs`),
  `writerWP_handleFullWith_root_swap` (the space root, any `up`), and
  `setX_self` (with `CacheUnique`). Differences from SwapStmt.lean: the
  version before the transaction is asked only for a node of before the
  transaction (`n.firstTime ≠ some c.i →`), since the split's last step runs
  only then (at time 0 the stop node's first time is the transaction's,
  as its times are at most 0).
- **S'**, the stop node with its bitmap, is `S.add c.i (.del ...)`, the
  first form of `BitmapOf`, whichever branch the writer takes; its facts
  come from the room case's lemmas (`KNode.add_delete_wf`,
  `add_delete_live_lookup`, `bitmapOf_prefix`, `bitmapOf_firstTime`,
  `bitmapOf_lastLive`). Its first time equals S's because S has a time
  klong first (`KNode.firstTime_some_of_live`, new: a node with a live
  klong and well-formed klongs). The overlay has one entry per id from the
  books (`cacheUnique_of_book`), so the state with S' and S again is the
  writer's.
- **Step 2** (StopSwapRoot.lean): `writerWP_upCasc_root_j2S`, the
  take-back at the space root, with `CacheUnique v` in place of `hT2`.
- **Steps 3 and 4** (StopSwapBelow.lean): `writerWP_upCasc_below_delS`
  and `writerWP_upCasc_below_j2S`, the same below the space root; the
  split's postcondition, stated of the state with S', is moved back to the
  writer's state's names (`updN_updN_same`: the tree with the last version
  is the same from both states).
- **The consumers** (HeightsFillHolder.lean): `upCascOKHGJ_of_noU`,
  `upCascJ2OKHGJ_of_noU` (`CacheUnique` from `KdJP`'s books) and the eight
  lemmas of section 2.3 with `_noU`; each old lemma is now a one-line
  corollary of its `_noU` twin under its old statement, so no proof is kept
  twice there.
- **Step 5** (CollapseCommuteTop.lean): `invGetScanOK_merges_noU`, the top
  theorem's proof with the four lemmas without `hU`; premises `hp`, `hth`,
  `hchk5`, `htb`, `d4`, `l4`, `hMSF`, `hCoF`. `invGetScanOK_merges` is its
  corollary under its old statement (`hU` unused).
- **Size**: about 2,050 lines added, more than section 6's estimate. Steps
  2 to 4 are adapted copies of `writerWP_upCasc_root_j2`,
  `writerWP_upCasc_below_delT` and `writerWP_upCasc_below_j2T` (about
  1,100 lines): the old ones cannot be corollaries of the new, which take
  the books' `CacheUnique` in place of the tree. The old three are still
  used by DelStepsGh.lean (the NoOutside route, step 6); when that route
  leaves them too, they can go (the close step).
- **Left**: step 6 (`hU` out of `invGetScanOK_merges_noOutside`); the
  premises `hchk5`, `htb`, `d4`, `l4`, `hMSF`, `hCoF` (section 8).

