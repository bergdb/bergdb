# 030-01. The plan for l4

Created 2026-11-16 by Frans Lundberg. Status: open (steps 0, 1 and 2 done, 2026-11-16).

The plan for the premise `l4` of the key tree's top theorem
`invGetScanOK_merges_tbL` (lean/SIS/Tree/DeadTop.lean): `l4 : OpCaseOK p
(RunOK p) (QLive p) DelMergeOpenCase`, the deletes that keep TP7's live
counts in the open cases. It answers 006-27, section 8, decision 1: hu's
option (b) against copies and against route P's generic families, and
what MT would change. The plan is for today's model. I am the writer, an
agent of coord-1116 (plan 006-29); I wrote it on 2026-11-16 from 22:04.
The form is 025-04's and 025-05's.


# 1. The result

- **Statement change: no.** The recommended route (B, section 3.4)
  changes no existing definition and no existing statement. Every step
  adds definitions, lemmas and new top theorems; the old ones stay and
  become corollaries at the close step (006-27, decision 3). A prover can
  start tonight.
- **What `l4` says.** A delete with the merges on keeps TP7's live counts
  (`LiveCounts`: a live klong in every node reached but the space root as
  a segment leaf, two in an inner segment root, `mergeBelow` in a node an
  inner node names). Open only for the deletes that split their leaf,
  empty it, or leave it under the fill; the rest is proved.
- **Why it is hard.** It is used inside the joint induction, not after it,
  so its proof could use only what `RunOK` runs give. And its invariant is
  not local: a delete leaves one node under the fill (a hole), the merges'
  loop moves the hole up one level a merge, and root collapse closes it.
- **Step 1 is proved in scratch.** `invGetScanOK_merges_l4L`, premises
  `hp`, `hth`, `htbL` and `l4L`, where `l4L` (`LiveDelSL`) is `l4` at the
  induction's runs, at deletes whose start has the induction's facts, as
  `htbL` is `htb`'s (025-05, step 9). `l4` gives `l4L`, so the new theorem
  is stronger; `invGetScanOK_merges_tbL` is its corollary. On the standard
  three axioms; type-checked at 22:19 with `lake env lean` on main's
  build. The file, 442 lines, most of them near-copies:
  `/Users/f/fl/bench/2026-11-16/night/l4plan/L4Forms.lean`.
- **The routes** (section 3):
  - (a) copies of the delete's walks with the live counts, as `d4`'s
    `_D` copies: 6,000 to 9,000 lines;
  - (b) hu's option, the families' obligations with an extra invariant,
    the old definitions replaced: a statement change of definitions, B's
    size and 500 to 1,500 lines of churn, no gain for `l4`;
  - (c) route P's generic families as they stand: they do not give it;
  - B, (b) done route P's way, beside the old forms: 3,000 to 5,500
    lines, no statement change. **Recommended.**
- **Size of B:** 8 steps (0 to 7). By the plans' measure 19 to 36
  prover-hours. On 15 November provers did planned routes about ten times
  faster than planned, but stalled twice on non-local arguments; my
  expectation is 6 to 12 prover-hours: one night for two provers, if no
  stop rule fires.
- **The three points where it can stall:** finding the hole by the
  heights (the merges' loop descends by cached height); the upward
  delete's emptied chain; root collapse's early return for a root the
  transaction made with no made-for entry (section 2.3).
- **For Frans:** nothing is needed to start. Five choices with defaults
  in section 9.
- **If MT is taken** (section 8): about half of B's lines carry over (the
  hole's form, one merge, one collapse step, the bitmap and the split);
  the induction, the loop, the chain and the made-root branch do not.


# 2. What l4 says, where it is used, why it is hard

## 2.1 The premise

`OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase` (LiveDelNoop.lean,
LiveCounts.lean): for every run with `RunOK` (links, P's tree, `InvOK`),
every transaction within reach, every state that its earlier operations
reach with `PutInv` and the ranges, and every delete there in the open
case, the delete ends where, given the writer's tree after it, the live
counts at its start give the live counts at its end.

- **The open case** (`DelMergeOpenCase`): a delete with the merges on
  that is not (4a), not a noop, and not of a key with no leaf. Proved:
  (4a), a leaf with room that keeps enough live klongs
  (`liveCase_delRoomFill`, LiveDelRoom.lean; the merges' loop then merges
  nothing, `writerWP_afterDelete_none`, LiveNoMerge.lean); the noop and
  the key with no leaf (`opCaseOK_delNoop`, `opCaseOK_delNoLeaf`).
- **Left:** a full leaf (its split and cascade, then maybe merges); the
  upward delete (an emptied leaf, the chain above it, the stop node's
  bitmap or split, then maybe merges); a leaf with room left under the
  fill (the merges' loop and root collapse).
- **Evidence:** `LiveCounts` held at all 6,420 states between operations
  of runs with merges and collapses, and at 8,843 more with Java's theta
  (024-12, section 1; `12-tree-model/live-counts-check.lean.txt`,
  `dead-all-check.lean.txt`). No check looked inside a delete.

## 2.2 Where it is used: inside the joint induction

In `invGetScanOK_merges_tbL`, `l4` becomes the delete case of
`hLv : OpCaseOK p R (QLive p) AnyOp` (with `liveCase_delMerge_of_rest`,
`opCaseOK_of_open`, `opCaseOK_anti`), which goes into the joint induction
`jointHtJ_reached1` (StratumChk.lean), and down the wrappers
`jointHtJ_reachedS`, `jointHtJ_reachedT`, `jointHtJ_reached0` to
`jointHtJ_reachedJS` (HeightsFillTop.lean). There the delete branch
applies `hLv` with only `PutInv` and the ranges at the delete's start.
The induction is what gives the facts a proof of `l4` needs: the heights'
walk (`HtInv`), the writer's tree, the take-back's facts (`J2At`), the
books. So `l4` cannot use them as stated (hu's State note, 024-12,
section 1).

The fix is a change of the consumer, as for `d4` and `htb` on 15
November: the induction takes the delete's live case given the facts it
has at the delete's start. I did it in scratch (section 5, step 1):

- `jointHtJ_reachedJSL`: `jointHtJ_reachedJS` with `hLv` split into the
  puts' case (`OpCaseOK p R (QPut (QLive p)) AnyOp`) and the deletes'
  (`LiveDelS p R DelMergeCase`); the proof is the old one with two lines
  changed.
- `LiveDelS p R P`: `QLive` at a delete of case P of the runs of R whose
  start has `PutInv`, the ranges, `LiveCounts`, `HtInv`, the writer's
  tree and `J2At`, the same list as `TakeBelowFuelDelS`. `LiveDelSL p` is
  its open case at the induction's runs (`RunTreeQ p (LatestQD p)`).
- `liveDelSL_of`: `l4` gives `l4L`. `liveDelS_merge_of_open`: the open
  case gives every delete with the merges, the proved cases added.
- After the induction, `hLv` (used by `latestQD_snocR` and
  `opCaseOK_L_of_any`) comes from the induction's conclusion, as `hT`
  does today.

`l4` as stated stays undischarged, as `d4` and `htb` did. Whether it is
true for every `RunOK` run is open: such a run carries no kinds and no
heights (`RunOK` is links, P's tree and `InvOK`).

## 2.3 Why it is hard: the hole

**The hole.** After the leaf's change one node may be under the fill: the
leaf with room that kept fewer than `mergeBelow` live klongs, the full
leaf's last version after a time split, or the stop node after its
bitmap. `afterDelete key g h` then runs the merges' loop from the node of
segment g at height h on the key's path (`mergeUp`, Exec.lean): while
that node is not a segment root and is under the fill, it is merged with
a sibling; a merge into one node takes a live klong from the parent,
which becomes the hole, one height up; a merge into two nodes leaves no
hole. At the loop's end the hole, if any, is the segment root with one
live klong, and root collapse lets its child take its place.

**What makes it not local** (hu's note, 024-12, section 1, made exact):

- **R1, the heights find the hole.** `mergeUp` re-descends each round by
  cached height (`descendToHeight`, `descendHeight`). That it reaches the
  hole needs the heights' cache on the key's path (`HtInv`: `HtCache`,
  `PathHt`, WriterHeightsRules.lean, OverlayHeights.lean). The tree's
  facts that the stratum's family carries (`DelInvJT`) have no heights.
  The obligation for `afterDelete` must also know (g, h): today's
  families ask it for every g and h, and `writerWP_deleteUpward_full`
  (DelStepsFull.lean) gives its continuation no fact of the pair.
- **R2, the upward delete's chain.** The emptied chain's nodes are taken
  back or set back to their versions before the transaction while the
  stop node still names the top one; only after the stop node's bitmap is
  the tree the start's without the chain. The live counts hold only after
  that (`treeOK_up_tr`, `tReach_up_sub_tr`, WriterGetUpAll.lean, for the
  tree; `handleFull_swap`, StopSwap.lean, when the stop node splits).
- **R3, the made root.** `collapseRoot` returns early when the root was
  made by the transaction and has no made-for entry. A split of a node
  with no entry gives its new root none (`handleFullWith`,
  `setMadeFor r (← replacedBy x)`), so the root of a segment that the
  transaction made fresh is never collapsed. My reading: such a segment
  holds only keys that the transaction put, a transaction has one
  operation a key (`Tx.sorted`, 024-16), so no delete with an effect
  reaches it, and a hole never sits there. Not proved, not run.

**The hole's form.** `LiveEdgesX` (LiveStepsX.lean), the cascade's form
with exceptions, asks that an excepted node is named by segment leaves
only (a new segment's empty leaf). A hole under an inner node does not
fit (026-19, section 3, notes the same). So a new form is needed, and
the cascade's walk with exceptions, `writerWP_appendKlongs_chainGLX`
(WriterTreeChainG.lean, about 1,570 lines), must take it: the full
leaf's split, the stop node's split and a full merge parent's split all
cascade with the hole below the chain. In LiveStepsX.lean the condition
enters through `edgeX_grow` and five lines that name it, and the split
steps go through `liveEdgesX_of_sim`, which carries only the membership
of the exceptions. So a parameter for the condition looks mechanical (my
reading; R4 in section 3.4).

## 2.4 What exists

- **Counts:** `mergeKlongs_live_fill` (MergeLiveFill.lean: a merge's new
  nodes are filled); `halves_live_fill`,
  `halves_lastVersionGivenDel_live_fill` (SplitLiveFill.lean);
  `newRoot_liveAt_two`, `repoint_liveAt_length` (LiveChain.lean);
  `KNode.retarget_liveAt` (WriterTreeRetarget.lean);
  `mpNode_live_lookup` (WriterTreeMergeLive.lean: the merge parent's live
  klongs); `live_shrink`, `liveCounts_updN_leaf` (LiveDelRoom.lean);
  `stopLeaf_of_liveCounts` (StopLeafLive.lean).
- **Reach after each step**, from the tree's proofs: `treeOK_mergeOneAfter`
  (WriterTreeMerge.lean), `treeOK_mergeTwoAfter` (WriterTreeMergeTwo.lean),
  `mergeV_reach`, `treeOK_after_cleanup`, `writerWP_mergeParent_cases`
  (WriterTreeMergeFull.lean), `treeOK_collapse_reach`,
  `treeOK_collapseSpace`, `treeOK_collapseSegment`, `treeOK_up_tr`,
  `tReach_up_sub_tr`, `treeOK_dropSubtree_tr` (WriterGetUpLeb.lean), the
  delete's split (WriterTreeDelChain.lean, `delLast_halves`).
- **Edges:** `LiveEdges` and its equivalence with `LiveCounts`
  (LiveEdgesBase.lean, LiveEdges.lean); the steps (LiveSteps.lean,
  LiveStepsX.lean); the cascade with exceptions (`chainGLX`).
- **The stratum** (025-05, step 7): the family `DelStepsCaseTJ`
  (StratumSteps.lean) and its cases (`delStepsTJA_holds`,
  StratumCasc.lean), the tree's facts at the calls (`DelInvJT`,
  `DelInvJAE`), the loops with no fit (`writerWP_mergeUp_delJAE`,
  `rwp_mergeUp_of_JAE`, Stratum.lean).
- **Heights inside a delete:** `ht_merge_of_J` (DelMergeUp.lean),
  `ht_mergeUpChk`, `ht_afterDeleteChk`, `ht_collapseRootChk`
  (WriterHeightsChk.lean), `ht_putKvDelChk2` (HeightsPathFree.lean).
- **026-19's hole form** (on its branch, not on `main`): `LiveCountsH`,
  `LiveCounts` asked only outside a set of holes (026-19, section 3.2).


# 3. The routes

## 3.1 (a) Copies

`_L` copies of the stratum's case lemmas and walks that carry the live
counts with the hole beside `DelInvJT` to `afterDelete`, as `d4`'s `_D`
copies carry `DW` (DeadDelCases.lean: `writerWP_del_emptyRoomMKDG`,
`writerWP_del_emptyAnyMKLHGJDG`, about 600 lines with their instances). With
the hole's form, `chainGLX` and the steps of LiveStepsX.lean copied too.

- **Size:** 6,000 to 9,000 lines: B's 3,000 to 5,500, plus about 1,200
  of walk copies, 1,600 of `chainGLX` and 850 of LiveStepsX.lean. By the
  plans' measure 35 to 60 prover-hours.
- **Risks:** the same three points as B (R1 to R3); more code to keep and
  to remove at a close step.
- **Reuses:** what B reuses, by copy.
- Not recommended: the copies are the larger part and add nothing.

## 3.2 (b) The obligations with an extra invariant (hu's option)

`DelStepsCaseOK` and its sisters re-stated so that their obligations
carry an extra invariant; the `_D` copies and `l4`'s route become
instances. As hu put it, the old definitions are replaced.

- **A statement change** of definitions (not of a premise): Frans's word.
- **Size:** B's, and 500 to 1,500 lines of churn: every user of the old
  families restated.
- **Gain for `l4`:** none over B. The gain is fewer definitions, the
  close step's business.
- Not needed now; section 9, question 2.

## 3.3 (c) Route P's generic families as they stand

The P4 families (025-05, section 4.1: `DelStepsOKG`, `DelStepsJ2OKG`,
`DelStepsQdLJG`, `DelStepsCaseDOKG`, and the stratum's `DelStepsCaseTJ`)
take their obligations over an invariant I. They do **not** give what
`l4` needs:

- I is entered only from the tree's or the reading's invariant at the
  call (`∀ v, DelInvJT ... v → I ... v`). The live counts at a call do
  not follow from it: they depend on which node the case changed and on
  the counts at the start.
- The obligations are for every g and h; `l4`'s needs the pair of the
  changed node (R1).

What route P gives is the method: generalize beside, the old form an
instance, the proof kept once. With it, (b) is an addition. That is B.

## 3.4 B: (b) done route P's way (recommended)

- **The consumer change** (step 1): the induction takes the delete's live
  case with the facts at its start (section 2.2). Proved in scratch.
- **The hole's form** (step 2): `LiveEdges` with the links to a set of
  holes asked only for a live klong, and a form for the exit of the
  loop. One definition for both the hole under an inner node and
  `LiveEdgesX`'s exceptions if the pilot finds it cheap (`LiveEdgesX`
  then its instance), with an equivalence to 026-19's `LiveCountsH` so
  that the two directions share it.
- **The walks generalized, not copied:** `writerWP_deleteUpward_full`
  and the stratum's two upward walks (`writerWP_del_emptyRoomMJKT`,
  StratumSteps.lean; `writerWP_del_emptyAnyMJKT`, StratumCasc.lean) give
  their continuation the changed node's (g, h) and the frame facts (which
  node changed, the chain); `chainGLX` and LiveStepsX.lean's steps take
  the hole's form. Each old lemma becomes its instance.
- **A live family**, with obligations indexed by (g, h), whose five cases
  follow `delMerge_cover` as `DelStepsCaseTJ`'s do.
- **No statement change.** The gate passes such additions, as it passed
  route P's and `htbL`'s.
- **Size:** 3,000 to 5,500 lines in 8 steps (section 5); 19 to 36
  prover-hours by the plans' measure, 6 to 12 expected.
- **Risks:** R1 to R3 (section 2.3), and R4, the size of `chainGLX`'s
  generalization. R1 to R3 have a check in step 0; all four have a stop
  rule (section 7).
- **Reuses:** the counts, the reach lemmas, the stratum's tree facts, the
  heights' walk (section 2.4), and whatever `htbL`'s step 8 lands for the
  merges' site (it needs the node at (g, h) too).

## 3.5 Others

- **K, keep `l4`** as a tested premise. 0 lines. Against Frans's aim
  ("We still try to prove everything now", 2026-11-15, 08:47).
- **S, `l4` as stated**, by a second induction along the transaction for
  `RunOK` runs. `RunOK` has no kinds and no heights, so the walk's facts
  are not at hand, and `l4` as stated may not even hold there. Not
  recommended.
- **C, a checked copy** whose end checks the live counts: a restated
  premise, which 030's rules exclude.
- **MT** changes what `l4` says; section 8.


# 4. The recommendation

Route B. It changes no statement, lands its first theorem tonight (step
1, proved in scratch), tests the hole's form on runs before any long
proof (step 0), and settles the first hard point, the heights, on one
merge before the bulk (step 2). Copies cost twice the lines for the
same proof; hu's (b) as a replacement costs Frans a decision and gives
`l4` nothing more.


# 5. The steps

Each step: a prover, Opus 5.5 at xhigh, under the night's common brief
(`/Users/f/fl/bench/2026-11-16/night/common.md`, rules 1 to 8), in its
clone `/Users/f/fl/bench/2026-11-16/night/NAME/clone` (from `main`,
branch `proofs-NAME`, built), NAME `l4` for the first prover. New lemmas
go in new files first (025-05, section 6); an old lemma becomes a
corollary of its generalization when that is cheap, else at the close
step. Sizes are lines; "planned" is the plans' measure, "expected" mine
at 15 November's speed.

## Step 0. The hole on runs (scratch)

- **What:** a copy of `fuel-inside-check.lean.txt` (024-12's
  `12-tree-model/`: its copy of the writer's delete and its families),
  that checks at each state inside a delete:
  - C1, after the leaf's change (the bitmap with room, the full leaf's
    split, the stop node's bitmap or split, the space root kept empty):
    `LiveEdges` but for one hole, the node of segment g at height h on
    the key's path, (g, h) the changed node's cached pair;
  - C2, after each merge: the hole is the node at (g, h + 1) after a
    merge into one node, none after a merge into two;
  - C3, at the loop's end: no hole, or the hole is segment g's root,
    inner, with one live klong, and the loop merged;
  - C4, at root collapse's early return for a made root with no made-for
    entry: the root is a leaf or has not one live klong; how often the
    branch runs;
  - C5, at each round: `descendToHeight key g h` reaches the hole;
  - C6, the end: `LiveCounts`.
- **Families:** `fuel-inside-check`'s and `live-counts-check`'s, and one
  more for C4: transactions that put keys under new prefixes (new
  segments, split in place) and delete keys under old and new prefixes,
  in one transaction.
- **Size:** 250 to 400 lines of scratch; planned 1 to 2 hours, expected
  under 1. Runs of seconds to minutes with `lake env lean`.
- **Output:** counts, 0 failures, or the smallest failing run. Kept as
  `live-inside-check.lean.txt` with the plan's evidence (the coordinator
  copies it into the item).
- **Gate:** none (no repo change).

## Step 1. The reduction: `l4` to `l4L`

- **What:** the scratch file's content in a new file (default name
  `SIS/Tree/LiveTop.lean`, importing `SIS.Tree.DeadTop`):
  `LiveDelS`, `LiveDelSL`, `liveDelSL_of`, `liveDelS_merge_of_open`,
  `jointHtJ_reachedJSL` and its four wrappers (`jointHtJ_reached0L`,
  `_TL`, `_SL`, `_1L`), `invGetScanOK_merges_l4L`. The old induction and
  wrappers and `invGetScanOK_merges_tbL` become its corollaries at the
  close step (`liveDelS_of_any` and `qput_of_any` are in the file), not
  tonight: HeightsFillTop.lean and the Stratum files are deep in the
  build, and the prover of `htbL` works above them.
- **Size:** about 450 lines with the near-copies (about 150 of them would
  go at the close step); planned 1 to 2 hours, expected 15 to 30
  minutes.
- **Test:** none needed: `l4L` follows from `l4` (`liveDelSL_of`), which
  is tested.
- **Gate:** gate-1116.sh; beyond it, `#print axioms
  invGetScanOK_merges_l4L` (the standard three) and its statement
  against `invGetScanOK_merges_tbL`'s: the same but `l4L` for `l4`.
- **Rule 1 of the common brief** asks for one short corollary when a
  premise leaves. This step is a reduction, as 025-05's step 9 was for
  `htb`, not a discharge; the coordinator says yes to it in the brief.

## Step 2. The hole's form and one merge (the pilot)

- **What:**
  - the definitions: the hole's form (section 3.4), `HoleAt key g h v`
    (the hole is the node of segment g at height h on the key's path at
    v, with a live klong), the loop's exit form;
  - the invariant at a call of `afterDelete`: `DelInvJT`, the books,
    `HtInv` and the hole at (g, h);
  - the pilot: one merge into one node, the parent with room and no
    compaction, neither node made by the transaction, keeps the invariant
    with the hole at (g, h + 1); with `treeOK_mergeOneAfter`'s reach,
    `mergeKlongs_live_fill` (its order premises from `RangeOrder`, as
    `d4`'s merge took them, DeadMergeStep.lean), `mpNode_live_lookup`,
    and the heights for the parent's pair.
  - Choose where the heights come from: over `putKv`, from the stratum's
    loop with `ht_merge_of_J` or `rwp_mergeUp_of_JAE` and
    `ht_mergeUpChk`; or over the checked copy beside `ht_putKvDelChk2`,
    as `htbL`'s step 8 plans. Default: over `putKv`, the stratum's form;
    the other if the pilot's heights come cheaper there. Write why.
  - Before starting: read `main`'s log for `htbL`'s landings; if its step
    8 has a walk with the node at (g, h) at the merges, use it.
- **Size:** 300 to 600 lines; planned 3 to 5 hours, expected 1 to 2.
- **Test:** step 0's C1, C2, C5.
- **Gate:** gate-1116.sh (additions only).

## Step 3. The merges' loop

- **What:** every merge (two nodes; the parent full, `mergeFullLast`
  through `handleFull` with its cascade; the compaction, `deadOver`;
  made nodes retargeted and taken back, others unlinked), then the loop
  `mergeUp` from the hole at (g, h) to the exit form. The cascade with a
  hole below the chain: `chainGLX` and LiveStepsX.lean's steps over the
  hole's form, the old ones their instances.
- **Size:** 900 to 1,600 lines (of them 200 to 500 for `chainGLX`'s
  generalization); planned 6 to 10 hours, expected 2 to 4.
- **Test:** C2, C3, C5.
- **Gate:** each part alone.

## Step 4. Root collapse

- **What:** from the loop's exit form, `collapseRoot` ends with
  `LiveEdges`: `replaceRoot` (the space root through `newSuperRoot`; a
  segment root through `appendKlongs` at the segment leaf above),
  `takeBackRoot`, the loop; the early return for a made root with no
  made-for entry (R3).
- **Size:** 300 to 700 lines; planned 2 to 4 hours, expected 1 to 2.
- **Test:** C3, C4.

## Step 5. The leaf's change: room and full

- **What:** the bitmap with room (the leaf is the hole), the full leaf's
  split of its last version given the delete (a time split's copy may be
  the hole; a space split's halves are filled) with its cascade (step 3's
  generalized walk), and the (g, h) of the changed node at the call:
  `writerWP_deleteUpward_full` generalized to give its continuation the
  cached pair. The cases `room` and `full` of the live family.
- **Size:** 300 to 600 lines; planned 2 to 4 hours, expected about 1.
- **Test:** C1.

## Step 6. The upward delete

- **What:** the emptied chain's frame (a live mirror of `treeOK_up_tr`:
  after the stop node's bitmap the tree is the start's without the chain,
  the stop node the hole); the space root kept empty (`RootOK` allows
  it); the stop node with room; the stop node full, through
  `handleFull_swap` and the cascade. The stratum's upward walks
  generalized to hand `afterDelete` the frame facts and the stop node's
  pair; the old walks their instances. The cases `emptyRoom`,
  `emptyRoot`, `emptyCasc` of the live family.
- **Size:** 500 to 1,000 lines; planned 3 to 6 hours, expected 1 to 2.
- **Test:** C1 at the stop node.

## Step 7. The family, `l4L` discharged, the top theorem

- **What:** the live family's five cases by `delMerge_cover` (the noop,
  the key with no leaf and (4a) reused); `liveDelS_holds`, `LiveDelS`
  for the induction's runs; `invGetScanOK_merges_noL4` (name by rule),
  premises `hp`, `hth`, `htbL`: one short corollary of
  `invGetScanOK_merges_l4L` (common brief, rule 1). If `htbL`'s
  discharge has landed: the theorem with `hp` and `hth` only, a corollary
  of both. `l4`'s State note in 024-12, section 1; lean/README.md.
- **Size:** 200 to 400 lines; planned 1 to 3 hours, expected under 1.
- **Test:** C6.

## The order and what runs in parallel

- **Tonight, one prover:** step 1, then step 0, then step 2. Step 1
  first because it is short, sure and gated alone; step 0 before any
  long proof (common brief, rule 5); step 2 after step 0.
- **After step 2 lands, two provers:** A takes steps 3 and 4 (the
  obligation of `afterDelete`), B takes steps 5 and 6 (the cases up to
  the call). They meet only in the hole's form (step 2) and in
  `chainGLX`'s generalization (step 3, which step 5 uses: B starts with
  the room case and the upward delete's frame until A lands it). Step 7
  by whoever ends first.
- **Beside `htbL`'s prover** (tonight): no shared file. Step 1's new
  file imports DeadTop.lean; whoever lands second merges `main` first
  (common brief, rule 4). The shared idea is the node at (g, h) at a
  merge (step 2).
- **Beside 026-19** (D2, on its branch): its hole form `LiveCountsH`
  and its one-merge lemma are for fix steps with empty books. Step 2
  aligns with its definition; nothing is imported from the branch.


# 6. Tests on runs and the gate

- **Before a long proof:** step 0's checks, all 0 failures. Each later
  step's lemmas are theorems for every state with their hypotheses, so
  the runs test the hypotheses' form (C1 to C6). If a step changes the
  form, rerun step 0 at that point first.
- **The gate:** each proved step is committed on the prover's branch in
  Frans Lundberg's name ("030-01: ..." or "024-12: ...", plain words, no
  AI names), then

      sh /Users/f/fl/bench/2026-11-16/night/gate-1116.sh <clone> <dir>/gate-N

  It builds, refuses `sorry`, `admit`, axioms of ours, `native_decide`,
  `implemented_by` and `extern`, and checks that the trusted closure and
  the statements of `invGetScanOK_merges` and
  `invGetScanOK_merges_noOutside` equal the base's (`main` 96918d92).
  New top theorems are not on its audit list: the prover checks them
  beyond it (`#print axioms`, the statement against the one it
  replaces), as on 15 November. On GATE PASS: "GATED l4 <commit>
  gate-N: <theorem> with premises <list>" to `main`; the coordinator
  lands.


# 7. Stop rules

- **The night's:** the STOP file
  (`/Users/f/fl/bench/2026-11-16/night/STOP`), checked before each build
  and every 20 minutes; no new step after 04:30, stop at 05:30 (common
  brief, rule 7); the week's ceiling as the coordinator sets it.
- **Step 0:** a failure of C1 to C5 means the hole's form is wrong: no
  proof of it. Re-form (for example, the hole as a set on the key's path)
  and recheck. After two forms that fail, stop and report. A failure of
  C6 is a counterexample to `l4`: build it in Lean, stop (030's rules).
- **Step 1:** if a lemma between the induction and the top theorem uses
  `hLv` at a delete otherwise than through the induction's conclusion,
  write which and go on with step 0. (In scratch none did.)
- **Step 2 (R1):** if the pilot needs a fact at the merge's start that
  neither `DelInvJT`, nor `HtInv`, nor the induction's start gives,
  write which and stop the route; report.
- **Step 3 (R4):** if `chainGLX`'s generalization passes about 600
  changed lines, prove a narrower lemma for a hole below the chain's
  bottom instead; if that passes 800, report.
- **Step 4 (R3):** if the made-root branch needs an invariant over a
  transaction's earlier operations of more than about 400 lines, stop
  that branch: a narrowed premise for it alone, tested by C4, as a gated
  reduction; report.
- **Step 6 (R2):** if a hypothesis of the split's lemma fails at the
  swapped state (as 025-04's step 2 rule), report.
- **Size:** past 6,000 lines in all, stop after the current step and
  report.
- **MT:** if Frans decides MT, stop at the next gated step (006-28,
  section 7.7, item 1).


# 8. If MT is taken

MT (006-28, section 7.5; 026-17; 026-18): a user transaction makes no
merge, no upward delete and no root collapse; each is a fix step of its
own. Then `l4` is a statement about one step: a user delete keeps the
fill but on its key's path; a fix step keeps it but on its key's path,
by TP36 and TP37; the driver's end is the fill. With 026-18, readers see
only the states between main transactions.

What of B carries over:

- **Carries:** the hole's form (step 2), if it is 026-19's
  `LiveCountsH` or equivalent to it; one merge of nodes the transaction
  did not make (step 2's pilot and most of step 3's merge lemmas: a fix
  step starts with empty books); `replaceRoot`'s part of step 4; step 5
  whole (MT's user delete is the bitmap and the full leaf's split with
  the leaf excepted, 006-28, section 7.5); the stop node's bitmap and
  split of step 6 (MT's removal of an empty one-node tree from the leaf
  above); step 0's script, as a model for MT's K5-like checks.
- **Does not carry:** step 1 (today's induction and top theorem); the
  loop of step 3 and the made branches (retarget, take-back); the
  made-root branch and `takeBackRoot` of step 4; the chain's frame of
  step 6; step 7.
- **New under MT:** the merge of an empty node and of an only child
  (026-17, R3 and R4).
- **By lines:** about half of B. So if MT looks likely, steps 0, 2, 3's
  one-merge lemmas and 5 are the safe part; step 1 costs little either
  way.


# 9. For Frans, and for the coordinator

None of these is needed to start. Each has a default that goes ahead.

1. **The route.** Default: B, no statement change; steps 1, 0 and 2
   tonight, the rest after step 2 lands.
2. **hu's (b) as a replacement** of `DelStepsCaseOK` and its sisters (a
   statement change of definitions; the `_D` copies go). Default: not
   now; at the close step with 006-27's decision 3, only if fewer
   definitions are wanted.
3. **MT.** If decided, B stops at its next gated step. Default: B goes
   on until Tuesday's decision point (030's map, 2026-11-17 morning);
   steps 0, 2 and 5 are useful either way.
4. **The made-root branch (R3)**, if it needs a new invariant over a
   transaction's earlier operations. Default: a narrowed, tested premise
   for that branch alone (a gated reduction), the proof later.
5. **Keep `l4` as a tested premise** (K). Default: no.

For the coordinator: step 1 is a reduction, not one short corollary
(common brief, rule 1); the default is to allow it, as for `htbL`
(025-05, step 9).


# 10. What I could not check

- No `lake build` and no run check. Step 1 is type-checked in scratch
  with `lake env lean` against `main`'s build in htbl's clone, and stands
  on the standard three axioms there; the gate has not seen it.
- Step 0's checks are not written or run: C1 to C5 are my reading of
  `mergeUp`, `afterDelete`, `collapseRoot` and `deleteUpward`
  (Exec.lean).
- Whether the facts at the delete's start suffice for the pilot (R1),
  and whether the heights come cheaper over `putKv` or the checked copy.
- The size of `chainGLX`'s generalization (R4): I read its statement,
  not its 1,570 lines.
- R3's argument (fresh segments hold only this transaction's puts) is my
  reading of `setNode`, `handleFullWith` and `merge`; no Lean, no run.
- Whether `l4` as stated holds for every `RunOK` run.
- What the `htbL` prover and 026-19's provers land tonight, and whether
  their pieces fit.
- The line counts are estimates by analogy with `d4`'s route (DeadLocal
  to DeadDelCases, about 2,500 lines) and the stratum (about 2,000), not
  measured.


# Log

2026-11-16, 22:04 to 22:30. The plan written by an agent of coord-1116
(plan 006-29). Read: 006-27, section 8; 024-12, section 1; 025-04;
025-05; 006-28, section 7; 026-17's result; 026-18; 026-19, section 3;
the Lean of the premise, its consumers, the stratum, the families and
the writer's delete. Made, outside the repo: step 1 in
scratch (`/Users/f/fl/bench/2026-11-16/night/l4plan/L4Forms.lean`, 442
lines; `invGetScanOK_merges_l4L` and `invGetScanOK_merges_tbL` as its
corollary on the standard three axioms; checked 22:19). No Lean file of
the repo changed. No step of section 5 started.

2026-11-16, 22:27 to 22:30. Step 1, prover l4 (coord-1116): the scratch
file landed as `lean/SIS/Tree/LiveTop.lean` (453 lines), imported from
`SIS.lean`; `invGetScanOK_merges_tbL'` renamed
`invGetScanOK_merges_tbL_of_l4L`; doc comments added, nothing else
changed. `invGetScanOK_merges_l4L` and `invGetScanOK_merges_tbL_of_l4L`
on the standard three axioms (`#print axioms`); the statement is
`invGetScanOK_merges_tbL`'s with `LiveDelSL p` for `l4`. State notes:
024-12, section 1; lean/README.md.

2026-11-16, 22:31 to 22:38. Step 0, prover l4: `live-inside-check.lean.txt`
(in the night's directory, /Users/f/fl/bench/2026-11-16/night/l4/, for the
coordinator to copy here): C1 to C6 with 0 failures in 15 families, 2 min
26 s; its header has the counts. C4's branch (a made root with no made-for
entry) never ran, also in the two new families with new segments split in
the transaction beside deletes under old prefixes. The hole's form of
section 2.3 holds as stated: one hole, the node the descent finds at
(g, h), with a live klong; after a merge into one node at (g, h + 1); at the
loop's exit none or segment g's root with one live klong.

2026-11-16, 22:39 to 22:56. Step 2, first part, prover l4. The hole's form
as additions: `LiveEdgesH` (a hole asks only a live klong; the space root as
a hole only `RootOK`'s first half), `HoleAt` and `LiveHole` (the node that
the merges' descent finds), `liveEdgesH_mergeOne` (LiveHole.lean, on node
maps, the parent the hole after). R1's core (LiveHoleDescent.lean): the
descents as functions of what the writer reads (`rdN`, `rdG`; `lteP`,
`dsrP`, `dhP`), and `descendToHeight_up`: one height up, on a state that
reads alike on the path above the found node (its contents above its
parent, its heights down to its parent), the descent stops at the parent,
given that the heights go down by one at each inner node of the path
(`GradedL`). No stop rule fired.

2026-11-16, 22:57 to 23:10. Step 2 done, prover l4 (LiveHolePilot.lean,
about 800 lines): `liveHoleW_merge_pilot`, the pilot of section 5, at a
round of `mergeUp`: from the round's descent (v to v1), its reads (v3) and
`merge x d` into one node, p with room (`pn.size + 3 ≤ M`), no compaction
(`deadOver` false for the parent's new version) and no child made by the
transaction, `LiveHoleW key g h` at v gives `LiveHoleW key g (h + 1)` after.
Its parts: the merge at the writer's level on the steps of the tree's and
`d4`'s merge proofs (`writerWP_mergeTail_livePilot`,
`writerWP_merge_livePilot`), `gradedL_of_ht` (the heights from `HtInv`,
`Book` and `ViewHeights` at v1), `descendToHeight_up`. Where the heights
come from (section 5, step 2's choice): over `putKv`, the stratum's form;
the facts at the round are `HtInv` at the descent's end
(`ht_descendToHeight`), `Book` and `PathFreeTo`, so no checked copy was
needed. R1 did not stall. One definition added beside step 2a's:
`HoleAtW`, the node that every successful run of the descent finds (all
nodes if none succeeds), since a merge's post can give the next round's
hole only as a precondition of its descent; `HoleAt` asked for a run and is
unused (the close step can drop it). For steps 3 and 4 (A) and 5 and 6 (B):
the pilot's hypotheses are the facts at a round that the stratum's loop
(`writerWP_mergeUp_delJAE`) carries (`DelInvJT`'s tree and ranges, the
books) plus `HtInv` and `PathCached` at the descent's end, which
`ht_descendToHeight` and `writerWP_descendToHeight_path_cached` give.

2026-11-16, 23:14 to 23:35. Step 3, first part, prover l4a (LiveLoop.lean,
about 600 lines): the loop. `writerWP_afterDelete_live`: at a call of
`afterDelete key g 0` with `DelInvJAE`, `PutBook`, `HtInv` and `LiveHoleW key g 0`,
every run ends with `LiveEdges`, given `MergeLiveOK` (a merge at a round, from
the round's facts: the stratum's `DelInvJ` at a fuel, the books, `PathOK`, the
heights at the descent's end, keeps `LiveHoleW` one height up, or ends with
`LiveEdges`) and `CollapseLiveOK` (root collapse from the exit form). The exit
form `LiveExit`: `LiveEdgesH` with, after a merge, the hole only at the node that
collapse's descent finds (`SegRootW`). The loop (`writerWP_mergeUp_liveJW`) is
the stratum's `writerWP_mergeUp_delJW` with the hole, the heights
(`ht_descendToHeight`, `ht_merge_of_J`) and the books beside its invariant; the
exits are proved (`liveExit_round`): at the space root or under a segment leaf
the found node is the segment's root (`descend_exit_shape`, by `dhP_inner`), a
filled node meets `ChildOK`, and before any merge the hole is a leaf
(`found_leaf_of_h0`, the books). Choice (by rule, KISS): the hole at the call is
at height 0, the leaf's, so no separate leaf premise.
