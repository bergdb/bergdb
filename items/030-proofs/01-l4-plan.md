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

2026-11-16, 23:36 to 23:45. Step 3, second part, prover l4a (LiveMergeRoom.lean,
about 1,300 lines, about 400 of them near-copies of the pilot's writer-level
merge and round). `mergeLiveOK_of_full`: `MergeLiveOK` from `MergeLiveFullOK`,
which asks it only where the parent has no room or may compact (`¬ MergeRoom`).
Proved: every merge whose parent has room and no compaction, of nodes the
transaction made (taken back, `writerWP_mergeCleanup_frameV`) or not, into one
node (`liveEdgesH_mergeOne`) or into two (`liveEdges_mergeTwo`: no hole; the new
nodes are filled, halves of more than `mergeMax` klongs; the parent keeps its
number of live klongs, `live_len_mergeTwo`, the second node's compare value
being no other live one of the parent's, as `dw_mergeTail` shows for `d4`).
`writerWP_afterDelete_liveF`: `afterDelete` with premises `MergeLiveFullOK` and
`CollapseLiveOK` (and `MergeParamsOK`). The pilot's three lemmas are instances
of the room ones (`writerWP_mergeTail_liveRoom`, `writerWP_merge_liveRoom`,
`liveHoleW_merge_room`); the close step can drop them. Left in step 3: the full
parent (`mergeParent`'s `full`: `handleFull` of its last version and the
cascade, the hole below the chain, and R1 through the cascade).

2026-11-16, 23:15 to 23:47. Step 5, first part, prover l4b (coord-1116): the
leaf with room. `liveDel_room` (LiveDelLeaf.lean): a delete whose leaf keeps a
live klong and has room calls `afterDelete key g 0`, (g, 0) the leaf's cached
pair, from a state with `DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`;
its afterDelete is a hypothesis in that form, which is l4a's
`writerWP_afterDelete_live`'s, and `liveDel_room_live` composes the two: the
delete ends with `LiveEdges` given `MergeLiveOK` and `CollapseLiveOK`. The
heights reach the call through the walk (`HtJ0`: `HtJ` without the heights'
bound, which the stratum has not). R1 at the leaf (`holeAtW_leaf`,
LiveHoleLeaf.lean, about 560 lines) needed one fact the plan did not name: the
leaf's cached segment. The descent counts segments (`SegRd`: the books and the
kinds' walk give each node read a segment, its inner children the same, a
leaf's long segments the next; `dsrFold_seg`), so the leaf's segment is the
space root's plus the prefix's length; a successful descent has a segment below
the key's length, so it is the prefix's length (the space root's segment, 0 in
every run but no invariant of the model, is not needed). The descent then
follows the key's reading, whose nodes are on the walk's path
(`fromVisits_reach_leaf`, `nodeAt_of_reach`: the tree's one parent) and so
cached, and at height 0 it stops at the leaf. No stop rule fired. Left of step
5: the full leaf (its split and cascade with the hole, step 3's cascade).

2026-11-16, 23:46 to 23:58. Step 4, first part, prover l4a (LiveCollapse.lean).
`writerWP_collapseRoot_live`: from `DelInvJAE`, `PutBook`, the exit form after a
merge and `R3At` at its start, every run of `collapseRoot key g` ends with
`LiveEdges`, given `CollapseStepLiveOK` (a step at a hole root with one live
klong ends with the live counts). The loop is the stratum's (`collSteps_JW`)
with the live counts beside it. Its exits are proved: a leaf root; a root with
no only live klong, which, being the hole's, has two
(`two_le_live_of_onlyNone`, by `onlyLiveKlong`'s fold); then a segment leaf
names it or it is the space root (`liveEdges_of_segRoot`). After a step the
live counts hold and the next round returns. R3 (stop rule of section 7, step
4): the branch for a root the transaction made with no made-for entry needs a
fact over the transaction's earlier operations (a fresh segment holds only
this transaction's puts, and a key has one operation), well over 400 lines; so,
by the rule, a narrowed premise for that branch alone: `R3At key g c v`, at
collapse's start, the segment root that its first round finds, if made with no
made-for entry and inner, has no only live klong (step 0's C4: never ran). At a
later round the live counts hold, so the branch is harmless there.
`writerWP_afterDelete_liveR`: `afterDelete` with premises `MergeLiveOK`,
`CollapseStepLiveOK` and R3 after the merges' loop (`hR3`, a fact of the call's
state). The node-map lemmas of the steps are proved
(`liveEdges_collapseSpace`: the space root replaced by its child;
`liveEdges_collapseSeg`: a segment leaf's klong names the child instead).

2026-11-16, 23:58 to 2026-11-17, 00:00. Step 4, second part, prover l4a
(LiveCollapseStep.lean). `collapseStepLiveOK_of`: the collapse's step from
`CollapseSegFullLiveOK`, which asks it only at a segment root that existed
before the transaction whose segment leaf has no room for one more klong or
would compact (`replaceRoot`'s cascade at the leaf). Proved: at the space root,
`takeBackRoot` and `replaceRoot` (the child the new space root,
`liveEdges_collapseSpace`); below a segment leaf, `takeBackRoot` (the leaf's
klong pointed in place) and `replaceRoot` with room (a new klong of the same
compare value), both by `liveEdges_collapseSeg`. `writerWP_afterDelete_liveRF`:
`afterDelete` with premises `MergeLiveFullOK`, `CollapseSegFullLiveOK`,
`MergeParamsOK` and R3 after the merges' loop. Left of steps 3 and 4: the two
full cases. The collapse's has no hole (the leaf's klong names a filled child),
so `writerWP_appendKlongs_chainGL` applies as it stands, with the chain's facts
as `writerWP_replaceRoot_seg_cascadeF` (CollapseCascade.lean) derives them; the
merge's needs the cascade with the hole below the chain (R4) and R1 through it.

2026-11-16, 23:50, to 2026-11-17, 00:00. Step 6, first part, prover l4b. The
leaf at the space root emptied with room: after its bitmap the root is an empty
leaf that reaches nothing (`liveDel_emptyRootRoom`, LiveUpLeaf.lean, proved,
no obligation). R2's live part: `liveEdgesH_up`, the emptied chain's frame
(the tree's mirror `tReach_up_sub_tr`): after the chain leaves the tree and the
stop node keeps its other live klongs, the live counts hold but at the stop
node. The upward walks with the stop node's cached pair (LiveUpWalk.lean, about
920 lines, near-copies of `writerWP_deleteUpward_upT_getJMBK` and
`takeJ2_deleteUpward_upTMBKD`: their continuations get `ghOf`'s pair at a state
of the invariant, and the inner stop node's leaf flag). With `LiveCounts` at the
start the stop node is a segment leaf (`lebStop_false`), so the upward delete
calls `afterDelete` at (g, 0) like the leaf with room. A stall point found (R2's
heights): l4a's `writerWP_afterDelete_live` needs `HtInv` at the call; over
`putKv` the chain's take-backs keep the heights only with the checked copy's
checks (`ht_takeBackChk`: no other overlay node names the node taken back), so
`HtInv` at the stop node's call is not available over `putKv`. Ways: the
upward case over the checked copy (`putKvDelChk2`, its results equal by
`OpDelChk2ORJ`, proved), or an invariant over `putKv` that the checks verify.
Left in step 6: R1 at the stop node, the heights at its call, the full root and
the full stop node (with the cascade).

2026-11-17, 00:00 to 00:03. Step 4 done but R3, prover l4a
(LiveCollapseFull.lean, about 450 lines, about 330 of them a near-copy of the
tree's `writerWP_replaceRoot_seg_cascadeC`). `collapseSegFullLiveOK_holds`: at a
segment root below a full segment leaf, `replaceRoot`'s cascade keeps the live
counts: the room case's tree has them (`liveEdges_collapseSeg`), the cascade's
walk keeps them (`writerWP_appendKlongs_chainGL`, no hole), and the unlink of x,
out of reach after, changes none (`liveEdges_updN_unreach`).
`writerWP_afterDelete_liveFR`: `afterDelete` from the call's facts (`DelInvJAE`,
`PutBook`, `HtInv`, `LiveHoleW key g 0`) to `LiveEdges`, premises
`MergeLiveFullOK`, `MergeParamsOK` and R3 after the merges' loop. Left of steps 3
and 4: `MergeLiveFullOK` (the merge's parent full or compacting: `handleFull` of
its last version with the hole and its cascade; R4, and R1 through the cascade)
and R3 (narrowed, `R3At`).

2026-11-17, 00:04 to 00:10. Step 3's rest, R4 (prover l4a). The size of
`chainGLX`'s generalization: its walk (`writerWP_appendKlongs_chainGLX`, 1,570
lines) and LiveStepsX.lean's steps (850) take the exceptions' condition in
`edgeX_grow` and the steps' lemmas; a parameter for it means a copy of about
2,400 lines with the old ones as instances, and a live copy of the full node's
split (`writerWP_fullSplit_chainG`, 860 lines) on top: past the rule's 600 and
800. So, by section 7's rule, the narrower lemma: a full node's split whose
parent has room, no cascade (LiveSplitRoom.lean). `liveEdgesH_redirect`: the
hole x, named by q's klong k1, replaced by a fresh copy that q's klong names
instead: the hole is the copy after. `writerWP_handleFull_timeRoom_live`: a
full node that the transaction did not make, split in time with a last version
given (the merge's parent's, or a delete's leaf's), below a parent with room:
from the hole at x in the tree with x's node replaced by the last version, the
hole is at the copy (the new id) after; nothing else changes but the parent and
x. Shared with step 5's full leaf. Left for the merge's full parent: the space
split (no hole after), R1 through the parent's changed klong (the next round's
descent finds the copy), the merge's tail with `mergeParent`'s `full`, and the
cascade beyond a full grandparent.

2026-11-17, 00:10 to 00:15. R1 for the time split below a parent with room
(prover l4a, LiveRedirectDescent.lean): `descendToHeight_redirect`: after the
descent at (g, h) found x with its parent p and p's parent q inner, on a state
that reads alike above q (q's height too) where q's klong of the key's segment
names y, of height h + 1, the descent at (g, h + 1) ends at y (`dhP_redirect`,
`dhP_height`). With `writerWP_handleFull_timeRoom_live` it is the merge's full
parent's time split below a grandparent with room. Step 5's full leaf below a
parent with room needs the same kind of fact one level down (the descent at the
leaf's own height to the leaf's copy); `dhP_redirect`'s argument carries over,
its statement (an earlier descent ending two below q) does not.

2026-11-17, 00:02 to 00:18. Step 6, second part, prover l4b. The upward delete
with room above its leaf (`DelEmptyRoomM`), the live counts at the start:
`writerWP_del_upRoomLive` and its case `liveDel_upRoom` (LiveUpRoom.lean): the
stop node is a segment leaf (`lebStop_false`; the other two continuations are
void), and the delete calls `afterDelete key g 0`, (g, 0) the stop node's
cached pair, from a state with `DelInvJT`, `PutBook`, `HtInv` and
`LiveHoleW key g 0`: the live frame `liveEdgesH_up` when the stop node keeps a
live klong, or the space root left an empty leaf; R1 at the stop node
`holeAtW_stop` (LiveUpHole.lean): the key's descent at the walk's end is linked
in the tree (`dsrFold_linked`, `lteP_linked`), so it is the walk's path
(`linkedFrom_unique`); the stop node ends one segment's search
(`dsrFold_leaf_mid`); after the stop node's bitmap the key's descent is cut
there, so a successful descent at the stop node's segment finds it
(`holeAtW_cut`). `liveDel_upRoom_live` composes it with l4a's
`writerWP_afterDelete_live`: premises `MergeLiveOK`, `CollapseLiveOK` and
`UpHtWalk`, the heights through the upward delete's steps (an invariant from the
walk's end that note, take-back, unlink, bitmap and LE-b keep and that gives
`HtInv`): R2's heights, open (over `putKv` the take-back keeps `HtInv` only with
the checked copy's check that no other node names the node taken back). The
climb's fact at the stop node needed the upward walks again: LiveUpWalk.lean's
`...S` lemmas give it, and its `...G` lemmas are now their instances (about 900
lines fewer than two copies). Left in step 6: `UpHtWalk` (R2's heights), the
full root and the full stop node (the cascade).

2026-11-17, 00:20 to 00:22. Step 6, the space root emptied and full (prover
l4b): its last version without the key is one time klong
(`lastVersionGivenDel_ks_allIn`), so the root splits in time (in place if the
transaction made it) into an empty leaf, and the live counts hold
(`liveDel_emptyRoot`: the case `DelEmptyRootM` with room or full, no premise).

2026-11-17, 00:16 to 00:25. Prover l4a, the last pieces, and where the rest
stands. LiveSplitRoom2.lean: `writerWP_handleFull_timeRoom_liveGh`, the time
split's lemma with the copy's entry in `gh` (x's: the copy's segment and height
are the node's), for R1's height of the copy. Not done: composing these into
`MergeLiveFullOK`. What it takes (my estimate 1,000 to 1,500 lines): (1) the
merge's tail with both of `mergeParent`'s branches (`writerWP_mergeParent_cases`;
today's room tail, `writerWP_mergeTail_liveRoom`, selects the room branch by
`MergeRoom`, which `¬ MergeRoom` does not exclude), its full branch through
`writerWP_handleFull_timeRoom_liveGh` from the merged tree with the parent's
last version (its tree as `treeOK_mergeOneAfter`, `treeOK_mergeTwoAfter`; its
live form as `liveEdgesH_mergeOne`, `liveEdges_mergeTwo`, with
`mergeFullLast_liveAt`, `mergeFullLast_lookup`), then the cleanup with the
parent, l and r out of reach (a reach lemma beside `liveEdgesH_redirect`); (2)
the round: R1 by `descendToHeight_redirect`, the copy's height from the heights'
cache at q after the merge (`ht_merge_of_J`'s `HtInv`, `HtCache`'s `NodeHt` for
q's live klong to the copy: height h + 1, the ids above B unknown to H), q's
search by the spec (`KNode.searchLte_spec`: q's klongs as before but k1 naming the
copy); (3) the rest as an obligation: the parent's space split (no hole, but the
divider's range as `writerWP_fullSplit_chainG`'s `hhalves`), the parent made by
the transaction (in place), a parent that is the space root or a segment root,
and a grandparent without room (the cascade, R4's general case).

2026-11-17, 00:23 to 00:27. Step 5, second part, prover l4b: the full leaf
that the transaction made, its last version without the key within a split's
bound (`DelFullTimeM` and the leaf made): it splits in time in place
(`writerWP_appendDeleteKlong_fullMade`), the leaf's node its last version, so
the room case's argument applies (`liveHoleW_leafChange`, the room case's hole
made a lemma for any change of the leaf alone that keeps its kind and its other
live klongs): `liveDel_fullMade`, and with l4a's loop `liveDel_fullMade_live`.
Left of step 5: the full leaf not made by the transaction (its time split's copy
is the hole: l4a's `writerWP_handleFull_timeRoom_live` below a parent with room,
and R1 at the copy), the space splits (no hole), and the cascades.

2026-11-17, 00:28 to 00:40. Step 5, the full leaf not made by the transaction,
prover l4b: split in time below a parent with room, below the space root
(`DelFullTimeRoomM`): l4a's `writerWP_handleFull_timeRoom_liveGh` gives the live
counts but at the copy, and R1 at the copy (`holeAtW_copy`,
LiveDelFullCopy.lean): the key's descent after the split is the walk's but at
the parent, whose search now names the copy: in the last segment's tree
(`lteP_redirect`; the run's step at the parent went to the leaf, since the leaf
has one parent, `nodeAt_of_reach`), or the parent's segment search when the leaf
is a segment root (`KNode.add_key_searchEq`). `liveDel_fullTimeRoom` and, with
l4a's loop, `liveDel_fullTimeRoom_live`. Left of step 5: the space split (no
hole after, its halves filled), the parent full (the cascade, R4), the leaf at
the space root, and the made leaf's space split.

2026-11-17, 00:27 to 00:40. Step 3's rest, first part, prover l4c
(`LiveMergeTail.lean`; LiveMergeRoom.lean's room lemmas generalized, the old ones
their instances, about 300 lines added in all). `MergeLiveFullOK` asked every merge
whose parent may lack room for some merge (`¬ MergeRoom`); but `mergeParent` takes
its branch with room whenever the merge it makes fits (`MergeParentRoom`: its `need`
and no compaction, for the merge's own arguments). So the room proof now takes that
exact condition: `writerWP_mergeTail_liveRoomB` (the tail),
`writerWP_mergeTail_liveRoomR` (the tail from a state that reads as the merge's
start), `writerWP_merge_liveG` (the merge's reads up to its tail, the tail a
hypothesis), `liveHoleW_merge_G` (the round, given the tail where the parent goes
`full`). What is left is `MergeTailFullOK`: at a round with `MergeLiveOK`'s facts,
the merge's tail with the two nodes chosen and their facts, where `¬
MergeParentRoom`. `mergeLiveOK_of_tailFull` and `writerWP_afterDelete_liveTF`
(premises `MergeTailFullOK`, `MergeParamsOK`, R3). No stop rule fired.

2026-11-17, 00:44 to 00:55. Step 5, the full leaf's space split, prover l4b:
the leaf not made by the transaction, full with no bitmap of the transaction last
("bitmap.full"), its last version without the key above h, below an inner parent
with room for the halves' klongs (`DelFullSpaceRoomM`, LiveDelSpace.lean). Both
halves hold m live klongs and more (`halves_del_halfOK`, from
`halves_lastVersionGivenDel_live_fill`), so the split keeps the live counts with
no hole (`writerWP_handleFull_spaceRoom_live`, by `liveEdgesX_spaceSplit_gen`
from the start's counts: the halves hold the leaf's live klongs, the parent
gains one), and `afterDelete` starts from them (no R1 needed):
`liveDel_fullSpaceRoom` and, with l4a's loop, `liveDel_fullSpaceRoom_live`.
Not chosen: the cascade through `writerWP_appendKlongs_chainGL` above a full
parent, which needs a live copy of `writerWP_fullSplit_chainG`'s premises (its
860 lines; R4's rule). Left of step 5: the parent full (the cascade), the parent
a segment leaf or the leaf at the space root (a new root above the halves), the
made leaf's space split in place, and a compacting split ("bitmap.dead") of a
last version above h.

2026-11-17, 00:58 to 01:02. Step 5, the full leaf at the space root, prover
l4b: not made by the transaction (`DelFullRootM`, LiveDelRoot.lean), any branch
of the bitmap: a time split puts its last version without the key in a new root
(a leaf root asks no count of its own, `liveEdges_root_shrink`; then
`liveEdgesX_rootTimeStep`), a space split puts its halves (`HalfOK`) under a new
inner root of two live klongs (`liveEdgesX_rootSpaceStep`); the live counts hold
after with no hole (`writerWP_handleFull_root_live`): `liveDel_fullRoot` and,
with l4a's loop, `liveDel_fullRoot_live`. Left of step 5: the parent full (the
cascade), the parent a segment leaf, the made leaf's space split in place, the
made space root's space split, and a compacting split of a last version above h
below a parent.

2026-11-17, 00:41 to 01:12. Step 3's rest, second part, prover l4c
(`LiveMergeFull.lean`, about 2,000 lines; about 600 of them the room tail's preludes
again). `MergeTailFullOK` reduced to `MergeTailFullRestOK`, which asks it but in the
case `MergeFullTimeRoom`, now proved: a merge whose parent p, not made by the
transaction, goes `full` (`writerWP_mergeParent_fullB`) and splits in time (it
compacts, or its last version has at most `splitAbove` klongs), below its inner parent q
(depth d - 2) with room for one more klong and no compaction. The tail
(`writerWP_mergeTail_liveFullTime`): the merged tree with p's last version has the hole at
p (`liveEdgesH_mergeOne`, its tree `treeOK_mergeOneAfter`, l and r not reached
`mergeV_reach`, q reached by its path above p `tReach_of_pathLen_agree`), the time split
moves it to p's copy (`writerWP_handleFull_timeRoom_liveGh`), and the cleanup changes only
p, l and r, which are no longer reached (`redirect_reach`, `liveEdgesH_congr_reach`,
`writerWP_mergeCleanup_frameL`). The round (`writerWP_mergeTail_liveFullTimeRound`): R1
by `descendToHeight_redirect`; q's search at the key finds the copy (`descend_qsearch`:
the descent's step at q, `dhP_step`; `searchLte_add_key`); the copy's height is p's, one
above x's (`gradedL_get`); the path above q reads alike (the tail's frames of nodes and
of the heights' cache). `writerWP_afterDelete_liveTR`: premises `MergeTailFullRestOK`,
`MergeParamsOK`, R3. A merge into two nodes with the same parent
(`writerWP_mergeTail_liveFullTime2`): no hole before the split (`liveEdges_mergeTwo`), and
p's copy holds p's live klongs or more (`live_len_mergeTwo`), so q's link to it is filled
(`liveEdges_of_oneHole`). Left in `MergeTailFullRestOK`: p made by the transaction (split
in place; its tree is the room case's with p's last version, so the room tail would serve
if generalized over p's new node), p's space split, p the space root (d = 1) or a segment
root (q a segment leaf: R1 at the segment root), and q full or compacting (the cascade,
R4). No stop rule fired.

2026-11-17, 01:10 to 01:11. Step 5, the made leaf's space split in place,
prover l4b: the leaf made by the transaction, "bitmap.full", its last version
without the key above h, below an inner parent with room for the second half's
klong (`DelFullSpaceMadeRoomM`, LiveDelSpaceMade.lean): the leaf keeps the first
half, a new node the second, and both are `HalfOK`; the live counts hold after
with no hole (`writerWP_handleFull_spaceInPlaceRoom_live`, by
`liveEdgesX_spaceInPlaceStep`): `liveDel_fullSpaceMadeRoom` and, with l4a's
loop, `liveDel_fullSpaceMadeRoom_live`. Left of step 5: the parent full (the
cascade), the parent a segment leaf, the made space root's space split, and a
compacting split of a last version above h below a parent.

2026-11-17, 01:14 to 01:15. Step 5, the leaf below a segment leaf, prover l4b:
not made by the transaction, "bitmap.full", its last version without the key
above h, the segment leaf above with room for one klong
(`DelFullSegSpaceRoomM`, LiveDelSegSpace.lean): the halves (`HalfOK`) under a
new inner segment root of two live klongs, which the segment leaf names by the
leaf's klong; the live counts hold after with no hole
(`writerWP_handleFull_segSpaceRoom_live`, by `liveEdgesX_segSpaceStep`):
`liveDel_fullSegSpaceRoom` and, with l4a's loop,
`liveDel_fullSegSpaceRoom_live`. Left of step 5: the parent full (the cascade),
the made segment root's space split, the made space root's space split, and a
compacting split of a last version above h below a parent.

2026-11-17, 01:15 to 01:18. Step 5, the made segment root's space split, prover
l4b: the leaf made by the transaction, a segment root, "bitmap.full", its last
version without the key above h (`DelFullSegSpaceMadeM`,
LiveDelSegSpaceMade.lean): it keeps the first half, a new node the second, under
a new segment root that the segment leaf's klong names instead, in place (no
room asked); the live counts hold after with no hole
(`writerWP_handleFull_segSpaceMade_live`, by `liveEdgesX_segSpaceInPlaceStep`):
`liveDel_fullSegSpaceMade` and, with l4a's loop, `liveDel_fullSegSpaceMade_live`.
Left of step 5: the parent full (the cascade), the made space root's space split,
and a compacting split of a last version above h below a parent.

2026-11-17, 01:18 to 01:20. Step 5, the made space root's space split, prover
l4b: the leaf at the space root made by the transaction, "bitmap.full", its last
version without the key above h (`DelFullRootSpaceMadeM`, LiveDelRootMade.lean):
it keeps the first half, a new node the second, under a new inner root
(`writerWP_handleFull_rootSpaceMade_live`, by `liveEdgesX_rootSpaceInPlaceStep`):
`liveDel_fullRootSpaceMade` and, with l4a's loop,
`liveDel_fullRootSpaceMade_live`. Left of step 5: the parent full (the cascade),
and a compacting split ("bitmap.dead") of a last version above h, below a parent
or at a made root (a time split: the copy, or the leaf in place, is the hole).

2026-11-17, 01:13 to 01:22. Step 3's rest, third part, prover l4c
(`LiveMergeMade.lean`, about 1,000 lines; about 450 of them the room tail again, with the
parent's change and the heights' cache's frame). `MergeTailFullRestOK` reduced to
`MergeTailFullRest2OK`, its case `MergeFullMadeTime` proved: the merge's parent p, made by
the transaction, goes `full` and splits in time, which is in place
(`writerWP_handleFullWith_timeInPlace_nodesL`: p's node becomes its last version, nothing
else changes). So the room proof's steps carry over with `mergeFullLast` for
`mergeParentNode` (`writerWP_mergeTail_liveMade`, one node or two), and the next round's
descent finds p (`writerWP_mergeTail_liveMadeRound`, `descendToHeight_up`, the path's
reads and heights alike from the tail's frames, `writerWP_mergeCleanup_ghp` for p's).
`writerWP_afterDelete_liveTR2`: premises `MergeTailFullRest2OK`, `MergeParamsOK`, R3.
Left: p's space split (made, in place, or not), p not made and the space root (d = 1) or
a segment root (R1 at the root), and q full or compacting (the cascade, R4). No stop rule
fired.

2026-11-17, 01:00 to 01:25. R2's heights, prover l4d: `UpHtWalk` is false for
every context, oracle and B (`upHtWalk_false`, `not_exists_upHtWalk`,
LiveUpHtFalse.lean), so `liveDel_upRoom` and `liveDel_upRoom_live` never apply
as stated. Its take-back step asks Ju kept by `takeBack x q k` for every x, q
and k, from every state that `HtJ0` gives Ju. A state of three nodes of the
transaction, q and z inner nodes of height 1 that both name the empty leaf x
(x made by a split), meets `HtJ0` for every context; `takeBack x q 0` succeeds
and leaves z, not taken back, naming x, taken back, so `HtCache` fails at z.
The checked copy's `checkFree` is what excludes that state (`ht_takeBackChk`);
at the runs, the loop's take-backs pass it (`step_takeBack`, `HoldInv`). The
true form needs the heights at the stop node's call from the walk's start and
the loop's frame, not an invariant of every step (next).



2026-11-17, 01:21 to 01:26. Step 5, the space split's cascade, prover l4b. After
a space split no hole is left (both halves `HalfOK`), so R4's hole below the
chain does not arise: the parent's klongs to the halves go up through
`writerWP_appendKlongs_chainGL` (s = 0), whose live post needs only the live
counts of the tree with the halves in place and the parent's klongs put
(`liveEdgesX_spaceSplit_gen` from the start's), then the leaf left behind is not
reached (`liveEdges_updN_unreach`): `writerWP_handleFull_spaceChain_live`
(LiveDelSpaceChain.lean). Its chain premises come from the walk's `PathOK` and
`RangeOrder` as in `writerWP_appendDeleteKlong_full_invT` (`rangeG_of_rangeOrder`,
`lenG_of_splitAbove`, `pathOK_dist`; the divider in the parent's range by
`mrg_child_range`). The case: the leaf not made by the transaction,
"bitmap.full", above h, below an inner parent with or without room
(`DelFullSpaceChainM`): `liveDel_fullSpaceChain` and, with l4a's loop,
`liveDel_fullSpaceChain_live`. Left of step 5: the time split's cascade (R4), the
made leaf's and the segment root's space split below a full parent (the same
route), and a compacting split of a last version above h.

2026-11-17, 01:25 to 01:30. R2's heights, true form, prover l4d: the upward
delete with room keeps the live counts with no heights premise
(`liveDel_upRoom_liveH`, LiveUpRoomH.lean; premises `MergeLiveOK` and
`CollapseLiveOK`), and `liveDel_upRoomH` calls `afterDelete` with `HtInv` from
no premise. The heights at the stop node's call come from `HtInv` at the upward
walk's start w3 through the loop's frame (`htInv_upFrame`, LiveUpHt.lean, about
230 lines): between w3 and the call only the chain and the stop node change; a
chain node the transaction made is taken back, and its one holder is its tree
parent (`liveHolder_unique`, from `TakeJ2` at w3), the next chain node or the
stop node, whose klong to it is gone; another chain node is unlinked to its
version before the transaction, which names only nodes below B (`OldBelowN`),
never taken back; the stop node's version before the transaction is unchanged
(`bitmapOf_prefix`, `retFormS_prefix`). The walks were not touched: the copy of
`writerWP_del_upRoomLive` (`writerWP_del_upRoomLiveH`, about 330 lines, one B
for the books and the kinds) passes the frame that `takeJ2_deleteUpward_upTMBKDS`
already gives its continuation. R2's heights are done for the upward delete with
room; the full stop node (the cascade) is left with step 6.

2026-11-17, 01:23 to 01:31. Step 3's rest, fourth part, prover l4c
(`LiveMergeSpace.lean`, about 1,200 lines; about 700 of them the full tails' preludes and
l4b's space split again). `MergeTailFullRest2OK` reduced to `MergeTailFullRest3OK`, its
case `MergeFullSpaceRoom` proved: the merge's parent p, not made by the transaction, goes
`full` and splits in space, below its inner parent q with room for the halves' klongs and
no compaction. A space split leaves no hole: p's last version has more than `splitAbove`
klongs, so p was filled after the merge though it lost a klong (`liveEdges_of_oneHole`;
into two nodes there is no hole before, `liveEdges_mergeTwo`), and its halves are `HalfOK`
(`halves_mergeLast`, from `halves_facts_nil` and `halves_live_fill`); l4b's split lemma
carries over to the merged tree (`writerWP_handleFull_spaceRoomV_live`), and the cleanup
changes only p, l and r, which are no longer reached. No descent is needed after
(`writerWP_mergeTail_liveSpace`, `writerWP_mergeTail_liveSpaceRound`).
`writerWP_afterDelete_liveTR3`: premises `MergeTailFullRest3OK`, `MergeParamsOK`, R3.
Left: p not made and the space root (d = 1) or a segment root (q a segment leaf; a time
split needs R1 at the root; a space split needs l4b's segment-root split on the merged
tree), q full or compacting (the cascade, R4), and p made and split in space (in place,
l4b's `writerWP_handleFull_spaceInPlaceRoom_live` on the merged tree). No stop rule fired.

2026-11-17, 01:28. Step 6, R2's heights, prover l4b: `UpHtWalk` (00:18's premise
of `liveDel_upRoom` and `liveDel_upRoom_live`) is false for every context, oracle
and B (prover l4d's `upHtWalk_false`, LiveUpHtFalse.lean: a take-back from an
`HtJ0` state where another node names the node taken back keeps no heights). So
`liveDel_upRoom_live` never applies as stated; its true form (`HtInv` at the stop
node's call from the walk's start and the loop's frame) is l4d's. No step of l4b
builds on `UpHtWalk`.

2026-11-17, 01:29 to 01:37. Step 5, the space split's cascade, the other
branches, prover l4b (LiveDelSpaceChain2.lean): the made leaf split in place
below an inner parent (`writerWP_handleFull_spaceInPlaceChain_live`, the parent's
one klong to the second half, `liveEdgesX_spaceInPlaceStep`) and the segment root
not made below its segment leaf (`writerWP_handleFull_segSpaceChain_live`, the
segment leaf's klong to the new segment root, `liveEdgesX_segSpaceStep`), each
through `writerWP_appendKlongs_chainGL`: `liveDel_fullSpaceMadeChain_live`
(`DelFullSpaceMadeChainM`) and `liveDel_fullSegSpaceChain_live`
(`DelFullSegSpaceChainM`). With the room cases, the space root's and the made
segment root's (no cascade), every space split of the full leaf is proved, given
l4a's loop. Left of step 5: the time split's cascade (R4), and a compacting split
of a last version above h.




2026-11-17, 01:39 to 01:41. Step 5, the compacting split, prover l4b
(LiveDelFullDead.lean): a full leaf whose bitmap compacts ("bitmap.dead",
"bitmap.inplace.dead") splits in time whatever its last version's size; the split
is in space only on "bitmap.full" (`writerWP_appendDeleteKlong_full_ofP`, the path
given to the continuation; `compact_time_of_path`). `DelFullTimeGM` widens
`DelFullTimeM`'s size bound by the compacting path, and the time cases carry over
unchanged otherwise: `liveDel_fullMadeG_live` (made, in place) and
`liveDel_fullTimeRoomG_live` (not made, below a parent with room). The full leaf's
cases are now all proved but one, given l4a's loop: the leaf not made, split in
time, its parent without room for the copy's klong (the cascade with the copy the
hole below the chain, R4).

2026-11-17, 01:33 to 01:45. Step 3's rest, fifth part, prover l4c. Which full-parent
merges occur on step 0's runs: step 0's checker with each merge whose parent goes `full`
classified by its notes (`/Users/f/fl/bench/2026-11-16/night/l4c/runs/merge-full-cases.lean.txt`,
2 min 30 s, the same 15 families). Of 1,134 full-parent merges: the parent a segment root
split in time below its segment leaf, no cascade, 454 (233 into one node, 221 into two);
the same with a cascade, 194; made, split in time in place, 162 (proved); below an
inner parent, split in time, no cascade, 100 (proved); the space root split in time
(d = 1), 81; a segment root split in space, 67 without a cascade and 60 with; the space
root split in space, 12; below an inner parent split in space, 2 (proved); in time with
a cascade, 2. So the segment root case was taken next: `MergeTailFullRest3OK` reduced to
`MergeTailFullRest4OK`, its case `MergeFullTimeRoomG` proved (p not made, split in time,
below q, a segment leaf or inner, with room; one node or two). R1 at the segment root
(`descendToHeight_redirectSeg`, LiveMergeFull.lean): the round's descent below the segment
root is one step (q, a leaf, cannot be inner on it), so p is the segment root and q the
leaf above; at the next round the segment search reads alike up to q, q's long klong now
names the copy (`KNode.add_key_searchEq`), and the descent stops at the copy, of height
h + 1. Into two nodes the copy is filled under the segment leaf too
(`writerWP_mergeTail_liveFullTime2G`, by `childOK_grow`). The round lemma
`writerWP_mergeTail_liveFullTimeRoundG` takes both; the earlier ones are its instances.
`writerWP_afterDelete_liveTR4`: premises `MergeTailFullRest4OK`, `MergeParamsOK`, R3.
Left: p not made and the space root (d = 1; 93 on the runs), a segment root's space split
(127), q full or compacting (the cascade, R4; 196), and p made and split in space (0 on the
runs). No stop rule fired.

2026-11-17, 01:44 to 01:50. Step 7, the assembly, prover l4b (LiveAssembly.lean):
`invGetScanOK_merges_noL4`, TP7, TP10 and TP11 for Java's parameters without
`l4`, a corollary of `invGetScanOK_merges_l4L` with `htbL` proved
(`takeBelowFuelDelSL_holds`) and `l4L` from `liveDelSL_of_pieces`. Its premises
besides `hp` and `hth` are `l4`'s open narrow pieces, each at the induction's runs
(`RunTreeQ p (LatestQD p)`): `MergeTailRuns` (l4c's `MergeTailFullRest3OK` at the
runs' contexts), `R3Calls` (R3 at the calls of `afterDelete`, with the call's
facts), and in the delete cases' form (`DelCaseLive`: from the first stratum's
start to the call of `afterDelete` with the hole) the full leaf split in time below
a parent without room (`DelFullTimeCascM`, R4) and the upward delete whose stop
node has no room (`DelEmptyCascM`, prover l4e's). `liveDelSL_of_pieces`: `SJ0` from
the induction's facts (as `jointHtJ_reached0L` builds it), `TakeJ2` is `J2At`, and
the cases: the noop and the key with no leaf excluded by the open case,
`delMerge_cover`, the emptied leaf by `delEmptyM_split` and `delEmptyOther_split`
(l4d's `liveDel_upRoomH`, `liveDel_emptyRoot`, the premise), the bitmap with room
(`liveDel_room`), the full leaf by `delFullM_cover` into nine cases, all proved but
R4. `afterDelete` at every call by `writerWP_afterDelete_liveTR3`
(`afterDelete_live_runs`). When a piece lands, its premise goes.

(127, 60 of them with a cascade), q full or compacting (the cascade, R4; 256 in all: 196
in time, 60 in space), and p made and split in space (0 on the runs). No stop rule fired.

2026-11-17, 01:46 to 01:50. Step 3's rest, sixth part, prover l4c. `MergeTailFullRest4OK`
reduced to `MergeTailFullRest5OK`, its case `MergeFullSpaceG` proved: a segment root, not
made, split in space below its segment leaf with room (67 on the runs). l4b's segment-root
split on the merged tree (`writerWP_handleFull_segSpaceRoomV_live`, with the nodes reached
after from `treeOK_segSpaceStep`); the space tail and its round now take the split as a
premise (`SplitStepOK`; `writerWP_mergeTail_liveSpaceG`, `writerWP_mergeTail_liveSpaceRoundG`;
`splitStepOK_spaceRoom` and `splitStepOK_segSpace` its instances; the earlier lemmas are
instances, statements unchanged). `writerWP_afterDelete_liveTR5`: premises
`MergeTailFullRest5OK`, `MergeParamsOK`, R3. Left: p not made and the space root (d = 1;
93 on the runs: a time split makes the copy the new space root, `newSuperRoot`, R1 at the
root; a space split a new root above the halves, no hole), q full or compacting (the
cascade, R4; 256 on the runs, 196 in time and 60 in space; for a space split l4b's
cascade lemmas for the leaf may
serve on the merged tree, as its split lemmas did; a time split's cascade keeps the hole
below the chain, R4's general case), and p made and split in space (0 on the runs). With
this part the proved cases cover 785 of the 1,134 full-parent merges on the runs (69%);
left 349: the cascade 256, the space root 93. No stop rule fired.

2026-11-17, 01:53. Step 7, a successor as l4c's fifth part landed:
`invGetScanOK_merges_noL4b`, `invGetScanOK_merges_noL4` with `MergeTailRuns4`
(l4c's `MergeTailFullRest4OK` at the runs' contexts) for `MergeTailRuns`, by
`mergeTailFullRest3OK_of_rest4` (`mergeTailRuns_of_4`).

2026-11-17, 01:37 to 01:56. Step 6, the stop node at the space root, prover l4e
(`LiveUpCascWalk.lean`, about 620 lines, near-copies; `LiveUpCascRoot.lean`, about 650
lines, about 400 of them near-copies of the stratum's walk and of the tree's root swap).
`liveDel_upRoot_live`: a delete that empties its leaf, not the space root, whose climb
reaches the space root (`DelEmptyUpRootM`: every node strictly between the root and the
leaf on the key's path empties, and the root was not made by the transaction), keeps the
live counts, the root with room or full, with no premise and no heights. The stop node is
the root, a segment leaf (`lebStop_false` excludes an inner one), which asks no count: after
its bitmap the live counts hold (`liveEdgesH_up`, the root the only hole), and a full root
splits (`writerWP_upCasc_root_live`: l4b's `writerWP_handleFull_root_live` at the state whose
root has its bitmap, moved to the writer's state by `writerWP_handleFullWith_root_swap`, as the
tree's `writerWP_upCasc_root_j2S` does). With no hole the merges' loop merges nothing
(`writerWP_afterDelete_none`), so neither `MergeLiveOK` nor `CollapseLiveOK` nor the stop
node's pair is needed. The walk (`takeJ2_deleteUpward_stepMBKGDS`, `writerWP_deleteUpward_stepJGS`:
the stratum's with the climb's stop fact, the stop node's `gh` entry and an inner stop node's
leaf flag given to the continuations) pins the stop node to the root. Choice (R4, narrower
lemmas): the case by the path (`UpToRoot`), not by `DelEmptyCascM`, whose stop candidate
need not be the climb's stop. Left of step 6: the root made by the transaction (in place),
and a stop node below the root that is full (its split and cascade; a time split's copy is
the hole, which needs the stop node's pair, now given by the new walk).

2026-11-17, 01:52 to 01:59. Step 3's rest, seventh part, prover l4c (`LiveMergeRoot.lean`,
about 900 lines, about 450 of them the time tail's prelude again). `MergeTailFullRest5OK`
reduced to `MergeTailFullRest6OK`, its case `MergeFullTimeRoot1` proved: a merge into one
node whose parent p is the space root, not made, split in time (52 on the runs). The copy
becomes the space root (`writerWP_handleFullWith_time_root_gh`, `newSuperRoot`,
`writerWP_newSuperRoot_frameG`) and the hole (`liveEdgesH_newRoot`: the reached nodes are
the copy and the ones reached before but p; `writerWP_handleFull_timeRoot_live`); the
cleanup changes nothing reached; the next round's descent starts at the new space root
and stops there (`descendToHeight_newRoot`: p, inner, at depth 0 is not above a segment
leaf, so the key's segment is the first). `writerWP_afterDelete_liveTR6`: premises
`MergeTailFullRest6OK`, `MergeParamsOK`, R3. On the runs the proved cases now cover 837 of
the 1,134 full-parent merges (74%); left 297: the cascade 256, the space root split in
time into two nodes 29 or in space 12. No stop rule fired.

2026-11-17, 02:00. Prover l4c stops, by section 7's size rule: its additions for
`MergeLiveFullOK` are about 6,500 lines (LiveMergeTail, LiveMergeFull, LiveMergeMade,
LiveMergeSpace, LiveMergeRoot; LiveMergeRoom's room lemmas generalized), about 3,000 of
them near-copies of the merge tail's prelude (the reads, the new nodes, the books up to
`mergeParent`) in its five tails. State for a successor: `MergeLiveFullOK` follows from
`MergeTailFullRest6OK` (`writerWP_afterDelete_liveTR6`; the chain of reductions
`mergeLiveFullOK_of_tailFull`, `mergeTailFullOK_of_rest`, `..._of_rest2` to
`..._of_rest6`). Left in it, with the runs' counts of step 0's families (1,134 merges with
a full parent; 837 in the proved cases): the cascade, q full or compacting (256: 196 time
splits, mostly a segment root below a full segment leaf, the hole below the chain, R4's
general case; 60 space splits, no hole, for which l4b's leaf cascade
`writerWP_handleFull_spaceChain_live` and its segment-root cousins should carry over to
the merged tree as `writerWP_handleFull_spaceRoomV_live` did, with the divider's range
`hrK` from `hhalves_of_sorted`'s last part); the space root split in time with a merge
into two nodes (29; `writerWP_mergeTail_liveFullTime2G` with
`writerWP_handleFull_timeRoot_live`, no descent) or in space (12; a new space root above
the halves, no hole); and p made and split in space, in place (0). Before more cases: fold
the five tails' common prelude into one continuation lemma (about 1,000 lines fewer), and
give the round lemmas one shared derivation of the tail's facts.

2026-11-17, 01:58 to 02:04. Step 6, the stop node without room, prover l4e
(`LiveUpCascCall.lean`, about 490 lines, most of them near-copies of the stratum's walk
and of l4d's `writerWP_del_upRoomLiveH`). l4b's premise `hCasc` (`DelCaseLive …
DelEmptyCascM`) reduced to one narrow obligation, `UpCascCallOK`: at the upward loop's
end, a full segment-leaf stop node's bitmap (its split, maybe a cascade) ends at the
call's facts (`DelInvJT`, `PutBook`, `HtInv`, `LiveHoleW key g 0`, (g, 0) the stop
node's pair). `delCaseLive_emptyCasc` (premise `UpCascCallRuns`, the obligation at the
runs) and `invGetScanOK_merges_noL4U` (`invGetScanOK_merges_noL4` with it for `hCasc`).
`DelEmptyCascM`'s stop candidate need not be the climb's stop, so the walk
(`takeJ2_deleteUpward_stepMBKGDS`) splits by the room at the climb's stop: with room,
l4d's argument (`liveEdgesH_up`, `holeAtW_stop`, `htInv_upFrame`) over the new walk;
full, the obligation; an inner stop node is excluded by the live counts. Next: the
obligation at the space root (01:56's argument, with the heights through the swap),
then the space splits below it.

2026-11-17, 01:56 to 02:00. R3Calls checked, prover l4b. No Lean counterexample
found within the time box; what was found:

- At the runs R3 holds, by key order. A delete that reaches `afterDelete`
  removes a key that existed before its transaction (a transaction's keys are
  strictly increasing, `sortedKeys`, so no key is put and deleted in one
  transaction). Every segment root on such a key's path is a node from before
  the transaction, or a node the transaction made by a split or a merge with a
  made-for entry: `split.space2` and `split.space3` set `some x`;
  `split.space2.inplace`, `split.space3.inplace` and a merge's node copy
  `replacedBy` of a made node, which has an entry when that node lies on an old
  key's path. A node with no made-for entry (`setMadeFor _ none`) arises only
  in a segment tree under a prefix new in the transaction, which holds only
  keys put in it, none of which a later delete of the same transaction names.
  R3At asks `madeFor.lookup x = none` of the root it finds, so at the runs it
  holds vacuously. Probe: the step-0 checker with one transaction that makes a
  new segment, splits it in place and deletes under that prefix is not within
  reach (its operations are not sorted), as the argument says.
- `R3Calls` as stated (as `writerWP_afterDelete_liveTR3`'s `hR3`) asks R3At at
  every state with the call's facts (`DelInvJT`, `PutBook`, `HtInv`,
  `LiveHoleW`), and none of these mentions made-for entries (`PutInv`,
  `PutInvG`, `RangeOrder`, `InnerChildrenExist`, `PutBase`, `PutBook`, `Book`,
  `KdInv`, `TakeJ2`). A state whose segment root is made by the transaction,
  has no made-for entry and two live klongs, one the hole leaf, the other a leaf
  that fits it in one node, would run the merge into one node and stop there
  with R3At false. I believe `R3Calls` is false at such unreached states (as
  `UpHtWalk` was), but did not build one: a state meeting `DelInvJT` is large.
- The restatement that follows: R3 at the calls given the made-for fact,
  "segment g's root on the key's path is from before the transaction or has a
  made-for entry", which the merges' loop keeps (a split of the root copies its
  entry) and which makes R3At vacuous; the fact itself at the calls is the key
  order argument above, an obligation of the delete's walk (the stratum's
  facts do not carry made-for entries today).

2026-11-17, 02:01 to 02:08. R3's fix and R4 narrowed, prover l4b. The fix of
R3 (the coordinator's ask): it does not fit tonight. R3At needs a made-for fact at
`afterDelete`'s call and no fact the case theorems hand to it carries made-for
entries, so every afterDelete form with only those facts (l4a's `CollapseLiveOK`,
`hR3` of TR3 to TR6, `R3Calls`) is believed false at unreached states. A premise
"R3 at the delete's own call" in the cases' continuation form is not narrow (it
subsumes the case theorems: two continuation statements about one run do not
combine). The fix is an invariant carried from the delete's start to the call:
a reached node that the transaction made with no made-for entry names only such
nodes (no-made-for nodes arise only in segment trees under prefixes new in the
transaction), and the deleted key's leaf is old or has an entry (key order); then
the segment root on the key's path is old or has an entry, R3At is vacuous, and
the merges' loop keeps it (a split of the root copies its entry). The invariant
must be kept by every writer step, like MFB (MadeForOld.lean) but on links: days.
No Lean counterexample: a concrete state meeting `DelInvJT` is beyond tonight.
R4 narrowed (LiveAssembly2.lean): the leaf's time split below a parent without
room has its copy filled (`ChildOK` at the copy, m live klongs or more below an
inner parent, any below a segment leaf: no hole) or a hole. Filled: through the
cascade as the space splits (`writerWP_handleFull_timeChain_live`: the tree with
the leaf's node its last version meets `LiveEdges`, `liveEdges_of_holeChild`;
then `liveEdgesX_timeSplit_gen` and `writerWP_appendKlongs_chainGL`),
`liveDel_fullTimeChainF`. Left of R4: `DelFullTimeHoleM` (the copy below an inner
parent, fewer than m live klongs), `delCaseLive_timeCasc_of_hole`.
`invGetScanOK_merges_noL4c`: premises `hp`, `hth`, `MergeTailRuns6` (l4c's
`MergeTailFullRest6OK`), `R3Calls` (believed false), `DelFullTimeHoleM`,
`DelEmptyCascM`.

2026-11-17, 02:05 to 02:08. Step 6, the obligation at the space root, prover l4e
(`LiveUpCascRootH.lean`, about 400 lines, about 170 of them 01:56's root lemma's
prelude again). `upCascCallOK_of_below`: `UpCascCallOK` holds where the stop node is
the space root not made by the transaction, so it is left only below the root or at a
made root (`UpCascCallBelowOK`). After the root's split no node is under the fill, so the
hole's form holds for the stop node's pair; the tree's facts by `upCascJ2OKT_holds`, the
books by `putBook_appendDeleteKlong`, and the heights (`writerWP_upCasc_root_ht`): at the
state whose root has its bitmap, `htInv_upFrame` gives `HtInv` from the walk's start, the
books by `book_putNode`, and `ht_handleFull` gives it after the split (the root a leaf, the
last version's klongs its live ones, not taken back), moved by the swap. Corollary
`invGetScanOK_merges_noL4bU` (l4b's `invGetScanOK_merges_noL4b` with
`UpCascCallBelowRuns` for `hCasc`, by `upCascCallRuns_of_below` and
`delCaseLive_emptyCasc`).

2026-11-17, 02:09 to 02:15. Step 6, the stop node below the root split in space, prover
l4e (`LiveUpCascBelow.lean`, about 630 lines, about 370 of them the tree's below-root swap
prelude, `writerWP_upCasc_below_delST`, again). `writerWP_upCasc_below_spaceH`: a full stop
node X (D + 1) below the space root, not made by the transaction, split in space with no
compaction (a last version of more than `splitAbove` klongs), ends with the heights and the
live counts, no hole. At the state whose stop node has its bitmap (S') the tree is the
start's without the chain, and S' is filled (it holds a half's live klongs, `HalfOK`,
`liveAt_length_le`), so the live counts hold there (`liveEdgesH_up`,
`liveEdges_of_oneHole`); l4b's `writerWP_handleFull_spaceChain_live` (inner parent) or
`writerWP_handleFull_segSpaceChain_live` (the stop node a segment root) take the split and
its cascade, with the chain's ranges and lengths as the tree's swap has them; the heights
by `htInv_upFrame` and `ht_handleFull` at that state; all moved by the swap.
`upCascCallBelowOK_of_rest`: `UpCascCallBelowOK` from `UpCascSplitRestOK`, the cases left at
the stop node's split (after the bitmap's note): a split in time (the copy, or the stop
node made by the transaction, is the hole), a made stop node's split in space in place,
and a made space root. `upCascCallRuns_of_rest` at the runs; no new top corollary (the
coordinator's word, 02:10: none more carrying `R3Calls`).

2026-11-17, 02:16 to 02:22. Step 6, the made stop node's split in time, prover l4e
(`LiveUpCascMade.lean`, about 720 lines, about 330 of them the swap prelude again for the
heights). `writerWP_upCasc_below_madeTime`: a full stop node below the space root that the
transaction made, split in time in place (compacting or not), becomes its last version
without the chain's klong, with the live klongs its bitmap would leave: the live counts hold
but at the stop node (`liveEdgesH_up`), and the merges' descent at its pair finds it
(`holeAtW_stop`, the key's path given as the walk's from its start: `linkedFrom_of_nodes`;
the segments from the kinds after the split, `kd_handleFull`). `writerWP_upCasc_below_ht`:
the heights after any split of a stop node below the root (the swap, `htInv_upFrame`,
`ht_handleFull`). `upCascSplitRestOK_of_rest2`: `UpCascSplitRestOK` from
`UpCascSplitRest2OK`, its cases left: a stop node not made split in time (the copy the
hole, below a parent with room or with the cascade), a made stop node's split in space in
place, and a made space root; at the runs `upCascCallRuns_of_rest2`.

2026-11-17, 02:23 to 02:27. Step 6, the made stop node's split in space, prover l4e
(`LiveUpCascMade.lean`, about 400 lines more, most of them the swap prelude again).
`writerWP_upCasc_below_madeSpaceH`: a full stop node below the root that the transaction
made, split in space in place, leaves no hole: at the state with its bitmap it is filled
(it holds a half's live klongs), and l4b's in-place lemmas take the split and its cascade
(`writerWP_handleFull_spaceInPlaceChain_live` below an inner parent,
`writerWP_handleFull_segSpaceMade_live` below a segment leaf). `upCascSplitRest2OK_of_rest3`:
left `UpCascSplitRest3OK`, a stop node below the root not made by the transaction split in
time (the copy the hole, below a parent with room, or with the cascade: 030-01's R4) and a
made space root; `upCascCallRuns_of_rest3` at the runs.
