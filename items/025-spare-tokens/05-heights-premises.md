# 025-05. The heights' premises htb, hMSF and hCoF: the plan

Created 2026-11-15 by Frans Lundberg. Status: part 1 done (the plan
written 2026-11-15, 12:39, by coord-1115's planning agent; part 1, steps 1
to 6, gated on the prover fit's branch 2026-11-15: the top theorem
`invGetScanOK_merges_noFit`, premises hp, hth, htb, l4); part 2 (`htb`)
started 2026-11-15 by the prover htb: step 7 reduced to `hchk` without
`htb` (`jointHtJ_reachedS`). Section 8 has the state.

The key tree's best top theorem on `main` since 2026-11-15, 11:17, is
`invGetScanOK_merges_free_noD4` (DeadTop.lean): TP7, TP10 and TP11 for
Java's parameters from the premises hp, hth, htb, l4, hMSF and hCoF.
Three of them, `htb`, `hMSF` and `hCoF`, say that the tree fits the fuel
inside an operation (006-26, section 4, group B). This entry is the
plan for them, as 025-04 was for `hU`; `l4` has its own plan in 024-12,
section 1.

The plan follows.


The scratch files of 2026-11-15 named below as /Users/f/fl/bench/2026-11-15/day/hplan/run/X.lean are kept in this entry's folder as
[05-heights-premises/](05-heights-premises/)X.lean.txt (FuelNext, P4Reading, RouteP, htb-sites-check and its output).

## 1. In short

Written 2026-11-15 by the planning agent of coord-1115 ("hplan").
Nothing is proved in the repo here; section 5 says what was tested on
runs. Route P's statements are type-checked in
/Users/f/fl/bench/2026-11-15/day/hplan/run/RouteP.lean, and route P is
proved in scratch for the first of its six consumers, the reading's case
of a delete with the merges (TP10): `opGetCaseOK_delMergeA`, with no
`MergeStepOK` and no `CollapseFitsOK`, in P4Reading.lean beside it
(1,575 lines, most of them copies of the old proofs; on the standard
axioms, no `sorry`). Scratch only: no file of the repo changed.

- **`hMSF` and `hCoF` can go the way of `hU`:** out, with no statement
  change, by a change of the consumer (route P, section 4.1). The heights
  are then not needed inside a delete for the reading, and neither is the
  bound across a delete's steps that delj found no local invariant for
  (024-12, section 1).
- **What they say.** After a merge of the merges' loop, and after a step
  of root collapse, the writer's tree fits the fuel: every segment tree
  is at most p.fuel deep. For every state that meets the loop's reading
  invariant (`DelInvF`), which carries no heights. Believed false as
  stated: a state exactly p.fuel deep meets it, and a merge can add a
  level (139 of 3,032 merges on runs did).
- **Where they are used.** Only to keep the reading invariant through
  the merges' loop and root collapse at the fixed fuel p.fuel + 1: in the
  obligations that four families of case lemmas (`DelStepsOK` and three
  sisters) ask for `afterDelete`, `mergeUp` and `collapseRoot`, and in
  `hchk`'s discharge.
- **Why they are not needed.** That fuel is the proof's choice: the
  writer's own descents use p.fuel and throw when it runs out. The
  reading at a fuel above the state's next id is always the true reading:
  the writer's tree is a tree whose nodes all have ids below the next id,
  so no chain of inner nodes is longer than that (the pigeonhole bound,
  P1, proved in scratch). So the merges' loop and root collapse keep the
  reading at such a fuel with no fit premise, and the fit at p.fuel is
  needed only at the operation's end, where it holds between operations
  and where the families' conclusions already ask for it.
- **The change:** the families' obligations over an invariant of the
  consumer's choice (P4), and the loops at a fuel above the next id
  (P3). The old families are instances; nothing proved changes.
- **Size of route P:** 6 steps, 1,750 to 3,500 lines, 10 to 19 prover
  hours; one night for two provers. It lands the top theorem with the
  premises `hp`, `hth`, `htb`, `l4`. An addition. Its first consumer is
  done in scratch, with no surprise: every step lemma took the new
  invariant with a few edited lines (section 6.1, step 1).
- **`htb`** (a delete takes back no node, found at its start, at the
  fuel's height or above) has a direct argument, the take-back sites
  (section 4.4), and every site held on runs (section 5: 4,335 nodes
  found and taken back, 0 failures). But it is in a circle today: the
  heights inside a delete that the argument needs come from the joint
  induction and `hchk`'s discharge, which use `htb` for the fit at the
  delete's start. Route P's invariant breaks the circle, so `htb` is a
  second part (steps 7 to 9), after route P: 2,500 to 5,000 lines, 18 to
  29 hours.
- **One argument for all three** is the fuel above the next id: inside a
  delete for `hMSF` and `hCoF`, and for the first stratum of the
  assembly for `htb`. Between operations the readings stay at p.fuel, so
  the fit between operations, and with it `htb`, is still needed.


## 2. What the three premises say and where they are used

### 2.1 hMSF and hCoF

`hMSF` is `∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts))
(p.fuel + 1)` (SIS/Tree/LatestTop.lean): for every writer state v with
`DelInvF` at fuel f (`PutInv`, `PutInvG`, the ranges, inner children,
`SegFits (f - 1)`, the reading at fuel f equal to the delete's start
without the key, the books), and the key access path down to a node x
at depth d > 0 with fewer than `mergeBelow` live klongs under an inner
parent, every successful `merge x d` ends in a state that fits f - 1,
that is p.fuel. `hCoF` is `CollapseFitsOK` (same file): the same for a
`replaceRoot` at a segment root, from `CollGetInvF`.

**The uses in the top theorem's proof** (`invGetScanOK_merges_free_noD4`,
DeadTop.lean, and `invGetScanOK_merges_noU_noD4` that it applies). `hMSF`
becomes `MergeStepOK` (`mergeStepOK_of_segFits` adds the untaken part,
proved). With `CollapseFitsOK` it goes to six consumers:

- `opGetCaseOK_delMergeC` (CollapseCommuteStep.lean), the reading's case
  of a delete with the merges (TP10), family `DelStepsOK`;
- `opCaseOKJ_treeInvRange_delMergeRLC` (CollapseCommuteRun.lean), the
  joint induction's tree, `PutInv` and ranges, family `DelStepsQdLJ`;
- `opJ2Case_delMergeRC` and `runTreeQ_of_mergesSC` (CollapseCommuteRun.lean),
  the take-back's facts, family `DelStepsJ2OK` (with S `SJ` and `TakeS4`);
- `opCaseOK_dead_delMerge` (DeadDelCases.lean), the dead klongs' bound,
  family `DelStepsCaseDOK` (`MergeStepOK` only);
- `hchk`'s discharge: `opDelChk5OKR_of_chk6` (DelHoleRoot.lean) and
  `opDelChk8OKR_holds` (DelMergeUp.lean).

Each consumer uses them in one way only: to keep the reading invariant
at p.fuel + 1 through `afterDelete`, `mergeUp` and `collapseRoot`, for
every state. For the four families these are their obligations ("from
`DelInv` at p.fuel + 1, `afterDelete` ends in `DelInv` at p.fuel + 1", and
the same for the other two); for `hchk`'s discharge, its relational loops
(`rwp_mergeUp_of_J`, `rwp_afterDelete_of_J`, `rwp_collapseRoot_chkJ`). For
`opGetCaseOK'_delMergeC` this is the whole proof: it hands
`writerWP_afterDelete_delC`, `writerWP_mergeUp_del` and
`writerWP_collapseRoot_delC` to `DelStepsOK`. The step lemmas that apply
the premises to a state are about twelve: `writerWP_mergeUp_del`
(DelMergeCaseKd.lean), `writerWP_mergeUp_delJ` (TakeDelMergeKd.lean),
`writerWP_mergeUp_delDW` and `dw_afterDelete` (DeadMergeLoop.lean),
`writerWP_collapseRoot_delC` and `writerWP_afterDelete_delC`
(CollapseCommuteStep.lean), `writerWP_collapseRoot_delJC` and
`writerWP_afterDelete_delJC` (CollapseCommuteJ2.lean), `rwp_mergeUp_of_J`
(DelMergeUp.lean), `putBook_mergeUp` and `rwp_afterDelete_of_J`
(DelHoleRoot.lean). In each, the premise gives one fact: the fit at the
end of a merge or a `replaceRoot`, at the fixed fuel, so that the loop's
invariant holds again for the next step. In `writerWP_mergeUp_del` it is
`hF4`, one conjunct of `hms`; the reading through the merge
(`writerWP_merge_get_inv`) asks the fit at its end as a hypothesis.

**Why believed false as stated** (delj, 024-12, section 1): `DelInvF` has
no heights. It admits a state whose deepest segment tree is p.fuel deep,
and a merge whose parent's cascade makes a new root ends p.fuel + 1 deep.
No counterexample was built (it needs a chain about p.fuel deep, and
p.fuel = (G + 1)(H + 2) + 2).

**True forms, proved** (delj, DelMergeFit.lean): `mergeFits_of_htJ` and
`collapseFits_of_htJ`, from the heights' books with their bound
(`HtJ`, `UntakenBound (p.fuel - 1)`) at the step's start.

### 2.2 htb

`htb` is `TakeBelowFuelDelOK p` (SIS/Tree/HeightsFit.lean): for every
run within reach, every delete of a transaction, every node in the
heights' cache at the delete's start and not taken back then, that the
delete takes back, has a cached height below p.fuel.

**Its one use** is the doomed transaction, in two copies,
`htStart_reachedU` (HeightsUnder.lean) and `htStart_of_ht`
(HeightsFill.lean): at every operation's start, every node not taken back
has a height below p.fuel. A node above H is noted in `outside`; the
transaction ends without error, so a later delete takes it back, having
found it at its start; `htb` bounds it. From that bound:

- the fit between operations (`txSegFitsOK_of_takeBelowDelRHU`,
  `TxSegFitsOK`, p.fuel - 1), which the reading needs at every
  operation's start and end;
- the heights' bound at a delete's start (`HtStartAt`, `UntakenBound
  (p.fuel - 1)`), from which the fits inside a delete before
  `afterDelete` are proved: after the full leaf's split
  (`delFullFitsOKR_run`) and after the stop node's cascade
  (`upCascFitsOKR_of`).

**Its consumers in the top theorem:** `jointHtJ_reachedJ`
(HeightsFillTop.lean, `htStart_of_ht` for the delete cases),
`txSegFitsOK_of_takeBelowDelRHU`, the families' cases that split a full
node (`delStepsCaseOK_fullH`, `delStepsCaseOK_emptyCascLHGJ_noU`, and
their sisters in `delStepsJ2OKJ_of_openR_noU`, `delStepsCaseDOK_merge`),
and `hchk`'s discharge: `opDelChk6OKR_of_chk7` (DelHoleLeaf.lean),
`opDelChk7OKR_of_chk8` (DelHoleClimb.lean), `opDelChk8OKR_holds`
(DelMergeUp.lean), each through `htStart_of_ht`.

**Evidence** (024-12, section 1): 316 runs within reach, 18,201
operations, 3,205 deletes that take nodes back, no failure.

### 2.3 How they hang together

- `htb` gives the heights' bound at a delete's start, p.fuel - 1. The
  true forms of `hMSF` and `hCoF` start from it. Inside the delete the
  reading is at p.fuel + 1, so it fits p.fuel: one level of room. A
  delete that adds a level twice would need two; no local invariant
  excludes it (delj's point (1)), though no run showed it (17,390
  operations, 159 with one step that added a level, none with two).
- `htb` also feeds `hchk`'s discharge and the joint induction, through
  the fit at the delete's start. That is the circle of section 4.4.
- On the NoOutside route (025-03) the heights are within H at every
  moment, so the bound is direct there, but `hMSF` and `hCoF` stay
  (025-03, section 3.3): the bound needs the heights' cache at the state
  after the merge, which the reading's loop invariant does not carry.


## 3. What the consumers need

**The fuel inside an operation is the proof's.** The writer never reads
with the fuel of `DelInvF`: its descents use `c.p.fuel` and throw
"bounds" when it runs out, so a run within reach never runs out. The fuel
f of `DelInvF` is what the proof reads the writer's tree with; 024-12's
(4), option (a), chose p.fuel + 1. The reading at f agrees with the
reading at any larger fuel once the tree fits below both
(`getFromR_fuel_mono`, GetFuel.lean; `wGetAt_eq_wGet`, DelMergeCaseF.lean).

**Every writer state fits its next id.** `PutInv` says that the writer's
tree is a tree (`TreeOK`: nothing names the root, one holder per reached
node) and that every node it reads has an id below the next id (`ids`
for the overlay, `fresh` for the base). In a tree, a node has one depth
(`PathLen.depth_unique`, WriterTreeDepth.lean), so a chain of inner nodes
has distinct ids, all below the next id, and is shorter than it. So every
segment tree is at most v.next deep (`SegFits ... v.next`), with no fact
of heights. That is P1.

**So the reading at a fuel above p.fuel and the next id is right at
every state inside a delete, reached or not.** Through a merge: the
merge's reading lemma asks the fit at its end at the fuel it reads with;
at a fuel above the next id at the merge's end the fit is P1. The same
for `replaceRoot`. Neither `MergeFitsOK` nor `CollapseFitsOK` is needed
for that.

**What needs the fixed fuel is the shape of the obligations.** The four
families state them as "`DelInv` at p.fuel + 1 before, `DelInv` at
p.fuel + 1 after", for every state. "After" is the part that fails: after
a merge the state can be one level deeper than p.fuel. Where the families
use the "after", at the operation's end, the state fits between
operations (p.fuel - 1, `TxSegFitsOK`), and the families' conclusions
already take that fit as a hypothesis:

    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

So the families can take their obligations over any invariant that holds
where `DelInv` at p.fuel + 1 holds (at the calls) and gives it back where
the state fits p.fuel - 1 (at the end). With the invariant "`DelInv` at
every fuel above p.fuel and the next id" (`DelInvA`), the obligations hold
for every state with no premise.

This is 025-04's pattern. There the split was asked for a tree at a state
where it did not read the part that was not one. Here the merges' loop is
asked for a fit at p.fuel where the reading does not need it; it needs it
only at the operation's end, where it holds.


## 4. The routes

### 4.1 Route P: a fuel above every node id (recommended for hMSF, hCoF)

**What it adds** (statements type-checked, RouteP.lean):

- **P1, the pigeonhole bound:** `segFits_of_idsBelow` (a tree whose nodes
  have ids below n fits n) and `segFits_next_of_putInv` (every state with
  `PutInv` fits its next id). Proved in scratch,
  /Users/f/fl/bench/2026-11-15/day/hplan/run/FuelNext.lean, 96 lines:
  a segment tree deeper than d has a chain of d + 1 inner nodes at
  growing depths, so of distinct ids (`chain_of_not_segDepthLe`), and
  core's `List.Nodup.length_le_of_subset` against `List.range n` ends
  it.
- **P2, the invariant above the next id:**

      def DelInvA (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (KO : KindOracle) (BK : NodeId)
          (v : W) : Prop :=
        ∀ F, c.p.fuel + 1 ≤ F → v.next < F → DelInv c base w0 key F KO BK v

  with the two conversions: `DelInv` at p.fuel + 1 gives `DelInvA`
  (`delInvA_of_delInv`, the delete's start fitting p.fuel - 1); `DelInvA`
  with the fit p.fuel - 1 gives `DelInv` at p.fuel + 1 back
  (`delInv_of_delInvA`). Both proved in scratch (FuelNext.lean, through
  `delInvF_fuel`: `DelInvF` moved between two fuels of at least p.fuel,
  by `getFromR_fuel_mono`). The same for the other families' invariants
  (`DelInvJF` with `TakeJ2`, with `DW`, with the Qd facts).
- **P3, the loops with no fit premise:** `writerWP_mergeUp_delA` and
  `writerWP_collapseRoot_delA` keep `DelInvA` with no premise, and their
  sisters for the other families and for `hchk`'s discharge.
  `writerWP_mergeUp_delA` is proved in scratch (FuelNext.lean): its
  one-fuel form `writerWP_mergeUp_delN` is `writerWP_mergeUp_del`'s proof
  (103 lines) with eight edits. So are root collapse
  (`writerWP_collapseRoot_collN`, `writerWP_collapseRoot_delA`) and
  `writerWP_afterDelete_delA`.
- **P4, the families over an invariant:** `DelStepsOKG p R I`, the body
  of `DelStepsOK` with the three obligations over I, and two more
  hypotheses: I holds where `DelInv` at p.fuel + 1 holds, and with the
  fit p.fuel - 1 gives it back. `DelStepsOK` is its instance at `DelInv`
  (`delStepsOK_of_G`, proved in RouteP.lean, four lines). The same for
  `DelStepsJ2OK`, `DelStepsQdLJ` and `DelStepsCaseDOK`. Tried in scratch
  (/Users/f/fl/bench/2026-11-15/day/hplan/run/P4Trial.lean): the case
  family `DelStepsCaseOKG`, the old case as its instance
  (`delStepsCaseOK_of_G`), and the leaf-with-room case over any I
  (`delStepsCaseOK_roomG`), which is the old proof with two lines
  changed.
- **P5, the consumers:** the six of section 2.1 at I := `DelInvA` (and
  its sisters), with no `MergeStepOK` and no `CollapseFitsOK`; then the
  top theorem with the premises `hp`, `hth`, `htb`, `l4`. The first,
  `opGetCaseOK_delMergeA`, is proved in scratch (P4Reading.lean), with
  the whole family over I under it (seven cases, two walks).

**How P3 goes.** `writerWP_mergeUp_del` today keeps `DelInv c base w0 k0
fuelR KO BK` for one fuel fuelR, given `MergeStepOK c base fuelR`. For
`DelInvA` fix F and carry "v.next < F → `DelInv` at F" through the loop:
the next id only grows along the writer's steps (`KeepsFreshCache`,
FreshCache.lean: `freshCache_mergeUp`, `freshCache_merge`,
`freshCache_collapseRoot`), so where the end's next id is below F, so is
the start's, and the start has `DelInv` at F; the merge's lemmas apply at
F as they do at fuelR (all are generic in it); `MergeStepOK`'s untaken
part is proved (`mergeStepOK_untaken`), and the fit at the merge's end at
F is P1, since its next id is below F. The trial's invariant at one fuel
F (`QF`) is the fresh ids' books (`FreshCache`, which every writer
function keeps) and `DelInv` at F while the next id is below F; then
`DelInvA` at the end is that, for every F. A prover may instead give the
old lemma's hypothesis a form both sources meet ("the fit at each merge's
end at fuel F, where a condition on the end state holds": `MergeStepOK`
with the condition `True`, P1 with "next < F"), so that the old lemma
becomes a corollary and no proof is kept twice; the trial copied.

**Against the counterexample.** Route P never claims a fit at p.fuel
inside a delete. Its lemmas hold for every state with their hypotheses,
reached or not. At a state p.fuel deep whose merge adds a level, `DelInvA`
holds before and after; only the conversion back to p.fuel + 1 is not
available there, and it is used only where the fit between operations is
given.

**Against the runs.** Every claim of route P is a theorem for every
state, so runs test nothing that the proof does not cover. Section 5 has
a sanity check of P1.

**Size and risk.** 1,750 to 3,500 lines in 6 steps (section 6.1). Risk:
low. The one mathematical point, P1, is proved, and so is the whole route
for the reading's consumer (P4Reading.lean): the merges' loop
(`writerWP_mergeUp_del`'s proof with eight edits), root collapse
(`writerWP_collapseRoot_collC`'s with about fifteen), `afterDelete`, the
family over I with its seven cases, the two walks of the upward delete
with a fixed obligation (five edits each), and the consumer. What is left
is the same on four more families. A step lemma of those that asks for
the fit at its fixed fuel other than at its end would stop that family
(section 6.1 has the stop rule); none of the reading's did.

**What it also gives.** P4 is the generalization that hu proposed for
`d4` and `l4` as option (b) (024-12, section 1): with I := `DelInv` and
`DW`, the copies in DeadDelCases.lean become instances, and `l4`'s live
counts can ride in I. It is an addition here, since the old families stay
as instances; hu called it a statement change because it would replace
them.

### 4.2 Route H: the heights carried to the calls (delj's plan)

delj's plan of 11:45 (024-12, section 1): carry `HtJ` to every call of
`afterDelete` in each family's walk and in `hchk`'s discharge; a merges'
loop with the heights (`ht_merge_of_J`, `mergeFits_of_htJ`); and the bound
across a delete's steps, either "a delete adds at most one level" (the
klongs a new root gets in the delete, against M; or that after a step that
adds a level every node on the path above has room for the rest of the
delete) or a ladder (the bound p.fuel - 1 + k after k steps, the merges'
fuel counter bounding k, with a fuel inside the delete near 3 p.fuel).

It needs P4's change of the families too (the obligations given the
heights at the calls), and on top of it the heights through every walk to
the calls and point (1). So it is route P and more. Not recommended. Its
pieces stay as proved true forms.

### 4.3 Route C: a checked copy

A premise that the writer's delete runs as a copy that checks the fit
after each merge and `replaceRoot`. A statement change (two premises
replaced by a tested one), and the reading over the checked copy needs
the same change of the families as route P, since the case lemmas are
over `putKv`. Not recommended.

### 4.4 htb: the take-back sites, and the circle

**The argument** (cost's plan, 024-12, section 1: "every take-back site
lies on a successful descent"; made exact here). A delete takes back at
three places; for a node it found at its start:

- **the upward loop's `takeBack`:** the chain's nodes are on the key
  access path that the delete's own descent built (the start path). That
  descent went from each segment root to the leaf within p.fuel steps, so
  their heights are below p.fuel (`ht_descendLte_height`).
- **a merge's `takenBack`:** the two nodes merged, when the transaction
  made them. The merged node x has the loop's height h (`descendHeight`
  stops at the cached height h), and h is below p.fuel by the merges'
  fuel counter (`mergeUp key g c.p.fuel h0`, h0 the changed segment
  leaf's height, 0, one height up per merge, and the loop throws at
  counter 0). The other node, a live child of the same parent, has x's
  height by the heights' cache at the merge (`HtCache`).
- **root collapse's `takeBackRoot`:** a root the transaction made. Found
  at the start, it is a segment root on the start path, so as the chain.
  Why: a segment root of the key's path during the delete is the start's,
  or one the delete made, or the only child of a root collapsed before
  it; that child is one a merge of the delete made, since the collapsed
  root had at least two live klongs at the start (the live counts) and
  lost all but one to merges into one node. A node the delete made is not
  one `htb` speaks of. A fallback: the root is the parent of the loop's
  last merge, one above the loop's last h.

**The circle.** The argument needs the heights' cache at the take-back
sites inside the delete, at the runs. Today those come from the joint
induction (`HtInv` at the operation's start) and from `hchk`'s discharge
(the delete runs as its checked copy, over which the heights' walk
`ht_putKvDelChk2` goes). Both use `htb`: `htStart_of_ht`, for the fit at
the delete's start (`DelInvJ` at p.fuel + 1 there) and for the heights'
bound that the fits after the full leaf's split and the stop node's
cascade use. So `htb` at an operation needs the heights at it, which need
the fit at its start, which needs `htb` at it. On top of today's assembly
`htb` cannot be discharged.

**What breaks it:** a first stratum with no fit and no bound. Every fact
the joint induction carries (`PutInv`, the ranges, the live counts,
`HtInv`, the writer's tree, `TakeJ2`; none of them speaks of the fuel)
and `hchk`'s equivalence, proved at `DelInvA` from the delete's start:

- the full leaf's split and the stop node's cascade keep `DelInvA` by P1,
  so `delFullFitsOKR_run` and `upCascFitsOKR_of` drop out of the stratum;
- the families' delete cases there need no fit at the start (their
  conclusions in the stratum are fuel-free);
- `jointHtJ_reachedJ` without `hdel`: the delete cases given `HtInv`
  without the bound.

Then `htb` from the sites, with the stratum's heights; then the bound and
`TxSegFitsOK` by the doomed transaction, as today; then the readings as
today. Route P's `DelInvA` is what makes the stratum possible.

**How `htb` leaves.** As `d4` did (024-12, section 1): `htb` speaks of
every run within reach, and the sites need the joint induction's facts at
the runs (`RunTreeQ`). So the top theorem's proof proves the case it uses,
inside the transactions' induction, and `htb` as stated stays undischarged.

**Alternatives:**

- **NoOutside** (025-03, F1): the theorem with the hypothesis that no
  transaction makes a node outside G and H has no `htb`. It is in Lean as
  a separate theorem (`invGetScanOK_merges_noOutside_noU`), on the older
  route, with `hHL` and `hCoU` still in it; route P applies there too.
- **Keep `htb`** as the one heights premise: it is tested (section 5),
  and its true form is a fact of runs within reach, not of every state.

### 4.5 One argument for all three?

- The doomed transaction carried into the operation (every node that a
  delete takes back, found or made, is below p.fuel) would bound every
  state inside a delete by p.fuel - 1, and `htb` would be its special
  case. But the reading's consumers would still need the heights at the
  calls (route H), so it does not remove `hMSF` and `hCoF` by itself.
- The fuel above the next id is the one argument that serves all three:
  route P inside a delete, and the stratum of section 4.4 for `htb`.
- Between operations the readings stay at p.fuel (`runGet`, the trusted
  reader's fuel), so the fit between operations is still needed, and with
  it `htb`. Making those readings adaptive too would remove `htb` with no
  site argument: at a transaction's end the committed tree fits H
  (`boundsOK`), and nothing else needs the fit. But it restates the
  reading route of puts and deletes and the transactions' assembly
  (`OpGetCaseOK`, the put cases, `getOK_scanOK_of_cases_merges_open`),
  4,000 lines or more, as NoOutside's copy was (025-03, section 3.2). Not
  recommended now.


## 5. The run checks

One new script: /Users/f/fl/bench/2026-11-15/day/hplan/run/htb-sites-check.lean,
a copy of 024-12's `12-tree-model/merge-fit-forms-check.lean.txt` (its
writer copy, runs and parameters: theta 0 at node sizes 8 and 10, Java's
theta at 8 and 14) that notes every take-back of a delete. Run from the
lean/ of a built clone with `lake env lean`, 16 seconds; its output is
`htb-sites-check.out` beside it.

**`htb`'s sites, 0 failures:**

- 4,573 nodes taken back by deletes: 251 by the upward loop, 3,765 by
  merges, 557 by root collapse. 4,335 of them found at the delete's start
  (cached, not taken back): 251, 3,642 and 442.
- Every found node had a cached height below p.fuel, and within H.
- Every found node that a merge took back had the loop's height h as its
  cached height: 3,642 of 3,642 (x and the other node merged).
- Every found root that root collapse took back was on the start path:
  442 of 442. Every chain node was on it, as it must be.
- No stop node was inner (the inner stop node's branch never ran).

**Route P's pigeonhole bound,** a sanity check: at 3,667 states after a
merge or a step of root collapse, the deepest segment tree was at most
the next id deep. 0 failures (trivially: the trees are a few levels deep,
the next ids above 1,000).

**What the runs do not show.** No found node taken back was outside H:
in these runs no transaction leaves a node above H between operations for
a later delete to take back, so the doomed transaction's own case never
arose, and `htb`'s bound (p.fuel) is far from tight there. The script's
two families of transactions with puts and deletes mixed (`uFamilyPD`,
`uFamilyNew`, which 024-12's check does not run either) were not within
reach and gave nothing. Not tested: node sizes above 14; Java's traces.

**Earlier evidence:** `htb`, 3,205 deletes that took nodes back (024-12,
section 1); the fits inside deletes, 11,057 states, every one within
p.fuel - 1 (`fuel-inside-check.lean.txt`); `merge-fit-forms-check`,
section 2.3.


## 6. The recommended route, step by step

No statement changes: every step adds lemmas and definitions. Where a
lemma loses a hypothesis or gains generality, the new lemma gets the
proof and the old one becomes a corollary under its old statement, so
that no proof is kept twice (025-04's rule). The new lemmas go first in
new files and move when they build: a change in DelStepsGh.lean or
HeightsFillHolder.lean rebuilds most of the route above it.

### 6.1 Part 1: route P, `hMSF` and `hCoF` out

By consumer, as the trial went: the reading's (section 2.1, the first) is
done in scratch, and each of the other four is the same pattern on its own
family. Each step is gated alone.

1. **Land the reading's consumer** (2 to 3 hours, 600 to 1,000 lines
   in place). From /Users/f/fl/bench/2026-11-15/day/hplan/run/:
   - FuelNext.lean: P1 (`chain_of_not_segDepthLe`, `segFits_of_idsBelow`,
     `segFits_next_of_putInv`, `segFits_next_of_putInvG`), P2 for `DelInv`
     (`segFits_mono'`, `wGetAt_fuel_eq`, `delInvF_fuel`, `DelInvA`,
     `delInvA_of_delInv`, `delInv_of_delInvA`), and P3 for the reading
     (`QF`, `writerWP_mergeUp_delN`, `writerWP_mergeUp_delA`; `CI`,
     `freshCache_takeBackRoot'`, `freshCache_replaceRoot'`,
     `writerWP_collapseRoot_collN`, `writerWP_collapseRoot_delA`,
     `writerWP_afterDelete_delA`);
   - P4Reading.lean, which repeats FuelNext.lean and P4Trial.lean and
     adds: `DelStepsCaseOKG`, `DelStepsOKG`, `delStepsCaseOK_of_G`, the
     seven cases over I (`delStepsCaseOK_noLeafG`, `_noopG`,
     `_emptyRoomG`, `_emptyRootG`, `_emptyCascLHGJ_noUG`, `_roomG`,
     `_fullHG`), the two walks over I (`writerWP_del_emptyRoomMKG`,
     `writerWP_del_emptyAnyMKLHGJG`), `delStepsCaseOK_orG`,
     `delStepsOK_of_casesG`, `delStepsOKJ_of_open_noUG`, `DelStepsOKA`,
     `opGetCaseOK'_delMergeA` and `opGetCaseOK_delMergeA`.

   The trial copied the old proofs; in the repo the new lemma gets the
   proof and the old one becomes its corollary (the walks' `hpost` is
   then unused, as the trial's warnings show). New files: FuelNext.lean,
   and the generalized lemmas beside the old ones in their own files.
2. **The take-back's family** (2 to 4 hours, 300 to 600 lines):
   `DelStepsJ2OK` over I, with I := `DelInvJF` at every fuel above
   p.fuel and the next id (its end, `TakeJ2`, is fuel-free, so the
   conversion out needs no fit); its loops (`writerWP_mergeUp_delJ`,
   `writerWP_collapseRoot_delJC`, `writerWP_afterDelete_delJC`) as step
   1's; its walks over I (`writerWP_del_emptyAnyMJKLHG` and the others of
   DelStepsGh.lean, `writerWP_del_emptyRoomMJK` in TakeDelSteps.lean,
   `takeJ2_deleteUpward_upTMBK`) as `writerWP_del_emptyAnyMKLHGJG`; then
   `opJ2Case_delMergeRC` and `runTreeQ_of_mergesSC` without `MergeStepOK`
   and `CollapseFitsOK`.
3. **The joint induction's tree family** (2 to 3 hours, 200 to 500
   lines): `DelStepsQdLJ` (`DelStepsCaseQdJ`) the same; then
   `opCaseOKJ_treeInvRange_delMergeRLC`.
4. **The dead klongs' family** (1 to 3 hours, 200 to 500 lines):
   `DelStepsCaseDOK` with I := `DelInvA` and `DW`; `writerWP_mergeUp_delDW`
   and `dw_afterDelete` as step 1's; then `opCaseOK_dead_delMerge`.
5. **`hchk`'s discharge** (2 to 4 hours, 300 to 600 lines): the
   relational loops (`rwp_mergeUp_of_J`, `rwp_afterDelete_of_J`,
   `putBook_mergeUp`, `rwp_collapseRoot_chkJ`) at the J invariant above
   the next id; then `opDelChk5OKR_of_chk6` and `opDelChk8OKR_holds`
   without `MergeStepOK` and `CollapseFitsOK`.
6. **The top theorem** (1 to 2 hours, 150 to 300 lines):
   `invGetScanOK_merges_noFit` (name by rule: the next free one),
   premises `hp`, `hth`, `htb`, `l4`, by `invGetScanOK_merges_free_noD4`'s
   proof with the six consumers replaced; `invGetScanOK_merges_free_noD4`
   its corollary. The paragraphs in 024-12, section 1 (`hMSF`, `hCoF`),
   and lean/README.md; the gate as for `invGetScanOK_merges_noU`.

**Stop rule** for steps 2 to 5: if a loop's step lemma asks for a fit at
its fixed fuel other than at its end, or a family's conclusion needs the
fit where it does not take it as a hypothesis, the prover writes which
and goes on with the other steps; the fix to try is P1 at that state.

**Part 1 in all:** 1,750 to 3,500 lines, 10 to 19 prover hours. Steps 2
to 5 do not depend on each other: after step 1, two provers can share
them; one night for two, a night and a day for one.

### 6.2 Part 2: `htb` out

After part 1 lands, by rule (section 7).

7. **The first stratum** (8 to 12 hours, 1,000 to 2,000 lines): the
   families' delete cases in the joint induction at `DelInvA` with no fit
   and no heights' bound at the delete's start (the full leaf's split and
   the stop node's cascade by P1); `hchk`'s discharge the same
   (`opDelChk6OKR_of_chk7`, `opDelChk7OKR_of_chk8`, `opDelChk8OKR_holds`
   with no `htb`); `jointHtJ_reachedJ` without `hdel`, with the delete
   cases given `HtInv` without the bound.
   **Stop rule:** if a member of the joint induction turns out to need
   the fit at an operation's start, the prover writes which and why, and
   stops part 2 there.
8. **`htb`'s sites** (8 to 14 hours, 1,200 to 2,500 lines): a walk over
   the delete's checked copy beside the heights' walk (`ht_putKvDelChk2`
   and its parts) that carries "every node found at the start and taken
   back has a height below p.fuel", with the three sites of section 4.4.
   The collapse's site is the hardest: first the start-path form (tested
   442 of 442); if its frame argument grows past about 800 lines, the
   fallback through the loop's last merge.
9. **The top theorem without `htb`** (2 to 3 hours, 300 to 500 lines):
   inside the transactions' induction, `htb`'s case at the runs from step
   8, then the bound and `TxSegFitsOK` as today; premises `hp`, `hth`,
   `l4`.

**Part 2 in all:** 2,500 to 5,000 lines, 18 to 29 prover hours, two to
three nights for one prover. Steps 7 and 8 can share out once step 7's
statements are fixed (step 8 uses only their conclusions).

**The first prover step:** step 1, landing the reading's consumer from
/Users/f/fl/bench/2026-11-15/day/hplan/run/FuelNext.lean and
P4Reading.lean; then steps 2 to 5 side by side.


## 7. What stays open, and Frans's decisions

**Open after part 1:**

- `htb` (part 2, or NoOutside, or kept as a tested premise);
- `l4`, with its plan in 024-12, section 1 (P4's families over an
  invariant serve it: the live counts can ride in I);
- `MergeFitsOK` and `CollapseFitsOK` as stated: still believed false,
  not refuted, and no longer used by the newest top theorem. They stay in
  the code with the older theorems that name them.

**Open after part 2:** `l4` only, among the joint route's premises.

**Decided here by rule** (025's rules: no step waits for Frans):

- Part 1 first, part 2 after it lands, if the tokens allow; NoOutside is
  not taken up, since it is a hypothesis on the run (025-03) and part 2
  needs none.
- The families are generalized beside the old ones, which become their
  instances; they are not replaced.
- The fuel inside a delete is "every fuel above p.fuel and the next id",
  not one chosen fuel: no fixed fuel makes the universal obligations
  true.

**For Frans, none needed to start.** Two optional choices, neither a
step of the plan:

- whether to replace the four families by their generalized forms (the
  close step), which would also remove the `_D` copies of `d4`'s route
  (hu's option (b)); a statement change of definitions, not of a
  premise;
- whether to keep `htb` as a premise rather than spend part 2's two to
  three nights on it.


## 8. Log

2026-11-15, 11:45 to 13:00. The plan written (sections 1 to 7) by the
planning agent of coord-1115 (plan 006-27). Read: 024-12, section 1;
006-26, section 4, and its correction; 025-03, section 3; 026-16,
section 4; 024-22, section 11.1; the reports of hu and delj; the
Lean code of the premises, their consumers and the chain. Made: the run
check of section 5 (htb-sites-check.lean, 16 seconds); the statements of
route P type-checked (RouteP.lean; `delStepsOK_of_G` proved, the others
`sorry`, scratch only); route P proved for the reading's consumer
(`opGetCaseOK_delMergeA`, P4Reading.lean, 1,575 lines with its copies;
its parts also in FuelNext.lean, 551 lines, and P4Trial.lean, 446).
No Lean file of the repo changed. No step of section 6 started in the
repo.

2026-11-15, 12:45 to 13:15. Part 1, step 1 (prover fit, plan 006-27):
the reading's consumer in lean/, about 800 lines added and 130 removed.
No statement changed; each generalized lemma has the proof and the old
one is its corollary under its old statement.

- New file SIS/Tree/FuelNext.lean: P1 (`segFits_of_idsBelow`,
  `segFits_next_of_putInv`, `segFits_next_of_putInvG`), P2 (`DelInvA`,
  `delInvA_of_delInv`, `delInv_of_delInvA`), P3 (`mergeStepOKW_next`,
  `writerWP_mergeUp_delA`, `writerWP_collapseRoot_delA`,
  `writerWP_afterDelete_delA`) and P5 (`DelStepsOKA`,
  `opGetCaseOK_delMergeA`: case 4 of the reading from the family at
  `DelInvA`, `TxSegFitsOK` and TP4, with no `MergeStepOK` and no
  `CollapseFitsOK`).
- The loops, one proof each (the plan's "a form both sources meet", not
  the trial's copies): a condition C on the state that holds at a state if
  it holds at a later one with a larger next id; the invariant is the
  fresh ids' books, and the old invariant where C holds (`DelInvW`,
  `CollInvW`); the fit at a merge's end, or after a replaceRoot, is asked
  only where C holds there (`MergeStepOKW`). `writerWP_mergeUp_delW`
  (DelMergeCaseKd.lean) and `writerWP_collapseRoot_collW`
  (CollapseCommuteStep.lean); `writerWP_mergeUp_del` and
  `writerWP_collapseRoot_collC` are C true, route P is C "the next id
  below F".
- P4: `DelStepsCaseOKG`, `DelStepsOKG` and `DelInvI` (the old
  invariant) in DelSteps.lean, with `delStepsCaseOK_of_G`,
  `delStepsCaseOK_to_G`, `delStepsOK_of_G`; the seven cases and the two
  walks over I beside the old ones (DelSteps.lean, DelStepsEmptyRoot.lean,
  DelStepsFullH.lean, HeightsFillHolder.lean; the walks' obligations end
  in their Post and an `Imid`, so they have no `hpost`);
  `delStepsOKJ_of_open_noUG`.
- The trial's primed copies `freshCache_takeBackRoot'`,
  `freshCache_replaceRoot'` and `segFits_mono'` are the existing
  `freshCache_takeBackRoot`, `freshCache_replaceRoot` and `segFits_mono`.

Gated: f719fb4f (with main, 89273873), gate-1 PASS.

2026-11-15, 13:00 to 13:10. Part 1, step 2 (fit): the take-back's
family, as step 1, about 600 lines added and 150 removed.

- The loops with the take-back's facts: `writerWP_mergeUp_delJW`
  (TakeDelMergeKd.lean, `DelInvJW`) and `writerWP_collapseRoot_collJW`
  (CollapseCommuteJ2.lean, `CollInvJW`); `writerWP_mergeUp_delJ` and
  `writerWP_collapseRoot_collJC` are C true.
- P4: `DelStepsJ2OKG`, `DelStepsCaseJ2OKG`, `DelInvJI` (TakeDelSteps.lean;
  I gives `TakeJ2`, which speaks of no fuel, so no fit is asked at the
  end); the cases and walks over I beside the old ones (TakeDelSteps.lean,
  TakeRunQ.lean, DelStepsGh.lean, DelStepsFullH.lean,
  HeightsFillHolder.lean), `delStepsJ2OKJ_of_openR_noUG` and
  `delStepsJ2OKS_of_openR_noUG`.
- FuelNext.lean: `DelInvJA`, `writerWP_afterDelete_delJA` and its parts
  (root collapse's `ReplaceRootFullJ2OKC` at each fuel by
  `replaceRootFullJ2OKC_holds`), and the consumers `opJ2Case_delMergeA`
  and `runTreeQ_of_mergesSA`, with no `MergeStepOK` and no
  `CollapseFitsOK`. The stop rule did not apply: no step lemma asked for
  the fit other than at its end.

Gated: edb53562, gate-2 PASS.

2026-11-15, 13:10 to 13:20. Part 1, step 3 (fit): the joint induction's
tree family, as step 1. `DelStepsCaseQdG` (DelStepsTree.lean; I gives
`QdW`, `PutInv` and the ranges, which speak of no fuel) and
`DelStepsCaseQdJG`, `DelStepsQdLJG` (HeightsFillHolder.lean), their cases
over I and `delStepsQdLJ_of_openR_noUG`; `opCaseOKJ_treeInvRange_of_qdW`
(CollapseCommuteRun.lean) has the old consumer's split, which is now its
corollary; FuelNext.lean: `opCaseOKJ_qdW_delMergeA` and
`opCaseOKJ_treeInvRange_delMergeA`, with no `MergeStepOK` and no
`CollapseFitsOK`. One surprise: NoOutsideRun3.lean stopped building,
since 025-03's `n_wrap` wraps the lemmas that the named lemmas' proofs
use, and `delStepsCaseQd_fullH`, now a corollary, no longer uses
`delFullFitsOKR_run`; one line in NoOutsideBase.lean wraps it by name
(`n_wrap_these`), no statement changed.

Gated: 7afd3be7, gate-3 PASS.

2026-11-15, 13:15 to 13:20. Part 1, step 4 (fit): the dead klongs'
family. `writerWP_mergeUp_delDWW` (DeadMergeLoop.lean, `DelInvDWW`: `DelInv`
and `DW` while C holds), `dw_afterDelete_of` (afterDelete from any loop
that keeps `DW`); `DelStepsCaseDOKG` (DeadDelCases.lean; only `hin`: the end
is `DW`, which speaks of no fuel), its cases, the two walks and
`delStepsCaseDOK_mergeG`; FuelNext.lean: `writerWP_mergeUp_delDWA`,
`dw_afterDeleteA`, `opCaseOK_dead_delMergeA`, with no `MergeStepOK`.

Gated: b799d6f8, gate-4 PASS.

2026-11-15, 13:20 to 13:30. Part 1, step 5 (fit): `hchk`'s discharge.
The relational loops run for the runs that end in a state of C (`RWPC`,
DelHoleRoot.lean, with its combinators): `rwp_collapseRoot_chkQ` (the
check asked only at states of C, which hold where the run's end does) and
`rwp_mergeUp_of_JW` (DelMergeUp.lean); the old `rwp_collapseRoot_chk` and
`rwp_mergeUp_of_J` are C true. Root collapse's four steps are one lemma,
`collSteps_JW` (`CollSteps`, CollapseCommuteJ2.lean), for the writer's
loop (`writerWP_collapseRoot_collJW`) and the checked one
(`rwp_collapseRoot_chkJW`; the old `rwp_collapseRoot_chkJ`, which repeated
the steps, is its corollary). `opDelChk8OKR_of_mergeChk` and
`opDelChk5OKR_of_chk6G` take the merges' loop's and `afterDelete`'s checked
runs as hypotheses; the old ones are their instances with `MergeStepOK`
and `CollapseFitsOK`. FuelNext.lean: `rwp_mergeUp_of_JA`,
`rwp_afterDelete_of_JA` (at a fuel above the run's end, F chosen from the
unchecked run's end), `opDelChk8OKR_holdsA` and `opDelChk5OKR_of_chk6A`,
with no `MergeStepOK` and no `CollapseFitsOK` (the fit at the delete's start
from the heights and `htb`, `htStart_of_ht`, as the chain has it).

Gated: d21270d2, gate-5 PASS.

2026-11-15, 13:30 to 13:40. Part 1, step 6 (fit): the top theorem
`invGetScanOK_merges_noFit` (DeadTop.lean): TP7, TP10 and TP11 for Java's
parameters from `hp`, `hth`, `htb`, `l4`, with no `hMSF` and no `hCoF`:
`invGetScanOK_merges_noU_noD4`'s proof with `hchk5` discharged by
`opDelChk5OKR_of_chk6A` and each of the six consumers in its route P form.
`invGetScanOK_merges_free_noD4` is its corollary under its old statement;
lean/README.md says so. Part 1 in all: about 2,000 lines added and 600
removed in 20 files, in about two hours; no statement changed; one line
added in NoOutsideBase.lean (step 3).

Gated: 96e9c079, gate-6 PASS (the gate's audit list does not name
`invGetScanOK_merges_noFit`; `#print axioms` gives the standard three).

Next, by rule (section 7): part 2, `htb` (steps 7 to 9), or `l4` (024-12,
section 1); `MergeFitsOK` and `CollapseFitsOK` as stated stay open and
unused by the newest top theorem.

2026-11-15, 13:40 to 14:20. Part 2, step 7: its statement, and the
stratum's invariant (prover htb). New file SIS/Tree/Stratum.lean; one
generalization in HeightsFillTop.lean. No statement changed.

- **The reading is not needed in the stratum.** The stratum's members
  conclude `QdW`, `TakeJ2` and the checked copies, which speak of no fuel.
  So the leaf's change need give only the tree's facts (`DelInvT`: `DelInv`
  with no fit and no reading). Route P's invariant then holds at the state
  after the leaf's change taken as its own reference, with the key `[]`
  (not well formed, so no read asks it): its fit at every fuel above the
  next id is P1, its reading clause the state reading as itself
  (`delInvA_self`). The loops keep `DelInvA` for every reference, so the
  invariant with the reference left open (`DelInvAE`, `DelInvJAE`, and
  `DelHoleJE` for the checked copies) is kept with no fit
  (`writerWP_afterDelete_delAE`, `writerWP_mergeUp_delJAE`,
  `rwp_afterDelete_of_JAE` and their sisters) and gives `QdW` and
  `TakeJ2` at the end. This replaces section 6.2's "the families' delete
  cases at `DelInvA`": `DelInvA` with the delete's start as reference would
  need the reading after the leaf's change at a fuel above the next id,
  that is the split's and the upward delete's reading lemmas at a fuel
  other than p.fuel (`wGet_leaf_change_seg`, `DelFullRootStepOK`,
  `collGetInv_after_upT` read at p.fuel), which the tree's facts do not.
- **The joint induction over its start's facts:** `jointHtJ_reachedJS`
  (HeightsFillTop.lean) takes the facts that the take-back's step and the
  delete's cases ask at an operation's start as two predicates S and St,
  each from what the induction knows there (`JointStartOK`), the delete's
  cases at St (`OpCaseOKJS`). `jointHtJ_reachedJ` is its corollary (S :=
  `SJ`, St := `StartJ`, both from `htb` as before).
- **Step 7's statement:** `jointHtJ_reached0` (Stratum.lean), the joint
  induction with no `htb`: `PutInv`, the ranges, the fill, the heights'
  walk, the writer's tree and the take-back's node facts at every state of
  a transaction, from the put cases, the live counts (from `l4`) and three
  stratum families: (i) the tree, `PutInv` and the ranges after a delete
  with the merges, given `StartJ0` (`StartJ` without the heights' bound;
  `OpCaseOKJS p R (StartJ0 p) _ DelMergeCaseL`); (ii) the take-back's
  step given `SJ0` (`SJ` without the fit and the bound; `OpJ2OK p R (SJ0
  p)`); (iii) `hchk` (`OpDelChk2ORJ`, as stated: it has neither, but its
  discharge today goes through `htb`). The old forms follow from them
  (`opCaseOKJ_of_0`, `opJ2OK_of_0`).

**Left of step 7:** (i), (ii), (iii). Each is the existing family's proof
with the leaf's change giving `DelInvT` (`DelInvJT`) in place of `DelInv`
at p.fuel + 1, then `delInvAE_of_T` (`delInvJAE_of_T`) and the loops at
`DelInvAE`. The step lemmas that take the start's fit, each only for the
fit and the reading after the change, and so each needing a tree-facts
form (the old one then its corollary, the fit and the reading added):

- the bitmap with room: `delInvF_after_bitmap` (DelStepsRoom.lean; its
  tree part needs no fit, about 40 lines);
- the bitmap into a full leaf: `writerWP_appendDeleteKlong_full_delH`
  (DelStepsFullH.lean) over `writerWP_appendDeleteKlong_full_inv_any`,
  `writerWP_appendDeleteKlong_full_inv` and the root's step
  `DelFullRootStepOK` (DelStepsFullGet.lean), and the fit after the split
  `DelFullFitsOKR` (not needed in the stratum);
- the upward delete with room: `writerWP_del_emptyRoomMKG` (DelSteps.lean)
  over `collGetInv_after_upT` (WriterGetUpTake.lean, `CollGetInv` carries
  the fit) and `delInvF_of_collGetInv`;
- the leaf at the space root emptied: `delStepsCaseQd_emptyRootG` and its
  sisters;
- the stop node's cascade: `writerWP_del_emptyAnyMKLHGJG`
  (HeightsFillHolder.lean), `UpCascOKHGJ` with `UpCascFitsOKR`; its descent
  invariant `KdHtJ` carries the bound (`HtJ.bound`), so the stratum's
  walk takes `KdJ` with the heights' walk without it.

(i) and (ii) can be one family: `DelInvJAE` gives `QdW` too
(`delInvAE_of_JAE`, `qdW_of_delInvAE`). For (iii) the chain is
`opDelChk5OKR_of_chk6G` (no fit already), then `OpDelChk6OKR` and
`OpDelChk7OKR` with `DelHoleJE` in place of `DelHoleJ` (new definitions),
and `opDelChk8OKR_of_mergeChk` with the merges' loop checked from
`DelInvJAE` (`rwp_mergeUp_of_JAE`). Stop rule: no member asked for the
fit at an operation's start other than through these step lemmas.

Next: the tree-facts forms, the room case first (it serves all three
families), then the full leaf, the upward delete, the root, the cascade;
then step 8 against `jointHtJ_reached0`'s conclusions.

2026-11-15, 14:00 to 14:10. Part 2, step 7: one stratum family for the
tree and the take-back, four of its seven cases (prover htb). New file
SIS/Tree/StratumSteps.lean; `DelInvT` and `DelInvJT` moved to the files of
`DelInv` and `DelInvJ` (DelMergeCaseKd.lean, TakeDelMergeKd.lean). No
statement changed.

- **One family for (i) and (ii):** `DelStepsCaseTJ` (StratumSteps.lean),
  a delete case from `SJ0` and `TakeJ2` with the obligations entered from
  `DelInvJT`, concluding `QdW` and `TakeJ2`. `DelInvJT` carries both, so
  the two families that the joint induction uses today (`DelStepsQdLJG`,
  `DelStepsJ2OKG`) are one here. At `DelInvJAE` (`DelStepsTJA`) it gives
  member (i), `opCaseOKJ0_treeInvRange_delMergeT`, and member (ii),
  `opJ2OK0_of_T`; with them `jointHtJ_reachedT`: the joint induction with
  no `htb`, from the family and `hchk`.
- **Proved cases:** no leaf, a noop, a leaf with room, a full leaf
  (`delStepsCaseTJ_noLeaf`, `_noop`, `_room`, `_full`). The tree-facts
  forms of the leaf's change: `delInvFT_after_bitmap` (DelStepsRoom.lean;
  `delInvF_after_bitmap` now takes its tree's facts from it);
  `writerWP_appendDeleteKlong_full_invT`, `_full_inv_anyT` and the root's
  step `DelFullRootStepOKT` with `delFullRootStepOKT_ctx`
  (DelStepsFullGet.lean, DelStepsFullRoot.lean; the reading under the
  start's fit as a premise, the old lemmas and `delFullRootStepOK_ctx`
  their corollaries); `writerWP_appendDeleteKlong_full_delT`
  (DelStepsFullH.lean, `DelInvT` with no fit and no heights; the old
  `writerWP_appendDeleteKlong_full_delH` keeps its proof, since it takes
  the root's step with the fit for every context). The full leaf's walk
  needs no heights in the stratum (the kinds' walk `writerWP_del_toLeafMK`).

**Left of step 7:** the three cases that empty the leaf (`DelEmptyM`):
the upward delete with room above (`DelEmptyRoomM`, as
`delStepsCaseJ2OK_emptyRoomRG` over `writerWP_del_emptyRoomMJKG`, whose
`hD` needs a tree-facts form of `collGetInv_after_upT` and
`delInvF_of_collGetInv`), the space root emptied (`DelEmptyRootM`, as
`delStepsCaseJ2OK_emptyRootRG`), the stop node's cascade (`DelEmptyCascM`
with the live counts from `SJ0`, as `delStepsCaseJ2OK_emptyCascS_noUG`;
`UpCascOKHGJ` and the walk carry the heights' bound in `KdHtJ`); and
`hchk` without `htb` (as in the 13:40 entry).

2026-11-15, 14:10 to 14:25. Part 2, step 7: the stratum family whole
(prover htb). New file SIS/Tree/StratumCasc.lean; additions in
WriterGetUpTake.lean, DelStepsBookK.lean, DelStepsGh.lean,
DelHoleClimb.lean, DelStepsCascRoot.lean, StopSwapBelow.lean. No statement
changed.

- **The three cases that empty the leaf**, proved: the space root
  (`delStepsCaseTJ_emptyRoot`, the root's bitmap or split by the tree-facts
  forms), room above the leaf (`delStepsCaseTJ_emptyRoom` over the walk
  `writerWP_del_emptyRoomMJKT`), the stop node's cascade
  (`delStepsCaseTJ_emptyCasc` over `writerWP_del_emptyAnyMJKT` and the
  obligation `UpCascJ2OKT`, proved: `upCascJ2OKT_holds`). So the family
  holds (`delStepsTJA_holds`), and the first stratum needs only `hchk`:
  `jointHtJ_reachedS` (StratumCasc.lean), the joint induction with no
  `htb`, from the put cases, the live counts and `hchk`.
- **The upward walks with the fit at any depth:** the fit at the start of
  the upward delete fed only `CollGetInv`'s fit, so `collGetInvD_after_upT`
  (`CollGetInvD`, the fit at a depth d), `takeJ2_deleteUpward_upTMBKD`,
  `takeJ2_deleteUpward_stepMBKGD` and `rwp_deleteUpwardP2_climbMBD` take it
  at any d; the stratum takes d the next id (P1). The old lemmas are their
  instances at p.fuel - 1 (`collGetInv_of_D`).
- **The stop node's split without the fits:** `writerWP_upCasc_root_delT`
  and `writerWP_upCasc_below_delST` give the tree's facts with no fit at the
  start and none after, `DelInv` where both hold; the old lemmas are their
  corollaries with the fit after (`hFits`). The heights served the cascade
  only for that fit (`UpCascFitsOKR`), so the stratum's cascade walk is the
  kinds' walk, with no heights.

**Left of step 7:** `hchk` without `htb`. The chain is that of the 13:40
entry: `OpDelChk6OKR` and `OpDelChk7OKR` with `DelHoleJE` (new
definitions), their leaf's and climb's proofs with the tree-facts forms
(the climb as `rwp_climb_of_J` over `rwp_deleteUpwardP2_climbMBD` and
`UpCascJ2OKT`), and `OpDelChk8OKR` by the same route with the merges'
loop checked from `DelInvJAE` (`rwp_mergeUp_of_JAE`).
