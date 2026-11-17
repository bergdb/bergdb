011-12. The Lean model's log: lean/README.md's Status until 2026-11-07
======================================================================

The dated log of the Lean model (`lean/`), from its start on 2026-10-12 to
2026-10-28: the milestones, the theorems proved, the checks run, and the
changes to the trusted part. It was the section Status of `lean/README.md`
until 2026-11-07, when it moved here, as it was, with its links fixed for
this place (bergdb 021-02; AGENTS.md: progress logs belong in an item).
`lean/README.md`'s Status keeps the current state, without dates. Its
first entry is the line of `lean/README.md`'s header that named its
author.


Log
===

2026-10-12. Started. Written by Claude for Frans Lundberg. (Moved here from
lean/README.md's header on 2026-11-07, at Frans's word, 2026-11-07, 08:00:
006-13, section 5, morning list, point 1; as 006-12, section 8, point 10,
option (b).)

2026-10-12. Milestone 1: the definitions, the assumptions, T1 and T2
stated, the examples. The first random runs found a gap in sis-model.md:
Rule R must also follow vpos pointers. Fixed.

2026-10-12. Milestones 2 to 5: T1 and T2 proven, in the strong forms
`T1_strong` (startup gives back every node, with its whole history, and D)
and `T2_strong` (a run with restarts stays in step with the run without).
`lake build` passes with no warnings and no `sorry`; `#print axioms` shows
only Lean's standard axioms. `lake exe sistest 20 40` passes.

2026-10-13. Fresh documentation-review checks: `lake build` passed all
27 jobs; `lake exe sistest 20 40` reported assumptions, T1 and T2 passing
20/20 seeds for each of eight algorithm variants. A fresh `#print axioms`
check of T1_recovery, T1_crash, T1_nodes and T2_restart printed only
`[propext, Classical.choice, Quot.sound]`. This reconfirms the existing
proofs; no new theorem or Java validation is implied. `good_mono` is
stability of a fixed version as the logical structure grows, not the
unproved Java lemma M about substituting a newer version.

2026-10-15. Marking (WP E1 of F1-008-11, repository f1): A5 added to the
assumptions, step 3 by marking (`Algo.mark`), T13 proven, and T1 and T2 for
both ways of step 3. `lake build` passes with no warnings and no `sorry`;
`lake exe sistest 20 40` passes for 16 algorithms, and marking gives the same
records as testing for 20/20 seeds; `#print axioms` of T1, T2 and
`T13_markExact` shows only Lean's standard axioms. Also new: the trace
checker (Check/, TraceCheck.lean), not part of the trusted part.

2026-10-15. BergDB's still-dirty test (WP E2 of F1-008-11): `javaTest`, Rule
A over all pointers, as in bergdb's `DbHelper.hasDirtyChild`. T1, T2 and T13
now hold for both still-dirty tests, the exact one and BergDB's
(`Proof/Still.lean`: the proofs need only that the test looks at P through
its nodes and puts back every written node that is still dirty; BergDB's
test does, because step 7 tests the written nodes lowest level first).
Together with marking, the model's bookkeeping is now BergDB's. `lake build`
passes with no warnings and no `sorry`; `#print axioms` as above.

2026-10-16. The remaining Level 2 model changes (WP E3 of F1-008-11): the
virtual root of option (a), Rule R from R(s) on (M7), and a policy that sees
the transaction (M10). T1, T2 and T13 hold with and without a virtual root.
`lake build` passes with no warnings and no `sorry`; `#print axioms` as above;
`lake exe sistest 20 40` passes for the 16 algorithms of the second structure
and the 8 of the third (the virtual root). The trace checker now runs the
model's own `init` and `step`, with no checker-local definitions, and checks
R1 to R4 (C-A).

2026-10-16. The conformance campaign (WP F1 of F1-008-11): on bergdb
`8f37d88`, the checker found every transaction of 59 traces of Java runs (50
small, 9 medium) a step of the model in the target mode, with no change to
the model (011-11, 10.5).

2026-10-16. Lemma M (bergdb item 001, WP L2): `LM_newer`, `LM_ruleR` and
`LM_cutTo` proved; `lake build` passes with no warnings and no `sorry`;
`#print axioms` shows only Lean's standard axioms; sistest also checks lemma
M by running.

2026-10-16. The physical layer, part 1 (bergdb item 001, WP L1): Java's
first touch and lazy startup in SIS/Phys.lean; `lake build` passes with no
warnings, with the `#guard` checks of SIS/PhysExample.lean; `lake exe phystest
20 40` passes (every read gives P, every canonical object whole, also from
prefixes of the stream).

2026-10-16. T1-L proved (bergdb item 001, WP L3): `T1_lazy`, with the proofs
in SIS/Proof/Fresh.lean and SIS/Proof/Phys*.lean; three refinements of the
lazy startup and two assumptions of the physical layer, below. `lake build`
passes with no warnings and no `sorry`; `#print axioms SIS.T1_lazy` shows only
Lean's standard axioms; `lake exe phystest 20 40` passes.

2026-10-16. CC and T2-L proved (bergdb item 001, WP L4): `CC_canonical` and
`T2_lazy`, for runs with lazy restarts whose writer works through the physical
layer (SIS/Proof/PhysFrozen.lean, PhysT2.lean). `lake build` passes with no
warnings and no `sorry`; `#print axioms` shows only Lean's standard axioms;
`lake exe phystest 20 40` passes, with runs with lazy restarts.

2026-10-17. T-CACHE proved (bergdb item 001, WP E3): `TC_records`, for runs
with eviction, any cache schedule and no restart, from the Level 4 startup
from R(0); and D closed upward (`T15_closed`, F1-008-08's T15), which the
proof needs for BergDB's bookkeeping. The proofs are in SIS/Proof/Evict*.lean.
`lake build` passes with no warnings and no `sorry`; `#print axioms` shows
only Lean's standard axioms; `lake exe phystest 20 40` passes.

2026-10-17. T-READ proved (bergdb item 001, WP E4): `TR_view`, for the same
runs: a read through the Level 4 loader at any time up to the last record
gives P at that time. The proofs are in SIS/Proof/EvictHist.lean,
EvictHistTrans.lean and EvictReadT.lean; `lake build` passes with no
warnings and no `sorry`; `#print axioms` shows only Lean's standard axioms.

2026-10-17. T2-C proved (bergdb item 001, WP E5): `T2_cache`, for the runs of
T-CACHE with restarts after any transactions: the records and D stay the
model's, P keeps the model's nodes, and the invariants of `TC_records` hold
for the stream of the last startup. And T-READ for the same runs
(`TR_view_restarts`). The proofs are in SIS/Proof/EvictRerun.lean and
EvictRestart.lean; `lake build` passes with no warnings and no `sorry`;
`#print axioms` shows only Lean's standard axioms; `lake exe phystest 20 40`
passes.

2026-10-17. T-PIN proved (bergdb item 001, WP E6): `TP_pins`, for the same
runs: every object outside the pinned set has been written, and unswizzling
its memory slots and then releasing it removes it. The proofs are in
SIS/Proof/EvictKeys.lean and EvictPin.lean; `lake build` passes with no
warnings and no `sorry`; `#print axioms` shows only Lean's standard axioms.

2026-10-17. Level 3, the definitions (bergdb item 001, WP R3): the touch, the
first available time, cuts, and runs that restart from cut streams; T13'
proved (`T13_markTouch`); every theorem above holds with touches. `lake
build` passes with no warnings and no `sorry`; `#print axioms` shows only
Lean's standard axioms; `lake exe reclaimtest 20 30` passes: for four startup
pos policies and 20 seeds, the assumptions and `PolicyCutOK`, T8 at every
restart and T12 hold at the largest safe cut, and with eviction 9,600
transactions are checked, none fails.

2026-10-17. The checker on Java's reclaim traces (bergdb item 001, WP R7): it
reads reclaim's lines (TOUCH, FA, CUT, PHYSCUT); C-A checks TouchOK, C-S
compares fa(i) and runs the steps on the cut stream, and C-CUT (new) checks
`CutOK` at every cut. On R2's reclaim sets (small: 25 traces, 14,448
transactions, 288 cuts; medium: rm-mixed-1 and rm-mixed-2, 4,415 transactions,
47 cuts, while its four largest traces were still in the checker), `CutOK`
holds at every cut Java decided, and every other failure is of one kind,
register M17: in a reclaim step, Java's gd(i) keeps
the marks of the nodes that the step's puts mark and replace (the red list,
[001-07](../001-lean-model-levels-3-4/07-level3-alignment.md), section 6). On the
way, `CutOK`'s part 2 was changed, found by running (`staleWitness`, below).
`lake build` passes with no warnings and no `sorry`; `#print axioms` shows
only Lean's standard axioms; the trace tests pass. The medium set's four
largest traces finished later the same day: the same, with `CutOK` at every
one of the set's 174 cuts.

2026-10-17. T8 proved (bergdb item 001, WP R4): `T8_recoverCut`, after a
safe cut, startup from the cut stream gives the same lookups at every time
from the first available time on, and the same D; with a virtual root it
needs `ExecRootOK` and `VirtLiveOK`, which example 4 meets (proved). The
proofs are in SIS/Proof/CutStream.lean to CutRecover.lean. T9 is stopped
(stop rule 4 of the plan): `cutReadWitness` is a run where `CutOK` holds and a
read in the running process, with eviction, follows a replaced node's
pointer to a version before the cut. T9 needs a stronger `CutOK` or a change
of the physical layer, which is Frans's decision
([001-07](../001-lean-model-levels-3-4/07-level3-alignment.md), 2.9, register
M48); the checker's new diagnostic C-CUT+ finds that Java's cuts meet the
stronger condition. `lake build` passes with no warnings and no `sorry`;
`#print axioms` shows only Lean's standard axioms; `lake exe reclaimtest 20
30` passes.

Changes to the trusted part while proving, all on 2026-10-12:

* A2 (`StepOK.current`): entries only to nodes reachable at time i after
  the change, instead of reachable at time i-1 or new. Without it, a
  transaction could add an entry to a node and cut it off in the same step;
  startup could not rebuild that entry. See sis-model.md, section 14.
* A3: `noResurrection` removed; the proofs do not need it.
* `step` split into named parts (`gotDirtyOf`, `startupPos`,
  `stillDirtyOf`), and step 3 lists nodes through `allIds` and `isIndex`.
  The same algorithm, written so that it does not depend on the order of
  nodes in P.
* The assumptions moved from Theorems.lean to Assumptions.lean.
* `T1_crash` added: T1 stated for a crash after any T(k), from the first
  k+1 records of a longer run's stream.
* `T1_nodes` added: the stronger form of T1.

Changes to the trusted part on 2026-10-15 (F1-008-11, WP E1;
[011-11](11-level2-alignment.md), M2):

* A5, no resurrection (`StepOK.noRes`): a node reachable after a transaction
  was reachable before it, or is new. Added because marking needs it: a node
  that becomes reachable again with nothing changed below it could be dirty
  without being on the access path of the change. BergDB meets it (the trace
  checker found no failure).
* Step 3 may mark the access path of the change instead of testing every
  index node (`Algo.mark`, default false; `changed`, `marked`, `markOf`):
  BergDB's way. T13 (`T13_markExact`): for an index node not in D, marked is
  the same as dirty, so both ways give the same records, and T1 and T2 hold
  for both (their proofs use T13 when `al.mark` is true).
* BergDB's still-dirty test, `javaTest` (WP E2): a written node goes back
  into D if one of its pointees, live or dead, is in D. The hypothesis of T1,
  T2 and T13 changed from `al.stillDirty = exactTest sp` to
  `al.stillDirty = exactTest sp ∨ al.stillDirty = javaTest sp`: the theorems
  now cover both tests.

Changes to the trusted part on 2026-10-16 (F1-008-11, WP E3;
[011-11](11-level2-alignment.md), M7, M10, M11 and
section 8):

* M7: `newest`, and so Rule R, looks at R(s), ..., R(k), as BergDB's
  `DbStarter.createMaps` does, instead of R(s+1), ..., R(k). The proofs needed
  only `<` changed to `≤` in L-SEC.
* M10: the startup pos policy also gets the transaction T(i)
  (`Algo.policy`, `startupPos`), as BergDB's `TransSeq.take` depends on the
  transaction's size.
* M11, option (a) of Q7, the virtual root. `Spec` gets `virt` (default
  false: the root is an ordinary node, as before), `topLevel` and `rootVal`.
  With `virt`: step 3 never gives the root (`written`), R(0) does not write it,
  and top(i) names the root's child at s(i) and the record of its latest
  version (`topOf`, `topV`); `Record.top` is now a node and a record. Startup
  reads the root children from that version through their pointers, live or
  dead (`readTops`, with Rule R), and rebuilds the root (`rootVersion`), then
  reads as before (`startVersion`).
* With a virtual root, new assumptions (`VirtInit`, `VirtStep`): R1, the
  root's entry for child z points to z; at most one initial root child and at
  most one new root child per transaction, an index node with entries; R3, a
  root child gets entries only in the transaction that creates it; R2, the
  root gets exactly the entry for the new root child; R4, every older root
  child can be reached from the new one through pointers between root
  children; and a root child that a root child points to is not reachable.
  BergDB meets them (the trace checker checks them, C-A).
* The hypothesis of T1, T2 and T13: BergDB's still-dirty test, or, without a
  virtual root, the exact one. With a virtual root the proofs need BergDB's
  test: it puts a written top node back into D when an older top node it
  points to is in D, so the latest version of a top node that stayed clean
  names the latest versions of the older top nodes it points to
  (`VInv.fresh`), and startup, which finds older top nodes only through these
  references, reads them right. With the exact test a top node can keep a
  reference to a stale version of an older top node: `exactWitness3` in
  SIS/Example.lean is a run where T1 then fails.
* T13's statement says "an index node other than a virtual root"
  (`written`).

Changes to the trusted part on 2026-10-16 (bergdb item 001, WP L2;
[011-11](11-level2-alignment.md), M8): two new
files; nothing that was there changed.

* SIS/Phys.lean, the start of the physical layer: `Version.cutTo`, a version
  cut back to a time, as BergDB's `KeyNode.toPreviousState` cuts back a
  version of the startup section to the startup time.
* SIS/PhysTheorems.lean, lemma M: `LM_newer`, a version of a node written at
  or after a version that is good for time t is good for t too; `LM_ruleR`,
  so is the newest version in R(s), ..., R(k), which Rule R follows; and
  `LM_cutTo`, a version cut back to s is good for a time t ≤ s exactly when
  the whole version is. Checked by running too: sistest counts the cases
  (`lemmaMCheck` in SIS/Example.lean).

Changes to the trusted part on 2026-10-16 (bergdb item 001, WP L1;
[011-11](11-level2-alignment.md), section 13):
SIS/Phys.lean gets the physical layer, part 1, as BergDB reads today:

* `Slot`, `Obj`, `Mem`: objects with identity (by handle), their slots
  (memory or stream), their canonical flag and position; the node table; the
  startup pos of Rule R; the root's object.
* Java's first touch, `Mem.follow` (`NodeCollection.followPointer`,
  `followStreamPointer`, `WriterFollower`): Rule R for the whole process
  (`ruleRRef`), the node table's object if canonical or at least as new
  (`Obj.usable`), else the version read (`Obj.ofVersion`), cut back to s if it
  is a key node version of the section (`isKeyLevel`), entered in the table
  (`Mem.register`, `Obj.better`); the slot swizzled; the writer's promotion
  (`Mem.makeCanonical`).
* Reads, `Mem.read` and `Mem.readAt`: from the root's object at time t, down
  the live children, through the readers' follower.
* The lazy startup, `lazyStartup` (`DbStarter.doOrdinaryStartup`): the
  section's index nodes as canonical objects (`sectionNodes`,
  `canonOfVersion`), the root's object, memory slots between canonical
  objects (`Mem.linkCanonical`), and the rerun: the writer's paths (`pathOf`,
  `Mem.reachOnPath`), the change on the canonical objects (`Mem.applyChange`,
  `Mem.newSlot`), the nodes of D (`Mem.canonicalNode`).

Nothing that was there changed. What the layer leaves out: section 13.1 of
011-11.

Changes to the trusted part on 2026-10-16 (bergdb item 001, WP L3;
[011-11](11-level2-alignment.md), section 13.3),
found while proving T1-L and checked by running (phystest) before the
proofs:

* `lazyStartup`, step 1: a node of the section whose newest version has no
  entries up to s gets no canonical object at startup, as in Java
  (`wasCreatedInRerunSection`); the rerun makes it canonical when the writer
  reaches or creates it. Before, a node created after s got two canonical
  objects, one at startup and one when the rerun created it.
* `Mem.newSlot`, the slot of a new pointer: the slot it copies is that of a
  canonical object whose node is reachable at j - 1 and has the pointee as a
  live child then (`srcOK`), else the object's own slot for the pointee,
  else any canonical object's; and it is taken from the objects as they were
  before the transaction's entries. `Mem.applyChange` gives every pointee of
  a new entry this slot (`Obj.putSlot`), also one the object already had a
  slot for: the new pointer's slot replaces the old one.
* New, for the statement of T1-L: the operations after startup (`Op`: a
  read at a time, or the writer's follow of a slot; `Mem.step`) and when they
  are admissible (`OpsOK`, `Mem.writable`: reads up to the last time; the
  writer follows live slots of canonical objects of reachable nodes).
* New assumptions of the physical layer (`PhysStep`, for every transaction:
  `PhysRunOK`; register M47): a node's new live children are pointees of its
  new entries (`liveNew`), and a new live child of a reachable node that the
  transaction does not create was, just before, a live child of a reachable
  node that the transaction changes or replaces (`adopt`: the node a split
  takes it from). BergDB meets both (a klong stays live until a later klong
  of its key; a split's new nodes take the children of the node they split,
  M43); examples 2 and 3 meet them (`physRunOKB`).
* T1-L (`T1_lazy`) in SIS/PhysTheorems.lean.

Changes to the trusted part on 2026-10-16 (bergdb item 001, WP L4;
[011-11](11-level2-alignment.md), section 13.4):

* A read returns nodes, not only histories: for each node it reaches, the
  node that its object gives at the time, with its level and kind
  (`Mem.readAt`, `Mem.read`, `Obj.nodeAt`), as Java's reads return node
  contents. So the writer can take its view of P from a read. T1-L's first
  part now says that a read reaches exactly the nodes reachable at t, each
  with its node in P@t; before, it gave the histories only.
* New: `stepWith`, steps 2 to 8 of `step` with the change given (`step` is
  `stepWith` with step 1's change, `step_eq_stepWith`, by `rfl`); the
  writer's view through the physical layer (`Mem.view`); one transaction of
  the writer after a lazy startup (`lazyTrans`: the change from the view the
  writer reads at i - 1; the writer reaches the nodes of its paths, highest
  level first, and applies the change to the canonical objects, as the rerun
  does; Rule R and the versions read come from the stream at the startup, as
  Java's section map); a run with lazy restarts (`runLazy`).
* CC (`CC_canonical`) and T2-L (`T2_lazy`) in SIS/PhysTheorems.lean.

What T2-L does not cover yet: the versions and references the writer writes
still come from ⟨P, D, S⟩ (`mkVersion`: the node's history in P, references
from `S.lv`). Computing them from the canonical objects and their slots is
stage 2 (bergdb item 001, WP E3); so are steps 3 and 7 by the physical
writer.

Changes to the trusted part on 2026-10-16 and 17 (bergdb item 001, WP E2;
[001-08](../001-lean-model-levels-3-4/08-level4-alignment.md), section 5, the
design of E1, and 5.10, what E2 found): a new file, SIS/Evict.lean, the
physical layer, part 2, with eviction. Nothing that was there changed.

* Pins and eviction: the pinned objects (`Mem.pinned`: the canonical
  objects of D's nodes, the root's object); objects that may be detached
  (`Mem.detachable`: not pinned, written) and released (`Mem.eligible`: also
  no memory slot to them, `Mem.incoming`); unswizzling (`Mem.unswizzle`: a
  memory slot to a detachable object becomes a stream slot naming its
  position) and release (`Mem.release`: the object leaves memory and the node
  table).
* The Level 4 loader (`Mem.follow4`, Q7 of the plan): the node table's
  canonical object, else exactly the version the slot names after Rule R,
  not cut back and not entered in the table; the writer's promotion
  (`Mem.promote`); reads through it (`Mem.readAt4`, `Mem.read4`,
  `Mem.view4`) and the writer's path (`Mem.reachOnPath4`, which follows the
  parent's slot also when the node has a canonical object, as Java's writer
  walks from the root). Rule R comes from the stream of the last startup,
  versions from the stream now.
* The change applied to the canonical objects (`Mem.applyChange4`): as stage
  1's, with the slot of a new pointer from `Mem.newSlot4`: the pointee's
  canonical object, else a copy of the slot of a canonical object of a node
  reachable before the change that has the pointee in its history (`srcOK4`;
  live there, for a virtual root), else the object's own. Stage 1's last
  resort, a copy from any canonical object, is gone.
* Startup, Level 4 (`evictStartup`): stage 1's `lazyStartup`, the positions
  of its canonical objects as Java sets them (`Mem.sectionPos`), and rule 4,
  D's objects linked by node id (`Mem.linkD`).
* The physical writer: the reference for a pointee (`Mem.refOf`: a pinned
  pointee's canonical object's position, else the slot's), a node's version
  from its canonical object (`Mem.writeNode`, `writeNodes`), and one
  transaction (`evictTrans`: as `lazyTrans`, with the record's versions from
  the objects; the rest is step's).
* Cache schedules and runs: `CacheOp` (a read, an unswizzle, a release),
  `Mem.cacheOp`, `runEvict` (transactions, each followed by its cache
  operations, and restarts).
* The assumptions of stage 2: TREE (`treeAt`) and A6' (`adoptAt`), in
  `EvictStep`, after every transaction of a run, and A-COPY (`CopyStep`: the
  pointer of a new entry names a node of the writer's paths or a pointee of
  one) for its change (`EvictRunOK`).

Checked by running before any proof (SIS/EvictExample.lean, `phystest`'s
eviction part): examples 2, 3 and a new example 5 (example 3 with drops, a
leaf replaced by an empty one, so a subtree goes cold), with restarts and four
cache schedules (none; every object that may be detached, after every
transaction; each with probability 0.3; and unswizzles and releases apart,
so that objects stay with some slots unswizzled): after every transaction the
records and D are the model's, reads give P, and INV-CAN, INV-SNAP and
INV-SLOT hold; the examples meet TREE, A6' and A-COPY. 20 seeds of 40
transactions, 25,600 transactions, none fails. Without rule 4 (the startup
links nothing by id), example 3 writes a wrong record (seed 8 of 10, after a
restart): the gap of the plan's 8.5.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E3): two new
statements in SIS/PhysTheorems.lean, D closed upward (`T15_closed`) and
T-CACHE (`TC_records`); nothing else. The changes that E3's proofs asked of the
model (the writer's walk, `Mem.newSlot4` and A-COPY) were made in
SIS/Evict.lean before E2 was committed (above;
[001-08](../001-lean-model-levels-3-4/08-level4-alignment.md), 5.10).

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E4): one new
statement in SIS/PhysTheorems.lean, T-READ (`TR_view`); nothing else.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E5;
[001-08](../001-lean-model-levels-3-4/08-level4-alignment.md), 5.13; register
M44):

* Rule 4 (`Mem.linkD`, used by `evictStartup`) links the slots of the root's
  object too, besides those of D's canonical objects: all the pinned
  objects. Reason: the invariant needs a current canonical object's live
  slot to a node of D to be a memory slot to its canonical object; for D's
  objects rule 4 gives it, and the root's object, of a virtual root, is
  never in D. The startup's rerun leaves that slot a memory slot in every
  startup of the examples, but a proof would have to follow the virtual
  root's slots through the rerun. Java's virtual root holds its super root
  as a memory reference to its canonical object (`TopDs.superRoot`), so the
  model now says what Java does. No record changes: a virtual root is never
  written, and a written root with a pointee in D is in D itself.
* Two new statements in SIS/PhysTheorems.lean, T2-C (`T2_cache`) and T-READ
  with restarts (`TR_view_restarts`).

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E6): one new
statement in SIS/PhysTheorems.lean, T-PIN (`TP_pins`); nothing else.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R3;
[001-07](../001-lean-model-levels-3-4/07-level3-alignment.md), register M17,
M32, M33, M36 and M41, and 2.8):

* The touch (M17, Q6 of the plan): `Changes.touch`, the index nodes that a
  transaction's touch makes dirty without giving them entries (Java's
  `Db.touchRange`), none by default. The plan said `Spec.touch`; the touch
  is part of a transaction's changes, a function of T(i), i and P@(i-1) as
  the rest of them (A1). Step 3 adds the touched index nodes not in D that
  it did not find otherwise (`touchOf`), after the others, and never a
  virtual root; step 3 is now a function, `gotDirty3`, used by `step`,
  `stepWith` and `evictTrans`. The writer's paths reach the touched nodes
  (`pathOf`).
* The touch's assumptions, the plan's TouchOK, in `StepOK`: the touched
  nodes are index nodes reachable at i-1 (`touchIndex`, `touchReach`), and
  every node reachable at i-1 with a touched node below it then is touched
  too, or is a virtual root (`touchUp`): Java's range traversal walks down
  from the super root. The proofs need `touchUp`, transitively: a clean
  node with a touched node below it would be outside D with a pointee in D.
  Without a touch the three say nothing.
* The first available time (M32, Q5): `Record.fa`, 0 by default, and
  `Algo.faPolicy`, 0 by default; step 4 clamps the policy so that fa never
  decreases and stays at most the startup pos (`lastFa`, `firstAvail`).
* SIS/Reclaim.lean, new: version stubs (`Version.stub`: a cut keeps a
  version's node, record number, level and kind, as Java's slots keep
  positions), records cut (`Record.cut`: the stubs, no transaction, no gd
  list), `cutStream`; `CutOK` (the plan's 8.7 with part 3 refined: every
  reference below the cut of the latest version of a node in D names the
  latest version of its node, which is the pSafe wait, M33 and M41; part 4
  is implied by part 2); `SameFrom`, the same lookups from f on,
  with a virtual root compared by its live children (a startup from a cut
  stream rebuilds the root without the root children it cannot read); and,
  for R4 to R6: `PolicyCutOK`, `ExecRootOK`, `runRestartsCut`, `cutMax`,
  `runEvictCut`.
* SIS/ReclaimTheorems.lean, new: T13' (`T13_markTouch`).

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R7;
[001-07](../001-lean-model-levels-3-4/07-level3-alignment.md), 2.8):

* `CutOK`'s part 2: every version that a lookup at some time from f to k may
  read (`ReadsAt`, new: the latest versions of the nodes reachable then, and
  the versions that their pointers to live children lead to, with Rule R) is
  at the cut or later; R3's asked this of the latest versions only. Reason: a
  run of the model (`staleWitness`) where R3's condition holds and a physical
  read at the first available time, after a restart from the cut stream,
  reads a stub: a tree root reachable then, and replaced later, names an
  older version of a child whose latest version is after the cut. In the
  random runs of `reclaimtest` the two give the same cuts.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R4;
[001-07](../001-lean-model-levels-3-4/07-level3-alignment.md), 2.9):

* `VirtLiveOK` (new, SIS/Reclaim.lean): with a virtual root, the live
  children of a history of root entries are the pointers of its last entry
  (BergDB's TopDs: the super root at a time is the newest top node created
  up to it). T8 needs it: startup rebuilds the root without the entries that
  the cut made unreadable, and only so does that leave the live children
  from f on as they are. Example 4 meets it (`virtLiveOK_spec4`).
* `ExecRootOK` (R3's) asks its condition only of views whose roots hold root
  entries: a weaker assumption, so the theorems that use it say more. As R3
  stated it, example 4 could not meet it, since its transactions read the
  root's entries as slots, and a view's root could hold any entries; now it
  does (`execRootOK_spec4`). T8 uses it for the reruns of the startup
  section, whose views' roots hold root entries.
* SIS/ReclaimTheorems.lean: T8 (`T8_recoverCut`), new.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R6, part 1;
register M48 of [001-07](../001-lean-model-levels-3-4/07-level3-alignment.md),
option (a), Frans):

* `ReadsPhys` (new, SIS/Reclaim.lean): the versions that a read at time t may
  follow, a lookup's (`ReadsAt`) or a physical read's in the running process:
  through a pointer of one of them to a live child, also every version of the
  child at or after the record that the pointer names (every version if it
  names none). A memory's Rule R is that of its last startup, and its objects
  can be newer than a pointer; a version that either gives is such a one.
* `CutOK`'s part 2 over `ReadsPhys` instead of `ReadsAt`: a stronger
  condition. Reason: `cutReadWitness`, a run where R7's `CutOK` holds and a
  read in the running process with eviction follows a replaced node's pointer
  to a version before the cut (WP R4, T9 stopped). T8's statement is
  unchanged (its hypothesis is now stronger); its proof takes each version a
  lookup reads to `ReadsPhys` (`ReadsAt.phys`). In example 4's fixed run the
  stronger part rules out that cut and, in `pSafeWitness`, the cut before
  the pSafe wait already by part 2; the other `#guard`s are unchanged.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R6, part 1b;
[001-07](../001-lean-model-levels-3-4/07-level3-alignment.md), 2.9):

* `ReadsPhys` takes D, and does not extend through a version that Rule A put
  back and that is still in D ((x, r) ∈ D, r the version's record): through
  it, only what a lookup reads (Rule R). The running memory has held that
  node's canonical object since it wrote the version (D is pinned), and
  reads through its slots, which name the latest versions; no snapshot of
  the version exists. Reason: T-SCHEME, tried by running before proving,
  fails without it (`schemeWitness`, SIS/ReclaimExample.lean): a run of
  example 4 that meets Java's scheme, with its strict waits, where a stale
  chain of put-back versions during the settling (tree root, mid node, leaf)
  leads below the cut, while the running memory's reads, with every cache
  schedule, give P on the cut stream. `CutOK` is weaker by this; T8 is
  unchanged (`ReadsAt.phys` uses the lookups' part). `pSafeWitness`'s cut
  before the wait is ruled out by part 3 only again, as by R7's `CutOK`.

2026-10-17. T12 proved (bergdb item 001, WP R5): `T12_restartCut`, a run
that restarts from safe cut streams appends the records of the run without
restarts, cut at the largest cut, and has its D and its lookups from the
first available time on; for BergDB's bookkeeping (marking and `javaTest`),
with T8's assumptions and `PolicyCutOK`, and without A6'. The nodes of D that
no lookup from f on reaches are the delicate case (M33, M34): their
ancestors at a time they were reachable stay in D, put back by Rule A with
versions after the startup pos, and startup reads them through these (Rule
R). The proofs are in SIS/Proof/CutRestart.lean, CutHist.lean,
CutHistRead.lean and CutRuns.lean. `lake build` passes with no warnings and
no `sorry`; `#print axioms` shows only Lean's standard axioms; `lake exe
reclaimtest 20 30` passes (its runs had 125 cuts with a node in D that no
lookup from f on reaches). T12 with eviction (`runEvictCut`) follows T9.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R5): T12
(`T12_restartCut`, SIS/ReclaimTheorems.lean), new. No definition changed.

2026-10-17. T9 proved (bergdb item 001, WP R4): `T9_readCut`, in a run with
eviction as in T2-C (any cache schedules, restarts after any transactions),
after any transaction and its cache operations or its restart, with `CutOK`
at c: a read through the Level 4 loader in the running process, at any time
from the first available time to the last record, gives the same on the
stream cut at c as on the whole stream, so it needs no record before the cut,
and gives P at that time. The proof is an invariant on the slots (`CInv`,
the table above): a read from f on follows only canonical objects and
versions that `CutOK`'s part 2 covers (`ReadsPhys`). The proofs are in
SIS/Proof/CutPhys.lean, CutPhysTrans.lean and CutPhysRun.lean. `lake build`
passes with no warnings and no `sorry`; `#print axioms` shows only Lean's
standard axioms; `lake exe reclaimtest 20 30` passes (its runs with eviction
read from f on, on the cut stream, from the running memory).

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R4, T9): T9
(`T9_readCut`, SIS/ReclaimTheorems.lean), new; SIS/ReclaimTheorems.lean
imports SIS/PhysTheorems.lean (T9's second half is `TR_view_restarts`). No
definition changed.

2026-10-17. T12 with eviction proved (bergdb item 001, WP R5):
`T12_evictCut`, the run with eviction that restarts from safe cut streams
(`runEvictCut`, the Level 4 startup at each restart), with any cache
schedules whose reads are at times from the first available time on,
appends the records of the run without restarts, cut at the largest cut, and
has its D and its lookups from the first available time on; with the
assumptions of T12 and of T2-C. It has the states of the run without
eviction that restarts from the same cut streams (`evictCut_restartsCut`),
through the run with eviction that restarts from the whole streams at the
same points: the memories are the same but for a virtual root's object,
rebuilt from the root children that the cut stream still has, and where its
entry is in the list of objects (the table above). The proofs are in
SIS/Proof/CutLater.lean to CutLaterRun.lean. `lake build` passes with no
warnings and no `sorry`; `#print axioms` shows only Lean's standard axioms;
`lake exe reclaimtest 20 30` passes.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP R5, T12 with
eviction): T12 with eviction (`T12_evictCut`, SIS/ReclaimTheorems.lean), new;
SIS/ReclaimTheorems.lean imports SIS/Proof/CutLaterRun.lean. No definition
changed.

Changes to the trusted part on 2026-10-23 (bergdb item 007, T3): two new
files. SIS/Bound.lean: `Stream.cost`, `sdTarget`, `KeepsUp`, `sdPolicy`.
SIS/BoundTheorems.lean: `T3_section`, `T3_restarts`, `T3_reads`,
`T3_rerun`, `T3_bounded`. No definition changed. `lake build` passes with
no warnings and no `sorry`; `#print axioms` shows only Lean's standard
axioms.

2026-10-25. Handles (bergdb item 009, phase 2): steps 2a to 2c
(SIS/Handle.lean, SIS/HandleExample.lean, SIS/HandleTheorems.lean), the
alignment with Java's step 3a, and 2d: T-CACHE over handles is proved
(`tc_handles`, `TC_handles_records`; SIS/Proof/Handle*.lean). T2-C, T-READ
and T-PIN over handles are stated as definitions, not proved. Nothing that was
there changed. `lake build` passes with no warnings and no `sorry`; `#print
axioms` shows only Lean's standard axioms.

2026-10-26. Handles, phase 4a (bergdb item 009): T-READ, T2-C, T-READ with
restarts and T-PIN over handles are proved (`tr_handles`, `t2_handles`,
`tr_handles_restarts`, `tp_handles`; SIS/Proof/HandleHist.lean,
HandleHistTrans.lean, HandleReadT.lean, HandleRestart.lean, HandlePin.lean),
as E4 to E6 prove them for Evict.lean. The invariant for reads at earlier
times over handles (`HInvH`) asks of the pointer of a canonical object what a
read at t needs: that it holds a canonical object, or that its slow path's
reference names a version good for t, or INV-SLOT's second half. Rule R's
written-back reference keeps it, and so does an eviction: a canonical object
that may be evicted is of a node not in D, so the written position its handle
gets is its node's latest version, good for every time at which the node is
reachable. Changes to earlier proofs: the readers' follow states more
(`HFollowed`, HandleFollow.lean: what the pointers give is kept,
`HMem.KeepPtrs`; where the canonical objects after it come from; the parent's
pointer; the object reached serves the slow path's reference); E5's rerun
invariant records that every stream slot names a version (`RInv.ver`,
EvictRerun.lean), which the startup with handles from the stream after T(k)
needs, since its pointers keep the stream slots' references; and
`HEInv.relinkH` (HandleInit.lean) lets a pointer that takes the pointee's
live handle have any reference that names a version (Evict.lean's rule 4
gives such a pointer the canonical object's position, rule 4 with handles
keeps the stream slot's). Changes to the trusted part: comments only
(SIS/Handle.lean's and SIS/HandleTheorems.lean's, on what is proved). `lake
build` passes with no warnings and no `sorry`; `#print axioms` shows only
Lean's standard axioms.

2026-10-26. Handles, step 4c (bergdb item 009): the trace checker's C-H
(Check/Steps.lean, `toHMem` and `handleFailures`; Check/Trace.lean reads the
new lines; TraceCheck.lean). Java's trace exporter writes run E's memory as
the model's memory with handles at the end of each transaction (HMEM, HTABLE,
HANDLE, HOBJ and HPTR lines, trace format 2; docs/trace-format.md, 2),
and C-H checks it against the invariants of SIS/HandleTheorems.lean, with
the model's own definitions where they decide (`HMem.refOf` for the record
rule, `HMem.canonicalOf`, `HObj.usable`, `ruleRRef`, `maxRef`, `newest`,
`HMem.pinned`, `HMem.evictable`); 009-05, section 4, says
what it checks and what it cannot. Run E got reads and restarts between its
transactions (the exporter's `ereads`, `erestart`), so that its states hold
snapshots and the startups' memories. On `conformance.sh evict` (15
configurations, 3 seeds): 45 traces, 8,520 states, C-H 0 of 10,321
transactions fail. No change to the trusted part. `lake build` passes with no
warnings and no `sorry`. Then, at Frans's word ("Use a hash."), C-H compares
an object's history by its contents too: the exporter writes a hash of its
entries on the HOBJ line (FNV-1a with 64 bits over the entries as on H lines;
`historyHash` in Check/Trace.lean, the same in TraceExport), and C-H compares
it with the hash of the node's history in P (a canonical object) or of the
version at its position (a snapshot); a HOBJ line without a hash is checked
by the number of entries only. On the evict set (3 seeds) every object's
history is compared.

2026-10-27. Rule 4 by position (bergdb 005-58), Java's since bergdb 005-57
(`e773562`). Changes to the trusted part: new definitions in SIS/Handle.lean,
`inPosToId` (Java's `posToId` as a test), `HMem.byPos`, `HMem.linkDPos`,
`handleStartupPos` and `runHandlesPos`; new statements in
SIS/HandleTheorems.lean, `Rule4_positions`, `Rule4Pos_handles` and
`RunPos_handles`. No definition changed. All three are proved
(`rule4_positions`, `rule4Pos_handles`, `runPos_handles`;
SIS/Proof/HandleLinkPos.lean). The proof rests on two more facts of E5's rerun
invariant (`RInv.near`, `RInv.keys`, SIS/Proof/EvictRerun.lean): a stream slot's
reference comes from a version of the section, with Rule R or as it is (the
record rule), or from the latest version of a node that has no version in the
section and is current and clean when the rerun's walk loads it (in the
section, so its references name the latest versions then), or is a copy of
one of those; so no version of its pointee lies between it and the section.
The memory before rule 4 is the model's startup's, which applies Rule R by node
id to the slots of the objects it makes from versions (`canonOfVersion`), where
Java can apply it only where `posToId` gives the node: on the example runs
(SIS/HandleExample.lean, `rule4Counts`) every pointer that rule 4 links is at
its node's canonical object's position, and none needs `posToId` or the header
read that Java does for a top node's pointer (bergdb 005-58, Outcome).
`lake build` passes with no warnings and no `sorry`; `#print axioms` shows only
Lean's standard axioms.

2026-10-27. T9 over handles (bergdb 005-62). Changes to the trusted part: a new
file, SIS/HandleReclaimTheorems.lean, with the run with handles that restarts
from cut streams (`runHandlesCut`) and two statements as definitions,
`T9_handles` and `T12_handles` (T9 and T12 with eviction over `runHandles` and
`runHandlesCut`, with the assumptions of `T9_readCut` and `T12_evictCut`). No
definition changed. `T9_handles` is proved (`t9_handles`;
SIS/Proof/HandleCut.lean, HandleCutTrans.lean, HandleCutRun.lean), with T9's
invariant over handles (`CInvH`), which needs less than CInv: a node has one
object in memory and every node of D its canonical object, which every follow
of a pointer to it reaches without a load. `heinv_hinvH_startup`
(SIS/Proof/HandleRestart.lean) now also gives the startup's pointer facts that
`CInvH` needs. `T12_handles` is proved too (`t12_handles`); its part 1
(SIS/Proof/HandleCutLater.lean): after a restart from a stream on which a cut
is safe, reads from the first available time on and the writer's walk give the
same on the cut streams (`CInvH.read_later`, `HEInv.reachPath_later`), with T9's
invariant; and its part 2 (SIS/Proof/HandleCutStart.lean): the startup with
handles from a stream cut safely is the one from the whole stream but for the
root's object (`handleStartup_sim`); `startup_sim` (SIS/Proof/CutLaterStart.lean)
now comes from `sectionPos_sim`, its part before rule 4; part 3 to 5
(SIS/Proof/HandleCutSim.lean, HandleCutTransSim.lean, HandleCutT12.lean):
C's transactions, cache operations and restarts against E's, on memories that
differ only in the root's object, as SIS/Proof/CutLaterRun.lean does for the
run with eviction (whose `lastR` and `logOf` now take any cache operations).
By running, reclaim with handles passes (SIS/HandleReclaimExample.lean,
`reclaimtest`). `lake build` passes with no warnings and no `sorry`;
`#print axioms SIS.t9_handles` and `SIS.t12_handles` show only Lean's
standard axioms.

2026-10-28. The design before handles removed (bergdb 005-62, question 3,
steps a to c, Frans: "as proposed, all steps"). Step a: the seven theorems
over SIS/Evict.lean that have a counterpart over handles (`TC_records`,
`TR_view`, `T2_cache`, `TR_view_restarts` and `TP_pins` of
SIS/PhysTheorems.lean, `T9_readCut` and `T12_evictCut` of
SIS/ReclaimTheorems.lean), Reclaim.lean's `runEvictCut`, the eight proof files
that only they used, and the declarations of the other proof files of the
design that nothing kept used; SIS/EvictExample.lean's runs with eviction (its
checks of TREE, A6' and A-COPY and example 5 moved to SIS/PhysExample.lean;
ReclaimExample.lean's three witnesses run with handles and hold as before;
`phystest` has no `evict` part any more). Step c: the startup with handles is
proved from the lazy startup's memory directly (SIS/Proof/HandleStart.lean:
`StartMem`, `startMem_st`, `StartMem.heinv`, `heinv_startup`, and
`StartMem.hinvH` in HandleRestart.lean), no longer through Evict.lean's Level 4
startup and its invariants (`evictStartup`, `Mem.linkD`, `EInv`, `HInv`); then
SIS/Evict.lean went, its assumptions of stage 2 (`EvictRunOK` and its parts)
and `Mem.sectionPos` moved word for word to SIS/Phys.lean. Step b: what the
proofs over handles still used of the proof files of the design moved to
SIS/Proof/LogicFacts.lean, PhysStart.lean (`RInv`, `rinv_lazyStartup`),
EvLogic.lean (EvictLogic.lean renamed), CutLazySim.lean and CutLazyStart.lean
(`sectionPos_sim`), and into HandleCut, HandleCutTrans, HandleCutLater and
HandleCutT12. No other definition or statement of the trusted part changed;
comments of Handle.lean, HandleTheorems.lean and HandleReclaimTheorems.lean no
longer compare with Evict.lean but as history. And rule 4 by position after a
cut (question 2, Frans: "Prove it!"): `HMem.linkDPosFrom`, `handleStartupPosFrom`
and `runHandlesCutPos`, Java's rule with its skip below the stream's first
position; `Rule4PosCut_handles` and `RunPosCut_handles` proved
(`rule4PosCut_handles`, `runPosCut_handles`, SIS/Proof/HandleCutSkip.lean and
HandleCutPos.lean), with no new assumption. lean/ from 144 files and 66,452
lines to 119 and 51,539. `lake build` passes with no warnings and no `sorry`;
`#print axioms` of every theorem of the lists above shows only Lean's standard
axioms; `lake exe reclaimtest 20 30` passes, with 1,920 skipped pointers at 744
restarts, none to a node with a canonical object; `phystest 20 40` and
`sistest 20 40` pass; the trace tests pass.

2026-10-28. T3 for BergDB's take (bergdb 007-08, step 4 of 007-03), the take
of `TransSeq.take` as 007-07 left it, with D4:B. Changes to the trusted part:
new definitions in SIS/Bound.lean, `Stream.span`, `Pace`, `takeLoop`,
`takePolicy`, `share`, `dither`, `javaPace` and `javaTake`, and the import of
SIS/Startup.lean (for `sectionIdx`); new statements in SIS/BoundTheorems.lean,
`T3_take_step`, `T3_take`, `T3_take_restarts`, `T3_take_decrease`,
`T3_take_decrease_restarts`, `T3_take_rerun` and `T3_take_reads`; the
comments of `sdTarget` and `KeepsUp` no longer describe the take before
007-07; no definition changed. The theorems hold for every pace and every cost of a record, with
nothing else assumed; `KeepsUp` with twice the setting does not hold for the
take (on a stream whose span is longer, its deadline is at the span), so they
are proved by induction over the run from the bound for one transaction,
which follows from the take keeping up with its own deadline's distance
(`takePolicy_keepsUp`; SIS/Proof/BoundTake.lean). By running
(SIS/BoundExample.lean): Java's dither and share bit for bit; `javaTake`
against Java's `TransSeq.take` on 300 generated cases, the same in all;
runs of example 2 with constant and decreasing settings, with and without
restarts. `lake build` passes with no warnings and no `sorry`; `#print
axioms` of the seven theorems shows only Lean's standard axioms; the trace
tests pass.
After 007-08's review (2026-10-28, its section "Review"), comments only:
`T3_take_decrease`'s comment no longer says that the section never costs
more than after T(m), which holds only if that is twice the new setting or
more; `share`, `dither` and `javaPace` are marked as used by no theorem, kept
in the trusted part to check the model against Java's arithmetic (Frans).

Stage 1 of bergdb item 001 is done (2026-10-16): lemma M (`LM_newer`, L2),
T1-L (`T1_lazy`, L3), CC and T2-L (`CC_canonical`, `T2_lazy`, L4) are proved,
and Java's first touches after restarts are checked against the model's rule
(C-L, L5). Stage 2 (2026-10-17, over the design before handles; since
005-62 over handles, 009): T-CACHE, T-READ, T2-C and T-PIN (`tc_handles`,
`tr_handles`, `t2_handles`, `tr_handles_restarts`, `tp_handles`), and rule 4
by position (005-58). Stage 3 (2026-10-17): the definitions and T13' (R3),
the checker on Java's reclaim traces with the red list (R7), T8 (R4),
`CutOK`'s part 2 over `ReadsPhys` (R6, part 1: register M48, option (a),
Frans), T12 for runs without eviction (R5); over handles T9 and T12 with
eviction (`t9_handles`, `t12_handles`), and rule 4 by position after a cut
(005-62).

Not done:

* A check of the physical layer's assumptions (`PhysStep`, M47) on Java
  traces; they are argued (011-11, 13.3).
* The bounds: T4 (D) (bergdb item 007). T3 for BergDB's take is proved
  without its record limit (bergdb 007-08). The stream's meta blocks are
  not modelled either, but they make no difference to the take: when it
  runs, the stream's length is where the new record begins (bergdb 005-68).
* Reclaim's theorems: T-SCHEME (R6), that Java's scheme gives safe cuts:
  checked, not proved (the plan's fallback; 001-07, section 5):
  by running on example 4 (`reclaimtest`, `checkSchemeB`), and at every cut
  of Java's reclaim traces (C-CUT).
