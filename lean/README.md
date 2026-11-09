Self-indexed streams in Lean
============================

The model of [../docs/sis-model.md](../docs/sis-model.md) in Lean 4:
the definitions, the assumptions, and the theorems T1 (recovery) and T2
(restart invariance), and those below, with their proofs. See Status.

Since bergdb item 001 (2026-10-16 to 18) the model also has the physical
layer (lazy reading, stage 1), eviction (stage 2) and reclaim (stage 3),
with their theorems (Status; 001-08, section 5;
001-07, sections 2 and 5). They are proofs of the
abstract model, not of Java, concurrency, serialization, torn bytes or
resource bounds; Java's runs are checked against the model by the trace
checker (`Check/`, `TraceCheck.lean`). Reviewed 2026-10-13 at the `ebe5f77`
documentation cutoff, before item 001: the abstract model with the exact
still-dirty test.
What an implementation must meet is in sis-model.md, section 11; how Java
is checked against the model, in [levels.md](../docs/levels.md).

Since bergdb item 007 (2026-10-23) the model also has the first bound, T3:
with any cost of a record and a startup pos policy that keeps up with a
startup distance, the startup section is bounded (SIS/Bound.lean,
SIS/BoundTheorems.lean; ../items/007-bounds/01-startup-bound.md).

Since bergdb 007-08 (2026-10-28) T3 also holds for BergDB's own take,
`TransSeq.take` as step 3 of 007-03 and D4:B left it (`takePolicy`, with
any pace, and with BergDB's share `javaTake`, SIS/Bound.lean): after a
transaction the startup section without its last record costs less than
the larger of twice the startup distance's setting and what it cost before
(`T3_take_step`), so less than twice the setting with a constant one, also
with restarts (`T3_take`, `T3_take_restarts`), and after a decrease of the
setting it shrinks with every transaction until it is below twice the new
one, and then stays below it (`T3_take_decrease`); SIS/Proof/BoundTake.lean.
`javaTake` gives the startup pos of Java's `TransSeq.take` on 300 generated
cases (SIS/BoundExample.lean). Its share and dither are the double rule of
2026-10-28; since bergdb 005-79 (2026-11-03) Java's take computes them in
integers, in units of 2^-16 (`TransSeq.shareFp`, `ditherFp`). On the 300
cases the integer take gives the same startup pos, `BoundExample.lean`'s;
over 3 * 10^6 of TakeCheck's cases it differs from the double rule in 13,
each taking one transaction more (the review of 005-79's Part B). The bit
guards of `dither` and `share` have no Java counterpart since then, as
`TransSeq.dither` is gone.

Since bergdb item 009 (2026-10-25) the model also has handles: SIS/Handle.lean
models 009's design of the physical layer (one handle per node, pointers that
hold handles, eviction without walks;
009-02, phase 2), aligned with Java's handles (009, on main since
2026-10-26), and SIS/HandleTheorems.lean
states T-CACHE, T2-C, T-READ and T-PIN over it, all proved. T-CACHE
(`tc_handles`, `TC_handles_records`, SIS/Proof/HandleRecords.lean; step 2d):
with any reads and evictions between transactions, the physical writer with
handles writes the model's records and leaves the model's D. T-READ
(`tr_handles`, SIS/Proof/HandleReadT.lean): a read through the handles at any
time up to the last record gives P at that time. T2-C and T-READ with
restarts (`t2_handles`, `tr_handles_restarts`, SIS/Proof/HandleRestart.lean),
and T-PIN (`tp_handles`, SIS/Proof/HandlePin.lean): every live handle whose
object is not pinned may be evicted (phase 4a, 2026-10-26).
SIS/HandleExample.lean checks them by running. Its runs found two points
where the plan's design needs more than it says, and Java does both: the
slow path writes the pointer's reference, raised to the written position of the dead handle it holds, back
into the pointer, and compares the live handle's object with that raised
reference (SIS/Handle.lean's header, choices 1 and 7). Java's handle state
is checked against the invariants of SIS/HandleTheorems.lean by the trace
checker's C-H (step 4c, 2026-10-26).

Since bergdb 005-58 (2026-10-27) the model also has Java's rule 4 by position
(bergdb 005-57): `HMem.linkDPos` finds the node that a pointer of D names from
the startup section's `posToId` and the canonical objects' positions, without
reading the stream; `handleStartupPos` and `runHandlesPos` are the startup and
the run with it. Proved: a pointer that rule 4 links names a version of the
section, the version before its node's first version there, or its node's
canonical object's (`rule4_positions`), so rule 4 by position links what rule 4
by node id links (`rule4Pos_handles`), and the runs are the same
(`runPos_handles`); SIS/Proof/HandleLinkPos.lean.

Since bergdb 005-62 (2026-10-27) Level 3's reclaim theorems with eviction are
stated over handles too (SIS/HandleReclaimTheorems.lean), so that the design
before handles could be removed: T9 over handles (`T9_handles`) is proved
(`t9_handles`, SIS/Proof/HandleCutRun.lean): in a run with handles, after a
safe cut, a read through the handles at a time from the first available time
on gives the same on the cut stream as on the whole stream, and gives P. T12
with eviction over handles (`T12_handles`, over the run with handles that
restarts from cut streams, `runHandlesCut`) is proved too (`t12_handles`,
SIS/Proof/HandleCutT12.lean): that run appends the records of the run without
restarts, cut at the largest cut, with its D and lookups from the first
available time on.

Since bergdb 005-62 (2026-10-28) eviction is modeled with handles only: the
model of eviction before handles (SIS/Evict.lean, with memory slots, stream
slots, unswizzle and release) is gone, with its proofs and the theorems stated
over it (`TC_records`, `TR_view`, `T2_cache`, `TR_view_restarts` and `TP_pins`
of SIS/PhysTheorems.lean, `T9_readCut` and `T12_evictCut` of
SIS/ReclaimTheorems.lean), each of which has its counterpart over handles. The
assumptions of stage 2 (`EvictRunOK`) are now in SIS/Phys.lean, and the startup
with handles is proved from the lazy startup's memory directly
(SIS/Proof/HandleStart.lean).

Since bergdb 005-62's question 2 (2026-10-28) the model also has Java's rule 4
by position after a cut: `HMem.linkDPosFrom` is `HMem.linkDPos` with Java's skip
of a stream pointer of a node of D below the stream's first position;
`handleStartupPosFrom` and `runHandlesCutPos` are the startup and the run with
cuts with it. Proved: after a safe cut, for every first position up to the cut,
it links what rule 4 by node id links (`rule4PosCut_handles`): the pointers it
skips name no node with a canonical object; so the run with cuts and rule 4 by
position is `runHandlesCut` (`runPosCut_handles`), and T12 over handles holds
for it; SIS/Proof/HandleCutSkip.lean, SIS/Proof/HandleCutPos.lean.

Since bergdb 020-29 (2026-11-09) a second library, `BergDB`, has the user
indexes of release 2026.4 (020-10 with 020-18's fixes), the protocol that
020-26 checked with TLC within small bounds, for any number of index names
and directories: the writers (transactions of any keys, each key's index set
read under the lock), the builds, the activation, the deletion and the
cleanup of each name's generations, crashes and restarts
(BergDB/Index/Model.lean, the trusted part), and 020-26's safety invariants
proved for every size (BergDB/Index/Theorems.lean): at every lookup time an
active index's entries are exactly f over the data (`index_is_function`), no
entry of a live generation is stale, a build covers the keys it passed, every
generation with entries is live or has a marker, no marker names a live
generation, a creation's G is new. It imports nothing of SIS. The proofs:
BergDB/Index/Inv.lean, BergDB/Index/Steps.lean; while a build step holds the
manager's lock, only writers that could commit when it took the lock can
refuse it, each once (BergDB/Index/Locked.lean); runs of the model:
BergDB/Index/Example.lean. Liveness over runs with weak and strong fairness
(BergDB/Index/Liveness.lean): a cleanup ends (`cleanup_ends`, weak fairness
of its thread, finitely many crashes), so no generation that is not live
keeps entries for ever (`no_orphans`, BergDB/Index/Orphans.lean), and a
build ends, its definition active or deleted (`build_ends`, strong fairness
of the build's thread, the manager's lock free again and again, finitely
many crashes and retries); the lock is free again and again under weak
fairness of its holders (`lock_released`, `build_ends_wf`,
BergDB/Index/Release.lean); a run in which weak fairness does not give
BuildEnds, with two names and definition changes without end
(`weak_fairness_not_enough`, BergDB/Index/Starve.lean), and with finitely
many definition changes it does (`build_ends_finite`,
BergDB/Index/Finite.lean).


Build and run
=============

Needs elan (`brew install elan-init`). The toolchain version is in
`lean-toolchain`; elan downloads it on first use. No Mathlib.

    cd lean
    lake build              # checks every file but the test programs, runs the #guard tests
    lake build BergDB       # the user indexes' library alone (020-29)
    lake exe sistest 20 40  # random runs: 20 seeds, 40 transactions each (7 min)
    lake exe phystest 20 40 # the physical layer on random runs (7 min)
    lake exe reclaimtest 20 30     # reclaim: random runs with cuts (1 min)

The level scripts run `lake build` and `tracecheck`; the three test programs
run unattended in `java/stress/lean-tests.sh`, a step of `java/night.sh`,
with 5 seeds for sistest and phystest (about 4.5 minutes in all;
`lean-tests.sh full` runs the sizes above). Each program exits with status
1 and prints "N failures" when a check fails, and the step fails then.

`lake build` checks every proof. To see that a theorem depends on nothing but
Lean's standard axioms (no `sorry`), put this in a file, for example
`Axioms.lean`, and run `lake env lean Axioms.lean`:

    import SIS.Theorems
    import SIS.PhysTheorems
    import SIS.ReclaimTheorems
    import SIS.BoundTheorems
    #print axioms SIS.T1_recovery
    #print axioms SIS.T1_crash
    #print axioms SIS.T1_nodes
    #print axioms SIS.T2_restart
    #print axioms SIS.T13_markExact
    #print axioms SIS.LM_newer
    #print axioms SIS.LM_ruleR
    #print axioms SIS.LM_cutTo
    #print axioms SIS.T1_lazy
    #print axioms SIS.CC_canonical
    #print axioms SIS.T2_lazy
    #print axioms SIS.T15_closed
    #print axioms SIS.T13_markTouch
    #print axioms SIS.T8_recoverCut
    #print axioms SIS.T12_restartCut
    #print axioms SIS.T3_section
    #print axioms SIS.T3_restarts
    #print axioms SIS.T3_reads
    #print axioms SIS.T3_rerun
    #print axioms SIS.T3_bounded
    #print axioms SIS.T3_take_step
    #print axioms SIS.T3_take
    #print axioms SIS.T3_take_restarts
    #print axioms SIS.T3_take_decrease
    #print axioms SIS.T3_take_decrease_restarts
    #print axioms SIS.T3_take_rerun
    #print axioms SIS.T3_take_reads

Each prints `[propext, Classical.choice, Quot.sound]`, or a part of it
(`LM_cutTo`, `T3_section` and `T3_restarts` need no `Classical.choice`).
SIS/HandleTheorems.lean and SIS/HandleReclaimTheorems.lean state the
theorems over handles as definitions;
their proofs are checked the same way, each printing
`[propext, Classical.choice, Quot.sound]`:

    import SIS.Proof.HandlePin
    import SIS.Proof.HandleLinkPos
    import SIS.Proof.HandleCutRun
    import SIS.Proof.HandleCutT12
    import SIS.Proof.HandleCutPos
    #print axioms SIS.tc_handles
    #print axioms SIS.tr_handles
    #print axioms SIS.t2_handles
    #print axioms SIS.tr_handles_restarts
    #print axioms SIS.tp_handles
    #print axioms SIS.rule4_positions
    #print axioms SIS.rule4Pos_handles
    #print axioms SIS.runPos_handles
    #print axioms SIS.t9_handles
    #print axioms SIS.t12_handles
    #print axioms SIS.rule4PosCut_handles
    #print axioms SIS.runPosCut_handles

The equalities of the checker's fast paths (Check/Fast.lean,
Check/R4.lean) are checked the same way:

    import Check.Steps
    #print axioms SIS.Fast.markOf_eq_fast
    #print axioms SIS.Fast.writeAll_eq_fast
    #print axioms SIS.Fast.reachList_eq_fast
    #print axioms SIS.Fast.step_eq_fast
    #print axioms SIS.TopBridge.r4Fast_sound

The user indexes' theorems (BergDB/Index/Theorems.lean, Liveness.lean,
Orphans.lean, Release.lean, Finite.lean and Starve.lean, 020-29) the same
way, each printing
`[propext, Classical.choice, Quot.sound]`:

    import BergDB
    #print axioms BergDB.Index.reach_inv
    #print axioms BergDB.Index.index_is_function
    #print axioms BergDB.Index.no_stale_entry
    #print axioms BergDB.Index.build_covers
    #print axioms BergDB.Index.gens_accounted
    #print axioms BergDB.Index.start_accepted
    #print axioms BergDB.Index.gen_fresh
    #print axioms BergDB.Index.locked_phase
    #print axioms BergDB.Index.cleanup_ends
    #print axioms BergDB.Index.build_ends
    #print axioms BergDB.Index.weak_fairness_not_enough
    #print axioms BergDB.Index.no_orphans
    #print axioms BergDB.Index.lock_released
    #print axioms BergDB.Index.build_ends_wf
    #print axioms BergDB.Index.build_ends_finite


What to read
============

The trusted part is the definitions and the theorem statements. If they say
what sis-model.md says, a proof that Lean accepts proves the theorems for
the model. Read in this order; each definition has a comment that points to
its section in sis-model.md.

* SIS/Basic.lean (sis-model.md, sections 2, 3). Entries, histories, x@t
  (`upTo`), nodes, P (`Struct`), changes (with the touch, `Changes.touch`),
  the structure's functions (`Spec`, with the virtual root's switch `virt`,
  `topLevel` and `rootVal`), root children (`isTop`), reachability, P@t
  (`view`), equivalence (`Equiv`).
* SIS/Stream.lean (sis-model.md, sections 4, 5). Versions, records (top(i)
  as a node and a record; fa(i), `Record.fa`), the stream, lv(x)
  (`Stream.lv`), references, `good`, `dirty`.
* SIS/Algorithm.lean (sis-model.md, section 6.1). DB = <P, D, S>, the
  policy, the still-dirty test and the choice of step 3 (`Algo`), the exact
  and BergDB's still-dirty tests (`exactTest`, `javaTest`), marking
  (`changed`, `marked`, `markOf`), what can be in D and written (`written`),
  top(i) (`topOf`, `topV`), the first available time (`Algo.faPolicy`,
  `lastFa`, `firstAvail`), step 3 with the touch (`touchOf`, `gotDirty3`),
  transaction i (`step`), R(0) (`init`), `run`.
* SIS/Startup.lean (sis-model.md, section 6.2). `newest` (R(s) to R(k)),
  Rule R (`follow`), reading the stream (`readFrom`), where reading starts
  (`topVersion`, `startVersion`; with a virtual root `readTops`, `topsRead`,
  `rootVersion`), P up to s (`baseStruct`), `rerun`, `startup`.
* SIS/Assumptions.lean (sis-model.md, section 3.4). Assumptions A2 to A5,
  the data node rules and the touch's (`SpecOK`, `StepOK`, `RunOK`), with a
  virtual root R1 to R4 (`VirtInit`, `VirtStep`, `topClosure`),
  `runRestarts`.
* SIS/Theorems.lean (sis-model.md, section 9). T1 (`T1_recovery`,
  `T1_crash`, `T1_nodes`), T2 (`T2_restart`), T13 (`T13_markExact`).
* SIS/Phys.lean (not in sis-model.md; 011-11, 13; 001-08, 4). The physical
  layer, what Java holds in memory (bergdb item 001, WPs L1 and L3): objects
  (`Obj`), their slots (`Slot`), the memory with the node table (`Mem`);
  Java's first touch (`Mem.follow`: Rule R, the table, the version read, cut
  back in the section); reads (`Mem.read`); the lazy startup
  (`lazyStartup`); a version cut back to a time (`Version.cutTo`); the
  operations after startup (`Op`, `Mem.step`, admissible: `OpsOK`); the
  assumptions of the physical layer (`PhysStep`, `PhysRunOK`); the writer
  after a lazy startup (WP L4: its view through the physical layer,
  `Mem.view`; its transaction, `lazyTrans`, with the record of `stepWith`,
  `step` with its change given) and a run with lazy restarts (`runLazy`);
  the writer's paths reach the touched nodes too (`pathOf`, WP R3); the
  positions of the startup section's canonical objects, as Java's startup
  sets them (`Mem.sectionPos`); the assumptions of stage 2, eviction (bergdb
  item 001, WP E2; 001-08, section 4: `EvictStep`, TREE, `treeAt`, and A6',
  `adoptAt`; A-COPY, `CopyStep`; `EvictRunOK`), in Evict.lean until bergdb
  005-62.
* SIS/Handle.lean (not in sis-model.md; 009-02, 4). The physical layer with
  handles (bergdb item 009, phase 2, 2a; aligned with Java's step 3a;
  009-02, section 4): objects by address (`HObj`), pointers with a reference
  and a handle (`HPtr`), handles (`Handle`: node, object, written position,
  dead), the table from node to live handle (`HMem`); following a pointer
  (`HMem.followR`: the fast path's test, else the reference after Rule R
  raised to the held handle's written position and written back,
  `HMem.setRef`, the live handle, `HMem.resolve`, and the load, `HMem.load`;
  `HMem.follow`, with the writer's `HMem.promote`); reads (`HMem.read`); the
  writer's walk and change (`HMem.reachOnPath`, `HMem.newPtr`,
  `HMem.applyChange`); the record rule (`HMem.ptrRef`, `HMem.refOf`) and the
  physical writer (`HMem.writeNode`, with `resolvePointers`; `handleTrans`);
  eviction (`HMem.evictable`, `HMem.evict`); startup with rule 4 by handles
  (`handleStartup`, `Mem.toH`, `HMem.linkD`); rule 4 by position, Java's
  since bergdb 005-57 (`inPosToId` for Java's `posToId`, `HMem.byPos`,
  `HMem.linkDPos`, `handleStartupPos`); after a cut, with Java's skip of the
  pointers below the stream's first position (`HMem.linkDPosFrom`,
  `handleStartupPosFrom`, bergdb 005-62); reads and evictions between
  transactions (`HCacheOp`) and runs (`runHandles`; with rule 4 by position,
  `runHandlesPos`). The file's header lists the choices where the plan is
  vague.
* SIS/HandleTheorems.lean (not in sis-model.md; 009-02, 5, phase 2). The
  statements over handles (bergdb item 009, 2c): the invariants (`HTableOK`,
  `HCanOK`, `HSnapOK`, `HSlotOK` for the record rule, `HRuleROK`,
  `HLiveWrittenOK` and `HFastOK` for the fast path's test, `HWrittenOK`);
  T-CACHE (`TC_handles`, proved: `tc_handles`), T2-C (`T2_handles`, with
  restarts), T-READ (`TR_handles`; with restarts, `TR_handles_restarts`),
  T-PIN (`TP_handles`); rule 4 by position (bergdb 005-58): the positions of
  the pointers that rule 4 links (`Rule4_positions`), rule 4 by position is
  rule 4 by node id (`Rule4Pos_handles`), and so are the runs
  (`RunPos_handles`); all proved in SIS/Proof/ (`tc_handles`, `t2_handles`,
  `tr_handles`, `tr_handles_restarts`, `tp_handles`, `rule4_positions`,
  `rule4Pos_handles`, `runPos_handles`).
* SIS/PhysTheorems.lean (sis-model.md, sections 5.1, 9). Lemma M: a newer
  version of a node serves every time an older one serves (`LM_newer`), so
  Rule R's version does (`LM_ruleR`), and a version cut back to s serves the
  times up to s (`LM_cutTo`); T1-L (`T1_lazy`): after the lazy startup from
  the stream of a run, or of a prefix of it (a crash), and any reads and
  writer follows, a read at any time up to the last record gives P at that
  time; CC (`CC_canonical`): in a run with lazy restarts, every canonical
  object holds its node's whole history; T2-L (`T2_lazy`): such a run
  appends the records of the run without restarts; `step_eq_stepWith`; stage
  2 (bergdb item 001, WP E3): D closed upward (`T15_closed`). Stage 2's
  T-CACHE, T-READ, T2-C and T-PIN are stated over handles
  (SIS/HandleTheorems.lean); over Evict.lean they were here until bergdb
  005-62.
* SIS/Reclaim.lean (not in sis-model.md; 001-07, 5). Level 3, reclaim
  (bergdb item 001, WP R3): what a cut leaves of a version (`Version.stub`)
  and of a record (`Record.cut`); the stream after a cut (`cutStream`); the
  versions that a lookup at a time may read (`ReadsAt`, WP R7); when a cut
  is safe (`CutOK`); the same lookups from f on (`SameFrom`); policies that
  a cut does not change (`PolicyCutOK`); a virtual root seen only through
  its live children (`ExecRootOK`), whose live children are those of its
  last entry (`VirtLiveOK`, WP R4); runs that restart from cut streams
  (`runRestartsCut`, `cutMax`).
* SIS/ReclaimTheorems.lean (not in sis-model.md; 001-07, 2.2, 2.10). T13'
  (`T13_markTouch`, WP R3): with touches, step 3 gives exactly the index
  nodes not in D (and not a virtual root) that are dirty or touched; T8
  (`T8_recoverCut`, WP R4): after a safe cut, startup from the cut stream
  gives the same lookups at every time from the first available time on
  (`SameFrom`), and the same D; T12 (`T12_restartCut`, WP R5): a run that
  restarts from safe cut streams appends the records of the run without
  restarts (its stream is that run's, cut at the largest cut), with that
  run's D and lookups from the first available time on. T9 and T12 with
  eviction are stated over handles (SIS/HandleReclaimTheorems.lean); over
  Evict.lean they were here until bergdb 005-62.
* SIS/HandleReclaimTheorems.lean (not in sis-model.md; 001-07, 2.9, 2.10;
  005-62). Level 3's reclaim theorems with eviction over handles (bergdb
  005-62), as definitions of type `Prop`: the run with handles that restarts
  from cut streams (`runHandlesCut`); T9 with handles (`T9_handles`): in a
  run with handles as in `T2_handles`, after a safe cut, a read through the
  handles at any time from the first available time on gives the same on the
  cut stream as on the whole stream (memory and nodes), and gives P; proved
  (`t9_handles`, SIS/Proof/HandleCutRun.lean); T12 with eviction over
  handles (`T12_handles`): the run with handles that restarts from safe cut
  streams appends the records of the run without restarts, cut at the
  largest cut, with that run's D and lookups from the first available time
  on; proved (`t12_handles`, SIS/Proof/HandleCutT12.lean); rule 4 by
  position after a cut (question 2): the run with cuts and Java's rule 4 by
  position (`runHandlesCutPos`), the startup from a stream cut safely with
  it is `handleStartup` (`Rule4PosCut_handles`), and so is the run
  (`RunPosCut_handles`); proved (`rule4PosCut_handles`, `runPosCut_handles`,
  SIS/Proof/HandleCutPos.lean).
* SIS/Bound.lean (sis-model.md, section 10; 007-01, 3; 007-08, 1). Bounds,
  part 1 (bergdb item 007): the cost of the records R(a), ..., R(b-1) for
  any cost of a record (`Stream.cost`); the startup pos that a startup
  distance d asks for (`sdTarget`); a policy that keeps up with d
  (`KeepsUp`); the startup distance policy (`sdPolicy`). BergDB's take
  (bergdb 007-08; `TransSeq.take` since 007-07): the startup section without
  its last record, which is the span of its transactions (`Stream.span`); a
  pace, any rule that decides whether to take the next transaction (`Pace`);
  the take's loop (`takeLoop`) and the take, whole transactions oldest
  first, each taken if it begins max(2 sd, span) or more before the end of
  the stream or if the pace takes it, with the setting sd any function of
  the transaction (`takePolicy`); BergDB's pace, its share and its dither in
  the double arithmetic of Java's take from 2026-10-28 until 005-79
  (`share`, `dither`, `javaPace`), and the take with it (`javaTake`); no
  theorem uses these four, kept to check the model against that arithmetic
  (the `#guard`s, TakeCheck); Java's take is in integers since 005-79
  (015-03).
* SIS/BoundTheorems.lean (sis-model.md, section 10; 007-01, 3; 007-08, 2).
  T3 (`T3_section`): in every run whose policy keeps up with d, the startup
  section without its last record costs less than d; also with restarts
  (`T3_restarts`); what startup reads (`T3_reads`) and reruns (`T3_rerun`),
  and with records of bounded cost (`T3_bounded`). No assumption but the
  policy. T3 for BergDB's take (bergdb 007-08), for every pace: after a
  transaction on any database, the section costs less than max(2 sd, the
  section before) (`T3_take_step`); with settings at most M, less than 2 M,
  also with restarts (`T3_take`, `T3_take_restarts`); after a change of the
  setting to sd', less than 2 sd' or at least one less for each transaction
  since (`T3_take_decrease`, `T3_take_decrease_restarts`); what startup
  reruns and reads (`T3_take_rerun`, `T3_take_reads`). No assumption but the
  policy.

The proofs, in SIS/Proof/ (not needed for reading the statements):

* Basic, Reach. Histories, nodes, reachability as an inductive definition,
  growing structures.
* StreamLemmas, Write. Latest versions, `good` and `dirty`, stability
  (`good_mono`), writing versions.
* Run. The parts of a transaction, runs, and the invariant `Inv` (INV-1 to
  INV-4 and the facts about S and P).
* Init, Util, StepFacts, StepP, StepS, StepD, StepInv. The invariant holds
  after T(0) and after every transaction (`inv_st`).
* Mark. Marking the access path of the change finds exactly the dirty index
  nodes not in D (`step_marked_iff`, T13).
* StepFacts, Fresh, VStep, EvLogic (the touch). WP R3: what step 3 gives
  with touches (`mem_touchOf`, `step_gd3_mem`, `step_gd3_of_touch`); the
  nodes reachable before the change with a touched node below them are
  touched, so a clean node's live children stay out of D (`step_cleanFresh`)
  and D stays closed upward (`step_touch_D1`, with A6' also before the
  change); a root child that a root child points to is not reachable
  (`VInv.deadTops`), so it is never touched.
* Still. What the proofs need of the still-dirty test (`StillOK`), for the
  exact test and BergDB's (`java_stillOK`).
* VStep. With a virtual root, the transaction keeps `VInv` (`step_vinv`):
  the root children, the root's history, R4, and that the latest version of
  a root child names the latest versions of the root children it points to
  (`step_fresh`, which needs BergDB's still-dirty test).
* RunFacts. How the states of a run relate.
* Recon. L-OUT (`Inv.lout`) and L-SEC (`Inv.recon`), reading with Rule R.
* Read. Reading from a version that is good with Rule R (`Inv.read`).
* VRead. With a virtual root, startup reads every root child created up to
  s, at its latest version, and rebuilds the root (`Inv.readAt_spec_virt`).
* Base. Reading the stream (`Inv.readAt_spec`), P up to s (`Inv.base_get?`).
* Recovery. The rerun, and T1 in the strong form (`T1_strong`).
* Restart. Every part of a transaction depends on P only through its nodes,
  and T2 (`T2_strong`).
* Newer. Lemma M (`Inv.newer`): references name latest versions, so a newer
  version's references name versions at least as new; by induction on the
  level.
* Fresh. Two facts of every run: a clean reachable node's latest version
  names the latest versions of its live children, which are not in D
  (`CleanFresh`, with BergDB's still-dirty test); a data node has one
  version (`DataOnce`).
* PhysMem, PhysInv. The memory's operations; the invariant of the proof of
  T1-L at time K (`MemInv`): canonical objects (`CanonOK`: in the node
  table, the node's history up to K, slots good at every time the node is
  reachable and fresh at K), snapshots (`SnapOK`, `SnapSlots`), memory slots
  (`MemSlotOK`), the nodes that have canonical objects (D, the section, the
  entries after s).
* PhysFollow, PhysRead, PhysWriter. The first touch keeps the invariant
  (`follow_reader`); reads give P (`MemInv.read_ok`, also from a stream that
  agrees on the nodes without canonical objects, `StreamAgree`); the
  writer's follow makes the object canonical (`MemInv.follow_writer`).
* PhysLogic, PhysRun. What the run says of nodes without a canonical object
  (`KCtx`; `Cover.mg`: their latest version is good; `KCtx.fresh_ref`,
  `Cover.cf`: its references are fresh).
* PhysPath, PhysRerun, PhysApply, PhysStep. The rerun of one transaction:
  the writer's paths, reached highest level first (`MemInv.reachPath_ok`);
  the change applied keeps the invariant from K to K + 1
  (`MemInv.applyChange_ok`).
* PhysLazy, PhysBase. The rerun keeps the invariant (`rerun_fold_ok`); the
  memory before it meets it at s (`PCtx.base_ok`).
* PhysT1. The operations keep the invariant (`MemInv.ops_ok`); T1-L in the
  strong form (`T1_lazy_strong`).
* PhysFrozen. The frozen run (WP L4): the same transactions with the startup
  pos frozen after a restart at k1 (`frozenAlgo`); after k1 it takes no node
  and writes only new data nodes, so its states only grow (`frozen_grow`),
  and the invariant carries over (`MemInv.transfer`).
* PhysT2. A run with lazy restarts: after every transaction, ⟨P, D, S⟩ is
  the run's, and the memory meets the invariant for the frozen run from the
  last restart (`LazyInv`, `lazyInv_all`); CC and T2-L in the strong form
  (`T2_lazy_strong`).
* EvLogic. Stage 2 (WP E3): the logical facts that the design rests on
  (`EvLogic`): D is closed upward, and a current clean node has no pointee
  in D and names the latest versions of its pointees (`evLogic_st`); D
  closed upward alone needs no A6' (`DClosed`, `step_closed`; WP R5).
* LogicFacts. Logical facts and list lemmas that the proofs of the physical
  layer share (bergdb 005-62, from the proof files of the design before
  handles): D's got-dirty indices (`dOf`), Rule R's bounds
  (`Inv.ruleR_bound`, `Inv.ruleR_lv0`), the latest versions (`Inv.lv_whole`,
  `Inv.ref_versionAt`), a clean node's latest version good for every time it
  is reachable (`Inv.clean_good`), TREE's one current parent
  (`treeAt_unique`), the parts of a transaction from step 3 on (`D1Of`,
  `takenOf`, `stepOf`), which depend on P only through its nodes
  (`stepOf_congr`).
* PhysStart. The lazy startup from the stream after T(k) (WP E5): its rerun
  keeps `RInv` (every object canonical, every stream slot naming its
  pointee's latest version after Rule R and naming a version, a slot for
  each pointee; since bergdb 005-58 also: no version of a stream slot's
  pointee between it and the section, `RInv.near`, and every slot for a
  pointee, `RInv.keys`; `rinv_lazyStartup`); the node table has no repeated
  keys (`tblND_lazyStartup`), and no object two slots for the same pointee
  (`slotsND_lazyStartup`).
* HandleMem, HandleInv. Bergdb item 009, 2d, T-CACHE over handles: the
  memory's operations; the fast path's test with a pointer's own reference
  agrees with the slow path's (`hFastOK_of`); evicting a handle changes no
  pointer's record (`HMem.ptrRef_evict_of`); the invariant with handles
  (`HEInv`: the table and the handles, INV-CAN, INV-SNAP, INV-SLOT for the
  record rule, the live pointers of current canonical objects, the snapshots
  against Rule R, live handles without a written position, references that
  name versions), and an eviction keeps it (`HEInv.evict`).
* HandleFollow, HandleRead. The readers' follow keeps it
  (`HEInv.followR_ok`: the fast path; the slow path's write-back, live
  handle and load; and, for reads at earlier times, what the pointers give,
  `HMem.KeepPtrs`), so reads and any operations between transactions do
  (`HEInv.cacheOps`); a read at the last time gives P, the writer's view
  (`HEInv.view_ok`).
* HandleWalk, HandleApply, HandleApplyInv. The writer's promote and its walk
  (`HEInv.follow_writer`, `HEInv.reachPath_ok`); the change applied, with
  TREE and A-COPY (`HEInv.applyChange_ok`, `HAInv`).
* HandleWrite, HandleWrites, HandleStepInv. The writer's loop writes the
  model's versions (`writeNodesH_eq`), its two loops the model's record
  (`HAInv.loops_vs`); the memory after the record has the next state's
  invariant (`HAInv.final_ok`).
* HandleTrans, HandleInit, HandleStart, HandleRecords. One transaction
  (`HEInv.handleTrans_ok`); runs (`TC_runH`); stage 1's memory with handles
  (`Mem.toH`) and rule 4 with handles (`HMem.linkD`), by lookup; the startup
  with handles from the stream after T(k), R(0) included, has the invariant
  (bergdb 005-62: the lazy startup's memory with the positions of its
  section meets `StartMem`, `startMem_st`, by `RInv`; taken to handles and
  with rule 4 it has `HEInv` and the pointer facts of T9's invariant,
  `StartMem.heinv`, `heinv_startup`, `heinv_init`); T-CACHE over handles
  (`TC_handles_records`, `tc_handles`).
* HandleHist, HandleHistTrans, HandleReadT. Bergdb item 009, phase 4a,
  T-READ over handles: the invariant for reads at earlier times (`HInvH`:
  the pointer of a canonical object for a live child at a time t holds a
  canonical object, or its slow path's reference names a version good for t,
  or, by INV-SLOT's second half, a node of D), kept by reads
  (`HInvH.followR`), evictions (`HInvH.evict`: a pointer whose handle held
  the evicted canonical object then has its node's latest version, clean, as
  its slow path's reference), every transaction (`HInvH.handleTrans_ok`) and
  in every run (`HInvH.run`); a read at any time up to the last record gives
  P (`HEInv.readT_ok`, `tr_handles`).
* HandleRestart, HandlePin. The startup with handles from the stream after
  T(k) has both invariants (`heinv_hinvH_startup`; the invariant for reads
  at earlier times from `StartMem`, `StartMem.hinvH`); the physical writer
  with handles depends on P only through its nodes (`handleTrans_congr`);
  runs with restarts (`HandleInvR`, `handleInvR_all`); T2-C and T-READ with
  restarts over handles (`t2_handles`, `tr_handles_restarts`); a live handle
  whose object is not pinned may be evicted (`HEInv.evictable_of_unpinned`),
  T-PIN (`tp_handles`).
* HandleLinkPos. Bergdb 005-58, rule 4 by position: a pointer that holds no
  handle in the memory before rule 4 is a stream slot of the lazy startup's
  memory (`before_ptr`), so `RInv` says what it names (`before_ptr_facts`);
  a canonical object there is at its node's latest position
  (`before_canon`); the positions (`rule4_positions`); rule 4 by position is
  rule 4 by node id where each pointer it leaves is in `posToId` or at the
  canonical object's position (`HMem.linkDPos_eq_linkD`), which the
  startup's memories meet, with the first version of a node in the section
  (`first_version`), A4 and a data node's one version (`rule4Pos_handles`);
  runs (`runPos_handles`; `runHandlesPos` is `runHandles` but for its
  startups, `runHandlesPos_of_startup`).
* HandleCut. Bergdb 005-62, T9 over handles: the invariant on the pointers
  (`CInvH`: a canonical object of a clean written node has, for each pointee
  that its latest version names at r0, a pointer that holds a canonical
  object or whose slow path's reference is r0 or later, `HMem.PtrAtLeast`;
  with a virtual root, the root's object holds the canonical objects of the
  root children of D and names the others at their latest versions or
  later); a follow on a stream cut safely is the follow on the whole stream
  when the pointee has a canonical object or every version at or after the
  slow path's reference is one `ReadsPhys` covers (`HEInv.followR_cut`,
  `HPtrCutT`); the pointers of an object a read at t may reach are such
  (`HEInv.cutPtr`), so a read at a time from f on gives the same on the cut
  stream (`CInvH.read_cut`); reads and evictions keep `CInvH`
  (`CInvH.readAt`, `CInvH.evict`, `CInvH.cacheOps`).
* HandleCutTrans, HandleCutRun. One transaction keeps `CInvH`: the writer's
  promote and walk, the change (new pointers hold canonical objects or copy
  pointers at their pointees' latest versions), the root's pointers to the
  nodes on the paths and the new ones (`HEInv.rootPtrs_change`), the writes
  and the next state (`CInvH.next`, `CInvH.handleTrans_ok`); the startup
  with handles gives it (`cinvH_startup`, from the pointer facts that
  `heinv_hinvH_startup` now also gives); runs with restarts (`HandleInvC`,
  `handleInvC_all`), and T9 over handles (`readCutH`, `t9_handles`).
* HandleCutLater. Bergdb 005-62, part 1 of T12 over handles: in a state
  later than a restart from a stream on which a cut at c is safe (`Later`,
  `later_st`; and the versions that the loads may read then, `LaterOK`), a
  read through the handles at a time from the restart state's first
  available time on gives the same on the cut streams (the stream now, and
  the restart's for Rule R) as on the whole streams (`CInvH.read_later`),
  and so does the writer's walk (`HEInv.reachPath_later`): every load is of
  a version at least as new as one that `LaterOK` allows (`HPtrLaterT`,
  `HLaterSafeT`, `HEInv.laterPtr`); a snapshot taken from the live handle is
  newer than the version the pointer names, and names its live children at
  least as new (`Inv.ref_mono`, `ruleRRef_mono`). T9's invariant is all it
  needs of the memory.
* HandleCutStart. Bergdb 005-62, part 2 of T12 over handles: the memory with
  handles with another root object (`HMem.withRoot`), the two root objects
  (`RootRelH`: the same but for the history and the pointers of the root
  children that only times before the first available time need); `Mem.toH`
  and rule 4 with handles keep a memory with another root object
  (`Mem.toH_withRoot`, `HMem.linkD_withRoot`), so the startup with handles
  from a stream cut safely is the one from the whole stream but for the
  root's object (`handleStartup_sim`, from `sectionPos_sim`, the same for
  the lazy startup with the positions of its section,
  SIS/Proof/CutLazyStart.lean).
* HandleCutSim. Part 3 of T12 over handles: the steps of a transaction and
  the reads on the memory with another root object and the cut streams,
  against the same on E's memory and the whole streams, give the same
  results and memories that differ only in the root's object again, with the
  same history: the follow and the read from the root (`HEInv.followR_sim`,
  `CInvH.read_sim`, with `CInvH.readAt_sim` below the root), the writer's
  walk (`HEInv.reachPath_sim`), the change (`HMem.withRoot_applyChange`, the
  source search finding corresponding objects; the two root objects get the
  same new entries, `RootRelH.addRoot`), the writes
  (`HMem.withRoot_writeNodes`, with Rule R of the cut stream,
  `HMem.writeNodes_cutS0`) and an eviction (`HMem.withRoot_evict`).
* HandleCutTransSim, HandleCutT12. Part 4 and 5 of T12 over handles: one
  transaction of C (the run with handles that restarts from cut streams)
  against one of E (the run with handles that restarts from the whole
  streams at the same points, with the same cache operations): the same
  record as the logical step from C's state, and memories that differ only
  in the root's object (`handleTrans_sim`); C's cache operations
  (`ops_simH`); the two runs side by side (`RunSimH`, `runSimH_zero`,
  `runSimH_step`: a restart by `handleStartup_sim`), so C appends the
  records of the run that restarts from cut streams
  (`handleCut_restartsCut`), and T12 over handles (`t12_handles`) follows
  from `restartCut`.
* HandleCutSkip. Bergdb 005-62, question 2: the pointers that Java's rule 4
  skips after a cut name no node with a canonical object (`cutSkip_lazy`):
  the rerun's invariant against the safe cut (`CutInv`: every object is the
  root's or of a node whose latest version is at c or later; a live stream
  slot below c of a node reachable then names a node without a version in
  the section, `cut_ref_live`; a stream slot below c of a node of D names
  such a node, or one not reachable from then on without a canonical
  object), for the memory before the rerun (`cutInv_lazyBase`), the walk
  (`CutInv.reachOnPath`) and the change (`CutInv.applyChange`: a new pointer
  without a source, `stale_absurd`, with TREE, no resurrection `reach_back`,
  `clean_ref_lvAt` and `PhysStep`'s `liveNew`), and the rerun
  (`cutInv_lazyStartup`).
* HandleCutPos. Rule 4 by position with a first position is rule 4 by
  position where the skipped pointers name no node with a canonical object
  (`HMem.linkDPosFrom_eq_linkDPos`); `posToId` on a cut stream
  (`inPosToId_cut`); `rule4Pos_handles`'s condition (`rule4Pos_cond`)
  carried to the startup from a stream cut safely by `sectionPos_sim`
  (`handleStartupPosFrom_cut`; `rule4PosCut_zero` without the skip;
  `rule4PosCut_handles`); runs (`runHandlesCutPos_succ`,
  `runPosCut_handles`, the restarts' streams by T12's `RunSimH`).
* CutStream, CutRead. Stage 3 (WP R4): the stream after a cut (its records,
  `versionAt`, `newest`, the last record); a pointer followed, or a read
  from a version, on a stream cut at or before the startup pos gives what it
  gives on the whole stream if it reads no record before the cut
  (`follow_cut`, `readFrom_cut`); a read from a version that a lookup may
  read reaches only such versions (`readFrom_readsAt`); a version a lookup
  may read, a physical read may follow (`ReadsAt.phys`, WP R6).
* CutAgree, CutRerun. Structures that agree for lookups from f on
  (`CutAgree`); a transaction's change is the same on both (`exec_cutAgree`,
  with `ExecRootOK`), and so is the rerun of the startup section
  (`rerun_cutAgree`, with `VirtLiveOK`), which keeps every node it starts
  with the run's (`rerun_cutAgree_nodes`, WP R5).
* CutBase, CutTops, CutStart. Startup's reads of a stream cut safely at the
  times from f to s: without a virtual root, the whole stream's
  (`Inv.readAt_cut_nv`); with one, the whole stream's but for the root's
  version, which startup rebuilds from the root children it can read: the
  root children live from f on are read at their latest versions
  (`Inv.topsRead_cut_all`), so the rebuilt root has the root's live children
  from f on (`Inv.cutRoot_live`, `Inv.readAt_cut_v`).
* CutRecover. P up to s, read from the cut stream, agrees with P after T(s)
  for lookups from f to s (`base_cutAgree`); T8 (`recoverCut`).
* CutRestart. WP R5: a cut of a cut (`cutStream_cutStream`); a state related
  to the run's (`CutRel`: the run's stream cut at m, its D, its nodes for
  the lookups from f on and for D), on which a transaction appends the run's
  record and keeps the relation (`step_congr_cut`).
* CutHist. WP R5: the nodes of D that no lookup from f on may reach (M33,
  M34): every node of D was reachable at a time at which its ancestors (it
  included) are in D, each with an entry from just after that time or a
  version in the record of its entry, put back by Rule A (`DAnchor`,
  `dAnchor_st`: Rule A with BergDB's test along the path,
  `step_anc_persist`, and D closed upward, `dClosed_st`); with a virtual
  root, every root child created after a root child of D is in D (`TopsD`,
  `topsD_st`).
* CutHistRead. WP R5: after a safe cut, startup reads such a node at that
  time through its ancestors' versions in the startup section (Rule R), at
  its newest version, from the cut stream as from the whole stream
  (`Inv.baseCut_get?_hist`; with a virtual root, the root children from its
  root child then on are read, `Inv.topsRead_cut_from`); T8 with D's nodes
  (`recoverCut_dNodes`).
* CutRuns. WP R5: the relation after every prefix of a run with restarts
  from cut streams (`restartCut_rel`), and T12 (`restartCut`).
* CutLazySim, CutLazyStart. WP R5, for T12 over handles: stage 1's memory
  with another object for the root (`Mem.withRoot`); two root objects that
  agree from f on (`RootRel`: the same live children from f on, and the same
  slots for the pointees of the cut run's root); the lazy startup with the
  positions of its section from a stream cut safely is the one from the
  whole stream but for the root's object (`sectionPos_sim`): the rebuilt
  virtual root (`rootObj_rel`), the rerun's transactions (`rerunStep_sim`),
  with the writer's last resort for a root child that only the whole
  stream's root still points to: every slot for it is the same stream slot
  (`anySlot_sim`); a transaction's change on views whose roots differ only
  there (`exec_rootSwap`), and the writer's paths on structures that agree
  (`CutAgree.pathOf_eq`).
* Bound. The cost of a part of the stream (`cost_split`, `cost_append_left`,
  `cost_ge_count`), the target's maximality (`sdTarget_max`), T3 after one
  transaction (`section_step`), for runs (`section_run`) and runs with
  restarts (`section_runRestarts`), and what startup reads and reruns
  (`reads_of_section`, `rerun_of_section`, `bounded_of_section`); bergdb
  item 007.
* BoundTake. T3 for BergDB's take (bergdb 007-08): the target of a distance
  (`sdTarget_spec`); the take's loop never goes back and takes every
  transaction up to the target, whatever the pace (`takeLoop_ge`,
  `takeLoop_reaches`), so the take keeps up with its deadline's distance
  (`takePolicy_keepsUp`); one transaction of a policy that keeps up with a
  distance in it (`section_step_of`, `take_step`); folds of steps, each
  followed by a restart or not (`fold_length`, `fold_bound`,
  `fold_decrease`).

Not trusted, tests only:

* SIS/Example.lean. The example of section 7, checked with `#guard`; a
  second structure with four levels, data nodes and time splits; and a third
  with a virtual root, as in BergDB: top nodes with a dead pointer to the
  previous one, and root splits that make a new top node. Also a check by
  running that a run meets the assumptions (`runOKB`, with `virtStepB` for
  R1 to R4).
* Test.lean. Runs the second structure on pseudo-random transactions and
  checks the assumptions, T1 in every state, and T2 with random restarts,
  for 16 algorithms (4 policies, the exact and BergDB's still-dirty test,
  step 3 by testing or by marking), and that marking gives the same records
  as testing; then the third structure for 8 algorithms (4 policies, step 3
  by testing or by marking, BergDB's test); and it reports how often the
  exact test fails T1 with the virtual root, which the theorems do not
  cover.
* SIS/PhysExample.lean and PhysTest.lean (bergdb item 001, WP L1): the
  physical layer by running. `#guard` checks: in every state of runs of
  examples 2 and 3, the lazy startup's reads give P at every time, and every
  canonical object holds its node's whole history, also with the writer's
  walks between reads; first touches with Rule R, a newer snapshot in the
  table, the writer's promotion, `canonicalNode`; the assumptions of the
  physical layer (`physRunOKB`, WP L3) on runs of examples 2 and 3. `lake exe
  phystest`: the same on random runs, with random reads and writer walks in
  random order, and startups from prefixes of the stream (crashes); since L3
  it also checks `PhysRunOK`, and the proof's invariant by running
  (`memInvB`) after the startup and after every operation; since L4, runs
  with lazy restarts (`checkLazy`, also as `#guard`s): after every
  transaction the writer's view is P's, the records are the run's, every
  canonical object is whole, and the memory meets the invariant for the
  frozen run (`frozenB`). `#guard`s in SIS/PhysExample.lean also check the
  assumptions of stage 2 (bergdb item 001, WP E2: TREE, A6' and A-COPY;
  `treeB`, `adoptB`, `copyB`, `evictRunOKB`) on examples 2, 3 and 5 (example
  3 with drops), moved there from SIS/EvictExample.lean in 005-62; `phystest`
  does not run them.
* SIS/HandleExample.lean (bergdb item 009, phase 2, 2b): the physical layer
  with handles by running. The invariants of SIS/HandleTheorems.lean as
  `Bool`s (`hTableOKB`, `hCanOKB`, `hSnapOKB`, `hSlotOKB`, `hRuleROKB`,
  `hLiveWrittenOKB`, `hWrittenOKB`, `hPinOKB`); schedules of evictions
  (`hschedule`: none, every handle that may be evicted, each with probability
  0.3, canonical objects only, snapshots only); runs of examples 2, 3 and 5
  with restarts, checked after every transaction (`checkHandles`: the records
  and D are the model's, reads give P, the invariants hold; reads at earlier
  times also before reads at the last time), and the trusted run
  `runHandles`; counts that show the runs reach the cases of the plan's open
  points (`pointCounts`); the pointers that rule 4 links, by the record they
  name and by how rule 4 by position finds them (`rule4Counts`, bergdb
  005-58); three small examples: open point 1, the written position that the
  slow path writes back into the pointer, and the slow path's test against it.
* SIS/ReclaimExample.lean and ReclaimTest.lean (bergdb item 001, WP R3):
  reclaim by running. Example 4, F1-008-07's reclaim example adapted to
  BergDB: example 3's virtual root and top nodes, one value per leaf, reclaim
  steps that touch the nodes their range traversal visits (without entries)
  and rewrite the values stored before pCut, the first available time at the
  end of an iteration once the startup pos has passed it. `CutOK` by running
  (`cutOKB`; WP R7's, with part 2 over `ReadsAt`, `cutOKAtB`), the largest
  safe cut (`safeCut`), T8 by running (`checkT8`),
  `PolicyCutOK` by running (`policyCutB`), and runs with restarts from cut
  streams (`checkCut`); with eviction, HandleReclaimExample.lean below.
  `#guard` checks on a fixed run: the touch makes clean nodes dirty, and
  without it no cut is safe; T8 and T12 at the safe cut, and T12's
  assumption on the cuts (WP R5); the pSafe wait
  (`pSafeWitness`); a stale reference that WP R3's `CutOK` let through, after
  which a physical read from the cut stream fails (`staleWitness`, WP R7); a
  read in the running process, with eviction, that follows a pointer of a
  replaced node to a version before a cut that WP R7's `CutOK` allows
  (`cutReadWitness`, WP R4; `CutOK` since WP R6 does not); Java's scheme,
  and a stale chain of put-back versions that only the exception of
  `ReadsPhys` for them lets through (`schemeWitness`, WP R6). The three
  witnesses run with handles since bergdb 005-62 (`runHandlesWith`, with
  HandleExample.lean's eviction schedules) and hold as they did with
  Evict.lean's eviction. T-SCHEME by
  running (`checkSchemeB`, WP R6: for every iteration whose scheme conditions
  hold, `CutOK` at its cut position in every later state past the waits; a
  `#guard` on the fixed run). Proved there (WP
  R4): example 4 meets T8's
  assumptions on the virtual root (`execRootOK_spec4`, `virtLiveOK_spec4`;
  also `virtLiveOK_spec4e`).
  `lake exe reclaimtest 20 30`: the same on random runs,
  for four startup pos policies, and with handles (below); `lake exe
  reclaimtest 100 100 scheme`: T-SCHEME only, on larger runs (9 minutes).
* SIS/HandleReclaimExample.lean (bergdb 005-62): reclaim with handles by
  running, on example 4 with cuts and HandleExample's five eviction schedules
  (`checkHandleCut`): after every transaction the records are the run's, cut at
  the largest cut so far, and D is the run's (T12 over handles); reads from the
  first available time on give P, also on the cut stream from the running
  memory (T9 over handles) and after the restart from the cut stream; at the
  end the lookups from the first available time on are the run's. `#guard`
  checks on the fixed run with a cut at 3 (`tsCut4`) and on two runs with
  cuts; `lake exe reclaimtest` runs it on random runs. And at every restart,
  rule 4 by position with the cut as the stream's first position (at the
  restart's cut and at the largest cut so far) against rule 4 by node id
  (`checkHandleCut`), and the pointers that Java skips, by whether they name a
  node with a canonical object (`posCutCounts`, bergdb 005-62, question 2;
  `#guard`s on the two runs); `reclaimtest` prints the counts per policy.
* Check/ and TraceCheck.lean: the trace checker, `lake exe tracecheck`. It
  checks traces of Java runs against the model's definitions
  ([011-11](../items/011-docs-archive/11-level2-alignment.md), section 8.5;
  [docs/trace-format.md](../docs/trace-format.md)). `sh test-traces/run.sh` runs
  its tests. Since bergdb item 001's L5 it reads trace format 2 and checks
  C-L, every first touch after a restart
  against the rule of SIS/Phys.lean (`firstFailures`), and in C-S the top
  nodes' skip slots: their layout and cached times (`topFailures`; section
  13.5 there). Since bergdb 005-04, C-A also checks the assumptions of stage
  2 (`EvictRunOK`): TREE (`treeFailures`) and A6' (`adoptFailures`) after
  every transaction, R(0) included, and A-COPY (`copyFailures`: the pointers
  of new entries) for each change; it counts the adoptions below the old
  parent, which A6' allows and A6 does not (test traces `adopt.trace`,
  `adopt2.trace`, `copy.trace`). Item 001's A4, E2 and E3 had A6, TREE and
  A-COPY as diagnostics. Since item 001's R7 it reads reclaim's lines
  (TOUCH, FA, CUT, PHYSCUT): C-A checks TouchOK (`touchFailures`), C-S
  compares fa(i) and, from the first cut on, runs the model's step on the
  stream cut at the largest cut so far, and C-CUT checks `CutOK` at every CUT
  line and that every physical cut is at or below the decided one
  (`cutFailures`; [001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md),
  section 6). Since R4, a diagnostic that does not fail a trace, C-CUT+: at
  every CUT line, whether a physical read in the running process from f on
  may follow a version before the cut (`readsBelowPhys`: through a pointer to
  a live child, every version of the child at or after the one the pointer
  names; register M48 of 001-07). Since R6, part of C-CUT,
  as `CutOK`'s part 2 is (`ReadsPhys`, with its exception for the versions
  of D that Rule A put back; test trace `physcut.trace`, where only that part
  fails). Since R8's change 3, the
  diagnostic C-L4: the FIRST lines against the Level 4 loader
  (`loader4Failures`: no snapshot from the node table; section 13.5 of
  011-11). Since J4, C-P: INV-SLOT on Java's physical states,
  the SLOT lines of the exporter's run E, which runs with a forced eviction
  schedule (`slotFailures`, after the model's `invSlotB` of the design before
  handles, removed in bergdb 005-62; test traces `slot.trace` and
  `badslot.trace`;
  [001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), section 7.3).
  Since bergdb item 009, step 4c, C-H: the model's invariants with handles
  (SIS/HandleTheorems.lean) on run E's handle state, which the exporter
  writes as the model's memory with handles (the HMEM, HTABLE, HANDLE, HOBJ
  and HPTR lines; `toHMem`, `handleFailures`, after the `Bool` twins of
  SIS/HandleExample.lean): the table and the handles, the canonical objects
  and D, the snapshots (an object's history by its number of entries and a
  hash of them, `historyHash`), the record rule by the model's own
  `HMem.refOf`, the snapshots against Rule R, live handles without a written
  position, written positions and references that name versions, the fast
  path's test, T-PIN's unpinned objects written; and how often the states
  reach the cases of `pointCounts` (test traces `handles.trace`,
  `badhandle.trace` and `badhash.trace`;
  [009-05](../items/009-handles/05-handles-alignment.md), section 4).
* SIS/BoundExample.lean (bergdb item 007): T3 by running. The policy of
  the example of section 7 is a startup distance of two records; on random
  runs of example 2 with a cost like bytes (`bytes2`), the section without
  its last record stays below d with `sdPolicy`, with and without restarts;
  a sketch of BergDB's take before 007-07 (`oldTake`) with a tight node
  limit does not keep up. Since bergdb 007-08, BergDB's take since 007-07:
  `dither` and `share` give the bits of Java's `TransSeq.dither` and share
  (until 005-79);
  `javaTake` gives the result of Java's `TransSeq.take` on 300 cases that
  `TakeCheck` (../items/007-bounds/08-step4-take-in-lean/) and `takeCase`
  make with the same generator; runs of example 2 with `javaTake` at a
  constant setting, with restarts (the same stream as without, T2) and
  with decreases of the setting meet `T3_take_step`, `T3_take` and
  `T3_take_decrease`; the counterexamples to `KeepsUp` with twice the
  setting, to the new bound right after a decrease, and to the rerun's
  bound with the last transaction's own bytes in place of its record; and a
  run where the section comes down by one unit a transaction (`slowSpans`).
* Check/Fast.lean and Check/R4.lean, the checker's fast paths (bergdb item
  001, WP C2). `markOf`, `writeAll`, `reachList` and `step` have fast
  versions, proven equal to them and marked `@[csimp]` (`markOf_eq_fast`,
  `writeAll_eq_fast`, `reachList_eq_fast`, `step_eq_fast`), so the compiled
  checker runs the fast versions where the model's code calls the
  definitions, which stay as they are: P and the latest versions are looked
  up through hash maps, and step 3 computes the reachable nodes once per
  transaction, not once per node. `step_eq_fast` is there because a
  `@[csimp]` equation changes only code compiled after it: `stepFast` is
  `step` word for word, compiled again. R4 (`VirtStep.closure`) is tested
  first through the chain of top node ordinals (`r4Fast`, sound by
  `r4Fast_sound`; `PredChain` and `mem_topClosure` are from the
  `R4Bridge.lean` of F1-008-13's review in the f1 repository), and the
  exponential `topClosure` runs only when that test fails. On 2026-10-16 (001-02) the
  medium set took 88 s instead of 6,770 s, and a trace of 5,000 transactions
  at node size 30 with 1,000 keys 428 s and 128 MB.

Choices made in Lean that the text leaves open:

* Node ids and times are natural numbers; root has id 0.
* A reference is the record number of the version (a node is written at
  most once per record), and a missing reference is a vpos.
* `good` and the reading of the stream do not follow a pointer to a node
  that is not on a lower level. This makes the recursion end, and changes
  nothing for a structure that has A4.
* gd(i) lists the nodes of step 3 sorted by id, then the touched nodes
  that step 3 did not find otherwise, sorted by id (since WP R3), then those
  of step 7, so that a record does not depend on the order of nodes in P.
  The checker compares gd as a set.
* Step 7 tests the taken nodes lowest level first, adding each still-dirty
  node to D before the next test, so that the conservative test sees
  children that stayed dirty.
* P after startup is a list of nodes: each node reached when reading the
  stream at some time t <= s, with the history of the version it is read
  from at the latest such t, cut at s; then the rerun.
* Step 3 lists the nodes of P by id (`allIds`), sorted, so that a record
  does not depend on the order of the nodes in the list that holds P.
* `Time` and `NodeId` are notations for `Nat`, so that arithmetic
  automation (`omega`) sees through them.
* T1 and T2 are stated for the exact still-dirty test and for BergDB's
  conservative one (`javaTest`), since 2026-10-15; with a virtual root, for
  BergDB's only (since 2026-10-16).
* With a virtual root, top(i) is the root's child named by the root's last
  entry up to s(i), with the record of its latest version (`topV`). BergDB's
  topPos names the latest version of the newest top node written; the trace
  checker compares the two (C-S).
* With a virtual root, startup rebuilds the root's history from the root
  children read: for each time t <= s, the entry (t, rootVal z) of the root
  child z whose entries are at t (`rootVersion`).


Reading Lean
============

Enough to read the trusted part:

* `def f (x : A) : B := ...` defines a function f from A to B. Arguments in
  `{ }` are filled in by Lean; `[DecidableEq V]` says that values of type V
  can be compared.
* `structure` is a record type with named fields; `{ f := 1, g := 2 }`
  builds one, `r.f` reads a field, `{ r with f := 3 }` copies with a change.
* `Option A` is `some a` or `none`. `List A` is a list; `xs.map f`,
  `xs.filter p`, `xs.foldl f a` (a loop), `xs.flatMap f`, `xs.all p`,
  `xs.any p` are the usual list functions. `List.range n` is 0, ..., n-1.
* `match e with | p => ...` is a case analysis. `fun x => e` is a lambda.
* `termination_by n.level` tells Lean why a recursive definition ends: the
  level goes down at each call.
* `Prop` is the type of statements; `∀`, `∃`, `∧`, `∨`, `→` are as in logic.
  A `theorem` is a statement followed by its proof after `:= by`.
* `Bool` values are `true` and `false`; `b = true` turns one into a
  statement.

Two good introductions, if more is wanted: Functional Programming in Lean
(chapters 1 and 2) and Theorem Proving in Lean 4.


Status
======

What the model holds now. How it got here, with the checks run at each
step and the changes to the trusted part, is the model's log, 011-12.

Proved, each theorem with nothing but Lean's standard axioms (Build and
run):

* Level 2, the abstract model: T1 (`T1_recovery`, `T1_crash`,
  `T1_nodes`) and T2 (`T2_restart`), for the exact and BergDB's still-dirty
  test, with step 3 by testing or by marking, with and without a virtual
  root; T13 (`T13_markExact`): marking gives the same records as testing;
  D closed upward (`T15_closed`).
* Stage 1 of bergdb item 001, the physical layer: lemma M (`LM_newer`,
  `LM_ruleR`, `LM_cutTo`; L2), T1-L (`T1_lazy`, L3), CC and T2-L
  (`CC_canonical`, `T2_lazy`, L4); Java's first touches after restarts are
  checked against the model's rule (C-L, L5).
* Stage 2, eviction, over handles (009): T-CACHE, T-READ, T2-C and T-PIN
  (`tc_handles`, `tr_handles`, `t2_handles`, `tr_handles_restarts`,
  `tp_handles`), and rule 4 by position (005-58).
* Stage 3, reclaim: the definitions and T13' (`T13_markTouch`, R3), the
  checker on Java's reclaim traces with the red list (R7), T8
  (`T8_recoverCut`, R4), `CutOK`'s part 2 over `ReadsPhys` (R6, part 1:
  register M48, option (a), Frans), T12 for runs without eviction
  (`T12_restartCut`, R5); over handles T9 and T12 with eviction
  (`t9_handles`, `t12_handles`), and rule 4 by position after a cut
  (005-62).
* Bounds (bergdb item 007): T3 (`T3_section`, `T3_restarts`, `T3_reads`,
  `T3_rerun`, `T3_bounded`), and T3 for BergDB's take (`T3_take_step`,
  `T3_take`, `T3_take_restarts`, `T3_take_decrease`,
  `T3_take_decrease_restarts`, `T3_take_rerun`, `T3_take_reads`; 007-08).

Checked by running: the `#guard`s of `lake build`, the random runs of
`sistest`, `phystest` and `reclaimtest` (Build and run), and Java's traces
by `tracecheck` ([levels.md](../docs/levels.md)).

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
