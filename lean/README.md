Self-indexed streams in Lean
============================

Started 2026-10-12. Written by Claude for Frans Lundberg.

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


Build and run
=============

Needs elan (`brew install elan-init`). The toolchain version is in
`lean-toolchain`; elan downloads it on first use. No Mathlib.

    cd lean
    lake build              # checks every file but the test programs, runs the #guard tests
    lake exe sistest 20 40  # random runs: 20 seeds, 40 transactions each (7 min)
    lake exe phystest 20 40 # the physical layer on random runs (7 min)
    lake exe reclaimtest 20 30     # reclaim: random runs with cuts (1 min)

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


What to read
============

The trusted part is the definitions and the theorem statements. If they say
what sis-model.md says, a proof that Lean accepts proves the theorems for
the model. Read in this order; each definition has a comment that points to
its section in sis-model.md.

| File | Contents | sis-model.md |
|---|---|---|
| SIS/Basic.lean | Entries, histories, x@t (`upTo`), nodes, P (`Struct`), changes (with the touch, `Changes.touch`), the structure's functions (`Spec`, with the virtual root's switch `virt`, `topLevel` and `rootVal`), root children (`isTop`), reachability, P@t (`view`), equivalence (`Equiv`) | 2, 3 |
| SIS/Stream.lean | Versions, records (top(i) as a node and a record; fa(i), `Record.fa`), the stream, lv(x) (`Stream.lv`), references, `good`, `dirty` | 4, 5 |
| SIS/Algorithm.lean | DB = <P, D, S>, the policy, the still-dirty test and the choice of step 3 (`Algo`), the exact and BergDB's still-dirty tests (`exactTest`, `javaTest`), marking (`changed`, `marked`, `markOf`), what can be in D and written (`written`), top(i) (`topOf`, `topV`), the first available time (`Algo.faPolicy`, `lastFa`, `firstAvail`), step 3 with the touch (`touchOf`, `gotDirty3`), transaction i (`step`), R(0) (`init`), `run` | 6.1 |
| SIS/Startup.lean | `newest` (R(s) to R(k)), Rule R (`follow`), reading the stream (`readFrom`), where reading starts (`topVersion`, `startVersion`; with a virtual root `readTops`, `topsRead`, `rootVersion`), P up to s (`baseStruct`), `rerun`, `startup` | 6.2 |
| SIS/Assumptions.lean | Assumptions A2 to A5, the data node rules and the touch's (`SpecOK`, `StepOK`, `RunOK`), with a virtual root R1 to R4 (`VirtInit`, `VirtStep`, `topClosure`), `runRestarts` | 3.4 |
| SIS/Theorems.lean | T1 (`T1_recovery`, `T1_crash`, `T1_nodes`), T2 (`T2_restart`), T13 (`T13_markExact`) | 9 |
| SIS/Phys.lean | The physical layer, what Java holds in memory (bergdb item 001, WPs L1 and L3): objects (`Obj`), their slots (`Slot`), the memory with the node table (`Mem`); Java's first touch (`Mem.follow`: Rule R, the table, the version read, cut back in the section); reads (`Mem.read`); the lazy startup (`lazyStartup`); a version cut back to a time (`Version.cutTo`); the operations after startup (`Op`, `Mem.step`, admissible: `OpsOK`); the assumptions of the physical layer (`PhysStep`, `PhysRunOK`); the writer after a lazy startup (WP L4: its view through the physical layer, `Mem.view`; its transaction, `lazyTrans`, with the record of `stepWith`, `step` with its change given) and a run with lazy restarts (`runLazy`); the writer's paths reach the touched nodes too (`pathOf`, WP R3); the positions of the startup section's canonical objects, as Java's startup sets them (`Mem.sectionPos`); the assumptions of stage 2, eviction (bergdb item 001, WP E2; 001-08, section 4: `EvictStep`, TREE, `treeAt`, and A6', `adoptAt`; A-COPY, `CopyStep`; `EvictRunOK`), in Evict.lean until bergdb 005-62 | — (011-11, 13; 001-08, 4) |
| SIS/Handle.lean | The physical layer with handles (bergdb item 009, phase 2, 2a; aligned with Java's step 3a; ../items/009-handles/02-implementation-plan.md, section 4): objects by address (`HObj`), pointers with a reference and a handle (`HPtr`), handles (`Handle`: node, object, written position, dead), the table from node to live handle (`HMem`); following a pointer (`HMem.followR`: the fast path's test, else the reference after Rule R raised to the held handle's written position and written back, `HMem.setRef`, the live handle, `HMem.resolve`, and the load, `HMem.load`; `HMem.follow`, with the writer's `HMem.promote`); reads (`HMem.read`); the writer's walk and change (`HMem.reachOnPath`, `HMem.newPtr`, `HMem.applyChange`); the record rule (`HMem.ptrRef`, `HMem.refOf`) and the physical writer (`HMem.writeNode`, with `resolvePointers`; `handleTrans`); eviction (`HMem.evictable`, `HMem.evict`); startup with rule 4 by handles (`handleStartup`, `Mem.toH`, `HMem.linkD`); rule 4 by position, Java's since bergdb 005-57 (`inPosToId` for Java's `posToId`, `HMem.byPos`, `HMem.linkDPos`, `handleStartupPos`); after a cut, with Java's skip of the pointers below the stream's first position (`HMem.linkDPosFrom`, `handleStartupPosFrom`, bergdb 005-62); reads and evictions between transactions (`HCacheOp`) and runs (`runHandles`; with rule 4 by position, `runHandlesPos`). The file's header lists the choices where the plan is vague | — (../items/009-handles/02-implementation-plan.md, 4) |
| SIS/HandleTheorems.lean | The statements over handles (bergdb item 009, 2c): the invariants (`HTableOK`, `HCanOK`, `HSnapOK`, `HSlotOK` for the record rule, `HRuleROK`, `HLiveWrittenOK` and `HFastOK` for the fast path's test, `HWrittenOK`); T-CACHE (`TC_handles`, proved: `tc_handles`), T2-C (`T2_handles`, with restarts), T-READ (`TR_handles`; with restarts, `TR_handles_restarts`), T-PIN (`TP_handles`); rule 4 by position (bergdb 005-58): the positions of the pointers that rule 4 links (`Rule4_positions`), rule 4 by position is rule 4 by node id (`Rule4Pos_handles`), and so are the runs (`RunPos_handles`); all proved in SIS/Proof/ (`tc_handles`, `t2_handles`, `tr_handles`, `tr_handles_restarts`, `tp_handles`, `rule4_positions`, `rule4Pos_handles`, `runPos_handles`) | — (../items/009-handles/02-implementation-plan.md, 5, phase 2) |
| SIS/PhysTheorems.lean | Lemma M: a newer version of a node serves every time an older one serves (`LM_newer`), so Rule R's version does (`LM_ruleR`), and a version cut back to s serves the times up to s (`LM_cutTo`); T1-L (`T1_lazy`): after the lazy startup from the stream of a run, or of a prefix of it (a crash), and any reads and writer follows, a read at any time up to the last record gives P at that time; CC (`CC_canonical`): in a run with lazy restarts, every canonical object holds its node's whole history; T2-L (`T2_lazy`): such a run appends the records of the run without restarts; `step_eq_stepWith`; stage 2 (bergdb item 001, WP E3): D closed upward (`T15_closed`). Stage 2's T-CACHE, T-READ, T2-C and T-PIN are stated over handles (SIS/HandleTheorems.lean); over Evict.lean they were here until bergdb 005-62 | 5.1, 9 |
| SIS/Reclaim.lean | Level 3, reclaim (bergdb item 001, WP R3): what a cut leaves of a version (`Version.stub`) and of a record (`Record.cut`); the stream after a cut (`cutStream`); the versions that a lookup at a time may read (`ReadsAt`, WP R7); when a cut is safe (`CutOK`); the same lookups from f on (`SameFrom`); policies that a cut does not change (`PolicyCutOK`); a virtual root seen only through its live children (`ExecRootOK`), whose live children are those of its last entry (`VirtLiveOK`, WP R4); runs that restart from cut streams (`runRestartsCut`, `cutMax`) | — (001-07, 5) |
| SIS/ReclaimTheorems.lean | T13' (`T13_markTouch`, WP R3): with touches, step 3 gives exactly the index nodes not in D (and not a virtual root) that are dirty or touched; T8 (`T8_recoverCut`, WP R4): after a safe cut, startup from the cut stream gives the same lookups at every time from the first available time on (`SameFrom`), and the same D; T12 (`T12_restartCut`, WP R5): a run that restarts from safe cut streams appends the records of the run without restarts (its stream is that run's, cut at the largest cut), with that run's D and lookups from the first available time on. T9 and T12 with eviction are stated over handles (SIS/HandleReclaimTheorems.lean); over Evict.lean they were here until bergdb 005-62 | — (001-07, 2.2, 2.10) |
| SIS/HandleReclaimTheorems.lean | Level 3's reclaim theorems with eviction over handles (bergdb 005-62), as definitions of type `Prop`: the run with handles that restarts from cut streams (`runHandlesCut`); T9 with handles (`T9_handles`): in a run with handles as in `T2_handles`, after a safe cut, a read through the handles at any time from the first available time on gives the same on the cut stream as on the whole stream (memory and nodes), and gives P; proved (`t9_handles`, SIS/Proof/HandleCutRun.lean); T12 with eviction over handles (`T12_handles`): the run with handles that restarts from safe cut streams appends the records of the run without restarts, cut at the largest cut, with that run's D and lookups from the first available time on; proved (`t12_handles`, SIS/Proof/HandleCutT12.lean); rule 4 by position after a cut (question 2): the run with cuts and Java's rule 4 by position (`runHandlesCutPos`), the startup from a stream cut safely with it is `handleStartup` (`Rule4PosCut_handles`), and so is the run (`RunPosCut_handles`); proved (`rule4PosCut_handles`, `runPosCut_handles`, SIS/Proof/HandleCutPos.lean) | — (001-07, 2.9, 2.10; ../items/005-todo/62-lean-t9-t12-over-handles.md) |
| SIS/Bound.lean | Bounds, part 1 (bergdb item 007): the cost of the records R(a), ..., R(b-1) for any cost of a record (`Stream.cost`); the startup pos that a startup distance d asks for (`sdTarget`); a policy that keeps up with d (`KeepsUp`); the startup distance policy (`sdPolicy`). BergDB's take (bergdb 007-08; `TransSeq.take` since 007-07): the startup section without its last record, which is the span of its transactions (`Stream.span`); a pace, any rule that decides whether to take the next transaction (`Pace`); the take's loop (`takeLoop`) and the take, whole transactions oldest first, each taken if it begins max(2 sd, span) or more before the end of the stream or if the pace takes it, with the setting sd any function of the transaction (`takePolicy`); BergDB's pace, its share and its dither in the double arithmetic of Java's take from 2026-10-28 until 005-79 (`share`, `dither`, `javaPace`), and the take with it (`javaTake`); no theorem uses these four, kept to check the model against that arithmetic (the `#guard`s, TakeCheck); Java's take is in integers since 005-79 (015-03) | 10 (../items/007-bounds/01-startup-bound.md, 3; ../items/007-bounds/08-step4-take-in-lean.md, 1) |
| SIS/BoundTheorems.lean | T3 (`T3_section`): in every run whose policy keeps up with d, the startup section without its last record costs less than d; also with restarts (`T3_restarts`); what startup reads (`T3_reads`) and reruns (`T3_rerun`), and with records of bounded cost (`T3_bounded`). No assumption but the policy. T3 for BergDB's take (bergdb 007-08), for every pace: after a transaction on any database, the section costs less than max(2 sd, the section before) (`T3_take_step`); with settings at most M, less than 2 M, also with restarts (`T3_take`, `T3_take_restarts`); after a change of the setting to sd', less than 2 sd' or at least one less for each transaction since (`T3_take_decrease`, `T3_take_decrease_restarts`); what startup reruns and reads (`T3_take_rerun`, `T3_take_reads`). No assumption but the policy | 10 (../items/007-bounds/01-startup-bound.md, 3; ../items/007-bounds/08-step4-take-in-lean.md, 2) |

The proofs, in SIS/Proof/ (not needed for reading the statements):

| File | Contents |
|---|---|
| Basic, Reach | Histories, nodes, reachability as an inductive definition, growing structures |
| StreamLemmas, Write | Latest versions, `good` and `dirty`, stability (`good_mono`), writing versions |
| Run | The parts of a transaction, runs, and the invariant `Inv` (INV-1 to INV-4 and the facts about S and P) |
| Init, Util, StepFacts, StepP, StepS, StepD, StepInv | The invariant holds after T(0) and after every transaction (`inv_st`) |
| Mark | Marking the access path of the change finds exactly the dirty index nodes not in D (`step_marked_iff`, T13) |
| StepFacts, Fresh, VStep, EvLogic (the touch) | WP R3: what step 3 gives with touches (`mem_touchOf`, `step_gd3_mem`, `step_gd3_of_touch`); the nodes reachable before the change with a touched node below them are touched, so a clean node's live children stay out of D (`step_cleanFresh`) and D stays closed upward (`step_touch_D1`, with A6' also before the change); a root child that a root child points to is not reachable (`VInv.deadTops`), so it is never touched |
| Still | What the proofs need of the still-dirty test (`StillOK`), for the exact test and BergDB's (`java_stillOK`) |
| VStep | With a virtual root, the transaction keeps `VInv` (`step_vinv`): the root children, the root's history, R4, and that the latest version of a root child names the latest versions of the root children it points to (`step_fresh`, which needs BergDB's still-dirty test) |
| RunFacts | How the states of a run relate |
| Recon | L-OUT (`Inv.lout`) and L-SEC (`Inv.recon`), reading with Rule R |
| Read | Reading from a version that is good with Rule R (`Inv.read`) |
| VRead | With a virtual root, startup reads every root child created up to s, at its latest version, and rebuilds the root (`Inv.readAt_spec_virt`) |
| Base | Reading the stream (`Inv.readAt_spec`), P up to s (`Inv.base_get?`) |
| Recovery | The rerun, and T1 in the strong form (`T1_strong`) |
| Restart | Every part of a transaction depends on P only through its nodes, and T2 (`T2_strong`) |
| Newer | Lemma M (`Inv.newer`): references name latest versions, so a newer version's references name versions at least as new; by induction on the level |
| Fresh | Two facts of every run: a clean reachable node's latest version names the latest versions of its live children, which are not in D (`CleanFresh`, with BergDB's still-dirty test); a data node has one version (`DataOnce`) |
| PhysMem, PhysInv | The memory's operations; the invariant of the proof of T1-L at time K (`MemInv`): canonical objects (`CanonOK`: in the node table, the node's history up to K, slots good at every time the node is reachable and fresh at K), snapshots (`SnapOK`, `SnapSlots`), memory slots (`MemSlotOK`), the nodes that have canonical objects (D, the section, the entries after s) |
| PhysFollow, PhysRead, PhysWriter | The first touch keeps the invariant (`follow_reader`); reads give P (`MemInv.read_ok`, also from a stream that agrees on the nodes without canonical objects, `StreamAgree`); the writer's follow makes the object canonical (`MemInv.follow_writer`) |
| PhysLogic, PhysRun | What the run says of nodes without a canonical object (`KCtx`; `Cover.mg`: their latest version is good; `KCtx.fresh_ref`, `Cover.cf`: its references are fresh) |
| PhysPath, PhysRerun, PhysApply, PhysStep | The rerun of one transaction: the writer's paths, reached highest level first (`MemInv.reachPath_ok`); the change applied keeps the invariant from K to K + 1 (`MemInv.applyChange_ok`) |
| PhysLazy, PhysBase | The rerun keeps the invariant (`rerun_fold_ok`); the memory before it meets it at s (`PCtx.base_ok`) |
| PhysT1 | The operations keep the invariant (`MemInv.ops_ok`); T1-L in the strong form (`T1_lazy_strong`) |
| PhysFrozen | The frozen run (WP L4): the same transactions with the startup pos frozen after a restart at k1 (`frozenAlgo`); after k1 it takes no node and writes only new data nodes, so its states only grow (`frozen_grow`), and the invariant carries over (`MemInv.transfer`) |
| PhysT2 | A run with lazy restarts: after every transaction, ⟨P, D, S⟩ is the run's, and the memory meets the invariant for the frozen run from the last restart (`LazyInv`, `lazyInv_all`); CC and T2-L in the strong form (`T2_lazy_strong`) |
| EvLogic | Stage 2 (WP E3): the logical facts that the design rests on (`EvLogic`): D is closed upward, and a current clean node has no pointee in D and names the latest versions of its pointees (`evLogic_st`); D closed upward alone needs no A6' (`DClosed`, `step_closed`; WP R5) |
| LogicFacts | Logical facts and list lemmas that the proofs of the physical layer share (bergdb 005-62, from the proof files of the design before handles): D's got-dirty indices (`dOf`), Rule R's bounds (`Inv.ruleR_bound`, `Inv.ruleR_lv0`), the latest versions (`Inv.lv_whole`, `Inv.ref_versionAt`), a clean node's latest version good for every time it is reachable (`Inv.clean_good`), TREE's one current parent (`treeAt_unique`), the parts of a transaction from step 3 on (`D1Of`, `takenOf`, `stepOf`), which depend on P only through its nodes (`stepOf_congr`) |
| PhysStart | The lazy startup from the stream after T(k) (WP E5): its rerun keeps `RInv` (every object canonical, every stream slot naming its pointee's latest version after Rule R and naming a version, a slot for each pointee; since bergdb 005-58 also: no version of a stream slot's pointee between it and the section, `RInv.near`, and every slot for a pointee, `RInv.keys`; `rinv_lazyStartup`); the node table has no repeated keys (`tblND_lazyStartup`), and no object two slots for the same pointee (`slotsND_lazyStartup`) |
| HandleMem, HandleInv | Bergdb item 009, 2d, T-CACHE over handles: the memory's operations; the fast path's test with a pointer's own reference agrees with the slow path's (`hFastOK_of`); evicting a handle changes no pointer's record (`HMem.ptrRef_evict_of`); the invariant with handles (`HEInv`: the table and the handles, INV-CAN, INV-SNAP, INV-SLOT for the record rule, the live pointers of current canonical objects, the snapshots against Rule R, live handles without a written position, references that name versions), and an eviction keeps it (`HEInv.evict`) |
| HandleFollow, HandleRead | The readers' follow keeps it (`HEInv.followR_ok`: the fast path; the slow path's write-back, live handle and load; and, for reads at earlier times, what the pointers give, `HMem.KeepPtrs`), so reads and any operations between transactions do (`HEInv.cacheOps`); a read at the last time gives P, the writer's view (`HEInv.view_ok`) |
| HandleWalk, HandleApply, HandleApplyInv | The writer's promote and its walk (`HEInv.follow_writer`, `HEInv.reachPath_ok`); the change applied, with TREE and A-COPY (`HEInv.applyChange_ok`, `HAInv`) |
| HandleWrite, HandleWrites, HandleStepInv | The writer's loop writes the model's versions (`writeNodesH_eq`), its two loops the model's record (`HAInv.loops_vs`); the memory after the record has the next state's invariant (`HAInv.final_ok`) |
| HandleTrans, HandleInit, HandleStart, HandleRecords | One transaction (`HEInv.handleTrans_ok`); runs (`TC_runH`); stage 1's memory with handles (`Mem.toH`) and rule 4 with handles (`HMem.linkD`), by lookup; the startup with handles from the stream after T(k), R(0) included, has the invariant (bergdb 005-62: the lazy startup's memory with the positions of its section meets `StartMem`, `startMem_st`, by `RInv`; taken to handles and with rule 4 it has `HEInv` and the pointer facts of T9's invariant, `StartMem.heinv`, `heinv_startup`, `heinv_init`); T-CACHE over handles (`TC_handles_records`, `tc_handles`) |
| HandleHist, HandleHistTrans, HandleReadT | Bergdb item 009, phase 4a, T-READ over handles: the invariant for reads at earlier times (`HInvH`: the pointer of a canonical object for a live child at a time t holds a canonical object, or its slow path's reference names a version good for t, or, by INV-SLOT's second half, a node of D), kept by reads (`HInvH.followR`), evictions (`HInvH.evict`: a pointer whose handle held the evicted canonical object then has its node's latest version, clean, as its slow path's reference), every transaction (`HInvH.handleTrans_ok`) and in every run (`HInvH.run`); a read at any time up to the last record gives P (`HEInv.readT_ok`, `tr_handles`) |
| HandleRestart, HandlePin | The startup with handles from the stream after T(k) has both invariants (`heinv_hinvH_startup`; the invariant for reads at earlier times from `StartMem`, `StartMem.hinvH`); the physical writer with handles depends on P only through its nodes (`handleTrans_congr`); runs with restarts (`HandleInvR`, `handleInvR_all`); T2-C and T-READ with restarts over handles (`t2_handles`, `tr_handles_restarts`); a live handle whose object is not pinned may be evicted (`HEInv.evictable_of_unpinned`), T-PIN (`tp_handles`) |
| HandleLinkPos | Bergdb 005-58, rule 4 by position: a pointer that holds no handle in the memory before rule 4 is a stream slot of the lazy startup's memory (`before_ptr`), so `RInv` says what it names (`before_ptr_facts`); a canonical object there is at its node's latest position (`before_canon`); the positions (`rule4_positions`); rule 4 by position is rule 4 by node id where each pointer it leaves is in `posToId` or at the canonical object's position (`HMem.linkDPos_eq_linkD`), which the startup's memories meet, with the first version of a node in the section (`first_version`), A4 and a data node's one version (`rule4Pos_handles`); runs (`runPos_handles`; `runHandlesPos` is `runHandles` but for its startups, `runHandlesPos_of_startup`) |
| HandleCut | Bergdb 005-62, T9 over handles: the invariant on the pointers (`CInvH`: a canonical object of a clean written node has, for each pointee that its latest version names at r0, a pointer that holds a canonical object or whose slow path's reference is r0 or later, `HMem.PtrAtLeast`; with a virtual root, the root's object holds the canonical objects of the root children of D and names the others at their latest versions or later); a follow on a stream cut safely is the follow on the whole stream when the pointee has a canonical object or every version at or after the slow path's reference is one `ReadsPhys` covers (`HEInv.followR_cut`, `HPtrCutT`); the pointers of an object a read at t may reach are such (`HEInv.cutPtr`), so a read at a time from f on gives the same on the cut stream (`CInvH.read_cut`); reads and evictions keep `CInvH` (`CInvH.readAt`, `CInvH.evict`, `CInvH.cacheOps`) |
| HandleCutTrans, HandleCutRun | One transaction keeps `CInvH`: the writer's promote and walk, the change (new pointers hold canonical objects or copy pointers at their pointees' latest versions), the root's pointers to the nodes on the paths and the new ones (`HEInv.rootPtrs_change`), the writes and the next state (`CInvH.next`, `CInvH.handleTrans_ok`); the startup with handles gives it (`cinvH_startup`, from the pointer facts that `heinv_hinvH_startup` now also gives); runs with restarts (`HandleInvC`, `handleInvC_all`), and T9 over handles (`readCutH`, `t9_handles`) |
| HandleCutLater | Bergdb 005-62, part 1 of T12 over handles: in a state later than a restart from a stream on which a cut at c is safe (`Later`, `later_st`; and the versions that the loads may read then, `LaterOK`), a read through the handles at a time from the restart state's first available time on gives the same on the cut streams (the stream now, and the restart's for Rule R) as on the whole streams (`CInvH.read_later`), and so does the writer's walk (`HEInv.reachPath_later`): every load is of a version at least as new as one that `LaterOK` allows (`HPtrLaterT`, `HLaterSafeT`, `HEInv.laterPtr`); a snapshot taken from the live handle is newer than the version the pointer names, and names its live children at least as new (`Inv.ref_mono`, `ruleRRef_mono`). T9's invariant is all it needs of the memory |
| HandleCutStart | Bergdb 005-62, part 2 of T12 over handles: the memory with handles with another root object (`HMem.withRoot`), the two root objects (`RootRelH`: the same but for the history and the pointers of the root children that only times before the first available time need); `Mem.toH` and rule 4 with handles keep a memory with another root object (`Mem.toH_withRoot`, `HMem.linkD_withRoot`), so the startup with handles from a stream cut safely is the one from the whole stream but for the root's object (`handleStartup_sim`, from `sectionPos_sim`, the same for the lazy startup with the positions of its section, SIS/Proof/CutLazyStart.lean) |
| HandleCutSim | Part 3 of T12 over handles: the steps of a transaction and the reads on the memory with another root object and the cut streams, against the same on E's memory and the whole streams, give the same results and memories that differ only in the root's object again, with the same history: the follow and the read from the root (`HEInv.followR_sim`, `CInvH.read_sim`, with `CInvH.readAt_sim` below the root), the writer's walk (`HEInv.reachPath_sim`), the change (`HMem.withRoot_applyChange`, the source search finding corresponding objects; the two root objects get the same new entries, `RootRelH.addRoot`), the writes (`HMem.withRoot_writeNodes`, with Rule R of the cut stream, `HMem.writeNodes_cutS0`) and an eviction (`HMem.withRoot_evict`) |
| HandleCutTransSim, HandleCutT12 | Part 4 and 5 of T12 over handles: one transaction of C (the run with handles that restarts from cut streams) against one of E (the run with handles that restarts from the whole streams at the same points, with the same cache operations): the same record as the logical step from C's state, and memories that differ only in the root's object (`handleTrans_sim`); C's cache operations (`ops_simH`); the two runs side by side (`RunSimH`, `runSimH_zero`, `runSimH_step`: a restart by `handleStartup_sim`), so C appends the records of the run that restarts from cut streams (`handleCut_restartsCut`), and T12 over handles (`t12_handles`) follows from `restartCut` |
| HandleCutSkip | Bergdb 005-62, question 2: the pointers that Java's rule 4 skips after a cut name no node with a canonical object (`cutSkip_lazy`): the rerun's invariant against the safe cut (`CutInv`: every object is the root's or of a node whose latest version is at c or later; a live stream slot below c of a node reachable then names a node without a version in the section, `cut_ref_live`; a stream slot below c of a node of D names such a node, or one not reachable from then on without a canonical object), for the memory before the rerun (`cutInv_lazyBase`), the walk (`CutInv.reachOnPath`) and the change (`CutInv.applyChange`: a new pointer without a source, `stale_absurd`, with TREE, no resurrection `reach_back`, `clean_ref_lvAt` and `PhysStep`'s `liveNew`), and the rerun (`cutInv_lazyStartup`) |
| HandleCutPos | Rule 4 by position with a first position is rule 4 by position where the skipped pointers name no node with a canonical object (`HMem.linkDPosFrom_eq_linkDPos`); `posToId` on a cut stream (`inPosToId_cut`); `rule4Pos_handles`'s condition (`rule4Pos_cond`) carried to the startup from a stream cut safely by `sectionPos_sim` (`handleStartupPosFrom_cut`; `rule4PosCut_zero` without the skip; `rule4PosCut_handles`); runs (`runHandlesCutPos_succ`, `runPosCut_handles`, the restarts' streams by T12's `RunSimH`) |
| CutStream, CutRead | Stage 3 (WP R4): the stream after a cut (its records, `versionAt`, `newest`, the last record); a pointer followed, or a read from a version, on a stream cut at or before the startup pos gives what it gives on the whole stream if it reads no record before the cut (`follow_cut`, `readFrom_cut`); a read from a version that a lookup may read reaches only such versions (`readFrom_readsAt`); a version a lookup may read, a physical read may follow (`ReadsAt.phys`, WP R6) |
| CutAgree, CutRerun | Structures that agree for lookups from f on (`CutAgree`); a transaction's change is the same on both (`exec_cutAgree`, with `ExecRootOK`), and so is the rerun of the startup section (`rerun_cutAgree`, with `VirtLiveOK`), which keeps every node it starts with the run's (`rerun_cutAgree_nodes`, WP R5) |
| CutBase, CutTops, CutStart | Startup's reads of a stream cut safely at the times from f to s: without a virtual root, the whole stream's (`Inv.readAt_cut_nv`); with one, the whole stream's but for the root's version, which startup rebuilds from the root children it can read: the root children live from f on are read at their latest versions (`Inv.topsRead_cut_all`), so the rebuilt root has the root's live children from f on (`Inv.cutRoot_live`, `Inv.readAt_cut_v`) |
| CutRecover | P up to s, read from the cut stream, agrees with P after T(s) for lookups from f to s (`base_cutAgree`); T8 (`recoverCut`) |
| CutRestart | WP R5: a cut of a cut (`cutStream_cutStream`); a state related to the run's (`CutRel`: the run's stream cut at m, its D, its nodes for the lookups from f on and for D), on which a transaction appends the run's record and keeps the relation (`step_congr_cut`) |
| CutHist | WP R5: the nodes of D that no lookup from f on may reach (M33, M34): every node of D was reachable at a time at which its ancestors (it included) are in D, each with an entry from just after that time or a version in the record of its entry, put back by Rule A (`DAnchor`, `dAnchor_st`: Rule A with BergDB's test along the path, `step_anc_persist`, and D closed upward, `dClosed_st`); with a virtual root, every root child created after a root child of D is in D (`TopsD`, `topsD_st`) |
| CutHistRead | WP R5: after a safe cut, startup reads such a node at that time through its ancestors' versions in the startup section (Rule R), at its newest version, from the cut stream as from the whole stream (`Inv.baseCut_get?_hist`; with a virtual root, the root children from its root child then on are read, `Inv.topsRead_cut_from`); T8 with D's nodes (`recoverCut_dNodes`) |
| CutRuns | WP R5: the relation after every prefix of a run with restarts from cut streams (`restartCut_rel`), and T12 (`restartCut`) |
| CutLazySim, CutLazyStart | WP R5, for T12 over handles: stage 1's memory with another object for the root (`Mem.withRoot`); two root objects that agree from f on (`RootRel`: the same live children from f on, and the same slots for the pointees of the cut run's root); the lazy startup with the positions of its section from a stream cut safely is the one from the whole stream but for the root's object (`sectionPos_sim`): the rebuilt virtual root (`rootObj_rel`), the rerun's transactions (`rerunStep_sim`), with the writer's last resort for a root child that only the whole stream's root still points to: every slot for it is the same stream slot (`anySlot_sim`); a transaction's change on views whose roots differ only there (`exec_rootSwap`), and the writer's paths on structures that agree (`CutAgree.pathOf_eq`) |
| Bound | The cost of a part of the stream (`cost_split`, `cost_append_left`, `cost_ge_count`), the target's maximality (`sdTarget_max`), T3 after one transaction (`section_step`), for runs (`section_run`) and runs with restarts (`section_runRestarts`), and what startup reads and reruns (`reads_of_section`, `rerun_of_section`, `bounded_of_section`); bergdb item 007 |
| BoundTake | T3 for BergDB's take (bergdb 007-08): the target of a distance (`sdTarget_spec`); the take's loop never goes back and takes every transaction up to the target, whatever the pace (`takeLoop_ge`, `takeLoop_reaches`), so the take keeps up with its deadline's distance (`takePolicy_keepsUp`); one transaction of a policy that keeps up with a distance in it (`section_step_of`, `take_step`); folds of steps, each followed by a restart or not (`fold_length`, `fold_bound`, `fold_decrease`) |

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
  `r4Fast_sound`; `PredChain` and `mem_topClosure` are from review-13-claude's
  `R4Bridge.lean`, F1-008-13 in the f1 repository), and the exponential
  `topClosure` runs only when that test fails. On 2026-10-16 (001-02) the
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
`d5c56dd`, the checker found every transaction of 59 traces of Java runs (50
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
[001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), section 6). On the
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
([001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), 2.9, register
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
[011-11](../items/011-docs-archive/11-level2-alignment.md), M2):

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
[011-11](../items/011-docs-archive/11-level2-alignment.md), M7, M10, M11 and
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
[011-11](../items/011-docs-archive/11-level2-alignment.md), M8): two new
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
[011-11](../items/011-docs-archive/11-level2-alignment.md), section 13):
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
[011-11](../items/011-docs-archive/11-level2-alignment.md), section 13.3),
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
[011-11](../items/011-docs-archive/11-level2-alignment.md), section 13.4):

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
[001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), section 5, the
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
[001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), 5.10).

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E4): one new
statement in SIS/PhysTheorems.lean, T-READ (`TR_view`); nothing else.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E5;
[001-08](../items/001-lean-model-levels-3-4/08-level4-alignment.md), 5.13; register
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
[001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), register M17,
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
[001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), 2.8):

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
[001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), 2.9):

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
register M48 of [001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md),
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
[001-07](../items/001-lean-model-levels-3-4/07-level3-alignment.md), 2.9):

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
(`07b6375`). Changes to the trusted part: new definitions in SIS/Handle.lean,
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
