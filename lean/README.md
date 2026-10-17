Self-indexed streams in Lean
============================

Started 2026-10-12. Written by Claude for Frans Lundberg.

The model of [../docs/sis-model.md](../docs/sis-model.md) in Lean 4:
the definitions, the assumptions, and the theorems T1 (recovery) and T2
(restart invariance), with their proofs. See Status.

Reviewed 2026-10-13 at the `ebe5f77` documentation cutoff. Lean source is
unchanged from the earlier build, randomized and axiom checks. These are proofs
of the abstract model with the exact still-dirty test, not of Java, reclaim,
eviction, concurrency, serialization, torn bytes or resource bounds.
Java's conservative tracking and reference-resolution obligations are in
[levels.md](../docs/levels.md).


Build and run
=============

Needs elan (`brew install elan-init`). The toolchain version is in
`lean-toolchain`; elan downloads it on first use. No Mathlib.

    cd lean
    lake build              # checks every file, runs the #guard tests
    lake exe sistest 20 40  # random runs: 20 seeds, 40 transactions each (7 min)
    lake exe phystest 20 40 # the physical layer on random runs (9 min)
    lake exe phystest 20 40 evict  # its eviction part only (2.5 min)
    lake exe reclaimtest 20 30     # reclaim: random runs with cuts (1 min)

`lake build` checks every proof. To see that a theorem depends on nothing but
Lean's standard axioms (no `sorry`), put this in a file, for example
`Axioms.lean`, and run `lake env lean Axioms.lean`:

    import SIS.Theorems
    import SIS.PhysTheorems
    import SIS.ReclaimTheorems
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
    #print axioms SIS.TC_records
    #print axioms SIS.TR_view
    #print axioms SIS.T2_cache
    #print axioms SIS.TR_view_restarts
    #print axioms SIS.TP_pins
    #print axioms SIS.T13_markTouch
    #print axioms SIS.T8_recoverCut
    #print axioms SIS.T9_readCut
    #print axioms SIS.T12_restartCut
    #print axioms SIS.T12_evictCut

Each prints `[propext, Classical.choice, Quot.sound]`, or a part of it
(`LM_cutTo` needs no `Classical.choice`). The equalities of
the checker's fast paths (Check/Fast.lean, Check/R4.lean) are checked the
same way:

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
| SIS/Phys.lean | The physical layer, what Java holds in memory (bergdb item 001, WPs L1 and L3): objects (`Obj`), their slots (`Slot`), the memory with the node table (`Mem`); Java's first touch (`Mem.follow`: Rule R, the table, the version read, cut back in the section); reads (`Mem.read`); the lazy startup (`lazyStartup`); a version cut back to a time (`Version.cutTo`); the operations after startup (`Op`, `Mem.step`, admissible: `OpsOK`); the assumptions of the physical layer (`PhysStep`, `PhysRunOK`); the writer after a lazy startup (WP L4: its view through the physical layer, `Mem.view`; its transaction, `lazyTrans`, with the record of `stepWith`, `step` with its change given) and a run with lazy restarts (`runLazy`); the writer's paths reach the touched nodes too (`pathOf`, WP R3) | — (docs/level2-alignment.md, 13) |
| SIS/Evict.lean | The physical layer, part 2, with eviction (bergdb item 001, WP E2; docs/level4-alignment.md, section 5): the pinned objects (`Mem.pinned`), unswizzling (`Mem.unswizzle`) and release (`Mem.release`); the Level 4 loader (`Mem.follow4`: the canonical object, or exactly the version a slot names after Rule R) and reads through it (`Mem.read4`); the writer's path (`Mem.reachOnPath4`) and the change (`Mem.applyChange4`, `Mem.newSlot4`); startup with rule 4 (`evictStartup`, `Mem.linkD`); the physical writer (`Mem.refOf`, `Mem.writeNode`) and its transaction (`evictTrans`); cache schedules (`CacheOp`) and runs (`runEvict`); the assumptions of stage 2 (`EvictStep`: TREE, `treeAt`, and A6', `adoptAt`; A-COPY, `CopyStep`; `EvictRunOK`) | — (docs/level4-alignment.md, 5) |
| SIS/PhysTheorems.lean | Lemma M: a newer version of a node serves every time an older one serves (`LM_newer`), so Rule R's version does (`LM_ruleR`), and a version cut back to s serves the times up to s (`LM_cutTo`); T1-L (`T1_lazy`): after the lazy startup from the stream of a run, or of a prefix of it (a crash), and any reads and writer follows, a read at any time up to the last record gives P at that time; CC (`CC_canonical`): in a run with lazy restarts, every canonical object holds its node's whole history; T2-L (`T2_lazy`): such a run appends the records of the run without restarts; `step_eq_stepWith`; stage 2 (bergdb item 001, WP E3): D closed upward (`T15_closed`), and T-CACHE (`TC_records`): in a run with eviction and any cache schedule, without restarts, every transaction of the physical writer appends the model's record and leaves the model's D, and INV-CAN, INV-SNAP and INV-SLOT hold; T-READ (`TR_view`, WP E4): in such a run, a read through the Level 4 loader at any time up to the last record gives P at that time; T2-C (`T2_cache`, WP E5): with restarts too, the records and D stay the model's, and the invariants hold for the stream of the last startup; and T-READ with restarts (`TR_view_restarts`, WP E5); T-PIN (`TP_pins`, WP E6): in such runs, every object outside the pinned set may be evicted | 5.1, 9; ../docs/level4-alignment.md, 5.3 to 5.6 |
| SIS/Reclaim.lean | Level 3, reclaim (bergdb item 001, WP R3): what a cut leaves of a version (`Version.stub`) and of a record (`Record.cut`); the stream after a cut (`cutStream`); the versions that a lookup at a time may read (`ReadsAt`, WP R7); when a cut is safe (`CutOK`); the same lookups from f on (`SameFrom`); policies that a cut does not change (`PolicyCutOK`); a virtual root seen only through its live children (`ExecRootOK`), whose live children are those of its last entry (`VirtLiveOK`, WP R4); runs that restart from cut streams (`runRestartsCut`, `cutMax`; with eviction, `runEvictCut`) | — (../docs/level3-alignment.md, 5) |
| SIS/ReclaimTheorems.lean | T13' (`T13_markTouch`, WP R3): with touches, step 3 gives exactly the index nodes not in D (and not a virtual root) that are dirty or touched; T8 (`T8_recoverCut`, WP R4): after a safe cut, startup from the cut stream gives the same lookups at every time from the first available time on (`SameFrom`), and the same D; T9 (`T9_readCut`, WP R4): in a run with eviction as in T2-C, after a safe cut, a read through the Level 4 loader in the running process at any time from the first available time on gives the same on the cut stream as on the whole stream, and gives P; T12 (`T12_restartCut`, WP R5): a run that restarts from safe cut streams appends the records of the run without restarts (its stream is that run's, cut at the largest cut), with that run's D and lookups from the first available time on; T12 with eviction (`T12_evictCut`, WP R5): so does the run with eviction (`runEvictCut`), with any cache schedules whose reads are from the first available time on and the Level 4 startup at each restart | — (../docs/level3-alignment.md, 2.2, 2.9, 2.10) |

The proofs, in SIS/Proof/ (not needed for reading the statements):

| File | Contents |
|---|---|
| Basic, Reach | Histories, nodes, reachability as an inductive definition, growing structures |
| StreamLemmas, Write | Latest versions, `good` and `dirty`, stability (`good_mono`), writing versions |
| Run | The parts of a transaction, runs, and the invariant `Inv` (INV-1 to INV-4 and the facts about S and P) |
| Init, Util, StepFacts, StepP, StepS, StepD, StepInv | The invariant holds after T(0) and after every transaction (`inv_st`) |
| Mark | Marking the access path of the change finds exactly the dirty index nodes not in D (`step_marked_iff`, T13) |
| StepFacts, Fresh, VStep, EvictLogic (the touch) | WP R3: what step 3 gives with touches (`mem_touchOf`, `step_gd3_mem`, `step_gd3_of_touch`); the nodes reachable before the change with a touched node below them are touched, so a clean node's live children stay out of D (`step_cleanFresh`) and D stays closed upward (`step_touch_D1`, with A6' also before the change); a root child that a root child points to is not reachable (`VInv.deadTops`), so it is never touched |
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
| EvictLogic | Stage 2 (WP E3): the logical facts that the design rests on (`EvLogic`): D is closed upward, and a current clean node has no pointee in D and names the latest versions of its pointees (`evLogic_st`); D closed upward alone needs no A6' (`DClosed`, `step_closed`; WP R5) |
| EvictWrite, EvictWrites | The physical writer's loop writes the model's versions (`writeNodes_eq`), and its two loops write the model's record (`AInv.loops_vs`) |
| EvictInv | The invariant with eviction (`EInv`): INV-CAN, INV-SNAP, INV-SLOT made precise (`SlotInv`), and the live slots of current canonical objects (`LiveInv`); unswizzle and release keep it (`EInv.unswizzle`, `EInv.release`) |
| EvictFollow, EvictPromote, EvictRead | The Level 4 loader keeps it, so reads and cache schedules do (`EInv.cacheOps`); the writer's follow and promotion (`EInv.follow4_writer`); a read at the last time gives P, the writer's view (`EInv.view4_ok`) |
| EvictPath, EvictApply, EvictApplyInv | The writer's paths (`EInv.reachPath4_ok`); the change applied, with TREE's one current parent (`treeAt_unique`) and A-COPY (`EInv.applyChange4_ok`) |
| EvictStepInv, EvictTrans, EvictRun, EvictInit | The memory after the record has the next state's invariant (`AInv.final_ok`); one transaction (`EInv.evictTrans_ok`); runs (`TC_run`); the startup from R(0) (`einv_init`); the invariant in the terms of `TC_records` (`EInv.tc_facts`) |
| EvictHist, EvictHistTrans, EvictReadT | Stage 2 (WP E4): the invariant for reads at earlier times (`HInv`: every slot of a canonical object for a live child at a time t names an object or a version good for t, or, by INV-SLOT's second half, a node of D), kept by the cache operations and every transaction (`HInv.evictTrans_ok`) and in every run (`HInv.run`); a read at any time up to the last record gives P (`EInv.read4T_ok`) |
| EvictKeys, EvictPin | Stage 2 (WP E6): no object has two slots for the same pointee, in every memory of every run (`SlotsND`, `slotsND_runEvict`); unswizzling every memory slot to an object, then releasing it, removes it (`Mem.evict_ok`); an object outside the pinned set has been written (`EInv.detachable_of_unpinned`) |
| EvictRerun, EvictRestart | Stage 2 (WP E5): the startup from the stream after T(k): its rerun keeps `RInv` (every object canonical, every stream slot naming its pointee's latest version after Rule R, a slot for each pointee; `rinv_lazyStartup`), and after the positions and rule 4 the memory has the invariant and the invariant for reads at earlier times (`einv_hinv_startup`; with what T9's invariant needs, `einv_hinv_startup_facts`); the physical writer depends on P only through its nodes (`evictTrans_congr`); runs with restarts (`EvictInvR`, `evictInvR_all`) |
| CutStream, CutRead | Stage 3 (WP R4): the stream after a cut (its records, `versionAt`, `newest`, the last record); a pointer followed, or a read from a version, on a stream cut at or before the startup pos gives what it gives on the whole stream if it reads no record before the cut (`follow_cut`, `readFrom_cut`); a read from a version that a lookup may read reaches only such versions (`readFrom_readsAt`); a version a lookup may read, a physical read may follow (`ReadsAt.phys`, WP R6) |
| CutAgree, CutRerun | Structures that agree for lookups from f on (`CutAgree`); a transaction's change is the same on both (`exec_cutAgree`, with `ExecRootOK`), and so is the rerun of the startup section (`rerun_cutAgree`, with `VirtLiveOK`), which keeps every node it starts with the run's (`rerun_cutAgree_nodes`, WP R5) |
| CutBase, CutTops, CutStart | Startup's reads of a stream cut safely at the times from f to s: without a virtual root, the whole stream's (`Inv.readAt_cut_nv`); with one, the whole stream's but for the root's version, which startup rebuilds from the root children it can read: the root children live from f on are read at their latest versions (`Inv.topsRead_cut_all`), so the rebuilt root has the root's live children from f on (`Inv.cutRoot_live`, `Inv.readAt_cut_v`) |
| CutRecover | P up to s, read from the cut stream, agrees with P after T(s) for lookups from f to s (`base_cutAgree`); T8 (`recoverCut`) |
| CutRestart | WP R5: a cut of a cut (`cutStream_cutStream`); a state related to the run's (`CutRel`: the run's stream cut at m, its D, its nodes for the lookups from f on and for D), on which a transaction appends the run's record and keeps the relation (`step_congr_cut`) |
| CutHist | WP R5: the nodes of D that no lookup from f on may reach (M33, M34): every node of D was reachable at a time at which its ancestors (it included) are in D, each with an entry from just after that time or a version in the record of its entry, put back by Rule A (`DAnchor`, `dAnchor_st`: Rule A with BergDB's test along the path, `step_anc_persist`, and D closed upward, `dClosed_st`); with a virtual root, every root child created after a root child of D is in D (`TopsD`, `topsD_st`) |
| CutHistRead | WP R5: after a safe cut, startup reads such a node at that time through its ancestors' versions in the startup section (Rule R), at its newest version, from the cut stream as from the whole stream (`Inv.baseCut_get?_hist`; with a virtual root, the root children from its root child then on are read, `Inv.topsRead_cut_from`); T8 with D's nodes (`recoverCut_dNodes`) |
| CutRuns | WP R5: the relation after every prefix of a run with restarts from cut streams (`restartCut_rel`), and T12 (`restartCut`) |
| CutPhys, CutPhysTrans, CutPhysRun | WP R4, T9: the invariant on the slots (`CInv`: a canonical object of a clean node names, for each pointee, a canonical object or a record at or after the one its node's latest version names; one of a node of D names a pointee of D by a snapshot only of the pointee's latest version; a virtual root's object names its root children of D by their canonical objects and the others at their latest versions; no snapshot of a version that Rule A put back and that is still in D); with it a read at a time from f on follows only canonical objects and versions that `ReadsPhys` covers, so it gives the same on a stream cut safely (`CInv.read4_cut`); the cache operations, the writer's walk and change, and the writes keep it (`CInv.evictTrans_ok`); the startup gives it (`cinv_startup`); runs with restarts (`EvictInvC`, `evictInvC_all`), and T9 (`readCut`) |
| CutLater, CutLaterRead | WP R5, T12 with eviction: the invariant on the slots after a restart (`NInv`: every slot of a canonical object names a canonical object, or a record that is its pointee's latest version in the stream of the last startup, or one written after it; a snapshot's slot may also name what its version's reference names after Rule R), which the startup gives (`ninv_startup`) and the cache operations and transactions keep (`NInv.evictTrans_ok`, `evictInvN_all`); in a state later than one where a cut at c is safe (`Later`), a read from f on and the writer's walk then follow only versions that `ReadsPhys` covers in that state or written after it, so they give the same on the streams cut at c (`NInv.read4_later`, `NInv.reachPath4_later`) |
| CutLaterSim | WP R5: a memory with another object for the root (`Mem.withRoot`); two root objects that agree from f on (`RootRel`: the same live children from f on, and the same slots for the pointees of the cut run's root); the Level 4 loader, the writer's walk, its change and its writes on such memories (`read4_withRoot`, `reachPath4_withRoot`, `applyChange4_withRoot`, `writeNodes_withRoot`); the writer's paths on structures that agree (`CutAgree.pathOf_eq`) |
| CutLaterPerm | WP R5: memories that are the same but for where the root's entry is in the list of objects (`RootPerm`), which every operation keeps (`RootPerm.applyChange4`: the one search over the list finds the root's object only when it is the only source, `RootOnly`) |
| CutLaterTrans | WP R5: one transaction of C, after a restart from a cut stream, and of E, after the restart from the whole stream at the same point: the same record, and memories related again (`SimC`, `evictTrans_sim`); a batch of C's cache operations and E's with extra unswizzles of its root's slots before each release (`augment`, `ExtraOK`, `ops_sim`) |
| CutLaterStart | WP R5: the Level 4 startup from a stream cut safely is the one from the whole stream but for the root's object (`startup_sim`): the rebuilt virtual root (`rootObj_rel`), the rerun's transactions (`rerunStep_sim`), with the writer's last resort for a root child that only the whole stream's root still points to: every slot for it is the same stream slot (`anySlot_sim`) |
| CutLaterRun | WP R5: the run with eviction that restarts from cut streams (C) has the states of the run without eviction that restarts from cut streams (`evictCut_restartsCut`), through the run with eviction that restarts from the whole streams at the same points (E) with the schedule `esOf`; T12 with eviction (`restartCut_evict`) |

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
  frozen run (`frozenB`).
* SIS/EvictExample.lean (bergdb item 001, WP E2): the physical layer with
  eviction by running. The invariants of docs/level4-alignment.md, 5.3
  (`invCanB`, `invSnapB`, `invSlotB`, `noDanglingB`); cache schedules
  (`schedule`: none, every object that may be detached, each with
  probability 0.3, unswizzles and releases apart); runs with restarts and a
  schedule, checked after every transaction (`checkEvict`: the records and D
  are the model's, reads give P, the invariants hold); TREE, A6' and A-COPY by
  running (`treeB`, `adoptB`, `copyB`, `evictRunOKB`); example 5 (example 3
  with drops). `lake exe phystest 20 40 evict` runs `checkEvict` on examples
  2, 3 and 5 with every schedule.
* SIS/ReclaimExample.lean and ReclaimTest.lean (bergdb item 001, WP R3):
  reclaim by running. Example 4, F1-008-07's reclaim example adapted to
  BergDB: example 3's virtual root and top nodes, one value per leaf, reclaim
  steps that touch the nodes their range traversal visits (without entries)
  and rewrite the values stored before pCut, the first available time at the
  end of an iteration once the startup pos has passed it. `CutOK` by running
  (`cutOKB`; WP R7's, with part 2 over `ReadsAt`, `cutOKAtB`), the largest
  safe cut (`safeCut`), T8 by running (`checkT8`),
  `PolicyCutOK` by running (`policyCutB`), runs with restarts from cut
  streams (`checkCut`), and with eviction and the four cache schedules
  (`checkEvictCut`: the records, D, reads from f on, also on the cut stream
  from the running memory, the invariants, the restarts). `#guard` checks on
  a fixed run: the touch makes clean nodes dirty, and without it no cut is
  safe; T8 and T12 at the safe cut, logical and with eviction, and T12's
  assumption on the cuts (WP R5); the pSafe wait
  (`pSafeWitness`); a stale reference that WP R3's `CutOK` let through, after
  which a physical read from the cut stream fails (`staleWitness`, WP R7); a
  read in the running process, with eviction, that follows a pointer of a
  replaced node to a version before a cut that WP R7's `CutOK` allows
  (`cutReadWitness`, WP R4; `CutOK` since WP R6 does not); Java's scheme,
  and a stale chain of put-back versions that only the exception of
  `ReadsPhys` for them lets through (`schemeWitness`, WP R6); T-SCHEME by
  running (`checkSchemeB`, WP R6: for every iteration whose scheme conditions
  hold, `CutOK` at its cut position in every later state past the waits; a
  `#guard` on the fixed run). Proved there (WP
  R4): example 4 meets T8's
  assumptions on the virtual root (`execRootOK_spec4`, `virtLiveOK_spec4`;
  also `virtLiveOK_spec4e`).
  `lake exe reclaimtest 20 30`: the same on random runs,
  for four startup pos policies; `lake exe reclaimtest 100 100 scheme`:
  T-SCHEME only, on larger runs (9 minutes).
* Check/ and TraceCheck.lean: the trace checker, `lake exe tracecheck`. It
  checks traces of Java runs against the model's definitions
  ([../docs/level2-alignment.md](../docs/level2-alignment.md), sections 8.5
  and 9). `sh test-traces/run.sh` runs its tests. Since bergdb item 001's L5
  it reads trace format 2 and checks C-L, every first touch after a restart
  against the rule of SIS/Phys.lean (`firstFailures`), and in C-S the top
  nodes' skip slots: their layout and cached times (`topFailures`; section
  13.5 there). Its diagnostics also count A6, TREE (item 001, A4) and A-COPY
  (`copyFailures`, item 001, E2 and E3: the assumption of stage 2 on the
  pointers of new entries). Since item 001's R7 it reads reclaim's lines
  (TOUCH, FA, CUT, PHYSCUT): C-A checks TouchOK (`touchFailures`), C-S
  compares fa(i) and, from the first cut on, runs the model's step on the
  stream cut at the largest cut so far, and C-CUT checks `CutOK` at every CUT
  line and that every physical cut is at or below the decided one
  (`cutFailures`; [../docs/level3-alignment.md](../docs/level3-alignment.md),
  section 6). Since R4, a diagnostic that does not fail a trace, C-CUT+: at
  every CUT line, whether a physical read in the running process from f on
  may follow a version before the cut (`readsBelowPhys`: through a pointer to
  a live child, every version of the child at or after the one the pointer
  names; register M48 of level3-alignment.md). Since R6, part of C-CUT,
  as `CutOK`'s part 2 is (`ReadsPhys`, with its exception for the versions
  of D that Rule A put back; test trace `physcut.trace`, where only that part
  fails). Since R8's change 3, the
  diagnostic C-L4: the FIRST lines against the Level 4 loader
  (`loader4Failures`: no snapshot from the node table; section 13.5 of
  level2-alignment.md).
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
  `topClosure` runs only when that test fails. The medium set took 6,770 s and
  takes 88 s; a trace of 5,000 transactions at node size 30 with 1,000 keys
  takes 428 s and 128 MB.

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
the model (../docs/level2-alignment.md, 10.5).

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
[../docs/level3-alignment.md](../docs/level3-alignment.md), section 6). On the
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
([../docs/level3-alignment.md](../docs/level3-alignment.md), 2.9, register
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
[../docs/level2-alignment.md](../docs/level2-alignment.md), M2):

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
[../docs/level2-alignment.md](../docs/level2-alignment.md), M7, M10, M11 and
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
[../docs/level2-alignment.md](../docs/level2-alignment.md), M8): two new
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
[../docs/level2-alignment.md](../docs/level2-alignment.md), section 13):
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
level2-alignment.md.

Changes to the trusted part on 2026-10-16 (bergdb item 001, WP L3;
[../docs/level2-alignment.md](../docs/level2-alignment.md), section 13.3),
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
[../docs/level2-alignment.md](../docs/level2-alignment.md), section 13.4):

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
[../docs/level4-alignment.md](../docs/level4-alignment.md), section 5, the
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
[../docs/level4-alignment.md](../docs/level4-alignment.md), 5.10).

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E4): one new
statement in SIS/PhysTheorems.lean, T-READ (`TR_view`); nothing else.

Changes to the trusted part on 2026-10-17 (bergdb item 001, WP E5;
[../docs/level4-alignment.md](../docs/level4-alignment.md), 5.13; register
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
[../docs/level3-alignment.md](../docs/level3-alignment.md), register M17,
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
[../docs/level3-alignment.md](../docs/level3-alignment.md), 2.8):

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
[../docs/level3-alignment.md](../docs/level3-alignment.md), 2.9):

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
register M48 of [../docs/level3-alignment.md](../docs/level3-alignment.md),
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
[../docs/level3-alignment.md](../docs/level3-alignment.md), 2.9):

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

Stage 1 of bergdb item 001 is done (2026-10-16): lemma M (`LM_newer`, L2),
T1-L (`T1_lazy`, L3), CC and T2-L (`CC_canonical`, `T2_lazy`, L4) are proved,
and Java's first touches after restarts are checked against the model's rule
(C-L, L5). Stage 2: T-CACHE (`TC_records`, E3) and T-READ (`TR_view`, E4)
are proved for runs without restarts, and T2-C (`T2_cache`, E5), T-CACHE
with restarts, T-READ with restarts (`TR_view_restarts`, E5) and T-PIN
(`TP_pins`, E6) (2026-10-17). Stage 3: the definitions and T13' (R3), the
checker on Java's reclaim traces with the red list (R7), T8 (R4),
`CutOK`'s part 2 over `ReadsPhys` (R6, part 1: register M48, option (a),
Frans), T12 for runs without eviction (R5), T9 (R4), and T12 with eviction
(R5) (2026-10-17).

Not done:

* A check of the physical layer's assumptions (`PhysStep`, M47) on Java
  traces; they are argued (level2-alignment.md, 13.3).
* The bounds (T3, T4).
* Reclaim's theorems: T-SCHEME (R6), that Java's scheme gives safe cuts:
  checked, not proved (the plan's fallback; level3-alignment.md, section 5):
  by running on example 4 (`reclaimtest`, `checkSchemeB`), and at every cut
  of Java's reclaim traces (C-CUT).
