005-62. Lean: T9 and T12 over handles
=====================================

Status: open. Kind: fix. Created 2026-10-27.

Registered at Frans's request (2026-10-27, 006-09: "Lean: T9 and T12 over
handles"), to restate Level 3's reclaim theorems with eviction over the
model with handles, so that the Lean files of the design before handles
can be removed later. Written by Claude (Opus 5.5, Claude Code).


The issue
---------

Level 3's two reclaim theorems with eviction are stated over the runs of
the design before handles (`lean/SIS/Evict.lean`'s `runEvict`, and
Reclaim.lean's `runEvictCut`):

* T9 (`T9_readCut`, lean/SIS/ReclaimTheorems.lean): in a run with eviction,
  after a safe cut, a read in the running process at a time from the first
  available time on gives the same on the cut stream as on the whole
  stream, and gives P;
* T12 with eviction (`T12_evictCut`): the run with eviction that restarts
  from safe cut streams appends the records of the run without restarts.

Java has used handles since 009 (merged 2026-10-26), and the model with
handles (lean/SIS/Handle.lean, `runHandles`) has T-CACHE, T2-C, T-READ and
T-PIN (009-05, section 1) and rule 4 by position (005-58), but no reclaim
theorem. On 2026-10-26 Frans asked for the old Lean files to be removed;
none could go (009's log, 09:00), as T9 and T12 use all 42 Phys and Evict
modules. So the model has two models of eviction, and the trusted base
keeps the older one for these two theorems.


Why
---

One model of eviction, the one Java runs; a smaller trusted base later;
009's leftover.


Questions
---------

1. The statements: T9 and T12 over handles in the model's terms, with the
   same shape and assumptions as `T9_readCut` and `T12_evictCut` (section
   "The statements" below). Are they the right ones?
2. Rule 4 by position after a cut. Java's startup links D by position
   since 005-57 and leaves a pointer below the stream's first position as
   it is; the model's `handleStartupPos` has no cuts, and `RunPos_handles`
   is for runs without cuts. T12 below is stated with rule 4 by node id
   (`handleStartup`), as `T2_handles` is. Is a theorem that rule 4 by
   position gives the same after a cut wanted too (a `RunPos` for
   `runHandlesCut`)?
3. What can be removed once both are proved. Handle.lean imports
   Evict.lean: the startup with handles is built from Evict.lean's startup
   memory (`lazyStartup`, `sectionPos`, then `Mem.toH`), and the proofs
   over handles reuse E3 to E5's parts (39 of the 42 modules). So T9 and
   T12 over handles free `T9_readCut`, `T12_evictCut` and their proofs
   (CutPhys*, CutLater*), and the theorems of PhysTheorems.lean over
   `runEvict` with the proofs that only they use (EvictKeys, EvictPin,
   ...); removing Evict.lean itself would also need the startup with
   handles without Evict.lean's memory, a larger step. For Frans to
   decide.
4. The order: T9 first; its invariant (`CInvH` below) is also what T12's
   proof needs for the reads after a restart from a cut stream.


Done when
---------

`T9_handles` and `T12_handles` proved (`t9_handles`, `t12_handles`):
`lake build` clean, no `sorry`, only Lean's standard axioms (`#print
axioms`); lean/README.md's tables updated; the old files and their
theorems removed or kept, for Frans to decide (question 3).


First step
----------

State both in the model's terms, paired with plain English, in this entry
first; then the proof of T9, in a clone. (Done 2026-10-27; see "State".)


Size and order
--------------

L. T9 is about the size of CutPhys, CutPhysTrans and CutPhysRun (2,600
lines over Evict.lean); T12 about that of CutLater to CutLaterRun (8,100
lines). More than one session.


The statements
--------------

2026-10-27, by Claude (Opus 5.5, Claude Code), written before the proofs.
In a new trusted file, lean/SIS/HandleReclaimTheorems.lean (in the clone,
see "State"), as definitions of type `Prop`, like HandleTheorems.lean's,
so that nothing is assumed; the proofs go in new files of SIS/Proof/.

**The run with cuts.** As Reclaim.lean's `runEvictCut`, over handles:

    def runHandlesCut (sp : Spec V T) (al : Algo V T)
        (ts : List (T × Option Nat × List HCacheOp)) : DB V T × HMem V × Stream V T :=
      ts.foldl (fun (acc : DB V T × HMem V × Stream V T) p =>
        let r := handleTrans sp al acc.2.2 acc.1 acc.2.1 p.1
        match p.2.1 with
        | some c =>
          let S := cutStream c r.1.S
          (startup sp S, handleStartup sp S, S)
        | none => (r.1, p.2.2.foldl (HMem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
        (init sp, handleStartup sp (init sp).S, (init sp).S)

In words: the run with handles (`runHandles`), where each transaction is
the physical writer with handles (`handleTrans`), but a transaction marked
`some c` is followed by a crash and a restart from the stream cut at c:
the logical startup for ⟨P, D, S⟩, the startup with handles for the memory
(`handleStartup`), and the cut stream for Rule R. A transaction marked
`none` is followed by its reads and evictions (`HCacheOp`). The run's state
is the triple: the database ⟨P, D, S⟩, the memory, and the stream of the
last startup.

**1. T9 with handles.**

    def T9_handles (sp : Spec V T) (al : Algo V T) : Prop :=
      ∀ ts : List (T × Bool × List HCacheOp),
        RunOK sp al (ts.map (·.1)) → PhysRunOK sp al (ts.map (·.1)) →
        EvictRunOK sp al (ts.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
        ∀ j ≤ ts.length, ∀ c t,
          let db := run sp al ((ts.take j).map (·.1))
          let r := runHandles sp al (ts.take j)
          let m := r.2.1
          CutOK sp c db j → lastFa db.S ≤ t → t ≤ j →
          m.read sp r.2.2 (cutStream c db.S) t = m.read sp r.2.2 db.S t ∧
            (m.read sp r.2.2 (cutStream c db.S) t).2.map (·.1) = reachList sp db.P t ∧
            ∀ p ∈ (m.read sp r.2.2 (cutStream c db.S) t).2, view sp db.P t p.1 = some p.2

In words: take a run with handles of BergDB's algorithm (the still-dirty
test `javaTest`, step 3 by marking) that meets the model's assumptions
(`RunOK`, `PhysRunOK`, `EvictRunOK`, as for `T2_handles`), with any reads
and evictions between transactions and restarts after any transactions
(`runHandles`). After any transaction j and its operations or its restart,
let db be the run's state (the run without restarts, which T2-C says the
records and D are), and suppose a cut at c is safe in it (`CutOK`). Then a
read through the handles (`HMem.read`, with Rule R from the stream of the
last startup, `r.2.2`) at any time t from the first available time
(`lastFa db.S`) to j:

1. gives the same on the stream cut at c as on the whole stream: the same
   memory after the read (its loads and write-backs) and the same list of
   nodes; so it reads no record before the cut;
2. reaches exactly the nodes reachable at t;
3. gives each of them its node at t (P at t).

The cut is made while the process runs: the memory keeps the objects and
handles made before it. Parts 2 and 3 are `TR_handles_restarts`; part 1 is
new.

**2. T12 with eviction over handles.**

    def T12_handles (sp : Spec V T) (al : Algo V T) : Prop :=
      ∀ cs : List (T × Option Nat × List HCacheOp),
        RunOK sp al (cs.map (·.1)) → PhysRunOK sp al (cs.map (·.1)) →
        EvictRunOK sp al (cs.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
        ExecRootOK sp → VirtLiveOK sp → PolicyCutOK al →
        (∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
          CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1)))
            (run sp al ((cs.map (·.1)).take (j + 1))) (j + 1)) →
        (∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, HCacheOp.read t ∈ cs[j].2.2 →
          lastFa (run sp al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) →
        let db := (runHandlesCut sp al cs).1
        let r := run sp al (cs.map (·.1))
        db.S = cutStream (cutMax (cs.map (·.2.1))) r.S ∧ db.D = r.D ∧
          SameFrom sp (lastFa r.S) cs.length db.P r.P

In words: take a run as in T9, but whose restarts are from cut streams
(`runHandlesCut`), with T12's assumptions: with a virtual root, the
transactions see the root only through its live children (`ExecRootOK`)
and its live children are those of its last entry (`VirtLiveOK`); the
policies do not look at what a cut removes (`PolicyCutOK`); each cut is
safe at the largest cut so far, in the state of the run without restarts
at that point; and every read between transactions is at a time from the
first available time on (a read before it may need a record before the
cut). Then, after all of the run:

1. its stream, written by the physical writer with handles, is the stream
   of the run without restarts, cut at the largest cut (the records before
   it are stubs);
2. its D is that run's D;
3. its P gives the same lookups as that run's at every time from that
   run's first available time on (`SameFrom`).


The proof plan
--------------

By Claude, 2026-10-27, from reading CutPhys*, CutLater* and the proofs
over handles (009-05, section 1).

**T9.** As CutPhys, CutPhysTrans and CutPhysRun do for Evict.lean, with
the handle proofs' structure (HandleHist, HandleReadT, HandleHistTrans,
HandleRestart):

1. The invariant `CInvH` (T9's, over handles), for the state db and the
   stream S0 of the last startup:
   * mono: for a canonical object of a written node x not in D, with x's
     latest version v, its pointer for each pointee y that v names at
     record r0 holds a handle that holds a canonical object, or its slow
     path's reference (`HMem.slowRef`: the reference after Rule R, raised
     to the held handle's written position) is r0 or later;
   * root: with a virtual root, the root's object's pointer for a root
     child not in D gives, by the record rule, that child's latest version.

   CInv's other three parts are not needed with handles: a node has at
   most one object in memory, held by its live handle (`HTableOK`), every
   node of D has a canonical object (`HCanOK`), and every follow of a
   pointer to a node with a canonical object reaches it without a load.
   For a node current at the last time, `HSlotOK` already gives mono; the
   invariant matters for nodes that are no longer current.
2. What a read at t from f on needs: an object that can be read at t on a
   cut stream (canonical, or the snapshot of a version that `ReadsPhys`
   covers at t); a pointer whose pointee has a canonical object, or every
   version of the pointee at or after the slow path's reference is
   covered. A follow of such a pointer gives the same on the cut stream:
   only the load reads the stream, and it reads the version at the slow
   path's reference, which `CutOK`'s part 2 puts at c or later.
3. The read on the cut stream is the read on the whole stream (as
   `HEInv.readAtT_ok`, with `CInvH`).
4. `CInvH` is kept by reads (a follow writes back the slow path's
   reference, a fixed point of Rule R), by evictions (an evicted canonical
   object gives its handle its position, its node's latest version), by
   each transaction (the writer's view, walk, change and writes, and the
   next state: current nodes by `HSlotOK`, a node written now by the
   record rule, others as before), and given by the startup (every pointer
   names its pointee's latest version).
5. Runs with restarts (`HandleInvC`, as `EvictInvC`), and `t9_handles`.

**T12.** As CutLater to CutLaterRun, with C the run with handles that
restarts from cut streams (`runHandlesCut`) and E the run with handles that
restarts from the whole streams at the same points (`runHandles`) with C's
operations: an eviction with handles is local, so E needs no extra
unswizzles of its root's slots (CutLaterTrans's `augment`). E's states are
the run's by T2-C over handles (`t2_handles`); C is shown to have E's
records, so C's states are those of the logical run that restarts from cut
streams (as `evictCut_restartsCut`), and the logical T12 (`T12_restartCut`)
gives the rest. The pieces (revised 2026-10-27, 18:20, after T9):

1. The startup: the startup with handles from a cut stream is the one from
   the whole stream but for the virtual root's object. The startup with
   handles is `Mem.toH` and rule 4 on Evict.lean's startup memory before
   rule 4 (`(lazyStartup sp S).sectionPos S`), so CutLaterStart's
   `startup_sim` carries over if its relation holds before rule 4. To
   check: rule 4 with handles keeps a stream slot's reference where
   Evict.lean's rule 4 makes the slot a memory slot.
2. Memories that differ only in the root's object, whose live children
   agree from the first available time on (`RootRel`): reads from then
   on, the writer's walk, the change, the writes and evictions give related
   memories and the same results (CutLaterSim, CutLaterPerm over handles).
   A relation by lookups (`obj?`) may make CutLaterPerm unnecessary, since
   the operations with handles look objects up by address.
3. The loads. After a restart from the stream of state j1 with a safe cut
   at c, every load of E's reads from the first available time on, and of
   its writer, is at c or later, so C's loads from the cut stream are E's
   (CutLater and CutLaterRead's `NInv`, `Later`, `LaterOK`). The design
   risk is here. The readers' slow path takes the live handle's snapshot
   when it is at least as new as the pointer's reference, so a read may
   reach a snapshot that was loaded for another pointer at another time,
   newer than the version the pointer names, and not a version that
   `LaterOK` allows (`ReadsPhys` in the state of the last startup, or
   written after it). What should save it is the closure upward, as for
   T9: such a snapshot is good for t (lemma M), and its references for
   its live children at t are at least those of the older allowed version
   (lemma M again, `Inv.newer`; Rule R is monotone), whose children's
   versions `CutOK` (part 2, at j1) puts at c or later. So the invariant to
   carry: an object that a read at t reaches is canonical, or a snapshot
   at least as new as a version that `LaterOK` allows, and good for t; a
   pointer's slow path's reference is at least such a version.
4. One transaction of C and of E: the same record, memories related again;
   the run (`RunSim`) and `t12_handles`.

By running, the claim holds: `reclaimtest 20 30` checks C after every
transaction under five eviction schedules (State).


State
-----

2026-10-27, 19:40. By Claude (Opus 5.5, Claude Code).

**T9 and T12 over handles are both proved** (`t9_handles`, `t12_handles`),
in a clone; not yet in `main`.

Where. The clone `/Users/f/fl/bench/006-09/w12/` (a clone of bergdb at
`af67145`): 11 commits in Frans's name, lean/ only, each with `lake build`
clean and no `sorry`. They are also patches 0001 to 0011 in this entry's
directory ([62-lean-t9-t12-over-handles/](62-lean-t9-t12-over-handles/)).
`git am` applies them on `main` at `9fa1789` (tested in a scratch clone;
the result's lean/SIS is the clone's, and main's lean/ has not changed
since `af67145`). In all 16 files, +5,723 and −57 lines:

1. `03a4b0e`: T9 over handles. New trusted file
   lean/SIS/HandleReclaimTheorems.lean (87 lines): `runHandlesCut`,
   `T9_handles`, `T12_handles`, as in section "The statements"; no
   definition changed. Proofs: SIS/Proof/HandleCut.lean (the invariant
   `CInvH`, the follow and the read on a cut stream, reads and
   evictions), HandleCutTrans.lean (one transaction keeps `CInvH`),
   HandleCutRun.lean (the startup, runs with restarts, `t9_handles`);
   `heinv_hinvH_startup` (HandleRestart.lean) also gives the startup's
   pointer facts now.
2. `dc49b91`: by running (not trusted): SIS/HandleReclaimExample.lean,
   `checkHandleCut`, and `reclaimtest` runs it.
3. `df56709`: T12, the loads (plan, piece 3): SIS/Proof/HandleCutLater.lean
   (`CInvH.read_later`, `HEInv.reachPath_later`).
4. `4112e3e`: T12, the startup (piece 1): SIS/Proof/HandleCutStart.lean
   (`handleStartup_sim`: the startup with handles from a cut stream is the
   one from the whole stream but for the root's object, `HMem.withRoot`,
   `RootRelH`); from `sectionPos_sim`, now a lemma of its own in
   SIS/Proof/CutLaterStart.lean.
5. `a571932`, `ccf54fa`, `70777f3`, `9a17f01`, `0c67750`: T12, the
   simulation (piece 2), SIS/Proof/HandleCutSim.lean: on a memory with
   another root object and the cut streams, C's follow and read, the
   writer's walk, evictions, the change (`HMem.withRoot_applyChange`) and
   the writes (`HMem.withRoot_writeNodes`) give E's results on the whole
   streams, and memories that again differ only in the root's object.
6. `074017a`: T12, one transaction (piece 4):
   SIS/Proof/HandleCutTransSim.lean, `handleTrans_sim`.
7. `3a2d2e5`: T12, the cache operations and the run:
   SIS/Proof/HandleCutT12.lean (`ops_simH`; `RunSimH`, the two runs side
   by side; `handleCut_restartsCut`; `t12_handles` from the logical T12,
   `restartCut`). CutLaterRun.lean's `lastR` and `logOf` (and their
   lemmas) now take any kind of cache operation. lean/README.md: the
   tables, the axioms check, the log.

Sizes: T9's proofs 1,955 lines (HandleCut, HandleCutTrans, HandleCutRun);
T12's 3,364 (HandleCutLater 608, HandleCutStart 295, HandleCutSim 1,728,
HandleCutTransSim 331, HandleCutT12 402), against 8,100 for T12 over
Evict.lean.

Checks. `lake build`: "Build completed successfully (173 jobs)", no
warnings; no `sorry` anywhere in lean/SIS. `#print axioms SIS.t9_handles`
and `#print axioms SIS.t12_handles`: `[propext, Classical.choice,
Quot.sound]`; `T9_readCut` and `T12_evictCut` are still proved (same build).
`lake exe reclaimtest 20 30` (at `dc49b91`; no definition changed since):
all checks pass; with handles 3,000 transactions per policy, 12,000 in all,
0 fail; cuts up to 23, 125 with a node of D that no lookup from the first
available time on reaches
([reclaimtest-20-30.txt](62-lean-t9-t12-over-handles/reclaimtest-20-30.txt)).

How it went, against the plan:

* T9: `CInvH` has three parts, each "holds a canonical object, or its slow
  path's reference is at least ..." (`HMem.PtrAtLeast`): mono (as
  planned), and with a virtual root `rootD` (the root's pointer for a root
  child of D holds its canonical object) and `rootClean` (for any other
  root child, at least its latest version). The read's condition is
  closed upward (every version at or after the slow path's reference is
  one `ReadsPhys` covers), which covers the slow path's taking of a newer
  snapshot from the live handle.
* T12 needed less than over Evict.lean: no `NInv` (T9's `CInvH` is all the
  loads need; the plan's design risk did not happen), no extra unswizzles
  (an eviction with handles is local, so E runs C's cache operations as
  they are, `esH`), and no permutation of memories (`CutLaterPerm` has no
  counterpart): C's memory is E's with another root object, an equation.

Next step, for Frans:

1. Apply the 11 commits to `main` (`git am` of the patches), or ask for
   changes.
2. Question 3, what to remove. What the kept theorems still use, by
   declaration (2026-10-27, 19:25: a script over the built environment
   that follows the constants each theorem uses). Kept: the logical
   theorems, the ten over handles and the checker's fast paths. Dropped:
   `TC_records`, `TR_view`, `T2_cache`, `TR_view_restarts`, `TP_pins`,
   `T9_readCut`, `T12_evictCut` (each now has a counterpart over handles).
   * Eight proof files are then not used at all: EvictHistTrans,
     EvictPath, EvictPin, EvictRead, EvictReadT, EvictRun, CutLaterPerm,
     CutPhysRun (and the example files).
   * Most others over Evict.lean are used in part, for example (used of
     all declarations): Evict.lean 16 of 93, EvictApply 13 of 135,
     EvictKeys 61 of 164, EvictInit 49 of 92, EvictInv 50 of 99,
     EvictRerun 93 of 137, CutPhys 2 of 97, CutLater 9 of 74,
     CutLaterSim 62 of 191, CutLaterTrans 1 of 81, CutLaterStart 123 of
     195.
   * The trusted statements over handles use from Evict.lean only the
     assumptions (`EvictRunOK`, with `EvictStep`, `CopyStep`, `adoptAt`,
     `treeAt`) and `Mem.sectionPos` (in `handleStartup`); the proofs also
     `evictStartup` and `Mem.linkD`, through the startup's proofs.

   So, in steps: (a) drop the seven theorems and the eight unused files, a
   small step; (b) cut the partly used files down to what the proofs over
   handles use, or move that to shared files; (c) drop Evict.lean: move
   the assumptions, build the startup with handles without Evict.lean's
   memory, and redo `sectionPos_sim` and the startup facts over handles,
   the larger step. Frans to choose how far.
3. Question 2 (rule 4 by position after a cut) is still open.

Traps:

* The main tree's lean/.lake is older than lean/ (its Basic.olean of
  2026-10-17; Basic.lean changed 2026-10-26): a clone with a copy of it
  rebuilds everything. A .lake from a clone built today at the same lean/
  is up to date (006-09/w7's was).
* `heinv_hinvH_startup` has four parts now; its caller in
  HandleRestart.lean takes `.2.1`.
* The proofs over handles use lemmas from files of the design before
  handles: CutPhys (`foldl_eq_inv`, `Inv.ref_le_lv`), CutPhysTrans
  (`Inv.ref_pointees`, `VInv.top_of_pointee`, `Inv.parent_of_top`),
  CutLater and CutLaterRead (`VOK`, `Later`, `LaterOK`), CutLaterStart
  (`sectionPos_sim`, which the startup with handles rests on), CutLaterSim
  (`find?_congr_of_mem`), CutLaterRun (`lastR`, `logOf`, `st_fa_mono`).
  Before those files go, these move to shared files (step (b) above).
* The simulation's lemmas need E's invariants (`HEInv`) for structural
  facts, so each combines the cut and the root swap: C's operation on the
  cut streams is E's on the whole streams, root swapped. `lake env lean
  <file>` checks one file in about a second here.


Log
---

2026-10-27. Registered at Frans's request (006-09, W12); the statements
written; the proof of T9 started in a clone.
2026-10-27, 18:25. T9 over handles proved (`t9_handles`, clone commit
`03a4b0e`); reclaim with handles by running (`dc49b91`, `reclaimtest 20
30` passes); patches in the entry's directory; T12 over handles stated,
its plan revised (the loads, piece 3).
2026-10-27, 18:55. T12 over handles: the loads (`df56709`), the startup
(`4112e3e`), and the simulation's reads, walk and evictions (`a571932`,
`ccf54fa`, `70777f3`); the rest planned in "State".
2026-10-27, 19:40. T12 over handles proved: the change and the writes
(`9a17f01`, `0c67750`), one transaction (`074017a`), the cache operations
and the run (`3a2d2e5`, `t12_handles`); patches 0001 to 0011, which apply
on `main` at `9fa1789`; what the kept theorems still use of the old files
(State, next step 2).


Review, 2026-10-27
------------------

2026-10-27, 19:37, by Claude (Opus 5.5, Claude Code), at max effort: an
adversarial review of the 11 commits (`03a4b0e` to `3a2d2e5`) before they
go into `main`, from the code, not from the account above. In a clone of my
own, `/Users/f/fl/bench/006-09/w12r/`: `main` at `9fa1789` with the 11
patches applied by `git am`. My checks are in its `review/` folder (not
committed; run from lean/ with `lake env lean ../review/<file>`).

**1. Faithfulness.** `T9_handles` and `T12_handles` are `T9_readCut` and
`T12_evictCut` word for word, with the model before handles swapped for the
model with handles. `runHandlesCut` is `runEvictCut` line by line, with
`handleTrans` for `evictTrans`, `handleStartup` for `evictStartup` and
`HMem.cacheOp` for `Mem.cacheOp`. Every difference:

* The operations between transactions: `HCacheOp` (`read t`, or `evict n`,
  the eviction of handle n, which does nothing when `HMem.evictable`
  forbids it) instead of `CacheOp` (`read t`, `unswizzle h y`,
  `release h`). Each statement takes every list of its own model's
  operations, so neither is weaker; the one with handles is Java's eviction
  since 009.
* The read: `HMem.read` (through the handles) instead of `Mem.read4`, on
  the memory of `runHandles` instead of `runEvict`. The conclusion is the
  same: on the cut stream, the same memory after the read and the same
  nodes as on the whole stream; and P at t.
* The form: a definition of type `Prop` and a theorem for every spec and
  algorithm, `theorem t9_handles (sp : Spec V T) (al : Algo V T) :
  T9_handles sp al`, instead of a theorem with the hypotheses as arguments.
  It says the same; in T9, `∀ j ≤ ts.length, ∀ c t` takes the old
  arguments `j c`, `hjt` and `t` in another order.
* The hypotheses: the same, one by one (`RunOK`, `PhysRunOK`, `EvictRunOK`,
  `javaTest` and marking, as in `T2_handles`; for T12 also `ExecRootOK`,
  `VirtLiveOK`, `PolicyCutOK`, the cuts and the reads), but `HCacheOp.read`
  for `CacheOp.read`. None is added, none dropped.

None of these weakens the result. The statements in "The statements" above
are the file's, character for character but for spaces.

**2. Vacuity; restarts as Java does them.**

* The hypotheses speak of the logical run, the spec, the algorithm and the
  times of the reads, never of the memory, so they hold together wherever
  the old ones do. On reclaimtest's runs (example 4, `spec4` with a virtual
  root; 4 policies, 20 seeds, 30 transactions): `RunOK`, `PhysRunOK` and
  `EvictRunOK` hold by running in 80 of 80 runs, 74 of them with a
  cut above 0, up to 23 (review/Vac.lean); `PolicyCutOK` by running
  (reclaimtest's "assumptions 20/20"); `ExecRootOK spec4` and
  `VirtLiveOK spec4` are proved (ReclaimExample.lean); the cuts are the
  largest that `CutOK` allows, by running (`cutsFor`). On these runs
  `checkHandleCut` checks T12's conclusion, and T9's parts 2 and 3 on the
  cut stream, by running.
* No conclusion is trivially true. A load reads the stream it is given
  (`S.versionAt r` in `HMem.load`), and a cut leaves stubs before c: T9's
  part 1 says that no load of a read from the first available time on reads
  a record before the cut. In T12 the records come from the memory
  (`HMem.writeNodes`) and the change from the memory's view, so C's records
  equal E's only if its memory serves them.
* Restarts from cut streams. At the level of the model, `runHandlesCut`
  restarts as Java does: the stream after a restart is cut at the largest
  cut so far (Java's cut table keeps the cuts across restarts, and
  Reclaim's start applies them again, 005-63); both startups read only the
  cut stream; after the restart, Rule R and every load use the cut stream.
  005-61 is about when Reclaim cuts; the theorems hold for every safe cut,
  so it does not enter.
* Limit a, the entry's question 2: both startups link D by node id
  (`handleStartup`), Java by position since 005-57. For T9, whose restarts
  are from whole streams, `RunPos_handles` carries the theorem over to
  `runHandlesPos`. For T12 nothing does. By running, rule 4 by position
  gives the same pointers as rule 4 by node id at all 744 restarts of
  reclaimtest's runs, on the stream cut at the largest cut so far (442 of
  them with a cut above 0), and on the whole stream (review/Pos.lean). So a
  `RunPos` for `runHandlesCut` looks true.
* Limit b: in the model a cut reaches the writer only at a restart. Java
  cuts while it runs (Reclaim's iterations, started from
  `transactionCompleted`) and goes on writing with the running memory,
  whose loads then read the cut stream. T9 covers reads of the running
  memory on the cut stream, in any state where the cut is safe; no theorem
  covers the writer's transactions between a cut and the next restart. The
  same holds for the old theorems.

**3. CutLaterRun.lean.** A proof file (SIS/Proof/), not trusted. `lastR`
and `logOf` (and their lemmas `lastR_le`, `lastR_succ_none`,
`lastR_succ_some`, `cutMax_take_succ`, `runRestartsCut_succ`, `logOf_fst`,
`logOf_snd`) now take `List (T × Option Nat × C)` for any type `C`, where
`C` was `List CacheOp`. Every old use takes `C := List CacheOp` and gets
the same function and the same lemma. No trusted statement names either;
they are used only in CutLaterRun.lean and HandleCutT12.lean.
`T12_evictCut` still builds, with the same axioms. The two other changed
proof files: `sectionPos_sim` is split out of `startup_sim`
(CutLaterStart.lean), and `heinv_hinvH_startup` gives two more parts
(HandleRestart.lean). The diff touches no trusted file but the new one,
SIS.lean's imports and the README.

**4. Soundness.**

* None of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `unsafe`, `extern`, `partial` and `opaque` anywhere in lean/ (SIS/,
  Check/ and the top files), not only in the new code.
* `lake build` from scratch (a fresh clone, no .lake): "Build completed
  successfully (173 jobs)", no warnings, 58 s.
* `#print axioms` (review/Axioms.lean) for `t9_handles`, `t12_handles`,
  `T9_readCut`, `T12_evictCut`, `T12_restartCut`, `T8_recoverCut`,
  `TR_view_restarts`, `T2_cache` and the README's handle theorems
  (`tc_handles`, `tr_handles`, `t2_handles`, `tr_handles_restarts`,
  `tp_handles`, `rule4_positions`, `rule4Pos_handles`, `runPos_handles`):
  each `[propext, Classical.choice, Quot.sound]`. The same file checks
  `example : T9_handles sp al := t9_handles sp al`, and likewise for T12.
* `sh test-traces/run.sh`: "TRACE TESTS OK".
* `lake exe reclaimtest 20 30` at the final commit: "all checks pass", with
  handles 3,000 transactions per policy, 0 fail; the output is the agent's
  ([reclaimtest-20-30.txt](62-lean-t9-t12-over-handles/reclaimtest-20-30.txt))
  but for the time.

**5. The patches.** The 11 patches apply with `git am` on `main` at
`9fa1789`; the result's lean/ tree is `14b995f`, the same as `3a2d2e5`'s.
They touch 16 files, all in lean/; the author is Frans Lundberg, with no AI
attribution.

**Changes made.** None: no new commits, the patches stand.

**Verdict.** Commit the 11 patches to `main` as they are.

**For Frans.**

1. Question 2: a `RunPos` for `runHandlesCut` (rule 4 by position after a
   cut, Java's since 005-57)? By running it holds (limit a).
2. Limit b: a run where a cut does not restart, as Reclaim cuts while the
   database runs, with T12's conclusion for it? The theorems before handles
   lacked it too.
3. Question 3, what to remove, as in "State".


In main, 2026-10-27, 19:39: the 11 commits, after the review, as
`bba91dd` to `a506b34` (the same lean/ tree as `3a2d2e5`), by the 006-09
session; the patch files 0001 to 0011 were then removed from this
directory, as the commits hold them. Left for Frans: questions 2 to 4 of
the State (the statements, how far to remove the old design, a `RunPos`
for `runHandlesCut`) and the review's two (rule 4 by position after a cut;
a cut without a restart).
