/-
Self-indexed streams in Lean: Level 3's reclaim theorems with eviction over
handles: T9 (`T9_handles`) and T12 with eviction (`T12_handles`) of bergdb item
001 (WPs R4 and R5; 001-07, 2.9 and 2.10), stated over the run with handles of
SIS/Handle.lean (`runHandles`, and `runHandlesCut` below) since bergdb 005-62,
and before over Evict.lean's runs (ReclaimTheorems.lean's `T9_readCut` and
`T12_evictCut`). Trusted part: the run with cuts and the statements, as
definitions of type `Prop`, not as theorems, so that nothing here is assumed or
left unproved. The proofs are in SIS/Proof/.

Assumptions as in ReclaimTheorems.lean: BergDB's bookkeeping (`javaTest`,
marking), the Level 2 assumptions (`RunOK`), those of the physical layer
(`PhysRunOK`) and of stage 2 (`EvictRunOK`), and for T12 those of the logical
T12 (`ExecRootOK`, `VirtLiveOK`, `PolicyCutOK`).

And rule 4 by position after a cut (bergdb 005-62, question 2; Java's since
bergdb 005-57): `Rule4PosCut_handles` (the startup from a stream cut safely, with
Java's skip of the pointers below the stream's first position,
`handleStartupPosFrom`, is the startup with rule 4 by node id) and
`RunPosCut_handles` (so the run with it, `runHandlesCutPos`, is `runHandlesCut`,
and `T12_handles` holds for it as it is).
-/
import SIS.HandleTheorems
import SIS.Reclaim

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A run with handles, restarts and cuts (bergdb item 001, WP R5): as
`runHandles`, but a transaction marked some c is followed by a restart from the
stream cut at c: the logical startup, the startup with handles (`handleStartup`)
for the memory, and the cut stream for Rule R. A transaction marked none is
followed by its reads and evictions. -/
def runHandlesCut (sp : Spec V T) (al : Algo V T) (ts : List (T × Option Nat × List HCacheOp)) :
    DB V T × HMem V × Stream V T :=
  ts.foldl (fun (acc : DB V T × HMem V × Stream V T) p =>
    let r := handleTrans sp al acc.2.2 acc.1 acc.2.1 p.1
    match p.2.1 with
    | some c =>
      let S := cutStream c r.1.S
      (startup sp S, handleStartup sp S, S)
    | none => (r.1, p.2.2.foldl (HMem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
    (init sp, handleStartup sp (init sp).S, (init sp).S)

/-- T9 with handles (bergdb item 001, WP R4). In a run with handles as in
`T2_handles` (any reads and evictions between transactions, restarts after any
transactions), after any transaction j and its operations or its restart, with
a safe cut (`CutOK`) at c in the run's state: a read through the handles
(`HMem.read`, with Rule R from the stream of the last startup) at any time t
from the first available time f to the last record gives the same on the stream
cut at c as on the whole stream (the same memory after it and the same nodes),
so it reads no record before the cut; and it gives P at t
(`TR_handles_restarts`): exactly the nodes reachable at t, each with its node
at t. The cut is made while the process runs: the memory keeps the objects and
the handles made before it. -/
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

/-- T12 with eviction over handles (bergdb item 001, WP R5). For the run
with handles that restarts from safe cut streams (`runHandlesCut`), with the
assumptions of `T2_handles` and of T12: any reads and evictions between
transactions, the reads at times from the first available time on (a read
before it may need a record before the cut), and restarts from safe cut streams
with the startup with handles. The run appends the records of the run without
restarts: its stream is that run's, cut at the largest cut; its D is the run's,
and so are its lookups from the run's first available time on. The records are
those of the physical writer with handles (`handleTrans`). -/
def T12_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ cs : List (T × Option Nat × List HCacheOp),
    RunOK sp al (cs.map (·.1)) → PhysRunOK sp al (cs.map (·.1)) →
    EvictRunOK sp al (cs.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    ExecRootOK sp → VirtLiveOK sp → PolicyCutOK al →
    (∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1)) →
    (∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, HCacheOp.read t ∈ cs[j].2.2 →
      lastFa (run sp al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) →
    let db := (runHandlesCut sp al cs).1
    let r := run sp al (cs.map (·.1))
    db.S = cutStream (cutMax (cs.map (·.2.1))) r.S ∧ db.D = r.D ∧
      SameFrom sp (lastFa r.S) cs.length db.P r.P

/-! ## Rule 4 by position after a cut (bergdb 005-62) -/

/-- A run with handles, restarts and cuts, with rule 4 by position (bergdb 005-62;
Java's since bergdb 005-57): `runHandlesCut` with `handleStartupPosFrom` in place of
`handleStartup`, at R(0) with the stream's first position 0, and at a restart
marked some c from the stream cut at c with the first position c (Java's first
position is at or below the largest cut: `Rule4PosCut_handles` holds for every
first position up to the cut). Nothing else changed. -/
def runHandlesCutPos (sp : Spec V T) (al : Algo V T) (ts : List (T × Option Nat × List HCacheOp)) :
    DB V T × HMem V × Stream V T :=
  ts.foldl (fun (acc : DB V T × HMem V × Stream V T) p =>
    let r := handleTrans sp al acc.2.2 acc.1 acc.2.1 p.1
    match p.2.1 with
    | some c =>
      let S := cutStream c r.1.S
      (startup sp S, handleStartupPosFrom sp c S, S)
    | none => (r.1, p.2.2.foldl (HMem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
    (init sp, handleStartupPosFrom sp 0 (init sp).S, (init sp).S)

/-- Rule 4 by position after a cut is rule 4 by node id (bergdb 005-62, question
2). In a run as in `Rule4Pos_handles`, with T12's assumptions on the virtual root
(`ExecRootOK`, `VirtLiveOK`), take the stream S after any transaction k and a cut
at c that is safe there (`CutOK`). The startup with handles and Java's rule 4 by
position from the stream cut at c, with any first position up to c
(`handleStartupPosFrom`: a pointer of a node of D below the first position is left
as it is), gives the same memory as the startup with rule 4 by node id from it
(`handleStartup`), the one that `runHandlesCut` and `T12_handles` use. So no
pointer that Java skips names a node with a canonical object, and every other
one is found by `posToId`, by `byPos`, or, for a top node's, by node id.
Proved: `rule4PosCut_handles` (SIS/Proof/HandleCutPos.lean). -/
def Rule4PosCut_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ ts : List T, RunOK sp al ts → PhysRunOK sp al ts → EvictRunOK sp al ts →
    al.stillDirty = javaTest sp → al.mark = true → ExecRootOK sp → VirtLiveOK sp →
    ∀ k ≤ ts.length, ∀ c first, CutOK sp c (run sp al (ts.take k)) k → first ≤ c →
      handleStartupPosFrom sp first (cutStream c (run sp al (ts.take k)).S) =
        handleStartup sp (cutStream c (run sp al (ts.take k)).S)

/-- Runs with cuts and rule 4 by position are runs with cuts and rule 4 by node id
(bergdb 005-62). With the assumptions of `T12_handles`, the run with handles and
rule 4 by position at every startup (`runHandlesCutPos`) is the same as
`runHandlesCut` after every transaction and its operations or its restart: the
same state, memory and stream of the last startup. So `T12_handles` holds for it
as it is. Proved: `runPosCut_handles` (SIS/Proof/HandleCutPos.lean). -/
def RunPosCut_handles (sp : Spec V T) (al : Algo V T) : Prop :=
  ∀ cs : List (T × Option Nat × List HCacheOp),
    RunOK sp al (cs.map (·.1)) → PhysRunOK sp al (cs.map (·.1)) →
    EvictRunOK sp al (cs.map (·.1)) → al.stillDirty = javaTest sp → al.mark = true →
    ExecRootOK sp → VirtLiveOK sp → PolicyCutOK al →
    (∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1)) →
    (∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, HCacheOp.read t ∈ cs[j].2.2 →
      lastFa (run sp al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) →
    ∀ j ≤ cs.length, runHandlesCutPos sp al (cs.take j) = runHandlesCut sp al (cs.take j)

end SIS
