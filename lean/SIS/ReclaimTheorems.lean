/-
Self-indexed streams in Lean: the theorems of Level 3, reclaim (bergdb item
001, WPs R3 to R6).

Trusted part: the statements. The proofs are in SIS/Proof/; the proofs here
only connect them.
-/
import SIS.Theorems
import SIS.Reclaim
import SIS.PhysTheorems
import SIS.Proof.CutRecover
import SIS.Proof.CutRuns
import SIS.Proof.CutPhysRun

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T13' (bergdb item 001, WP R3): with touches, step 3, by testing or by
marking, gives exactly the index nodes that are not in D (and not a virtual
root) and are dirty or touched. BergDB's reclaim step touches the nodes that
its range traversal visits, which makes them dirty without adding entries
(`Db.touchRange`, M17), and then rewrites the old values. -/
theorem T13_markTouch (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (j : Nat) (hj : j < ts.length) (x : NodeId) :
    let db := run sp al (ts.take j)
    let c := sp.exec ts[j] (j + 1) (view sp db.P j)
    let P := db.P.apply (j + 1) c
    let vs0 := writeAll sp db.S (j + 1) P ((c.new.filter (·.isData)).map (·.id)) []
    x ∈ gotDirty3 sp al db.S vs0 P c db.D (j + 1) ↔
      isIndex P x = true ∧ inD db.D x = false ∧ written sp x = true ∧
        (dirty sp (db.S.building vs0) P (j + 1) x = true ∨ x ∈ c.touch) := by
  intro db c P vs0
  have hinv : Inv sp db j := inv_st sp al ts hok (algOK_of sp al hst) j (by omega)
  have hlen := hinv.len
  have hc : (parts sp al db ts[j]).c = c := by rw [parts_c, hlen]; rfl
  have hP : (parts sp al db ts[j]).P = P := by rw [parts_P, hc, hlen]
  have hvs0 : (parts sp al db ts[j]).vs0 = vs0 := by rw [parts_vs0, hP, hc, hlen]
  have hstep : StepOK sp db.P (j + 1) (parts sp al db ts[j]).c := by
    rw [hc]; have := hok.2 j hj; simpa [st] using this
  have h := step_gd3_mem' sp al db ts[j] hok.1 hinv hstep x
  have hg : (parts sp al db ts[j]).gd3 = gotDirty3 sp al db.S vs0 P c db.D (j + 1) := by
    rw [← hvs0, ← hP, ← hc, ← hlen]; rfl
  rw [hg, hP, hc, hvs0] at h
  rw [h]
  constructor
  · rintro ⟨-, a, b, w, d⟩; exact ⟨a, b, w, d⟩
  · rintro ⟨a, b, w, d⟩; exact ⟨isSome_of_isIndex' a, a, b, w, d⟩

/-- T8 (bergdb item 001, WP R4): after a safe cut (`CutOK`) at c in the state
after transaction k of a run, startup from the cut stream gives the same
lookups at every time from the first available time f to k (`SameFrom`: every
node but a virtual root has the same content, and a virtual root the same
live children), and the same D. With a virtual root, the transactions that
startup reruns see the root only through its live children (`ExecRootOK`),
and the root's live children are those of its last entry (`VirtLiveOK`):
startup rebuilds the root from the root children it can read, which lacks the
entries for the older ones. The records before c are gone (their stubs keep
only the node ids and record numbers); startup's reads for the times from f on
read none of them. -/
theorem T8_recoverCut (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) (k c : Nat) (hk : k ≤ ts.length)
    (hcut : CutOK sp c (run sp al (ts.take k)) k) :
    let db := run sp al (ts.take k)
    SameFrom sp (lastFa db.S) k (startup sp (cutStream c db.S)).P db.P ∧
      (startup sp (cutStream c db.S)).D = db.D :=
  recoverCut sp al ts hok (algOK_of sp al hst) hk hex hvl hcut

/-- T9 (bergdb item 001, WP R4): in a run with eviction as in `T2_cache`
(BergDB's algorithm with marking, the assumptions, those of the physical layer
and of stage 2, the Level 4 startup, any cache schedules, restarts after any
transactions), after any transaction and its cache operations or its restart,
with a safe cut (`CutOK`) at c in the run's state: a read through the Level 4
loader (`Mem.read4`, with Rule R from the stream of the last startup) at any
time t from the first available time f to the last record gives the same on
the stream cut at c as on the whole stream, so it needs no record before the
cut; and it gives P at t (`TR_view_restarts`): exactly the nodes reachable at
t, each with its node at t. The cut is made while the process runs: the
memory keeps the objects and slots made before it. -/
theorem T9_readCut (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp))
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hev : EvictRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (j c : Nat) (hjt : j ≤ ts.length)
    (hcut : CutOK sp c (run sp al ((ts.take j).map (·.1))) j) (t : Time)
    (hft : lastFa (run sp al ((ts.take j).map (·.1))).S ≤ t) (ht : t ≤ j) :
    let db := run sp al ((ts.take j).map (·.1))
    let r := runEvict sp al (ts.take j)
    let m := r.2.1
    m.read4 sp r.2.2 (cutStream c db.S) t = m.read4 sp r.2.2 db.S t ∧
      (m.read4 sp r.2.2 (cutStream c db.S) t).2.map (·.1) = reachList sp db.P t ∧
      ∀ p ∈ (m.read4 sp r.2.2 (cutStream c db.S) t).2, view sp db.P t p.1 = some p.2 := by
  intro db r m
  have he : m.read4 sp r.2.2 (cutStream c db.S) t = m.read4 sp r.2.2 db.S t :=
    readCut ts hok hph hev hj hmk j hjt hcut hft ht
  rw [he]
  exact ⟨rfl, TR_view_restarts sp al ts hok hph hev hj hmk j hjt t ht⟩

/-- T12 (bergdb item 001, WP R5): a run that restarts from safe cut streams
(`runRestartsCut`: after a transaction marked some c, a restart from the stream
cut at c, with `CutOK` at the largest cut so far in the run without restarts
at that point) appends the records of the run without restarts: its stream is
that run's, cut at the largest cut (the records before it are stubs); its D is
the run's, and so are its lookups from the run's first available time on.
With BergDB's bookkeeping (marking and `javaTest`), T8's assumptions on a
virtual root, and policies that do not look at what a cut removes
(`PolicyCutOK`). The nodes of D that no lookup from f on reaches (M33, M34)
are written again with the run's content: Rule A keeps their ancestors at a
time they were reachable in D, put back with versions after the startup pos,
and startup reads them through these versions (Rule R). -/
theorem T12_restartCut (sp : Spec V T) (al : Algo V T) (cs : List (T × Option Nat))
    (hok : RunOK sp al (cs.map (·.1))) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1)) :
    let db := runRestartsCut sp al cs
    let r := run sp al (cs.map (·.1))
    db.S = cutStream (cutMax (cs.map (·.2))) r.S ∧ db.D = r.D ∧
      SameFrom sp (lastFa r.S) cs.length db.P r.P :=
  restartCut sp al cs hok hj hmk hex hvl hpol hcut

end SIS
