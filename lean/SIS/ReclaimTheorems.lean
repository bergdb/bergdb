/-
Self-indexed streams in Lean: the theorems of Level 3, reclaim (bergdb item
001, WPs R3 to R6). T9 and T12 with eviction are stated over handles, in
HandleReclaimTheorems.lean (bergdb 005-62).

Trusted part: the statements. The proofs are in SIS/Proof/; the proofs here
only connect them.
-/
import SIS.Theorems
import SIS.Reclaim
import SIS.Proof.CutRecover
import SIS.Proof.CutRuns
import SIS.Proof.CutCover

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T13' (bergdb item 001, WP R3): with touches, step 3, by testing or by
marking, gives exactly the index nodes that are not in D (and not a virtual
root) and are dirty or touched. BergDB's reclaim step touches index nodes,
which makes them dirty without adding entries (M17), and then rewrites the old
values: until bergdb 024-07 the nodes that the traversal of its key range
visited (`Db.touchRange`), since then the nodes on the paths of its own puts
(`Db.touchPaths`). -/
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

/-- T-COVER (bergdb 024-07, section 4): what puts the index nodes at the cut or
later when no key range is touched. In the state after transaction e of a run
(e the end of an iteration of reclaim, c its cut): if every data node reachable
at e has its version at c or later (the rewrites), and every written index node
reachable at e has a data node below it at e (reachable from it through live
pointers), then every written index node reachable at e is in D or has its
latest version at c or later. A node that is not in D is clean, so its latest
version is good, and a good version's references lead, each to a record at or
before the one above, down to the one version of the data node below
(`Inv.clean_ge_data`).

Since 024-07 a reclaim step of BergDB touches only the index nodes on the paths
of its own puts, not every index node of a key range (`Db.touchPaths`; before,
`Db.touchRange`). The second premise is BergDB's: a delete unlinks the nodes it
empties (`Dag.deleteUpward`), so no index node that a lookup reaches is without
a live key below it, but an empty space root; the model has no keys and takes
it as given. T-SCHEME, that the scheme's waits then give `CutOK`, is still
checked by running (`checkSchemeC` in SIS/ReclaimExample.lean), not proved;
`T_latest` below proves its part about the latest versions. -/
theorem T_cover (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (e c : Nat) (he : e ≤ ts.length) :
    let db := run sp al (ts.take e)
    (∀ d m, db.P.get? d = some m → m.isData = true → reachable sp db.P e d = true →
      ∃ u, db.S.lv d = some u ∧ c ≤ u.recNo) →
    (∀ x n, db.P.get? x = some n → n.isData = false → written sp x = true →
      reachable sp db.P e x = true →
      ∃ d m, d ∈ reachFrom sp db.P e x n ∧ db.P.get? d = some m ∧ m.isData = true) →
    ∀ x, isIndex db.P x = true → written sp x = true → reachable sp db.P e x = true →
      inD db.D x = true ∨ ∃ v, db.S.lv x = some v ∧ c ≤ v.recNo :=
  cover_st sp al ts hok (algOK_of sp al hst) e c he

/-- T-LATEST (bergdb 024-07, section 4): from an iteration's end on, the latest
versions are at the cut or later. With T-COVER's two premises at e, the end of
an iteration with its cut at c ≤ e, in every state after T(k), e ≤ k, whose
startup pos has passed e (BergDB waits for it: pEnd), every node reachable at a
time from e to k has its latest version, if it has one, at c or later: the
latest versions that a read from the first available time e on may follow
(`ReadsPhys.latest`, and so `CutOK`'s part 4), and the first half of `CutOK`'s
part 3 for the nodes of D that such a read reaches.

A node made after T(e) has its versions after e; one that existed then was
reachable at e (no resurrection): there a data node is at c or later by the
rewrites, and an index node is at c or later or in D (T-COVER), with a
got-dirty index at most e, so it is written once the startup pos has passed e.

Not in it, and still checked by running (`checkSchemeC`, and C-CUT on Java's
traces), not proved: the versions that a pointer leads to besides the latest
ones (`ReadsPhys.child`), the references of D's nodes, and the nodes of D that
no read from e on reaches (BergDB's second wait, pSafe; bergdb 001-07, section
5, steps 6 and 7). -/
theorem T_latest (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (e k c : Nat) (hce : c ≤ e) (hek : e ≤ k) (hk : k ≤ ts.length) :
    let db := run sp al (ts.take e)
    let dbk := run sp al (ts.take k)
    (∀ d m, db.P.get? d = some m → m.isData = true → reachable sp db.P e d = true →
      ∃ u, db.S.lv d = some u ∧ c ≤ u.recNo) →
    (∀ x n, db.P.get? x = some n → n.isData = false → written sp x = true →
      reachable sp db.P e x = true →
      ∃ d m, d ∈ reachFrom sp db.P e x n ∧ db.P.get? d = some m ∧ m.isData = true) →
    e < lastSp dbk.S →
    ∀ t x, e ≤ t → t ≤ k → reachable sp dbk.P t x = true →
      ∀ v, dbk.S.lv x = some v → c ≤ v.recNo :=
  latest_st sp al ts hok (algOK_of sp al hst) e k c hce hek hk

/-- The bound of a touch (bergdb 024-07, section 5), a definition: the touch of
the changes c made at time i to P marks only nodes on the paths of the change.
Every touched node has below it at i - 1, itself included, a node that c gives
an entry or that is no longer reachable at i (a node that the change replaces).
So a touch makes no node dirty outside the writer's own paths, and what a
transaction with a touch makes dirty is bounded by the paths of its change,
whatever else the structure holds. Java's reclaim steps meet it since 024-07
(`Db.touchPaths` visits the paths of the step's own puts; `Db.touchRange`
visited a key range), and the trace checker checks it (C-A, `touchPath`). No
theorem assumes it: it is a cost property, and `StepOK` allows any touch that
is closed upward. -/
def TouchOnPaths (sp : Spec V T) (P : Struct V) (i : Time) (c : Changes V) : Prop :=
  ∀ x ∈ c.touch, ∀ nx, P.get? x = some nx →
    ∃ z ∈ reachFrom sp P (i - 1) x nx,
      changed c z = true ∨ reachable sp (P.apply i c) i z = false

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
