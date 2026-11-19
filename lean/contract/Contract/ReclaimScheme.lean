/-
The contract package (bergdb 030-23): reclaim's contract RC and T-SCHEME, the
statement that a cut that meets RC is safe (`CutOK`), in the form that
replaces the premise `hcut` of `full_cut`, `cut_keeps_top` and
`cut_java_reads` (bergdb 030-22, sections 2 and 3).

RC is in the abstract model's words, for a run of transactions ts, a cut c,
the end e of the iteration of reclaim that decided the cut (tEnd, the record
of its last step), and a state k from the decision on (bergdb 030-22,
section 2.2):

* RC1, the order: c ≤ e ≤ fa(k);
* RC2, the rewrites: every data node that a read at e reaches has its
  version at c or later;
* RC3, a value below: every written index node that a read at e reaches has
  a data node below it at e;
* RC4, Java's two waits: some record v has its startup pos at e or later,
  and the startup pos of record k is after v (so the first such record is
  before it too: `Reclaim.markSafePositions`, `pretruncateIfPossible`).

T-SCHEME (`TScheme`) is a definition, not a theorem: it is half proved. The
proved half (`rc_latest`, `rc_parts`): parts 1, 3 (latest versions) and 4 of
`CutOK`, and part 2 for the latest versions that a read follows. The open
half (`TSchemeOpen`): part 2 for the versions that a pointer leads to
besides the latest ones (`ReadsPhys.child`), and part 3's references below
the cut, which need an invariant on superseded versions that is not known
(bergdb 030-22, section 3.2; 030-23). `tscheme_of_open` puts the halves
together; `full_cut_rc`, `cut_keeps_top_rc` and `cut_java_reads_rc` are the
theorems after cuts with T-SCHEME and RC in place of `CutOK`.
-/
import Contract.RecoverCutTheorems
import SIS.ReclaimTheorems
import Contract.Proof.ReclaimScheme

namespace Contract

open SIS.Check (BVal)
open SIS (Spec Algo DB Struct reachable reachFrom written lastSp lastFa inD run CutOK
  ReadsPhys RunOK javaTest cutMax)

variable {V T : Type} [DecidableEq V]

/-- RC2 (bergdb 030-22, section 2.2), in the state db after transaction e:
every data node reachable at e has its version at c or later. The premise
`hrw` of `T_cover` and `T_latest`. -/
def RC2 (sp : Spec V T) (db : DB V T) (e c : Nat) : Prop :=
  ∀ d m, db.P.get? d = some m → m.isData = true → reachable sp db.P e d = true →
    ∃ u, db.S.lv d = some u ∧ c ≤ u.recNo

/-- RC3 (bergdb 030-22, section 2.2), in the state db after transaction e:
every written index node reachable at e has a data node below it at e. The
premise `hlb` of `T_cover` and `T_latest`. -/
def RC3 (sp : Spec V T) (db : DB V T) (e : Nat) : Prop :=
  ∀ x n, db.P.get? x = some n → n.isData = false → written sp x = true →
    reachable sp db.P e x = true →
    ∃ d m, d ∈ reachFrom sp db.P e x n ∧ db.P.get? d = some m ∧ m.isData = true

/-- RC4 (bergdb 030-22, section 2.2): some record v has its startup pos at e
or later, and the startup pos of record k is after v. Equivalent to the
condition on the first such record v, since the first is at or before any. -/
def RC4 (sp : Spec V T) (al : Algo V T) (ts : List T) (e k : Nat) : Prop :=
  ∃ v, e ≤ lastSp (run sp al (ts.take v)).S ∧ v < lastSp (run sp al (ts.take k)).S

/-- Reclaim's contract RC at a cut c, for the iteration that ends at e, in the
state after transaction k of the run of ts (bergdb 030-22, section 2.2). RC1
is c ≤ e ≤ fa(k); that c is at or after every earlier cut is the run's, in
`CutsMeetRC`. -/
def RC (sp : Spec V T) (al : Algo V T) (ts : List T) (c e k : Nat) : Prop :=
  c ≤ e ∧ e ≤ lastFa (run sp al (ts.take k)).S ∧
    RC2 sp (run sp al (ts.take e)) e c ∧ RC3 sp (run sp al (ts.take e)) e ∧ RC4 sp al ts e k

/-- **T-SCHEME** (bergdb 030-22, section 3.1; 024-06; 001-07, section 5): for a
run that meets `RunOK`, with Java's still-dirty test (Rule A) and the marking,
a cut that meets RC is safe. A definition: half proved (`rc_parts`), the
rest open (`TSchemeOpen`). -/
def TScheme (sp : Spec V T) (al : Algo V T) : Prop :=
  al.stillDirty = javaTest sp → al.mark = true →
  ∀ ts : List T, RunOK sp al ts → ∀ c e k, k ≤ ts.length → RC sp al ts c e k →
    CutOK sp c (run sp al (ts.take k)) k

/-- The open half of T-SCHEME (bergdb 030-22, section 3.2, points 2 and 3):
under RC, every version that a read from the first available time on may
follow is at c or later (`CutOK`'s part 2; its latest versions are proved,
`rc_latest`), and every reference below c of the latest version of a node
of D names the latest version of its node (part 3's second half). -/
def TSchemeOpen (sp : Spec V T) (al : Algo V T) : Prop :=
  al.stillDirty = javaTest sp → al.mark = true →
  ∀ ts : List T, RunOK sp al ts → ∀ c e k, k ≤ ts.length → RC sp al ts c e k →
    let db := run sp al (ts.take k)
    (∀ t w, lastFa db.S ≤ t → t ≤ k → ReadsPhys sp db.S db.P db.D t w → c ≤ w.recNo) ∧
    (∀ x, inD db.D x = true → ∀ v, db.S.lv x = some v →
      ∀ y r, v.ref? y = some r → r < c → (db.S.lv y).map (·.recNo) = some r)

/-- The cut marks of a run with handles meet RC: at each mark of a cut c, c is
at or after every earlier mark's cut (RC1's order of the cuts), and c meets
RC for some iteration's end e in the state after that transaction. -/
def CutsMeetRC (sp : Spec V T) (al : Algo V T) (cs : List (T × Option Nat × List SIS.HCacheOp)) :
    Prop :=
  ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
    (∀ i (hi : i < j) c', cs[i].2.1 = some c' → c' ≤ c) ∧
    ∃ e, RC sp al (cs.map (·.1)) c e (j + 1)

/-! ## The proved half -/

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- Under RC, every node that is reachable at a time from the first available
time f to k has its latest version, if any, at c or later (`T_latest`, with
RC4 giving that the startup pos of record k is at e or later). -/
theorem rc_latest (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {c e k : Nat}
    (hk : k ≤ ts.length) (hrc : RC sp al ts c e k) :
    let db := run sp al (ts.take k)
    ∀ t x, lastFa db.S ≤ t → t ≤ k → reachable sp db.P t x = true →
      ∀ v, db.S.lv x = some v → c ≤ v.recNo := by
  dsimp only
  intro t x hft htk hr v hv
  have hst := SIS.algOK_of sp al (Or.inl hj)
  obtain ⟨hce, hef, hrw, hlb, w, hw1, hw2⟩ := hrc
  have h1 := lastSp_take_le hok hst w
  have h2 := lastSp_take_le hok hst k
  exact SIS.latest_st sp al ts hok hst e k c hce (by omega) hk hrw hlb
    (show e ≤ lastSp (run sp al (ts.take k)).S by omega) t x (by omega) htk hr v hv

/-- The proved half of T-SCHEME: under RC, `CutOK`'s part 1, part 2 for the
latest versions (`ReadsPhys.latest`), the first half of part 3 for every node
of D, and part 4. -/
theorem rc_parts (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    {c e k : Nat} (hk : k ≤ ts.length) (hrc : RC sp al ts c e k) :
    let db := run sp al (ts.take k)
    c ≤ lastFa db.S ∧
    (∀ t x v, lastFa db.S ≤ t → t ≤ k → reachable sp db.P t x = true → db.S.lv x = some v →
      c ≤ v.recNo) ∧
    (∀ x, inD db.D x = true → ∀ v, db.S.lv x = some v → c ≤ v.recNo) ∧
    (∀ R z r, db.S.getLast? = some R → R.top = some (z, r) → c ≤ r) := by
  dsimp only
  have hst := SIS.algOK_of sp al (Or.inl hj)
  have hlat0 := rc_latest hok hj hk hrc
  obtain ⟨hce, hef, hrw, hlb, w, hw1, hw2⟩ := hrc
  have h1 := lastSp_take_le hok hst w
  have h2 := lastSp_take_le hok hst k
  have hes : e ≤ lastSp (run sp al (ts.take k)).S := by omega
  have hlat : ∀ t x, e ≤ t → t ≤ k → reachable sp (run sp al (ts.take k)).P t x = true →
      ∀ v, (run sp al (ts.take k)).S.lv x = some v → c ≤ v.recNo :=
    SIS.latest_st sp al ts hok hst e k c hce (by omega) hk hrw hlb hes
  refine ⟨by omega, fun t x v hft htk hr hv => hlat0 t x hft htk hr v hv,
    inD_lv_ge hok hst hmk hk hce hes hlat, ?_⟩
  exact top_ge (SIS.inv_st sp al ts hok hst k hk) hok.1.liveSub hes hlat

end

/-- T-SCHEME from its open half: the proved half gives the rest of `CutOK`. -/
theorem tscheme_of_open {sp : Spec V T} {al : Algo V T} (ho : TSchemeOpen sp al) :
    TScheme sp al := by
  intro hj hmk ts hok c e k hk hrc
  obtain ⟨h2, h3⟩ := ho hj hmk ts hok c e k hk hrc
  obtain ⟨p1, -, p3, p4⟩ := rc_parts hok hj hmk hk hrc
  exact ⟨p1, h2, fun x hx v hv => ⟨p3 x hx v hv, h3 x hx v hv⟩, p4⟩

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- CutOK's part 3, second half, under RC, for a run with TREE and A6'
(`EvictRunOK`, which the bridge gives for BergDB's key tree): a reference below
c of the latest version of a node of D names the latest version of a node not
in D. -/
theorem rc_dref (hok : RunOK sp al ts) (hev : SIS.EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {c e k : Nat}
    (hk : k ≤ ts.length) (hrc : RC sp al ts c e k) :
    let db := run sp al (ts.take k)
    ∀ x, inD db.D x = true → ∀ v, db.S.lv x = some v →
      ∀ y r, v.ref? y = some r → r < c → (db.S.lv y).map (·.recNo) = some r ∧ inD db.D y = false := by
  dsimp only
  have hst := SIS.algOK_of sp al (Or.inl hj)
  obtain ⟨hce, -, hrw, hlb, w, hw1, hw2⟩ := hrc
  have h1 := lastSp_take_le hok hst w
  apply dref_lv hok hj hmk hev hk
  intro K hsK hKk
  have h2 := lastSp_take_le hok hst K
  have hes : e ≤ lastSp (run sp al (ts.take K)).S :=
    Nat.le_trans hw1 (SIS.lastSp_st_mono hok hst (i := w) (j := K) (by omega) (by omega))
  exact inD_lv_ge hok hst hmk (by omega) hce hes
    (SIS.latest_st sp al ts hok hst e K c hce (by omega) (by omega) hrw hlb hes)

/-- CutOK under RC from part 2 alone, for a run with TREE and A6'. -/
theorem cutOK_of_reads (hok : RunOK sp al ts) (hev : SIS.EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {c e k : Nat}
    (hk : k ≤ ts.length) (hrc : RC sp al ts c e k)
    (h2 : ∀ t w, lastFa (run sp al (ts.take k)).S ≤ t → t ≤ k →
      ReadsPhys sp (run sp al (ts.take k)).S (run sp al (ts.take k)).P (run sp al (ts.take k)).D t w →
      c ≤ w.recNo) :
    CutOK sp c (run sp al (ts.take k)) k := by
  obtain ⟨p1, -, p3, p4⟩ := rc_parts hok hj hmk hk hrc
  have hd := rc_dref hok hev hj hmk hk hrc
  exact ⟨p1, h2, fun x hx v hv => ⟨p3 x hx v hv, fun y r hr hrc' => (hd x hx v hv y r hr hrc').1⟩,
    p4⟩

end

/-- The open half of T-SCHEME as it stands since `rc_dref` (bergdb 030-23): for
a run with TREE and A6' (`EvictRunOK`, which the bridge gives for BergDB's key
tree), under RC, every version that a read at a time from the first available
time on may follow is at c or later (`CutOK`'s part 2). -/
def TSchemeReads (sp : Spec V T) (al : Algo V T) : Prop :=
  al.stillDirty = javaTest sp → al.mark = true →
  ∀ ts : List T, RunOK sp al ts → SIS.EvictRunOK sp al ts → ∀ c e k, k ≤ ts.length →
    RC sp al ts c e k →
    let db := run sp al (ts.take k)
    ∀ t w, lastFa db.S ≤ t → t ≤ k → ReadsPhys sp db.S db.P db.D t w → c ≤ w.recNo

/-- `TSchemeReads` and RC at every cut mark give `hcut`, for a run with A6'. -/
theorem hcut_of_reads {sp : Spec V T} {al : Algo V T} (hts : TSchemeReads sp al)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    {cs : List (T × Option Nat × List SIS.HCacheOp)} (hok : RunOK sp al (cs.map (·.1)))
    (hev : SIS.EvictRunOK sp al (cs.map (·.1))) (hrc : CutsMeetRC sp al cs) :
    ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1) := by
  intro j hjl c hc
  obtain ⟨hle, e, hrc'⟩ := hrc j hjl c hc
  rw [cutMax_take_of_le cs hjl hc hle]
  have hk : j + 1 ≤ (cs.map (·.1)).length := by simp only [List.length_map]; omega
  exact cutOK_of_reads hok hev hj hmk hk hrc' (hts hj hmk _ hok hev c e (j + 1) hk hrc')

/-- T-SCHEME and RC at every cut mark give the premise `hcut` of the theorems
after cuts: `CutOK` at the largest cut so far. -/
theorem hcut_of_rc {sp : Spec V T} {al : Algo V T} (hts : TScheme sp al)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    {cs : List (T × Option Nat × List SIS.HCacheOp)} (hok : RunOK sp al (cs.map (·.1)))
    (hrc : CutsMeetRC sp al cs) :
    ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1) := by
  intro j hjl c hc
  obtain ⟨hle, e, hrc'⟩ := hrc j hjl c hc
  rw [cutMax_take_of_le cs hjl hc hle]
  exact hts hj hmk _ hok c e (j + 1) (by simp only [List.length_map]; omega) hrc'

/-! ## The theorems after cuts, with RC in place of `CutOK` -/

section

variable {p : Params} {h : BHist} {top : Nat → Top} {kind : Nat → Bool}

/-- `full_cut` with T-SCHEME and RC at every cut mark in place of `CutOK`. -/
theorem full_cut_rc (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hts : TScheme h.spec al)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) :
    let db := (SIS.runHandlesCut h.spec al cs).1
    let r := SIS.run h.spec al (cs.map (·.1))
    db.S = SIS.cutStream (SIS.cutMax (cs.map (·.2.1))) r.S ∧ db.D = r.D ∧
      SIS.SameFrom h.spec (SIS.lastFa r.S) cs.length db.P r.P := by
  have hok : SIS.RunOK h.spec al (cs.map (·.1)) := by rw [hcs]; exact hm.meetsBridge.runOK al
  exact full_cut hm al hj hmk hpol cs hcs (hcut_of_rc hts hj hmk hok hrc) hreads

/-- `cut_keeps_top` with T-SCHEME and RC at every cut mark in place of `CutOK`:
after the run with handles, reads from the first available time on,
evictions, and restarts from cut streams whose cuts meet RC, the cut stream
keeps the top nodes that Java's search reads. -/
theorem cut_keeps_top_rc (hm : MeetsFull p h top)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hts : TScheme h.spec al)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    {zn : NodeId × TopNode} (hz : topAt (top h.txs.length) t = some zn) :
    let P' := (SIS.runHandlesCut h.spec al cs).1.P
    viewTop (SIS.view h.spec P' t) = some zn.1 ∧
      ∃ nz, SIS.view h.spec P' t zn.1 = some nz ∧ nz.hist = topEntries zn.2 := by
  have hok : SIS.RunOK h.spec al (cs.map (·.1)) := by rw [hcs]; exact hm.meetsBridge.runOK al
  exact cut_keeps_top hm al hj hmk hpol cs hcs (hcut_of_rc hts hj hmk hok hrc) hreads hft htn hz

/-- `cut_java_reads` with T-SCHEME and RC at every cut mark in place of
`CutOK`: after the run with handles, reads from the first available time on,
evictions, and restarts from cut streams whose cuts meet RC, Java's get and
scan at a time from the first available time on are right. -/
theorem cut_java_reads_rc (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hts : TScheme h.spec al)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  have hok : SIS.RunOK h.spec al (cs.map (·.1)) := by rw [hcs]; exact hm.meetsBridge.runOK al
  exact cut_java_reads hm hM hkd al hj hmk hpol cs hcs (hcut_of_rc hts hj hmk hok hrc) hreads
    hft htn mid s tp


/-- `full_cut` with `TSchemeReads` and RC at every cut mark in place of `CutOK`. -/
theorem full_cut_reads (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hts : TSchemeReads h.spec al)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) :
    let db := (SIS.runHandlesCut h.spec al cs).1
    let r := SIS.run h.spec al (cs.map (·.1))
    db.S = SIS.cutStream (SIS.cutMax (cs.map (·.2.1))) r.S ∧ db.D = r.D ∧
      SIS.SameFrom h.spec (SIS.lastFa r.S) cs.length db.P r.P := by
  have hok : SIS.RunOK h.spec al (cs.map (·.1)) := by rw [hcs]; exact hm.meetsBridge.runOK al
  have hev : SIS.EvictRunOK h.spec al (cs.map (·.1)) := by
    rw [hcs]; exact bridge_evictRunOK hm.meetsBridge hm.meetsEvict al
  exact full_cut hm al hj hmk hpol cs hcs (hcut_of_reads hts hj hmk hok hev hrc) hreads

/-- `cut_keeps_top` with `TSchemeReads` and RC at every cut mark in place of
`CutOK`: after the run with handles, reads from the first available time on,
evictions, and restarts from cut streams whose cuts meet RC, the cut stream
keeps the top nodes that Java's search reads. -/
theorem cut_keeps_top_reads (hm : MeetsFull p h top)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hts : TSchemeReads h.spec al)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    {zn : NodeId × TopNode} (hz : topAt (top h.txs.length) t = some zn) :
    let P' := (SIS.runHandlesCut h.spec al cs).1.P
    viewTop (SIS.view h.spec P' t) = some zn.1 ∧
      ∃ nz, SIS.view h.spec P' t zn.1 = some nz ∧ nz.hist = topEntries zn.2 := by
  have hok : SIS.RunOK h.spec al (cs.map (·.1)) := by rw [hcs]; exact hm.meetsBridge.runOK al
  have hev : SIS.EvictRunOK h.spec al (cs.map (·.1)) := by
    rw [hcs]; exact bridge_evictRunOK hm.meetsBridge hm.meetsEvict al
  exact cut_keeps_top hm al hj hmk hpol cs hcs (hcut_of_reads hts hj hmk hok hev hrc) hreads hft htn hz

/-- `cut_java_reads` with `TSchemeReads` and RC at every cut mark in place of
`CutOK`: after the run with handles, reads from the first available time on,
evictions, and restarts from cut streams whose cuts meet RC, Java's get and
scan at a time from the first available time on are right. -/
theorem cut_java_reads_reads (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hts : TSchemeReads h.spec al)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  have hok : SIS.RunOK h.spec al (cs.map (·.1)) := by rw [hcs]; exact hm.meetsBridge.runOK al
  have hev : SIS.EvictRunOK h.spec al (cs.map (·.1)) := by
    rw [hcs]; exact bridge_evictRunOK hm.meetsBridge hm.meetsEvict al
  exact cut_java_reads hm hM hkd al hj hmk hpol cs hcs (hcut_of_reads hts hj hmk hok hev hrc) hreads
    hft htn mid s tp
end

end Contract
