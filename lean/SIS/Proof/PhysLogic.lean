/-
Proofs about the physical layer, part 5: what the run says about nodes
without a canonical object (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysFollow

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The facts of the run after T(K) (the state dbK) that the proofs of the
physical layer use; db is the final state. -/
structure KCtx (sp : Spec V T) (db dbK : DB V T) (K : Nat) : Prop where
  inv : Inv sp dbK K
  fresh : CleanFresh sp dbK K
  pre : dbK.S = db.S.take (K + 1)
  grow : Grow dbK.P K db.P
  dLater : ∀ y d, (y, d) ∈ dbK.D → d ≤ lastSp db.S → ∃ r w, K < r ∧ db.S.versionAt r y = some w
  dSec : ∀ y d, (y, d) ∈ dbK.D → lastSp db.S < d → ∃ R, db.S[d]? = some R ∧ y ∈ R.gd ∧ d ≤ K
  fixedLe : FixedLe sp db K

theorem live_nil {sp : Spec V T} (hls : LiveSub sp) : sp.live ([] : History V) = [] := by
  cases h : sp.live ([] : History V) with
  | nil => rfl
  | cons y l =>
    obtain ⟨e, he, -⟩ := hls [] y (by rw [h]; exact List.mem_cons_self)
    cases he

theorem sext_take (S : Stream V T) (n : Nat) : SExt (S.take n) S := by
  have := SExt.append (S.take n) (S.drop n)
  rwa [List.take_append_drop] at this

/-- The coverage clauses of the invariant at K: the nodes that have canonical
objects. -/
structure Cover (db : DB V T) (K : Nat) (m : Mem V) : Prop where
  sK : lastSp db.S ≤ K
  rootC : m.canonicalOf root ≠ none
  coverGd : ∀ d R x, lastSp db.S < d → d ≤ K → db.S[d]? = some R → x ∈ R.gd →
    m.canonicalOf x ≠ none
  coverSec : ∀ x w, newest db.S (lastSp db.S) x = some w → w.isData = false →
    w.hist.upTo (lastSp db.S) ≠ [] → m.canonicalOf x ≠ none
  coverNew : ∀ x n e, db.P.get? x = some n → e ∈ n.hist → lastSp db.S < e.time → e.time ≤ K →
    m.canonicalOf x ≠ none

theorem MemInv.cover {sp : Spec V T} {db : DB V T} {K : Nat} {m : Mem V} (hm : MemInv sp db K m) :
    Cover db K m := by
  refine ⟨hm.sK, ?_, hm.coverGd, hm.coverSec, hm.coverNew⟩
  obtain ⟨ht0, o0, ho0, hc0, -⟩ := hm.root
  rw [(m.canonicalOf_eq_some SIS.root m.root).mpr ⟨ht0, o0, ho0, hc0⟩]
  simp

theorem Cover.ne_root {db : DB V T} {K : Nat} {m : Mem V} (hc : Cover db K m) {y : NodeId}
    (hnc : m.canonicalOf y = none) : y ≠ SIS.root := by
  intro hy; rw [hy] at hnc; exact hc.rootC hnc

section Logic

variable {sp : Spec V T} {db dbK : DB V T} {K k : Nat} {m : Mem V}

theorem KCtx.lv_eq (hk : KCtx sp db dbK K) {y : NodeId}
    (hvK : ∀ r w, K < r → db.S.versionAt r y = some w → False) : db.S.lv y = dbK.S.lv y := by
  rw [hk.pre]
  symm
  apply lv_take
  intro r' hr'
  cases h : db.S.versionAt r' y with
  | none => rfl
  | some w => exact (hvK r' w (by omega) h).elim

theorem KCtx.reachable_eq (hk : KCtx sp db dbK K) (hls : LiveSub sp) {t : Time} (ht : t ≤ K)
    (y : NodeId) : reachable sp db.P t y = reachable sp dbK.P t y :=
  reachable_grow hls hk.inv.ptrs hk.inv.rootIn hk.grow ht y

/-- A node without a canonical object, with no version after K, is not in D
after T(K). -/
theorem Cover.notD (hm : Cover db K m) (hk : KCtx sp db dbK K) {y : NodeId}
    (hnc : m.canonicalOf y = none) (hvK : ∀ r w, K < r → db.S.versionAt r y = some w → False) :
    inD dbK.D y = false := by
  cases hD : inD dbK.D y
  · rfl
  · exfalso
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD
    by_cases hds : d ≤ lastSp db.S
    · obtain ⟨r, w, hr, hw⟩ := hk.dLater y d hd hds
      exact hvK r w hr hw
    · obtain ⟨R, hR, hy, hdK⟩ := hk.dSec y d hd (by omega)
      exact hm.coverGd d R y (by omega) hdK hR hy hnc

/-- A node without a canonical object has no entries up to K, if it has a
version after K: it is an index node. -/
theorem Cover.late_empty (hm : Cover db K m) (hctx : PCtx sp db k) {y : NodeId}
    (hnc : m.canonicalOf y = none) {ny : Node V} (hny : db.P.get? y = some ny)
    (hidx : ny.isData = false) {r : Nat} {w : Version V} (hr : K < r)
    (hw : db.S.versionAt r y = some w) :
    ny.hist.upTo K = [] ∧ ∃ w', newest db.S (lastSp db.S) y = some w' ∧ db.S.lv y = some w' := by
  have hsK := hm.sK
  cases hnw : newest db.S (lastSp db.S) y with
  | none =>
    have := (newest_eq_none_iff db.S (lastSp db.S) y).mp hnw r (by omega)
    rw [hw] at this; cases this
  | some w' =>
    refine ⟨?_, w', rfl, newest_lv hnw⟩
    obtain ⟨r2, hr2s, hw2, -⟩ := newest_ge hnw hw
    obtain ⟨-, -, ny2, hny2, hwh2, -, hwd2⟩ := hctx.inv.version_node hw2
    rw [hny, Option.some.injEq] at hny2
    subst hny2
    have hsec : w'.hist.upTo (lastSp db.S) = [] := by
      cases hh : w'.hist.upTo (lastSp db.S) with
      | nil => rfl
      | cons e l =>
        exfalso
        exact hm.coverSec y w' hnw (by rw [hwd2, hidx]) (by rw [hh]; simp) hnc
    have hs' : ny.hist.upTo (lastSp db.S) = [] := by
      rw [hwh2, upTo_upTo _ hr2s] at hsec; exact hsec
    apply upTo_eq_nil
    intro e he
    apply Classical.byContradiction
    intro hlt
    by_cases hes : e.time ≤ lastSp db.S
    · have : e ∈ ny.hist.upTo (lastSp db.S) := mem_upTo.mpr ⟨he, hes⟩
      rw [hs'] at this; cases this
    · exact hm.coverNew y ny e hny he (by omega) (by omega) hnc

/-- MG: a node without a canonical object, reachable at a time t up to K: its
latest version is good for t. -/
theorem Cover.mg (hm : Cover db K m) (hk : KCtx sp db dbK K) (hctx : PCtx sp db k)
    {y : NodeId} (hnc : m.canonicalOf y = none) {t : Time} (ht : t ≤ K)
    (hr : reachable sp db.P t y = true) :
    ∃ v, db.S.lv y = some v ∧ good sp db.S db.P t v = true := by
  have hls := hctx.ls
  obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  cases hd : ny.isData
  · by_cases hlate : ∃ r w, K < r ∧ db.S.versionAt r y = some w
    · obtain ⟨r, w, hrK, hw⟩ := hlate
      obtain ⟨hemp, w', hnw, hlv⟩ := hm.late_empty hctx hnc hny hd hrK hw
      refine ⟨w', hlv, ?_⟩
      obtain ⟨r2, hr2s, hw2, hle⟩ := newest_ge hnw hw
      obtain ⟨hw2y, -, ny2, hny2, hwh2, -, -⟩ := hctx.inv.version_node hw2
      rw [hny, Option.some.injEq] at hny2
      subst hny2
      have hupt : w'.hist.upTo t = ny.hist.upTo t := by rw [hwh2, upTo_upTo _ (by omega)]
      have hemp' : ny.hist.upTo t = [] := by rw [← upTo_upTo _ ht, hemp]; rfl
      rw [good_iff]
      refine ⟨⟨ny, by rw [hw2y]; exact hny, hupt⟩, ?_⟩
      intro z hz
      rw [hupt, hemp', live_nil hls] at hz
      cases hz
    · have hvK : ∀ r w, K < r → db.S.versionAt r y = some w → False :=
        fun r w h1 h2 => hlate ⟨r, w, h1, h2⟩
      have hDK := hm.notD hk hnc hvK
      have hrK : reachable sp dbK.P t y = true := by rw [← hk.reachable_eq hls ht]; exact hr
      obtain ⟨nK, hnK⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hrK))
      obtain ⟨n', hn', -, hd', -⟩ := hk.grow y nK hnK
      rw [hny, Option.some.injEq] at hn'
      subst hn'
      have hidx : isIndex dbK.P y = true := by simp [isIndex, hnK, ← hd', hd]
      have hyr : y ≠ SIS.root := hm.ne_root hnc
      have hcl : dirty sp dbK.S dbK.P K y = false := by
        cases hc : dirty sp dbK.S dbK.P K y
        · rfl
        · have := hk.inv.inv2 y hidx (written_of_ne_root sp hyr) hc
          rw [hDK] at this; cases this
      obtain ⟨vK, hvKl, hg⟩ := (dirty_false_iff sp dbK.S dbK.P K y).mp hcl
      refine ⟨vK, by rw [hk.lv_eq hvK]; exact hvKl, ?_⟩
      have hgK := hg t ht hrK
      rw [hk.pre] at hgK
      exact good_mono' sp (sext_take db.S (K + 1)) hk.grow ht hgK
  · obtain ⟨v, hv, -⟩ := hctx.inv.dataV y ny hny hd
    exact ⟨v, hv, hctx.inv.good_data hls hny hd hv t⟩


/-- The latest version v of a node y reachable at K, not in D after T(K), with
no version after K: its references to its live children lead, with Rule R,
to their latest versions. -/
theorem KCtx.fresh_ref (hk : KCtx sp db dbK K) (hctx : PCtx sp db k) (hsK : lastSp db.S ≤ K)
    {y : NodeId} (hDK : inD dbK.D y = false) (hwy : written sp y = true)
    (hr : reachable sp db.P K y = true) {v : Version V} (hv : db.S.lv y = some v)
    (hvK : ∀ r w, K < r → db.S.versionAt r y = some w → False) {z : NodeId}
    (hz : z ∈ sp.live v.hist) :
    ruleRRef db.S (lastSp db.S) z (v.ref? z) = (db.S.lv z).map (·.recNo) ∧ (db.S.lv z).isSome := by
  have hls := hctx.ls
  have hrK : reachable sp dbK.P K y = true := by rw [← hk.reachable_eq hls (Nat.le_refl K)]; exact hr
  have hvKl : dbK.S.lv y = some v := by rw [← hk.lv_eq hvK]; exact hv
  obtain ⟨hzD, hzref⟩ := hk.fresh y v hrK hDK hvKl z hz
  -- z is a node of dbK, a live child of y at K.
  obtain ⟨-, -, nyK, hnyK, hvhK, -, -⟩ := hk.inv.version_node (hk.inv.lv_at hvKl)
  obtain ⟨e, he, hze⟩ := hls _ _ hz
  have he' : e ∈ nyK.hist := by rw [hvhK] at he; exact (mem_upTo.mp he).1
  obtain ⟨nzK, hnzK, hlt⟩ := hk.inv.ptrs y nyK hnyK e he' z hze
  have hzr : z ≠ SIS.root := hk.inv.ptr_ne_root hnyK he' hze
  -- z has a latest version by K.
  obtain ⟨uK, huK⟩ : ∃ u, dbK.S.lv z = some u := by
    cases hdz : nzK.isData
    · have hlive : z ∈ sp.live (nyK.hist.upTo K) := by
        have hvk : v.hist.upTo K = v.hist := by
          apply upTo_of_forall
          intro e1 he1
          have := (mem_upTo.mp (hvhK ▸ he1)).2
          obtain ⟨R0, hR0, -, -⟩ := versionAt_spec (hk.inv.lv_at hvKl)
          obtain ⟨hlt0, -⟩ := List.getElem?_eq_some_iff.mp hR0
          have := hk.inv.len
          omega
        have hidx : isIndex dbK.P y = true := by
          cases hdy : nyK.isData
          · simp [isIndex, hnyK, hdy]
          · have := hk.inv.data y nyK hnyK hdy e he'
            rw [this] at hze; cases hze
        have hcl : dirty sp dbK.S dbK.P K y = false := by
          cases hc : dirty sp dbK.S dbK.P K y
          · rfl
          · have := hk.inv.inv2 y hidx hwy hc
            rw [hDK] at this; cases this
        obtain ⟨v', hv', hg⟩ := (dirty_false_iff sp dbK.S dbK.P K y).mp hcl
        rw [hvKl, Option.some.injEq] at hv'
        subst hv'
        have hgK := hg K (Nat.le_refl _) hrK
        rw [good_iff] at hgK
        obtain ⟨⟨n', hn', hc⟩, -⟩ := hgK
        rw [(hk.inv.version_node (hk.inv.lv_at hvKl)).1, hnyK, Option.some.injEq] at hn'
        subst hn'
        rw [← hc, hvk]; exact hz
      have hzrK : reachable sp dbK.P K z = true := by
        rw [reachable_iff] at hrK ⊢
        exact Reach.child hrK hnyK hlive hnzK hlt
      have hzidx : isIndex dbK.P z = true := by simp [isIndex, hnzK, hdz]
      have hzcl : dirty sp dbK.S dbK.P K z = false := by
        cases hc : dirty sp dbK.S dbK.P K z
        · rfl
        · have := hk.inv.inv2 z hzidx (written_of_ne_root sp hzr) hc
          rw [hzD] at this; cases this
      obtain ⟨uK, huK, -⟩ := (dirty_false_iff sp dbK.S dbK.P K z).mp hzcl
      exact ⟨uK, huK⟩
    · obtain ⟨uK, huK, -⟩ := hk.inv.dataV z nzK hnzK hdz
      exact ⟨uK, huK⟩
  rw [hzref, huK]
  simp only [Option.map_some]
  have huKS : db.S.versionAt uK.recNo z = some uK := by
    have := hk.inv.lv_at huK
    rw [hk.pre, versionAt_take] at this
    split at this
    · exact this
    · cases this
  by_cases hlz : ∃ r w, K < r ∧ db.S.versionAt r z = some w
  · obtain ⟨r, w, hrK', hw⟩ := hlz
    cases hnw : newest db.S (lastSp db.S) z with
    | none =>
      have := (newest_eq_none_iff db.S (lastSp db.S) z).mp hnw r (by omega)
      rw [hw] at this; cases this
    | some w' =>
      obtain ⟨r2, -, hw2, hle⟩ := newest_ge hnw hw
      obtain ⟨-, hrec2, -⟩ := hctx.inv.version_node hw2
      have huK_le : uK.recNo ≤ K := by
        obtain ⟨R0, hR0, -, -⟩ := versionAt_spec (hk.inv.lv_at huK)
        obtain ⟨hlt0, -⟩ := List.getElem?_eq_some_iff.mp hR0
        have := hk.inv.len
        omega
      rw [newest_lv hnw]
      refine ⟨?_, rfl⟩
      unfold ruleRRef
      rw [hnw]
      simp only [Option.map_some]
      have : uK.recNo < w'.recNo := by omega
      simp [this]
  · have hvKz : ∀ r w, K < r → db.S.versionAt r z = some w → False :=
      fun r w h1 h2 => hlz ⟨r, w, h1, h2⟩
    have hlvz : db.S.lv z = some uK := by rw [hk.lv_eq hvKz]; exact huK
    rw [hlvz]
    refine ⟨?_, rfl⟩
    have := ruleR_lv db.S (lastSp db.S) z
    rw [hlvz] at this
    exact this

/-- CF: the latest version v of a node y without a canonical object, reachable at
K, with no version after K: its references to its live children lead, with
Rule R, to their latest versions. -/
theorem Cover.cf (hm : Cover db K m) (hk : KCtx sp db dbK K) (hctx : PCtx sp db k)
    {y : NodeId} (hnc : m.canonicalOf y = none) (hr : reachable sp db.P K y = true)
    {v : Version V} (hv : db.S.lv y = some v)
    (hvK : ∀ r w, K < r → db.S.versionAt r y = some w → False) {z : NodeId}
    (hz : z ∈ sp.live v.hist) :
    ruleRRef db.S (lastSp db.S) z (v.ref? z) = (db.S.lv z).map (·.recNo) ∧ (db.S.lv z).isSome :=
  hk.fresh_ref hctx hm.sK (hm.notD hk hnc hvK) (written_of_ne_root sp (hm.ne_root hnc)) hr hv hvK hz

end Logic

end SIS
