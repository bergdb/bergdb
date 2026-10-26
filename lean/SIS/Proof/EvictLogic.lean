/-
Proofs for stage 2 (bergdb item 001, WP E3), part 1: the logical facts that the
design of bergdb 001-08, 5.4, rests on. With BergDB's bookkeeping
(marking and `javaTest`) and A6', after every transaction of a run: D is closed
upward (every current ancestor of a node of D is in D), and a current node that
is not in D has no pointee in D, and its latest version names the latest
version of every pointee.
-/
import SIS.Proof.Still
import SIS.Proof.StepInv
import SIS.Proof.Newer
import SIS.Evict

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- D is closed upward at time k: every current ancestor of a node of D is in
D (`EvLogic.closed`; T12 needs it without A6', bergdb item 001, WP R5). -/
def DClosed (sp : Spec V T) (db : DB V T) (k : Nat) : Prop :=
  ∀ x n y, written sp x = true → reachable sp db.P k x = true → db.P.get? x = some n →
    inD db.D y = true → y ∈ reachFrom sp db.P k x n → inD db.D x = true

/-- The logical facts of stage 2 for state db at time k. -/
structure EvLogic (sp : Spec V T) (db : DB V T) (k : Nat) : Prop where
  /-- D is closed upward. -/
  closed : ∀ x n y, written sp x = true → reachable sp db.P k x = true → db.P.get? x = some n →
    inD db.D y = true → y ∈ reachFrom sp db.P k x n → inD db.D x = true
  /-- A current node that is not in D: no pointee in D, and its latest version
  names the latest version of every pointee. -/
  clean : ∀ x n, written sp x = true → reachable sp db.P k x = true → db.P.get? x = some n →
    inD db.D x = false → ∀ y ∈ pointees sp n.hist,
      inD db.D y = false ∧ ∃ v, db.S.lv x = some v ∧ v.ref? y = (db.S.lv y).map (·.recNo)

/-- The nodes below a node below x are below x. -/
theorem reachFrom_trans' (sp : Spec V T) {P : Struct V} {t : Time} :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b → P.get? x = some n →
      ∀ y m, y ∈ reachFrom sp P t x n → P.get? y = some m →
        ∀ w ∈ reachFrom sp P t y m, w ∈ reachFrom sp P t x n := by
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb hx y m hy hym w hw
    have hy' := hy
    rw [reachFrom_eq] at hy'
    simp only [List.mem_cons, List.mem_flatMap] at hy'
    rcases hy' with rfl | ⟨z, hz, hyz⟩
    · rw [hx, Option.some.injEq] at hym
      subst hym
      exact hw
    · split at hyz
      · rename_i mz hmz
        split at hyz
        · rename_i hlt
          exact reachFrom_child_sub sp hz hmz hlt w (ih z mz (by omega) hmz y m hyz hym w hw)
        · simp at hyz
      · simp at hyz

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- With nothing changed below node x now, the nodes below x now are below x at
k, with the same nodes in P before and after. -/
theorem step_reachFrom_unchanged (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k) :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b →
      (parts sp al db tr).P.get? x = some n → db.P.get? x = some n →
      (∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n, changed (parts sp al db tr).c z = false) →
      ∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n,
        z ∈ reachFrom sp db.P k x n ∧ (parts sp al db tr).P.get? z = db.P.get? z := by
  have hlen := hinv.len
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb hx hx0 hun z hz
    have hnt : ∀ e ∈ n.hist, e.time ≤ k := hinv.times x n hx0
    have hup : n.hist.upTo (k + 1) = n.hist.upTo k := by
      rw [upTo_of_forall _ _ (fun e he => by have := hnt e he; omega),
        upTo_of_forall _ _ (fun e he => hnt e he)]
    have hz' := hz
    rw [reachFrom_eq] at hz'
    simp only [List.mem_cons, List.mem_flatMap] at hz'
    rcases hz' with rfl | ⟨y, hy, hzy⟩
    · exact ⟨self_mem_reachFrom sp _ _ _ _, by rw [hx, hx0]⟩
    · split at hzy
      · rename_i m hm
        split at hzy
        · rename_i hlt
          -- y is an old node with no new entries: the same node before.
          have hy0 : y ∈ sp.live (n.hist.upTo k) := by rw [← hup]; exact hy
          obtain ⟨e, he, hye⟩ := hsp.liveSub _ _ hy0
          obtain ⟨m0, hm0, -⟩ := hinv.ptrs x n hx0 e (mem_upTo.mp he).1 y hye
          have hyz : y ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n :=
            reachFrom_child_sub sp hy hm hlt y (self_mem_reachFrom sp _ _ y m)
          have hcy := hun y hyz
          have hadds : addsFor (parts sp al db tr).c (k + 1) y = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro e' he'
            obtain ⟨-, ha⟩ := mem_addsFor.mp he'
            unfold changed at hcy
            rw [Bool.or_eq_false_iff, List.any_eq_false, List.any_eq_false] at hcy
            exact hcy.2 _ ha (by simp)
          have hmy := step_P_old sp al db tr hlen hm0
          rw [hadds, List.append_nil, hm, Option.some.injEq] at hmy
          have hmm : m = m0 := by rw [hmy]
          subst hmm
          obtain ⟨h1, h2⟩ := ih y m (by omega) hm hm0
            (fun z' hz' => hun z' (reachFrom_child_sub sp hy hm hlt z' hz')) z hzy
          refine ⟨reachFrom_child_sub sp hy0 hm0 hlt z h1, h2⟩
        · simp at hzy
      · simp at hzy

/-- A pointee of a node is on a lower level. -/
theorem pointee_lvl_lt {P : Struct V} {k : Nat} (hpf : PFacts sp P k) {x : NodeId} {n : Node V}
    (hx : P.get? x = some n) {y : NodeId} (hy : y ∈ pointees sp n.hist) :
    lvlOf P y < lvlOf P x := by
  rw [mem_pointees] at hy
  obtain ⟨e, he, hye⟩ := hy
  obtain ⟨m, hm, hlt⟩ := hpf.ptrs x n hx e he y hye
  simp only [lvlOf, hm, hx, Option.map_some, Option.getD_some]
  exact hlt

/-- BergDB's test (Rule A): a taken node is put back exactly when one of its
pointees is in the new D. Its pointees are on lower levels, so those that are
taken are tested before it. -/
theorem step_java_pointee (hj : al.stillDirty = javaTest sp) (hsp : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) {nx : Node V}
    (hnx : (parts sp al db tr).P.get? x = some nx) :
    x ∈ (parts sp al db tr).r7.2 ↔
      ∃ z ∈ pointees sp nx.hist, inD (parts sp al db tr).r7.1 z = true := by
  have hlen := hinv.len
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  obtain ⟨pre, post, hsplit, hxpre, hxpost, hdis, hpost⟩ := step_taken_split sp al db tr hinv hx
  obtain ⟨M0, hM0, hst⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) pre
    (parts sp al db tr).D2 []
  have hr7 : (parts sp al db tr).r7 = stillDirtyOf al (parts sp al db tr).S'
      (parts sp al db tr).P (parts sp al db tr).D2 (k + 1) (pre ++ x :: post) := by
    rw [parts_r7, hlen, hsplit]
  unfold stillDirtyOf at hr7
  rw [List.foldl_append, hst, List.foldl_cons] at hr7
  have hshape := step_r7_shape sp al db tr hlen
  -- The test of x sees D2 and the nodes of pre put back (M0).
  have htest_iff : al.stillDirty (parts sp al db tr).S' (parts sp al db tr).P
      ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) (k + 1) x = true ↔
      ∃ z ∈ pointees sp nx.hist,
        inD ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) z = true := by
    rw [hj]
    simp only [javaTest, hnx, List.any_eq_true]
  by_cases htest : al.stillDirty (parts sp al db tr).S' (parts sp al db tr).P
      ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) (k + 1) x = true
  · -- Put back.
    simp only [htest, ↓reduceIte] at hr7
    obtain ⟨M1, -, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) post
      ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1)) ++ [(x, k + 1)]) ([] ++ M0 ++ [x])
    rw [h1] at hr7
    constructor
    · intro _
      obtain ⟨z, hz, hzin⟩ := htest_iff.mp htest
      refine ⟨z, hz, ?_⟩
      rw [hr7]
      rw [inD_iff] at hzin ⊢
      obtain ⟨d, hd⟩ := hzin
      exact ⟨d, List.mem_append_left _ (List.mem_append_left _ hd)⟩
    · intro _
      rw [hr7]
      simp
  · -- Not put back: no pointee in the new D.
    simp only [htest, Bool.false_eq_true, ↓reduceIte] at hr7
    obtain ⟨M1, hM1, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) post
      ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) ([] ++ M0)
    rw [h1] at hr7
    constructor
    · intro hx7
      exfalso
      rw [hr7] at hx7
      simp only [List.nil_append, List.mem_append] at hx7
      rcases hx7 with h | h
      · exact hxpre (hM0.subset h)
      · exact hxpost (hM1.subset h)
    · rintro ⟨z, hz, hzin⟩
      exfalso
      apply htest
      apply htest_iff.mpr
      refine ⟨z, hz, ?_⟩
      rw [hr7] at hzin
      simp only [inD_iff] at hzin ⊢
      obtain ⟨d, hd⟩ := hzin
      simp only [List.mem_append, List.mem_map] at hd
      rcases hd with (hd | ⟨z', hz', hzz⟩) | ⟨z', hz', hzz⟩
      · exact ⟨d, List.mem_append_left _ hd⟩
      · exact ⟨d, List.mem_append_right _ (List.mem_map.mpr ⟨z', hz', hzz⟩)⟩
      · -- z was put back while testing post: it is on a level at least x's.
        exfalso
        have hzeq : z' = z := by simp only [Prod.mk.injEq] at hzz; exact hzz.1
        subst hzeq
        have hzpost : z' ∈ post := hM1.subset hz'
        have hlz := hpost z' hzpost
        have hlt := pointee_lvl_lt sp hpf hnx hz
        omega

/-- The new D is in D1. -/
theorem step_r7_D1 {k : Nat} (hinv : Inv sp db k) {z : NodeId}
    (hz : inD (parts sp al db tr).r7.1 z = true) : inD (parts sp al db tr).D1 z = true := by
  have hshape := step_r7_shape sp al db tr hinv.len
  rw [hshape.1, inD_iff] at hz
  obtain ⟨d, hd⟩ := hz
  rw [inD_iff]
  rcases List.mem_append.mp hd with h | h
  · exact ⟨d, ((step_D2_mem sp al db tr _).mp h).1⟩
  · obtain ⟨z', hz', hzz⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at hzz
    obtain ⟨rfl, -⟩ := hzz
    obtain ⟨d', hd', -⟩ := (step_taken_mem sp al db tr z').mp (hshape.2.subset hz')
    exact ⟨d', hd'⟩

/-- A taken node that is put back is in the new D; so is a node of D2. -/
theorem step_inD_r7_of_put {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).r7.2) : inD (parts sp al db tr).r7.1 x = true := by
  rw [(step_r7_shape sp al db tr hinv.len).1, inD_iff]
  exact ⟨k + 1, List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩

theorem step_inD_r7_of_D2 {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : inD (parts sp al db tr).D2 x = true) : inD (parts sp al db tr).r7.1 x = true := by
  rw [(step_r7_shape sp al db tr hinv.len).1, inD_iff]
  obtain ⟨d, hd⟩ := (inD_iff _ _).mp hx
  exact ⟨d, List.mem_append_left _ hd⟩

/-- A node in D1 is in D, or marked now (with marking), or touched. -/
theorem step_D1_cases (hmk : al.mark = true) {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : inD (parts sp al db tr).D1 x = true) :
    inD db.D x = true ∨ marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = true ∨
      x ∈ (parts sp al db tr).c.touch := by
  obtain ⟨d, hd⟩ := (inD_iff _ _).mp hx
  rcases (step_D1_mem sp al db tr hinv.len _).mp hd with h | ⟨-, h⟩
  · exact Or.inl ((inD_iff _ _).mpr ⟨d, h⟩)
  · right
    rw [parts_gd3, hinv.len, List.mem_filter, List.mem_append] at h
    rcases h.1 with h1 | h1
    · simp only [hmk, ↓reduceIte, markOf, List.mem_mergeSort, List.mem_filter, mem_allIds,
        Bool.and_eq_true] at h1
      exact Or.inl h1.2.2
    · exact Or.inr (mem_touchOf.mp h1).1

/-- With marking, a marked index node not in D is in gd3, but a virtual root. -/
theorem step_gd3_of_marked (hmk : al.mark = true) {k : Nat} (hlen : db.S.length = k + 1)
    {x : NodeId} {n : Node V} (hx : (parts sp al db tr).P.get? x = some n)
    (hi : isIndex (parts sp al db tr).P x = true) (hD : inD db.D x = false)
    (hw : written sp x = true)
    (hm : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = true) :
    x ∈ (parts sp al db tr).gd3 := by
  rw [parts_gd3, List.mem_filter, List.mem_append]
  refine ⟨Or.inl ?_, hw⟩
  rw [hlen]
  simp only [hmk, ↓reduceIte, markOf, List.mem_mergeSort, List.mem_filter, mem_allIds,
    Bool.and_eq_true]
  exact ⟨by simp [hx], ⟨hi, by simp [hD]⟩, hm⟩

/-- A node reachable before the step, with a touched node below it then, is in
D1: it is touched too (StepOK.touchUp; bergdb item 001, WP R3). -/
theorem step_touch_D1 {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x y : NodeId} {n : Node V}
    (hw : written sp x = true) (hrk : reachable sp db.P k x = true) (hx0 : db.P.get? x = some n)
    (hy : y ∈ (parts sp al db tr).c.touch) (hyx : y ∈ reachFrom sp db.P k x n) :
    inD (parts sp al db tr).D1 x = true := by
  rcases hstep.touchUp y hy x n (by simpa using hrk) hx0 (by simpa using hyx) with h | ⟨h1, h2⟩
  · cases hxD : inD db.D x
    · have hxi : isIndex (parts sp al db tr).P x = true := by
        rw [step_isIndex_old sp al db tr hinv.len (by simp [hx0])]; exact hstep.touchIndex x h
      exact (inD_iff _ _).mpr ⟨k + 1, (step_D1_mem sp al db tr hinv.len _).mpr
        (Or.inr ⟨rfl, step_gd3_of_touch sp al db tr h hxi hxD hw⟩)⟩
    · obtain ⟨d, hd⟩ := (inD_iff _ _).mp hxD
      exact (inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩
  · exfalso; rw [h2] at hw; simp [written, h1] at hw

/-- A node that is not marked now, reachable now: it was reachable before, it
is the same node, and the nodes below it are those below it before. -/
theorem step_unmarked_old (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId} {n : Node V}
    (hr : reachable sp (parts sp al db tr).P (k + 1) x = true)
    (hx : (parts sp al db tr).P.get? x = some n)
    (hm : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = false) :
    db.P.get? x = some n ∧ reachable sp db.P k x = true ∧
      (∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n, changed (parts sp al db tr).c z = false) ∧
      ∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n,
        z ∈ reachFrom sp db.P k x n ∧ (parts sp al db tr).P.get? z = db.P.get? z := by
  have hlen := hinv.len
  have hP := parts_P' sp al db tr hlen
  have hun : ∀ z ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n,
      changed (parts sp al db tr).c z = false := by
    unfold marked at hm
    rw [hr, hx] at hm
    simp only [Bool.true_and, List.any_eq_false] at hm
    intro z hz
    cases h1 : changed (parts sp al db tr).c z
    · rfl
    · exact absurd h1 (hm z hz)
  have hcx := hun x (self_mem_reachFrom sp _ _ x n)
  -- x is old: a new node is changed.
  obtain ⟨n0, hn0⟩ : ∃ n0, db.P.get? x = some n0 := by
    rcases step_node_cases sp al db tr hlen hx with ⟨n1, hn1, -⟩ | ⟨-, nn, hnn, hid, -⟩
    · exact ⟨n1, hn1⟩
    · exfalso
      unfold changed at hcx
      rw [Bool.or_eq_false_iff, List.any_eq_false] at hcx
      exact hcx.1 nn hnn (by simp [hid])
  have hadds : addsFor (parts sp al db tr).c (k + 1) x = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro e he
    obtain ⟨-, ha⟩ := mem_addsFor.mp he
    unfold changed at hcx
    rw [Bool.or_eq_false_iff, List.any_eq_false, List.any_eq_false] at hcx
    exact hcx.2 _ ha (by simp)
  have hm0 := step_P_old sp al db tr hlen hn0
  rw [hadds, List.append_nil, hx, Option.some.injEq] at hm0
  have hnn : n = n0 := by rw [hm0]
  subst hnn
  have hrk : reachable sp db.P k x = true := by
    rcases hstep.noRes x (by rw [← hP]; exact hr) with h1 | h1
    · simpa using h1
    · exfalso
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp h1
      have := hstep.fresh nn hnn
      rw [hid, hn0] at this
      simp at this
  exact ⟨hn0, hrk, hun, step_reachFrom_unchanged sp al db tr hsp hinv (n.level + 1) x n
    (Nat.lt_succ_self _) hx hn0 hun⟩

/-- D stays closed upward (F1-008-08's T15, in bergdb's model): marking marks
the current ancestors of a changed node, and Rule A puts back a taken node
with a pointee in the new D, lowest level first. -/
theorem step_closed (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hsp : SpecOK sp)
    {k : Nat} (hinv : Inv sp db k) (hcl : DClosed sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b → written sp x = true →
      reachable sp (parts sp al db tr).P (k + 1) x = true → (parts sp al db tr).P.get? x = some n →
      ∀ y, inD (parts sp al db tr).r7.1 y = true → y ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n →
        inD (parts sp al db tr).r7.1 x = true := by
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb hw hr hx y hy hyx
    -- y = x, or y is below a live child z of x.
    have hyx' := hyx
    rw [reachFrom_eq] at hyx'
    simp only [List.mem_cons, List.mem_flatMap] at hyx'
    rcases hyx' with rfl | ⟨z, hz, hyz⟩
    · exact hy
    · split at hyz
      · rename_i m hm
        split at hyz
        · rename_i hlt
          by_cases hD1 : inD (parts sp al db tr).D1 x = true
          · by_cases ht : x ∈ (parts sp al db tr).taken
            · -- Taken: z is in the new D (by induction), so Rule A puts x back.
              have hzr : reachable sp (parts sp al db tr).P (k + 1) z = true :=
                (reachable_iff _ _ _ _).mpr (Reach.child ((reachable_iff _ _ _ _).mp hr) hx hz hm hlt)
              have hzw : written sp z = true := by
                apply written_of_ne_root
                obtain ⟨e, he, hze⟩ := hsp.liveSub _ _ hz
                exact hpf.ptr_ne_root sp hx (mem_upTo.mp he).1 hze
              have hzD := ih z m (by omega) hzw hzr hm y hy hyz
              exact step_inD_r7_of_put sp al db tr hinv
                ((step_java_pointee sp al db tr hj hsp hinv hstep ht hx).mpr
                  ⟨z, mem_pointees_of_live hsp.liveSub hz, hzD⟩)
            · obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD1
              exact step_inD_r7_of_D2 sp al db tr hinv (step_D2_of_not_taken sp al db tr hd ht)
          · exfalso
            -- x is not in D1: not in D, not marked; nothing below it changed.
            have hxD : inD db.D x = false := by
              cases h : inD db.D x
              · rfl
              · exfalso
                obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
                exact hD1 ((inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩)
            have hmx : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = false := by
              cases h : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x
              · rfl
              · exfalso
                apply hD1
                have hxi : isIndex (parts sp al db tr).P x = true := by
                  simp only [isIndex, hx]
                  cases hd : n.isData
                  · rfl
                  · exfalso
                    obtain ⟨e, he, hze⟩ := hsp.liveSub _ _ hz
                    rw [hpf.data x n hx hd e (mem_upTo.mp he).1] at hze
                    simp at hze
                have hg : x ∈ (parts sp al db tr).gd3 :=
                  step_gd3_of_marked sp al db tr hmk hinv.len hx hxi hxD hw h
                exact (inD_iff _ _).mpr
                  ⟨k + 1, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inr ⟨rfl, hg⟩)⟩
            obtain ⟨hx0, hrk, hun, hsame⟩ := step_unmarked_old sp al db tr hsp hinv hstep hr hx hmx
            have hyfull : y ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n :=
              reachFrom_child_sub sp hz hm hlt y hyz
            obtain ⟨hy0, -⟩ := hsame y hyfull
            -- y is in D1: in D, or marked; marked would put a changed node below x.
            rcases step_D1_cases sp al db tr hmk hinv (step_r7_D1 sp al db tr hinv hy) with hyD | hym | hyt
            rotate_right
            · exact hD1 (step_touch_D1 sp al db tr hinv hstep hw hrk hx0 hyt hy0)
            · rw [hcl x n y hw hrk hx0 hyD hy0] at hxD
              simp at hxD
            · unfold marked at hym
              rw [Bool.and_eq_true] at hym
              obtain ⟨-, hym⟩ := hym
              split at hym
              · rename_i my hmy
                obtain ⟨w, hw', hcw⟩ := List.any_eq_true.mp hym
                have := hun w (reachFrom_trans' sp (n.level + 1) x n (Nat.lt_succ_self _) hx y my
                  hyfull hmy w hw')
                rw [hcw] at this
                simp at this
              · simp at hym
        · simp at hyz
      · simp at hyz

/-- A taken node, written in the new record: its version names, for each
pointee, the latest version in the new stream (its pointees are on lower levels,
so their versions in the record come before its own). -/
theorem step_taken_refs (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) {nx : Node V}
    (hnx : (parts sp al db tr).P.get? x = some nx) :
    ∃ v, (Snew sp al db tr).lv x = some v ∧ ∀ y ∈ pointees sp nx.hist,
      v.ref? y = ((Snew sp al db tr).lv y).map (·.recNo) := by
  have hlen := hinv.len
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  obtain ⟨pre, post, hsplit, -, -, -, hpost⟩ := step_taken_split sp al db tr hinv hx
  obtain ⟨wpre, hwpre⟩ : ∃ w, w = writeAll sp db.S (k + 1) (parts sp al db tr).P pre
      (parts sp al db tr).vs0 := ⟨_, rfl⟩
  obtain ⟨vx, hvx⟩ : ∃ v, v = mkVersion sp (db.S.building wpre) (k + 1) x nx := ⟨_, rfl⟩
  have hvs : (parts sp al db tr).vs =
      writeAll sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [vx]) := by
    rw [parts_vs, hlen, hsplit, writeAll_split sp _ _ _ hnx, ← hwpre, ← hvx]
  have hpre_vs : wpre ++ [vx] <+: (parts sp al db tr).vs := by
    rw [hvs]; exact writeAll_prefix sp _ _ _ _ _
  have hw_vs : wpre <+: (parts sp al db tr).vs := (List.prefix_append _ _).trans hpre_vs
  have hvx_mem : vx ∈ (parts sp al db tr).vs := hpre_vs.subset (by simp)
  have hnodup := step_vs_nodup sp al db tr hinv hstep
  have hwnodup : (wpre.map (·.node)).Nodup := (hw_vs.sublist.map _).nodup hnodup
  have hvxnode : vx.node = x := by rw [hvx]; rfl
  have hlvx : (Snew sp al db tr).lv x = some vx := by
    rw [← hvxnode]; exact lv_Snew_written sp al db tr hnodup hvx_mem
  -- The nodes of wpre: the data ids and pre.
  have hwnodes : ∀ z, (∃ u ∈ wpre, u.node = z) ↔ z ∈ dataIds sp al db tr ∨ z ∈ pre := by
    intro z
    have h1 : wpre.map (·.node) = (parts sp al db tr).vs0.map (·.node) ++
        pre.filter (fun z => ((parts sp al db tr).P.get? z).isSome) := by
      rw [hwpre, writeAll_nodes]
    have h2 : (parts sp al db tr).vs0.map (·.node) = (dataIds sp al db tr).filter
        (fun z => ((parts sp al db tr).P.get? z).isSome) := by
      rw [parts_vs0, writeAll_nodes]; simp [dataIds]
    have h3 : (dataIds sp al db tr).filter (fun z => ((parts sp al db tr).P.get? z).isSome) =
        dataIds sp al db tr := by
      apply List.filter_eq_self.mpr
      intro z hz
      obtain ⟨-, n, hn, -⟩ := step_dataIds_spec sp al db tr hinv hstep hz
      simp [hn]
    have h4 : pre.filter (fun z => ((parts sp al db tr).P.get? z).isSome) = pre := by
      apply List.filter_eq_self.mpr
      intro z hz
      have : z ∈ (parts sp al db tr).taken := by rw [hsplit]; simp [hz]
      exact isSome_of_isIndex (step_taken_index sp al db tr hinv this)
    rw [h2, h3, h4] at h1
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : u.node ∈ wpre.map (·.node) := List.mem_map_of_mem hu
      rw [h1] at this
      exact List.mem_append.mp this
    · intro hz
      have : z ∈ wpre.map (·.node) := by rw [h1]; exact List.mem_append.mpr hz
      simpa using this
  refine ⟨vx, hlvx, fun y hy => ?_⟩
  rw [hvx, ref?_mkVersion]
  simp only [hy, ↓reduceIte]
  have hlt := pointee_lvl_lt sp hpf hnx hy
  rw [lv_building]
  by_cases hwr : ∃ w ∈ (parts sp al db tr).vs, w.node = y
  · obtain ⟨w, hw, hwy⟩ := hwr
    rw [← hwy, lv_Snew_written sp al db tr hnodup hw]
    -- y's version is in wpre: y is a data node of the change or in pre.
    have hyw : y ∈ dataIds sp al db tr ∨ y ∈ pre := by
      rcases (step_written_iff sp al db tr hinv hstep y).mp ⟨w, hw, hwy⟩ with h | h
      · exact Or.inl h
      · right
        rw [hsplit] at h
        rcases List.mem_append.mp h with h | h
        · exact h
        · rcases List.mem_cons.mp h with h | h
          · subst h; omega
          · have := hpost y h; omega
    obtain ⟨u, hu, huy⟩ := (hwnodes y).mpr hyw
    have huw : u = w := by
      have hu' : u ∈ (parts sp al db tr).vs := hw_vs.subset hu
      exact eq_of_map_nodup hnodup hu' hw (by rw [huy, hwy])
    subst huw
    rw [find?_node_of_mem hwnodup hu rfl, Option.some_or]
  · have hnw : ∀ w ∈ (parts sp al db tr).vs, w.node ≠ y := fun w hw hwy => hwr ⟨w, hw, hwy⟩
    rw [lv_Snew_not_written sp al db tr hnw]
    have : wpre.find? (fun v => v.node == y) = none := by
      rw [List.find?_eq_none]
      intro w hw
      simpa using hnw w (hw_vs.subset hw)
    rw [this, Option.none_or]

/-- A current node that is not in the new D: its pointees are not in the new D,
and its latest version names their latest versions. -/
theorem step_clean (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hsp : SpecOK sp)
    {k : Nat} (hinv : Inv sp db k) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hA6 : adoptAt sp (parts sp al db tr).P (k + 1)) (hA6k : adoptAt sp db.P k) :
    ∀ x n, written sp x = true → reachable sp (parts sp al db tr).P (k + 1) x = true →
      (parts sp al db tr).P.get? x = some n → inD (parts sp al db tr).r7.1 x = false →
      ∀ y ∈ pointees sp n.hist, inD (parts sp al db tr).r7.1 y = false ∧
        ∃ v, (Snew sp al db tr).lv x = some v ∧ v.ref? y = ((Snew sp al db tr).lv y).map (·.recNo) := by
  have hpf := step_pfacts sp al db tr hsp hinv hstep
  intro x n hw hr hx hxD y hy
  by_cases hD1 : inD (parts sp al db tr).D1 x = true
  · -- In D1 and not in the new D: taken, and not put back.
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hD1
    have ht : x ∈ (parts sp al db tr).taken := by
      apply Classical.byContradiction
      intro ht
      rw [step_inD_r7_of_D2 sp al db tr hinv (step_D2_of_not_taken sp al db tr hd ht)] at hxD
      simp at hxD
    have hn7 : x ∉ (parts sp al db tr).r7.2 := by
      intro h
      rw [step_inD_r7_of_put sp al db tr hinv h] at hxD
      simp at hxD
    have hyD : inD (parts sp al db tr).r7.1 y = false := by
      cases h : inD (parts sp al db tr).r7.1 y
      · rfl
      · exact absurd ((step_java_pointee sp al db tr hj hsp hinv hstep ht hx).mpr ⟨y, hy, h⟩) hn7
    obtain ⟨v, hv, href⟩ := step_taken_refs sp al db tr hsp hinv hstep ht hx
    exact ⟨hyD, v, hv, href y hy⟩
  · -- Not in D1: not in D, not marked; as it was, and so are its pointees.
    have hxD0 : inD db.D x = false := by
      cases h : inD db.D x
      · rfl
      · exfalso
        obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
        exact hD1 ((inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩)
    have hmx : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x = false := by
      cases h : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) x
      · rfl
      · exfalso
        apply hD1
        -- x has a pointee, so it is an index node.
        have hxi : isIndex (parts sp al db tr).P x = true := by
          simp only [isIndex, hx]
          cases hd : n.isData
          · rfl
          · exfalso
            obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
            rw [hpf.data x n hx hd e he] at hye
            simp at hye
        have hg : x ∈ (parts sp al db tr).gd3 :=
          step_gd3_of_marked sp al db tr hmk hinv.len hx hxi hxD0 hw h
        exact (inD_iff _ _).mpr
          ⟨k + 1, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inr ⟨rfl, hg⟩)⟩
    obtain ⟨hx0, hrk, hun, hsame⟩ := step_unmarked_old sp al db tr hsp hinv hstep hr hx hmx
    obtain ⟨hyD0, v, hv, href⟩ := hev.clean x n hw hrk hx0 hxD0 y hy
    -- y is not marked: it would be below x (a live child, or by A6'), or not reachable.
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
    obtain ⟨my, hmy, hlt⟩ := hpf.ptrs x n hx e he y hye
    have hym : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) y = false := by
      cases h : marked sp (parts sp al db tr).P (parts sp al db tr).c (k + 1) y
      · rfl
      · exfalso
        have hm' := h
        unfold marked at hm'
        rw [Bool.and_eq_true] at hm'
        obtain ⟨hyr, hm'⟩ := hm'
        rw [hmy] at hm'
        obtain ⟨w, hw', hcw⟩ := List.any_eq_true.mp hm'
        -- y is below x now.
        have hyx : y ∈ reachFrom sp (parts sp al db tr).P (k + 1) x n := by
          by_cases hl : y ∈ sp.live (n.hist.upTo (k + 1))
          · exact reachFrom_child_sub sp hl hmy hlt y (self_mem_reachFrom sp _ _ y my)
          · rcases hA6 x n hr hx y hy hl with ⟨ny, hny, hdy⟩ | hnr | hbelow
            · rw [hmy, Option.some.injEq] at hny
              -- A data node has no node below it but itself, and it is not changed now.
              exfalso
              have hdy' : my.isData = true := by rw [hny]; exact hdy
              have hwy : w = y := by
                rw [reachFrom_eq] at hw'
                simp only [List.mem_cons, List.mem_flatMap] at hw'
                rcases hw' with h1 | ⟨z, hz, -⟩
                · exact h1
                · exfalso
                  obtain ⟨e', he', hze⟩ := hsp.liveSub _ _ hz
                  rw [hpf.data y my hmy hdy' e' (mem_upTo.mp he').1] at hze
                  simp at hze
              rw [hwy] at hcw
              obtain ⟨m0, hm0, -⟩ := hinv.ptrs x n hx0 e he y hye
              unfold changed at hcw
              rw [Bool.or_eq_true] at hcw
              rcases hcw with hcw | hcw
              · obtain ⟨nn, hnn, hid⟩ := List.any_eq_true.mp hcw
                have := hstep.fresh nn hnn
                rw [show nn.id = y by simpa using hid, hm0] at this
                simp at this
              · obtain ⟨a, ha, haw⟩ := List.any_eq_true.mp hcw
                have haw' : a.1 = y := by simpa using haw
                have h1 := hstep.dataFixed a ha m0 (by rw [haw']; exact hm0)
                have hmy' := step_P_old sp al db tr hinv.len hm0
                rw [hmy, Option.some.injEq] at hmy'
                have hk : my.isData = m0.isData := by rw [hmy']
                rw [hk, h1] at hdy'
                simp at hdy'
            · rw [hyr] at hnr; simp at hnr
            · exact hbelow
        have := hun w (reachFrom_trans' sp (n.level + 1) x n (Nat.lt_succ_self _) hx y my hyx hmy w hw')
        rw [hcw] at this
        simp at this
    -- So y is not in D1, hence not in the new D, and not written now; were y
    -- touched, it would be below x before the step (a live child, or by A6'),
    -- and x touched too.
    have hyD1 : inD (parts sp al db tr).D1 y = false := by
      cases h : inD (parts sp al db tr).D1 y
      · rfl
      · rcases step_D1_cases sp al db tr hmk hinv h with h1 | h1 | h1
        · rw [h1] at hyD0; simp at hyD0
        · rw [h1] at hym; simp at hym
        · exfalso
          apply hD1
          obtain ⟨m0, hm0, hlt0⟩ := hinv.ptrs x n hx0 e he y hye
          have hyx : y ∈ reachFrom sp db.P k x n := by
            by_cases hl : y ∈ sp.live (n.hist.upTo k)
            · exact reachFrom_child_sub sp hl hm0 hlt0 y (self_mem_reachFrom sp _ _ y m0)
            · rcases hA6k x n hrk hx0 y hy hl with ⟨ny, hny, hdy⟩ | hnr | hbelow
              · have := hstep.touchIndex y h1
                simp [isIndex, hny, hdy] at this
              · have := hstep.touchReach y h1
                simp only [Nat.add_sub_cancel] at this
                rw [hnr] at this; simp at this
              · exact hbelow
          exact step_touch_D1 sp al db tr hinv hstep hw hrk hx0 h1 hyx
    refine ⟨?_, ?_⟩
    · cases h : inD (parts sp al db tr).r7.1 y
      · rfl
      · rw [step_r7_D1 sp al db tr hinv h] at hyD1; simp at hyD1
    · -- Neither x nor y is written in the new record.
      have hnotw : ∀ z, inD (parts sp al db tr).D1 z = false → (db.P.get? z).isSome →
          ∀ w ∈ (parts sp al db tr).vs, w.node ≠ z := by
        intro z hz hz0 w hw hwz
        rcases (step_written_iff sp al db tr hinv hstep z).mp ⟨w, hw, hwz⟩ with h | h
        · obtain ⟨h0, -⟩ := step_dataIds_spec sp al db tr hinv hstep h
          rw [h0] at hz0; simp at hz0
        · obtain ⟨d, hd, -⟩ := (step_taken_mem sp al db tr z).mp h
          rw [(inD_iff _ _).mpr ⟨d, hd⟩] at hz; simp at hz
      obtain ⟨m0, hm0, -⟩ := hinv.ptrs x n hx0 e he y hye
      have hxD1 : inD (parts sp al db tr).D1 x = false := by simpa using hD1
      refine ⟨v, ?_, ?_⟩
      · rw [lv_Snew_not_written sp al db tr (hnotw x hxD1 (by simp [hx0]))]; exact hv
      · rw [lv_Snew_not_written sp al db tr (hnotw y hyD1 (by simp [hm0]))]; exact href

/-- The logical facts after a transaction. -/
theorem step_evLogic (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hsp : SpecOK sp)
    {k : Nat} (hinv : Inv sp db k) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hA6 : adoptAt sp (parts sp al db tr).P (k + 1)) (hA6k : adoptAt sp db.P k) :
    EvLogic sp (step sp al db tr) (k + 1) where
  closed := by
    intro x n y hw hr hx hy hyx
    rw [step_D] at hy ⊢
    exact step_closed sp al db tr hj hmk hsp hinv hev.closed hstep (n.level + 1) x n (Nat.lt_succ_self _)
      hw hr hx y hy hyx
  clean := by
    intro x n hw hr hx hxD y hy
    rw [step_D] at hxD ⊢
    rw [step_S]
    exact step_clean sp al db tr hj hmk hsp hinv hev hstep hA6 hA6k x n hw hr hx hxD y hy

end Step

/-- The logical facts hold for R(0): D is empty, and every version of R(0) names
the versions of R(0) of its pointees, which are on lower levels, so written
first. -/
theorem evLogic_init (sp : Spec V T) (hok : SpecOK sp) : EvLogic sp (init sp) 0 where
  closed := by
    intro x n y _ _ _ hy
    rw [init_D] at hy
    simp [inD] at hy
  clean := by
    intro x n hw _ hx _ y hy
    rw [init_P] at hx
    refine ⟨by simp [init_D, inD], ?_⟩
    have hB := initVers_built sp
    have hnd := initVers_nodup sp hok
    have hN : ((initVers sp).map (·.node)).Pairwise (fun a b => lev sp.init a ≤ lev sp.init b) := by
      rw [initVers_nodes sp hok]; exact byLevel_pairwise _ _
    obtain ⟨w, hw', hwx⟩ := initVers_mem_node sp hok (by simp [hx]) hw
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hw'
    have hlvx : Stream.lv (init sp).S x = some (initVers sp)[p] := by
      rw [lv_init sp hok]; exact find?_node_of_mem hnd hw' hwx
    refine ⟨_, hlvx, ?_⟩
    obtain ⟨n', hn', heq⟩ := hB p hp
    rw [hwx, hx, Option.some.injEq] at hn'
    subst hn'
    rw [heq, ref?_mkVersion]
    simp only [hy, ↓reduceIte]
    -- y is in R(0), on a lower level, so before x.
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
    obtain ⟨my, hmy, hlt⟩ := hok.initLevels _ (mem_of_get? hx) e he y hye
    have hyw : written sp y = true := by
      apply written_of_ne_root
      intro hyr
      subst hyr
      obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hok.initRoot
      exact absurd (SIS.ptr_ne_root h0 (fun x n hn e he y hy => hok.initLevels _ (mem_of_get? hn) e he y hy)
        (fun x hx => ⟨0, (reachable_iff _ _ _ _).mp (by
          obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp hx
          exact hok.initReachable _ (mem_of_get? hn1))⟩) hx he hye) (by simp)
    obtain ⟨u, hu, huy⟩ := initVers_mem_node sp hok (by simp [hmy]) hyw
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hu
    have hqp : q < p := lower_first hN hp hq (by
      rw [huy, hwx, lev_of_get? hmy, lev_of_get? hx]; exact hlt)
    rw [lv_init sp hok, find?_node_of_mem hnd hu huy, lv_building]
    have hmem : (initVers sp)[q] ∈ (initVers sp).take p :=
      List.mem_iff_getElem.mpr ⟨q, by simp; omega, by simp⟩
    have hnd' : (((initVers sp).take p).map (·.node)).Nodup :=
      ((List.take_sublist p _).map _).nodup hnd
    rw [find?_node_of_mem hnd' hmem huy, Option.some_or]

/-- The logical facts hold after every transaction of a run with BergDB's
bookkeeping (marking and `javaTest`) and A6'. -/
theorem evLogic_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hev : EvictRunOK sp al ts) :
    ∀ j ≤ ts.length, EvLogic sp (st sp al ts j) j := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero => intro _; rw [st_zero]; exact evLogic_init sp hok.1
  | succ j ih =>
    intro hjl
    have hinv := inv_st sp al ts hok hst j (by omega)
    have hstep : StepOK sp (st sp al ts j).P (j + 1)
        (parts sp al (st sp al ts j) ts[j]).c := by
      have h1 := hok.2 j (by omega)
      rw [parts_c, hinv.len]
      simpa [st] using h1
    have hA6 : adoptAt sp (parts sp al (st sp al ts j) ts[j]).P (j + 1) := by
      have h1 := (hev.1 (j + 1) hjl).adopt
      have h2 : (run sp al (ts.take (j + 1))).P = (parts sp al (st sp al ts j) ts[j]).P := by
        rw [← step_P]; rw [← st_succ sp al ts (by omega)]; rfl
      rw [h2] at h1
      exact h1
    have hA6k : adoptAt sp (st sp al ts j).P j := by
      have h1 := (hev.1 j (by omega)).adopt
      simpa [st] using h1
    rw [st_succ sp al ts (by omega)]
    exact step_evLogic sp al (st sp al ts j) ts[j] hj hmk hok.1 hinv (ih (by omega)) hstep hA6 hA6k

end SIS
