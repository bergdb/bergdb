/-
Proofs, part 11b: with a virtual root (`Spec.virt`, option (a) of Q7), one
transaction keeps `VInv`.

Written 2026-10-16 for F1-008-11, WP E3 (bergdb 011-11, 8.2).
-/
import SIS.Proof.StepD

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem written_root_false {sp : Spec V T} (hv : sp.virt = true) : written sp root = false := by
  simp [written, hv]

theorem ne_root_of_written {sp : Spec V T} (hv : sp.virt = true) {x : NodeId}
    (h : written sp x = true) : x ≠ root := by
  intro hx; subst hx; rw [written_root_false hv] at h; simp at h

theorem isTop_iff {sp : Spec V T} {P : Struct V} {x : NodeId} :
    isTop sp P x = true ↔ x ≠ root ∧ ∃ n, P.get? x = some n ∧ sp.topLevel ≤ n.level := by
  simp only [isTop, Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases hn : P.get? x with
    | none => rw [hn] at h2; simp at h2
    | some n => rw [hn] at h2; exact ⟨n, rfl, by simpa using h2⟩
  · rintro ⟨h1, n, hn, hl⟩
    refine ⟨h1, ?_⟩
    rw [hn]; simpa using hl

theorem TopAt.isTop {sp : Spec V T} {P : Struct V} {z : NodeId} {n : Node V} {c : Time}
    (h : TopAt sp P z n c) : isTop sp P z = true :=
  isTop_iff.mpr ⟨h.2.1, n, h.1, h.2.2.1⟩

/-- A root child's entries are all at the time it was created. -/
theorem TopAt.time_of_mem {sp : Spec V T} {P : Struct V} {z : NodeId} {n : Node V} {c : Time}
    (h : TopAt sp P z n c) {e : Entry V} (he : e ∈ n.hist) : e.time = c := h.2.2.2.2.2 e he

theorem TopAt.exists_entry {sp : Spec V T} {P : Struct V} {z : NodeId} {n : Node V} {c : Time}
    (h : TopAt sp P z n c) : ∃ e ∈ n.hist, e.time = c := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ h.2.2.2.2.1
  exact ⟨e, he, h.time_of_mem he⟩

/-- A node is created at one time only. -/
theorem TopAt.time_unique {sp : Spec V T} {P : Struct V} {z : NodeId} {n n' : Node V} {c c' : Time}
    (h : TopAt sp P z n c) (h' : TopAt sp P z n' c') : c = c' := by
  have : n = n' := by have := h.1; rw [h'.1] at this; exact (Option.some.inj this).symm
  subst this
  obtain ⟨e, he, rfl⟩ := h.exists_entry
  exact h'.time_of_mem he

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- The root children that the transaction creates: at most one. -/
def newTops : List NewNode :=
  (parts sp al db tr).c.new.filter (fun nn => decide (sp.topLevel ≤ nn.level))

theorem mem_newTops {nn : NewNode} :
    nn ∈ newTops sp al db tr ↔ nn ∈ (parts sp al db tr).c.new ∧ sp.topLevel ≤ nn.level := by
  simp [newTops]

theorem step_newTops_unique {k : Nat} (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hv : sp.virt = true) {a b : NewNode} (ha : a ∈ newTops sp al db tr)
    (hb : b ∈ newTops sp al db tr) : b = a := by
  rw [mem_newTops] at ha hb
  exact ((hstep.virt hv).newTop a ha.1 ha.2).2.2 b hb.1 hb.2

theorem step_addsFor_root {k : Nat} (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hv : sp.virt = true) (i : Time) :
    addsFor (parts sp al db tr).c i root =
      (newTops sp al db tr).map (fun nn => (⟨i, sp.rootVal nn.id⟩ : Entry V)) := by
  unfold addsFor newTops
  rw [(hstep.virt hv).rootAdds, List.map_map]
  rfl

/-- The root after the transaction: its old entries, and the entry for the new
root child. -/
theorem step_P_root {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {n0 : Node V}
    (h0 : db.P.get? root = some n0) :
    (parts sp al db tr).P.get? root =
      some { n0 with hist := n0.hist ++ (newTops sp al db tr).map (fun nn => (⟨k + 1, sp.rootVal nn.id⟩ : Entry V)) } := by
  rw [step_P_old sp al db tr hinv.len h0, step_addsFor_root sp al db tr hstep hv]

/-- An old root child does not change. -/
theorem step_top_old {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {z : NodeId}
    {m : Node V} (hz : db.P.get? z = some m) (hzr : z ≠ root) (hl : sp.topLevel ≤ m.level) :
    (parts sp al db tr).P.get? z = some m := by
  rw [step_P_old sp al db tr hinv.len hz]
  have : addsFor (parts sp al db tr).c (k + 1) z = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    rw [mem_addsFor] at he
    have := (hstep.virt hv).topFixed (z, e.val) he.2 m hz hzr
    omega
  rw [this, List.append_nil]

theorem step_isTop_old {k : Nat} (hinv : Inv sp db k) {z : NodeId}
    (hz : (db.P.get? z).isSome) : isTop sp (parts sp al db tr).P z = isTop sp db.P z := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hz
  simp only [isTop, step_P_old sp al db tr hinv.len hm, hm]

theorem step_topAt_old {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {z : NodeId}
    {m : Node V} {c : Time} (h : TopAt sp db.P z m c) : TopAt sp (parts sp al db tr).P z m c :=
  ⟨step_top_old sp al db tr hinv hstep hv h.1 h.2.1 h.2.2.1, h.2⟩

theorem step_topAt_back {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {z : NodeId}
    {m : Node V} {c : Time} (h : TopAt sp (parts sp al db tr).P z m c)
    (hz : (db.P.get? z).isSome) : TopAt sp db.P z m c := by
  obtain ⟨m0, hm0⟩ := Option.isSome_iff_exists.mp hz
  have h1 := step_P_old sp al db tr hinv.len hm0
  rw [h.1, Option.some.injEq] at h1
  have hl : sp.topLevel ≤ m0.level := by have := h.2.2.1; rw [h1] at this; exact this
  have h2 := step_top_old sp al db tr hinv hstep hv hm0 h.2.1 hl
  rw [h.1, Option.some.injEq] at h2
  subst h2
  exact ⟨hm0, h.2⟩

/-- The node of a new root child. -/
theorem step_newTop_node {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {nn : NewNode}
    (hnn : nn ∈ (parts sp al db tr).c.new) :
    (parts sp al db tr).P.get? nn.id =
      some { level := nn.level, isData := nn.isData, hist := addsFor (parts sp al db tr).c (k + 1) nn.id } := by
  have hfresh := hstep.fresh nn hnn
  rw [step_P_new sp al db tr hinv.len hfresh]
  cases hm : newNodeOf (parts sp al db tr).c nn.id with
  | none =>
    have := newNodeOf_isSome hnn
    rw [hm] at this; simp at this
  | some m =>
    obtain ⟨nn', hnn', hid, rfl⟩ := newNodeOf_some hm
    have : nn' = nn := eq_of_map_nodup hstep.distinct hnn' hnn hid
    subst this
    simp

theorem step_topAt_new {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {nn : NewNode}
    (hnn : nn ∈ newTops sp al db tr) :
    TopAt sp (parts sp al db tr).P nn.id
      { level := nn.level, isData := nn.isData, hist := addsFor (parts sp al db tr).c (k + 1) nn.id } (k + 1) := by
  rw [mem_newTops] at hnn
  obtain ⟨hd, ⟨a, ha, hai⟩, -⟩ := (hstep.virt hv).newTop nn hnn.1 hnn.2
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hfresh := hstep.fresh nn hnn.1
  refine ⟨step_newTop_node sp al db tr hinv hstep hnn.1, ?_, hnn.2, hd, ?_, ?_⟩
  · intro h; rw [h, h0] at hfresh; simp at hfresh
  · simp only
    intro hnil
    have : (⟨k + 1, a.2⟩ : Entry V) ∈ addsFor (parts sp al db tr).c (k + 1) nn.id :=
      mem_addsFor.mpr ⟨rfl, by rw [← hai]; exact ha⟩
    rw [hnil] at this; simp at this
  · intro e he
    exact (mem_addsFor.mp he).1

/-- A root child after the transaction is old, or the new one. -/
theorem step_topAt_cases {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {z : NodeId}
    {m : Node V} {c : Time} (h : TopAt sp (parts sp al db tr).P z m c) :
    TopAt sp db.P z m c ∨ (c = k + 1 ∧ db.P.get? z = none ∧ ∃ nn ∈ newTops sp al db tr, nn.id = z) := by
  cases hz : db.P.get? z with
  | some m0 => exact Or.inl (step_topAt_back sp al db tr hinv hstep hv h (by simp [hz]))
  | none =>
    right
    rcases step_node_cases sp al db tr hinv.len h.1 with ⟨n1, hn1, -⟩ | ⟨-, nn, hnn, hid, hm⟩
    · rw [hz] at hn1; simp at hn1
    · have hl : sp.topLevel ≤ nn.level := by have := h.2.2.1; rw [hm] at this; exact this
      have hnt : nn ∈ newTops sp al db tr := (mem_newTops sp al db tr).mpr ⟨hnn, hl⟩
      have ht := step_topAt_new sp al db tr hinv hstep hv hnt
      rw [hid] at ht
      exact ⟨(TopAt.time_unique h ht), rfl, nn, hnt, hid⟩

/-! ### The root is never in D -/

theorem step_root_D1 {k : Nat} (hinv : Inv sp db k) (hv : sp.virt = true) :
    ∀ e ∈ (parts sp al db tr).D1, e.1 ≠ root := by
  intro e he hr
  rcases (step_D1_mem sp al db tr hinv.len e).mp he with h | ⟨-, h⟩
  · have := (hinv.vr hv).rootND
    rw [← hr] at this
    have h2 : inD db.D e.1 = true := (inD_iff _ _).mpr ⟨e.2, h⟩
    rw [this] at h2; simp at h2
  · have := step_gd3_written sp al db tr e.1 h
    rw [hr, written_root_false hv] at this; simp at this

theorem step_root_not_taken {k : Nat} (hinv : Inv sp db k) (hv : sp.virt = true) :
    root ∉ (parts sp al db tr).taken := by
  intro h
  obtain ⟨d, hd, -⟩ := (step_taken_mem sp al db tr root).mp h
  exact step_root_D1 sp al db tr hinv hv _ hd rfl

theorem step_rootND {k : Nat} (hinv : Inv sp db k) (hv : sp.virt = true) :
    inD (parts sp al db tr).r7.1 root = false := by
  cases h : inD (parts sp al db tr).r7.1 root
  · rfl
  · exfalso
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
    rw [(step_r7_shape sp al db tr hinv.len).1] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact step_root_D1 sp al db tr hinv hv _ ((step_D2_mem sp al db tr _).mp hd).1 rfl
    · obtain ⟨y, hy, hye⟩ := List.mem_map.mp hd
      simp only [Prod.mk.injEq] at hye
      rw [hye.1] at hy
      exact step_root_not_taken sp al db tr hinv hv ((step_r7_shape sp al db tr hinv.len).2.subset hy)

theorem step_rootNV {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) :
    ∀ (r : Nat) (R : Record V T), (Snew sp al db tr)[r]? = some R → ∀ v ∈ R.vers, v.node ≠ root := by
  intro r R hR v hvR
  rcases step_Snew_cases sp al db tr hinv hR with ⟨-, h⟩ | ⟨rfl, rfl⟩
  · exact (hinv.vr hv).rootNV r R h v hvR
  · intro hr
    have hw := (step_written_iff sp al db tr hinv hstep root).mp ⟨v, hvR, hr⟩
    rcases hw with h | h
    · have h1 := (step_dataIds_spec sp al db tr hinv hstep h).1
      have h2 := hinv.rootIn
      rw [h1] at h2; simp at h2
    · exact step_root_not_taken sp al db tr hinv hv h

/-! ### R4 for old root children -/

theorem topClosure_eq (P : Struct V) (x : NodeId) (n : Node V) :
    topClosure sp P x n = x :: (pointees sp n.hist).flatMap (fun y =>
      match P.get? y with
      | some m => if sp.topLevel ≤ m.level ∧ m.level < n.level then topClosure sp P y m else []
      | none => []) := by
  rw [topClosure]; rfl

/-- The root children that can be reached from an old one do not change. -/
theorem step_topClosure_old {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) :
    ∀ (b : Nat) (z : NodeId) (m : Node V), m.level < b → db.P.get? z = some m →
      topClosure sp (parts sp al db tr).P z m = topClosure sp db.P z m := by
  intro b
  induction b with
  | zero => intro z m h; omega
  | succ b ih =>
    intro z m hb hz
    rw [topClosure_eq sp, topClosure_eq sp]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
    obtain ⟨my, hmy, hlt⟩ := hinv.ptrs z m hz e he y hye
    have hyr : y ≠ root := hinv.ptr_ne_root hz he hye
    rw [hmy]
    by_cases hc : sp.topLevel ≤ my.level ∧ my.level < m.level
    · rw [step_top_old sp al db tr hinv hstep hv hmy hyr hc.1]
      simp only [hc, and_self, ite_true]
      exact ih y my (by omega) hmy
    · rw [step_P_old sp al db tr hinv.len hmy]
      simp only [hc, ite_false]

/-! ### The latest versions of root children name the latest versions -/

/-- The root children after the transaction were all created at some time. -/
theorem step_tops {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) :
    ∀ z, isTop sp (parts sp al db tr).P z = true → ∃ n c, TopAt sp (parts sp al db tr).P z n c := by
  intro z hz
  obtain ⟨hzr, n, hn, hl⟩ := isTop_iff.mp hz
  cases h0 : db.P.get? z with
  | some n0 =>
    have hz0 : isTop sp db.P z = true := by
      rw [← step_isTop_old sp al db tr hinv (by simp [h0])]; exact hz
    obtain ⟨m, c, hm⟩ := (hinv.vr hv).tops z hz0
    exact ⟨m, c, step_topAt_old sp al db tr hinv hstep hv hm⟩
  | none =>
    rcases step_node_cases sp al db tr hinv.len hn with ⟨n1, hn1, -⟩ | ⟨-, nn, hnn, hid, hm⟩
    · rw [h0] at hn1; simp at hn1
    · have hl' : sp.topLevel ≤ nn.level := by rw [hm] at hl; exact hl
      have hnt := (mem_newTops sp al db tr).mpr ⟨hnn, hl'⟩
      have := step_topAt_new sp al db tr hinv hstep hv hnt
      rw [hid] at this
      exact ⟨_, _, this⟩

/-- `VInv.fresh` after the transaction, with BergDB's still-dirty test. A root
child written now and not put back: BergDB's test found none of its pointees
in D, and the pointees on lower levels were written before it in the record.
A root child not written now: the root children it points to are dead
(`VirtStep.dead`) and were clean, so they stay clean, out of D and unwritten. -/
theorem step_fresh (hok : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true)
    (hj : al.stillDirty = javaTest sp) :
    ∀ z v, isTop sp (parts sp al db tr).P z = true → (Snew sp al db tr).lv z = some v →
      (z, v.recNo) ∉ (parts sp al db tr).r7.1 →
      ∀ y ∈ pointees sp v.hist, isTop sp (parts sp al db tr).P y = true →
        inD (parts sp al db tr).r7.1 y = false ∧
          v.ref? y = ((Snew sp al db tr).lv y).map (·.recNo) := by
  intro z v hz hlv hzD y hy hyt
  have hlen := hinv.len
  have hvi := hinv.vr hv
  have hpf := step_pfacts sp al db tr hok hinv hstep
  obtain ⟨nz, cz, hzt⟩ := step_tops sp al db tr hinv hstep hv z hz
  have hnz := hzt.1
  have hzidx : isIndex (parts sp al db tr).P z = true := by simp [isIndex, hnz, hzt.2.2.2.1]
  obtain ⟨ny, cy, hyt'⟩ := step_tops sp al db tr hinv hstep hv y hyt
  have hyidx : isIndex (parts sp al db tr).P y = true := by simp [isIndex, hyt'.1, hyt'.2.2.2.1]
  have hyw : written sp y = true := written_of_ne_root sp hyt'.2.1
  by_cases hzt' : z ∈ (parts sp al db tr).taken
  · -- z is written in the record and not put back.
    obtain ⟨pre, post, hsplit, -, -, -, hpost⟩ := step_taken_split sp al db tr hinv hzt'
    obtain ⟨wpre, hwpre⟩ : ∃ w, w = writeAll sp db.S (k + 1) (parts sp al db tr).P pre
        (parts sp al db tr).vs0 := ⟨_, rfl⟩
    obtain ⟨vx, hvx⟩ : ∃ v, v = mkVersion sp (db.S.building wpre) (k + 1) z nz := ⟨_, rfl⟩
    have hvs : (parts sp al db tr).vs =
        writeAll sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [vx]) := by
      rw [parts_vs, hlen, hsplit, writeAll_split sp _ _ _ hnz, ← hwpre, ← hvx]
    have hnodup := step_vs_nodup sp al db tr hinv hstep
    have hvx_mem : vx ∈ (parts sp al db tr).vs := by
      rw [hvs]; exact (writeAll_prefix sp _ _ _ _ _).subset (by simp)
    have hvxz : vx.node = z := by rw [hvx]; rfl
    have hvv : v = vx := by
      have := lv_Snew_written sp al db tr hnodup hvx_mem
      rw [hvxz, hlv] at this
      exact Option.some.inj this
    subst hvv
    have hvh : v.hist = nz.hist := by rw [hvx]; rfl
    rw [hvh] at hy
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
    obtain ⟨ny', hny', hlt⟩ := hpf.ptrs z nz hnz e he y hye
    rw [hyt'.1, Option.some.injEq] at hny'
    subst hny'
    have hylvl : lvlOf (parts sp al db tr).P y < lvlOf (parts sp al db tr).P z := by
      simp [lvlOf, hyt'.1, hnz, hlt]
    have hypost : y ∉ post := fun h => by have := hpost y h; omega
    -- z was tested, and not put back.
    obtain ⟨M0, -, hst0⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) pre
      (parts sp al db tr).D2 []
    have hr7 : (parts sp al db tr).r7 = stillDirtyOf al (parts sp al db tr).S'
        (parts sp al db tr).P (parts sp al db tr).D2 (k + 1) (pre ++ z :: post) := by
      rw [parts_r7, hlen, hsplit]
    unfold stillDirtyOf at hr7
    rw [List.foldl_append, hst0, List.foldl_cons] at hr7
    have hnotput : z ∉ (parts sp al db tr).r7.2 := by
      intro h
      apply hzD
      rw [(step_r7_shape sp al db tr hlen).1]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨z, h, by rw [hvx]; rfl⟩)
    by_cases htest : al.stillDirty (parts sp al db tr).S' (parts sp al db tr).P
        ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) (k + 1) z = true
    · exfalso
      simp only [htest, ↓reduceIte] at hr7
      obtain ⟨M1, -, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) post
        ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1)) ++ [(z, k + 1)]) ([] ++ M0 ++ [z])
      rw [h1] at hr7
      apply hnotput
      rw [hr7]
      simp
    · simp only [htest, Bool.false_eq_true, ↓reduceIte] at hr7
      obtain ⟨M1, hM1, h1⟩ := fold_shape al (parts sp al db tr).S' (parts sp al db tr).P (k + 1) post
        ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1))) ([] ++ M0)
      rw [h1] at hr7
      rw [hj] at htest
      simp only [javaTest, hnz, Bool.not_eq_true, List.any_eq_false] at htest
      have hyD := htest y hy
      constructor
      · -- y is not in D after step 7.
        rw [hr7]
        cases h : inD ((parts sp al db tr).D2 ++ M0.map (fun z => (z, k + 1)) ++
            M1.map (fun z => (z, k + 1))) y
        · rfl
        · exfalso
          obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
          rcases List.mem_append.mp hd with hd | hd
          · have := (inD_iff _ _).mpr ⟨d, hd⟩
            rw [hyD] at this; simp at this
          · obtain ⟨y', hy', hye'⟩ := List.mem_map.mp hd
            simp only [Prod.mk.injEq] at hye'
            rw [hye'.1] at hy'
            exact hypost (hM1.subset hy')
      · -- The reference names y's latest version: no version of y after z's.
        rw [hvx, ref?_mkVersion]
        simp only [hy, ↓reduceIte]
        congr 1
        obtain ⟨rest, hrest⟩ := writeAll_prefix sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [v])
        have hnodes := writeAll_nodes sp db.S (k + 1) (parts sp al db tr).P post (wpre ++ [v])
        rw [← hrest, List.map_append, List.append_cancel_left_eq] at hnodes
        have hrestn : rest.find? (fun w => w.node == y) = none := by
          rw [List.find?_eq_none]
          intro w hw hwy
          have : w.node ∈ rest.map (·.node) := List.mem_map_of_mem hw
          rw [hnodes] at this
          have hwy' : w.node = y := by simpa using hwy
          rw [hwy'] at this
          exact hypost (List.mem_filter.mp this).1
        have hvn : [v].find? (fun w => w.node == y) = none := by
          rw [List.find?_eq_none]
          intro w hw hwy
          simp only [List.mem_singleton] at hw
          subst hw
          have hwy' : w.node = y := by simpa using hwy
          rw [hvxz] at hwy'
          subst hwy'
          omega
        have hvsfind : (parts sp al db tr).vs.find? (fun w => w.node == y) =
            wpre.find? (fun w => w.node == y) := by
          rw [hvs, ← hrest, List.find?_append, List.find?_append, hvn, hrestn]
          simp
        unfold Snew
        rw [lv_append, lv_building]
        have : Stream.lv [(parts sp al db tr).R] y = (parts sp al db tr).vs.find? (fun w => w.node == y) := by
          simp [Stream.lv, parts_R]
        rw [this, hvsfind]
  · -- z is not written: v is its old latest version, and y stays clean and dead.
    have hlv0 : db.S.lv z = some v := by
      rw [← step_lv_index_not_taken sp al db tr hinv hstep hzidx hzt']; exact hlv
    obtain ⟨r, hr⟩ := lv_versionAt hlv0
    obtain ⟨-, hvz, nz0, hnz0, hvh, -⟩ := version_old_facts hinv hr
    have hz0 : isTop sp db.P z = true := by
      rw [← step_isTop_old sp al db tr hinv (by simp [hnz0])]; exact hz
    have hzD0 : (z, v.recNo) ∉ db.D := by
      intro h
      apply hzD
      have hD1 : (z, v.recNo) ∈ (parts sp al db tr).D1 :=
        (step_D1_mem sp al db tr hlen _).mpr (Or.inl h)
      have hlt : (parts sp al db tr).s < v.recNo := Nat.lt_of_not_le (fun hle =>
        hzt' ((step_taken_mem sp al db tr z).mpr ⟨v.recNo, hD1, hle⟩))
      rw [(step_r7_shape sp al db tr hlen).1]
      exact List.mem_append_left _ ((step_D2_mem sp al db tr _).mpr ⟨hD1, hlt⟩)
    -- y is an old root child.
    have hyp0 : y ∈ pointees sp nz0.hist := by
      rw [hvh] at hy
      obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
      exact (mem_pointees sp _ y).mpr ⟨e, (mem_upTo.mp he).1, hye⟩
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hyp0
    obtain ⟨my, hmy, -⟩ := hinv.ptrs z nz0 hnz0 e he y hye
    have hy0 : isTop sp db.P y = true := by
      rw [← step_isTop_old sp al db tr hinv (by simp [hmy])]; exact hyt
    obtain ⟨hyD0, href⟩ := hvi.fresh z v hz0 hlv0 hzD0 y hy hy0
    -- y is clean now: it is clean at k, and not reachable now.
    have hyidx0 : isIndex db.P y = true := by
      rw [← step_isIndex_old sp al db tr hlen (by simp [hmy])]; exact hyidx
    have hcl0 : dirty sp db.S db.P k y = false := by
      cases h : dirty sp db.S db.P k y
      · rfl
      · have := hinv.inv2 y hyidx0 hyw h
        rw [hyD0] at this; simp at this
    obtain ⟨u, hu, hgood⟩ := (dirty_false_iff _ _ _ _ _).mp hcl0
    have hdead : reachable sp (parts sp al db tr).P (k + 1) y = false := by
      have hzP' := step_top_old sp al db tr hinv hstep hv hnz0 (isTop_iff.mp hz0).1
        (by obtain ⟨-, n', hn', hl'⟩ := isTop_iff.mp hz0; rw [hnz0] at hn'; cases hn'; exact hl')
      exact (hstep.virt hv).dead z nz0 (by rw [← parts_P' sp al db tr hlen]; exact hzP')
        (by rw [← parts_P' sp al db tr hlen]; exact hz) y hyp0
        (by rw [← parts_P' sp al db tr hlen]; exact hyt) |> fun h => by
          rw [← parts_P' sp al db tr hlen] at h; exact h
    have hcl : dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) y = false := by
      rw [dirty_false_iff]
      refine ⟨u, by rw [step_lv_S0_old sp al db tr hinv hstep (by simp [hmy])]; exact hu, ?_⟩
      intro t ht hrt
      rcases Nat.lt_or_ge t (k + 1) with h | h
      · rw [reachable_grow hok.liveSub hinv.ptrs hinv.rootIn (step_grow sp al db tr hlen) (by omega)] at hrt
        exact good_mono' sp (SExt.append _ _) (step_grow sp al db tr hlen) (by omega) (hgood t (by omega) hrt)
      · have : t = k + 1 := by omega
        subst this
        rw [hdead] at hrt; simp at hrt
    have hyg : y ∉ (parts sp al db tr).gd3 := by
      intro h
      rcases ((step_gd3_mem' sp al db tr hok hinv hstep y).mp h).2.2.2.2 with h1 | h1
      · rw [hcl] at h1; simp at h1
      · -- A touched node is reachable at k; y is not (VInv.deadTops).
        have h2 := hstep.touchReach y h1
        simp only [Nat.add_sub_cancel] at h2
        rw [hvi.deadTops z nz0 hnz0 hz0 y hyp0 hy0] at h2; cases h2
    have hyD1 : ∀ d, (y, d) ∉ (parts sp al db tr).D1 := by
      intro d hd
      rcases (step_D1_mem sp al db tr hlen _).mp hd with h | ⟨-, h⟩
      · rw [(inD_iff _ _).mpr ⟨d, h⟩] at hyD0; simp at hyD0
      · exact hyg h
    have hynt : y ∉ (parts sp al db tr).taken := by
      intro h
      obtain ⟨d, hd, -⟩ := (step_taken_mem sp al db tr y).mp h
      exact hyD1 d hd
    constructor
    · cases h : inD (parts sp al db tr).r7.1 y
      · rfl
      · exfalso
        obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
        rw [(step_r7_shape sp al db tr hlen).1] at hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hyD1 d ((step_D2_mem sp al db tr _).mp hd).1
        · obtain ⟨y', hy', hye'⟩ := List.mem_map.mp hd
          simp only [Prod.mk.injEq] at hye'
          rw [hye'.1] at hy'
          exact hynt ((step_r7_shape sp al db tr hlen).2.subset hy')
    · rw [href, step_lv_index_not_taken sp al db tr hinv hstep hyidx hynt]

/-! ### VInv after the transaction -/

theorem step_newTops_len {k : Nat} (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hv : sp.virt = true) : (newTops sp al db tr).length ≤ 1 := by
  have h := length_le_one_of_nodup (l := (newTops sp al db tr).map (·.id))
    ((List.filter_sublist.map _).nodup hstep.distinct) (by
      intro a ha b hb
      obtain ⟨na, hna, rfl⟩ := List.mem_map.mp ha
      obtain ⟨nb, hnb, rfl⟩ := List.mem_map.mp hb
      rw [step_newTops_unique sp al db tr hstep hv hna hnb])
  simpa using h

/-- With a virtual root and BergDB's still-dirty test, one transaction keeps
`VInv`. -/
theorem step_vinv (hok : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true)
    (hj : al.stillDirty = javaTest sp) :
    VInv sp { P := (parts sp al db tr).P, D := (parts sp al db tr).r7.1, S := Snew sp al db tr }
      (k + 1) := by
  have hlen := hinv.len
  have hvi := hinv.vr hv
  have hvs := hstep.virt hv
  have hpf := step_pfacts sp al db tr hok hinv hstep
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hroot := step_P_root sp al db tr hinv hstep hv h0
  -- An old root child was created at k or before.
  have hold_time : ∀ z m c, TopAt sp db.P z m c → c ≤ k := by
    intro z m c h
    obtain ⟨e, he, hec⟩ := h.exists_entry
    rw [← hec]
    exact hinv.times z m h.1 e he
  refine ⟨hvi.rootPtrs, step_rootND sp al db tr hinv hv, step_rootNV sp al db tr hinv hstep hv, ?_,
    step_tops sp al db tr hinv hstep hv, ?_, ?_, ?_, ?_, ?_, ?_,
    step_fresh sp al db tr hok hinv hstep hv hj, ?_⟩
  · -- rootIdx
    intro n hn
    simp only at hn
    rw [hroot, Option.some.injEq] at hn
    subst hn
    exact hvi.rootIdx n0 h0
  · -- topVers
    intro z m c hzt r w hw
    simp only at hzt hw
    obtain ⟨R, hR, hwR, hwz⟩ := versionAt_spec hw
    rcases step_Snew_cases sp al db tr hinv hR with ⟨hr, h⟩ | ⟨rfl, rfl⟩
    · -- An old record: z is old.
      have hw0 : db.S.versionAt r z = some w := by
        rw [← hwz]; exact versionAt_of_mem h (hinv.versNodup r R h) hwR
      obtain ⟨-, -, n1, hn1, -⟩ := version_old_facts hinv hw0
      exact hvi.topVers z m c (step_topAt_back sp al db tr hinv hstep hv hzt (by simp [hn1])) r w hw0
    · -- The new record.
      rw [parts_R] at hwR
      obtain ⟨n, pre, hn, -, -, hvh, -⟩ := built_mem (step_vs_built sp al db tr hlen) hwR
      rw [hwz, hzt.1, Option.some.injEq] at hn
      rw [hvh, hn]
  · -- rootSorted
    intro n hn
    simp only at hn
    rw [hroot, Option.some.injEq] at hn
    subst hn
    simp only
    rw [List.pairwise_append]
    refine ⟨hvi.rootSorted n0 h0, pairwise_of_length_le_one (by
      rw [List.length_map]; exact step_newTops_len sp al db tr hstep hv), ?_⟩
    intro a ha b hb
    obtain ⟨nn, -, rfl⟩ := List.mem_map.mp hb
    have := hinv.times root n0 h0 a ha
    simp only
    omega
  · -- rootEntry
    intro n hn e he
    simp only at hn ⊢
    rw [hroot, Option.some.injEq] at hn
    subst hn
    rcases List.mem_append.mp he with he | he
    · obtain ⟨z, m, hzt, hzv⟩ := hvi.rootEntry n0 h0 e he
      exact ⟨z, m, step_topAt_old sp al db tr hinv hstep hv hzt, hzv⟩
    · obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp he
      exact ⟨nn.id, _, step_topAt_new sp al db tr hinv hstep hv hnn, rfl⟩
  · -- topEntry
    intro z m c hzt n hn
    simp only at hzt hn
    rw [hroot, Option.some.injEq] at hn
    subst hn
    rcases step_topAt_cases sp al db tr hinv hstep hv hzt with h | ⟨rfl, -, nn, hnn, rfl⟩
    · exact List.mem_append_left _ (hvi.topEntry z m c h n0 h0)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨nn, hnn, rfl⟩)
  · -- older
    intro z m c hzt y hy hyt
    simp only at hzt hyt ⊢
    obtain ⟨m', c', hyt'⟩ := step_tops sp al db tr hinv hstep hv y hyt
    rcases step_topAt_cases sp al db tr hinv hstep hv hzt with h | ⟨rfl, hz0, nn, hnn, rfl⟩
    · obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
      obtain ⟨my, hmy, -⟩ := hinv.ptrs _ m h.1 e he y hye
      have hy0 : isTop sp db.P y = true := by
        rw [← step_isTop_old sp al db tr hinv (by simp [hmy])]; exact hyt
      obtain ⟨m'', c'', hyt'', hlt⟩ := hvi.older _ m c h y hy hy0
      exact ⟨m'', c'', step_topAt_old sp al db tr hinv hstep hv hyt'', hlt⟩
    · refine ⟨m', c', hyt', ?_⟩
      rcases step_topAt_cases sp al db tr hinv hstep hv hyt' with h | ⟨rfl, -, nn', hnn', hid⟩
      · have := hold_time y m' c' h
        omega
      · exfalso
        have := step_newTops_unique sp al db tr hstep hv hnn hnn'
        subst this
        obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hy
        obtain ⟨my, hmy, hlt⟩ := hpf.ptrs _ m hzt.1 e he y hye
        rw [← hid, hzt.1, Option.some.injEq] at hmy
        subst hmy
        omega
  · -- closed
    intro z m c y m' c' hzt hyt hlt
    simp only at hzt hyt ⊢
    rcases step_topAt_cases sp al db tr hinv hstep hv hzt with h | ⟨rfl, hz0, nn, hnn, rfl⟩
    · rcases step_topAt_cases sp al db tr hinv hstep hv hyt with h' | ⟨rfl, -, -⟩
      · rw [step_topClosure_old sp al db tr hinv hstep hv (m.level + 1) _ m (by omega) h.1]
        exact hvi.closed _ m c y m' c' h h' hlt
      · have := hold_time _ m c h
        omega
    · rcases step_topAt_cases sp al db tr hinv hstep hv hyt with h' | ⟨rfl, -, -⟩
      · obtain ⟨hnnc, hnnl⟩ := (mem_newTops sp al db tr).mp hnn
        have := hvs.closure nn hnnc hnnl m (by rw [← parts_P' sp al db tr hlen]; exact hzt.1)
          y m' h'.1 h'.2.1 h'.2.2.1
        rw [← parts_P' sp al db tr hlen] at this
        exact this
      · omega
  · -- deadTops
    intro z n hz hzt y hy hyt
    simp only at hz hzt hyt ⊢
    have := hvs.dead z n (by rw [← parts_P' sp al db tr hlen]; exact hz)
      (by rw [← parts_P' sp al db tr hlen]; exact hzt) y hy
      (by rw [← parts_P' sp al db tr hlen]; exact hyt)
    rw [← parts_P' sp al db tr hlen] at this
    exact this

end Step

end SIS
