/-
Proofs, part 8: facts about one transaction.
-/
import SIS.Proof.Util

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem newNodeOf_some {c : Changes V} {x : NodeId} {m : Node V} (h : newNodeOf c x = some m) :
    ∃ nn ∈ c.new, nn.id = x ∧ m = { level := nn.level, isData := nn.isData, hist := [] } := by
  have := mem_of_get? h
  simp only [List.mem_map, Prod.mk.injEq] at this
  obtain ⟨nn, hnn, h1, h2⟩ := this
  exact ⟨nn, hnn, h1, h2.symm⟩

theorem newNodeOf_isSome {c : Changes V} {nn : NewNode} (h : nn ∈ c.new) :
    (newNodeOf c nn.id).isSome := by
  apply get?_isSome_of_mem
  exact List.mem_map.mpr ⟨nn, h, rfl⟩

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- The ids of the data nodes created by the transaction. -/
def dataIds : List NodeId := (((parts sp al db tr).c.new.filter (·.isData)).map (·.id))

theorem parts_P' {k : Nat} (hlen : db.S.length = k + 1) :
    (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := by
  rw [parts_P, hlen]

theorem step_grow {k : Nat} (hlen : db.S.length = k + 1) : Grow db.P k (parts sp al db tr).P := by
  rw [parts_P' sp al db tr hlen]
  exact grow_apply _ _ _ (by omega)

theorem step_P_old {k : Nat} (hlen : db.S.length = k + 1) {x : NodeId} {n : Node V}
    (h : db.P.get? x = some n) :
    (parts sp al db tr).P.get? x =
      some { n with hist := n.hist ++ addsFor (parts sp al db tr).c (k + 1) x } := by
  rw [parts_P' sp al db tr hlen]
  exact get?_apply_of_get? h

theorem step_P_new {k : Nat} (hlen : db.S.length = k + 1) {x : NodeId} (h : db.P.get? x = none) :
    (parts sp al db tr).P.get? x =
      (newNodeOf (parts sp al db tr).c x).map
        (fun n => { n with hist := n.hist ++ addsFor (parts sp al db tr).c (k + 1) x }) := by
  rw [parts_P' sp al db tr hlen, get?_apply, h]
  rfl

theorem step_vs_built {k : Nat} (hlen : db.S.length = k + 1) :
    Built sp db.S (k + 1) (parts sp al db tr).P (parts sp al db tr).vs := by
  have h1 : Built sp db.S (k + 1) (parts sp al db tr).P (parts sp al db tr).vs0 := by
    rw [parts_vs0, hlen]
    exact built_writeAll _ (built_nil _ _ _ _)
  rw [parts_vs, hlen]
  exact built_writeAll _ h1

theorem step_vs0_prefix : (parts sp al db tr).vs0 <+: (parts sp al db tr).vs := by
  rw [parts_vs]
  exact writeAll_prefix _ _ _ _ _ _

theorem step_vs_nodes :
    (parts sp al db tr).vs.map (·.node) =
      (dataIds sp al db tr).filter (fun x => ((parts sp al db tr).P.get? x).isSome) ++
        (parts sp al db tr).taken.filter (fun x => ((parts sp al db tr).P.get? x).isSome) := by
  rw [parts_vs, writeAll_nodes, parts_vs0, writeAll_nodes]
  simp [dataIds]

theorem step_taken_mem (x : NodeId) :
    x ∈ (parts sp al db tr).taken ↔
      ∃ d, (x, d) ∈ (parts sp al db tr).D1 ∧ d ≤ (parts sp al db tr).s := by
  rw [parts_taken]
  rw [(byLevel_perm _ _).mem_iff]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨y, d⟩, ⟨h1, h2⟩, rfl⟩
    exact ⟨d, h1, h2⟩
  · rintro ⟨d, h1, h2⟩
    exact ⟨(x, d), ⟨h1, h2⟩, rfl⟩

theorem step_D2_mem (e : NodeId × Nat) :
    e ∈ (parts sp al db tr).D2 ↔ e ∈ (parts sp al db tr).D1 ∧ (parts sp al db tr).s < e.2 := by
  rw [parts_D2]
  simp

theorem step_D1_mem {k : Nat} (hlen : db.S.length = k + 1) (e : NodeId × Nat) :
    e ∈ (parts sp al db tr).D1 ↔ e ∈ db.D ∨ (e.2 = k + 1 ∧ e.1 ∈ (parts sp al db tr).gd3) := by
  rw [parts_D1, hlen]
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨x, hx, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hx⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · obtain ⟨x, d⟩ := e
      simp only at h1 h2
      subst h1
      exact Or.inr ⟨x, h2, rfl⟩

theorem step_gd3_mem {k : Nat} (hlen : db.S.length = k + 1) (x : NodeId) :
    x ∈ (parts sp al db tr).gd3 ↔
      ((parts sp al db tr).P.get? x).isSome ∧ isIndex (parts sp al db tr).P x = true ∧
        inD db.D x = false ∧
        dirty sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P (k + 1) x = true := by
  rw [parts_gd3, hlen]
  simp only [gotDirtyOf, List.mem_mergeSort, List.mem_filter, mem_allIds, Bool.and_eq_true,
    Bool.not_eq_true']
  exact ⟨fun ⟨a, ⟨b, c⟩, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, ⟨b, c⟩, d⟩⟩

theorem step_gd3_nodup : (parts sp al db tr).gd3.Nodup := by
  rw [parts_gd3]
  simp only [gotDirtyOf]
  exact (List.mergeSort_perm _ _).symm.nodup_iff.mp (nodup_filter (nodup_eraseDups _) _)

theorem step_s_le {k : Nat} (hlen : db.S.length = k + 1) : (parts sp al db tr).s ≤ k := by
  rw [parts_s, hlen]
  simp only [startupPos]
  omega

theorem step_s_ge {k : Nat} (hlen : db.S.length = k + 1)
    (hsp : lastSp db.S < k ∨ (k = 0 ∧ lastSp db.S = 0)) : lastSp db.S ≤ (parts sp al db tr).s := by
  rw [parts_s, hlen]
  simp only [startupPos]
  omega

/-- The stream after the transaction. -/
def Snew : Stream V T := db.S ++ [(parts sp al db tr).R]

theorem step_S : (step sp al db tr).S = Snew sp al db tr := rfl
theorem step_P : (step sp al db tr).P = (parts sp al db tr).P := rfl
theorem step_D : (step sp al db tr).D = (parts sp al db tr).r7.1 := rfl

/-- The new stream and the stream under construction have the same versions. -/
theorem Snew_versionAt (r : Nat) (y : NodeId) :
    (Snew sp al db tr).versionAt r y = (parts sp al db tr).S'.versionAt r y := by
  rw [parts_S']
  unfold Snew Stream.building Stream.versionAt
  rcases Nat.lt_or_ge r db.S.length with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right h, List.getElem?_append_right h]
    cases r - db.S.length with
    | zero => simp [parts_R]
    | succ n => simp

theorem lv_of_versionAt_eq {S S' : Stream V T} (h : ∀ r y, S.versionAt r y = S'.versionAt r y)
    (x : NodeId) : S.lv x = S'.lv x := by
  cases h1 : S.lv x with
  | none =>
    have := (lv_eq_none_iff S x).mp h1
    symm
    exact (lv_eq_none_iff S' x).mpr (fun r => by rw [← h]; exact this r)
  | some v =>
    obtain ⟨r, hr1, hr2⟩ := (lv_eq_some_iff S x v).mp h1
    symm
    exact (lv_eq_some_iff S' x v).mpr ⟨r, by rw [← h]; exact hr1, fun r' hr' => by rw [← h]; exact hr2 r' hr'⟩

theorem good_of_versionAt_eq {S S' : Stream V T} (h : ∀ r y, S.versionAt r y = S'.versionAt r y)
    (P : Struct V) (t : Time) (v : Version V) : good sp S P t v = good sp S' P t v := by
  have key : ∀ (b : Nat) (v : Version V), v.level < b →
      (good sp S P t v = true ↔ good sp S' P t v = true) := by
    intro b
    induction b with
    | zero => intro v h; omega
    | succ b ih =>
      intro v hb
      rw [good_iff, good_iff]
      apply and_congr Iff.rfl
      apply forall_congr'
      intro y
      apply imp_congr_right
      intro _
      constructor
      · rintro ⟨r, w, h1, h2, h3, h4⟩
        exact ⟨r, w, h1, by rw [← h]; exact h2, h3, (ih w (by omega)).mp h4⟩
      · rintro ⟨r, w, h1, h2, h3, h4⟩
        exact ⟨r, w, h1, by rw [h]; exact h2, h3, (ih w (by omega)).mpr h4⟩
  exact Bool.eq_iff_iff.mpr (key (v.level + 1) v (by omega))

theorem dirty_of_versionAt_eq {S S' : Stream V T} (h : ∀ r y, S.versionAt r y = S'.versionAt r y)
    (P : Struct V) (i : Time) (x : NodeId) : dirty sp S P i x = dirty sp S' P i x := by
  unfold dirty
  rw [lv_of_versionAt_eq h x]
  split
  · rfl
  · rename_i v _
    apply List.any_congr rfl
    intro t
    rw [good_of_versionAt_eq sp h P t v]

theorem step_r7 (hex : al.stillDirty = exactTest sp) {k : Nat} (hlen : db.S.length = k + 1) :
    (parts sp al db tr).r7 =
      ((parts sp al db tr).D2 ++
          ((parts sp al db tr).taken.filter
            (fun x => dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x)).map
            (fun x => (x, k + 1)),
        (parts sp al db tr).taken.filter
          (fun x => dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x)) := by
  rw [parts_r7, stillDirtyOf_exact sp al hex, hlen]
  have : ∀ x, dirty sp (parts sp al db tr).S' (parts sp al db tr).P (k + 1) x =
      dirty sp (Snew sp al db tr) (parts sp al db tr).P (k + 1) x := by
    intro x
    exact (dirty_of_versionAt_eq sp (Snew_versionAt sp al db tr) _ _ x).symm
  simp only [this]

/-- A node that is not written in the record keeps its latest version. -/
theorem lv_Snew_not_written {x : NodeId} (hx : ∀ w ∈ (parts sp al db tr).vs, w.node ≠ x) :
    (Snew sp al db tr).lv x = db.S.lv x := by
  unfold Snew
  rw [lv_append]
  have : Stream.lv [(parts sp al db tr).R] x = none := by
    simp only [Stream.lv, List.reverse_singleton, List.findSome?_singleton, parts_R]
    rw [List.find?_eq_none]
    intro w hw
    simpa using hx w hw
  rw [this, Option.none_or]

theorem lv_Snew_written (hnd : ((parts sp al db tr).vs.map (·.node)).Nodup) {w : Version V}
    (hw : w ∈ (parts sp al db tr).vs) : (Snew sp al db tr).lv w.node = some w := by
  unfold Snew
  rw [lv_append]
  have : Stream.lv [(parts sp al db tr).R] w.node = some w := by
    simp only [Stream.lv, List.reverse_singleton, List.findSome?_singleton, parts_R]
    exact find?_node_of_mem hnd hw rfl
  rw [this, Option.some_or]

theorem Snew_getElem?_old {r : Nat} (hr : r < db.S.length) :
    (Snew sp al db tr)[r]? = db.S[r]? := by
  unfold Snew
  rw [List.getElem?_append_left hr]

theorem Snew_getElem?_new : (Snew sp al db tr)[db.S.length]? = some (parts sp al db tr).R := by
  unfold Snew
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem Snew_ext : SExt db.S (Snew sp al db tr) := SExt.append _ _

end Step

end SIS
