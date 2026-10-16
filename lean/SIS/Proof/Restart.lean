/-
Proofs, part 17: T2, restart invariance.
-/
import SIS.Proof.Recovery

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Two states agree: the same stream, the same D, the same nodes. -/
def Rel (db1 db2 : DB V T) : Prop := db1.S = db2.S ∧ db1.D = db2.D ∧ SameNodes db1.P db2.P

/-! ### Every part of a transaction depends on P only through its nodes -/

theorem writeAll_congr (sp : Spec V T) (S : Stream V T) (i : Nat) {P P' : Struct V}
    (h : SameNodes P P') (xs : List NodeId) :
    ∀ (vs : List (Version V)), writeAll sp S i P xs vs = writeAll sp S i P' xs vs := by
  induction xs with
  | nil => intro vs; rfl
  | cons x xs ih =>
    intro vs
    rw [writeAll_cons, writeAll_cons, h x]
    exact ih _

theorem byLevel_congr {P P' : Struct V} (h : SameNodes P P') (xs : List NodeId) :
    byLevel P xs = byLevel P' xs := by
  unfold byLevel
  have : (fun a b => decide (((P.get? a).map (·.level)).getD 0 ≤ ((P.get? b).map (·.level)).getD 0)) =
      (fun a b => decide (((P'.get? a).map (·.level)).getD 0 ≤ ((P'.get? b).map (·.level)).getD 0)) := by
    funext a b; rw [h a, h b]
  rw [this]

theorem isIndex_congr {P P' : Struct V} (h : SameNodes P P') (x : NodeId) :
    isIndex P x = isIndex P' x := by
  simp only [isIndex, h x]

theorem mergeSort_eq_of_mem {l₁ l₂ : List Nat} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.mergeSort (fun a b => decide (a ≤ b)) = l₂.mergeSort (fun a b => decide (a ≤ b)) := by
  have hp : (l₁.mergeSort (fun a b => decide (a ≤ b))).Perm (l₂.mergeSort (fun a b => decide (a ≤ b))) :=
    (List.mergeSort_perm _ _).trans (((List.perm_ext_iff_of_nodup h₁ h₂).mpr h).trans
      (List.mergeSort_perm _ _).symm)
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true) _ _ _ hp
  · intro a b _ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    omega
  · exact List.pairwise_mergeSort (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  · exact List.pairwise_mergeSort (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

theorem gotDirtyOf_congr (sp : Spec V T) (S : Stream V T) {P P' : Struct V} (h : SameNodes P P')
    (D : Dirty) (i : Time) : gotDirtyOf sp S P D i = gotDirtyOf sp S P' D i := by
  unfold gotDirtyOf
  have hf : (fun x => isIndex P x && !inD D x && dirty sp S P i x) =
      (fun x => isIndex P' x && !inD D x && dirty sp S P' i x) := by
    funext x; rw [isIndex_congr h x, h.dirty i x]
  rw [hf]
  apply mergeSort_eq_of_mem (nodup_filter (nodup_eraseDups _) _) (nodup_filter (nodup_eraseDups _) _)
  intro x
  rw [List.mem_filter, List.mem_filter]
  have h1 := mem_allIds P x
  have h2 := mem_allIds P' x
  unfold allIds at h1 h2
  rw [h1, h2, h x]

/-- `reachFrom` only looks at P through its nodes. -/
theorem SameNodes.reachFrom {sp : Spec V T} {P P' : Struct V} (h : SameNodes P P') (t : Time) :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b →
      SIS.reachFrom sp P t x n = SIS.reachFrom sp P' t x n := by
  intro b
  induction b with
  | zero => intro x n hb; omega
  | succ b ih =>
    intro x n hb
    rw [reachFrom_eq, reachFrom_eq]
    congr 1
    apply flatMap_congr_mem
    intro y _
    rw [h y]
    split
    · rename_i m _
      split
      · exact ih y m (by omega)
      · rfl
    · rfl

theorem marked_congr (sp : Spec V T) {P P' : Struct V} (h : SameNodes P P') (c : Changes V)
    (i : Time) (x : NodeId) : marked sp P c i x = marked sp P' c i x := by
  unfold marked
  rw [h.reachable i x, h x]
  split
  · rename_i n _
    rw [h.reachFrom i (n.level + 1) x n (by omega)]
  · rfl

theorem markOf_congr (sp : Spec V T) {P P' : Struct V} (h : SameNodes P P') (c : Changes V)
    (D : Dirty) (i : Time) : markOf sp P c D i = markOf sp P' c D i := by
  unfold markOf
  have hf : (fun x => isIndex P x && !inD D x && marked sp P c i x) =
      (fun x => isIndex P' x && !inD D x && marked sp P' c i x) := by
    funext x; rw [isIndex_congr h x, marked_congr sp h c i x]
  rw [hf]
  apply mergeSort_eq_of_mem (nodup_filter (nodup_eraseDups _) _) (nodup_filter (nodup_eraseDups _) _)
  intro x
  rw [List.mem_filter, List.mem_filter]
  have h1 := mem_allIds P x
  have h2 := mem_allIds P' x
  unfold allIds at h1 h2
  rw [h1, h2, h x]

theorem topOf_sameNodes (sp : Spec V T) {P P' : Struct V} (h : SameNodes P P') (S : Stream V T)
    (s : Nat) : topOf sp P S s = topOf sp P' S s := by
  unfold topOf topV
  rw [h root]

theorem step_congr (sp : Spec V T) (al : Algo V T) (hst : AlgOK sp al)
    {db1 db2 : DB V T} (h : Rel db1 db2) (tr : T) : Rel (step sp al db1 tr) (step sp al db2 tr) := by
  obtain ⟨hS, hD, hP⟩ := h
  obtain ⟨P1, D1, S1⟩ := db1
  obtain ⟨P2, D2, S2⟩ := db2
  simp only at hS hD hP
  subst hS hD
  have hc : (parts sp al ⟨P1, D1, S1⟩ tr).c = (parts sp al ⟨P2, D1, S1⟩ tr).c := by
    rw [parts_c, parts_c]; simp only; rw [hP.view]
  have hPP : SameNodes (parts sp al ⟨P1, D1, S1⟩ tr).P (parts sp al ⟨P2, D1, S1⟩ tr).P := by
    rw [parts_P, parts_P, hc]; exact hP.apply _ _
  have hvs0 : (parts sp al ⟨P1, D1, S1⟩ tr).vs0 = (parts sp al ⟨P2, D1, S1⟩ tr).vs0 := by
    rw [parts_vs0, parts_vs0, hc]; exact writeAll_congr sp _ _ hPP _ _
  have hgd3 : (parts sp al ⟨P1, D1, S1⟩ tr).gd3 = (parts sp al ⟨P2, D1, S1⟩ tr).gd3 := by
    rw [parts_gd3, parts_gd3]
    congr 1
    by_cases hmk : al.mark = true
    · simp only [hmk, ↓reduceIte]
      rw [hc]; exact markOf_congr sp hPP _ _ _
    · simp only [hmk]
      rw [hvs0]; exact gotDirtyOf_congr sp _ hPP _ _
  have hD1 : (parts sp al ⟨P1, D1, S1⟩ tr).D1 = (parts sp al ⟨P2, D1, S1⟩ tr).D1 := by
    rw [parts_D1, parts_D1, hgd3]
  have hs : (parts sp al ⟨P1, D1, S1⟩ tr).s = (parts sp al ⟨P2, D1, S1⟩ tr).s := by
    rw [parts_s, parts_s, hD1]
  have htaken : (parts sp al ⟨P1, D1, S1⟩ tr).taken = (parts sp al ⟨P2, D1, S1⟩ tr).taken := by
    rw [parts_taken, parts_taken, hD1, hs, byLevel_congr hPP]
  have hD2 : (parts sp al ⟨P1, D1, S1⟩ tr).D2 = (parts sp al ⟨P2, D1, S1⟩ tr).D2 := by
    rw [parts_D2, parts_D2, hD1, hs]
  have hvs : (parts sp al ⟨P1, D1, S1⟩ tr).vs = (parts sp al ⟨P2, D1, S1⟩ tr).vs := by
    rw [parts_vs, parts_vs, htaken, hvs0]; exact writeAll_congr sp _ _ hPP _ _
  have hS' : (parts sp al ⟨P1, D1, S1⟩ tr).S' = (parts sp al ⟨P2, D1, S1⟩ tr).S' := by
    rw [parts_S', parts_S', hvs]
  have hr7 : (parts sp al ⟨P1, D1, S1⟩ tr).r7 = (parts sp al ⟨P2, D1, S1⟩ tr).r7 := by
    rw [parts_r7, parts_r7, hS', hD2, htaken]
    exact stillDirtyOf_congr al hst.still.congr hPP _ _ _ _
  have hR : (parts sp al ⟨P1, D1, S1⟩ tr).R = (parts sp al ⟨P2, D1, S1⟩ tr).R := by
    rw [parts_R, parts_R, hs, hvs, hgd3, hr7, hS', topOf_sameNodes sp hPP]
  rw [step_eq_parts, step_eq_parts]
  exact ⟨by simp only [hR], by simp only [hr7], hPP⟩

/-! ### Runs with restarts -/

theorem T2_strong (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hst : AlgOK sp al) :
    ∀ j ≤ ts.length, Rel (runRestarts sp al (ts.take j)) (st sp al (ts.map (·.1)) j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [st_zero]
    simp only [List.take_zero, runRestarts, List.foldl_nil]
    exact ⟨rfl, rfl, SameNodes.refl _⟩
  | succ j ih =>
    intro hj
    have hj' : j < (ts.map (·.1)).length := by simp; omega
    have h1 := step_congr sp al hst (ih (by omega)) ts[j].1
    have hsj : st sp al (ts.map (·.1)) (j + 1) = step sp al (st sp al (ts.map (·.1)) j) ts[j].1 := by
      rw [st_succ sp al _ hj']
      simp
    have htake : ts.take (j + 1) = ts.take j ++ [ts[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    simp only [runRestarts] at ih ⊢
    rw [htake, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hsj]
    split
    · -- A restart: startup from the stream gives the same state.
      have hS : (step sp al (List.foldl (fun db p =>
            if p.2 = true then startup sp (step sp al db p.1).S else step sp al db p.1) (init sp)
            (List.take j ts)) ts[j].1).S = (step sp al (st sp al (ts.map (·.1)) j) ts[j].1).S := h1.1
      rw [hS, ← hsj]
      have := T1_strong sp al (ts.map (·.1)) hok hst (k := j + 1) (by simp; omega)
      exact ⟨rfl, this.2, this.1⟩
    · exact h1

end SIS
