/-
Proofs for bounds counted by height (bergdb item 007; SIS/BoundHeight.lean).
Added 2026-11-13.

With TREE the ancestors of a node at t form one chain of live pointers down
from the root (`tree_anc_chain`), so there are at most H + 1 of them if the
root's live height at t is at most H (`anc_count_height`). The counts of the
access path of a change (`accessPath_count_height`) and of the writer's paths
(`pathOf_count_height`) follow as with levels.
-/
import SIS.BoundHeight
import SIS.Proof.BoundColdD
import SIS.Proof.BoundT4Java

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Tree

variable {sp : Spec V T} {P : Struct V} {t : Time}

/-- A node below x other than x is below a live child of x on a lower level. -/
theorem reachFrom_below_child {x : NodeId} {n : Node V} {a : NodeId}
    (ha : a ∈ reachFrom sp P t x n) (hax : a ≠ x) :
    ∃ y m, y ∈ sp.live (n.hist.upTo t) ∧ P.get? y = some m ∧ m.level < n.level ∧
      a ∈ reachFrom sp P t y m := by
  rw [reachFrom_eq] at ha
  simp only [List.mem_cons, List.mem_flatMap] at ha
  rcases ha with rfl | ⟨y, hy, hay⟩
  · exact absurd rfl hax
  · split at hay
    · rename_i m hm
      split at hay
      · rename_i hlt
        exact ⟨y, m, hy, hm, hlt, hay⟩
      · simp at hay
    · simp at hay

/-- With TREE, of two ancestors of z, one is below the other. -/
theorem tree_anc_chain (htree : treeAt sp P t) :
    ∀ (b : Nat) (z : NodeId) (m : Node V) (x1 x2 : NodeId) (n1 n2 : Node V),
      P.get? z = some m → (n1.level - m.level) + (n2.level - m.level) < b →
      reachable sp P t x1 = true → P.get? x1 = some n1 → z ∈ reachFrom sp P t x1 n1 →
      reachable sp P t x2 = true → P.get? x2 = some n2 → z ∈ reachFrom sp P t x2 n2 →
      x1 ∈ reachFrom sp P t x2 n2 ∨ x2 ∈ reachFrom sp P t x1 n1 := by
  intro b
  induction b with
  | zero => intro z m x1 x2 n1 n2 _ h; omega
  | succ b ih =>
    intro z m x1 x2 n1 n2 hm hb hr1 hn1 hz1 hr2 hn2 hz2
    by_cases h1 : z = x1
    · subst h1; exact Or.inl hz2
    by_cases h2 : z = x2
    · subst h2; exact Or.inr hz1
    obtain ⟨q1, nq1, m1, hq1, hnq1, hzq1, hm1, hlt1⟩ :=
      reachFrom_parent sp P t (n1.level + 1) x1 n1 (by omega) hn1 z hz1 h1
    obtain ⟨q2, nq2, m2, hq2, hnq2, hzq2, hm2, hlt2⟩ :=
      reachFrom_parent sp P t (n2.level + 1) x2 n2 (by omega) hn2 z hz2 h2
    rw [hm, Option.some.injEq] at hm1 hm2
    subst hm1; subst hm2
    have hrq1 : reachable sp P t q1 = true := by
      rw [reachable_iff] at hr1 ⊢
      exact reach_of_mem_reachFrom sp P t (n1.level + 1) x1 n1 (by omega) hn1 hr1 q1 hq1
    have hrq2 : reachable sp P t q2 = true := by
      rw [reachable_iff] at hr2 ⊢
      exact reach_of_mem_reachFrom sp P t (n2.level + 1) x2 n2 (by omega) hn2 hr2 q2 hq2
    have hrz : reachable sp P t z = true := by
      rw [reachable_iff] at hr1 ⊢
      exact reach_of_mem_reachFrom sp P t (n1.level + 1) x1 n1 (by omega) hn1 hr1 z hz1
    have hzr : z ≠ root := by
      intro hz0
      subst hz0
      rw [reachable_iff] at hrq1
      rcases reach_level_root hrq1 hm nq1 hnq1 with h | h
      · subst h; rw [hm, Option.some.injEq] at hnq1; subst hnq1; omega
      · omega
    have hq := tree_parent_unique htree hrz hzr hrq1 hrq2 hnq1 hnq2 hzq1 hzq2
    subst hq
    rw [hnq1, Option.some.injEq] at hnq2
    subst hnq2
    have hle1 : nq1.level ≤ n1.level := by
      rcases reachFrom_level sp P t (n1.level + 1) x1 n1 (by omega) hn1 q1 hq1 nq1 hnq1 with h | h
      · subst h; rw [hn1, Option.some.injEq] at hnq1; subst hnq1; omega
      · omega
    have hle2 : nq1.level ≤ n2.level := by
      rcases reachFrom_level sp P t (n2.level + 1) x2 n2 (by omega) hn2 q1 hq2 nq1 hnq1 with h | h
      · subst h; rw [hn2, Option.some.injEq] at hnq1; subst hnq1; omega
      · omega
    exact ih q1 nq1 x1 x2 n1 n2 hnq1 (by omega) hr1 hn1 hq1 hr2 hn2 hq2

/-- With TREE, the ancestors of z at t below x, without repeats, are at most
H + 1 if x's live height at t is at most H. -/
theorem anc_below_count (htree : treeAt sp P t) (z : NodeId) :
    ∀ (H : Nat) (x : NodeId) (n : Node V), LiveHeightLe sp P t H x → P.get? x = some n →
      reachable sp P t x = true → ∀ L : List NodeId, L.Nodup →
      (∀ a ∈ L, a ∈ reachFrom sp P t x n ∧ AncAt sp P t z a) → L.length ≤ H + 1 := by
  intro H
  induction H with
  | zero =>
    intro x n hh hn _ L hnd hL
    apply length_le_one_of_nodup hnd
    have key : ∀ a ∈ L, a = x := by
      intro a ha
      apply Classical.byContradiction; intro hax
      obtain ⟨y, m, hy, -, -, -⟩ := reachFrom_below_child (hL a ha).1 hax
      rw [hh n hn] at hy; cases hy
    intro a ha b hb; rw [key a ha, key b hb]
  | succ H ih =>
    intro x n hh hn hrx L hnd hL
    rw [length_filter_add L (fun a => a == x)]
    have h1 : (L.filter (fun a => a == x)).length ≤ 1 :=
      length_le_one_of_nodup (hnd.filter _) (fun a ha b hb => by
        simp only [List.mem_filter, beq_iff_eq] at ha hb
        rw [ha.2, hb.2])
    cases hrest : L.filter (fun a => !(a == x)) with
    | nil => simp only [List.length_nil]; omega
    | cons a0 L0 =>
      have ha0 : a0 ∈ L.filter (fun a => !(a == x)) := by rw [hrest]; simp
      obtain ⟨ha0L, ha0x⟩ := List.mem_filter.mp ha0
      have ha0x' : a0 ≠ x := by simpa using ha0x
      obtain ⟨y0, m0, hy0, hm0, hlt0, ha0y⟩ := reachFrom_below_child (hL a0 ha0L).1 ha0x'
      have hry0 : reachable sp P t y0 = true := by
        rw [reachable_iff] at hrx ⊢
        exact Reach.child hrx hn hy0 hm0 hlt0
      have hnot_root : ∀ y m, P.get? y = some m → m.level < n.level → y ≠ root := by
        intro y m hym hlt hy
        subst hy
        rw [reachable_iff] at hrx
        rcases reach_level_root hrx hym n hn with h | h
        · subst h; rw [hn, Option.some.injEq] at hym; subst hym; omega
        · omega
      -- Every other ancestor in L is below y0.
      have hall : ∀ a ∈ a0 :: L0, a ∈ reachFrom sp P t y0 m0 ∧ AncAt sp P t z a := by
        intro a haL
        rw [← hrest] at haL
        obtain ⟨haL', hax⟩ := List.mem_filter.mp haL
        have hax' : a ≠ x := by simpa using hax
        refine ⟨?_, (hL a haL').2⟩
        obtain ⟨y, m, hy, hm, hlt, hay⟩ := reachFrom_below_child (hL a haL').1 hax'
        have hry : reachable sp P t y = true := by
          rw [reachable_iff] at hrx ⊢
          exact Reach.child hrx hn hy hm hlt
        -- z is below y and below y0.
        obtain ⟨-, na, hna, hza⟩ := (hL a haL').2
        obtain ⟨-, na0, hna0, hza0⟩ := (hL a0 ha0L).2
        have hzy : z ∈ reachFrom sp P t y m :=
          reachFrom_trans' sp (m.level + 1) y m (by omega) hm a na hay hna z hza
        have hzy0 : z ∈ reachFrom sp P t y0 m0 :=
          reachFrom_trans' sp (m0.level + 1) y0 m0 (by omega) hm0 a0 na0 ha0y hna0 z hza0
        obtain ⟨mz, hmz⟩ : ∃ mz, P.get? z = some mz := by
          have hrz : Reach sp P t z := by
            rw [reachable_iff] at hry
            exact reach_of_mem_reachFrom sp P t (m.level + 1) y m (by omega) hm hry z hzy
          exact Option.isSome_iff_exists.mp hrz.isSome
        -- y = y0: else one is below the other and has two parents.
        have hyy0 : y = y0 := by
          apply Classical.byContradiction; intro hne
          have hbelow : ∀ (u u' : NodeId) (mu mu' : Node V), P.get? u = some mu →
              P.get? u' = some mu' → u ∈ sp.live (n.hist.upTo t) → mu.level < n.level →
              u' ∈ sp.live (n.hist.upTo t) → mu'.level < n.level →
              u ∈ reachFrom sp P t u' mu' → u ≠ u' → False := by
            intro u u' mu mu' hmu hmu' hu hltu hu' hltu' hin hne'
            obtain ⟨q, nq, mq, hq, hnq, huq, hmq, -⟩ :=
              reachFrom_parent sp P t (mu'.level + 1) u' mu' (by omega) hmu' u hin hne'
            rw [hmu, Option.some.injEq] at hmq
            subst hmq
            have hru' : reachable sp P t u' = true := by
              rw [reachable_iff] at hrx ⊢
              exact Reach.child hrx hn hu' hmu' hltu'
            have hrq : reachable sp P t q = true := by
              rw [reachable_iff] at hru' ⊢
              exact reach_of_mem_reachFrom sp P t (mu'.level + 1) u' mu' (by omega) hmu' hru' q hq
            have hru : reachable sp P t u = true := by
              rw [reachable_iff] at hrx ⊢
              exact Reach.child hrx hn hu hmu hltu
            have hqx := tree_parent_unique htree hru (hnot_root u mu hmu hltu) hrq hrx hnq hn huq hu
            subst hqx
            rw [hn, Option.some.injEq] at hnq
            subst hnq
            rcases reachFrom_level sp P t (mu'.level + 1) u' mu' (by omega) hmu' q hq n hn with h | h
            · subst h; rw [hn, Option.some.injEq] at hmu'; subst hmu'; omega
            · omega
          rcases tree_anc_chain htree (m.level + m0.level + 1) z mz y y0 m m0 hmz (by omega)
            hry hm hzy hry0 hm0 hzy0 with h | h
          · exact hbelow y y0 m m0 hm hm0 hy hlt hy0 hlt0 h hne
          · exact hbelow y0 y m0 m hm0 hm hy0 hlt0 hy hlt h (Ne.symm hne)
        subst hyy0
        rw [hm, Option.some.injEq] at hm0
        subst hm0
        exact hay
      have := ih y0 m0 (hh n hn y0 hy0) hm0 hry0 (a0 :: L0)
        (by rw [← hrest]; exact hnd.filter _) hall
      simp only [List.length_cons] at this ⊢
      omega

/-- With TREE, the ancestors of a node at t, without repeats, are at most
H + 1, H a bound on the root's live height at t. -/
theorem anc_count_height (htree : treeAt sp P t) {n0 : Node V} (h0 : P.get? root = some n0)
    {H : Nat} (hH : LiveHeightLe sp P t H root) (z : NodeId)
    (L : List NodeId) (hnd : L.Nodup) (hL : ∀ x ∈ L, AncAt sp P t z x) :
    L.length ≤ H + 1 := by
  have hr0 : reachable sp P t root = true :=
    (reachable_iff _ _ _ _).mpr (Reach.root n0 h0)
  apply anc_below_count htree z H root n0 hH h0 hr0 L hnd
  intro a ha
  refine ⟨?_, hL a ha⟩
  have := (hL a ha).1
  unfold reachable reachList at this
  rw [h0] at this
  simpa using this

end Tree

/-! ### The counts of a change by height -/

/-- With TREE at j - 1 and the root's live height at j - 1 at most H, the
writer's paths for the change c at time j have at most H + 1 nodes for each
node c creates, gives an entry, touches or makes unreachable. -/
theorem pathOf_count_height {sp : Spec V T} {P : Struct V} {j : Time} (htree : treeAt sp P (j - 1))
    {n0 : Node V} (h0 : P.get? root = some n0) {H : Nat} (hH : LiveHeightLe sp P (j - 1) H root)
    (c : Changes V) :
    (pathOf sp P c j).length ≤ (H + 1) *
      (c.new.length + c.adds.length + c.touch.length + (removedAt sp P c j).length) := by
  have hnd : (pathOf sp P c j).Nodup := by
    unfold pathOf
    exact nodup_filter (nodup_eraseDups _) _
  have h := nodup_length_le_sum (fun z x => AncAt sp P (j - 1) z x) (fun _ => H + 1)
    (fun z L hndL hL => anc_count_height htree h0 hH z L hndL hL)
    (c.new.map (·.id) ++ c.adds.map (·.1) ++ c.touch ++ removedAt sp P c j) (pathOf sp P c j) hnd
    (by
      intro x hx
      obtain ⟨hr, n, hn, hany⟩ := mem_pathOf hx
      obtain ⟨z, hz, hcz⟩ := List.any_eq_true.mp hany
      refine ⟨z, ?_, hr, n, hn, hz⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hcz
      rcases hcz with (hch | ht) | ⟨hrz, hnr⟩
      · unfold changed at hch
        simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hch
        rcases hch with ⟨nn, hnn, rfl⟩ | ⟨a, ha, rfl⟩
        · simp only [List.mem_append, List.mem_map]
          exact Or.inl (Or.inl (Or.inl ⟨nn, hnn, rfl⟩))
        · simp only [List.mem_append, List.mem_map]
          exact Or.inl (Or.inl (Or.inr ⟨a, ha, rfl⟩))
      · simp only [List.mem_append]
        exact Or.inl (Or.inr (List.contains_iff_mem.mp ht))
      · simp only [List.mem_append]
        right
        unfold removedAt
        refine List.mem_filter.mpr ⟨List.mem_eraseDups.mpr ?_, by simp [hnr]⟩
        simpa [reachable] using hrz)
  rw [sum_map_const] at h
  simp only [List.length_append, List.length_map] at h
  rw [Nat.mul_comm]
  exact h

section Change

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- With TREE after T(j + 1) and the root's live height then at most H, the
nodes on the access path of its change, without repeats, are at most (H + 1)
times its changed nodes, plus its touched ones. -/
theorem accessPath_count_height (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j < ts.length) (htree : treeAt sp (st sp al ts (j + 1)).P (j + 1)) {n0 : Node V}
    (h0 : (st sp al ts (j + 1)).P.get? root = some n0) {H : Nat}
    (hH : LiveHeightLe sp (st sp al ts (j + 1)).P (j + 1) H root) (L : List NodeId) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, onAccessPath sp al ts (j + 1) x) :
    L.length ≤ (H + 1) * ((chg sp al ts j hj).new.length + (chg sp al ts j hj).adds.length) +
      (chg sp al ts j hj).touch.length := by
  classical
  have hL' : ∀ x ∈ L, marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x = true ∨
      x ∈ (chg sp al ts j hj).touch := by
    intro x hx
    obtain ⟨j', hj', hjj, h⟩ := onAccessPath_elim hok hst (hL x hx)
    obtain rfl : j' = j := by omega
    exact h
  rw [length_filter_add L (fun x => marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x)]
  have h1 := nodup_length_le_sum (fun z x => AncAt sp (st sp al ts (j + 1)).P (j + 1) z x)
    (fun _ => H + 1)
    (fun z L' hnd' hL'' => anc_count_height htree h0 hH z L' hnd' hL'')
    ((chg sp al ts j hj).new.map (·.id) ++ (chg sp al ts j hj).adds.map (·.1))
    (L.filter (fun x => marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x))
    (hnd.filter _) (by
      intro x hx
      have hm := (List.mem_filter.mp hx).2
      unfold marked at hm
      simp only [Bool.and_eq_true] at hm
      obtain ⟨hr, hm⟩ := hm
      cases hnx : (st sp al ts (j + 1)).P.get? x with
      | none => rw [hnx] at hm; cases hm
      | some nx =>
        rw [hnx] at hm
        obtain ⟨z, hz, hcz⟩ := List.any_eq_true.mp hm
        refine ⟨z, ?_, hr, nx, hnx, hz⟩
        unfold changed at hcz
        simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hcz
        rcases hcz with ⟨nn, hnn, rfl⟩ | ⟨a, ha, rfl⟩
        · exact List.mem_append_left _ (List.mem_map_of_mem hnn)
        · exact List.mem_append_right _ (List.mem_map_of_mem ha))
  have h2 := nodup_length_le_sum (fun z x => x = z) (fun _ => 1)
    (fun z L' hnd' hL'' => length_le_one_of_nodup hnd' (fun a ha b hb => by
      rw [hL'' a ha, hL'' b hb]))
    (chg sp al ts j hj).touch
    (L.filter (fun x => !marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x))
    (hnd.filter _) (by
      intro x hx
      obtain ⟨hxL, hnm⟩ := List.mem_filter.mp hx
      rcases hL' x hxL with h | h
      · rw [h] at hnm; cases hnm
      · exact ⟨x, h, rfl⟩)
  rw [sum_map_const, List.length_append, List.length_map, List.length_map] at h1
  rw [sum_map_const] at h2
  have : (H + 1) * ((chg sp al ts j hj).new.length + (chg sp al ts j hj).adds.length) =
      ((chg sp al ts j hj).new.length + (chg sp al ts j hj).adds.length) * (H + 1) :=
    Nat.mul_comm _ _
  omega

end Change

/-! ### Pointer ancestors within h steps -/

section PtrUp

variable {sp : Spec V T} {P : Struct V}

/-- x reaches z through pointers in at most m steps, taken from z upwards. -/
def PtrUp (sp : Spec V T) (P : Struct V) : Nat → NodeId → NodeId → Prop
  | 0, x, z => x = z
  | m + 1, x, z => x = z ∨ ∃ p ∈ ptrParents sp P z, PtrUp sp P m x p

theorem ptrUp_refl : ∀ m (x : NodeId), PtrUp sp P m x x
  | 0, _ => rfl
  | _ + 1, _ => Or.inl rfl

theorem ptrUp_parent {x y : NodeId} (hx : x ∈ ptrParents sp P y) :
    ∀ m z, PtrUp sp P m y z → PtrUp sp P (m + 1) x z := by
  intro m
  induction m with
  | zero => intro z h; subst h; exact Or.inr ⟨x, hx, rfl⟩
  | succ m ih =>
    intro z h
    rcases h with rfl | ⟨p, hp, hyp⟩
    · exact Or.inr ⟨x, hx, ptrUp_refl _ _⟩
    · exact Or.inr ⟨p, hp, ih p hyp⟩

theorem ptrUp_of_below {x z : NodeId} (h : PtrBelow sp P x z) :
    ∀ H, PtrHeightLe sp P H x → PtrUp sp P H x z := by
  induction h with
  | refl x => intro H _; exact ptrUp_refl H x
  | @step x y z n hn hy _ ih =>
    intro H hH
    cases H with
    | zero => rw [hH n hn] at hy; cases hy
    | succ H =>
      exact ptrUp_parent (mem_ptrParents.mpr ⟨n, hn, hy⟩) H z (ih H (hH n hn y hy))

/-- The nodes that reach z in at most m steps, without repeats, are at most
1 + Q + ... + Q^m with at most Q pointer parents per node. -/
theorem ptrUp_count (Q : Nat) (hQ : ∀ z, (ptrParents sp P z).length ≤ Q) :
    ∀ m z (L : List NodeId), L.Nodup → (∀ x ∈ L, PtrUp sp P m x z) → L.length ≤ geomSum Q m := by
  intro m
  induction m with
  | zero =>
    intro z L hnd hL
    exact length_le_one_of_nodup hnd (fun a ha b hb => by
      have h1 : a = z := hL a ha
      have h2 : b = z := hL b hb
      rw [h1, h2])
  | succ m ih =>
    intro z L hnd hL
    rw [length_filter_add L (fun x => x == z)]
    have h1 : (L.filter (fun x => x == z)).length ≤ 1 :=
      length_le_one_of_nodup (hnd.filter _) (fun a ha b hb => by
        simp only [List.mem_filter, beq_iff_eq] at ha hb
        rw [ha.2, hb.2])
    have h2 := nodup_length_le_sum (fun p x => PtrUp sp P m x p) (fun _ => geomSum Q m)
      (fun p L' hnd' hL' => ih p L' hnd' hL')
      (ptrParents sp P z) (L.filter (fun x => !(x == z))) (hnd.filter _) (by
        intro x hx
        obtain ⟨hxL, hne⟩ := List.mem_filter.mp hx
        rcases hL x hxL with h | ⟨p, hp, hxp⟩
        · simp [h] at hne
        · exact ⟨p, hp, hxp⟩)
    rw [sum_map_const] at h2
    have h3 := Nat.mul_le_mul_right (geomSum Q m) (hQ z)
    show _ ≤ 1 + Q * geomSum Q m
    omega

/-- The nodes of height at most H that reach a node with property A through
pointers: at most NA (1 + Q + ... + Q^H). -/
theorem ptrAnc_count_height (Q H : Nat) (hQ : ∀ z, (ptrParents sp P z).length ≤ Q)
    (A : NodeId → Prop) (NA : Nat)
    (hA : ∀ Z : List NodeId, Z.Nodup → (∀ z ∈ Z, A z) → Z.length ≤ NA)
    (L : List NodeId) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, (∃ z, PtrBelow sp P x z ∧ A z) ∧ PtrHeightLe sp P H x) :
    L.length ≤ NA * geomSum Q H := by
  classical
  let w : {x // x ∈ L} → NodeId := fun x => Classical.choose (hL x.1 x.2).1
  have hw : ∀ x (hx : x ∈ L), PtrBelow sp P x (w ⟨x, hx⟩) ∧ A (w ⟨x, hx⟩) :=
    fun x hx => Classical.choose_spec (hL x hx).1
  let Z := (L.attach.map w).eraseDups
  have hZnd : Z.Nodup := nodup_eraseDups _
  have hZA : ∀ z ∈ Z, A z := by
    intro z hz
    obtain ⟨⟨x, hx⟩, -, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hz)
    exact (hw x hx).2
  have h1 := nodup_length_le_sum (fun z x => PtrUp sp P H x z)
    (fun _ => geomSum Q H)
    (fun z L' hnd' hL' => ptrUp_count Q hQ H z L' hnd' hL')
    Z L hnd (by
      intro x hx
      refine ⟨w ⟨x, hx⟩, ?_, ptrUp_of_below (hw x hx).1 H (hL x hx).2⟩
      exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨⟨x, hx⟩, List.mem_attach _ _, rfl⟩))
  rw [sum_map_const] at h1
  have := Nat.mul_le_mul_right (geomSum Q H) (hA Z hZnd hZA)
  omega

end PtrUp

/-! ### The bounds by height -/

/-- T4's debt with BergDB's test, by height, counted with nodes of height at
most H. -/
theorem debt_count_java_h2 (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (H : Nat)
    (hH : ∀ e ∈ (run sp al ts).D, PtrHeightLe sp (run sp al ts).P H e.1) (N : Nat → Nat)
    (hN : ∀ τ (L : List NodeId), L.Nodup →
      (∀ x ∈ L, (∃ z, PtrBelow sp (run sp al ts).P x z ∧ onAccessPath sp al ts τ z) ∧
        PtrHeightLe sp (run sp al ts).P H x) → L.length ≤ N τ) :
    (run sp al ts).D.length ≤
      ((List.range' (spIter (run sp al ts).S (H + 1) ts.length + 1)
        (ts.length - spIter (run sp al ts).S (H + 1) ts.length)).map N).sum := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  have hinvK := inv_st sp al ts hok hst ts.length hK
  rw [st_length] at hinvK
  have hdebt := debtByChainsH_java sp al ts hok hj
  rw [← List.length_map (f := (·.1))]
  apply nodup_length_le_sum (fun τ x => (∃ z, PtrBelow sp (run sp al ts).P x z ∧
    onAccessPath sp al ts τ z) ∧ PtrHeightLe sp (run sp al ts).P H x) N hN _ _ hinvK.dNodup
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨τ, z, h1, h2, h3, h4⟩ := hdebt e he H (hH e he)
  refine ⟨τ, ?_, ⟨z, h3, h4⟩, hH e he⟩
  rw [List.mem_range'_1]
  omega

/-- T4's debt with BergDB's test and TREE, by height. -/
theorem debt_tree_java_h (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (htree : TreeRunOK sp al ts) (Hp Hl Q : Nat)
    (hHp : ∀ e ∈ (run sp al ts).D, PtrHeightLe sp (run sp al ts).P Hp e.1)
    (hHl : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t Hl root)
    (hQ : ∀ z, (ptrParents sp (run sp al ts).P z).length ≤ Q) :
    (run sp al ts).D.length ≤ geomSum Q Hp *
      ((List.range' (spIter (run sp al ts).S (Hp + 1) ts.length + 1)
        (ts.length - spIter (run sp al ts).S (Hp + 1) ts.length)).map (fun τ =>
          (Hl + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length) +
            (changeAt sp al ts τ).touch.length)).sum := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  rw [← sum_map_mul_left]
  apply debt_count_java_h2 sp al ts hok hj Hp hHp
  intro τ L hnd hL
  rw [Nat.mul_comm]
  refine ptrAnc_count_height Q Hp hQ (fun z => onAccessPath sp al ts τ z) _ ?_ L hnd hL
  intro Z hZnd hZ
  cases Z with
  | nil => exact Nat.zero_le _
  | cons x Z' =>
    obtain ⟨j, hj', rfl, -⟩ := onAccessPath_elim hok hst (hZ x (by simp))
    rw [changeAt_succ j hj']
    have hinv1 := inv_st sp al ts hok hst (j + 1) (by omega)
    obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp hinv1.rootIn
    exact accessPath_count_height hok hst hj' (by have := htree j hj'; simpa [st] using this) hn1
      (hHl (j + 1) (by omega)) (x :: Z') hZnd hZ

/-- A cold start's reads after a run with TREE, `DropRunOK`, without D, by
height. -/
theorem coldReads_height_of (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts) (hdrop : DropRunOK sp al ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    (lazyStartup sp (run sp al ts).S).next ≤
      (sectionNodes (run sp al ts).S (lastSp (run sp al ts).S)).length +
      ((sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + 2 * (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length) +
        (changeAt sp al ts j).new.length)).sum + 2 := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have h := coldReads_run_noD_of sp al ts hok hla htree hj
  have hle := sum_map_le (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S))
    (fun j => (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
      (changeAt sp al ts j).new.length)
    (fun j => (H + 1) * ((changeAt sp al ts j).new.length +
        2 * (changeAt sp al ts j).adds.length + (changeAt sp al ts j).touch.length) +
        (changeAt sp al ts j).new.length) (by
      intro j hj
      simp only [sectionIdx, List.mem_range'_1, run_length] at hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < ts.length := by omega
      have htj : treeAt sp (run sp al (ts.take j')).P j' := by
        rcases Nat.eq_zero_or_pos j' with h0' | hpos
        · subst h0'; rw [List.take_zero]; exact htree0
        · obtain ⟨j'', hj''⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
          subst hj''
          exact htree j'' (by omega)
      have hinvj := inv_st sp al ts hok hst j' (by omega)
      obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hinvj.rootIn
      have hp := pathOf_count_height (P := (st sp al ts j').P) (j := j' + 1)
        (by simpa [st] using htj) hnr (by simpa [st] using hH j' (by omega))
        (changeAt sp al ts (j' + 1))
      have hr := removedAt_le_adds sp _ _ _ (hdrop j' hj')
      rw [changeAt_succ j' hj'] at hp ⊢
      simp only [Nat.add_sub_cancel, chg, st] at hp hr ⊢
      have := Nat.mul_le_mul_left (H + 1)
        (show (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length +
            (removedAt sp (run sp al (List.take j' ts)).P
              (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')) (j' + 1)).length ≤
          (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).new.length +
            2 * (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).adds.length +
            (sp.exec ts[j'] (j' + 1) (view sp (run sp al (List.take j' ts)).P j')).touch.length by
          omega)
      omega)
  omega

end SIS
