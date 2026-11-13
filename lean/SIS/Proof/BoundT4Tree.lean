/-
Proofs for bounds, part 2 (bergdb item 007): T4 with TREE, the size of the
access path of a change (SIS/BoundT4.lean, `T4_debt_tree`). Added 2026-11-13.

With TREE at time t (`treeAt`: every reachable node but the root is the live
child of exactly one reachable node), the reachable nodes with a given node z
below them at t, z included, are on distinct levels (`anc_level_inj`), so there
are at most H + 1 of them, H the root's level. The access path of a change is
such nodes for the changed nodes, and the touched nodes.
-/
import SIS.Proof.BoundT4Debt

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Paths

variable (sp : Spec V T) (P : Struct V) (t : Time)

/-- A node below x is x, or on a lower level than x. -/
theorem reachFrom_level :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b → P.get? x = some n →
      ∀ z ∈ reachFrom sp P t x n, ∀ m, P.get? z = some m → z = x ∨ m.level < n.level := by
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb hx z hz m hm
    rw [reachFrom_eq] at hz
    simp only [List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | ⟨y, -, hz⟩
    · left; rfl
    · right
      split at hz
      · rename_i my hmy
        split at hz
        · rename_i hlt
          rcases ih y my (by omega) hmy z hz m hm with rfl | h
          · rw [hmy] at hm; cases hm; exact hlt
          · omega
        · simp at hz
      · simp at hz

/-- A node below x other than x is a live child of a node below x, on a lower
level than it. -/
theorem reachFrom_parent :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b → P.get? x = some n →
      ∀ z ∈ reachFrom sp P t x n, z ≠ x →
        ∃ q nq m, q ∈ reachFrom sp P t x n ∧ P.get? q = some nq ∧ z ∈ sp.live (nq.hist.upTo t) ∧
          P.get? z = some m ∧ m.level < nq.level := by
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb hx z hz hzx
    have hz' := hz
    rw [reachFrom_eq] at hz'
    simp only [List.mem_cons, List.mem_flatMap] at hz'
    rcases hz' with rfl | ⟨y, hy, hzy⟩
    · exact absurd rfl hzx
    · split at hzy
      · rename_i my hmy
        split at hzy
        · rename_i hlt
          by_cases hzy' : z = y
          · subst hzy'
            exact ⟨x, n, my, self_mem_reachFrom sp P t x n, hx, hy, hmy, hlt⟩
          · obtain ⟨q, nq, m, hq, hnq, hzq, hm, hlt'⟩ := ih y my (by omega) hmy z hzy hzy'
            exact ⟨q, nq, m, reachFrom_child_sub sp hy hmy hlt q hq, hnq, hzq, hm, hlt'⟩
        · simp at hzy
      · simp at hzy

end Paths

/-! ### TREE: one parent, ancestors on distinct levels -/

theorem filter_length_one {L : List NodeId} {p : NodeId → Bool} (h : (L.filter p).length = 1)
    {q1 q2 : NodeId} (h1 : q1 ∈ L) (hp1 : p q1 = true) (h2 : q2 ∈ L) (hp2 : p q2 = true) :
    q1 = q2 := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
  have e1 : q1 ∈ L.filter p := List.mem_filter.mpr ⟨h1, hp1⟩
  have e2 : q2 ∈ L.filter p := List.mem_filter.mpr ⟨h2, hp2⟩
  rw [ha] at e1 e2
  simp at e1 e2
  rw [e1, e2]

theorem sum_map_const (l : List Nat) (c : Nat) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Nat.succ_mul]; omega

section Tree

variable {sp : Spec V T} {P : Struct V} {t : Time}

/-- With TREE, two reachable nodes that both have z as a live child are the
same node. -/
theorem tree_parent_unique (htree : treeAt sp P t) {z : NodeId} (hz : reachable sp P t z = true)
    (hzr : z ≠ root) {q1 q2 : NodeId} {n1 n2 : Node V} (hq1 : reachable sp P t q1 = true)
    (hq2 : reachable sp P t q2 = true) (hn1 : P.get? q1 = some n1) (hn2 : P.get? q2 = some n2)
    (hz1 : z ∈ sp.live (n1.hist.upTo t)) (hz2 : z ∈ sp.live (n2.hist.upTo t)) : q1 = q2 := by
  have h := htree z hz hzr
  have hm1 : q1 ∈ reachList sp P t := by simpa [reachable] using hq1
  have hm2 : q2 ∈ reachList sp P t := by simpa [reachable] using hq2
  exact filter_length_one h (List.mem_eraseDups.mpr hm1) (by simp only [hn1]; simpa using hz1)
    (List.mem_eraseDups.mpr hm2) (by simp only [hn2]; simpa using hz2)

/-- x is an ancestor of z at t: reachable at t, with z below it then (x = z
included). -/
def AncAt (sp : Spec V T) (P : Struct V) (t : Time) (z x : NodeId) : Prop :=
  reachable sp P t x = true ∧ ∃ nx, P.get? x = some nx ∧ z ∈ reachFrom sp P t x nx

/-- With TREE, two ancestors of z on the same level are the same node. -/
theorem anc_level_inj (htree : treeAt sp P t) :
    ∀ (b : Nat) (z : NodeId) (m : Node V) (x1 x2 : NodeId) (n1 n2 : Node V),
      P.get? z = some m → n1.level - m.level < b →
      reachable sp P t x1 = true → P.get? x1 = some n1 → z ∈ reachFrom sp P t x1 n1 →
      reachable sp P t x2 = true → P.get? x2 = some n2 → z ∈ reachFrom sp P t x2 n2 →
      n1.level = n2.level → x1 = x2 := by
  intro b
  induction b with
  | zero => intro z m x1 x2 n1 n2 _ h; omega
  | succ b ih =>
    intro z m x1 x2 n1 n2 hm hb hr1 hn1 hz1 hr2 hn2 hz2 hlv
    have hl1 := reachFrom_level sp P t (n1.level + 1) x1 n1 (by omega) hn1 z hz1 m hm
    have hl2 := reachFrom_level sp P t (n2.level + 1) x2 n2 (by omega) hn2 z hz2 m hm
    by_cases h1 : z = x1
    · subst h1
      rw [hm, Option.some.injEq] at hn1; subst hn1
      rcases hl2 with h | h
      · exact h.symm ▸ rfl
      · omega
    by_cases h2 : z = x2
    · subst h2
      rw [hm, Option.some.injEq] at hn2; subst hn2
      rcases hl1 with h | h
      · exact absurd h h1
      · omega
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
    have hlq1 := reachFrom_level sp P t (n1.level + 1) x1 n1 (by omega) hn1 q1 hq1 nq1 hnq1
    have hle : nq1.level ≤ n1.level := by
      rcases hlq1 with h | h
      · subst h; rw [hn1, Option.some.injEq] at hnq1; subst hnq1; omega
      · omega
    exact ih q1 nq1 x1 x2 n1 n2 hnq1 (by omega) hr1 hn1 hq1 hr2 hn2 hq2 hlv

/-- With TREE, the ancestors of a node at t, without repeats, are at most H + 1,
H the root's level. -/
theorem anc_count (htree : treeAt sp P t) {n0 : Node V} (h0 : P.get? root = some n0) (z : NodeId)
    (L : List NodeId) (hnd : L.Nodup) (hL : ∀ x ∈ L, AncAt sp P t z x) :
    L.length ≤ n0.level + 1 := by
  classical
  have hW : ∀ x ∈ L, ∃ ℓ ∈ List.range (n0.level + 1), AncAt sp P t z x ∧ levelOf P x = ℓ := by
    intro x hx
    obtain ⟨hr, nx, hnx, -⟩ := hL x hx
    refine ⟨levelOf P x, ?_, hL x hx, rfl⟩
    rw [List.mem_range, levelOf_of_get hnx]
    rw [reachable_iff] at hr
    rcases reach_level_root hr h0 nx hnx with h | h
    · subst h; rw [h0, Option.some.injEq] at hnx; subst hnx; omega
    · omega
  have := nodup_length_le_sum (fun ℓ x => AncAt sp P t z x ∧ levelOf P x = ℓ) (fun _ => 1)
    (by
      intro ℓ L' hnd' hL'
      apply length_le_one_of_nodup hnd'
      intro a ha b hb
      obtain ⟨⟨hra, na, hna, hza⟩, hla⟩ := hL' a ha
      obtain ⟨⟨hrb, nb, hnb, hzb⟩, hlb⟩ := hL' b hb
      obtain ⟨m, hm⟩ : ∃ m, P.get? z = some m := by
        have hrz : Reach sp P t z := by
          rw [reachable_iff] at hra
          exact reach_of_mem_reachFrom sp P t (na.level + 1) a na (by omega) hna hra z hza
        exact Option.isSome_iff_exists.mp hrz.isSome
      rw [levelOf_of_get hna] at hla
      rw [levelOf_of_get hnb] at hlb
      exact anc_level_inj htree (na.level + 1) z m a b na nb hm (by omega) hra hna hza hrb hnb hzb
        (by omega))
    (List.range (n0.level + 1)) L hnd hW
  rw [sum_map_const, List.length_range] at this
  omega

end Tree

/-! ### The access path of a change -/

section Change

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- With TREE after T(j + 1), the nodes on the access path of its change, without
repeats, are at most (H + 1) times its changed nodes, plus its touched ones. -/
theorem accessPath_count (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat} (hj : j < ts.length)
    (htree : treeAt sp (st sp al ts (j + 1)).P (j + 1)) {n0 : Node V}
    (h0 : (st sp al ts (j + 1)).P.get? root = some n0) (L : List NodeId) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, onAccessPath sp al ts (j + 1) x) :
    L.length ≤ (n0.level + 1) * ((chg sp al ts j hj).new.length + (chg sp al ts j hj).adds.length) +
      (chg sp al ts j hj).touch.length := by
  classical
  have hL' : ∀ x ∈ L, marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x = true ∨
      x ∈ (chg sp al ts j hj).touch := by
    intro x hx
    obtain ⟨j', hj', hjj, h⟩ := onAccessPath_elim hok hst (hL x hx)
    obtain rfl : j' = j := by omega
    exact h
  rw [length_filter_add L (fun x => marked sp (st sp al ts (j + 1)).P (chg sp al ts j hj) (j + 1) x)]
  -- The marked nodes: ancestors of a changed node.
  have h1 := nodup_length_le_sum (fun z x => AncAt sp (st sp al ts (j + 1)).P (j + 1) z x)
    (fun _ => n0.level + 1)
    (fun z L' hnd' hL'' => anc_count htree h0 z L' hnd' hL'')
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
  -- The others: touched.
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
  have : (n0.level + 1) * ((chg sp al ts j hj).new.length + (chg sp al ts j hj).adds.length) =
      ((chg sp al ts j hj).new.length + (chg sp al ts j hj).adds.length) * (n0.level + 1) :=
    Nat.mul_comm _ _
  omega

theorem changeAt_succ (j : Nat) (hj : j < ts.length) :
    changeAt sp al ts (j + 1) = chg sp al ts j hj := by
  simp only [changeAt, List.getElem?_eq_getElem hj]
  rfl

end Change

/-- T4 with TREE: the debt of D counted by the changes of the last H + 1
sections, H the root's level. -/
theorem debt_tree_exact (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hex : al.stillDirty = exactTest sp) (hv : sp.virt = false) (htree : TreeRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) :
    (run sp al ts).D.length ≤
      ((List.range' (spIter (run sp al ts).S (n0.level + 1) ts.length + 1)
        (ts.length - spIter (run sp al ts).S (n0.level + 1) ts.length)).map (fun τ =>
          (n0.level + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length) +
            (changeAt sp al ts τ).touch.length)).sum := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inr ⟨hv, hex⟩)
  have hK : ts.length ≤ ts.length := Nat.le_refl _
  have hinvK := inv_st sp al ts hok hst ts.length hK
  rw [st_length] at hinvK
  apply debt_count_exact sp al ts hok hex hv n0.level
  · -- The nodes of D are on levels up to the root's.
    intro e he
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (isSome_of_isIndex (hinvK.dIndex e he))
    obtain ⟨t, -, hr⟩ := hinvK.born e.1 (by rw [hn]; rfl)
    rw [reachable_iff] at hr
    rw [levelOf_of_get hn]
    rcases reach_level_root hr h0 n hn with h | h
    · rw [h, h0, Option.some.injEq] at hn; subst hn; omega
    · omega
  · intro τ L hnd hL
    cases L with
    | nil => exact Nat.zero_le _
    | cons x L' =>
      obtain ⟨j, hj, rfl, -⟩ := onAccessPath_elim hok hst (hL x (by simp))
      rw [changeAt_succ j hj]
      have hinv1 := inv_st sp al ts hok hst (j + 1) (by omega)
      obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp hinv1.rootIn
      have hg := st_grow sp al ts hok hst (j := j + 1) (j' := ts.length) (by omega) hK
      obtain ⟨n1K, hn1K, hl, -, -⟩ := hg root n1 hn1
      rw [st_length, h0, Option.some.injEq] at hn1K
      subst hn1K
      have := accessPath_count hok hst hj (by have := htree j hj; simpa [st] using this) hn1
        (x :: L') hnd hL
      rw [← hl] at this
      exact this

end SIS
