/-
Proofs about the physical layer, part 10: the rerun of a lazy startup keeps
the invariant (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysPath

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Reach

variable {sp : Spec V T} {db dbK : DB V T} {K k : Nat} {m : Mem V}

/-- The writer reaches one node of a path. -/
theorem MemInv.reachOnPath_ok (hm : MemInv sp db K m) (hctx : PCtx sp db k)
    (hk : KCtx sp db dbK K) {P : Struct V} (hPs : SameNodes P dbK.P) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P K p = true) (x : NodeId) :
    MemInv sp db K (m.reachOnPath sp db.S P (K + 1) path x) ∧
      m.Le (m.reachOnPath sp db.S P (K + 1) path x) ∧
      ((∃ p ∈ path, ∃ np, P.get? p = some np ∧ m.canonicalOf p ≠ none ∧
          x ∈ sp.live (np.hist.upTo K)) →
        (m.reachOnPath sp db.S P (K + 1) path x).canonicalOf x ≠ none) := by
  unfold Mem.reachOnPath
  cases hcx : m.canonicalOf x with
  | some h0 =>
    simp only
    exact ⟨hm, Mem.Le.refl m, fun _ => by rw [hcx]; simp⟩
  | none =>
    simp only
    have hK1 : K + 1 - 1 = K := by omega
    cases hf : path.find? (fun p => match P.get? p, m.canonicalOf p with
        | some n, some _ => (sp.live (n.hist.upTo (K + 1 - 1))).contains x
        | _, _ => false) with
    | none =>
      simp only
      refine ⟨hm, Mem.Le.refl m, ?_⟩
      rintro ⟨p, hp, np, hnp, hcp, hxl⟩
      exfalso
      rw [List.find?_eq_none] at hf
      apply hf p hp
      rw [hnp]
      cases hc : m.canonicalOf p with
      | none => exact absurd hc hcp
      | some _ => simp only [hK1]; exact List.contains_iff_mem.mpr hxl
    | some p =>
      simp only
      have hpp := List.find?_some hf
      have hpm := List.mem_of_find?_eq_some hf
      cases hnp : P.get? p with
      | none => rw [hnp] at hpp; simp at hpp
      | some np =>
        cases hcp : m.canonicalOf p with
        | none => rw [hnp, hcp] at hpp; simp at hpp
        | some hp =>
          simp only
          rw [hnp, hcp] at hpp
          simp only [hK1, List.contains_iff_mem] at hpp
          obtain ⟨ht, op, hop, hcan⟩ := (m.canonicalOf_eq_some p hp).mp hcp
          obtain ⟨op', hop', hnode⟩ := hm.tbl p hp ht
          rw [hop, Option.some.injEq] at hop'
          subst hop'
          obtain ⟨-, ⟨nf, hnf, hh, -, -⟩, -⟩ := hm.canon hp op hop hcan
          have hxop : x ∈ sp.live op.hist := by
            rw [hh]
            have hnpK : dbK.P.get? p = some np := by rw [← hPs p]; exact hnp
            obtain ⟨n', hn', -, -, hh'⟩ := hk.grow p np hnpK
            rw [hnode] at hnf
            have hnn : nf = n' := by rw [hnf, Option.some.injEq] at hn'; exact hn'
            rw [hnn, hh']
            exact hpp
          obtain ⟨m', h1, hev, hm', hle, hc'⟩ :=
            hm.follow_writer hctx hk hop hcan (by rw [hnode]; exact hpath p hpm) hxop
          rw [hev]
          exact ⟨hm', hle, fun _ => by rw [hc']; simp⟩


theorem Mem.Le.ne_none {m m' : Mem V} (hle : m.Le m') {x : NodeId} (hx : m.canonicalOf x ≠ none) :
    m'.canonicalOf x ≠ none := by
  cases hc : m.canonicalOf x with
  | none => exact absurd hc hx
  | some h => rw [hle.canon x h hc]; simp

/-- The writer reaches every node of the paths, highest level first. -/
theorem MemInv.reachPath_ok (hctx : PCtx sp db k) (hk : KCtx sp db dbK K) {P : Struct V}
    (hPs : SameNodes P dbK.P) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P K p = true)
    (hparent : ∀ x ∈ path, x ≠ SIS.root → ∃ p ∈ path, ∃ np nx, P.get? p = some np ∧
      P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo K)) :
    ∀ (L A : List NodeId) (m : Mem V), MemInv sp db K m → (∀ a ∈ A, m.canonicalOf a ≠ none) →
      (∀ x, x ∈ A ++ L ↔ x ∈ path) →
      (A ++ L).Pairwise (fun a b => lev P b ≤ lev P a) →
      MemInv sp db K (L.foldl (Mem.reachOnPath sp db.S P (K + 1) path) m) ∧
        m.Le (L.foldl (Mem.reachOnPath sp db.S P (K + 1) path) m) ∧
        ∀ x ∈ path, (L.foldl (Mem.reachOnPath sp db.S P (K + 1) path) m).canonicalOf x ≠ none := by
  intro L
  induction L with
  | nil =>
    intro A m hm hA hmem _
    refine ⟨hm, Mem.Le.refl m, fun x hx => hA x ?_⟩
    have := (hmem x).mpr hx
    simpa using this
  | cons x L ih =>
    intro A m hm hA hmem hsort
    simp only [List.foldl_cons]
    obtain ⟨hm1, hle1, hc1⟩ := hm.reachOnPath_ok hctx hk hPs hpath x
    have hx1 : (m.reachOnPath sp db.S P (K + 1) path x).canonicalOf x ≠ none := by
      by_cases hcx : m.canonicalOf x ≠ none
      · exact hle1.ne_none hcx
      · apply hc1
        have hxr : x ≠ SIS.root := by
          intro hxr
          apply hcx
          rw [hxr]
          exact hm.cover.rootC
        obtain ⟨p, hp, np, nx, hnp, hnx, hlt, hxl⟩ := hparent x ((hmem x).mp (by simp)) hxr
        refine ⟨p, hp, np, hnp, ?_, hxl⟩
        -- p is before x in the sorted list: in A
        have hpA : p ∈ A := by
          have hpAL := (hmem p).mpr hp
          rcases List.mem_append.mp hpAL with h | h
          · exact h
          · exfalso
            rcases List.mem_cons.mp h with h | h
            · subst h; rw [hnp, Option.some.injEq] at hnx; subst hnx; omega
            · have hs := List.pairwise_append.mp hsort
              have := List.pairwise_cons.mp hs.2.1
              have := this.1 p h
              simp [lev, hnp, hnx] at this
              omega
        exact hA p hpA
    have := ih (A ++ [x]) _ hm1
      (by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hle1.ne_none (hA a h)
        · rw [List.mem_singleton] at h; subst h; exact hx1)
      (by intro y; rw [← hmem y]; simp)
      (by simpa using hsort)
    exact ⟨this.1, hle1.trans this.2.1, this.2.2⟩

/-- The writer reaches a node of a path the same way with streams that agree. -/
theorem reachOnPath_congr_stream {S S' : Stream V T} (hag : StreamAgree m S S') (P : Struct V)
    (j : Time) (path : List NodeId) (x : NodeId) :
    m.reachOnPath sp S P j path x = m.reachOnPath sp S' P j path x := by
  unfold Mem.reachOnPath
  simp only [follow_congr hag]

/-- The writer reaches the nodes of the paths the same way with a stream S_f that
agrees with the run's. -/
theorem MemInv.reachFold_congr (hctx : PCtx sp db k) (hk : KCtx sp db dbK K) {P : Struct V}
    (hPs : SameNodes P dbK.P) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P K p = true) {S_f : Stream V T} :
    ∀ (L : List NodeId) (m : Mem V), MemInv sp db K m → StreamAgree m S_f db.S →
      L.foldl (Mem.reachOnPath sp S_f P (K + 1) path) m =
        L.foldl (Mem.reachOnPath sp db.S P (K + 1) path) m := by
  intro L
  induction L with
  | nil => intro m _ _; rfl
  | cons x L ih =>
    intro m hm hag
    simp only [List.foldl_cons]
    rw [reachOnPath_congr_stream hag]
    obtain ⟨hm1, hle1, -⟩ := hm.reachOnPath_ok hctx hk hPs hpath x
    exact ih _ hm1 (hag.le hle1 (by rw [hm1.sEq, hm.sEq]))

end Reach

end SIS
