import SIS.Tree.GetInnerSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The space split of an inner node after a space split below it (bergdb
024-12, TP10; the cascades): the halves of an inner node's last version with
klongs put on one side of its divider find what the node with the klongs
found, by compare value (`halves_inner_searchLte_ins`). -/

theorem halves_inner_searchLte_ins (qn Q : KNode) (t : Time) (ins : List (Nat × NodeId))
    (hql : qn.leaf = false)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hside : (∀ q ∈ ins, r.1 ≤ q.1) ∨ (∀ q ∈ ins, q.1 < r.1))
    (hQt : ∀ s, Klong.time s ∈ Q.ks → s ≤ t)
    (hQlook : ∀ c, Q.live.lookup c = ins.foldl (pairLookupStep c) (qn.live.lookup c)) :
    let out := halves qn.leaf t (qn.lastVersion t) ins
    out.2.2 = r.1 ∧ out.1.leaf = false ∧ out.2.1.leaf = false ∧
      klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c : Nat, c < r.1 → (out.1.searchLte t c).map (·.y) =
        (Q.searchLte t c).map (·.y)) ∧
      (∀ c : Nat, r.1 ≤ c → (out.2.1.searchLte t c).map (·.y) =
        (Q.searchLte t c).map (·.y)) := by
  intro out
  have hlv := KNode.lastVersion_eq_newKlongs qn t
  rw [hql] at hlv
  have hout : out = halves false t ⟨false, newKlongs t qn.live⟩ ins := by
    simp only [out, hql, hlv]
  have hs : CvSorted qn.live := qn.live_order
  have hshape := halves_shape false t qn.live ins r hr
  have hside' : ∀ q ∈ ins, decide (r.1 ≤ q.1) =
      (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false) := by
    intro q hq
    cases hins : ins with
    | nil => rw [hins] at hq; cases hq
    | cons a rest =>
      rw [hins] at hq hside
      simp only [List.head?_cons]
      rcases hside with h | h
      · simp [h q hq, h a List.mem_cons_self]
      · have h1 := h q hq
        have h2 := h a List.mem_cons_self
        simp only [decide_eq_decide]
        omega
  have hlook := halves_lookup false t qn.live ins hs r hr hsc hside'
  rw [← hout] at hlook hshape
  simp only at hlook
  have hleft := halves_left_lt_divider qn.live (qn.live.length / 2) hs r hr
  have hright := halves_right_ge_divider qn.live (qn.live.length / 2) hs r hr
  -- the first half's and the second half's live klongs
  have hdrop : ∀ q ∈ (qn.live.drop (qn.live.length / 2)).tail, r.1 < q.1 := by
    have hd := hs.sublist (List.drop_sublist (qn.live.length / 2) qn.live)
    cases he : qn.live.drop (qn.live.length / 2) with
    | nil => rw [he] at hr; cases hr
    | cons a rest =>
      rw [he] at hr hd
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst hr
      intro q hq
      simp only [List.tail_cons] at hq
      exact (List.pairwise_cons.mp hd).1 q hq
  have hsec : ∀ c z, (c, z) ∈ secondSplitPairs false qn.live → c = 0 ∨ r.1 < c := by
    intro c z hcz
    simp only [secondSplitPairs, Bool.false_eq_true, ↓reduceIte] at hcz
    cases he : qn.live.drop (qn.live.length / 2) with
    | nil => rw [he] at hr; cases hr
    | cons a rest =>
      rw [he] at hcz hdrop
      simp only [renameHead, List.mem_cons, Prod.mk.injEq] at hcz
      rcases hcz with ⟨h1, _⟩ | h1
      · exact Or.inl h1
      · exact Or.inr (hdrop (c, z) (by simpa using h1))
  have htimesNK : ∀ (l : List (Nat × NodeId)), ∀ s, Klong.time s ∈ (⟨false, newKlongs t l⟩ : KNode).ks → s ≤ t :=
    fun l => newKlongs_times t l
  obtain ⟨hsc', hl1, hl2, hw1, hw2, ht1, ht2, hF, hS⟩ : out.2.2 = r.1 ∧ out.1.leaf = false ∧
      out.2.1.leaf = false ∧ klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c z, (c, z) ∈ out.1.live → c < r.1) ∧
      (∀ c z, (c, z) ∈ out.2.1.live → c = 0 ∨ r.1 < c) := by
    have htrue : (∀ a ∈ ins, r.1 ≤ a.1) →
        ∀ (A : KNode × KNode × Nat), A = (⟨false, newKlongs t (qn.live.take (qn.live.length / 2))⟩,
          ⟨false, newKlongs t (secondSplitPairs false qn.live ++
            ins.map (fun q => (splitLocalCv false r.1 q.1, q.2)))⟩, r.1) →
        A.2.2 = r.1 ∧ A.1.leaf = false ∧
        A.2.1.leaf = false ∧ klongsWf A.1.ks = true ∧ klongsWf A.2.1.ks = true ∧
        (∀ s, Klong.time s ∈ A.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ A.2.1.ks → s ≤ t) ∧
        (∀ c z, (c, z) ∈ A.1.live → c < r.1) ∧
        (∀ c z, (c, z) ∈ A.2.1.live → c = 0 ∨ r.1 < c) := by
      intro hin A hA
      subst hA
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        exact hleft (c, z) (newKlongs_live_mem false t _ c z hcz)
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hsec c z h1
        · obtain ⟨a, ha, hae⟩ := List.mem_map.mp h1
          have hra : r.1 ≤ a.1 := hin a ha
          simp only [Prod.mk.injEq] at hae
          rw [← hae.1]
          simp only [splitLocalCv, Bool.not_false, Bool.true_and]
          by_cases hk : a.1 = r.1
          · simp [hk]
          · have hk' : (a.1 == r.1) = false := by simpa using hk
            simp only [hk', Bool.false_eq_true, ↓reduceIte]
            right; omega
    have hfalse : (∀ a ∈ ins, a.1 < r.1) →
        ∀ (A : KNode × KNode × Nat), A = (⟨false, newKlongs t (qn.live.take (qn.live.length / 2) ++ ins)⟩,
          ⟨false, newKlongs t (secondSplitPairs false qn.live)⟩, r.1) →
        A.2.2 = r.1 ∧ A.1.leaf = false ∧
        A.2.1.leaf = false ∧ klongsWf A.1.ks = true ∧ klongsWf A.2.1.ks = true ∧
        (∀ s, Klong.time s ∈ A.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ A.2.1.ks → s ≤ t) ∧
        (∀ c z, (c, z) ∈ A.1.live → c < r.1) ∧
        (∀ c z, (c, z) ∈ A.2.1.live → c = 0 ∨ r.1 < c) := by
      intro hin A hA
      subst hA
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hleft (c, z) h1
        · exact hin (c, z) h1
      · intro c z hcz
        exact hsec c z (newKlongs_live_mem false t _ c z hcz)
    rw [hshape]
    split
    · rename_i a hhead
      have ha : a ∈ ins := List.mem_of_head? hhead
      split
      · rename_i hc
        simp only [decide_eq_true_eq] at hc
        refine htrue ?_ _ rfl
        intro b hb
        rcases hside with h | h
        · exact h b hb
        · have := h a ha; omega
      · rename_i hc
        simp only [decide_eq_true_eq] at hc
        refine hfalse ?_ _ rfl
        intro b hb
        rcases hside with h | h
        · have := h a ha; omega
        · exact h b hb
    · rename_i hhead
      have hnil : ins = [] := List.head?_eq_none_iff.mp hhead
      exact hfalse (by rw [hnil]; intro b hb; cases hb) _ rfl
  rw [hsc'] at hlook
  -- the parent with the klongs, as a lookup
  have hQlook' := hQlook
  have hmemQ : ∀ a z, (a, z) ∈ Q.live ↔ Q.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem1 : ∀ a z, (a, z) ∈ out.1.live ↔ out.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem2 : ∀ a z, (a, z) ∈ out.2.1.live ↔ out.2.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  -- below r.1 the first half and the parent agree
  have hlow : ∀ a z, a < r.1 → ((a, z) ∈ out.1.live ↔ (a, z) ∈ Q.live) := by
    intro a z ha
    rw [hmem1, hmemQ, hQlook', ← hlook a]
    simp [ha]
  -- from r.1 on the second half and the parent agree, r.1 named the empty key
  have hspl : ∀ a, r.1 ≤ a → splitLocalCv false r.1 a = if a = r.1 then 0 else a := by
    intro a _
    simp only [splitLocalCv, Bool.not_false, Bool.true_and]
    by_cases h : a = r.1
    · simp [h]
    · have h' : (a == r.1) = false := by simpa using h
      simp [h', h]
  have hhigh : ∀ a z, r.1 < a → ((a, z) ∈ out.2.1.live ↔ (a, z) ∈ Q.live) := by
    intro a z ha
    rw [hmem2, hmemQ, hQlook', ← hlook a, hspl a (by omega)]
    simp [show ¬ a < r.1 by omega, show a ≠ r.1 by omega]
  have hzero : ∀ z, (0, z) ∈ out.2.1.live ↔ (r.1, z) ∈ Q.live := by
    intro z
    rw [hmem2, hmemQ, hQlook', ← hlook r.1, hspl r.1 (Nat.le_refl _)]
    simp
  have hsQ := Q.searchLte_spec t
  refine ⟨hsc', hl1, hl2, hw1, hw2, ht1, ht2, ?_, ?_⟩
  · intro c hc
    have hs := hsQ c
    unfold NodeSearchSpec at hs
    rw [KNode.liveAt_of_times _ t hQt] at hs
    cases hq : Q.searchLte t c with
    | none =>
      have hall := hs.2.mp hq
      rw [KNode.searchLte_none_of out.1 t ht1 c (fun q hq1 => by
        have hqr := hF q.1 q.2 hq1
        have := hall q ((hlow q.1 q.2 hqr).mp hq1)
        simp only [decide_eq_false_iff_not] at this
        omega)]
    | some f =>
      obtain ⟨hfm, hfa, hfmax⟩ := hs.1 f hq
      simp only [decide_eq_true_eq] at hfa
      have hfr : f.c < r.1 := by omega
      rw [KNode.searchLte_of_max out.1 t ht1 c f.c f.y ((hlow f.c f.y hfr).mpr hfm) hfa
        (fun q hq1 hqc => by
          have := hfmax q ((hlow q.1 q.2 (hF q.1 q.2 hq1)).mp hq1) (by simpa using hqc)
          simpa using this)]
      rfl
  · intro c hc
    have hs := hsQ c
    unfold NodeSearchSpec at hs
    rw [KNode.liveAt_of_times _ t hQt] at hs
    -- the parent has a klong of r.1
    obtain ⟨zr, hzr⟩ : ∃ z, (r.1, z) ∈ Q.live := by
      have hrm : r ∈ qn.live := List.mem_of_mem_drop (List.mem_of_head? hr)
      have hl := lookup_some_of_mem (KNode.live_keys_nodup qn) hrm
      have hq := hQlook r.1
      rw [hl, pairLookupFold_reverse] at hq
      cases hx : ins.reverse.lookup r.1 with
      | none => rw [hx] at hq; exact ⟨r.2, (hmemQ _ _).mpr hq⟩
      | some y => rw [hx] at hq; exact ⟨y, (hmemQ _ _).mpr hq⟩
    cases hq : Q.searchLte t c with
    | none =>
      have := hs.2.mp hq (r.1, zr) hzr
      simp only [decide_eq_false_iff_not] at this
      omega
    | some f =>
      obtain ⟨hfm, hfa, hfmax⟩ := hs.1 f hq
      simp only [decide_eq_true_eq] at hfa
      have hfr : r.1 ≤ f.c := by
        have := hfmax (r.1, zr) hzr (by simp only [decide_eq_true_eq]; omega)
        simpa using this
      by_cases hfe : f.c = r.1
      · have hm0 : (0, f.y) ∈ out.2.1.live := (hzero f.y).mpr (by rw [← hfe]; exact hfm)
        rw [KNode.searchLte_of_max out.2.1 t ht2 c 0 f.y hm0 (by omega) (fun q hq2 hqc => by
          rcases hS q.1 q.2 hq2 with h0 | hgt
          · omega
          · have := hfmax q ((hhigh q.1 q.2 hgt).mp hq2) (by simpa using hqc)
            simp only [decide_eq_true_eq] at this
            omega)]
        rfl
      · have hfgt : r.1 < f.c := by omega
        rw [KNode.searchLte_of_max out.2.1 t ht2 c f.c f.y ((hhigh f.c f.y hfgt).mpr hfm) hfa
          (fun q hq2 hqc => by
            rcases hS q.1 q.2 hq2 with h0 | hgt
            · omega
            · have := hfmax q ((hhigh q.1 q.2 hgt).mp hq2) (by simpa using hqc)
              simpa using this)]
        rfl

end SIS.Tree
