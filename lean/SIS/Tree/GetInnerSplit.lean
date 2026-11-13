import SIS.Tree.GetChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The space split of an inner node (bergdb 024-12, TP10; the cascades): the
halves of an inner node's last version with a klong put find, for compare values
below the second half's first one, what the first half finds, and from it on,
what the second finds, the second half's first klong renamed to the empty key
(`halves_inner_searchLte`). -/

theorem halves_inner_searchLte (qn : KNode) (t : Time) (k1 : Nat) (Y : NodeId)
    (hql : qn.leaf = false) (hw : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1) :
    let out := halves qn.leaf t (qn.lastVersion t) [(k1, Y)]
    out.2.2 = r.1 ∧ out.1.leaf = false ∧ out.2.1.leaf = false ∧
      klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c : Nat, c < r.1 → (out.1.searchLte t c).map (·.y) =
        ((qn.add t (.key k1 Y)).searchLte t c).map (·.y)) ∧
      (∀ c : Nat, r.1 ≤ c → (out.2.1.searchLte t c).map (·.y) =
        ((qn.add t (.key k1 Y)).searchLte t c).map (·.y)) := by
  intro out
  have hlv := KNode.lastVersion_eq_newKlongs qn t
  rw [hql] at hlv
  have hout : out = halves false t ⟨false, newKlongs t qn.live⟩ [(k1, Y)] := by
    simp only [out, hql, hlv]
  have hs : CvSorted qn.live := qn.live_order
  have hshape := halves_shape false t qn.live [(k1, Y)] r hr
  simp only [List.head?_cons] at hshape
  have hlook := halves_lookup false t qn.live [(k1, Y)] hs r hr hsc (by simp)
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
    by_cases hc : r.1 ≤ k1
    · simp only [hc, decide_true, ↓reduceIte] at hshape
      rw [hshape]
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        exact hleft (c, z) (newKlongs_live_mem false t _ c z hcz)
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hsec c z h1
        · simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at h1
          obtain ⟨h1, _⟩ := h1
          subst h1
          simp only [splitLocalCv, Bool.not_false, Bool.true_and]
          by_cases hk : k1 = r.1
          · simp [hk]
          · have hk' : (k1 == r.1) = false := by simpa using hk
            simp only [hk', Bool.false_eq_true, ↓reduceIte]
            right; omega
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hshape
      rw [hshape]
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hleft (c, z) h1
        · simp only [List.mem_singleton, Prod.mk.injEq] at h1
          rw [h1.1]; omega
      · intro c z hcz
        exact hsec c z (newKlongs_live_mem false t _ c z hcz)
  rw [hsc'] at hlook
  -- the parent with the klong, as a lookup
  have hQw := KNode.add_key_wf qn t k1 Y hw
  have hQt := KNode.add_times qn t (.key k1 Y) (fun s h => by cases h) hqt
  have hQlook : ∀ c, (qn.add t (.key k1 Y)).live.lookup c =
      [(k1, Y)].foldl (pairLookupStep c) (qn.live.lookup c) := by
    intro c
    rw [KNode.add_key_live_lookup_of_wf qn t k1 c Y hw]
    simp [pairLookupStep]
  have hmemQ : ∀ a z, (a, z) ∈ (qn.add t (.key k1 Y)).live ↔
      (qn.add t (.key k1 Y)).live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem1 : ∀ a z, (a, z) ∈ out.1.live ↔ out.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem2 : ∀ a z, (a, z) ∈ out.2.1.live ↔ out.2.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  -- below r.1 the first half and the parent agree
  have hlow : ∀ a z, a < r.1 → ((a, z) ∈ out.1.live ↔ (a, z) ∈ (qn.add t (.key k1 Y)).live) := by
    intro a z ha
    rw [hmem1, hmemQ, hQlook, ← hlook a]
    simp [ha]
  -- from r.1 on the second half and the parent agree, r.1 named the empty key
  have hspl : ∀ a, r.1 ≤ a → splitLocalCv false r.1 a = if a = r.1 then 0 else a := by
    intro a _
    simp only [splitLocalCv, Bool.not_false, Bool.true_and]
    by_cases h : a = r.1
    · simp [h]
    · have h' : (a == r.1) = false := by simpa using h
      simp [h', h]
  have hhigh : ∀ a z, r.1 < a → ((a, z) ∈ out.2.1.live ↔ (a, z) ∈ (qn.add t (.key k1 Y)).live) := by
    intro a z ha
    rw [hmem2, hmemQ, hQlook, ← hlook a, hspl a (by omega)]
    simp [show ¬ a < r.1 by omega, show a ≠ r.1 by omega]
  have hzero : ∀ z, (0, z) ∈ out.2.1.live ↔ (r.1, z) ∈ (qn.add t (.key k1 Y)).live := by
    intro z
    rw [hmem2, hmemQ, hQlook, ← hlook r.1, hspl r.1 (Nat.le_refl _)]
    simp
  have hsQ := (qn.add t (.key k1 Y)).searchLte_spec t
  refine ⟨hsc', hl1, hl2, hw1, hw2, ht1, ht2, ?_, ?_⟩
  · intro c hc
    have hs := hsQ c
    unfold NodeSearchSpec at hs
    rw [KNode.liveAt_of_times _ t hQt] at hs
    cases hq : (qn.add t (.key k1 Y)).searchLte t c with
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
    obtain ⟨zr, hzr⟩ : ∃ z, (r.1, z) ∈ (qn.add t (.key k1 Y)).live := by
      have hrm : r ∈ qn.live := by
        have : r ∈ qn.live.drop (qn.live.length / 2) := by
          cases he : qn.live.drop (qn.live.length / 2) with
          | nil => rw [he] at hr; cases hr
          | cons a rest =>
            rw [he] at hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; simp
        exact List.mem_of_mem_drop this
      have hl := lookup_some_of_mem (KNode.live_keys_nodup qn) hrm
      by_cases hk : k1 = r.1
      · exact ⟨Y, by rw [hmemQ, KNode.add_key_live_lookup_of_wf qn t k1 r.1 Y hw]; simp [hk]⟩
      · refine ⟨r.2, ?_⟩
        rw [hmemQ, KNode.add_key_live_lookup_of_wf qn t k1 r.1 Y hw]
        have hk' : (k1 == r.1) = false := by simpa using hk
        simp only [hk', Bool.false_eq_true, ↓reduceIte]; exact hl
    cases hq : (qn.add t (.key k1 Y)).searchLte t c with
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
