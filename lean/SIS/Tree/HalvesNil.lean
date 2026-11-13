/-
The halves of a last version with nothing put (bergdb 024-22): a node whose
klongs are a time klong and sorted key klongs is its own last version, and its
halves with no klongs to insert search as it does, below the divider and from it
on (`halves_links`, `halves_read`, `halves_cover` for `ins = []`). For the
merge's full parent, whose last version the merge gives.
-/
import SIS.Tree.GetCascadeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Two lists sorted by compare value with the same lookups are one. -/
theorem sorted_pairs_eq : ∀ (a b : List (Nat × NodeId)), CvSorted a → CvSorted b →
    (∀ c, a.lookup c = b.lookup c) → a = b := by
  intro a
  induction a with
  | nil =>
    intro b _ _ h
    cases b with
    | nil => rfl
    | cons y b' =>
      have := h y.1
      simp [List.lookup] at this
  | cons x a' ih =>
    intro b ha hb h
    cases b with
    | nil =>
      have := h x.1
      simp [List.lookup] at this
    | cons y b' =>
      have hx := h x.1
      have hy := h y.1
      simp only [List.lookup, beq_self_eq_true] at hx hy
      have hxy : x.1 = y.1 := by
        rcases Nat.lt_trichotomy x.1 y.1 with hlt | heq | hlt
        · -- x.1 < y.1: b has no key x.1
          have hb1 : (x.1 == y.1) = false := by simp only [beq_eq_false_iff_ne]; omega
          rw [hb1] at hx
          simp only at hx
          have hm := lookup_some_mem hx.symm
          have := List.rel_of_pairwise_cons hb hm
          simp only at this; omega
        · exact heq
        · have hb1 : (y.1 == x.1) = false := by simp only [beq_eq_false_iff_ne]; omega
          rw [hb1] at hy
          simp only at hy
          have hm := lookup_some_mem hy
          have := List.rel_of_pairwise_cons ha hm
          simp only at this; omega
      have hx2 : x.2 = y.2 := by
        rw [hxy] at hx
        simp only [beq_self_eq_true] at hx
        exact Option.some.inj hx
      have hxe : x = y := Prod.ext hxy hx2
      subst hxe
      congr 1
      apply ih b' (List.Pairwise.of_cons ha) (List.Pairwise.of_cons hb)
      intro c
      by_cases hc : c = x.1
      · subst hc
        have h1 : a'.lookup x.1 = none := by
          cases hl : a'.lookup x.1 with
          | none => rfl
          | some z =>
            have hm := lookup_some_mem hl
            have := List.rel_of_pairwise_cons ha hm
            simp only at this; omega
        have h2 : b'.lookup x.1 = none := by
          cases hl : b'.lookup x.1 with
          | none => rfl
          | some z =>
            have hm := lookup_some_mem hl
            have := List.rel_of_pairwise_cons hb hm
            simp only at this; omega
        rw [h1, h2]
      · have := h c
        have hb1 : (c == x.1) = false := by simpa using hc
        simp only [List.lookup, hb1] at this
        exact this

/-- The live klongs of a node of a time klong and sorted key klongs are its
pairs. -/
theorem KNode.live_newKlongs_sorted (lf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hs : CvSorted pairs) : (⟨lf, newKlongs t pairs⟩ : KNode).live = pairs := by
  have hn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hs.imp (by intro a b hab; omega))
  exact sorted_pairs_eq _ _ (KNode.live_order _) hs
    (fun c => KNode.newKlongs_live_lookup lf t pairs hn c)

/-- Such a node is its own last version. -/
theorem KNode.lastVersion_newKlongs_sorted (lf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hs : CvSorted pairs) :
    (⟨lf, newKlongs t pairs⟩ : KNode).lastVersion t = ⟨lf, newKlongs t pairs⟩ := by
  rw [KNode.lastVersion_eq_newKlongs, KNode.live_newKlongs_sorted lf t pairs hs]

/-- `halves_links` with nothing put. -/
theorem halves_links_nil (leaf : Bool) (t : Time) (n : KNode) (hl : n.leaf = leaf)
    (r : Nat × NodeId) (hr : (n.live.drop (n.live.length / 2)).head? = some r) (hsc : 0 < r.1) :
    let out := halves leaf t (n.lastVersion t) []
    out.2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ out.1.liveAt t → c < r.1 ∧ n.live.lookup c = some z) ∧
    (∀ c z, (c, z) ∈ out.2.1.liveAt t → ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv leaf r.1 c0 ∧
      n.live.lookup c0 = some z) := by
  intro out
  have hlv : n.lastVersion t = ⟨leaf, newKlongs t n.live⟩ := by
    rw [KNode.lastVersion_eq_newKlongs, hl]
  have hout : out = halves leaf t ⟨leaf, newKlongs t n.live⟩ [] := by
    show halves leaf t (n.lastVersion t) [] = _
    rw [hlv]
  have hside' : ∀ q ∈ ([] : List (Nat × NodeId)), decide (r.1 ≤ q.1) =
      (match ([] : List (Nat × NodeId)).head? with | some a => decide (r.1 ≤ a.1) | none => false) := by
    intro q hq; cases hq
  have hmap := halves_lookup leaf t n.live [] n.live_order r hr hsc hside'
  have hshape := halves_shape leaf t n.live [] r hr
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hshape
  have hleft := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  have hright := halves_right_ge_divider n.live (n.live.length / 2) n.live_order r hr
  have hsec := secondSplitPairs_eq_map leaf n.live n.live_order r hr
  have hP := hout.trans hshape
  have hdiv : out.2.2 = r.1 := by rw [hP]
  have ht1 : ∀ s, Klong.time s ∈ out.1.ks → s ≤ t := by rw [hP]; exact newKlongs_times t _
  have ht2 : ∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t := by rw [hP]; exact newKlongs_times t _
  refine ⟨hdiv, ?_, ?_⟩
  · intro c z h
    have hc : c < r.1 := by
      have h' := h
      rw [hP] at h'
      exact hleft (c, z) (liveAt_newKlongs_mem leaf t t _ c z h')
    refine ⟨hc, ?_⟩
    have hlk : out.1.live.lookup c = some z := by
      rw [KNode.liveAt_of_times _ t ht1] at h
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
    have := hmap c
    simp only [] at this
    rw [← hout, hdiv] at this
    simp only [hc, ↓reduceIte, List.foldl_nil] at this
    rw [← this, hlk]
  · intro c z h
    obtain ⟨c0, hc0, hcc⟩ : ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv leaf r.1 c0 := by
      have h' := h
      rw [hP] at h'
      have hm := liveAt_newKlongs_mem leaf t t _ c z h'
      rw [hsec] at hm
      obtain ⟨q0, hq0, he⟩ := List.mem_map.mp hm
      exact ⟨q0.1, hright q0 hq0, (congrArg Prod.fst he).symm⟩
    refine ⟨c0, hc0, hcc, ?_⟩
    have hlk : out.2.1.live.lookup c = some z := by
      rw [KNode.liveAt_of_times _ t ht2] at h
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
    have := hmap c0
    simp only [] at this
    rw [← hout, hdiv] at this
    have hn : ¬ c0 < r.1 := by omega
    simp only [hn, ↓reduceIte, List.foldl_nil] at this
    rw [← this, ← hcc, hlk]

/-- `halves_read` with nothing put: the halves search as the node, below the
divider and from it on. -/
theorem halves_read_nil (t : Time) (n : KNode)
    (h2 : 2 ≤ n.live.length) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hnwf : klongsWf n.ks = true) :
    (halves n.leaf t (n.lastVersion t) []).1.leaf = n.leaf ∧
    (halves n.leaf t (n.lastVersion t) []).2.1.leaf = n.leaf ∧
    (n.leaf = true → ∀ c : Nat, c < (halves n.leaf t (n.lastVersion t) []).2.2 →
      ((halves n.leaf t (n.lastVersion t) []).1.searchEq t c).map (·.y) = (n.searchEq t c).map (·.y)) ∧
    (n.leaf = true → ∀ c : Nat, (halves n.leaf t (n.lastVersion t) []).2.2 ≤ c →
      ((halves n.leaf t (n.lastVersion t) []).2.1.searchEq t c).map (·.y) = (n.searchEq t c).map (·.y)) ∧
    (n.leaf = false → ∀ c : Nat, c < (halves n.leaf t (n.lastVersion t) []).2.2 →
      ((halves n.leaf t (n.lastVersion t) []).1.searchLte t c).map (·.y) = (n.searchLte t c).map (·.y)) ∧
    (n.leaf = false → ∀ c : Nat, (halves n.leaf t (n.lastVersion t) []).2.2 ≤ c →
      ((halves n.leaf t (n.lastVersion t) []).2.1.searchLte t c).map (·.y) =
        (n.searchLte t c).map (·.y)) := by
  obtain ⟨r, hr⟩ := divider_exists n (by omega)
  have hsc := divider_pos' n r h2 hr
  have hside' : (∀ q ∈ ([] : List (Nat × NodeId)), r.1 ≤ q.1) ∨ (∀ q ∈ ([] : List (Nat × NodeId)), q.1 < r.1) :=
    Or.inl (fun q hq => by cases hq)
  cases hxl : n.leaf with
  | true =>
    have hL := halves_leaf_searchEq_ins n n t [] hxl r hr hside' hnwf hnt (fun c => rfl)
    simp only at hL
    rw [hxl] at hL
    obtain ⟨hdiv, h1, h2, _, _, _, _, h3, h4⟩ := hL
    rw [hdiv]
    refine ⟨h1, h2, fun _ => h3, fun _ => h4, ?_, ?_⟩
    · intro h; cases h
    · intro h; cases h
  | false =>
    have hL := halves_inner_searchLte_ins n n t [] hxl r hr hsc hside' hnt (fun c => rfl)
    simp only at hL
    rw [hxl] at hL
    obtain ⟨hdiv, h1, h2, _, _, _, _, h3, h4⟩ := hL
    rw [hdiv]
    refine ⟨h1, h2, ?_, ?_, fun _ => h3, fun _ => h4⟩
    · intro h; cases h
    · intro h; cases h

/-- `halves_cover` with nothing put. -/
theorem halves_cover_nil (t : Time) (n : KNode)
    (h2 : 2 ≤ n.live.length) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hnwf : klongsWf n.ks = true)
    (c : Nat) (z : NodeId) (hc : (c, z) ∈ n.liveAt t) :
    (c < (halves n.leaf t (n.lastVersion t) []).2.2 →
      ∃ c', (c', z) ∈ (halves n.leaf t (n.lastVersion t) []).1.liveAt t) ∧
    ((halves n.leaf t (n.lastVersion t) []).2.2 ≤ c →
      ∃ c', (c', z) ∈ (halves n.leaf t (n.lastVersion t) []).2.1.liveAt t) := by
  have hh := halves_read_nil t n h2 hnt hnwf
  have hwh := halves_newKlongs_wf n.leaf t n.live []
  rw [← KNode.lastVersion_eq_newKlongs] at hwh
  have hlk : n.live.lookup c = some z := by
    rw [KNode.liveAt_of_times _ t hnt] at hc
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hc
  by_cases hl : n.leaf = true
  · have hxe := KNode.searchEq_live _ t hnwf hnt c
    rw [hlk] at hxe
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have he := hh.2.2.1 hl c hlt
      rw [hxe] at he
      cases hF : (halves n.leaf t (n.lastVersion t) []).1.searchEq t c with
      | none => rw [hF] at he; cases he
      | some fd =>
        rw [hF] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨c, he ▸ KNode.searchEq_mem _ t c fd hwh.1 hF⟩
    · have he := hh.2.2.2.1 hl c hge
      rw [hxe] at he
      cases hS : (halves n.leaf t (n.lastVersion t) []).2.1.searchEq t c with
      | none => rw [hS] at he; cases he
      | some fd =>
        rw [hS] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨c, he ▸ KNode.searchEq_mem _ t c fd hwh.2 hS⟩
  · have hl : n.leaf = false := by simpa using hl
    have hxe := KNode.searchLte_of_live _ t hnt c z hc
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have he := hh.2.2.2.2.1 hl c hlt
      rw [hxe] at he
      cases hF : (halves n.leaf t (n.lastVersion t) []).1.searchLte t c with
      | none => rw [hF] at he; cases he
      | some fd =>
        rw [hF] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨fd.c, he ▸ KNode.searchLte_mem _ t c fd hF⟩
    · have he := hh.2.2.2.2.2 hl c hge
      rw [hxe] at he
      cases hS : (halves n.leaf t (n.lastVersion t) []).2.1.searchLte t c with
      | none => rw [hS] at he; cases he
      | some fd =>
        rw [hS] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨fd.c, he ▸ KNode.searchLte_mem _ t c fd hS⟩

/-- The key klongs of the first half of a last version with nothing put are the
last version's. -/
theorem halves_nil_first_keys (leaf : Bool) (t : Time) (last : KNode) (cv : Nat) (y : NodeId)
    (h : Klong.key cv y ∈ (halves leaf t last []).1.ks) : Klong.key cv y ∈ last.ks := by
  simp only [halves, List.head?_nil, List.map_nil, List.append_nil, Bool.false_eq_true,
    ↓reduceIte, List.mem_cons, reduceCtorEq, false_or] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

end SIS.Tree
