/-
Cascades of time and space splits of any depth keep the writer's tree
(bergdb 024-22, `OpTreeOK`): the halves' live klongs as the node's with the
klongs put, cut at the divider (`halves_links`), the tree after a space split
in general (`treeOK_spaceSplit_gen`).
-/
import SIS.Tree.WriterTreeCascadeGen

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The live klongs of a node with key klongs put one after the other. -/
theorem KNode.addKeys_live_lookup (t : Time) : ∀ (ins : List (Nat × NodeId)) (n : KNode),
    klongsWf n.ks = true → ∀ c,
    (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).live.lookup c =
      ins.foldl (pairLookupStep c) (n.live.lookup c) := by
  intro ins
  induction ins with
  | nil => intro n _ c; rfl
  | cons a more ih =>
    intro n hw c
    simp only [List.foldl_cons]
    rw [ih _ (KNode.add_key_wf n t a.1 a.2 hw) c, KNode.add_key_live_lookup_of_wf n t a.1 c a.2 hw]
    simp only [pairLookupStep]

theorem KNode.addKeys_times (t : Time) : ∀ (ins : List (Nat × NodeId)) (n : KNode),
    (∀ s, Klong.time s ∈ n.ks → s ≤ t) →
    ∀ s, Klong.time s ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).ks → s ≤ t := by
  intro ins
  induction ins with
  | nil => intro n h; exact h
  | cons a more ih =>
    intro n h
    simp only [List.foldl_cons]
    exact ih _ (KNode.add_times n t _ (fun s h => by cases h) h)

theorem KNode.addKeys_wf (t : Time) : ∀ (ins : List (Nat × NodeId)) (n : KNode),
    klongsWf n.ks = true → klongsWf (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).ks = true := by
  intro ins
  induction ins with
  | nil => intro n h; exact h
  | cons a more ih =>
    intro n h
    simp only [List.foldl_cons]
    exact ih _ (KNode.add_key_wf n t a.1 a.2 h)

/-- The halves of a node's last version with klongs `a :: more` put on one
side of the divider: every live klong of the first is below the divider and
the node's with the klongs put; every one of the second is such a klong at
or above it, under its local name. -/
theorem halves_links (leaf : Bool) (t : Time) (n : KNode) (hl : n.leaf = leaf)
    (a : Nat × NodeId) (more : List (Nat × NodeId))
    (r : Nat × NodeId) (hr : (n.live.drop (n.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hside : ∀ q ∈ a :: more, (r.1 ≤ q.1 ↔ r.1 ≤ a.1)) :
    let out := halves leaf t (n.lastVersion t) (a :: more)
    out.2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ out.1.liveAt t → c < r.1 ∧
      (a :: more).foldl (pairLookupStep c) (n.live.lookup c) = some z) ∧
    (∀ c z, (c, z) ∈ out.2.1.liveAt t → ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv leaf r.1 c0 ∧
      (a :: more).foldl (pairLookupStep c0) (n.live.lookup c0) = some z) := by
  intro out
  have hlv : n.lastVersion t = ⟨leaf, newKlongs t n.live⟩ := by
    rw [KNode.lastVersion_eq_newKlongs, hl]
  have hout : out = halves leaf t ⟨leaf, newKlongs t n.live⟩ (a :: more) := by
    show halves leaf t (n.lastVersion t) (a :: more) = _
    rw [hlv]
  have hside' : ∀ q ∈ a :: more, decide (r.1 ≤ q.1) =
      (match (a :: more).head? with | some a => decide (r.1 ≤ a.1) | none => false) := by
    intro q hq
    simp only [List.head?_cons]
    exact decide_eq_decide.mpr (hside q hq)
  have hmap := halves_lookup leaf t n.live (a :: more) n.live_order r hr hsc hside'
  have hshape := halves_shape leaf t n.live (a :: more) r hr
  simp only [List.head?_cons] at hshape
  have hleft := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  have hright := halves_right_ge_divider n.live (n.live.length / 2) n.live_order r hr
  have hsec := secondSplitPairs_eq_map leaf n.live n.live_order r hr
  have key : ∀ P1 P2 : List (Nat × NodeId),
      out = (⟨leaf, newKlongs t P1⟩, ⟨leaf, newKlongs t P2⟩, r.1) → (∀ q ∈ P1, q.1 < r.1) →
      (∀ q ∈ P2, ∃ c0, r.1 ≤ c0 ∧ q.1 = splitLocalCv leaf r.1 c0) →
      out.2.2 = r.1 ∧
      (∀ c z, (c, z) ∈ out.1.liveAt t → c < r.1 ∧
        (a :: more).foldl (pairLookupStep c) (n.live.lookup c) = some z) ∧
      (∀ c z, (c, z) ∈ out.2.1.liveAt t → ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv leaf r.1 c0 ∧
        (a :: more).foldl (pairLookupStep c0) (n.live.lookup c0) = some z) := by
    intro P1 P2 hP hP1 hP2
    have hdiv : out.2.2 = r.1 := by rw [hP]
    have ht1 : ∀ s, Klong.time s ∈ out.1.ks → s ≤ t := by rw [hP]; exact newKlongs_times t _
    have ht2 : ∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t := by rw [hP]; exact newKlongs_times t _
    refine ⟨hdiv, ?_, ?_⟩
    · intro c z h
      have hc : c < r.1 := by
        rw [hP] at h
        exact hP1 (c, z) (liveAt_newKlongs_mem leaf t t _ c z h)
      refine ⟨hc, ?_⟩
      have hlk : out.1.live.lookup c = some z := by
        rw [KNode.liveAt_of_times _ t ht1] at h
        exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
      have := hmap c
      simp only [] at this
      rw [← hout, hdiv] at this
      simp only [hc, ↓reduceIte] at this
      rw [← this, hlk]
    · intro c z h
      obtain ⟨c0, hc0, hcc⟩ : ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv leaf r.1 c0 := by
        have h' := h
        rw [hP] at h'
        exact hP2 (c, z) (liveAt_newKlongs_mem leaf t t _ c z h')
      refine ⟨c0, hc0, hcc, ?_⟩
      have hlk : out.2.1.live.lookup c = some z := by
        rw [KNode.liveAt_of_times _ t ht2] at h
        exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
      have := hmap c0
      simp only [] at this
      rw [← hout, hdiv] at this
      have hn : ¬ c0 < r.1 := by omega
      simp only [hn, ↓reduceIte] at this
      rw [← this, ← hcc, hlk]
  by_cases hto : r.1 ≤ a.1
  · have hd : decide (r.1 ≤ a.1) = true := decide_eq_true hto
    simp only [hd, ↓reduceIte] at hshape
    apply key _ _ (hout.trans hshape)
    · exact hleft
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · rw [hsec] at hq
        obtain ⟨q0, hq0, he⟩ := List.mem_map.mp hq
        exact ⟨q0.1, hright q0 hq0, by rw [← he]⟩
      · obtain ⟨q0, hq0, he⟩ := List.mem_map.mp hq
        exact ⟨q0.1, (hside q0 hq0).mpr hto, by rw [← he]⟩
  · have hd : decide (r.1 ≤ a.1) = false := decide_eq_false hto
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hshape
    apply key _ _ (hout.trans hshape)
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hleft q hq
      · have := (hside q hq)
        have : ¬ r.1 ≤ q.1 := fun hh => hto (this.mp hh)
        omega
    · intro q hq
      rw [hsec] at hq
      obtain ⟨q0, hq0, he⟩ := List.mem_map.mp hq
      exact ⟨q0.1, hright q0 hq0, by rw [← he]⟩

/-- The space split of L below q into new nodes y1 and y2, in general: y1 has
live klongs of L below sc, y2 those at or above it under local names; q's new
node names y1 by k1 and y2 by sc, else q's live klongs. The tree is kept; it
reaches the nodes reached before and y1, y2, not L. -/
theorem treeOK_spaceSplit_gen (N N' : NodeId → Option KNode) (t : Time) (r q L y1 y2 : NodeId)
    (qn n f s qn' : KNode) (k1 sc : Nat) (loc : Nat → Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hLn : N L = some n)
    (hN'q : N' q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = sc ∧ z = y2) ∨ (c ≠ sc ∧ c = k1 ∧ z = y1) ∨
      (c ≠ sc ∧ c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN'1 : N' y1 = some f) (hN'2 : N' y2 = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ n.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ n.liveAt t)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y1 → z ≠ y2 → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (h12 : y1 ≠ y2)
    (hfresh : ∀ z, (z = y1 ∨ z = y2) → ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r ∧ ∀ z, TReach N' t r z → (TReach N t r z ∨ z = y1 ∨ z = y2) ∧ z ≠ L := by
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hL1 : L ≠ y1 := fun h => by rw [h, hf1] at hLn; cases hLn
  have hL2 : L ≠ y2 := fun h => by rw [h, hf2] at hLn; cases hLn
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hql : ∀ c' z, TLink N' t q c' z → (c' = sc ∧ z = y2) ∨ (c' ≠ sc ∧ c' = k1 ∧ z = y1) ∨
      (c' ≠ sc ∧ c' ≠ k1 ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'q] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hq' c' z hc
  have h1l : ∀ c' z, TLink N' t y1 c' z → TLink N t L c' z ∧ c' < sc := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'1] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨⟨n, hLn, (hf c' z hc).2⟩, (hf c' z hc).1⟩
  have h2l : ∀ c' z, TLink N' t y2 c' z → ∃ c0, sc ≤ c0 ∧ c' = loc c0 ∧ TLink N t L c0 z := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'2] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    obtain ⟨c0, h1, h2, h3⟩ := hs c' z hc
    exact ⟨c0, h1, h2, ⟨n, hLn, h3⟩⟩
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ y1 → u ≠ y2 → ∀ c' z, TLink N' t u c' z →
      TLink N t u c' z := by
    intro u h1 h2 h3 h4 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2 h3 h4] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, (z = y1 ∨ z = y2) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h <;> rw [h]
    · exact not_reach_fresh N t r y1 hT hf1 (hfresh y1 (Or.inl rfl))
    · exact not_reach_fresh N t r y2 hT hf2 (hfresh y2 (Or.inr rfl))
  have hr' : (r = r ∧ ¬ (fun z => z = L) r) ∨ ((fun z => z = y1 ∨ z = y2) r ∧ ∀ y' c,
      (TReach N t r y' ∨ (fun z => z = y1 ∨ z = y2) y') → ¬ (fun z => z = L) y' →
      ¬ TLink N' t y' c r) :=
    Or.inl ⟨rfl, fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)⟩
  have hnotL : ∀ y0 c0 z, TReach N t r y0 → TLink N t y0 c0 z → (y0 ≠ q ∨ c0 ≠ k1) →
      ¬ (fun z => z = L) z := by
    intro y0 c0 z hy0 hl0 hne hz
    have hz' : z = L := hz
    rw [hz'] at hl0
    obtain ⟨a, b⟩ := hLpar y0 c0 hy0 hl0
    rcases hne with h | h
    · exact h a
    · exact h b
  have hlinks : ∀ u c' z, (TReach N t r u ∨ (fun z => z = y1 ∨ z = y2) u) →
      ¬ (fun z => z = L) u → TLink N' t u c' z →
      (fun z => z = y1 ∨ z = y2) z ∨ (¬ (fun z => z = L) z ∧ ∃ y0 c0, TReach N t r y0 ∧
        TLink N t y0 c0 z ∧ (fun u c' => if u = L then (if c' < sc then (y1, c') else (y2, loc c'))
          else (u, c')) y0 c0 = (u, c')) := by
    intro u c' z hu hug hl
    have huL : u ≠ L := hug
    by_cases hu1 : u = y1
    · rw [hu1] at hl
      obtain ⟨hl0, hlt⟩ := h1l c' z hl
      exact Or.inr ⟨hnotL L c' z hL hl0 (Or.inl (Ne.symm hqL)), L, c', hL, hl0, by simp [hu1, hlt]⟩
    · by_cases hu2 : u = y2
      · rw [hu2] at hl
        obtain ⟨c0, hge, hcc, hl0⟩ := h2l c' z hl
        have hnlt : ¬ c0 < sc := by omega
        exact Or.inr ⟨hnotL L c0 z hL hl0 (Or.inl (Ne.symm hqL)), L, c0, hL, hl0,
          by simp [hu2, hnlt, hcc]⟩
      · have huR : TReach N t r u := by
          rcases hu with h | h
          · exact h
          · rcases h with h | h
            · exact absurd h hu1
            · exact absurd h hu2
        by_cases huq : u = q
        · rw [huq] at hl
          rcases hql c' z hl with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, hc, hm⟩
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · have hl0 : TLink N t q c' z := ⟨qn, hqn, hm⟩
            exact Or.inr ⟨hnotL q c' z hq hl0 (Or.inr hc), q, c', hq, hl0, by simp [hqL, huq]⟩
        · have hl0 := hOld u huL huq hu1 hu2 c' z hl
          exact Or.inr ⟨hnotL u c' z huR hl0 (Or.inl huq), u, c', huR, hl0, by simp [huL]⟩
  have hNewGone : ∀ z, (fun z => z = y1 ∨ z = y2) z → ¬ (fun z => z = L) z := by
    intro z hz hzg
    have h2 : z = L := hzg
    rcases hz with h | h
    · exact hL1 (h2.symm.trans h)
    · exact hL2 (h2.symm.trans h)
  refine ⟨?_, ?_⟩
  · apply treeOK_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2) (fun z => z = L)
      (fun u c' => if u = L then (if c' < sc then (y1, c') else (y2, loc c')) else (u, c')) hT hnotR
      hr' hlinks
    · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
      have hz' : z = y1 ∨ z = y2 := hz
      have hfr := hfresh z hz'
      have hone : ∀ v d, (TReach N t r v ∨ (v = y1 ∨ v = y2)) → v ≠ L → TLink N' t v d z →
          (v = q ∧ d = sc ∧ z = y2) ∨ (v = q ∧ d = k1 ∧ z = y1) := by
        intro v d hv hvg hl
        by_cases hv1 : v = y1
        · rw [hv1] at hl; exact absurd (h1l d z hl).1 (hfr L d hL)
        · by_cases hv2 : v = y2
          · rw [hv2] at hl
            obtain ⟨c0, _, _, hl0⟩ := h2l d z hl
            exact absurd hl0 (hfr L c0 hL)
          · have hvR : TReach N t r v := by
              rcases hv with h | h
              · exact h
              · rcases h with h | h
                · exact absurd h hv1
                · exact absurd h hv2
            by_cases hvq : v = q
            · rw [hvq] at hl
              rcases hql d z hl with ⟨hd, h⟩ | ⟨_, hd, h⟩ | ⟨_, _, hm⟩
              · exact Or.inl ⟨hvq, hd, h⟩
              · exact Or.inr ⟨hvq, hd, h⟩
              · exact absurd ⟨qn, hqn, hm⟩ (hfr q d hq)
            · exact absurd (hOld v hvg hvq hv1 hv2 d z hl) (hfr v d hvR)
      rcases hone u c' hu hug hl1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
        rcases hone u' c'' hu' hug' hl2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
      · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
      · exact absurd (c2.symm.trans c1) h12
      · exact absurd (c1.symm.trans c2) h12
      · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact hNewGone
    · by_cases hrq : r = q
      · rw [hrq, hN'q]; exact ⟨_, rfl⟩
      · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
        obtain ⟨rm, hrm⟩ := hT.rootKey
        have hr1 : r ≠ y1 := fun h => by rw [h, hf1] at hrm; cases hrm
        have hr2 : r ≠ y2 := fun h => by rw [h, hf2] at hrm; cases hrm
        rw [hother r hrL hrq hr1 hr2]; exact ⟨rm, hrm⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := tReach_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2) (fun z => z = L)
      (fun u c' => if u = L then (if c' < sc then (y1, c') else (y2, loc c')) else (u, c')) hr' hlinks
      hNewGone z hz
    exact ⟨h1, h2⟩

end SIS.Tree
