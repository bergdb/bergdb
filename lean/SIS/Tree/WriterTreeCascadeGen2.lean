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

/-- `appendKlongs` into a node with room for the klongs and no compaction:
the node with the klongs put. -/
theorem writerWP_appendKlongs_addKeys (d : Nat) (q : NodeId) (qn : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hlk : w.nodes.lookup q = some qn) (hroom : qn.size + ins.length + 1 ≤ c.p.M)
    (hdead : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false) :
    WriterWP (appendKlongs d q ins) c w (fun _ w' =>
      w' = { w with nodes := upsert w.nodes q (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn) }) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  have h1 : ¬ (qn.size + ins.length + 1 > c.p.M) := by omega
  simp only [h1, ↓reduceIte, hdead, Bool.false_eq_true]
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  simp only [putNode, writerWP_modify]

theorem wNode_two_updN (p : Params) (base : View BVal) (w w' : W) (y1 y2 : NodeId) (m1 m2 : KNode)
    (hn : ∀ z, w'.nodes.lookup z = if z = y1 then some m1 else if z = y2 then some m2
      else w.nodes.lookup z) (ht : w'.taken = w.taken) (h12 : y1 ≠ y2)
    (ht1 : w.taken.contains y1 = false) (ht2 : w.taken.contains y2 = false) :
    wNode p base w' = updN (updN (wNode p base w) y1 m1) y2 m2 := by
  funext z
  unfold wNode updN
  rw [ht, hn z]
  by_cases h2 : z = y2
  · subst h2
    have h1 : ¬ z = y1 := fun h => h12 h.symm
    simp only [ht2, h1, Bool.false_eq_true, ↓reduceIte]
  · simp only [h2, ↓reduceIte]
    by_cases h1 : z = y1
    · subst h1; simp only [ht1, Bool.false_eq_true, ↓reduceIte]
    · simp only [h1, ↓reduceIte]

/-- The divider of a node with at least two live klongs is above 0. -/
theorem divider_pos' (n : KNode) (r : Nat × NodeId) (h2 : 2 ≤ n.live.length)
    (hr : (n.live.drop (n.live.length / 2)).head? = some r) : 0 < r.1 := by
  have hleft := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  obtain ⟨a, ha⟩ : ∃ a, a ∈ n.live.take (n.live.length / 2) := by
    cases h : n.live.take (n.live.length / 2) with
    | nil =>
      exfalso
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this
      omega
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  have := hleft a ha
  omega

theorem divider_mem_live (n : KNode) (r : Nat × NodeId)
    (hr : (n.live.drop (n.live.length / 2)).head? = some r) : r ∈ n.live :=
  List.mem_of_mem_drop (List.mem_of_mem_head? hr)

theorem divider_exists (n : KNode) (h1 : 1 ≤ n.live.length) :
    ∃ r, (n.live.drop (n.live.length / 2)).head? = some r := by
  cases hd : (n.live.drop (n.live.length / 2)).head? with
  | some r => exact ⟨r, rfl⟩
  | none =>
    exfalso
    rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
    omega

/-- Links of a node with klongs put, from the fold of their lookups. -/
theorem KNode.addKeys_liveAt_of_fold (t : Time) (ins : List (Nat × NodeId)) (n : KNode)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (h : ins.foldl (pairLookupStep c) (n.live.lookup c) = some z) :
    (c, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.addKeys_times t ins n ht)]
  apply mem_of_lookup_nodup
  rw [KNode.addKeys_live_lookup t ins n hw c, h]

theorem KNode.addKeys_liveAt_fold (t : Time) (ins : List (Nat × NodeId)) (n : KNode)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (h : (c, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t) :
    ins.foldl (pairLookupStep c) (n.live.lookup c) = some z := by
  rw [KNode.liveAt_of_times _ t (KNode.addKeys_times t ins n ht)] at h
  rw [← KNode.addKeys_live_lookup t ins n hw c]
  exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h

/-- The klongs that `appendKlongs` puts into a node of a cascade: one, or two
(a space split below) whose second compare value is at least the first and
below every live compare value of the node above the first. -/
def InsOK (n : KNode) (ins : List (Nat × NodeId)) : Prop :=
  (∃ k y, ins = [(k, y)]) ∨
  (∃ k F sc S, ins = [(k, F), (sc, S)] ∧ k ≤ sc ∧ ∀ c'' z'', (c'', z'') ∈ n.live → k < c'' → sc < c'')

theorem InsOK.length {n : KNode} {ins : List (Nat × NodeId)} (h : InsOK n ins) : ins.length ≤ 2 := by
  rcases h with ⟨k, y, rfl⟩ | ⟨k, F, sc, S, rfl, _, _⟩ <;> simp

theorem InsOK.side {n : KNode} {ins : List (Nat × NodeId)} (h : InsOK n ins) (r : Nat × NodeId)
    (hr : r ∈ n.live) : ∃ a more, ins = a :: more ∧ ∀ q ∈ a :: more, (r.1 ≤ q.1 ↔ r.1 ≤ a.1) := by
  rcases h with ⟨k, y, rfl⟩ | ⟨k, F, sc, S, rfl, hks, hup⟩
  · refine ⟨(k, y), [], rfl, ?_⟩
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
  · refine ⟨(k, F), [(sc, S)], rfl, ?_⟩
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq
    · rw [hq]
    · rw [hq]
      constructor
      · intro h1
        rcases Nat.lt_or_ge k r.1 with h2 | h2
        · have := hup r.1 r.2 hr h2; simp only at this h1; omega
        · exact h2
      · intro h1; simp only at h1 ⊢; omega

/-- A cascade of time and space splits of any depth (bergdb 024-22,
`OpTreeOK`): as `writerWP_appendKlongs_timeChain`, with space splits too. The
access path's nodes X s (with room for two klongs) to X D, each below the one
before by klong K i, inner but X D, existed before the transaction, their
compare values in the range their parent's klongs give (`hrange`, putinv's
`RangeOrder`), two or more live klongs in a node that space splits. From a
state whose tree with the klongs ins put in X j is a tree,
`appendKlongs j (X j) ins` keeps the writer's tree. -/
theorem writerWP_appendKlongs_chain (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hinner : ∀ i, s < i → i ≤ D → (Nn (i - 1)).leaf = false)
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hnew : ∀ i, s < i → i ≤ D → (Nn i).firstTime ≠ some c.i)
    (hrange : ∀ i, s < i → i ≤ D → ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s < i → i ≤ D → c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : (Nn s).size + 2 + 1 ≤ c.p.M ∧ ∀ ins : List (Nat × NodeId), ins.length ≤ 2 →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn s)) = false)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i') :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i
            w.top.rootKey z ∨ w.next ≤ z)) := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      w.nodes.lookup (X (s + e)) = some (Nn (s + e)) → w.taken.contains (X (s + e)) = false →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i
            w.top.rootKey z ∨ w.next ≤ z)) := by
    intro e _ w ins hlk htk hroom hdead hV
    refine writerWP_mono (writerWP_appendKlongs_addKeys (s + e) (X (s + e)) (Nn (s + e)) ins c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    have hN := wNode_upsert_updN c.p base w { w with nodes := upsert w.nodes (X (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) } (X (s + e)) _ rfl rfl htk
    refine ⟨?_, ⟨rfl, rfl, rfl, Nat.le_refl _, rfl⟩, ?_, ?_⟩
    · rw [hN]; exact hV
    · intro z _ hz
      show (upsert w.nodes _ _).lookup z = _
      rw [lookup_upsert, ite_eq_right_of_eq_false _ _
        (eq_false (hz (s + e) (Nat.le_add_right _ _) (Nat.le_refl _)))]
    · intro z hz
      rw [hN] at hz
      exact Or.inl hz
  intro e
  induction e with
  | zero =>
    intro hD w ins hins _ _ hS2 _ _ _ _ hV
    obtain ⟨hlk, htk⟩ := hS2 s (Nat.le_refl _) (by omega)
    have hl := hins.length
    exact hroomCase 0 hD w ins hlk htk (by have := htop.1; simp only [Nat.add_zero]; omega)
      (by simpa using htop.2 ins hl) hV
  | succ e ih =>
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hV
    have hj : s < s + (e + 1) := by omega
    obtain ⟨hlk, htk⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, htq⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) = false
    · exact hroomCase (e + 1) hD w ins hlk htk hroom.1 hroom.2 hV
    · -- common facts of a split
      have hql : (Nn (s + e)).leaf = false := by
        have := hinner (s + (e + 1)) hj hD; simpa using this
      have hfirst := hnew (s + (e + 1)) hj hD
      have hpq : (w.path[s + e]?).map (·.2) = some (X (s + e)) := by
        rw [hS1]; exact hX (s + e) (by omega) (by omega)
      have hpk : w.path[s + e + 1]? = some (some (K (s + (e + 1))), X (s + (e + 1))) := by
        rw [hS1]; exact hK (s + (e + 1)) hj hD
      have hkl : (K (s + (e + 1)), X (s + (e + 1))) ∈ (Nn (s + e)).liveAt c.i := by
        have := hlinkK (s + (e + 1)) hj hD; simpa using this
      obtain ⟨hfree0, htk0, hbase0⟩ := hS5 w.next (Nat.le_refl _)
      obtain ⟨hfree2, htk2', hbase2⟩ := hS5 (w.next + 2) (by omega)
      have hwnext : wNode c.p base w w.next = none := by
        simp only [wNode, htk0, Bool.false_eq_true, ↓reduceIte, hfree0, hbase0]
      have hwnext2 : wNode c.p base w (w.next + 2) = none := by
        simp only [wNode, htk2', Bool.false_eq_true, ↓reduceIte, hfree2, hbase2]
      have hnoLink : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
        intro z hz u c' hl; have := hS6 u c' z hl; omega
      have hyR : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z := by
        intro z hz
        have hwz : wNode c.p base w z = none := by
          obtain ⟨a, b, d⟩ := hS5 z hz
          simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
        exact not_reach_fresh _ c.i _ z hS3 hwz (fun u c' _ => hnoLink z hz u c')
      have hXlt : ∀ i, s ≤ i → i ≤ s + (e + 1) → X i < w.next := by
        intro i h1 h2
        obtain ⟨hl, _⟩ := hS2 i h1 h2
        rcases Nat.lt_or_ge (X i) w.next with hlt | hge
        · exact hlt
        · have := (hS5 (X i) hge).1
          rw [hl] at this; cases this
      have hqx : X (s + e) ≠ X (s + (e + 1)) := by
        intro h; have := hdist _ _ (by omega) (by omega) (by omega) hD h; omega
      have hwq : wNode c.p base w (X (s + e)) = some (Nn (s + e)) := by
        simp only [wNode, htq, Bool.false_eq_true, ↓reduceIte, hlq]
      have hwx : wNode c.p base w (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
        simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
      have hqR : TReach (updN (wNode c.p base w) (X (s + (e + 1)))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey
          (X (s + e)) :=
        tReach_updN_parent _ c.i _ _ _ _ _ hS3 (hS4 (s + e) (by omega) (by omega))
          ⟨Nn (s + e), hwq, hkl⟩
      have hqtimes := htimes (s + e) (by omega) (by omega)
      have hqwf := hwf (s + e) (by omega) (by omega)
      have hxtimes := htimes (s + (e + 1)) (by omega) hD
      have hxwf := hwf (s + (e + 1)) (by omega) hD
      -- the links of the node with the klongs put are below the next id
      have hvxLinks : ∀ c' z, (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn (s + (e + 1)))).liveAt c.i → z < w.next := by
        intro c' z h
        have hf := KNode.addKeys_liveAt_fold c.i ins _ hxwf hxtimes c' z h
        rcases pairLookupFold_some_mem c' ins _ z hf with hm | hm
        · exact hinsT (c', z) hm
        · have hm' := lookup_some_mem hm
          rw [← KNode.liveAt_of_times _ c.i hxtimes] at hm'
          exact hS6 _ _ _ ⟨_, hwx, hm'⟩
      have hVfresh : ∀ z, w.next ≤ z → ∀ u c', TReach (updN (wNode c.p base w) (X (s + (e + 1)))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey u →
          ¬ TLink (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i u c' z := by
        intro z hz u c' _ hl
        obtain ⟨m, hm, hc⟩ := hl
        by_cases hu : u = X (s + (e + 1))
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hvxLinks c' z hc; omega
        · rw [updN_ne _ _ _ _ hu] at hm
          exact hnoLink z hz u c' ⟨m, hm, hc⟩
      -- the rest of a split: the parent's step by the induction, then the node left behind
      have hfinish : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (N1 : NodeId → Option KNode)
          (New : NodeId → Prop),
          InsOK (Nn (s + e)) ins' → (∀ q ∈ ins', q.2 < w1.next) →
          w1.path = w.path → w1.taken = w.taken → w1.top = w.top → w.next + 2 ≤ w1.next →
          w1.vals = w.vals → (∀ z, New z → w.next ≤ z) →
          (∀ z, z < w.next → w1.nodes.lookup z = w.nodes.lookup z) →
          wNode c.p base w1 = N1 →
          TreeOK N1 c.i w.top.rootKey →
          (∀ i, s ≤ i → i ≤ s + e → TReach N1 c.i w.top.rootKey (X i)) →
          (∀ z, w1.next ≤ z → w1.nodes.lookup z = none ∧ w1.taken.contains z = false ∧
            knodeOf c.p base z = none) →
          (∀ u c' z, TLink N1 c.i u c' z → z < w1.next) →
          TreeOK (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) c.i w.top.rootKey →
          (∀ z, TReach (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) c.i w.top.rootKey z →
            (TReach (updN (wNode c.p base w) (X (s + (e + 1)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
              w.top.rootKey z ∨ New z) ∧ z ≠ X (s + (e + 1))) →
          WriterWP (appendKlongs (s + e) (X (s + e)) ins') c w1 (fun _ w2 =>
            WriterWP (do let m ← getNode (X (s + (e + 1))); putNode (X (s + (e + 1))) (m.toPrev (c.i - 1)))
              c w2 (fun _ w3 =>
              TreeOK (wNode c.p base w3) c.i w3.top.rootKey ∧
              (w3.top = w.top ∧ w3.taken = w.taken ∧ w3.path = w.path ∧ w.next ≤ w3.next ∧ w3.vals = w.vals) ∧
              (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
                w3.nodes.lookup z = w.nodes.lookup z) ∧
              (∀ z, TReach (wNode c.p base w3) c.i w3.top.rootKey z →
                TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                  w.top.rootKey z ∨ w.next ≤ z))) := by
        intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hRV1
        have hpar := ih (by omega) w1 ins' hins' hinsT' (by rw [h1path, hS1])
          (by
            intro i h1 h2
            obtain ⟨a, b⟩ := hS2 i h1 (by omega)
            refine ⟨?_, by rw [h1t]; exact b⟩
            rw [h1low _ (hXlt i h1 (by omega)), a])
          (by rw [hN1, h1top]; exact hT1)
          (by intro i h1 h2; rw [hN1, h1top]; exact hR1 i h1 h2)
          hS5' (by rw [hN1]; exact hS6')
          (by rw [hN1, h1top]; exact hV1)
        refine writerWP_mono hpar ?_
        rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach⟩
        have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
          rw [h2frame _ (by have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)
            (fun i h1 h2 he => by have := hdist _ _ (by omega) hD h1 (by omega) he; omega),
            h1low _ (hXlt (s + (e + 1)) (by omega) (Nat.le_refl _)), hlk]
        simp only [writerWP_bind]
        rw [writerWP_getNode_known _ _ c w2 hlk2]
        simp only [putNode, writerWP_modify]
        have htk2 : w2.taken.contains (X (s + (e + 1))) = false := by rw [h2t, h1t]; exact htk
        generalize hw3 : ({ w2 with nodes := upsert w2.nodes (X (s + (e + 1))) ((Nn (s + (e + 1))).toPrev (c.i - 1)) } : W) = w3
        have h3n : w3.nodes = upsert w2.nodes (X (s + (e + 1))) ((Nn (s + (e + 1))).toPrev (c.i - 1)) := by
          rw [← hw3]
        have h3t : w3.taken = w2.taken := by rw [← hw3]
        have hN3 := wNode_upsert_updN c.p base w2 w3 (X (s + (e + 1))) _ h3n h3t htk2
        have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (s + (e + 1))) := by
          intro h
          rcases h2reach _ h with h' | h'
          · rw [hN1, h1top] at h'
            exact (hRV1 _ h').2 rfl
          · have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [hN3]; exact treeOK_updN_unreach _ c.i _ _ _ hT2 hxR2
        · rw [h2top, h1top]
        · rw [h2t, h1t]
        · rw [h2path, h1path]
        · omega
        · rw [h2vals, h1vals]
        · intro z hz hzX
          rw [lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _))),
            h2frame z (by omega) (fun i h1 h2 => hzX i h1 (by omega)), h1low z hz]
        · intro z hz
          rw [hN3] at hz
          have hz2 := tReach_updN_unreach _ c.i _ _ _ hxR2 z hz
          rcases h2reach z hz2 with h' | h'
          · rw [hN1, h1top] at h'
            rcases (hRV1 z h').1 with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (hNew z h'')
          · exact Or.inr (by omega)
      -- a time split, for either flag
      have hstepT : ∀ compact : Bool,
          (!compact && decide (((Nn (s + (e + 1))).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) compact) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                w.top.rootKey z ∨ w.next ≤ z)) := by
        intro compact hcs
        apply writerWP_handleFullWith_time_up (s + e) (X (s + (e + 1))) (X (s + e)) (Nn (s + (e + 1)))
          (Nn (s + e)) (K (s + (e + 1))) ins compact c w hlk hlq hql hfirst hcs hpq hpk
        intro l hl_leaf hl_wf hl_times hl_look w1 h1n h1t h1top h1path h1next h1vals
        have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ :=
          wNode_append_updN c.p base w w1 _ h1n h1t hfree0 htk0
        have hlsub : ∀ c' z, (c', z) ∈ (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode).liveAt c.i →
            (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          apply KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes
          have h' : (c', z) ∈ (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode).live := by
            rw [← KNode.liveAt_of_times (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode) c.i hl_times]; exact h
          have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z h'
          rw [← hl_look c']
          exact hlk'
        obtain ⟨hT1V, hR1V⟩ := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
          (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey (X (s + e))
          (X (s + (e + 1))) w.next (Nn (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
          ⟨(Nn (s + (e + 1))).leaf, l.ks⟩
          ([(K (s + (e + 1)), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
          (K (s + (e + 1))) hV hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq)
          hkl (updN_self _ _ _) (updN_self _ _ _)
          (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
          (by
            rw [updN_ne _ _ _ _ (fun h => by have := hXlt (s + e) (by omega) (by omega); omega), hN1]
            exact updN_self _ _ _)
          hlsub
          (by
            intro z hz1 hz2 hz3
            rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3]
            exact (updN_ne _ _ _ _ hz1).symm)
          (by
            rw [updN_ne _ _ _ _ (fun h => by
              have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)]
            exact hwnext)
          (hVfresh w.next (Nat.le_refl _))
        apply hfinish w1 [(K (s + (e + 1)), w.next)] _ (fun z => z = w.next)
          (Or.inl ⟨_, _, rfl⟩) (by intro q hq; simp at hq; rw [hq, h1next]; simp)
          h1path h1t h1top (by omega) h1vals (fun z hz => by have h : z = w.next := hz; omega)
          (by
            intro z hz
            rw [h1n, List.lookup_append]
            cases h : w.nodes.lookup z with
            | some _ => rfl
            | none =>
              have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
              simp [List.lookup, hb])
          hN1
          (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _)))
          (by
            intro i h1 h2
            obtain ⟨a, ha⟩ := (hS4 i h1 (by omega)).pathLen
            exact tReach_updN_of_short _ c.i _ _ _ a _ ha
              (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _))))
          (by
            intro z hz
            rw [h1next] at hz
            obtain ⟨a, b, d⟩ := hS5 z (by omega)
            refine ⟨?_, by rw [h1t]; exact b, d⟩
            rw [h1n, List.lookup_append, a]
            have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
            simp [List.lookup, hb])
          (by
            intro u c' z hl
            rw [h1next]
            obtain ⟨m, hm, hc⟩ := hl
            by_cases hu : u = w.next
            · rw [hu, updN_self] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              have := hvxLinks c' z (hlsub c' z hc); omega
            · rw [updN_ne _ _ _ _ hu] at hm
              have := hS6 u c' z ⟨m, hm, hc⟩; omega)
          (by rw [← hN1]; exact hT1V)
          (by rw [← hN1]; exact hR1V)
      -- a space split
      have hstepS : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) false) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            (w'.top = w.top ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                w.top.rootKey z ∨ w.next ≤ z)) := by
        intro hsp
        have h2l := hlen (s + (e + 1)) hj hD hsp
        obtain ⟨r, hr⟩ := divider_exists (Nn (s + (e + 1))) (by omega)
        have hrm := divider_mem_live _ r hr
        have hsc := divider_pos' _ r h2l hr
        obtain ⟨a, more, hins_eq, hside⟩ := hins.side r hrm
        obtain ⟨hdiv, hfh, hsh⟩ := halves_links (Nn (s + (e + 1))).leaf c.i (Nn (s + (e + 1))) rfl
          a more r hr hsc hside
        rw [← hins_eq] at hdiv hfh hsh
        apply writerWP_handleFullWith_space_up (s + e) (X (s + (e + 1))) (X (s + e)) (Nn (s + (e + 1)))
          (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hql hfirst hsp hpq hpk
        intro w1 h1n h1t h1top h1path h1next h1vals
        obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins = o :=
          ⟨_, rfl⟩
        rw [hout] at h1n hdiv hfh hsh ⊢
        rw [hdiv]
        have h12 : w.next ≠ w.next + 2 := by omega
        have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1 :=
          wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t h12 htk0 htk2'
        have hf : ∀ c' z, (c', z) ∈ out.1.liveAt c.i → c' < r.1 ∧
            (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          obtain ⟨h1, h2⟩ := hfh c' z h
          exact ⟨h1, KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes c' z h2⟩
        have hs : ∀ c' z, (c', z) ∈ out.2.1.liveAt c.i → ∃ c0, r.1 ≤ c0 ∧
            c' = splitLocalCv (Nn (s + (e + 1))).leaf r.1 c0 ∧
            (c0, z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          obtain ⟨c0, h1, h2, h3⟩ := hsh c' z h
          exact ⟨c0, h1, h2, KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes c0 z h3⟩
        have hq1wf := KNode.add_key_wf (Nn (s + e)) c.i (K (s + (e + 1))) w.next hqwf
        have hq1t := KNode.add_times (Nn (s + e)) c.i (.key (K (s + (e + 1))) w.next)
          (fun s h => by cases h) hqtimes
        have hqlinks : ∀ c' z, (c', z) ∈ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i →
            (c' = r.1 ∧ z = w.next + 2) ∨ (c' ≠ r.1 ∧ c' = K (s + (e + 1)) ∧ z = w.next) ∨
            (c' ≠ r.1 ∧ c' ≠ K (s + (e + 1)) ∧ (c', z) ∈ (Nn (s + e)).liveAt c.i) := by
          intro c' z h
          simp only [List.foldl_cons, List.foldl_nil] at h
          rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
            · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
        have hXn1 : X (s + (e + 1)) ≠ w.next := by
          have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        have hXn2 : X (s + (e + 1)) ≠ w.next + 2 := by
          have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        have hQn1 : X (s + e) ≠ w.next := by have := hXlt (s + e) (by omega) (by omega); omega
        have hQn2 : X (s + e) ≠ w.next + 2 := by have := hXlt (s + e) (by omega) (by omega); omega
        obtain ⟨hT1V, hR1V⟩ := treeOK_spaceSplit_gen (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
          (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey (X (s + e))
          (X (s + (e + 1))) w.next (w.next + 2) (Nn (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) out.1 out.2.1
          ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
          (K (s + (e + 1))) r.1 (splitLocalCv (Nn (s + (e + 1))).leaf r.1) hV hqR
          (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hkl (updN_self _ _ _) (updN_self _ _ _) hqlinks
          (by rw [updN_ne _ _ _ _ hQn1.symm, hN1, updN_ne _ _ _ _ h12]; exact updN_self _ _ _)
          (by rw [updN_ne _ _ _ _ hQn2.symm, hN1]; exact updN_self _ _ _)
          hf hs
          (by
            intro z hz1 hz2 hz3 hz4
            rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3]
            exact (updN_ne _ _ _ _ hz1).symm)
          (by rw [updN_ne _ _ _ _ hXn1.symm]; exact hwnext)
          (by rw [updN_ne _ _ _ _ hXn2.symm]; exact hwnext2)
          h12
          (by
            intro z hz
            rcases hz with hz | hz <;> rw [hz]
            · exact hVfresh w.next (Nat.le_refl _)
            · exact hVfresh (w.next + 2) (by omega))
        have hrK := hrange (s + (e + 1)) hj hD r.1 r.2 hrm hsc
        apply hfinish w1 [(K (s + (e + 1)), w.next), (r.1, w.next + 2)] _
          (fun z => z = w.next ∨ z = w.next + 2)
          (Or.inr ⟨_, _, _, _, rfl, hrK.1, fun c'' z'' hm hlt => by
            have := hrK.2 c'' z'' (by simpa using hm) hlt; exact this⟩)
          (by
            intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with hq | hq <;> rw [hq, h1next] <;> simp <;> omega)
          h1path h1t h1top (by omega) h1vals (fun z hz => by rcases hz with hz | hz <;> omega)
          (by
            intro z hz
            rw [h1n]
            have h1' : ¬ z = w.next := by omega
            have h2' : ¬ z = w.next + 2 := by omega
            simp only [h1', h2', ↓reduceIte])
          hN1
          (by
            have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
              fun h => hyR (w.next + 2) (by omega)
                (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
            exact treeOK_updN_unreach _ c.i _ _ _
              (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2)
          (by
            intro i h1 h2
            have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
              fun h => hyR (w.next + 2) (by omega)
                (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
            obtain ⟨a, ha⟩ := (hS4 i h1 (by omega)).pathLen
            have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
              (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
            obtain ⟨a', ha'⟩ := h1r.pathLen
            exact tReach_updN_of_short _ c.i _ _ _ a' _ ha' (fun b hb => absurd hb.reach hR2))
          (by
            intro z hz
            rw [h1next] at hz
            obtain ⟨a, b, d⟩ := hS5 z (by omega)
            refine ⟨?_, by rw [h1t]; exact b, d⟩
            rw [h1n]
            have h1' : ¬ z = w.next := by omega
            have h2' : ¬ z = w.next + 2 := by omega
            simp only [h1', h2', ↓reduceIte, a])
          (by
            intro u c' z hl
            rw [h1next]
            obtain ⟨m, hm, hc⟩ := hl
            by_cases hu2 : u = w.next + 2
            · rw [hu2, updN_self] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              obtain ⟨c0, _, _, h3⟩ := hs c' z hc
              have := hvxLinks c0 z h3; omega
            · rw [updN_ne _ _ _ _ hu2] at hm
              by_cases hu1 : u = w.next
              · rw [hu1, updN_self] at hm
                simp only [Option.some.injEq] at hm
                subst hm
                have := hvxLinks c' z (hf c' z hc).2; omega
              · rw [updN_ne _ _ _ _ hu1] at hm
                have := hS6 u c' z ⟨m, hm, hc⟩; omega)
          (by rw [← hN1]; exact hT1V)
          (by rw [← hN1]; exact hR1V)
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn (s + (e + 1))).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size
        · exact hstepS hsp
        · apply hstepT false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
          exact hsp
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hstepT true (by simp)

end SIS.Tree
