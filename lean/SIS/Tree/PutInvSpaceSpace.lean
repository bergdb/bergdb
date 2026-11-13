import SIS.Tree.PutInvDelSpace
import SIS.Tree.GetSpaceSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a space split of a leaf L whose full inner parent q is
space split too, below a grandparent g with room for two klongs (bergdb 024-12,
TP10; prover latest's `writerWP_put_spaceSpace`). q's last version gets the
klongs to L's halves, k1 to the first and the leaf's divider sL to the second;
both lie on one side of q's own divider sq (`halves_inner_live2`). -/

theorem halves_inner_live2 (qn : KNode) (t : Time) (k1 sL : Nat) (F S : NodeId)
    (hql : qn.leaf = false) (hks : k1 ≤ sL)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hside : decide (r.1 ≤ sL) = decide (r.1 ≤ k1)) :
    (halves qn.leaf t (qn.lastVersion t) [(k1, F), (sL, S)]).2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ (halves qn.leaf t (qn.lastVersion t) [(k1, F), (sL, S)]).1.live →
      c < r.1 ∧ ((c = sL ∧ z = S) ∨ (c = k1 ∧ z = F) ∨ (c ≠ k1 ∧ c ≠ sL ∧ (c, z) ∈ qn.live))) ∧
    (∀ c z, (c, z) ∈ (halves qn.leaf t (qn.lastVersion t) [(k1, F), (sL, S)]).2.1.live →
      ∃ c0, r.1 ≤ c0 ∧ c = (if c0 = r.1 then 0 else c0) ∧
       ((c0 = sL ∧ z = S) ∨ (c0 = k1 ∧ z = F) ∨ (c0 ≠ k1 ∧ c0 ≠ sL ∧ (c0, z) ∈ qn.live))) := by
  have hlv : qn.lastVersion t = ⟨false, newKlongs t qn.live⟩ := by
    rw [KNode.lastVersion_eq_newKlongs, hql]
  rw [hlv, hql]
  have hs : CvSorted qn.live := KNode.live_order qn
  have hshape := halves_shape false t qn.live [(k1, F), (sL, S)] r hr
  simp only [List.head?_cons] at hshape
  have hlook := halves_lookup false t qn.live [(k1, F), (sL, S)] hs r hr hsc (by
    intro q hq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rfl
    · exact hside)
  simp only at hlook
  have hleft := halves_left_lt_divider qn.live (qn.live.length / 2) hs r hr
  have hright := halves_right_ge_divider qn.live (qn.live.length / 2) hs r hr
  generalize hH : halves false t ⟨false, newKlongs t qn.live⟩ [(k1, F), (sL, S)] = H at hshape hlook
  have hdrop : ∀ c z, (c, z) ∈ secondSplitPairs false qn.live →
      ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv false r.1 c0 := by
    intro c z hm
    rw [secondSplitPairs_eq_map false qn.live hs r hr] at hm
    obtain ⟨q0, hq0, he⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at he
    exact ⟨q0.1, hright q0 hq0, he.1.symm⟩
  have key : ∃ A B : KNode, H = (A, B, r.1) ∧ (∀ c z, (c, z) ∈ A.live → c < r.1) ∧
      (∀ c z, (c, z) ∈ B.live → ∃ c0, r.1 ≤ c0 ∧ c = splitLocalCv false r.1 c0) := by
    cases hk : decide (r.1 ≤ k1) with
    | true =>
      simp only [hk, ↓reduceIte] at hshape
      refine ⟨_, _, hshape, ?_, ?_⟩
      · intro c z hm
        exact hleft (c, z) (newKlongs_live_mem false t _ c z hm)
      · intro c z hm
        rcases List.mem_append.mp (newKlongs_live_mem false t _ c z hm) with h1 | h1
        · exact hdrop c z h1
        · simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_singleton,
            Prod.mk.injEq, List.not_mem_nil, or_false] at h1
          have hk' : r.1 ≤ k1 := by simpa using hk
          rcases h1 with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact ⟨k1, hk', h1⟩
          · exact ⟨sL, by omega, h1⟩
    | false =>
      simp only [hk, Bool.false_eq_true, ↓reduceIte] at hshape
      have hk' : k1 < r.1 := by simp at hk; omega
      have hsl' : sL < r.1 := by rw [hk] at hside; simp at hside; omega
      refine ⟨_, _, hshape, ?_, ?_⟩
      · intro c z hm
        rcases List.mem_append.mp (newKlongs_live_mem false t _ c z hm) with h1 | h1
        · exact hleft (c, z) h1
        · simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil,
            or_false] at h1
          rcases h1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · intro c z hm
        exact hdrop c z (newKlongs_live_mem false t _ c z hm)
  obtain ⟨A, B, hHe, hA, hB⟩ := key
  subst hHe
  simp only at hlook ⊢
  have hval : ∀ c0 z, ([(k1, F), (sL, S)].foldl (pairLookupStep c0) (qn.live.lookup c0) = some z) →
      (c0 = sL ∧ z = S) ∨ (c0 = k1 ∧ z = F) ∨ (c0 ≠ k1 ∧ c0 ≠ sL ∧ (c0, z) ∈ qn.live) := by
    intro c0 z h
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at h
    by_cases h1 : sL = c0
    · subst h1; simp at h; exact Or.inl ⟨rfl, h.symm⟩
    · have hb1 : (sL == c0) = false := by simpa using h1
      simp only [hb1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : k1 = c0
      · subst h2; simp at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
      · have hb2 : (k1 == c0) = false := by simpa using h2
        simp only [hb2, Bool.false_eq_true, ↓reduceIte] at h
        exact Or.inr (Or.inr ⟨fun h' => h2 h'.symm, fun h' => h1 h'.symm, lookup_some_mem h⟩)
  refine ⟨trivial, ?_, ?_⟩
  · intro c z hz
    have hcl := hA c z hz
    refine ⟨hcl, ?_⟩
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz
    have hlk := hlook c
    simp only [hcl, ↓reduceIte] at hlk
    rw [hl] at hlk
    exact hval c z hlk.symm
  · intro c z hz
    obtain ⟨c0, hc0, hce⟩ := hB c z hz
    refine ⟨c0, hc0, ?_, ?_⟩
    · rw [hce]; unfold splitLocalCv; by_cases h : c0 = r.1 <;> simp [h]
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz
    have hlk := hlook c0
    simp only [show ¬ c0 < r.1 by omega, ↓reduceIte] at hlk
    rw [← hce, hl] at hlk
    exact hval c0 z hlk.symm

/-- The parts about the tree after a space split of a leaf L whose inner
parent q, full, is space split too, below the grandparent g: L's halves F and S
(divider sL), q's halves Q1 and Q2 (divider sq) with the klongs k1 to F and sL
to S, g's klongs kq to Q1 and sq to Q2. -/
theorem putInvT_spaceSpace (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv sL k1 kq sq : Nat) (v F S Q1 Q2 L q g : NodeId) (n qn gn f s f1 f2 : KNode)
    (hv : w.next ≤ v) (hF : w.next ≤ F) (hS : w.next ≤ S) (hQ1 : w.next ≤ Q1) (hQ2 : w.next ≤ Q2)
    (hvF : v ≠ F) (hvS : v ≠ S) (hvQ1 : v ≠ Q1) (hvQ2 : v ≠ Q2) (hFS : F ≠ S) (hFQ1 : F ≠ Q1)
    (hFQ2 : F ≠ Q2) (hSQ1 : S ≠ Q1) (hSQ2 : S ≠ Q2) (hQ12 : Q1 ≠ Q2)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hgn : wNode c.p base w g = some gn) (hgl : gn.leaf = false)
    (hg : ReachS (wNode c.p base w) c.i w.top.rootKey g)
    (hkq : (kq, q) ∈ gn.live) (hk1 : (k1, L) ∈ qn.live)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live → 0 < c' →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hsq : ∃ zs, (sq, zs) ∈ qn.live) (hsq0 : 0 < sq)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'g : wNode c.p base w' g = some ((gn.add c.i (.key kq Q1)).add c.i (.key sq Q2)))
    (hN'F : wNode c.p base w' F = some f) (hN'S : wNode c.p base w' S = some s)
    (hfl : f.leaf = true) (hsl : s.leaf = true)
    (hft : ∀ t, Klong.time t ∈ f.ks → t ≤ c.i) (hst : ∀ t, Klong.time t ∈ s.ks → t ≤ c.i)
    (hf : ∀ c' z, (c', z) ∈ f.liveAt c.i → ((c', z) = (cv, v) ∧ cv < sL) ∨ ((c', z) ∈ n.live ∧ c' < sL))
    (hs : ∀ c' z, (c', z) ∈ s.liveAt c.i →
      ((c', z) = (cv, v) ∧ sL ≤ cv) ∨ ((c', z) ∈ n.live ∧ sL ≤ c'))
    (hsL : ∃ zs, (sL, zs) ∈ n.live)
    (hN'Q1 : wNode c.p base w' Q1 = some f1) (hf1l : f1.leaf = false)
    (hf1t : ∀ s, Klong.time s ∈ f1.ks → s ≤ c.i)
    (hf1 : ∀ c' z, (c', z) ∈ f1.live →
      c' < sq ∧ ((c' = sL ∧ z = S) ∨ (c' = k1 ∧ z = F) ∨ (c' ≠ k1 ∧ c' ≠ sL ∧ (c', z) ∈ qn.live)))
    (hN'Q2 : wNode c.p base w' Q2 = some f2) (hf2l : f2.leaf = false)
    (hf2t : ∀ s, Klong.time s ∈ f2.ks → s ≤ c.i)
    (hf2 : ∀ c' z, (c', z) ∈ f2.live → ∃ c0, sq ≤ c0 ∧ c' = (if c0 = sq then 0 else c0) ∧
      ((c0 = sL ∧ z = S) ∨ (c0 = k1 ∧ z = F) ∨ (c0 ≠ k1 ∧ c0 ≠ sL ∧ (c0, z) ∈ qn.live)))
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ F → x ≠ S → x ≠ Q1 → x ≠ Q2 →
      wNode c.p base w' x = wNode c.p base w x)
    (hpar : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hgnext := hI.lt_next g gn hgn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hnt := hI.times L n hn
  have hqt := hI.times q qn hqn
  have hgt := hI.times g gn hgn
  have hgwf := hI.wf g gn hgn
  have hkq' : (kq, q) ∈ gn.liveAt c.i := by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkq
  have hk1' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  have hT := htree_of_treeOK _ _ _ hI.tree
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q := ReachS.step g gn kq q hg hgn hkq'
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L := ReachS.step q qn k1 L hrq hqn hk1'
  have hqnext := hI.reach_lt q hrq
  have hLnext := hI.reach_lt L hrL
  have honlyq : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, q) ∈ xn.liveAt c.i → x = g ∧ cc = kq :=
    fun x xn cc hx hxn hc => hT x xn cc q hx hxn hc g gn kq hg hgn hkq'
  have honlyL : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = q ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc q qn k1 hrq hqn hk1'
  have hgq : g ≠ q := by
    intro he; subst he
    exact hI.tree.no_self_link g kq (reachS_tReach _ _ _ _ hg) ⟨gn, hgn, hkq'⟩
  have hgL : g ≠ L := by intro he; subst he; rw [hn] at hgn; cases hgn; rw [hnl] at hgl; cases hgl
  have hrootq : w.top.rootKey ≠ q := by
    intro he; exact hI.rootFree' g gn kq hg hgn (he ▸ hkq')
  have hrootL : w.top.rootKey ≠ L := by
    intro he; exact hI.rootFree' q qn k1 hrq hqn (he ▸ hk1')
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) (by omega) hvF hvS hvQ1 hvQ2]; exact hvN
  have hold : LeafOrderAt qn k1 n := hI.order q qn L n k1 hrq hqn hql hn hnl hk1
  have hsLb : k1 ≤ sL ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → sL < c'' := by
    obtain ⟨zs, hzs⟩ := hsL
    exact hold sL zs hzs
  have hscg : kq ≤ sq ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → sq < c'' := by
    obtain ⟨zs, hzs⟩ := hsq
    exact hrangeq sq zs hzs hsq0
  have hg1wf := KNode.add_key_wf gn c.i kq Q1 hgwf
  have hg1t := KNode.add_times gn c.i (.key kq Q1) (fun s h => by cases h) hgt
  have hg2t := KNode.add_times _ c.i (.key sq Q2) (fun s h => by cases h) hg1t
  have hglive : ∀ c' z, (c', z) ∈ ((gn.add c.i (.key kq Q1)).add c.i (.key sq Q2)).liveAt c.i →
      (c' = sq ∧ z = Q2) ∨ (c' = kq ∧ z = Q1) ∨ (c' ≠ kq ∧ (c', z) ∈ gn.liveAt c.i) := by
    intro c' z h
    rcases KNode.add_key_liveAt_mem _ c.i sq Q2 hg1wf hg1t c' z h with h1 | ⟨_, h1⟩
    · exact Or.inl h1
    · rcases KNode.add_key_liveAt_mem gn c.i kq Q1 hgwf hgt c' z h1 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  have hqold : ∀ cc z, (cc, z) ∈ qn.live → cc ≠ k1 →
      ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ L ∧ z ≠ q := by
    intro cc z hz hne
    have hz' : (cc, z) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hz
    refine ⟨ReachS.step q qn cc z hrq hqn hz', ?_, ?_⟩
    · intro hzL; subst hzL; exact hne (honlyL q qn cc hrq hqn hz').2
    · intro hzq; subst hzq
      exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, hz'⟩
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧ x ≠ q) ∨
        x = F ∨ x = S ∨ x = Q1 ∨ x = Q2 ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧
      x ≠ q) ∨ x = F ∨ x = S ∨ x = Q1 ∨ x = Q2 ∨ x = v) (Or.inl ⟨ReachS.root, hrootL, hrootq⟩)
    intro x xn cc z hx hxn hz
    have hhalf : ∀ (m : KNode), (∀ t, Klong.time t ∈ m.ks → t ≤ c.i) →
        (∀ c' z, (c', z) ∈ m.liveAt c.i → (c', z) = (cv, v) ∨ (c', z) ∈ n.live) →
        (cc, z) ∈ m.liveAt c.i →
        (ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ L ∧ z ≠ q) ∨
          z = F ∨ z = S ∨ z = Q1 ∨ z = Q2 ∨ z = v := by
      intro m _ hm hzm
      rcases hm cc z hzm with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1.2))))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h1
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h1, ?_, ?_⟩
        · intro hzL; subst hzL
          exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h1⟩
        · intro hzq; subst hzq; exact hgL (honlyq L n cc hrL hn h1).1.symm
    have hqhalf : ∀ (c0 : Nat), ((c0 = sL ∧ z = S) ∨ (c0 = k1 ∧ z = F) ∨
        (c0 ≠ k1 ∧ c0 ≠ sL ∧ (c0, z) ∈ qn.live)) →
        (ReachS (wNode c.p base w) c.i w.top.rootKey z ∧ z ≠ L ∧ z ≠ q) ∨
          z = F ∨ z = S ∨ z = Q1 ∨ z = Q2 ∨ z = v := by
      intro c0 h
      rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨hne, _, h2⟩
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inl h2)
      · exact Or.inl (hqold c0 z h2 hne)
    rcases hx with ⟨hx, hxL, hxq⟩ | hx | hx | hx | hx | hx
    · have hxnext := hI.reach_lt x hx
      by_cases hxg : x = g
      · subst hxg
        rw [hN'g] at hxn
        cases hxn
        rcases hglive cc z hz with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · refine Or.inl ⟨ReachS.step x gn cc z hx hgn h2, ?_, ?_⟩
          · intro hzL; subst hzL; exact hgq (honlyL x gn cc hx hgn h2).1
          · intro hzq; subst hzq; exact hne (honlyq x gn cc hx hgn h2).2
      · rw [hother x hxL hxq hxg (by omega) (by omega) (by omega) (by omega)] at hxn
        refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_, ?_⟩
        · intro hzL; subst hzL; exact hxq (honlyL x xn cc hx hxn hz).1
        · intro hzq; subst hzq; exact hxg (honlyq x xn cc hx hxn hz).1
    · subst hx
      rw [hN'F] at hxn
      cases hxn
      exact hhalf _ hft (fun c' z h => by
        rcases hf c' z h with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1) hz
    · subst hx
      rw [hN'S] at hxn
      cases hxn
      exact hhalf _ hst (fun c' z h => by
        rcases hs c' z h with h1 | h1
        · exact Or.inl h1.1
        · exact Or.inr h1.1) hz
    · subst hx
      rw [hN'Q1] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hf1t] at hz
      exact hqhalf cc (hf1 cc z hz).2
    · subst hx
      rw [hN'Q2] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hf2t] at hz
      obtain ⟨c0, _, _, h2⟩ := hf2 cc z hz
      exact hqhalf c0 h2
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx | hx | hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hF
    · subst hx; exact hI.untaken_of_ge _ hS
    · subst hx; exact hI.untaken_of_ge _ hQ1
    · subst hx; exact hI.untaken_of_ge _ hQ2
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q' q'n L' n' k1' hq' hq'n hq'l hn' hnl' hk'
    have hL'g : L' ≠ g := by
      intro he; subst he; rw [hN'g] at hn'; cases hn'
      rw [KNode.add_leaf, KNode.add_leaf, hgl] at hnl'; cases hnl'
    have hL'Q1 : L' ≠ Q1 := by
      intro he; subst he; rw [hN'Q1] at hn'; cases hn'; rw [hf1l] at hnl'; cases hnl'
    have hL'Q2 : L' ≠ Q2 := by
      intro he; subst he; rw [hN'Q2] at hn'; cases hn'; rw [hf2l] at hnl'; cases hnl'
    -- the bound of a child of q's halves, by its compare value c0 in q
    have hbound : ∀ c0, ((c0 = sL ∧ L' = S) ∨ (c0 = k1 ∧ L' = F) ∨
        (c0 ≠ k1 ∧ c0 ≠ sL ∧ (c0, L') ∈ qn.live)) →
        ∀ c' z, (c', z) ∈ n'.live → c0 ≤ c' ∧
          (∀ c'' z', (c'', z') ∈ qn.live → c0 < c'' → c' < c'') ∧
          (c0 < sL → c' < sL) ∧ (c0 < k1 → c' < k1) := by
      intro c0 h c' z hz
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hne, hne2, h2⟩
      · subst h1 h2
        rw [hN'S] at hn'
        cases hn'
        rw [← KNode.liveAt_of_times _ c.i hst] at hz
        have hb : (k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'') ∧ c0 ≤ c' := by
          rcases hs c' z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Prod.mk.injEq] at h1; rw [h1.1]; exact ⟨hpar, h1.1 ▸ h2⟩
          · exact ⟨hold c' z h1, h2⟩
        refine ⟨hb.2, fun c'' z' hz' hlt => hb.1.2 c'' z' hz' (by omega), by omega, by omega⟩
      · subst h1 h2
        rw [hN'F] at hn'
        cases hn'
        rw [← KNode.liveAt_of_times _ c.i hft] at hz
        have hb : (c0 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → c0 < c'' → c' < c'') ∧ c' < sL := by
          rcases hf c' z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Prod.mk.injEq] at h1; rw [h1.1]; exact ⟨hpar, h1.1 ▸ h2⟩
          · exact ⟨hold c' z h1, h2⟩
        exact ⟨hb.1.1, hb.1.2, fun _ => hb.2, by omega⟩
      · have hk'' : (c0, L') ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact h2
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hne (honlyL q qn c0 hrq hqn hk'').2
        have hL'q : L' ≠ q := by
          intro he; subst he
          exact hI.tree.no_self_link L' c0 (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, hk''⟩
        have hlt' := hI.links q qn c0 L' hrq hqn hk''
        rw [hother L' hL'L hL'q hL'g (by omega) (by omega) hL'Q1 hL'Q2] at hn'
        have ho := hI.order q qn L' n' c0 hrq hqn hql hn' hnl' h2
        refine ⟨(ho c' z hz).1, (ho c' z hz).2, ?_, ?_⟩
        · intro hlt
          by_cases hk : c0 < k1
          · have := (ho c' z hz).2 k1 L hk1 hk; omega
          · have hk' : k1 < c0 := by omega
            have := hsLb.2 c0 L' h2 hk'; omega
        · intro hlt; exact (ho c' z hz).2 k1 L hk1 hlt
    -- the order below a half of q: its klongs are q's, k1 to F and sL to S
    have hhalfOrder : ∀ (Q : KNode) (cc c0 : Nat),
        (∀ c'' z'', (c'', z'') ∈ Q.live → cc < c'' → ∃ c0'', c0 < c0'' ∧ c'' = c0'' ∧
          ((c0'' = sL ∧ z'' = S) ∨ (c0'' = k1 ∧ z'' = F) ∨
            (c0'' ≠ k1 ∧ c0'' ≠ sL ∧ (c0'', z'') ∈ qn.live))) →
        (cc = 0 ∨ cc = c0) →
        ((c0 = sL ∧ L' = S) ∨ (c0 = k1 ∧ L' = F) ∨ (c0 ≠ k1 ∧ c0 ≠ sL ∧ (c0, L') ∈ qn.live)) →
        LeafOrderAt Q cc n' := by
      intro Q cc c0 hQ hcc hch c' z hz
      have hb := hbound c0 hch c' z hz
      refine ⟨by rcases hcc with h | h <;> omega, ?_⟩
      intro c'' z'' hz'' hlt
      obtain ⟨c0'', hlt'', he, h3⟩ := hQ c'' z'' hz'' hlt
      rw [he]
      rcases h3 with ⟨h4, _⟩ | ⟨h4, _⟩ | ⟨_, _, h4⟩
      · subst h4; exact hb.2.2.1 hlt''
      · subst h4; exact hb.2.2.2 hlt''
      · exact hb.2.1 c0'' z'' h4 hlt''
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'q⟩ | hq'F | hq'S | hq'Q1 | hq'Q2 | hq'v
    · have hq'next := hI.reach_lt q' hq'r
      by_cases hq'g : q' = g
      · subst hq'g
        rw [hN'g] at hq'n
        cases hq'n
        rw [← KNode.liveAt_of_times _ c.i hg2t] at hk'
        rcases hglive k1' L' hk' with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact absurd h2 hL'Q2
        · exact absurd h2 hL'Q1
        · have hL'L : L' ≠ L := by
            intro he; subst he; exact hgq (honlyL q' gn k1' hg hgn h2).1
          have hL'q : L' ≠ q := by
            intro he; subst he; exact hne (honlyq q' gn k1' hg hgn h2).2
          have hlt' := hI.links q' gn k1' L' hg hgn h2
          rw [hother L' hL'L hL'q hL'g (by omega) (by omega) hL'Q1 hL'Q2] at hn'
          rw [KNode.liveAt_of_times gn c.i hgt] at h2
          have ho := hI.order q' gn L' n' k1' hg hgn hgl hn' hnl' h2
          intro c' z hz
          refine ⟨(ho c' z hz).1, ?_⟩
          intro c'' z'' hz'' hlt
          rw [← KNode.liveAt_of_times _ c.i hg2t] at hz''
          rcases hglive c'' z'' hz'' with ⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3⟩
          · subst h3
            by_cases hk : k1' < kq
            · have := (ho c' z hz).2 kq q hkq hk; omega
            · have hk' : kq < k1' := by omega
              have := hscg.2 k1' L' h2 hk'; omega
          · subst h3; exact (ho c' z hz).2 _ q hkq hlt
          · rw [KNode.liveAt_of_times gn c.i hgt] at h3
            exact (ho c' z hz).2 c'' z'' h3 hlt
      · rw [hother q' hq'L hq'q hq'g (by omega) (by omega) (by omega) (by omega)] at hq'n
        have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
          rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hq'q (honlyL q' q'n k1' hq'r hq'n hk'').1
        have hL'q : L' ≠ q := by
          intro he; subst he; exact hq'g (honlyq q' q'n k1' hq'r hq'n hk'').1
        have hlt' := hI.links q' q'n k1' L' hq'r hq'n hk''
        rw [hother L' hL'L hL'q hL'g (by omega) (by omega) hL'Q1 hL'Q2] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'F; rw [hN'F] at hq'n; cases hq'n; rw [hfl] at hq'l; cases hq'l
    · subst hq'S; rw [hN'S] at hq'n; cases hq'n; rw [hsl] at hq'l; cases hq'l
    · subst hq'Q1
      rw [hN'Q1] at hq'n
      cases hq'n
      obtain ⟨_, hch⟩ := hf1 k1' L' hk'
      refine hhalfOrder f1 k1' k1' ?_ (Or.inr rfl) hch
      intro c'' z'' hz'' hlt
      exact ⟨c'', hlt, rfl, (hf1 c'' z'' hz'').2⟩
    · subst hq'Q2
      rw [hN'Q2] at hq'n
      cases hq'n
      obtain ⟨c0, hc0, hk1e, hch⟩ := hf2 k1' L' hk'
      refine hhalfOrder f2 k1' c0 ?_ ?_ hch
      · intro c'' z'' hz'' hlt
        obtain ⟨c0'', hc0'', hce'', h3⟩ := hf2 c'' z'' hz''
        refine ⟨c0'', ?_, ?_, h3⟩
        · by_cases h0'' : c0'' = sq
          · simp only [h0'', ↓reduceIte] at hce''; omega
          · simp only [h0'', ↓reduceIte] at hce''
            by_cases h0 : c0 = sq
            · omega
            · simp only [h0, ↓reduceIte] at hk1e; omega
        · by_cases h0'' : c0'' = sq
          · simp only [h0'', ↓reduceIte] at hce''; omega
          · simp only [h0'', ↓reduceIte] at hce''; exact hce''
      · by_cases h0 : c0 = sq
        · simp only [h0, ↓reduceIte] at hk1e; exact Or.inl hk1e
        · simp only [h0, ↓reduceIte] at hk1e; exact Or.inr hk1e
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

end SIS.Tree
