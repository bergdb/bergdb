import SIS.Tree.PutInvChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a time split of a leaf L whose full inner parent q is
space split, below a grandparent g with room for two klongs (bergdb 024-12,
TP10; prover latest's `writerWP_put_timeSpace`). The halves of an inner
node's last version with a klong put: the first holds the compare values below
the divider, the second the divider (renamed to the empty key) and those above
(`halves_inner_live`). The order at g's other leaf children needs, as latest's
rule, the range of q's compare values in g (`hrange`): `PutInv`'s order is at
the leaves only. -/

theorem halves_inner_live (qn : KNode) (t : Time) (k1 : Nat) (Y : NodeId) (hql : qn.leaf = false)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1) :
    (halves qn.leaf t (qn.lastVersion t) [(k1, Y)]).2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ (halves qn.leaf t (qn.lastVersion t) [(k1, Y)]).1.live →
      c < r.1 ∧ ((c = k1 ∧ z = Y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.live))) ∧
    (∀ c z, (c, z) ∈ (halves qn.leaf t (qn.lastVersion t) [(k1, Y)]).2.1.live →
      ∃ c0, r.1 ≤ c0 ∧ c = (if c0 = r.1 then 0 else c0) ∧
       ((c0 = k1 ∧ z = Y) ∨ (c0 ≠ k1 ∧ (c0, z) ∈ qn.live))) := by
  have hlv : qn.lastVersion t = ⟨false, newKlongs t qn.live⟩ := by
    rw [KNode.lastVersion_eq_newKlongs, hql]
  rw [hlv, hql]
  have hs : CvSorted qn.live := KNode.live_order qn
  have hshape := halves_shape false t qn.live [(k1, Y)] r hr
  simp only [List.head?_cons] at hshape
  have hlook := halves_lookup false t qn.live [(k1, Y)] hs r hr hsc (by simp)
  simp only at hlook
  have hleft := halves_left_lt_divider qn.live (qn.live.length / 2) hs r hr
  have hright := halves_right_ge_divider qn.live (qn.live.length / 2) hs r hr
  generalize hH : halves false t ⟨false, newKlongs t qn.live⟩ [(k1, Y)] = H at hshape hlook
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
        · simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at h1
          exact ⟨k1, by simpa using hk, h1.1⟩
    | false =>
      simp only [hk, Bool.false_eq_true, ↓reduceIte] at hshape
      refine ⟨_, _, hshape, ?_, ?_⟩
      · intro c z hm
        rcases List.mem_append.mp (newKlongs_live_mem false t _ c z hm) with h1 | h1
        · exact hleft (c, z) h1
        · simp only [List.mem_singleton, Prod.mk.injEq] at h1
          rw [h1.1]; simp at hk; omega
      · intro c z hm
        exact hdrop c z (newKlongs_live_mem false t _ c z hm)
  obtain ⟨A, B, hHe, hA, hB⟩ := key
  subst hHe
  simp only at hlook ⊢
  have hval : ∀ c0 z, (k1 = c0 → z = Y) → (k1 ≠ c0 → qn.live.lookup c0 = some z) →
      (c0 = k1 ∧ z = Y) ∨ (c0 ≠ k1 ∧ (c0, z) ∈ qn.live) := by
    intro c0 z h1 h2
    by_cases hk : k1 = c0
    · exact Or.inl ⟨hk.symm, h1 hk⟩
    · exact Or.inr ⟨fun h => hk h.symm, lookup_some_mem (h2 hk)⟩
  refine ⟨trivial, ?_, ?_⟩
  · intro c z hz
    have hcl := hA c z hz
    refine ⟨hcl, ?_⟩
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz
    have hlk := hlook c
    simp only [hcl, ↓reduceIte] at hlk
    unfold pairLookupStep at hlk
    rw [hl] at hlk
    apply hval c z
    · intro hk; subst hk; simp at hlk; exact hlk
    · intro hk
      have hb : (k1 == c) = false := by simpa using hk
      simp only [List.foldl_cons, List.foldl_nil, hb, Bool.false_eq_true, ↓reduceIte] at hlk
      exact hlk.symm
  · intro c z hz
    obtain ⟨c0, hc0, hce⟩ := hB c z hz
    refine ⟨c0, hc0, ?_, ?_⟩
    · rw [hce]; unfold splitLocalCv; by_cases h : c0 = r.1 <;> simp [h]
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz
    have hlk := hlook c0
    simp only [show ¬ c0 < r.1 by omega, ↓reduceIte] at hlk
    unfold pairLookupStep at hlk
    rw [← hce, hl] at hlk
    apply hval c0 z
    · intro hk; subst hk; simp at hlk; exact hlk
    · intro hk
      have hb : (k1 == c0) = false := by simpa using hk
      simp only [List.foldl_cons, List.foldl_nil, hb, Bool.false_eq_true, ↓reduceIte] at hlk
      exact hlk.symm

/-- The parts about the tree after a time split of a leaf L whose inner parent
q, full, is space split, below the grandparent g: g's klong kq names the first
half Q1 and a klong at the divider sc the second half Q2 of q's last version
with k1 naming a new leaf yL, which holds L's live klongs and the put's
(cv, v). q's compare values lie in g's range for it (`hrangeq`). -/
theorem putInvT_timeSpace (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv sc k1 kq : Nat) (v yL Q1 Q2 L q g : NodeId) (n qn gn l f1 f2 : KNode)
    (hv : w.next ≤ v) (hyL : w.next ≤ yL) (hQ1 : w.next ≤ Q1) (hQ2 : w.next ≤ Q2)
    (hvyL : v ≠ yL) (hvQ1 : v ≠ Q1) (hvQ2 : v ≠ Q2) (hyLQ1 : yL ≠ Q1) (hyLQ2 : yL ≠ Q2)
    (hQ12 : Q1 ≠ Q2)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hgn : wNode c.p base w g = some gn) (hgl : gn.leaf = false)
    (hg : ReachS (wNode c.p base w) c.i w.top.rootKey g)
    (hkq : (kq, q) ∈ gn.live) (hk1 : (k1, L) ∈ qn.live)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hsc : ∃ zs, (sc, zs) ∈ qn.live)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN'g : wNode c.p base w' g = some ((gn.add c.i (.key kq Q1)).add c.i (.key sc Q2)))
    (hN'yL : wNode c.p base w' yL = some l) (hll : l.leaf = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hlive : ∀ c' z, (c', z) ∈ l.live → (c' = cv ∧ z = v) ∨ (c', z) ∈ n.live)
    (hN'Q1 : wNode c.p base w' Q1 = some f1) (hf1l : f1.leaf = false)
    (hf1t : ∀ s, Klong.time s ∈ f1.ks → s ≤ c.i)
    (hf1 : ∀ c' z, (c', z) ∈ f1.live →
      c' < sc ∧ ((c' = k1 ∧ z = yL) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.live)))
    (hN'Q2 : wNode c.p base w' Q2 = some f2) (hf2l : f2.leaf = false)
    (hf2t : ∀ s, Klong.time s ∈ f2.ks → s ≤ c.i)
    (hf2 : ∀ c' z, (c', z) ∈ f2.live → ∃ c0, sc ≤ c0 ∧ c' = (if c0 = sc then 0 else c0) ∧
      ((c0 = k1 ∧ z = yL) ∨ (c0 ≠ k1 ∧ (c0, z) ∈ qn.live)))
    (hother : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ yL → x ≠ Q1 → x ≠ Q2 →
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
  have hqL : q ≠ L := by intro he; subst he; rw [hn] at hqn; cases hqn; rw [hnl] at hql; cases hql
  have hgq : g ≠ q := by
    intro he; subst he
    exact hI.tree.no_self_link g kq (reachS_tReach _ _ _ _ hg) ⟨gn, hgn, hkq'⟩
  have hgL : g ≠ L := by intro he; subst he; rw [hn] at hgn; cases hgn; rw [hnl] at hgl; cases hgl
  have hrootq : w.top.rootKey ≠ q := by
    intro he; exact hI.rootFree' g gn kq hg hgn (he ▸ hkq')
  have hrootL : w.top.rootKey ≠ L := by
    intro he; exact hI.rootFree' q qn k1 hrq hqn (he ▸ hk1')
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (by omega) (by omega) hvyL hvQ1 hvQ2]; exact hvN
  have hold : LeafOrderAt qn k1 n := hI.order q qn L n k1 hrq hqn hql hn hnl hk1
  have hscg : kq ≤ sc ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → sc < c'' := by
    obtain ⟨zs, hzs⟩ := hsc
    exact hrangeq sc zs hzs
  have hg1wf := KNode.add_key_wf gn c.i kq Q1 hgwf
  have hg1t := KNode.add_times gn c.i (.key kq Q1) (fun s h => by cases h) hgt
  have hg2t := KNode.add_times _ c.i (.key sc Q2) (fun s h => by cases h) hg1t
  have hglive : ∀ c' z, (c', z) ∈ ((gn.add c.i (.key kq Q1)).add c.i (.key sc Q2)).liveAt c.i →
      (c' = sc ∧ z = Q2) ∨ (c' = kq ∧ z = Q1) ∨ (c' ≠ kq ∧ (c', z) ∈ gn.liveAt c.i) := by
    intro c' z h
    rcases KNode.add_key_liveAt_mem _ c.i sc Q2 hg1wf hg1t c' z h with h1 | ⟨_, h1⟩
    · exact Or.inl h1
    · rcases KNode.add_key_liveAt_mem gn c.i kq Q1 hgwf hgt c' z h1 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  -- a link of q's old klongs: reachable before, not L but by k1, not q
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
        x = yL ∨ x = Q1 ∨ x = Q2 ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => (ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L ∧
      x ≠ q) ∨ x = yL ∨ x = Q1 ∨ x = Q2 ∨ x = v) (Or.inl ⟨ReachS.root, hrootL, hrootq⟩)
    intro x xn cc z hx hxn hz
    rcases hx with ⟨hx, hxL, hxq⟩ | hx | hx | hx | hx
    · have hxnext := hI.reach_lt x hx
      by_cases hxg : x = g
      · subst hxg
        rw [hN'g] at hxn
        cases hxn
        rcases hglive cc z hz with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨hne, h2⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · exact Or.inr (Or.inr (Or.inl h2))
        · refine Or.inl ⟨ReachS.step x gn cc z hx hgn h2, ?_, ?_⟩
          · intro hzL; subst hzL; exact hgq (honlyL x gn cc hx hgn h2).1
          · intro hzq; subst hzq; exact hne (honlyq x gn cc hx hgn h2).2
      · rw [hother x hxL hxq hxg (by omega) (by omega) (by omega)] at hxn
        refine Or.inl ⟨ReachS.step x xn cc z hx hxn hz, ?_, ?_⟩
        · intro hzL; subst hzL; exact hxq (honlyL x xn cc hx hxn hz).1
        · intro hzq; subst hzq; exact hxg (honlyq x xn cc hx hxn hz).1
    · subst hx
      rw [hN'yL] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hlt] at hz
      rcases hlive cc z hz with ⟨_, h2⟩ | h2
      · exact Or.inr (Or.inr (Or.inr (Or.inr h2)))
      · rw [← KNode.liveAt_of_times n c.i hnt] at h2
        refine Or.inl ⟨ReachS.step L n cc z hrL hn h2, ?_, ?_⟩
        · intro hzL; subst hzL
          exact hI.tree.no_self_link z cc (reachS_tReach _ _ _ _ hrL) ⟨n, hn, h2⟩
        · intro hzq; subst hzq; exact hgL (honlyq L n cc hrL hn h2).1.symm
    · subst hx
      rw [hN'Q1] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hf1t] at hz
      rcases (hf1 cc z hz).2 with ⟨_, h2⟩ | ⟨hne, h2⟩
      · exact Or.inr (Or.inl h2)
      · exact Or.inl (hqold cc z h2 hne)
    · subst hx
      rw [hN'Q2] at hxn
      cases hxn
      rw [KNode.liveAt_of_times _ c.i hf2t] at hz
      obtain ⟨c0, _, _, h2⟩ := hf2 cc z hz
      rcases h2 with ⟨_, h2⟩ | ⟨hne, h2⟩
      · exact Or.inr (Or.inl h2)
      · exact Or.inl (hqold c0 z h2 hne)
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with ⟨hx, _⟩ | hx | hx | hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hyL
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
    -- an old leaf child of q keeps its node
    have holdq : ∀ c0, (c0, L') ∈ qn.live → c0 ≠ k1 → wNode c.p base w' L' = wNode c.p base w L' := by
      intro c0 h2 hne
      have hk'' : (c0, L') ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact h2
      have hL'L : L' ≠ L := by
        intro he; subst he; exact hne (honlyL q qn c0 hrq hqn hk'').2
      have hL'q : L' ≠ q := by
        intro he; subst he
        exact hI.tree.no_self_link L' c0 (reachS_tReach _ _ _ _ hrq) ⟨qn, hqn, hk''⟩
      have hlt' := hI.links q qn c0 L' hrq hqn hk''
      exact hother L' hL'L hL'q hL'g (by omega) hL'Q1 hL'Q2
    rcases hsub q' hq' with ⟨hq'r, hq'L, hq'q⟩ | hq'yL | hq'Q1 | hq'Q2 | hq'v
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
          rw [hother L' hL'L hL'q hL'g (by omega) hL'Q1 hL'Q2] at hn'
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
      · rw [hother q' hq'L hq'q hq'g (by omega) (by omega) (by omega)] at hq'n
        have hk'' : (k1', L') ∈ q'n.liveAt c.i := by
          rw [KNode.liveAt_of_times q'n c.i (hI.times q' q'n hq'n)]; exact hk'
        have hL'L : L' ≠ L := by
          intro he; subst he; exact hq'q (honlyL q' q'n k1' hq'r hq'n hk'').1
        have hL'q : L' ≠ q := by
          intro he; subst he; exact hq'g (honlyq q' q'n k1' hq'r hq'n hk'').1
        have hlt' := hI.links q' q'n k1' L' hq'r hq'n hk''
        rw [hother L' hL'L hL'q hL'g (by omega) hL'Q1 hL'Q2] at hn'
        exact hI.order q' q'n L' n' k1' hq'r hq'n hq'l hn' hnl' hk'
    · subst hq'yL; rw [hN'yL] at hq'n; cases hq'n; rw [hll] at hq'l; cases hq'l
    · subst hq'Q1
      rw [hN'Q1] at hq'n
      cases hq'n
      obtain ⟨_, h2⟩ := hf1 k1' L' hk'
      rcases h2 with ⟨h1, h2⟩ | ⟨hne, h2⟩
      · subst h1 h2
        rw [hN'yL] at hn'
        cases hn'
        intro c' z hz
        have hb : k1' ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1' < c'' → c' < c'' := by
          rcases hlive c' z hz with ⟨h1, _⟩ | h1
          · subst h1; exact hpar
          · exact hold c' z h1
        refine ⟨hb.1, ?_⟩
        intro c'' z'' hz'' hlt
        rcases (hf1 c'' z'' hz'').2 with ⟨h3, _⟩ | ⟨_, h3⟩
        · omega
        · exact hb.2 c'' z'' h3 hlt
      · rw [holdq k1' h2 hne] at hn'
        have ho := hI.order q qn L' n' k1' hrq hqn hql hn' hnl' h2
        intro c' z hz
        refine ⟨(ho c' z hz).1, ?_⟩
        intro c'' z'' hz'' hlt
        rcases (hf1 c'' z'' hz'').2 with ⟨h3, _⟩ | ⟨_, h3⟩
        · subst h3; exact (ho c' z hz).2 c'' L hk1 hlt
        · exact (ho c' z hz).2 c'' z'' h3 hlt
    · subst hq'Q2
      rw [hN'Q2] at hq'n
      cases hq'n
      obtain ⟨c0, hc0, hk1e, h2⟩ := hf2 k1' L' hk'
      -- the child's bounds, by its compare value c0 in q
      have hchild : (c0 = k1 ∧ L' = yL) ∨ (c0 ≠ k1 ∧ (c0, L') ∈ qn.live) := h2
      have hbound : ∀ c' z, (c', z) ∈ n'.live →
          c0 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → c0 < c'' → c' < c'' := by
        rcases hchild with ⟨h1, h3⟩ | ⟨hne, h3⟩
        · subst h1 h3
          rw [hN'yL] at hn'
          cases hn'
          intro c' z hz
          rcases hlive c' z hz with ⟨h1, _⟩ | h1
          · subst h1; exact hpar
          · exact hold c' z h1
        · rw [holdq c0 h3 hne] at hn'
          exact hI.order q qn L' n' c0 hrq hqn hql hn' hnl' h3
      intro c' z hz
      refine ⟨?_, ?_⟩
      · by_cases h0 : c0 = sc
        · simp only [h0, ↓reduceIte] at hk1e; omega
        · simp only [h0, ↓reduceIte] at hk1e; rw [hk1e]; exact (hbound c' z hz).1
      · intro c'' z'' hz'' hlt
        obtain ⟨c0'', hc0'', hce'', h3⟩ := hf2 c'' z'' hz''
        have hc''pos : c'' = c0'' ∧ c0 < c0'' := by
          by_cases h0'' : c0'' = sc
          · simp only [h0'', ↓reduceIte] at hce''; omega
          · simp only [h0'', ↓reduceIte] at hce''
            refine ⟨hce'', ?_⟩
            by_cases h0 : c0 = sc
            · omega
            · simp only [h0, ↓reduceIte] at hk1e; omega
        rw [hc''pos.1]
        rcases h3 with ⟨h4, _⟩ | ⟨_, h4⟩
        · subst h4; exact (hbound c' z hz).2 c0'' L hk1 hc''pos.2
        · exact (hbound c' z hz).2 c0'' z'' h4 hc''pos.2
    · subst hq'v; rw [hvN'] at hq'n; cases hq'n

theorem divider_pos (l : List (Nat × NodeId)) (hs : CvSorted l) (h2 : 2 ≤ l.length)
    (r : Nat × NodeId) (hr : (l.drop (l.length / 2)).head? = some r) : 0 < r.1 := by
  have hleft := halves_left_lt_divider l (l.length / 2) hs r hr
  cases l with
  | nil => simp at h2
  | cons a rest =>
    have hk : 1 ≤ (a :: rest).length / 2 := by simp at h2 ⊢; omega
    have ha : a ∈ (a :: rest).take ((a :: rest).length / 2) := by
      obtain ⟨k, hk'⟩ : ∃ k, (a :: rest).length / 2 = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
      rw [hk']; simp
    have := hleft a ha
    omega

/-- A put into a full leaf that existed before the transaction, time split,
whose inner parent, full by its size and existing before the transaction, with
more than h klongs in its last version and at least two live, is space split,
below a grandparent with room for two klongs, keeps `PutInv` (the writer's tree
after it given; the rule of `writerWP_put_timeSpace`, with its premise on the
range of q's compare values in g). -/
theorem putInv_put_timeSpace (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : c.p.M < qn.size + 1 + 1 ∧ qn.firstTime ≠ some c.i ∧
      c.p.splitAbove < (qn.lastVersion c.i).size ∧ 2 ≤ qn.live.length)
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  obtain ⟨hfull, hfirst, hsplit⟩ := hleaf
  obtain ⟨hqfull, hqfirst, hqsplit, hq2⟩ := hparent
  obtain ⟨hroomg, hdeadg⟩ := hgp
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  apply writerWP_put_seg_append2 c base hB.coherent pre cv h rk w S0 kq k1 q L n qn gn hrk ht
    hI.ids.1 hI.ids.2.1 hpath hNL hnl hNq hNg hfull
  intro d'' w4 hqv hgv hvisL hql hgl hk1 hkq hqL hgq hgL h4t h4top h4next hlk4 hlq4 hlg4 hsrc4 hW4
    hpg hpq hpk
  generalize hgdef : pathEnd rk S0 = g at *
  have hLn := hI.lt_next L n hNL
  have hfree : ∀ z, w4.next ≤ z → w4.nodes.lookup z = none := by
    intro z hz
    cases h' : w4.nodes.lookup z with
    | none => rfl
    | some _ => have := hsrc4 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_timeSpace d'' L q g n qn gn kq k1 cv w.next c w4
    hlk4 hlq4 hlg4 hqL hgq hgL hql hgl hfirst hqfirst hfull hsplit hqfull hqsplit hpg hpq hpk hroomg
    hdeadg (hfree _ (Nat.le_refl _)) (hfree _ (by omega)) (hfree _ (by omega)) (by omega)) ?_
  intro _ w' ⟨l, hll, _, hlt, hlk, h't, h'top, _, h'nodes⟩
  have hqlive : qn.live ≠ [] := by intro he; rw [he] at hq2; simp at hq2
  obtain ⟨r0, hr0⟩ := live_ne_nil_head qn hqlive
  have hsc0 := divider_pos qn.live (KNode.live_order qn) hq2 r0 hr0
  rw [h4next] at h'nodes
  obtain ⟨hsc, hf1, hf2⟩ := halves_inner_live qn c.i k1 (w.next + 2) hql r0 hr0 hsc0
  have hfl := halves_leaf_flags qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next + 2)]
  have hht := halves_times qn.leaf qn c.i [(k1, w.next + 2)]
  generalize hout : halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next + 2)] = out at *
  rw [hql] at hfl
  have htk : w'.taken = w.taken := h't.trans h4t
  have hgt : w.taken.contains g = false := (wNode_cases _ _ _ _ _ hNg).1
  have hyLt : w.taken.contains (w.next + 2) = false := hI.untaken_of_ge _ (by omega)
  have hQ1t : w.taken.contains (w.next + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hQ2t : w.taken.contains (w.next + 2 + 2 + 2) = false := hI.untaken_of_ge _ (by omega)
  have hl_eq : (⟨n.leaf, l.ks⟩ : KNode) = l := by
    cases l with
    | mk lf ks => simp only at hll; rw [hll]
  have hqn' := hI.lt_next q qn hNq
  have hgn' := hI.lt_next g gn hNg
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hNq)]; exact hk1
  have hkql : (kq, q) ∈ gn.live := by
    rw [← KNode.liveAt_of_times gn c.i (hI.times g gn hNg)]; exact hkq
  have e1 : w.next + 2 ≠ L := by omega
  have e2 : w.next + 2 ≠ q := by omega
  have e3 : w.next + 2 ≠ g := by omega
  have e4 : w.next + 2 + 2 ≠ L := by omega
  have e5 : w.next + 2 + 2 ≠ q := by omega
  have e6 : w.next + 2 + 2 ≠ g := by omega
  have e7 : w.next + 2 + 2 ≠ w.next + 2 := by omega
  have e8 : w.next + 2 + 2 + 2 ≠ L := by omega
  have e9 : w.next + 2 + 2 + 2 ≠ q := by omega
  have e10 : w.next + 2 + 2 + 2 ≠ g := by omega
  have e11 : w.next + 2 + 2 + 2 ≠ w.next + 2 := by omega
  have e12 : w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 := by omega
  rw [hsc] at h'nodes
  refine putInvT_timeSpace c base w w' hI cv r0.1 k1 kq w.next (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) L q g n qn gn l out.1 out.2.1 (Nat.le_refl _) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hNL hnl hNq hql
    hNg hgl hrg hkql hk1l hrangeq (divider_mem qn r0 hr0) htk (h'top.trans h4top) ?_ ?_
    (by rw [hll]; exact hnl) hlt (live_of_lookup l n cv w.next hlk) ?_ hfl.1
    hht.1 hf1 ?_ hfl.2 hht.2 hf2 ?_
    (parentBound_gen c base w hI pre cv rk L hrk hvisL q qn k1 hrq hNq hql hk1l)
  · simp only [wNode, htk, hgt, Bool.false_eq_true, ↓reduceIte, h'nodes, hgL, hgq]
  · simp only [wNode, htk, hyLt, Bool.false_eq_true, ↓reduceIte, h'nodes, e1, e2, e3, hl_eq]
  · simp only [wNode, htk, hQ1t, Bool.false_eq_true, ↓reduceIte, h'nodes, e4, e5, e6, e7]
  · simp only [wNode, htk, hQ2t, Bool.false_eq_true, ↓reduceIte, h'nodes, e8, e9, e10, e11, e12]
  · intro x hxL hxq hxg hxyL hxQ1 hxQ2
    rw [← hW4]
    simp only [wNode, htk, h4t, h'nodes, hxL, hxq, hxg, hxyL, hxQ1, hxQ2, ↓reduceIte]

end SIS.Tree
