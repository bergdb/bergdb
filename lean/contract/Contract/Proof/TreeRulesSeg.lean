/-
The contract package (bergdb 030-10): the space split of the root of a
segment tree, as a statement about two trees (`space-split-2`): the node x,
the root of the tree of the next segment below the long klong k1 of the
segment leaf q, is replaced by two nodes with the halves of its live klongs
and a new root r' that names them; q's klong names r'.
-/
import Contract.Proof.TreeRules

namespace Contract

theorem Sound.spaceSplitSeg {M : Nat} {ex' : Option NodeId} {A B : Tree}
    {r q x first second r' : NodeId} {C : List (Key × Nat)} {nq nx : KNode} {k1 sc : Nat}
    {y0 : NodeId} {l1 rest : List (Nat × NodeId)}
    (h : Sound M (some x) A r C) (hq : q ∈ reachAt A (A.fuel r) r)
    (hAq : A.obj q = some (.key nq)) (hql : nq.leaf = true) (hk1 : (k1, x) ∈ live nq.ks)
    (hAx : A.obj x = some (.key nx)) (hsplit : live nx.ks = l1 ++ (sc, y0) :: rest)
    (hl1 : l1 ≠ []) (hfirst : first = x ∨ A.obj first = none) (hsecond : A.obj second = none)
    (hne : first ≠ second) (hr' : A.obj r' = none) (hne' : r' ≠ first ∧ r' ≠ second)
    (hlev : nx.level + 1 < nq.level) (hBf : NodeIs B first nx.level nx.leaf l1 M)
    (hBs : NodeIs B second nx.level nx.leaf
      (if nx.leaf then (sc, y0) :: rest else (0, y0) :: rest) M)
    (hBr : NodeIs B r' (nx.level + 1) false [(0, first), (sc, second)] M)
    (hBq : NodeIs B q nq.level true (insertCv k1 r' (live nq.ks)) (bnd M ex' q))
    (hBx : (B.obj x).isSome = true)
    (hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ r' → z ≠ q → B.obj z = A.obj z) :
    Sound M ex' B r C ∧ (first ≠ x → x ∉ reachAt B (B.fuel r) r) ∧
      ∀ z ∈ reachAt B (B.fuel r) r,
        z ∈ reachAt A (A.fuel r) r ∨ z = first ∨ z = second ∨ z = r' := by
  obtain ⟨nqb, hq1, hq2, hq3, hq4, hq5⟩ := hBq
  obtain ⟨nf, hf1, hf2, hf3, hf4, hf5⟩ := id hBf
  obtain ⟨ns, hs1, hs2, hs3, hs4, hs5⟩ := id hBs
  obtain ⟨nr, hr1, hr2, hr3, hr4, hr5⟩ := hBr
  have hG := h.good
  obtain ⟨loq, hiq, hgq⟩ := hG.tr_reach_good _ q hq nq hAq
  have hTq := hG.tr_nodup h.tree hq
  have hnotA : ∀ z, A.obj z = none → z ∉ reachAt A (A.fuel r) r := by
    intro z hz hm
    have := hG.tr_exists _ z hm
    simp [hz] at this
  have hsA := hnotA second hsecond
  have hr'A := hnotA r' hr'
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, _, _⟩ := live_split he
  have hlong : isLong k1 = true := by
    rcases hgq.kind hAq hk1 with ⟨_, _, v, hv⟩ | ⟨hk', _⟩
    · rw [hAx] at hv
      cases hv
    · exact hk' hql
  have hqx : q ≠ x := by
    intro e
    have h1 : A.obj q = some (.key nx) := e ▸ hAx
    rw [hAq] at h1
    cases h1
    omega
  have hfq : A.fuel q = nq.level + 1 := by simp [Tree.fuel, hAq]
  have hxq : x ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hk1 (tc_self _ _ _)
  have hxr : x ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hxq
  have hqnx : ∀ f, q ∉ reachAt A f x := fun f => hgq.tc_no_cycle hxq (Ne.symm hqx) f
  have hqA : ∀ z, z ∈ reachAt A (A.fuel q) q → z ∈ reachAt A (A.fuel r) r :=
    fun z hz => hG.tr_closed hq hz
  have hgx0 : Good A x 0 none := hgq.tr_seg hAq hql hk1 hlong
  have hax : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z := by
    intro z hz hzx
    have hzr := hG.tr_closed hxr hz
    refine hsame z hzx (fun e => ?_) (fun e => hsA (e ▸ hzr)) (fun e => hr'A (e ▸ hzr))
      (fun e => hqnx _ (e ▸ hz))
    rcases hfirst with e' | e'
    · exact hzx (e.trans e')
    · exact hnotA first e' (e ▸ hzr)
  have hmpp : ∀ a ∈ pre ++ post, a ∈ live nq.ks := by
    intro a h'
    rw [he]
    rcases List.mem_append.mp h' with h' | h' <;> simp [h']
  have hside : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A nq.level z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    obtain ⟨h1, h2, h3⟩ := hgq.tr_side hAq hTq he hb hz'
    have hz'x : z' ≠ x := fun e => h2 (e ▸ tc_self _ _ _)
    refine hsame z' hz'x (fun e => ?_) (fun e => ?_) (fun e => ?_) h1
    · rcases hfirst with e' | e'
      · exact hz'x (e.trans e')
      · rw [e, e'] at h3
        cases h3
    · rw [e, hsecond] at h3
      cases h3
    · rw [e, hr'] at h3
      cases h3
  have hside' : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A (A.fuel z) z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    rw [← hgq.tc_kid_eq hAq (hmpp _ hb)] at hz'
    exact hside c' z hb z' hz'
  obtain ⟨hGf, hGs, hLfs, hRf, hRs⟩ := tr_split hgx0 hAx hsplit hBf hBs hax
  have hwfr : klongsWf nr.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hr5
    exact hr5.1.2
  have hGr : Good B r' 0 none := by
    refine tr_good_of hr1 hwfr ?_
    rw [hr4, hr2, hr3]
    intro t ht
    simp only [bounds, nextHi, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨rfl, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
      exact ⟨nf, hf1, by omega, by rw [hf4]; exact hl1, by simpa using hGf⟩
    · refine ⟨rfl, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
      exact ⟨ns, hs1, by omega, by rw [hs4]; split <;> simp, by simpa using hGs⟩
  have hlvB : live nqb.ks = pre ++ (k1, r') :: post := by
    rw [hq4, he]
    exact tr_insertCv_replace post hpre
  have hwf : klongsWf nqb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hq5
    exact hq5.1.2
  have hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi' := by
    intro lo' hi' hg
    have hA := hg.tr_kids hAq
    rw [he, bounds_append, hql] at hA
    refine tr_good_of hq1 hwf ?_
    rw [hlvB, hq2, hq3, bounds_append]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hA' := hA t (List.mem_append_left _ ht)
      exact hA'.tr_move (hside' _ _ (List.mem_append_left _ (bounds_mem_live ht))) hA'.1
        (fun hl => ⟨rfl, hA'.2.1 hl⟩) (fun h' => (by cases h'))
    · simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | ht
      · obtain ⟨a1, a2, _, _⟩ := hA _ (List.mem_append_right _ List.mem_cons_self)
        refine ⟨a1, a2, fun _ hs => ?_, fun _ => ?_⟩
        · rw [hlong] at hs
          cases hs
        · exact ⟨nr, hr1, by omega, by rw [hr4]; simp, by simpa using hGr⟩
      · have hA' := hA t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
        exact hA'.tr_move (hside' _ _ (List.mem_append_right _ (bounds_mem_live ht))) hA'.1
          (fun hl => ⟨rfl, hA'.2.1 hl⟩) (fun h' => (by cases h'))
  have hgqB := hloc loq hiq hgq
  have hLr : L B r' = L A x := by
    rw [hGr.L_eq hr1, hr4, hr3]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, klongList,
      Bool.false_eq_true, ite_false]
    exact hLfs
  have hL : L B q = L A q := by
    rw [hgqB.L_eq hq1, hgq.L_eq hAq, hlvB, he, hq3, hql]
    have hE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ pre ++ post) →
        l.flatMap (fun cy => klongList B true (L B) cy.1 cy.2) =
          l.flatMap (fun cy => klongList A true (L A) cy.1 cy.2) := by
      intro l hl
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hside c z (hl _ hm) z (tc_self _ _ _))
        (L_agree (hside' c z (hl _ hm)))
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hE pre (fun a h' => List.mem_append_left _ h'),
      hE post (fun a h' => List.mem_append_right _ h'),
      tr_klongList_long (fun _ => hlong) hLr]
  have hRE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ pre ++ post) →
      l.flatMap (fun cy => reachAt B nq.level cy.2) =
        l.flatMap (fun cy => reachAt A nq.level cy.2) := by
    intro l hl
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact reachAt_agree _ _ (hside c z (hl _ hm))
  have hRf' : reachAt B (nx.level + 1) first =
      first :: l1.flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [← hRf, show B.fuel first = nx.level + 1 by simp [Tree.fuel, hf1, hf2]]
  have hRs' : reachAt B (nx.level + 1) second =
      second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [← hRs, show B.fuel second = nx.level + 1 by simp [Tree.fuel, hs1, hs2]]
  have hRr : reachAt B nq.level r' =
      r' :: ((first :: l1.flatMap (fun cy => reachAt A nx.level cy.2)) ++
        (second :: ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2))) := by
    rw [hGr.reachAt_eq nq.level (by simp [Tree.fuel, hr1, hr2]; omega),
      show B.fuel r' = nx.level + 1 + 1 by simp [Tree.fuel, hr1, hr2], tc_key hr1, hr4]
    simp [hRf', hRs']
  have hxA : reachAt A nq.level x = x :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
      ((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2)) := by
    rw [hgq.tc_kid_eq hAq hk1, show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx,
      hsplit, List.flatMap_append]
  have hRqA : reachAt A (A.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      x :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        (((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [hfq, tc_key hAq, he, List.flatMap_append, List.flatMap_cons, hxA]
    simp
  have hRqB : reachAt B (B.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      r' :: first :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        second :: (((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [show B.fuel q = nq.level + 1 by simp [Tree.fuel, hq1, hq2], tc_key hq1, hlvB,
      List.flatMap_append, List.flatMap_cons, hRr,
      hRE pre (fun a h' => List.mem_append_left _ h'),
      hRE post (fun a h' => List.mem_append_right _ h')]
    simp
  have hTq' := hTq
  rw [hRqA] at hTq'
  have hA1 : ((q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      first :: (l1.flatMap (fun cy => reachAt A nx.level cy.2) ++
        (((sc, y0) :: rest).flatMap (fun cy => reachAt A nx.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2)))).Nodup := by
    rcases hfirst with e | e
    · rw [e]
      exact hTq'
    · refine tr_nodup_replace hTq' (fun hm => hnotA first e (hqA first ?_))
      rw [hRqA]
      exact tr_mem_mid hm
  have hA2 := tr_nodup_insert2 (b := second) hA1 (fun hm => by
    rcases tr_mem_swap (a := x) hm with e | e
    · exact hne e.symm
    · exact hsA (hqA _ (by rw [hRqA]; exact e)))
  have hR : (reachAt B (B.fuel q) q).Nodup := by
    rw [hRqB, List.nodup_middle, List.nodup_cons]
    refine ⟨fun hm => ?_, hA2⟩
    rcases tr_mem_two hm with e | e | e
    · exact hne'.1 e
    · exact hne'.2 e
    · exact hr'A (hqA _ (by rw [hRqA]; exact tr_mem_mid e))
  have hmemq : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z = first ∨ z = second ∨ z = r' := by
    intro z hz
    rw [hRqB] at hz
    rcases List.mem_append.mp hz with h1 | h1
    · left
      rw [hRqA]
      exact List.mem_append_left _ h1
    rcases List.mem_cons.mp h1 with h1 | h1
    · exact Or.inr (Or.inr (Or.inr h1))
    rcases tr_mem_two (P := []) (List.mem_append_right [] h1) with e | e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · left
      rw [hRqA]
      exact tr_mem_mid (List.mem_append_right _ (by simpa using e))
  have hnew : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hmemq z hz with h' | rfl | rfl | rfl
    · exact Or.inl h'
    · rcases hfirst with e | e
      · rw [e]
        exact Or.inl hxq
      · exact Or.inr (hnotA _ e)
    · exact Or.inr hsA
    · exact Or.inr hr'A
  have ha : Agree A B r q := by
    intro z hz hzq
    have hzx : z ≠ x := fun e => hzq (e ▸ hxq)
    refine hsame z hzx (fun e => ?_) (fun e => hsA (e ▸ hz)) (fun e => hr'A (e ▸ hz))
      (fun e => hzq (e ▸ tc_self _ _ _))
    rcases hfirst with e' | e'
    · exact hzx (e.trans e')
    · exact hnotA first e' (e ▸ hz)
  have hk : KeepsKind A B q := by
    intro n hn
    rw [hAq] at hn
    cases hn
    exact ⟨nqb, hq1, by omega, fun _ => by rw [hlvB]; simp⟩
  have hqk : ∃ n, A.obj q = some (.key n) := ⟨nq, hAq⟩
  obtain ⟨hTB, hmemB⟩ := ctx_reach hG h.tree hq ha hk hloc hqk hR hnew
  have hxB : first ≠ x → x ∉ reachAt B (B.fuel r) r := by
    intro hfx hx
    rcases hmemB x hx with ⟨_, h2⟩ | h2
    · exact h2 hxq
    · rcases hmemq x h2 with h3 | h3 | h3 | h3
      · have hT2 := hTq'
        rw [List.nodup_middle, List.nodup_cons] at hT2
        rw [hRqB] at h2
        rcases List.mem_append.mp h2 with h4 | h4
        · exact hT2.1 (List.mem_append_left _ h4)
        rcases List.mem_cons.mp h4 with h4 | h4
        · exact tr_ne_of_obj hAx hr' h4
        rcases tr_mem_two (P := []) (List.mem_append_right [] h4) with e | e | e
        · exact hfx e.symm
        · exact tr_ne_of_obj hAx hsecond e
        · exact hT2.1 (List.mem_append_right _ (by simpa using e))
      · exact hfx h3.symm
      · exact tr_ne_of_obj hAx hsecond h3
      · exact tr_ne_of_obj hAx hr' h3
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r,
      z ∈ reachAt A (A.fuel r) r ∨ z = first ∨ z = second ∨ z = r' := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hmemq z h1 with h2 | h2 | h2 | h2
      · exact Or.inl (hqA z h2)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h2))
  have hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true := by
    intro w hw
    by_cases hwx : w = x
    · rw [hwx]
      exact hBx
    by_cases hwf : w = first
    · simp [hwf, hf1]
    by_cases hws : w = second
    · rw [hws, hsecond] at hw
      cases hw
    by_cases hwr : w = r'
    · rw [hwr, hr'] at hw
      cases hw
    by_cases hwq : w = q
    · simp [hwq, hq1]
    rw [hsame w hwx hwf hws hwr hwq]
    exact hw
  refine ⟨⟨?_, Good.ctx hG h.tree hq ha hk hloc hqk, ?_, ?_, hTB⟩, hxB, hmem⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    by_cases hrq : r = q
    · rw [hrq]
      exact ⟨nqb, hq1, Or.inl hq3⟩
    · have hrx : r ≠ x := fun e => hqnx _ (e ▸ hq)
      have hrf : r ≠ first := by
        intro e
        rcases hfirst with e' | e'
        · exact hrx (e.trans e')
        · exact tr_ne_of_obj ho e' e
      exact ⟨n, (hsame r hrx hrf (tr_ne_of_obj ho hsecond) (tr_ne_of_obj ho hr') hrq).trans ho,
        hne⟩
  · intro z hz m hm
    by_cases hzq : z = q
    · rw [hzq, hq1] at hm
      cases hm
      rw [hzq]
      exact hq5
    by_cases hzf : z = first
    · rw [hzf, hf1] at hm
      cases hm
      exact tr_nodeOk hf5 (by split <;> omega) (fun _ h' => h')
    by_cases hzs : z = second
    · rw [hzs, hs1] at hm
      cases hm
      exact tr_nodeOk hs5 (by split <;> omega) (fun _ h' => h')
    by_cases hzr : z = r'
    · rw [hzr, hr1] at hm
      cases hm
      exact tr_nodeOk hr5 (by split <;> omega) (fun _ h' => h')
    have hzx : z ≠ x := by
      intro e
      rcases hfirst with e' | e'
      · exact hzf (e.trans e'.symm)
      · have hfx : first ≠ x := fun e'' => tr_ne_of_obj hAx e' e''.symm
        exact hxB hfx (e ▸ hz)
    have hzA : z ∈ reachAt A (A.fuel r) r := by
      rcases hmem z hz with h' | h' | h' | h'
      · exact h'
      · exact absurd h' hzf
      · exact absurd h' hzs
      · exact absurd h' hzr
    exact h.tr_old hs hzA (fun e => hzx (Option.some.inj e).symm)
      (hsame z hzx hzf hzs hzr hzq) hm (by split <;> omega)
  · rw [ctx_L hG h.tree hq ha hk hloc hqk hL]
    exact h.holds

end Contract
