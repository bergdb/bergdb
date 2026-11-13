/-
The live klongs of the halves of an inner node's last version with a klong
(k1, Y) put in the place of its live klong of k1 (bergdb 024-22, `OpTreeOK`;
the inner space split of a cascade): `halves_inner_ins_live`.
-/
import SIS.Tree.WriterTreeCascadePut
import SIS.Tree.GetInnerSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem pairLookupFold_append_single (c : Nat) (A : List (Nat × NodeId)) (a : Nat) (y : NodeId) :
    (A ++ [(a, y)]).foldl (pairLookupStep c) none =
      if a == c then some y else A.foldl (pairLookupStep c) none := by
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]

/-- A live klong of a node of klongs `newKlongs t l` is the last of its compare
value in l. -/
theorem newKlongs_liveAt_fold (b : Bool) (t : Time) (l : List (Nat × NodeId)) (c : Nat) (z : NodeId)
    (h : (c, z) ∈ (⟨b, newKlongs t l⟩ : KNode).liveAt t) : l.foldl (pairLookupStep c) none = some z := by
  rw [KNode.liveAt_of_times _ t (newKlongs_times t l)] at h
  rw [← KNode.newKlongs_live_lookup_fold b t l c]
  exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h

theorem halves_inner_ins_live (qn : KNode) (t : Time) (k1 : Nat) (Y : NodeId) (hql : qn.leaf = false)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) :
    let out := halves false t (qn.lastVersion t) [(k1, Y)]
    out.2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ out.1.liveAt t →
      (c = k1 ∧ z = Y ∧ k1 < r.1) ∨ ((c, z) ∈ qn.live ∧ c < r.1 ∧ c ≠ k1)) ∧
    (∀ c z, (c, z) ∈ out.2.1.liveAt t →
      (c = splitLocalCv false r.1 k1 ∧ z = Y ∧ r.1 ≤ k1) ∨
      (∃ c0, (c0, z) ∈ qn.live ∧ r.1 ≤ c0 ∧ c0 ≠ k1 ∧ c = splitLocalCv false r.1 c0)) := by
  intro out
  have hlv := KNode.lastVersion_eq_newKlongs qn t
  rw [hql] at hlv
  have hout : out = halves false t ⟨false, newKlongs t qn.live⟩ [(k1, Y)] := by
    show halves false t (qn.lastVersion t) [(k1, Y)] = _
    rw [hlv]
  have hshape := halves_shape false t qn.live [(k1, Y)] r hr
  simp only [List.head?_cons] at hshape
  rw [hshape] at hout
  have hs := qn.live_order
  have hlt := halves_left_lt_divider qn.live (qn.live.length / 2) hs r hr
  obtain ⟨rest, hdrop⟩ : ∃ rest, qn.live.drop (qn.live.length / 2) = r :: rest := by
    cases he : qn.live.drop (qn.live.length / 2) with
    | nil => rw [he] at hr; cases hr
    | cons a rest =>
      rw [he] at hr; simp only [List.head?_cons, Option.some.injEq] at hr
      subst hr; exact ⟨rest, rfl⟩
  have hrmem : r ∈ qn.live := List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_self)
  have hrestmem : ∀ q ∈ rest, q ∈ qn.live := fun q hq =>
    List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_of_mem _ hq)
  have hrestgt : ∀ q ∈ rest, r.1 < q.1 := by
    have hd : (qn.live.drop (qn.live.length / 2)).Pairwise (fun a b => a.1 < b.1) :=
      hs.sublist (List.drop_sublist _ _)
    rw [hdrop] at hd
    exact (List.pairwise_cons.mp hd).1
  have hsec : secondSplitPairs false qn.live = (0, r.2) :: rest := by
    simp only [secondSplitPairs, Bool.false_eq_true, ↓reduceIte, hdrop, renameHead]
  have hsecmem : ∀ c z, (c, z) ∈ secondSplitPairs false qn.live →
      ∃ c0, (c0, z) ∈ qn.live ∧ r.1 ≤ c0 ∧ c = splitLocalCv false r.1 c0 := by
    intro c z hm
    rw [hsec] at hm
    rcases List.mem_cons.mp hm with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r.1, hrmem, Nat.le_refl _, by simp [splitLocalCv]⟩
    · have hg := hrestgt (c, z) h
      refine ⟨c, hrestmem _ h, by simp at hg; omega, ?_⟩
      have : (c == r.1) = false := by simp at hg; simpa using (by omega : c ≠ r.1)
      simp [splitLocalCv, this]
  by_cases hside : r.1 ≤ k1
  · have hd : decide (r.1 ≤ k1) = true := by simpa using hside
    simp only [hd, ↓reduceIte] at hout
    rw [hout]
    refine ⟨rfl, ?_, ?_⟩
    · intro c z h
      have hf := newKlongs_liveAt_fold false t _ c z h
      rcases pairLookupFold_some_mem c _ none z hf with hm | hm
      · have hc := hlt (c, z) hm
        exact Or.inr ⟨List.mem_of_mem_take hm, hc, by simp at hc; omega⟩
      · cases hm
    · intro c z h
      have hf := newKlongs_liveAt_fold false t _ c z h
      simp only [List.map_cons, List.map_nil] at hf
      rw [pairLookupFold_append_single] at hf
      by_cases hk : (splitLocalCv false r.1 k1 == c) = true
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hf
        exact Or.inl ⟨(beq_iff_eq.mp hk).symm, hf.symm, hside⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hf
        rcases pairLookupFold_some_mem c _ none z hf with hm | hm
        · obtain ⟨c0, hc0, hge, hcc⟩ := hsecmem c z hm
          refine Or.inr ⟨c0, hc0, hge, fun h0 => ?_, hcc⟩
          subst h0
          exact hk (by rw [hcc]; simp)
        · cases hm
  · have hd : decide (r.1 ≤ k1) = false := by simpa using hside
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hout
    rw [hout]
    refine ⟨rfl, ?_, ?_⟩
    · intro c z h
      have hf := newKlongs_liveAt_fold false t _ c z h
      rw [pairLookupFold_append_single] at hf
      by_cases hk : (k1 == c) = true
      · simp only [hk, ↓reduceIte, Option.some.injEq] at hf
        exact Or.inl ⟨(beq_iff_eq.mp hk).symm, hf.symm, by omega⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hf
        rcases pairLookupFold_some_mem c _ none z hf with hm | hm
        · exact Or.inr ⟨List.mem_of_mem_take hm, hlt (c, z) hm, fun h0 => hk (by rw [h0]; simp)⟩
        · cases hm
    · intro c z h
      have hf := newKlongs_liveAt_fold false t _ c z h
      rcases pairLookupFold_some_mem c _ none z hf with hm | hm
      · obtain ⟨c0, hc0, hge, hcc⟩ := hsecmem c z hm
        exact Or.inr ⟨c0, hc0, hge, by omega, hcc⟩
      · cases hm

/-- The tree after a time split of the leaf L under q and a space split of q
(its last version with k1 naming y1) under g: y1 L's last version with the
put's (cv, v), halves y2 and y3 of q, g's klong kq names y2 and a new klong at
the halves' divider names y3; L and q are left behind. -/
theorem treeOK_timeSpace (N N' : NodeId → Option KNode) (t : Time) (r g q L y1 y2 y3 v : NodeId)
    (gn qn n l : KNode) (kq k1 cv : Nat) (r0 : Nat × NodeId)
    (hT : TreeOK N t r) (hg : TReach N t r g) (hgn : N g = some gn)
    (hgk : (kq, q) ∈ gn.liveAt t) (hgwf : klongsWf gn.ks = true)
    (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ t)
    (hqn : N q = some qn) (hql : qn.leaf = false) (hqk : (k1, L) ∈ qn.liveAt t)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hr0 : (qn.live.drop (qn.live.length / 2)).head? = some r0)
    (hLn : N L = some n) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hl_times : ∀ s, Klong.time s ∈ l.ks → s ≤ t)
    (hl_look : ∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q')
    (hN'g : N' g = some ((gn.add t (.key kq y2)).add t
      (.key (halves false t (qn.lastVersion t) [(k1, y1)]).2.2 y3)))
    (hN'1 : N' y1 = some ⟨n.leaf, l.ks⟩)
    (hN'2 : N' y2 = some (halves false t (qn.lastVersion t) [(k1, y1)]).1)
    (hN'3 : N' y3 = some (halves false t (qn.lastVersion t) [(k1, y1)]).2.1)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ g → z ≠ y1 → z ≠ y2 → z ≠ y3 → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (hf3 : N y3 = none) (hvN : N v = none)
    (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3) (hv1 : v ≠ y1) (hv2 : v ≠ y2) (hv3 : v ≠ y3)
    (hfresh : ∀ z, (z = y1 ∨ z = y2 ∨ z = y3 ∨ z = v) →
      ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  obtain ⟨hsc, hfirst, hsecond⟩ := halves_inner_ins_live qn t k1 y1 hql r0 hr0
  generalize hout : halves false t (qn.lastVersion t) [(k1, y1)] = out at *
  rw [hsc] at hN'g
  have hqlive : qn.liveAt t = qn.live := KNode.liveAt_of_times qn t hqt
  have hne : ∀ z m, N z = some m → ∀ y, N y = none → z ≠ y := fun z m hz y hy he => by
    rw [he, hy] at hz; cases hz
  have hgq_link : TLink N t g kq q := ⟨gn, hgn, hgk⟩
  have hq : TReach N t r q := TReach.link hg hgq_link
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hgq : g ≠ q := fun h => hT.no_self_link g kq hg (by rw [← h] at hgq_link; exact hgq_link)
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hgL : g ≠ L := fun h => hT.no_two_cycle g q kq k1 hgq_link (by rw [h]; exact hqL_link) hg
  have hqpar : ∀ u c', TReach N t r u → TLink N t u c' q → u = g ∧ c' = kq :=
    fun u c' hu hl => hT.oneLink u c' g kq q hu hg hl hgq_link
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hQlink : ∀ c' z, (c', z) ∈ qn.live → TLink N t q c' z := fun c' z h =>
    ⟨qn, hqn, by rw [hqlive]; exact h⟩
  have hvN' : N' v = none := by
    rw [hother v (Ne.symm (hne L n hLn v hvN)) (Ne.symm (hne q qn hqn v hvN))
      (Ne.symm (hne g gn hgn v hvN)) hv1 hv2 hv3]; exact hvN
  have hnotR : ∀ z, (z = y1 ∨ z = y2 ∨ z = y3 ∨ z = v) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h | h | h <;> rw [h]
    · exact not_reach_fresh N t r y1 hT hf1 (hfresh y1 (Or.inl rfl))
    · exact not_reach_fresh N t r y2 hT hf2 (hfresh y2 (Or.inr (Or.inl rfl)))
    · exact not_reach_fresh N t r y3 hT hf3 (hfresh y3 (Or.inr (Or.inr (Or.inl rfl))))
    · exact not_reach_fresh N t r v hT hvN (hfresh v (Or.inr (Or.inr (Or.inr rfl))))
  have h1l : ∀ c' z, TLink N' t y1 c' z → (c' = cv ∧ z = v) ∨ ((c', z) ∈ n.liveAt t ∧ c' ≠ cv) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'1] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact liveAt_of_lookup_update _ n t cv v hl_times hnt hl_look c' z hc
  have h2l : ∀ c' z, TLink N' t y2 c' z →
      (c' = k1 ∧ z = y1 ∧ k1 < r0.1) ∨ ((c', z) ∈ qn.live ∧ c' < r0.1 ∧ c' ≠ k1) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'2] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hfirst c' z hc
  have h3l : ∀ c' z, TLink N' t y3 c' z →
      (c' = splitLocalCv false r0.1 k1 ∧ z = y1 ∧ r0.1 ≤ k1) ∨
      (∃ c0, (c0, z) ∈ qn.live ∧ r0.1 ≤ c0 ∧ c0 ≠ k1 ∧ c' = splitLocalCv false r0.1 c0) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'3] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hsecond c' z hc
  have hgl : ∀ c' z, TLink N' t g c' z → (c' = r0.1 ∧ z = y3) ∨ (c' ≠ r0.1 ∧ c' = kq ∧ z = y2) ∨
      (c' ≠ r0.1 ∧ c' ≠ kq ∧ (c', z) ∈ gn.liveAt t) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'g] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have hw1 := KNode.add_key_wf gn t kq y2 hgwf
    have ht1 := KNode.add_times gn t (.key kq y2) (fun s h => by cases h) hgt
    rcases KNode.add_key_liveAt_mem _ t r0.1 y3 hw1 ht1 c' z hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · rcases KNode.add_key_liveAt_mem gn t kq y2 hgwf hgt c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
      · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
  have hvl : ∀ c' z, ¬ TLink N' t v c' z := by
    intro c' z hl
    obtain ⟨m, hm, _⟩ := hl
    rw [hvN'] at hm; cases hm
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ g → u ≠ y1 → u ≠ y2 → u ≠ y3 → ∀ c' z,
      TLink N' t u c' z → TLink N t u c' z := by
    intro u h1 h2 h3 h4 h5 h6 c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hother u h1 h2 h3 h4 h5 h6] at hm
    exact ⟨m, hm, hc⟩
  have hReachOr : ∀ u, (TReach N t r u ∨ (u = y1 ∨ u = y2 ∨ u = y3 ∨ u = v)) → u ≠ y1 → u ≠ y2 →
      u ≠ y3 → u ≠ v → TReach N t r u := by
    intro u hu h1 h2 h3 h4
    rcases hu with h | h
    · exact h
    · rcases h with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact absurd h h4
  have hnotGone : ∀ u c' z, TReach N t r u → TLink N t u c' z → (u ≠ q ∨ c' ≠ k1) →
      (u ≠ g ∨ c' ≠ kq) → ¬ (z = L ∨ z = q) := by
    intro u c' z hu hl h1 h2 hz
    rcases hz with hz | hz
    · rw [hz] at hl
      obtain ⟨a, b⟩ := hLpar u c' hu hl
      rcases h1 with h1 | h1
      · exact h1 a
      · exact h1 b
    · rw [hz] at hl
      obtain ⟨a, b⟩ := hqpar u c' hu hl
      rcases h2 with h2 | h2
      · exact h2 a
      · exact h2 b
  apply treeOK_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2 ∨ z = y3 ∨ z = v)
    (fun z => z = L ∨ z = q)
    (fun u c' => if u = L then (y1, c')
      else if u = q then (if c' < r0.1 then (y2, c') else (y3, splitLocalCv false r0.1 c'))
      else (u, c')) hT hnotR
  · refine Or.inl ⟨rfl, ?_⟩
    rintro (h | h)
    · exact hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
    · exact hT.rootFree g kq hg (by rw [h]; exact hgq_link)
  · intro u c' z hu hug hl
    have huL : u ≠ L := fun h => hug (Or.inl h)
    have huq : u ≠ q := fun h => hug (Or.inr h)
    by_cases hu1 : u = y1
    · rw [hu1] at hl
      rcases h1l c' z hl with ⟨_, h⟩ | ⟨hmem, _⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
      · have hl0 : TLink N t L c' z := ⟨n, hLn, hmem⟩
        exact Or.inr ⟨hnotGone L c' z hL hl0 (Or.inl (Ne.symm hqL)) (Or.inl (Ne.symm hgL)),
          L, c', hL, hl0, by simp [hu1]⟩
    · by_cases hu2 : u = y2
      · rw [hu2] at hl
        rcases h2l c' z hl with ⟨_, h, _⟩ | ⟨hmem, hlt, hck⟩
        · exact Or.inl (Or.inl h)
        · have hl0 := hQlink c' z hmem
          exact Or.inr ⟨hnotGone q c' z hq hl0 (Or.inr hck) (Or.inl (Ne.symm hgq)),
            q, c', hq, hl0, by simp [hu2, hqL, hlt]⟩
      · by_cases hu3 : u = y3
        · rw [hu3] at hl
          rcases h3l c' z hl with ⟨_, h, _⟩ | ⟨c0, hmem, hge, hck, hcc⟩
          · exact Or.inl (Or.inl h)
          · have hl0 := hQlink c0 z hmem
            have hnlt : ¬ c0 < r0.1 := by omega
            exact Or.inr ⟨hnotGone q c0 z hq hl0 (Or.inr hck) (Or.inl (Ne.symm hgq)),
              q, c0, hq, hl0, by simp [hu3, hqL, hnlt, hcc]⟩
        · by_cases huv : u = v
          · rw [huv] at hl; exact absurd hl (hvl c' z)
          · have huR := hReachOr u hu hu1 hu2 hu3 huv
            by_cases hug' : u = g
            · rw [hug'] at hl
              rcases hgl c' z hl with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, hc, hmem⟩
              · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
              · exact Or.inl (Or.inr (Or.inl h))
              · have hl0 : TLink N t g c' z := ⟨gn, hgn, hmem⟩
                exact Or.inr ⟨hnotGone g c' z hg hl0 (Or.inl hgq) (Or.inr hc), g, c', hg, hl0,
                  by simp [hgL, hgq, hug']⟩
            · have hl0 := hOld u huL huq hug' hu1 hu2 hu3 c' z hl
              exact Or.inr ⟨hnotGone u c' z huR hl0 (Or.inl huq) (Or.inl hug'), u, c', huR, hl0,
                by simp [huL, huq]⟩
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hone : ∀ y d, (TReach N t r y ∨ (y = y1 ∨ y = y2 ∨ y = y3 ∨ y = v)) →
        ¬ (y = L ∨ y = q) → TLink N' t y d z →
        (y = y2 ∧ d = k1 ∧ z = y1 ∧ k1 < r0.1) ∨
        (y = y3 ∧ d = splitLocalCv false r0.1 k1 ∧ z = y1 ∧ r0.1 ≤ k1) ∨
        (y = g ∧ d = r0.1 ∧ z = y3) ∨ (y = g ∧ d = kq ∧ z = y2) ∨ (y = y1 ∧ d = cv ∧ z = v) := by
      intro y d hy hyg hl
      have hfr := hfresh z hz
      have hyL : y ≠ L := fun h => hyg (Or.inl h)
      have hyq : y ≠ q := fun h => hyg (Or.inr h)
      by_cases hy1 : y = y1
      · rw [hy1] at hl
        rcases h1l d z hl with ⟨hd, h⟩ | ⟨hmem, _⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hy1, hd, h⟩)))
        · exact absurd ⟨n, hLn, hmem⟩ (hfr L d hL)
      · by_cases hy2 : y = y2
        · rw [hy2] at hl
          rcases h2l d z hl with ⟨hd, h, hlt⟩ | ⟨hmem, _, _⟩
          · exact Or.inl ⟨hy2, hd, h, hlt⟩
          · exact absurd (hQlink d z hmem) (hfr q d hq)
        · by_cases hy3 : y = y3
          · rw [hy3] at hl
            rcases h3l d z hl with ⟨hd, h, hge⟩ | ⟨c0, hmem, _, _, _⟩
            · exact Or.inr (Or.inl ⟨hy3, hd, h, hge⟩)
            · exact absurd (hQlink c0 z hmem) (hfr q c0 hq)
          · by_cases hyv : y = v
            · rw [hyv] at hl; exact absurd hl (hvl d z)
            · have hyR := hReachOr y hy hy1 hy2 hy3 hyv
              by_cases hyg' : y = g
              · rw [hyg'] at hl
                rcases hgl d z hl with ⟨hd, h⟩ | ⟨_, hd, h⟩ | ⟨_, _, hmem⟩
                · exact Or.inr (Or.inr (Or.inl ⟨hyg', hd, h⟩))
                · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hyg', hd, h⟩)))
                · exact absurd ⟨gn, hgn, hmem⟩ (hfr g d hg)
              · exact absurd (hOld y hyL hyq hyg' hy1 hy2 hy3 d z hl) (hfr y d hyR)
    rcases hone u c' hu hug hl1 with ⟨a1, b1, c1, e1⟩ | ⟨a1, b1, c1, e1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ |
        ⟨a1, b1, c1⟩ <;>
      rcases hone u' c'' hu' hug' hl2 with ⟨a2, b2, c2, e2⟩ | ⟨a2, b2, c2, e2⟩ | ⟨a2, b2, c2⟩ |
        ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
    all_goals first
      | exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
      | exact absurd (c1.symm.trans c2) h12
      | exact absurd (c2.symm.trans c1) h12
      | exact absurd (c1.symm.trans c2) h13
      | exact absurd (c2.symm.trans c1) h13
      | exact absurd (c1.symm.trans c2) h23
      | exact absurd (c2.symm.trans c1) h23
      | exact absurd (c1.symm.trans c2) (Ne.symm hv1)
      | exact absurd (c2.symm.trans c1) (Ne.symm hv1)
      | exact absurd (c1.symm.trans c2) (Ne.symm hv2)
      | exact absurd (c2.symm.trans c1) (Ne.symm hv2)
      | exact absurd (c1.symm.trans c2) (Ne.symm hv3)
      | exact absurd (c2.symm.trans c1) (Ne.symm hv3)
      | (exfalso; omega)
  · intro z hz hzg
    rcases hz with h | h | h | h <;> rcases hzg with h' | h' <;> rw [h] at h'
    · exact hne L n hLn y1 hf1 h'.symm
    · exact hne q qn hqn y1 hf1 h'.symm
    · exact hne L n hLn y2 hf2 h'.symm
    · exact hne q qn hqn y2 hf2 h'.symm
    · exact hne L n hLn y3 hf3 h'.symm
    · exact hne q qn hqn y3 hf3 h'.symm
    · exact hne L n hLn v hvN h'.symm
    · exact hne q qn hqn v hvN h'.symm
  · by_cases hrg : r = g
    · rw [hrg, hN'g]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      have hrq : r ≠ q := fun h => hT.rootFree g kq hg (by rw [h]; exact hgq_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      rw [hother r hrL hrq hrg (hne r rm hrm y1 hf1) (hne r rm hrm y2 hf2) (hne r rm hrm y3 hf3)]
      exact ⟨rm, hrm⟩

/-- The writer's time split of a leaf with the space split of its full parent
keeps the writer's tree (`writerWP_appendKlongs_timeSpace` with
`treeOK_timeSpace`). -/
theorem writerWP_appendKlongs_timeSpace_tree (base : View BVal) (d'' : Nat) (L q g : NodeId)
    (n qn gn : KNode) (kq k1 cv v : Nat) (c : Ctx) (w : W) (r0 : Nat × NodeId)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hgR : TReach (wNode c.p base w) c.i w.top.rootKey g)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hgt' : w.taken.contains g = false)
    (hgk : (kq, q) ∈ gn.liveAt c.i) (hqk : (k1, L) ∈ qn.liveAt c.i)
    (hgwf : klongsWf gn.ks = true) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ c.i)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hr0 : (qn.live.drop (qn.live.length / 2)).head? = some r0)
    (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hqfull : c.p.M < qn.size + 1 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hf1 : wNode c.p base w w.next = none) (hf2 : wNode c.p base w (w.next + 2) = none)
    (hf3 : wNode c.p base w (w.next + 2 + 2) = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (ht3 : w.taken.contains (w.next + 2 + 2) = false)
    (hvN : wNode c.p base w v = none) (hv1 : v ≠ w.next) (hv2 : v ≠ w.next + 2)
    (hv3 : v ≠ w.next + 2 + 2) (hLn : L < w.next)
    (hfresh : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = w.next + 2 + 2 ∨ z = v) →
      ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u → ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  have hwg : wNode c.p base w g = some gn := by simp only [wNode, hgt', Bool.false_eq_true, ↓reduceIte, hlg]
  have hgqL : TLink (wNode c.p base w) c.i g kq q := ⟨gn, hwg, hgk⟩
  have hq : TReach (wNode c.p base w) c.i w.top.rootKey q := TReach.link hgR hgqL
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqk; exact ⟨qn, hwq, hqk⟩)
  have hgq : g ≠ q := fun h => hT.no_self_link g kq hgR (by rw [← h] at hgqL; exact hgqL)
  have hgL : g ≠ L := fun h => hT.no_two_cycle g q kq k1 hgqL (by rw [h]; exact ⟨qn, hwq, hqk⟩) hgR
  have hnone : ∀ z, w.taken.contains z = false → wNode c.p base w z = none → w.nodes.lookup z = none := by
    intro z htz hfz
    unfold wNode at hfz; simp only [htz, Bool.false_eq_true, ↓reduceIte] at hfz
    split at hfz
    · cases hfz
    · assumption
  refine writerWP_mono (writerWP_appendKlongs_timeSpace d'' L q g n qn gn kq k1 cv v c w hlk hlq
    hlg hqL hgq hgL hql hgl hfirst hqfirst hfull hsplit hqfull hqsplit hpg hpq hpk hroomg hdeadg
    (hnone _ ht1 hf1) (hnone _ ht2 hf2) (hnone _ ht3 hf3) hLn) ?_
  intro _ w' ⟨l, _, _, hl_times, hl_look, h'taken, h'top, _, h'nodes⟩
  rw [h'top]
  rw [hql] at h'nodes
  have h12 : w.next ≠ w.next + 2 := by omega
  have h13 : w.next ≠ w.next + 2 + 2 := by omega
  have h23 : w.next + 2 ≠ w.next + 2 + 2 := by omega
  have hne : ∀ z m, wNode c.p base w z = some m → ∀ y, wNode c.p base w y = none → z ≠ y :=
    fun z m hz y hy he => by rw [he, hy] at hz; cases hz
  have hN' : ∀ x, wNode c.p base w' x = if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some ((gn.add c.i (.key kq (w.next + 2))).add c.i
        (.key (halves false c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2)))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else if x = w.next + 2 then some (halves false c.i (qn.lastVersion c.i) [(k1, w.next)]).1
      else if x = w.next + 2 + 2 then some (halves false c.i (qn.lastVersion c.i) [(k1, w.next)]).2.1
      else wNode c.p base w x := by
    intro x
    unfold wNode
    rw [h'taken, h'nodes x]
    by_cases hxL : x = L
    · subst hxL; simp only [hLt, Bool.false_eq_true, ↓reduceIte]
    · by_cases hxq : x = q
      · subst hxq; simp only [hqt', hxL, Bool.false_eq_true, ↓reduceIte]
      · by_cases hxg : x = g
        · subst hxg; simp only [hgt', hxL, hxq, Bool.false_eq_true, ↓reduceIte]
        · by_cases hx1 : x = w.next
          · subst hx1; simp only [ht1, hxL, hxq, hxg, Bool.false_eq_true, ↓reduceIte]
          · by_cases hx2 : x = w.next + 2
            · subst hx2; simp only [ht2, hxL, hxq, hxg, hx1, Bool.false_eq_true, ↓reduceIte]
            · by_cases hx3 : x = w.next + 2 + 2
              · subst hx3; simp only [ht3, hxL, hxq, hxg, hx1, hx2, Bool.false_eq_true, ↓reduceIte]
              · simp only [hxL, hxq, hxg, hx1, hx2, hx3, ↓reduceIte]
  have hL1 := hne L n hwL _ hf1
  have hL2 := hne L n hwL _ hf2
  have hL3 := hne L n hwL _ hf3
  have hq1 := hne q qn hwq _ hf1
  have hq2 := hne q qn hwq _ hf2
  have hq3 := hne q qn hwq _ hf3
  have hg1 := hne g gn hwg _ hf1
  have hg2 := hne g gn hwg _ hf2
  have hg3 := hne g gn hwg _ hf3
  apply treeOK_timeSpace (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey g q L w.next
    (w.next + 2) (w.next + 2 + 2) v gn qn n l kq k1 cv r0 hT hgR hwg hgk hgwf hgt hwq hql hqk hqt hr0
    hwL hnt hl_times (fun q' => by rw [hl_look q'])
  · rw [hN' g]; simp [hgL, hgq]
  · rw [hN' w.next]; simp [Ne.symm hL1, Ne.symm hq1, Ne.symm hg1]
  · rw [hN' (w.next + 2)]; simp [Ne.symm hL2, Ne.symm hq2, Ne.symm hg2]
  · rw [hN' (w.next + 2 + 2)]; simp [Ne.symm hL3, Ne.symm hq3, Ne.symm hg3, Ne.symm h13]
  · intro z hzL hzq hzg hz1 hz2 hz3
    rw [hN' z]; simp [hzL, hzq, hzg, hz1, hz2, hz3]
  · exact hf1
  · exact hf2
  · exact hf3
  · exact hvN
  · exact h12
  · exact h13
  · exact h23
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hfresh

/-- `writerWP_put_timeSpace` keeps the writer's tree: the leaf split in time,
its full parent in space, the grandparent with room for two klongs. -/
theorem writerWP_put_timeSpace_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ c.p.M < qn.size + 1 + 1 ∧
      qn.firstTime ≠ some c.i ∧ c.p.splitAbove < (qn.lastVersion c.i).size ∧
      2 ≤ qn.live.length)
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hq2⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have htn : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  obtain ⟨r0, hr0'⟩ : ∃ r0, (qn.live.drop (qn.live.length / 2)).head? = some r0 := by
    cases hd : (qn.live.drop (qn.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      omega
  apply writerWP_put_seg_append2 c base hvc pre cv h rk w S0 kq k1 q L n hrk ht hidn hidv hpath hNL hnl
    hfull
  intro qn' gn' d'' w5 hNq' hNg' hqv hgv hLv ⟨fdg, fdq, hgs, hkqc, hgy, hqs, hk1c, hqy⟩ hgl hql
    h5t h5top h5next h5L h5q h5g h5src hW5 hpg hpq hpk
  rw [hNq] at hNq'; cases hNq'
  rw [hNg] at hNg'; cases hNg'
  have hgR : ReachS (wNode c.p base w) c.i w.top.rootKey (pathEnd rk S0) :=
    eqVisits_reach _ _ _ cv c.p.fuel rk _ cv hrrk hgv
  have hgk : (kq, q) ∈ gn.liveAt c.i := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs; rw [hkqc, hgy] at this; exact this
  have hqk : (k1, L) ∈ qn.liveAt c.i := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs; rw [hk1c, hqy] at this; exact this
  have hLt : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hLv)
  have hqt' : w.taken.contains q = false := ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hgt' : w.taken.contains (pathEnd rk S0) = false :=
    ht (_, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  have hLn : L < w5.next := by have := h5src L (by rw [h5L]; rfl); omega
  apply writerWP_appendKlongs_timeSpace_tree base d'' L q (pathEnd rk S0) n qn gn kq k1 cv w.next
    c w5 r0
  · rw [hW5, h5top]; exact hT
  · rw [hW5, h5top]; exact reachS_tReach _ _ _ _ hgR
  · exact h5L
  · exact h5q
  · exact h5g
  · rw [h5t]; exact hLt
  · rw [h5t]; exact hqt'
  · rw [h5t]; exact hgt'
  · exact hgk
  · exact hqk
  · exact hwf _ gn hgR hNg
  · exact hgt
  · exact hqt
  · exact htimes
  · exact hr0'
  · exact hql
  · exact hgl
  · exact hfirst
  · exact hqfirst
  · exact hfull
  · exact hsplit
  · exact hqfull
  · exact hqsplit
  · exact hpg
  · exact hpq
  · exact hpk
  · exact hroomg
  · exact hdeadg
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [hW5, h5next]; exact hfree _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [h5next, h5t]; exact htn _ (by omega)
  · rw [hW5]; exact hfree _ (Nat.le_refl _)
  · rw [h5next]; omega
  · rw [h5next]; omega
  · rw [h5next]; omega
  · exact hLn
  · intro z hz u c' hu
    rw [hW5, h5top] at *
    rw [h5next] at hz
    exact hfreshT z (by omega) u c' hu

end SIS.Tree
