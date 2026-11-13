/-
The writer's tree kept by the space split in place of a segment root that is a
leaf the transaction made, below the segment leaf q of the segment above
(bergdb 024-22, `OpTreeOK`): the root keeps the first half, a new node the
second, a new segment root R names both, and q's klong names R
(`treeOK_segSpaceSplitInPlace`, for prover latest's
`SegSpaceSplitInPlaceAfter`).
-/
import SIS.Tree.WriterTreeSegSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem treeOK_segSpaceSplitInPlace (N N' : NodeId → Option KNode) (t : Time)
    (r q L y2 R v : NodeId) (n qn : KNode) (k1 cv j : Nat) (r0 : Nat × NodeId)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn)
    (hqk : (k1, L) ∈ qn.liveAt t) (hj : qn.linkIndex L k1 = some j)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n) (hnleaf : n.leaf = true)
    (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hN'q : N' q = some (qn.repoint j R))
    (hN'L : N' L = some (halves true t (n.lastVersion t) [(cv, v)]).1)
    (hN2 : N' y2 = some (halves true t (n.lastVersion t) [(cv, v)]).2.1)
    (hNR : N' R = some ⟨false, newKlongs t [(0, L), ((halves true t (n.lastVersion t) [(cv, v)]).2.2, y2)]⟩)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y2 → z ≠ R → N' z = N z)
    (hf2 : N y2 = none) (hfR : N R = none) (hvN : N v = none)
    (h2R : y2 ≠ R) (hv2 : v ≠ y2) (hvR : v ≠ R)
    (hfresh : ∀ z, (z = y2 ∨ z = R ∨ z = v) →
      ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  obtain ⟨hsc, hfirst, hsecond⟩ := halves_leaf_live n t hnleaf cv v r0 hr0
  generalize hout : halves true t (n.lastVersion t) [(cv, v)] = out at *
  rw [hsc] at hNR
  have hnlive : n.liveAt t = n.live := KNode.liveAt_of_times n t hnt
  have hne : ∀ z m, N z = some m → ∀ y, N y = none → z ≠ y := fun z m hz y hy he => by
    rw [he, hy] at hz; cases hz
  have hL2 := hne L n hLn y2 hf2
  have hLR := hne L n hLn R hfR
  have hLv := hne L n hLn v hvN
  have hq2 := hne q qn hqn y2 hf2
  have hqR := hne q qn hqn R hfR
  have hqv := hne q qn hqn v hvN
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hLreach : TReach N t r L := TReach.link hq hqL_link
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hLlink : ∀ c' z, (c', z) ∈ n.live → TLink N t L c' z := fun c' z h =>
    ⟨n, hLn, by rw [hnlive]; exact h⟩
  have hnotR : ∀ z, (z = y2 ∨ z = R ∨ z = v) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h | h <;> rw [h]
    · exact not_reach_fresh N t r y2 hT hf2 (hfresh y2 (Or.inl rfl))
    · exact not_reach_fresh N t r R hT hfR (hfresh R (Or.inr (Or.inl rfl)))
    · exact not_reach_fresh N t r v hT hvN (hfresh v (Or.inr (Or.inr rfl)))
  have hvN' : N' v = none := by
    rw [hother v (Ne.symm hLv) (Ne.symm hqv) hv2 hvR]; exact hvN
  -- the links of the changed and new nodes
  have hRl : ∀ c' z, TLink N' t R c' z → (c' = 0 ∧ z = L) ∨ (c' = r0.1 ∧ z = y2) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hNR] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have := liveAt_newKlongs_mem false t t _ c' z hc
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at this
    exact this
  have hLl : ∀ c' z, TLink N' t L c' z → ((c', z) = (cv, v) ∧ cv < r0.1) ∨
      ((c', z) ∈ n.live ∧ c' < r0.1) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'L] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hfirst c' z hc
  have h2l : ∀ c' z, TLink N' t y2 c' z → ((c', z) = (cv, v) ∧ r0.1 ≤ cv) ∨
      ((c', z) ∈ n.live ∧ r0.1 ≤ c') := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN2] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hsecond c' z hc
  have hql : ∀ c' z, TLink N' t q c' z → (c' = k1 ∧ z = R) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'q] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    rw [KNode.liveAt_of_times _ t (KNode.repoint_times qn j R t hqt)] at hc
    have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hc
    rw [KNode.repoint_live_lookup qn L R k1 j hj c'] at hlk
    by_cases hck : k1 = c'
    · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
    · have hb : (k1 == c') = false := by simpa using hck
      rw [hb] at hlk
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk
      refine Or.inr ⟨Ne.symm hck, ?_⟩
      rw [KNode.liveAt_of_times qn t hqt]
      exact mem_of_lookup_nodup _ c' z hlk
  have hvl : ∀ c' z, ¬ TLink N' t v c' z := by
    intro c' z hl
    obtain ⟨m, hm, _⟩ := hl
    rw [hvN'] at hm; cases hm
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ y2 → u ≠ R → ∀ c' z,
      TLink N' t u c' z → TLink N t u c' z := by
    intro u huL huq hu2 huR c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hother u huL huq hu2 huR] at hm
    exact ⟨m, hm, hc⟩
  have hReachOr : ∀ u, (TReach N t r u ∨ (u = y2 ∨ u = R ∨ u = v)) → u ≠ y2 →
      u ≠ R → u ≠ v → TReach N t r u := by
    intro u hu h2 h3 h4
    rcases hu with h | h
    · exact h
    · rcases h with h | h | h
      · exact absurd h h2
      · exact absurd h h3
      · exact absurd h h4
  apply treeOK_transfer_gone N N' t r r (fun z => z = y2 ∨ z = R ∨ z = v) (fun _ => False)
    (fun u c' => if u = L then (if c' < r0.1 then (L, c') else (y2, c'))
      else if u = q ∧ c' = k1 then (R, 0) else (u, c')) hT hnotR
  · exact Or.inl ⟨rfl, id⟩
  · intro u c' z hu _ hl
    by_cases huR : u = R
    · rw [huR] at hl
      rcases hRl c' z hl with ⟨hc0, h⟩ | ⟨_, h⟩
      · rw [h]
        exact Or.inr ⟨id, q, k1, hq, hqL_link, by simp [hqL, huR, hc0]⟩
      · exact Or.inl (Or.inl h)
    · by_cases hu2 : u = y2
      · rw [hu2] at hl
        rcases h2l c' z hl with ⟨h, _⟩ | ⟨h, hge⟩
        · simp only [Prod.mk.injEq] at h
          exact Or.inl (Or.inr (Or.inr h.2))
        · have hnlt : ¬ c' < r0.1 := by omega
          exact Or.inr ⟨id, L, c', hLreach, hLlink c' z h, by simp [hu2, hnlt]⟩
      · by_cases huv : u = v
        · rw [huv] at hl; exact absurd hl (hvl c' z)
        · have huRch := hReachOr u hu hu2 huR huv
          by_cases huL : u = L
          · rw [huL] at hl
            rcases hLl c' z hl with ⟨h, _⟩ | ⟨h, hlt⟩
            · simp only [Prod.mk.injEq] at h
              exact Or.inl (Or.inr (Or.inr h.2))
            · exact Or.inr ⟨id, L, c', hLreach, hLlink c' z h, by simp [huL, hlt]⟩
          · by_cases huq : u = q
            · rw [huq] at hl
              rcases hql c' z hl with ⟨_, h⟩ | ⟨hck, hmem⟩
              · exact Or.inl (Or.inr (Or.inl h))
              · exact Or.inr ⟨id, q, c', hq, ⟨qn, hqn, hmem⟩, by simp [hqL, hck, huq]⟩
            · exact Or.inr ⟨id, u, c', huRch, hOld u huL huq hu2 huR c' z hl, by simp [huL, huq]⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl1 hl2
    have hone : ∀ y d, (TReach N t r y ∨ (y = y2 ∨ y = R ∨ y = v)) → TLink N' t y d z →
        (y = R ∧ d = r0.1 ∧ z = y2) ∨
        (z = v ∧ d = cv ∧ ((y = L ∧ cv < r0.1) ∨ (y = y2 ∧ r0.1 ≤ cv))) ∨
        (y = q ∧ d = k1 ∧ z = R) := by
      intro y d hy hl
      have hfr : ∀ u c', TReach N t r u → ¬ TLink N t u c' z := hfresh z hz
      by_cases hyR : y = R
      · rw [hyR] at hl
        rcases hRl d z hl with ⟨_, h⟩ | ⟨hd, h⟩
        · rw [h] at hz
          rcases hz with h' | h' | h'
          · exact absurd h' hL2
          · exact absurd h' hLR
          · exact absurd h' hLv
        · exact Or.inl ⟨hyR, hd, h⟩
      · by_cases hy2 : y = y2
        · rw [hy2] at hl
          rcases h2l d z hl with ⟨h, hge⟩ | ⟨h, _⟩
          · simp only [Prod.mk.injEq] at h
            exact Or.inr (Or.inl ⟨h.2, h.1, Or.inr ⟨hy2, hge⟩⟩)
          · exact absurd (hLlink d z h) (hfr L d hLreach)
        · by_cases hyv : y = v
          · rw [hyv] at hl; exact absurd hl (hvl d z)
          · have hyRch := hReachOr y hy hy2 hyR hyv
            by_cases hyL : y = L
            · rw [hyL] at hl
              rcases hLl d z hl with ⟨h, hlt⟩ | ⟨h, _⟩
              · simp only [Prod.mk.injEq] at h
                exact Or.inr (Or.inl ⟨h.2, h.1, Or.inl ⟨hyL, hlt⟩⟩)
              · exact absurd (hLlink d z h) (hfr L d hLreach)
            · by_cases hyq : y = q
              · rw [hyq] at hl
                rcases hql d z hl with ⟨hd, h⟩ | ⟨_, hmem⟩
                · exact Or.inr (Or.inr ⟨hyq, hd, h⟩)
                · exact absurd ⟨qn, hqn, hmem⟩ (hfr q d hq)
              · exact absurd (hOld y hyL hyq hy2 hyR d z hl) (hfr y d hyRch)
    rcases hone u c' hu hl1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
      rcases hone u' c'' hu' hl2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact absurd (a2.symm.trans c1) hv2
    · exact absurd (c1.symm.trans c2) h2R
    · exact absurd (a1.symm.trans c2) hv2
    · refine ⟨?_, b1.trans b2.symm⟩
      rcases c1 with ⟨h1, hlt⟩ | ⟨h1, hge⟩ <;> rcases c2 with ⟨h2, hlt'⟩ | ⟨h2, hge'⟩
      · exact h1.trans h2.symm
      · omega
      · omega
      · exact h1.trans h2.symm
    · exact absurd (a1.symm.trans c2) hvR
    · exact absurd (c2.symm.trans c1) h2R
    · exact absurd (a2.symm.trans c1) hvR
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro _ _ h; exact h
  · by_cases hrq : r = q
    · rw [hrq, hN'q]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hr2 := hne r rm hrm y2 hf2
      have hrR := hne r rm hrm R hfR
      rw [hother r hrL hrq hr2 hrR]; exact ⟨rm, hrm⟩

/-- `writerWP_put_segSpaceSplitInPlace` keeps the writer's tree: the space split
in place of a segment root, a leaf the transaction made, into a new segment
root below the segment leaf of the segment above. -/
theorem writerWP_put_segSpaceSplitInPlace_tree (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode)
    (w : W)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime = some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hsegT : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true → ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  obtain ⟨htimes, hfull, hmade, hsplit, hlive⟩ := hleaf
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
  have hrrq : ReachS (wNode c.p base w) c.i w.top.rootKey rq :=
    segRootR_reach _ _ _ _ hwf pre0 _ rq ReachS.root hrq
  have hqR : ∀ q, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    fun q hq => eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hq
  obtain ⟨r0, hr0'⟩ : ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
    cases hd : (n.live.drop (n.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      have : n.live.length ≠ 0 := fun h0 => hlive (List.eq_nil_of_length_eq_zero h0)
      omega
  apply writerWP_put_segRoot_append c base hvc pre0 k1 cv h rq L n w hrq ht hidn hidv hL hNL hnl
    (fun hh => by omega) (fun q qn hq hqn => hwf q qn (hqR q hq) hqn)
  intro q qn d' w5 hvisq hq hql hk1 h5t h5top h5next h5L h5q h5src hW5 hpq hpk
  have hqt := hsegT q qn hvisq hq hql
  have hqTR : TReach (wNode c.p base w) c.i w.top.rootKey q := reachS_tReach _ _ _ _ (hqR q hvisq)
  have hqL : q ≠ L := by
    intro he
    have hl : TLink (wNode c.p base w) c.i q k1 L := ⟨qn, hq, hk1⟩
    rw [← he] at hl
    exact hT.no_self_link q k1 hqTR hl
  have hLn : L < w5.next := by have := h5src L (by rw [h5L]; rfl); omega
  have hqn : q < w5.next := by have := h5src q (by rw [h5q]; rfl); omega
  have hny : w5.nodes.lookup (w5.next + 2) = none := by
    cases h' : w5.nodes.lookup (w5.next + 2) with
    | none => rfl
    | some _ => have := h5src _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_segSpaceSplitInPlace d' L q n qn k1 cv w.next c w5
    h5L h5q hqL hql hmade hfull hsplit hpq hpk hLn hqn hny) ?_
  intro _ wf hA
  obtain ⟨j, hj, hft, hftop, _, hfn⟩ := hA
  rw [hftop, h5top]
  rw [hnl, h5next] at hfn
  have hft' : wf.taken = w.taken := by rw [hft, h5t]
  have hLt : w.taken.contains L = false := by
    have := hNL; unfold wNode at this; split at this
    · cases this
    · rename_i h; simpa using h
  have hqt' : w.taken.contains q = false := by
    have := hq; unfold wNode at this; split at this
    · cases this
    · rename_i h; simpa using h
  apply treeOK_segSpaceSplitInPlace (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey q L
    (w.next + 2) (w.next + 2 + 2) w.next n qn k1 cv j r0 hT hqTR hq hk1 hj hqt hNL hnl hr0' htimes
  · simp only [wNode, hft', hqt', Bool.false_eq_true, ↓reduceIte, hfn, hqL]
  · simp only [wNode, hft', hLt, Bool.false_eq_true, ↓reduceIte, hfn]
  · simp only [wNode, hft', htn _ (by omega : w.next ≤ w.next + 2), Bool.false_eq_true, ↓reduceIte,
      hfn, show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega]
  · simp only [wNode, hft', htn _ (by omega : w.next ≤ w.next + 2 + 2), Bool.false_eq_true,
      ↓reduceIte, hfn, show w.next + 2 + 2 ≠ L by omega,
      show w.next + 2 + 2 ≠ q by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega]
    rfl
  · intro z hzL hzq hz2 hzR
    rw [← hW5]
    simp only [wNode, hft', hfn, hzL, hzq, hz2, hzR, ↓reduceIte, h5t]
  · exact hfree _ (by omega)
  · exact hfree _ (by omega)
  · exact hfree _ (Nat.le_refl _)
  · omega
  · omega
  · omega
  · intro z hz u c' hu
    exact hfreshT z (by omega) u c' hu

end SIS.Tree
