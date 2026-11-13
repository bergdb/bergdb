/-
The writer's tree kept by the space split of a segment root that is a leaf
below the segment leaf q of the segment above (bergdb 024-22, `OpTreeOK`): the
halves under a new segment root R that q's klong names (`treeOK_segSpaceSplit`,
for prover latest's `SegSpaceSplitAfter`).
-/
import SIS.Tree.WriterTreeSegRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The tree after a space split of the leaf L, named by q's klong k1, with a
klong (cv, v) put, into halves y1 and y2 under a new node R that q's klong k1
names instead of L; L is left behind. -/
theorem treeOK_segSpaceSplit (N N' : NodeId → Option KNode) (t : Time)
    (r q L y1 y2 R v : NodeId) (n qn : KNode) (k1 cv : Nat) (r0 : Nat × NodeId)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn)
    (hqk : (k1, L) ∈ qn.liveAt t) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n) (hnleaf : n.leaf = true)
    (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hN'q : N' q = some (qn.add t (.key k1 R)))
    (hN1 : N' y1 = some (halves true t (n.lastVersion t) [(cv, v)]).1)
    (hN2 : N' y2 = some (halves true t (n.lastVersion t) [(cv, v)]).2.1)
    (hNR : N' R = some ⟨false, newKlongs t [(0, y1), ((halves true t (n.lastVersion t) [(cv, v)]).2.2, y2)]⟩)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y1 → z ≠ y2 → z ≠ R → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (hfR : N R = none) (hvN : N v = none)
    (h12 : y1 ≠ y2) (h1R : y1 ≠ R) (h2R : y2 ≠ R) (hv1 : v ≠ y1) (hv2 : v ≠ y2) (hvR : v ≠ R)
    (hfresh : ∀ z, (z = y1 ∨ z = y2 ∨ z = R ∨ z = v) →
      ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  obtain ⟨hsc, hfirst, hsecond⟩ := halves_leaf_live n t hnleaf cv v r0 hr0
  generalize hout : halves true t (n.lastVersion t) [(cv, v)] = out at *
  rw [hsc] at hNR
  have hnlive : n.liveAt t = n.live := KNode.liveAt_of_times n t hnt
  have hne : ∀ z m, N z = some m → ∀ y, N y = none → z ≠ y := fun z m hz y hy he => by
    rw [he, hy] at hz; cases hz
  have hL1 := hne L n hLn y1 hf1
  have hL2 := hne L n hLn y2 hf2
  have hLR := hne L n hLn R hfR
  have hLv := hne L n hLn v hvN
  have hq1 := hne q qn hqn y1 hf1
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
  have hnotR : ∀ z, (z = y1 ∨ z = y2 ∨ z = R ∨ z = v) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h | h | h <;> rw [h]
    · exact not_reach_fresh N t r y1 hT hf1 (hfresh y1 (Or.inl rfl))
    · exact not_reach_fresh N t r y2 hT hf2 (hfresh y2 (Or.inr (Or.inl rfl)))
    · exact not_reach_fresh N t r R hT hfR (hfresh R (Or.inr (Or.inr (Or.inl rfl))))
    · exact not_reach_fresh N t r v hT hvN (hfresh v (Or.inr (Or.inr (Or.inr rfl))))
  have hvN' : N' v = none := by
    rw [hother v (Ne.symm hLv) (Ne.symm hqv) hv1 hv2 hvR]; exact hvN
  -- the links of the changed and new nodes
  have hRl : ∀ c' z, TLink N' t R c' z → (c' = 0 ∧ z = y1) ∨ (c' = r0.1 ∧ z = y2) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hNR] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have := liveAt_newKlongs_mem false t t _ c' z hc
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at this
    exact this
  have h1l : ∀ c' z, TLink N' t y1 c' z → ((c', z) = (cv, v) ∧ cv < r0.1) ∨
      ((c', z) ∈ n.live ∧ c' < r0.1) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN1] at hm
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
    exact KNode.add_key_liveAt_mem qn t k1 R hqwf hqt c' z hc
  have hvl : ∀ c' z, ¬ TLink N' t v c' z := by
    intro c' z hl
    obtain ⟨m, hm, _⟩ := hl
    rw [hvN'] at hm; cases hm
  -- an old node other than q names no new node and not L
  have hOld : ∀ u, TReach N t r u → u ≠ L → u ≠ q → u ≠ y1 → u ≠ y2 → u ≠ R → ∀ c' z,
      TLink N' t u c' z → TLink N t u c' z := by
    intro u _ huL huq hu1 hu2 huR c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hother u huL huq hu1 hu2 huR] at hm
    exact ⟨m, hm, hc⟩
  have hReachOr : ∀ u, (TReach N t r u ∨ (u = y1 ∨ u = y2 ∨ u = R ∨ u = v)) → u ≠ y1 → u ≠ y2 →
      u ≠ R → u ≠ v → TReach N t r u := by
    intro u hu h1 h2 h3 h4
    rcases hu with h | h
    · exact h
    · rcases h with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact absurd h h4
  apply treeOK_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2 ∨ z = R ∨ z = v) (fun z => z = L)
    (fun u c' => if u = L then (if c' < r0.1 then (y1, c') else (y2, c')) else (u, c')) hT hnotR
  · exact Or.inl ⟨rfl, fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)⟩
  · intro u c' z hu hug hl
    by_cases huR : u = R
    · rw [huR] at hl
      rcases hRl c' z hl with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
    · by_cases hu1 : u = y1
      · rw [hu1] at hl
        rcases h1l c' z hl with ⟨h, _⟩ | ⟨h, hlt⟩
        · simp only [Prod.mk.injEq] at h
          exact Or.inl (Or.inr (Or.inr (Or.inr h.2)))
        · refine Or.inr ⟨fun hzL => hT.no_self_link L c' hLreach (by
            have := hLlink c' z h; rw [hzL] at this; exact this),
            L, c', hLreach, hLlink c' z h, by simp [hu1, hlt]⟩
      · by_cases hu2 : u = y2
        · rw [hu2] at hl
          rcases h2l c' z hl with ⟨h, _⟩ | ⟨h, hge⟩
          · simp only [Prod.mk.injEq] at h
            exact Or.inl (Or.inr (Or.inr (Or.inr h.2)))
          · have hnlt : ¬ c' < r0.1 := by omega
            refine Or.inr ⟨fun hzL => hT.no_self_link L c' hLreach (by
              have := hLlink c' z h; rw [hzL] at this; exact this),
              L, c', hLreach, hLlink c' z h, by simp [hu2, hnlt]⟩
        · by_cases huv : u = v
          · rw [huv] at hl; exact absurd hl (hvl c' z)
          · have huRch := hReachOr u hu hu1 hu2 huR huv
            by_cases huq : u = q
            · rw [huq] at hl
              rcases hql c' z hl with ⟨_, h⟩ | ⟨hck, hmem⟩
              · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
              · have hl0 : TLink N t q c' z := ⟨qn, hqn, hmem⟩
                refine Or.inr ⟨fun hzL => ?_, q, c', hq, hl0, by simp [hqL]; exact huq.symm⟩
                rw [hzL] at hl0
                exact hck (hLpar q c' hq hl0).2
            · have hl0 := hOld u huRch hug huq hu1 hu2 huR c' z hl
              refine Or.inr ⟨fun hzL => ?_, u, c', huRch, hl0, by simp [hug]⟩
              rw [hzL] at hl0
              exact huq (hLpar u c' huRch hl0).1
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hone : ∀ y d, (TReach N t r y ∨ (y = y1 ∨ y = y2 ∨ y = R ∨ y = v)) → y ≠ L →
        TLink N' t y d z →
        (y = R ∧ d = 0 ∧ z = y1) ∨ (y = R ∧ d = r0.1 ∧ z = y2) ∨
        (z = v ∧ d = cv ∧ ((y = y1 ∧ cv < r0.1) ∨ (y = y2 ∧ r0.1 ≤ cv))) ∨
        (y = q ∧ d = k1 ∧ z = R) := by
      intro y d hy hyL hl
      have hfr : ∀ u c', TReach N t r u → ¬ TLink N t u c' z := hfresh z hz
      by_cases hyR : y = R
      · rw [hyR] at hl
        rcases hRl d z hl with ⟨hd, h⟩ | ⟨hd, h⟩
        · exact Or.inl ⟨hyR, hd, h⟩
        · exact Or.inr (Or.inl ⟨hyR, hd, h⟩)
      · by_cases hy1 : y = y1
        · rw [hy1] at hl
          rcases h1l d z hl with ⟨h, hlt⟩ | ⟨h, _⟩
          · simp only [Prod.mk.injEq] at h
            exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1, Or.inl ⟨hy1, hlt⟩⟩))
          · exact absurd (hLlink d z h) (hfr L d hLreach)
        · by_cases hy2 : y = y2
          · rw [hy2] at hl
            rcases h2l d z hl with ⟨h, hge⟩ | ⟨h, _⟩
            · simp only [Prod.mk.injEq] at h
              exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1, Or.inr ⟨hy2, hge⟩⟩))
            · exact absurd (hLlink d z h) (hfr L d hLreach)
          · by_cases hyv : y = v
            · rw [hyv] at hl; exact absurd hl (hvl d z)
            · have hyRch := hReachOr y hy hy1 hy2 hyR hyv
              by_cases hyq : y = q
              · rw [hyq] at hl
                rcases hql d z hl with ⟨hd, h⟩ | ⟨_, hmem⟩
                · exact Or.inr (Or.inr (Or.inr ⟨hyq, hd, h⟩))
                · exact absurd ⟨qn, hqn, hmem⟩ (hfr q d hq)
              · exact absurd (hOld y hyRch hyL hyq hy1 hy2 hyR d z hl) (hfr y d hyRch)
    rcases hone u c' hu hug hl1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
      rcases hone u' c'' hu' hug' hl2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact absurd (c1.symm.trans c2) h12
    · exact absurd (a2.symm.trans c1) hv1
    · exact absurd (c2.symm.trans c1) (Ne.symm h1R)
    · exact absurd (c2.symm.trans c1) h12
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact absurd (a2.symm.trans c1) hv2
    · exact absurd (c2.symm.trans c1) (Ne.symm h2R)
    · exact absurd (a1.symm.trans c2) hv1
    · exact absurd (a1.symm.trans c2) hv2
    · refine ⟨?_, b1.trans b2.symm⟩
      rcases c1 with ⟨h1, hlt⟩ | ⟨h1, hge⟩ <;> rcases c2 with ⟨h2, hlt'⟩ | ⟨h2, hge'⟩
      · exact h1.trans h2.symm
      · omega
      · omega
      · exact h1.trans h2.symm
    · exact absurd (a1.symm.trans c2) hvR
    · exact absurd (c1.symm.trans c2) (Ne.symm h1R)
    · exact absurd (c1.symm.trans c2) (Ne.symm h2R)
    · exact absurd (a2.symm.trans c1) hvR
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro z hz hzL
    rw [hzL] at hz
    rcases hz with h | h | h | h
    · exact hL1 h
    · exact hL2 h
    · exact hLR h
    · exact hLv h
  · by_cases hrq : r = q
    · rw [hrq, hN'q]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hr1 := hne r rm hrm y1 hf1
      have hr2 := hne r rm hrm y2 hf2
      have hrR := hne r rm hrm R hfR
      rw [hother r hrL hrq hr1 hr2 hrR]; exact ⟨rm, hrm⟩

/-- `writerWP_put_segSpaceSplit` keeps the writer's tree: the space split of a
segment root, a leaf that existed before the transaction, into a new segment
root below the segment leaf of the segment above with room. -/
theorem writerWP_put_segSpaceSplit_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive⟩ := hleaf
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
  obtain ⟨hqt, hroomq, hdeadq⟩ := hseg q qn hvisq hq hql
  have hqTR : TReach (wNode c.p base w) c.i w.top.rootKey q := reachS_tReach _ _ _ _ (hqR q hvisq)
  have hqL : q ≠ L := by
    intro he
    have hl : TLink (wNode c.p base w) c.i q k1 L := ⟨qn, hq, hk1⟩
    rw [← he] at hl
    exact hT.no_self_link q k1 hqTR hl
  have hLn : L < w5.next := by have := h5src L (by rw [h5L]; rfl); omega
  have hqn : q < w5.next := by have := h5src q (by rw [h5q]; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_segSpaceSplit d' L q n qn k1 cv w.next c w5
    h5L h5q hqL hql hfirst hfull hsplit hpq hpk hroomq hdeadq hLn hqn) ?_
  intro _ wf hA
  obtain ⟨hft, hftop, _, hfn⟩ := hA
  rw [hftop, h5top]
  rw [hnl] at hfn
  have hft' : wf.taken = w.taken := by rw [hft, h5t]
  have hLt : w.taken.contains L = false := by
    have := hNL; unfold wNode at this; split at this
    · cases this
    · rename_i h; simpa using h
  have hqt' : w.taken.contains q = false := by
    have := hq; unfold wNode at this; split at this
    · cases this
    · rename_i h; simpa using h
  rw [h5next] at hfn
  apply treeOK_segSpaceSplit (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey q L
    (w.next + 2) (w.next + 2 + 2) (w.next + 2 + 2 + 2) w.next n qn k1 cv r0 hT hqTR hq hk1
    (hwf q qn (hqR q hvisq) hq) hqt hNL hnl hr0' htimes
  · simp only [wNode, hft', hqt', Bool.false_eq_true, ↓reduceIte, hfn, hqL]
  · simp only [wNode, hft', htn _ (by omega : w.next ≤ w.next + 2), Bool.false_eq_true, ↓reduceIte,
      hfn, show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega]
  · simp only [wNode, hft', htn _ (by omega : w.next ≤ w.next + 2 + 2), Bool.false_eq_true,
      ↓reduceIte, hfn, show w.next + 2 + 2 ≠ L by omega,
      show w.next + 2 + 2 ≠ q by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega]
  · simp only [wNode, hft', htn _ (by omega : w.next ≤ w.next + 2 + 2 + 2), Bool.false_eq_true,
      ↓reduceIte, hfn, show w.next + 2 + 2 + 2 ≠ L by omega,
      show w.next + 2 + 2 + 2 ≠ q by omega, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
      show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega]
    rfl
  · intro z hzL hzq hz1 hz2 hzR
    rw [← hW5]
    simp only [wNode, hft', hfn, hzL, hzq, hz1, hz2, hzR, ↓reduceIte, h5t]
  · exact hfree _ (by omega)
  · exact hfree _ (by omega)
  · exact hfree _ (by omega)
  · exact hfree _ (Nat.le_refl _)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · intro z hz u c' hu
    exact hfreshT z (by omega) u c' hu

end SIS.Tree
