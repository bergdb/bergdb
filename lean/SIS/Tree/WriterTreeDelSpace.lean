/-
A delete into a full segment leaf whose last version without the key is
space split keeps the writer's tree (bergdb 024-22, `OpTreeOK`), as prover
putinv's `putInv_del_leafBelow2` (024-12): `treeOK_spaceSplit_sub`,
`treeOK_spaceSplitInPlace_sub`, `writerWP_appendDeleteKlong_tree2`,
`writerWP_del_leafBelow2_tree`, and with `PutInv`, `putInv_del_leafBelow2_full`.
-/
import SIS.Tree.PutInvDelSpace
import SIS.Tree.WriterTreeInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The tree after a space split of L below q into new nodes y1 and y2 whose
live klongs are L's below and at or above sc: q's klong k1 names y1 and a new
klong sc names y2; L is left behind. -/
theorem treeOK_spaceSplit_sub (N N' : NodeId → Option KNode) (t : Time) (r q L y1 y2 : NodeId)
    (qn n f s : KNode) (k1 sc : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n)
    (hN'q : N' q = some ((qn.add t (.key k1 y1)).add t (.key sc y2)))
    (hN'1 : N' y1 = some f) (hN'2 : N' y2 = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → (c, z) ∈ n.liveAt t ∧ c < sc)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → (c, z) ∈ n.liveAt t ∧ sc ≤ c)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y1 → z ≠ y2 → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (h12 : y1 ≠ y2)
    (hfresh : ∀ z, (z = y1 ∨ z = y2) → ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hL1 : L ≠ y1 := fun h => by rw [h, hf1] at hLn; cases hLn
  have hL2 : L ≠ y2 := fun h => by rw [h, hf2] at hLn; cases hLn
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hq1wf := KNode.add_key_wf qn t k1 y1 hqwf
  have hq1t := KNode.add_times qn t (.key k1 y1) (fun s h => by cases h) hqt
  have hql : ∀ c' z, TLink N' t q c' z → (c' = sc ∧ z = y2) ∨ (c' ≠ sc ∧ c' = k1 ∧ z = y1) ∨
      (c' ≠ sc ∧ c' ≠ k1 ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'q] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    rcases KNode.add_key_liveAt_mem _ t sc y2 hq1wf hq1t c' z hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · rcases KNode.add_key_liveAt_mem qn t k1 y1 hqwf hqt c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
      · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
  have h1l : ∀ c' z, TLink N' t y1 c' z → TLink N t L c' z ∧ c' < sc := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'1] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨⟨n, hLn, (hf c' z hc).1⟩, (hf c' z hc).2⟩
  have h2l : ∀ c' z, TLink N' t y2 c' z → TLink N t L c' z ∧ sc ≤ c' := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'2] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨⟨n, hLn, (hs c' z hc).1⟩, (hs c' z hc).2⟩
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
  apply treeOK_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2) (fun z => z = L)
    (fun u c' => if u = L then (if c' < sc then (y1, c') else (y2, c')) else (u, c')) hT hnotR
  · exact Or.inl ⟨rfl, fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)⟩
  · intro u c' z hu hug hl
    have huL : u ≠ L := hug
    have hnotL : ∀ y0 c0, TReach N t r y0 → TLink N t y0 c0 z → (y0 ≠ q ∨ c0 ≠ k1) →
        ¬ (fun z => z = L) z := by
      intro y0 c0 hy0 hl0 hne hz
      have hz' : z = L := hz
      rw [hz'] at hl0
      obtain ⟨a, b⟩ := hLpar y0 c0 hy0 hl0
      rcases hne with h | h
      · exact h a
      · exact h b
    by_cases hu1 : u = y1
    · rw [hu1] at hl
      obtain ⟨hl0, hlt⟩ := h1l c' z hl
      exact Or.inr ⟨hnotL L c' hL hl0 (Or.inl (Ne.symm hqL)), L, c', hL, hl0, by simp [hu1, hlt]⟩
    · by_cases hu2 : u = y2
      · rw [hu2] at hl
        obtain ⟨hl0, hge⟩ := h2l c' z hl
        have hnlt : ¬ c' < sc := by omega
        exact Or.inr ⟨hnotL L c' hL hl0 (Or.inl (Ne.symm hqL)), L, c', hL, hl0, by simp [hu2, hnlt]⟩
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
            exact Or.inr ⟨hnotL q c' hq hl0 (Or.inr hc), q, c', hq, hl0, by simp [hqL, huq]⟩
        · have hl0 := hOld u huL huq hu1 hu2 c' z hl
          exact Or.inr ⟨hnotL u c' huR hl0 (Or.inl huq), u, c', huR, hl0, by simp [huL]⟩
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hz' : z = y1 ∨ z = y2 := hz
    have hfr := hfresh z hz'
    have hone : ∀ v d, (TReach N t r v ∨ (v = y1 ∨ v = y2)) → v ≠ L → TLink N' t v d z →
        (v = q ∧ d = sc ∧ z = y2) ∨ (v = q ∧ d = k1 ∧ z = y1) := by
      intro v d hv hvg hl
      by_cases hv1 : v = y1
      · rw [hv1] at hl; exact absurd (h1l d z hl).1 (hfr L d hL)
      · by_cases hv2 : v = y2
        · rw [hv2] at hl; exact absurd (h2l d z hl).1 (hfr L d hL)
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
  · intro z hz hzg
    have h2 : z = L := hzg
    rcases hz with h | h
    · exact hL1 (h2.symm.trans h)
    · exact hL2 (h2.symm.trans h)
  · by_cases hrq : r = q
    · rw [hrq, hN'q]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hr1 : r ≠ y1 := fun h => by rw [h, hf1] at hrm; cases hrm
      have hr2 : r ≠ y2 := fun h => by rw [h, hf2] at hrm; cases hrm
      rw [hother r hrL hrq hr1 hr2]; exact ⟨rm, hrm⟩

/-- The tree after a space split in place of L below q: L keeps its live klongs
below sc, a new node y those at or above it, which q's new klong sc names. -/
theorem treeOK_spaceSplitInPlace_sub (N N' : NodeId → Option KNode) (t : Time) (r q L y : NodeId)
    (qn n f s : KNode) (k1 sc : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n)
    (hN'q : N' q = some (qn.add t (.key sc y))) (hN'L : N' L = some f) (hN'y : N' y = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → (c, z) ∈ n.liveAt t ∧ c < sc)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → (c, z) ∈ n.liveAt t ∧ sc ≤ c)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y → N' z = N z)
    (hfy : N y = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' y) :
    TreeOK N' t r := by
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hLy : L ≠ y := fun h => by rw [h, hfy] at hLn; cases hLn
  have hqy : q ≠ y := fun h => by rw [h, hfy] at hqn; cases hqn
  have hql : ∀ c' z, TLink N' t q c' z → (c' = sc ∧ z = y) ∨ (c' ≠ sc ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'q] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact KNode.add_key_liveAt_mem qn t sc y hqwf hqt c' z hc
  have hLl : ∀ c' z, TLink N' t L c' z → TLink N t L c' z ∧ c' < sc := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'L] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨⟨n, hLn, (hf c' z hc).1⟩, (hf c' z hc).2⟩
  have hyl : ∀ c' z, TLink N' t y c' z → TLink N t L c' z ∧ sc ≤ c' := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'y] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨⟨n, hLn, (hs c' z hc).1⟩, (hs c' z hc).2⟩
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ y → ∀ c' z, TLink N' t u c' z → TLink N t u c' z := by
    intro u h1 h2 h3 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2 h3] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, z = y → ¬ TReach N t r z := by
    intro z hz; rw [hz]; exact not_reach_fresh N t r y hT hfy hfresh
  apply treeOK_transfer_gone N N' t r r (fun z => z = y) (fun _ => False)
    (fun u c' => if u = L then (if c' < sc then (L, c') else (y, c')) else (u, c')) hT hnotR
  · exact Or.inl ⟨rfl, fun h => h⟩
  · intro u c' z hu _ hl
    by_cases huy : u = y
    · rw [huy] at hl
      obtain ⟨hl0, hge⟩ := hyl c' z hl
      have hnlt : ¬ c' < sc := by omega
      exact Or.inr ⟨fun h => h, L, c', hL, hl0, by simp [huy, hnlt]⟩
    · have huR : TReach N t r u := hu.elim id (fun h => absurd h huy)
      by_cases huL : u = L
      · rw [huL] at hl
        obtain ⟨hl0, hlt⟩ := hLl c' z hl
        exact Or.inr ⟨fun h => h, L, c', hL, hl0, by simp [huL, hlt]⟩
      · by_cases huq : u = q
        · rw [huq] at hl
          rcases hql c' z hl with ⟨_, h⟩ | ⟨_, hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨fun h => h, q, c', hq, ⟨qn, hqn, hm⟩, by simp [hqL, huq]⟩
        · exact Or.inr ⟨fun h => h, u, c', huR, hOld u huL huq huy c' z hl, by simp [huL]⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl1 hl2
    have hz' : z = y := hz
    have hone : ∀ v d, (TReach N t r v ∨ v = y) → TLink N' t v d z → v = q ∧ d = sc := by
      intro v d hv hl
      rw [hz'] at hl
      by_cases hvy : v = y
      · rw [hvy] at hl; exact absurd (hyl d y hl).1 (hfresh L d hL)
      · have hvR : TReach N t r v := hv.elim id (fun h => absurd h hvy)
        by_cases hvL : v = L
        · rw [hvL] at hl; exact absurd (hLl d y hl).1 (hfresh L d hL)
        · by_cases hvq : v = q
          · rw [hvq] at hl
            rcases hql d y hl with ⟨hd, _⟩ | ⟨_, hm⟩
            · exact ⟨hvq, hd⟩
            · exact absurd ⟨qn, hqn, hm⟩ (hfresh q d hq)
          · exact absurd (hOld v hvL hvq hvy d y hl) (hfresh v d hvR)
    obtain ⟨a1, b1⟩ := hone u c' hu hl1
    obtain ⟨a2, b2⟩ := hone u' c'' hu' hl2
    exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro z _ h; exact h
  · by_cases hrq : r = q
    · rw [hrq, hN'q]; exact ⟨_, rfl⟩
    · by_cases hrL : r = L
      · rw [hrL, hN'L]; exact ⟨_, rfl⟩
      · obtain ⟨rm, hrm⟩ := hT.rootKey
        have hry : r ≠ y := fun h => by rw [h, hfy] at hrm; cases hrm
        rw [hother r hrL hrq hry]; exact ⟨rm, hrm⟩

/-- A delete's bitmap in a segment leaf L below an inner parent q with room for
two klongs: by the bitmap, or, full, by a time split or a space split of L's
last version without the key (in place for a leaf the transaction made), the
writer's tree is kept. -/
theorem writerWP_appendDeleteKlong_tree2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w3 : W) (cv k1 d' : Nat) (L q : NodeId) (n qn : KNode)
    (hT : TreeOK (wNode c.p base w3) c.i w3.top.rootKey)
    (hq : TReach (wNode c.p base w3) c.i w3.top.rootKey q)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hLt : w3.taken.contains L = false) (hqt' : w3.taken.contains q = false)
    (hnl : n.leaf = true) (hql : qn.leaf = false) (hk1 : (k1, L) ∈ qn.liveAt c.i) (hqL : q ≠ L)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hpq : (w3.path[d']?).map (·.2) = some q) (hpk : w3.path[d' + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsa : 1 ≤ c.p.splitAbove)
    (hroomq2 : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq2 : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hdeadq1 : ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hLn : L < w3.next) (hqn : q < w3.next)
    (hny : wNode c.p base w3 w3.next = none) (hnyt : w3.taken.contains w3.next = false)
    (hny2 : wNode c.p base w3 (w3.next + 2) = none) (hnyt2 : w3.taken.contains (w3.next + 2) = false)
    (hfresh : ∀ z, (z = w3.next ∨ z = w3.next + 2) → ∀ u c', TReach (wNode c.p base w3) c.i
      w3.top.rootKey u → ¬ TLink (wNode c.p base w3) c.i u c' z) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 =>
      TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
  have hwL : wNode c.p base w3 L = some n := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk3]
  have hwq : wNode c.p base w3 q = some qn := by
    simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq3]
  have hnlive : n.liveAt c.i = n.live := KNode.liveAt_of_times n c.i hnt
  have hnone : ∀ z, w3.taken.contains z = false → wNode c.p base w3 z = none →
      w3.nodes.lookup z = none := by
    intro z htz hfz
    unfold wNode at hfz; simp only [htz, Bool.false_eq_true, ↓reduceIte] at hfz
    split at hfz
    · cases hfz
    · assumption
  have hroomq : qn.size + 1 + 1 ≤ c.p.M := by omega
  -- the space split of the full leaf
  have hspace0 : c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L []
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false) c
        ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 =>
          TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
    intro hsp s
    obtain ⟨sc, hsc, _, hfh, hsh⟩ := halves_del_live n c.i cv hnl (by omega)
    rw [hnl] at hfh hsh hsc
    generalize hout : halves true c.i (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) [] = out at *
    have hf : ∀ c' z, (c', z) ∈ out.1.liveAt c.i → (c', z) ∈ n.liveAt c.i ∧ c' < sc := by
      intro c' z h; rw [hnlive]; exact hfh c' z h
    have hs : ∀ c' z, (c', z) ∈ out.2.1.liveAt c.i → (c', z) ∈ n.liveAt c.i ∧ sc ≤ c' := by
      intro c' z h; rw [hnlive]; exact hsh c' z h
    have hlk3' : ({ w3 with trail := s :: w3.trail } : W).nodes.lookup L = some n := hlk3
    have hlq3' : ({ w3 with trail := s :: w3.trail } : W).nodes.lookup q = some qn := hlq3
    by_cases hnew : n.firstTime = some c.i
    · have h := writerWP_handleFullWith_spaceSplitInPlace_nil d' L q n qn
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) c _ hlk3' hlq3' hqL hql
        hnew hsp hpq hroomq (fun k y => hdeadq1 k y) hLn hqn
      rw [hnl, hout] at h
      refine writerWP_mono h ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hsc] at h4nodes
      have h4t' : w4.taken = w3.taken := h4t
      rw [h4top]
      have hLy : L ≠ w3.next := by omega
      have hqy : q ≠ w3.next := by omega
      apply treeOK_spaceSplitInPlace_sub (wNode c.p base w3) (wNode c.p base w4) c.i w3.top.rootKey
        q L w3.next qn n out.1 out.2.1 k1 sc hT hq hwq hk1 hqwf hqt hwL
      · show wNode c.p base w4 q = _
        simp only [wNode, h4t', hqt', Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · show wNode c.p base w4 L = _
        simp only [wNode, h4t', hLt, Bool.false_eq_true, ↓reduceIte, h4nodes]
      · show wNode c.p base w4 w3.next = _
        simp only [wNode, h4t', hnyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hLy.symm, hqy.symm]
      · exact hf
      · exact hs
      · intro x hxL hxq hxy
        show wNode c.p base w4 x = _
        simp only [wNode, h4t', h4nodes, hxL, hxq, hxy, ↓reduceIte]
      · exact hny
      · exact hfresh _ (Or.inl rfl)
    · have h := writerWP_handleFullWith_spaceSplit_nil d' L q n qn
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) k1 c _ hlk3' hlq3' hqL hql
        hnew hsp hpq hpk hroomq2 (fun y1 sc y2 => hdeadq2 y1 sc y2) (hnone _ hnyt hny)
        (hnone _ hnyt2 hny2)
      rw [hnl, hout] at h
      refine writerWP_mono h ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hsc] at h4nodes
      have h4t' : w4.taken = w3.taken := h4t
      rw [h4top]
      have hL1 : L ≠ w3.next := by omega
      have hq1 : q ≠ w3.next := by omega
      have hL2 : L ≠ w3.next + 2 := by omega
      have hq2 : q ≠ w3.next + 2 := by omega
      have h21 : w3.next + 2 ≠ w3.next := by omega
      apply treeOK_spaceSplit_sub (wNode c.p base w3) (wNode c.p base w4) c.i w3.top.rootKey
        q L w3.next (w3.next + 2) qn n out.1 out.2.1 k1 sc hT hq hwq hk1 hqwf hqt hwL
      · show wNode c.p base w4 q = _
        simp only [wNode, h4t', hqt', Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · show wNode c.p base w4 w3.next = _
        simp only [wNode, h4t', hnyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hL1.symm, hq1.symm]
      · show wNode c.p base w4 (w3.next + 2) = _
        simp only [wNode, h4t', hnyt2, Bool.false_eq_true, ↓reduceIte, h4nodes, hL2.symm, hq2.symm, h21]
      · exact hf
      · exact hs
      · intro x hxL hxq hx1 hx2
        show wNode c.p base w4 x = _
        simp only [wNode, h4t', h4nodes, hxL, hxq, hx1, hx2, ↓reduceIte]
      · exact hny
      · exact hny2
      · omega
      · exact hfresh
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hleq hlt hlsub hspace0
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hlsub hspace0
  have hlastsub : ∀ c' z, (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z h
    rw [hleq, KNode.liveAt_of_times last c.i hlt] at h
    rw [hnlive]; exact hlsub c' z h
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 =>
          TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
    intro compact hcs s
    have hlk3' : ({ w3 with trail := s :: w3.trail } : W).nodes.lookup L = some n := hlk3
    by_cases hnew : n.firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nil _ (d' + 1) L n last compact c
        base hvc _ hlk3' hLt hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, hN4⟩
      rw [h4top]
      refine treeOK_of_node_shrink (wNode c.p base w3) (wNode c.p base w4) c.i w3.top.rootKey L n
        ⟨n.leaf, last.ks⟩ hT hwL (by rw [hN4]; simp) ?_ hlastsub
      intro y hy; rw [hN4]; simp only [hy, ↓reduceIte]; rfl
    · have hny' : ({ w3 with trail := s :: w3.trail } : W).nodes.lookup
          ({ w3 with trail := s :: w3.trail } : W).next = none := hnone _ hnyt hny
      refine writerWP_mono (writerWP_handleFullWith_timeSplit_nil d' L q n qn last k1 compact c _
        hlk3' hlq3 hqL hql hnew hcs hpq hpk hroomq (hdeadq1 k1) hny') ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [h4top]
      have h4t' : w4.taken = w3.taken := h4t
      have hLy : L ≠ w3.next := by omega
      have hqy : q ≠ w3.next := by omega
      apply treeOK_timeSplit_sub (wNode c.p base w3) (wNode c.p base w4) c.i w3.top.rootKey q L
        w3.next qn n ⟨n.leaf, last.ks⟩ k1 hT hq hwq hk1 hqwf hqt hwL
      · simp only [wNode, h4t', hqt', Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · simp only [wNode, h4t', hnyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hLy.symm, hqy.symm]
      · exact hlastsub
      · intro x hxL hxq hxy
        simp only [wNode, h4t', h4nodes, hxL, hxq, hxy, ↓reduceIte]
      · exact hny
      · exact hfresh _ (Or.inl rfl)
  -- the bitmap in L: a node that loses live klongs only
  have hshrink : ∀ (n' : KNode) (s : String),
      (∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 =>
        TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
    intro n' s hsub
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    refine treeOK_of_node_shrink (wNode c.p base w3) _ c.i w3.top.rootKey L n n' hT hwL ?_ ?_ hsub
    · simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro y hy
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro old hold c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z, (c', z) ∈ (n.add c.i (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false) c w3 (fun _ w4 => TreeOK (wNode c.p base w4) c.i w4.top.rootKey) := by
      intro _
      by_cases hsz : n.size + 1 < c.p.M
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hsz)]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]; exact htime true _ (by simp)
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]; exact hshrink _ _ hadd
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hsz)]
        by_cases hsp : c.p.splitAbove < last.size
        · simp only [note, writerWP_bind, writerWP_modify]
          exact writerWP_mono (hspace0 hsp _) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
        · apply htime false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
          omega
    cases hg : n.ks.getLast? with
    | none =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i) with
        | false =>
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt)
        | true =>
          simp only [Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]; exact htime true _ (by simp)
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
            exact hshrink _ _ (hsetAt old hg)
      | _ =>
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-- Every delete of a key whose prefix is there, below an inner segment root
and an inner parent with room for two klongs, by a bitmap in its segment leaf,
which keeps a live klong, the merges off, keeps the writer's tree: with room
for the bitmap, or the leaf full by its size or by its dead klongs, time split
or space split, in place for a leaf the transaction made (as prover putinv's
`putInv_del_leafBelow2`). -/
theorem writerWP_del_leafBelow2_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimes : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
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
  apply writerWP_del_seg_leaf c base hvc pre cv rk w hrk ht hidn hidv hinner
  intro L n q qn k1 d' w3 hL hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 hsrc3 hpq hpk _
  obtain ⟨hne, hkeep⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq2, hdeadq2, hdeadq1⟩ := hparent q qn hqv hqn hql
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    eqVisits_reach _ _ _ cv c.p.fuel rk L cv hrrk hL
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hLt : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have hqt' : w.taken.contains q = false := ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  obtain ⟨hN3, htop3, htk3, _, hnext3⟩ := hr3
  have hLn : L < w3.next := by rw [hnext3]; exact hsrc3 L (by rw [hlk3]; rfl)
  have hqn' : q < w3.next := by rw [hnext3]; exact hsrc3 q (by rw [hlq3]; rfl)
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_tree2 c base hvc w3 cv k1 d' L q n qn
    (by rw [hN3, htop3]; exact hT) (by rw [hN3, htop3]; exact reachS_tReach _ _ _ _ hrq) hlk3 hlq3
    (by rw [htk3]; exact hLt) (by rw [htk3]; exact hqt') hnl hql hk1 hqL (htimes L n hrL hn)
    (htimes q qn hrq hqn) (hwf q qn hrq hqn) hpq hpk hne hsa hroomq2 (fun y1 sc y2 => hdeadq2 k1 y1 sc y2)
    hdeadq1 hLn hqn'
    (by rw [hN3, hnext3]; exact hfree _ (Nat.le_refl _)) (by rw [htk3, hnext3]; exact htn _ (Nat.le_refl _))
    (by rw [hN3, hnext3]; exact hfree _ (by omega)) (by rw [htk3, hnext3]; exact htn _ (by omega))
    (by
      intro z hz u c' hu
      rw [hN3, htop3] at hu
      rw [hN3]
      rw [hnext3] at hz
      exact hfreshT z (by omega) u c' hu)) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

theorem putInv_del_leafBelow2_full (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hsa : 1 ≤ c.p.splitAbove)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => PutInv c base w') := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_and_imp _ c w _ _
    (writerWP_del_leafBelow2_tree c base hB.coherent pre cv rk w hmerges hsa hrk (htk _)
      ⟨hidn, hidv, hidt⟩ hbaseF hwf (fun x xn _ hn => hI.times x xn hn) hinner hleaf hparent hI.tree
      hfreshT)
    (putInv_del_leafBelow2 c base B top0 hB pre cv rk w hI hw hmerges hsa hrk hinner hleaf hparent)

end SIS.Tree
