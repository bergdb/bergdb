/-
The writer's tree kept by the space split in place of a segment leaf the
transaction made (bergdb 024-22, `OpTreeOK`), on prover latest's state
`SpaceSplitInPlaceAfter` (`GetInPlace.lean`): L keeps the first half, the next id
holds the second, the parent gets a klong of the divider naming it.
-/
import SIS.Tree.WriterTreeMerge
import SIS.Tree.GetInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check


/-- The tree after a space split in place of a segment leaf below an inner
parent with room. -/
theorem treeOK_inPlaceSplitAfter (p : Params) (base : View BVal) (c : Ctx) (w w' : W)
    (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) (r0 : Nat × NodeId) (hcp : c.p = p)
    (hT : TreeOK (wNode p base w) c.i w.top.rootKey)
    (hA : SpaceSplitInPlaceAfter c w w' L q n qn cv v)
    (hLn : wNode p base w L = some n) (hqn : wNode p base w q = some qn) (hqL : q ≠ L)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode p base w) c.i w.top.rootKey q)
    (hnleaf : n.leaf = true) (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hf1 : wNode p base w w.next = none) (hvN : wNode p base w v = none)
    (ht1 : w.taken.contains w.next = false) (hv1 : v ≠ w.next)
    (hfresh : ∀ z, (z = w.next ∨ z = v) →
      ∀ u c', TReach (wNode p base w) c.i w.top.rootKey u → ¬ TLink (wNode p base w) c.i u c' z) :
    TreeOK (wNode p base w') c.i w'.top.rootKey := by
  subst hcp
  obtain ⟨hsc, hfirst, hsecond⟩ := halves_leaf_live n c.i hnleaf cv v r0 hr0
  unfold SpaceSplitInPlaceAfter at hA
  rw [hnleaf] at hA
  obtain ⟨h'taken, h'top, _, h'nodes⟩ := hA
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, v)] = out at *
  generalize hN : wNode c.p base w = N at *
  generalize hr : w.top.rootKey = r at *
  generalize hy1 : w.next = y1 at *
  rw [h'top, hr]
  have hLt : w.taken.contains L = false := by
    rw [← hN] at hLn; unfold wNode at hLn; split at hLn
    · cases hLn
    · rename_i h; simpa using h
  have hqt' : w.taken.contains q = false := by
    rw [← hN] at hqn; unfold wNode at hqn; split at hqn
    · cases hqn
    · rename_i h; simpa using h
  have hne : ∀ x m z, N x = some m → N z = none → x ≠ z := fun x m z hx hz he => by
    rw [he, hz] at hx; cases hx
  have hL1 := hne L n y1 hLn hf1
  have hLv := hne L n v hLn hvN
  have hq1 := hne q qn y1 hqn hf1
  have hN' : ∀ x, wNode c.p base w' x =
      if x = L then some out.1
      else if x = q then some (qn.add c.i (.key out.2.2 y1))
      else if x = y1 then some out.2.1
      else N x := by
    intro x
    rw [← hN]
    unfold wNode
    rw [h'taken, h'nodes x]
    by_cases hxL : x = L
    · subst hxL; simp only [hLt, Bool.false_eq_true, ↓reduceIte]
    · by_cases hxq : x = q
      · subst hxq; simp only [hqt', hxL, Bool.false_eq_true, ↓reduceIte]
      · by_cases hx1 : x = y1
        · subst hx1; simp only [ht1, hxL, hxq, Bool.false_eq_true, ↓reduceIte]
        · simp only [hxL, hxq, hx1, ↓reduceIte]
  rw [hsc] at hN'
  have hnlive : n.liveAt c.i = n.live := KNode.liveAt_of_times n c.i hnt
  have hqlive : ∀ c' z, (c', z) ∈ (qn.add c.i (.key r0.1 y1)).liveAt c.i →
      (c' = r0.1 ∧ z = y1) ∨ (c' ≠ r0.1 ∧ (c', z) ∈ qn.liveAt c.i) :=
    fun c' z h => KNode.add_key_liveAt_mem qn c.i r0.1 y1 hqwf hqt c' z h
  have hqLlink : TLink N c.i q k1 L := ⟨qn, hqn, hqk⟩
  have hLreach : TReach N c.i r L := TReach.link hq hqLlink
  have hLlink : ∀ c' z, (c', z) ∈ n.live → TLink N c.i L c' z := fun c' z h =>
    ⟨n, hLn, by rw [hnlive]; exact h⟩
  have hfr : ∀ z, (z = y1 ∨ z = v) → ∀ u c', TReach N c.i r u → ¬ TLink N c.i u c' z := hfresh
  have hnotR : ∀ z, (z = y1 ∨ z = v) → ¬ TReach N c.i r z := by
    intro z hz
    rcases hz with h | h <;> rw [h]
    · exact not_reach_fresh N c.i r y1 hT hf1 (hfr y1 (Or.inl rfl))
    · exact not_reach_fresh N c.i r v hT hvN (hfr v (Or.inr rfl))
  apply treeOK_transfer_gone N (wNode c.p base w') c.i r r (fun z => z = y1 ∨ z = v)
    (fun _ => False)
    (fun u c' => if u = L then (if c' < r0.1 then (L, c') else (y1, c')) else (u, c')) hT hnotR
  · exact Or.inl ⟨rfl, id⟩
  · intro u c' z hu _ hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN' u] at hm
    by_cases huL : u = L
    · simp only [huL, ↓reduceIte, Option.some.injEq] at hm
      subst hm
      rcases hfirst c' z hc with ⟨hcz, _⟩ | ⟨hmem, hlt⟩
      · simp only [Prod.mk.injEq] at hcz
        exact Or.inl (Or.inr hcz.2)
      · exact Or.inr ⟨id, L, c', hLreach, hLlink c' z hmem, by simp [huL, hlt]⟩
    · simp only [huL, ↓reduceIte] at hm
      by_cases huq : u = q
      · subst huq
        simp only [↓reduceIte, Option.some.injEq] at hm
        subst hm
        rcases hqlive c' z hc with ⟨_, hz⟩ | ⟨_, hmem⟩
        · exact Or.inl (Or.inl hz)
        · exact Or.inr ⟨id, u, c', hq, ⟨qn, hqn, hmem⟩, by simp [huL]⟩
      · simp only [huq, ↓reduceIte] at hm
        by_cases hu1 : u = y1
        · simp only [hu1, ↓reduceIte, Option.some.injEq] at hm
          subst hm
          rcases hsecond c' z hc with ⟨hcz, _⟩ | ⟨hmem, hge⟩
          · simp only [Prod.mk.injEq] at hcz
            exact Or.inl (Or.inr hcz.2)
          · have hnlt : ¬ c' < r0.1 := by omega
            exact Or.inr ⟨id, L, c', hLreach, hLlink c' z hmem, by simp [hu1, hnlt]⟩
        · simp only [hu1, ↓reduceIte] at hm
          have huR : TReach N c.i r u := by
            rcases hu with h | h
            · exact h
            · rcases h with h | h
              · exact absurd h hu1
              · rw [h, hvN] at hm; cases hm
          exact Or.inr ⟨id, u, c', huR, ⟨m, hm, hc⟩, by simp [huL]⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl hl'
    have hone : ∀ x d, (TReach N c.i r x ∨ (x = y1 ∨ x = v)) →
        TLink (wNode c.p base w') c.i x d z →
        (x = q ∧ d = r0.1 ∧ z = y1) ∨
        (z = v ∧ d = cv ∧ ((x = L ∧ cv < r0.1) ∨ (x = y1 ∧ r0.1 ≤ cv))) := by
      intro x d hx hl0
      obtain ⟨m, hm, hc⟩ := hl0
      rw [hN' x] at hm
      by_cases hxL : x = L
      · simp only [hxL, ↓reduceIte, Option.some.injEq] at hm
        subst hm
        rcases hfirst d z hc with ⟨hcz, hlt⟩ | ⟨hmem, _⟩
        · simp only [Prod.mk.injEq] at hcz
          exact Or.inr ⟨hcz.2, hcz.1, Or.inl ⟨hxL, hlt⟩⟩
        · exact absurd (hLlink d z hmem) (hfr z hz L d hLreach)
      · simp only [hxL, ↓reduceIte] at hm
        by_cases hxq : x = q
        · subst hxq
          simp only [↓reduceIte, Option.some.injEq] at hm
          subst hm
          rcases hqlive d z hc with ⟨hd, hzz⟩ | ⟨_, hmem⟩
          · exact Or.inl ⟨rfl, hd, hzz⟩
          · exact absurd ⟨qn, hqn, hmem⟩ (hfr z hz x d hq)
        · simp only [hxq, ↓reduceIte] at hm
          by_cases hx1 : x = y1
          · simp only [hx1, ↓reduceIte, Option.some.injEq] at hm
            subst hm
            rcases hsecond d z hc with ⟨hcz, hge⟩ | ⟨hmem, _⟩
            · simp only [Prod.mk.injEq] at hcz
              exact Or.inr ⟨hcz.2, hcz.1, Or.inr ⟨hx1, hge⟩⟩
            · exact absurd (hLlink d z hmem) (hfr z hz L d hLreach)
          · simp only [hx1, ↓reduceIte] at hm
            have hxR : TReach N c.i r x := by
              rcases hx with h | h
              · exact h
              · rcases h with h | h
                · exact absurd h hx1
                · rw [h, hvN] at hm; cases hm
            exact absurd ⟨m, hm, hc⟩ (hfr z hz x d hxR)
    rcases hone u c' hu hl with ⟨h1x, h1c, h1z⟩ | ⟨h1z, h1c, h1s⟩ <;>
      rcases hone u' c'' hu' hl' with ⟨h2x, h2c, h2z⟩ | ⟨h2z, h2c, h2s⟩
    · exact ⟨h1x.trans h2x.symm, h1c.trans h2c.symm⟩
    · exact absurd (h2z.symm.trans h1z) hv1
    · exact absurd (h1z.symm.trans h2z) hv1
    · refine ⟨?_, h1c.trans h2c.symm⟩
      rcases h1s with ⟨h1, hlt⟩ | ⟨h1, hge⟩ <;> rcases h2s with ⟨h2, hlt'⟩ | ⟨h2, hge'⟩
      · exact h1.trans h2.symm
      · omega
      · omega
      · exact h1.trans h2.symm
  · intro _ _ h; exact h
  · rw [hN' r]
    by_cases hrL : r = L
    · simp [hrL]
    · simp only [hrL, ↓reduceIte]
      by_cases hrq : r = q
      · simp [hrq]
      · obtain ⟨rm, hrm⟩ := hT.rootKey
        have hr1 := hne r rm y1 hrm hf1
        simp only [hrq, hr1, ↓reduceIte]
        exact ⟨rm, hrm⟩



/-- The rule: a klong (cv, v) of a fresh value put into a full segment leaf that
the transaction made, below an inner parent with room, split in place
(prover latest's `writerWP_appendKlongs_spaceSplitInPlace`): the writer's tree is
kept. -/
theorem writerWP_appendKlongs_spaceSplitInPlace_tree (base : View BVal) (d' : Nat)
    (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) (c : Ctx) (w : W) (r0 : Nat × NodeId)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hmade : n.firstTime = some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M)
    (hdeadq : ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hLn : L < w.next) (hqn : q < w.next)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode c.p base w) c.i w.top.rootKey q)
    (hnleaf : n.leaf = true) (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hf1 : wNode c.p base w w.next = none) (hvN : wNode c.p base w v = none)
    (ht1 : w.taken.contains w.next = false) (hv1 : v ≠ w.next)
    (hfresh : ∀ z, (z = w.next ∨ z = v) →
      ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u → ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by
    simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitInPlace d' L q n qn cv v c w hlk hlq hqL
    hql hmade hfull hsplit hpq hroomq hdeadq hLn hqn) ?_
  intro _ w' hA
  exact treeOK_inPlaceSplitAfter c.p base c w w' L q n qn k1 cv v r0 rfl hT hA hwL hwq hqL hqk hq
    hnleaf hr0 hnt hqt hqwf hf1 hvN ht1 hv1 hfresh

end SIS.Tree
