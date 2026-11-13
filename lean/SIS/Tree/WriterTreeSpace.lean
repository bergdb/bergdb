/-
The writer's tree kept by a space split (bergdb 024-22, `OpTreeOK`): a segment
leaf L that existed before the transaction, with a klong put into it, is split
into two new leaves, the halves of its last version with the klong
(`halves`); its inner parent q, with room, gets its klong of L pointed to the
first and a klong of the divider for the second; L keeps its klongs before the
transaction (`SpaceSplitAfter`). The tree is kept (`treeOK_spaceSplitAfter`, by
`treeOK_transfer_gone`: a klong of L goes to the first half below the divider,
to the second from it).
-/
import SIS.Tree.WriterTreeSplit
import SIS.Tree.SpaceSplitMap
import SIS.Tree.WalkComplete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Nodes -/

/-- A node of one time's klongs: its live klongs are among its pairs. -/
theorem liveAt_newKlongs_mem (leaf : Bool) (t t' : Time) (pairs : List (Nat × NodeId)) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ ({ leaf := leaf, ks := newKlongs t pairs } : KNode).liveAt t') :
    (c, z) ∈ pairs := by
  have hk := KNode.liveAt_key_mem _ t' c z h
  simp only [newKlongs, List.mem_cons, reduceCtorEq, false_or, List.mem_map] at hk
  obtain ⟨q, hq, he⟩ := hk
  rcases q with ⟨a, b⟩
  simp only [Klong.key.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hq

/-- A segment leaf's last version is the one-time node of its live klongs. -/
theorem KNode.lastVersion_leaf (n : KNode) (t : Time) (hl : n.leaf = true) :
    n.lastVersion t = { leaf := true, ks := newKlongs t n.live } := by
  have hk := n.lastVersion_keys t
  have hlf : (n.lastVersion t).leaf = n.leaf := rfl
  cases hv : n.lastVersion t with
  | mk leaf ks =>
    rw [hv] at hk hlf
    simp only at hk hlf
    rw [hlf, hl, hk]
    simp [newKlongs]

/-- Of a sorted list, every pair from the head of its drop on is at or above
that head. -/
theorem drop_ge_head (pairs : List (Nat × NodeId)) (k : Nat)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1)) (r : Nat × NodeId)
    (hr : (pairs.drop k).head? = some r) : ∀ q ∈ pairs.drop k, r.1 ≤ q.1 := by
  have hd : (pairs.drop k).Pairwise (fun a b => a.1 < b.1) := hs.sublist (List.drop_sublist _ _)
  cases he : pairs.drop k with
  | nil => rw [he] at hr; cases hr
  | cons a rest =>
    rw [he] at hr hd
    simp only [List.head?_cons, Option.some.injEq] at hr
    subst hr
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · rw [h]; exact Nat.le_refl _
    · exact Nat.le_of_lt ((List.pairwise_cons.mp hd).1 q h)

/-- The halves of a segment leaf's last version with a klong put: every live
klong of the first is the put's or a live klong of the leaf, below the
divider; of the second, at or above it. -/
theorem halves_leaf_live (n : KNode) (t : Time) (hl : n.leaf = true) (cv : Nat) (v : NodeId)
    (r : Nat × NodeId) (hr : (n.live.drop (n.live.length / 2)).head? = some r) :
    let out := halves true t (n.lastVersion t) [(cv, v)]
    out.2.2 = r.1 ∧
    (∀ c z, (c, z) ∈ out.1.liveAt t → ((c, z) = (cv, v) ∧ cv < r.1) ∨ ((c, z) ∈ n.live ∧ c < r.1)) ∧
    (∀ c z, (c, z) ∈ out.2.1.liveAt t →
      ((c, z) = (cv, v) ∧ r.1 ≤ cv) ∨ ((c, z) ∈ n.live ∧ r.1 ≤ c)) := by
  intro out
  have hshape := halves_leaf_shape t n.live [(cv, v)] r hr
  have hout : out = halves true t ⟨true, newKlongs t n.live⟩ [(cv, v)] := by
    show halves true t (n.lastVersion t) [(cv, v)] = _
    rw [n.lastVersion_leaf t hl]
  rw [hshape] at hout
  have hlt := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  have hge := drop_ge_head n.live (n.live.length / 2) n.live_order r hr
  by_cases hside : r.1 ≤ cv
  · simp only [List.head?_cons] at hout
    have hd : decide (r.1 ≤ cv) = true := by simpa using hside
    simp only [hd, ↓reduceIte] at hout
    rw [hout]
    refine ⟨rfl, ?_, ?_⟩
    · intro c z h
      have hm := liveAt_newKlongs_mem true t t _ c z h
      exact Or.inr ⟨List.mem_of_mem_take hm, hlt (c, z) hm⟩
    · intro c z h
      have hm := liveAt_newKlongs_mem true t t _ c z h
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inr ⟨List.mem_of_mem_drop hm, hge (c, z) hm⟩
      · simp only [List.mem_singleton] at hm
        exact Or.inl ⟨hm, hside⟩
  · simp only [List.head?_cons] at hout
    have hd : decide (r.1 ≤ cv) = false := by simpa using hside
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hout
    rw [hout]
    refine ⟨rfl, ?_, ?_⟩
    · intro c z h
      have hm := liveAt_newKlongs_mem true t t _ c z h
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inr ⟨List.mem_of_mem_take hm, hlt (c, z) hm⟩
      · simp only [List.mem_singleton] at hm
        exact Or.inl ⟨hm, by omega⟩
    · intro c z h
      have hm := liveAt_newKlongs_mem true t t _ c z h
      exact Or.inr ⟨List.mem_of_mem_drop hm, hge (c, z) hm⟩

/-! ## The state after a space split, and its tree -/

/-- The state after a space split of a segment leaf L, that existed before the
transaction and gets the klong (cv, v), below an inner parent q with room: the
halves at the next two ids, q's klong k1 pointing to the first and a klong of
the divider naming the second, L with its klongs before the transaction. -/
def SpaceSplitAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) : Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some ((qn.add c.i (.key k1 w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2)))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else w.nodes.lookup x

/-- The tree after a space split of a segment leaf below an inner parent with
room. The premises are the time split's (`treeOK_timeSplitAfter`), with the
second half nonempty and the next two ids fresh. -/
theorem treeOK_spaceSplitAfter (p : Params) (base : View BVal) (c : Ctx) (w w' : W)
    (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) (r0 : Nat × NodeId) (hcp : c.p = p)
    (hT : TreeOK (wNode p base w) c.i w.top.rootKey)
    (hA : SpaceSplitAfter c w w' L q n qn k1 cv v)
    (hLn : wNode p base w L = some n) (hqn : wNode p base w q = some qn) (hqL : q ≠ L)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode p base w) c.i w.top.rootKey q)
    (hnleaf : n.leaf = true) (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hf1 : wNode p base w w.next = none) (hf2 : wNode p base w (w.next + 2) = none)
    (hvN : wNode p base w v = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (hv1 : v ≠ w.next) (hv2 : v ≠ w.next + 2)
    (hfresh : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = v) →
      ∀ u c', TReach (wNode p base w) c.i w.top.rootKey u → ¬ TLink (wNode p base w) c.i u c' z) :
    TreeOK (wNode p base w') c.i w'.top.rootKey := by
  subst hcp
  obtain ⟨hsc, hfirst, hsecond⟩ := halves_leaf_live n c.i hnleaf cv v r0 hr0
  unfold SpaceSplitAfter at hA
  rw [hnleaf] at hA
  obtain ⟨h'taken, h'top, _, h'nodes⟩ := hA
  generalize hout : halves true c.i (n.lastVersion c.i) [(cv, v)] = out at *
  generalize hN : wNode c.p base w = N at *
  generalize hr : w.top.rootKey = r at *
  generalize hy1 : w.next = y1 at *
  rw [h'top, hr]
  have hy12 : y1 ≠ y1 + 2 := by omega
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
  have hL2 := hne L n (y1 + 2) hLn hf2
  have hLv := hne L n v hLn hvN
  have hq1 := hne q qn y1 hqn hf1
  have hq2 := hne q qn (y1 + 2) hqn hf2
  have hqv := hne q qn v hqn hvN
  have hN' : ∀ x, wNode c.p base w' x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some ((qn.add c.i (.key k1 y1)).add c.i (.key out.2.2 (y1 + 2)))
      else if x = y1 then some out.1
      else if x = y1 + 2 then some out.2.1
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
        · by_cases hx2 : x = y1 + 2
          · subst hx2; simp only [ht2, hxL, hxq, hx1, Bool.false_eq_true, ↓reduceIte]
          · simp only [hxL, hxq, hx1, hx2, ↓reduceIte]
  have hnlive : n.liveAt c.i = n.live := KNode.liveAt_of_times n c.i hnt
  rw [hsc] at hN'
  -- q's live klongs after
  have hq1wf := KNode.add_key_wf qn c.i k1 y1 hqwf
  have hq1t := KNode.add_times qn c.i (.key k1 y1) (fun s h => by cases h) hqt
  have hqlive : ∀ c' z, (c', z) ∈ ((qn.add c.i (.key k1 y1)).add c.i (.key r0.1 (y1 + 2))).liveAt c.i →
      (c' = r0.1 ∧ z = y1 + 2) ∨ (c' = k1 ∧ z = y1) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt c.i) := by
    intro c' z h
    rcases KNode.add_key_liveAt_mem _ c.i r0.1 (y1 + 2) hq1wf hq1t c' z h with h1 | ⟨_, h1⟩
    · exact Or.inl h1
    · rcases KNode.add_key_liveAt_mem qn c.i k1 y1 hqwf hqt c' z h1 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  -- the tree before
  have hqLlink : TLink N c.i q k1 L := ⟨qn, hqn, hqk⟩
  have hLreach : TReach N c.i r L := TReach.link hq hqLlink
  have hLparent : ∀ u c', TReach N c.i r u → TLink N c.i u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqLlink
  have hLlink : ∀ c' z, (c', z) ∈ n.live → TLink N c.i L c' z := fun c' z h =>
    ⟨n, hLn, by rw [hnlive]; exact h⟩
  have hnotL : ∀ c' , ¬ TLink N c.i L c' L := fun c' hl =>
    hqL (hLparent L c' hLreach hl).1.symm
  have hfr : ∀ z, (z = y1 ∨ z = y1 + 2 ∨ z = v) → ∀ u c', TReach N c.i r u → ¬ TLink N c.i u c' z :=
    hfresh
  have hnotR : ∀ z, (z = y1 ∨ z = y1 + 2 ∨ z = v) → ¬ TReach N c.i r z := by
    intro z hz
    rcases hz with h | h | h <;> rw [h]
    · exact not_reach_fresh N c.i r y1 hT hf1 (hfr y1 (Or.inl rfl))
    · exact not_reach_fresh N c.i r (y1 + 2) hT hf2 (hfr (y1 + 2) (Or.inr (Or.inl rfl)))
    · exact not_reach_fresh N c.i r v hT hvN (hfr v (Or.inr (Or.inr rfl)))
  apply treeOK_transfer_gone N (wNode c.p base w') c.i r r (fun z => z = y1 ∨ z = y1 + 2 ∨ z = v)
    (fun z => z = L)
    (fun u c' => if u = L then (if c' < r0.1 then (y1, c') else (y1 + 2, c')) else (u, c')) hT
    hnotR
  · refine Or.inl ⟨rfl, fun h => ?_⟩
    exact hT.rootFree q k1 hq (by rw [h]; exact hqLlink)
  · intro u c' z hu hug hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN' u] at hm
    by_cases huL : u = L
    · exact absurd huL hug
    simp only [huL, ↓reduceIte] at hm
    have hold : ∀ y0 c0, TReach N c.i r y0 → TLink N c.i y0 c0 z → y0 ≠ q → ¬ (z = L) := by
      intro y0 c0 hy0 hl0 hy0q hzL
      rw [hzL] at hl0
      exact hy0q (hLparent y0 c0 hy0 hl0).1
    by_cases huq : u = q
    · subst huq
      simp only [↓reduceIte, Option.some.injEq] at hm
      subst hm
      rcases hqlive c' z hc with ⟨_, hz⟩ | ⟨_, hz⟩ | ⟨hck, hmem⟩
      · exact Or.inl (Or.inr (Or.inl hz))
      · exact Or.inl (Or.inl hz)
      · right
        have hlink : TLink N c.i u c' z := ⟨qn, hqn, hmem⟩
        refine ⟨fun hzL => ?_, u, c', hq, hlink, by simp [hqL]⟩
        rw [hzL] at hlink
        exact hck (hLparent u c' hq hlink).2
    · simp only [huq, ↓reduceIte] at hm
      by_cases hu1 : u = y1
      · simp only [hu1, ↓reduceIte, Option.some.injEq] at hm
        subst hm
        rcases hfirst c' z hc with ⟨hcz, _⟩ | ⟨hmem, hlt⟩
        · simp only [Prod.mk.injEq] at hcz
          exact Or.inl (Or.inr (Or.inr hcz.2))
        · right
          refine ⟨fun hzL => ?_, L, c', hLreach, hLlink c' z hmem, by simp [hu1, hlt]⟩
          rw [hzL] at hmem
          exact hnotL c' (hLlink c' L hmem)
      · simp only [hu1, ↓reduceIte] at hm
        by_cases hu2 : u = y1 + 2
        · simp only [hu2, ↓reduceIte, Option.some.injEq] at hm
          subst hm
          rcases hsecond c' z hc with ⟨hcz, _⟩ | ⟨hmem, hge⟩
          · simp only [Prod.mk.injEq] at hcz
            exact Or.inl (Or.inr (Or.inr hcz.2))
          · right
            have hnlt : ¬ c' < r0.1 := by omega
            refine ⟨fun hzL => ?_, L, c', hLreach, hLlink c' z hmem, by simp [hu2, hnlt]⟩
            rw [hzL] at hmem
            exact hnotL c' (hLlink c' L hmem)
        · simp only [hu2, ↓reduceIte] at hm
          have huR : TReach N c.i r u := by
            rcases hu with h | h
            · exact h
            · rcases h with h | h | h
              · exact absurd h hu1
              · exact absurd h hu2
              · rw [h, hvN] at hm; cases hm
          have hlink : TLink N c.i u c' z := ⟨m, hm, hc⟩
          right
          exact ⟨hold u c' huR hlink huq, u, c', huR, hlink, by simp [huL]⟩
  · intro u c' u' c'' z hu hug hu' hug' hz hl hl'
    have hone : ∀ x d, (TReach N c.i r x ∨ (x = y1 ∨ x = y1 + 2 ∨ x = v)) → x ≠ L →
        TLink (wNode c.p base w') c.i x d z →
        (x = q ∧ d = k1 ∧ z = y1) ∨ (x = q ∧ d = r0.1 ∧ z = y1 + 2) ∨
        (z = v ∧ d = cv ∧ ((x = y1 ∧ cv < r0.1) ∨ (x = y1 + 2 ∧ r0.1 ≤ cv))) := by
      intro x d hx hxL hl0
      obtain ⟨m, hm, hc⟩ := hl0
      rw [hN' x] at hm
      simp only [hxL, ↓reduceIte] at hm
      by_cases hxq : x = q
      · subst hxq
        simp only [↓reduceIte, Option.some.injEq] at hm
        subst hm
        rcases hqlive d z hc with ⟨hd, hzz⟩ | ⟨hd, hzz⟩ | ⟨_, hmem⟩
        · exact Or.inr (Or.inl ⟨rfl, hd, hzz⟩)
        · exact Or.inl ⟨rfl, hd, hzz⟩
        · exact absurd ⟨qn, hqn, hmem⟩ (hfr z hz x d hq)
      · simp only [hxq, ↓reduceIte] at hm
        by_cases hx1 : x = y1
        · simp only [hx1, ↓reduceIte, Option.some.injEq] at hm
          subst hm
          rcases hfirst d z hc with ⟨hcz, hlt⟩ | ⟨hmem, _⟩
          · simp only [Prod.mk.injEq] at hcz
            exact Or.inr (Or.inr ⟨hcz.2, hcz.1, Or.inl ⟨hx1, hlt⟩⟩)
          · exact absurd (hLlink d z hmem) (hfr z hz L d hLreach)
        · simp only [hx1, ↓reduceIte] at hm
          by_cases hx2 : x = y1 + 2
          · simp only [hx2, ↓reduceIte, Option.some.injEq] at hm
            subst hm
            rcases hsecond d z hc with ⟨hcz, hge⟩ | ⟨hmem, _⟩
            · simp only [Prod.mk.injEq] at hcz
              exact Or.inr (Or.inr ⟨hcz.2, hcz.1, Or.inr ⟨hx2, hge⟩⟩)
            · exact absurd (hLlink d z hmem) (hfr z hz L d hLreach)
          · simp only [hx2, ↓reduceIte] at hm
            have hxR : TReach N c.i r x := by
              rcases hx with h | h
              · exact h
              · rcases h with h | h | h
                · exact absurd h hx1
                · exact absurd h hx2
                · rw [h, hvN] at hm; cases hm
            exact absurd ⟨m, hm, hc⟩ (hfr z hz x d hxR)
    rcases hone u c' hu hug hl with ⟨h1x, h1c, h1z⟩ | ⟨h1x, h1c, h1z⟩ | ⟨h1z, h1c, h1s⟩ <;>
      rcases hone u' c'' hu' hug' hl' with ⟨h2x, h2c, h2z⟩ | ⟨h2x, h2c, h2z⟩ | ⟨h2z, h2c, h2s⟩
    · exact ⟨h1x.trans h2x.symm, h1c.trans h2c.symm⟩
    · exact absurd (h1z.symm.trans h2z) hy12
    · exact absurd (h2z.symm.trans h1z) hv1
    · exact absurd (h2z.symm.trans h1z) hy12
    · exact ⟨h1x.trans h2x.symm, h1c.trans h2c.symm⟩
    · exact absurd (h2z.symm.trans h1z) hv2
    · exact absurd (h1z.symm.trans h2z) hv1
    · exact absurd (h1z.symm.trans h2z) hv2
    · refine ⟨?_, h1c.trans h2c.symm⟩
      rcases h1s with ⟨h1, hlt⟩ | ⟨h1, hge⟩ <;> rcases h2s with ⟨h2, hlt'⟩ | ⟨h2, hge'⟩
      · exact h1.trans h2.symm
      · omega
      · omega
      · exact h1.trans h2.symm
  · intro z hz hzL
    rw [hzL] at hz
    rcases hz with h | h | h
    · exact hL1 h
    · exact hL2 h
    · exact hLv h
  · by_cases hrL : r = L
    · exact absurd (by rw [hrL]; exact hqLlink) (hT.rootFree q k1 hq)
    · rw [hN' r]
      simp only [hrL, ↓reduceIte]
      by_cases hrq : r = q
      · simp [hrq]
      · obtain ⟨rm, hrm⟩ := hT.rootKey
        have hr1 := hne r rm y1 hrm hf1
        have hr2 := hne r rm (y1 + 2) hrm hf2
        simp only [hrq, hr1, hr2, ↓reduceIte]
        exact ⟨rm, hrm⟩

/-! ## The writer's space split -/

/-- Two klongs added to a node with room: the node gets them, nothing else
changes but the cache of the node. -/
theorem writerWP_appendKlongs_room2 (d : Nat) (q : NodeId) (qn : KNode) (k1 y1 k2 y2 : Nat)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup q = some qn) (hroom : qn.size + 2 + 1 ≤ c.p.M)
    (hdead : deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key k2 y2)) = false) :
    WriterWP (appendKlongs d q [(k1, y1), (k2, y2)]) c w (fun _ w' =>
      w' = { w with nodes := upsert w.nodes q ((qn.add c.i (.key k1 y1)).add c.i (.key k2 y2)) }) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  have h1 : ¬ (qn.size + [(k1, y1), (k2, y2)].length + 1 > c.p.M) := by simp; omega
  simp only [h1, decide_false, ↓reduceIte, List.foldl_cons, List.foldl_nil, hdead,
    Bool.false_eq_true]
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  simp only [putNode, List.foldl_cons, List.foldl_nil, writerWP_modify]

/-- The writer's space split of a segment leaf L that existed before the
transaction, below an inner parent q with room for two klongs: the state is
`SpaceSplitAfter`. -/
theorem writerWP_handleFullWith_spaceSplit (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitAfter c w w' L q n qn k1 cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_room2 d' q qn k1 w.next _ (w.next + 2) c _
        (by
          simp only [lookup_upsert]
          have h1 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
          have h2 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
          simp [h1, h2, List.lookup_append, hlq]) hroomq (hdeadq _ _ _)) ?_
      intro _ w2 hw2
      subst hw2
      rw [writerWP_getNode_known L n c _ (by
        simp only [lookup_upsert]
        have h1 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
        have h2 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
        simp [hqL.symm, h1, h2, List.lookup_append, hlk])]
      simp only [putNode, writerWP_modify]
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro x
      simp only [lookup_upsert, List.lookup_append]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hx2 : x = w.next + 2
          · have hx1 : x ≠ w.next := by omega
            simp [hx2]
          · simp only [hx2, ↓reduceIte]
            by_cases hx1 : x = w.next
            · simp [hx1]
            · simp only [hx1, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                have hb1 : (x == w.next) = false := by simpa using hx1
                have hb2 : (x == w.next + 2) = false := by simpa using hx2
                simp [List.lookup, hb1, hb2])

/-- The klongs put into a full segment leaf that existed before the
transaction, with a last version above h: the writer's space split. -/
theorem writerWP_appendKlongs_spaceSplit (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : c.p.M < n.size + 1 + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSplitAfter c w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hf : (n.size + [(cv, v)].length + 1 > c.p.M) := by simp; omega
  simp only [hf, decide_true, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplit d' L q n qn k1 cv v c w hlk hlq hqL hql hfirst hsplit
    hpq hpk hroomq hdeadq hn1 hn2

/-- The rule: a klong (cv, v) of a fresh value put into a full segment leaf that
existed before the transaction, below an inner parent with room, space split:
the writer's tree is kept. -/
theorem writerWP_appendKlongs_spaceSplit_tree (base : View BVal) (d' : Nat) (L q : NodeId)
    (n qn : KNode) (k1 cv v : Nat) (c : Ctx) (w : W) (r0 : Nat × NodeId)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : c.p.M < n.size + 1 + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode c.p base w) c.i w.top.rootKey q)
    (hnleaf : n.leaf = true) (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hf1 : wNode c.p base w w.next = none) (hf2 : wNode c.p base w (w.next + 2) = none)
    (hvN : wNode c.p base w v = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (hv1 : v ≠ w.next) (hv2 : v ≠ w.next + 2)
    (hfresh : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = v) →
      ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u → ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by
    simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  have hn1 : w.nodes.lookup w.next = none := by
    unfold wNode at hf1; simp only [ht1, Bool.false_eq_true, ↓reduceIte] at hf1
    split at hf1
    · cases hf1
    · assumption
  have hn2 : w.nodes.lookup (w.next + 2) = none := by
    unfold wNode at hf2; simp only [ht2, Bool.false_eq_true, ↓reduceIte] at hf2
    split at hf2
    · cases hf2
    · assumption
  refine writerWP_mono (writerWP_appendKlongs_spaceSplit d' L q n qn k1 cv v c w hlk hlq hqL hql
    hfirst hfull hsplit hpq hpk hroomq hdeadq hn1 hn2) ?_
  intro _ w' hA
  exact treeOK_spaceSplitAfter c.p base c w w' L q n qn k1 cv v r0 rfl hT hA hwL hwq hqL hqk hq
    hnleaf hr0 hnt hqt hqwf hf1 hf2 hvN ht1 ht2 hv1 hv2 hfresh

/-- The rule: a klong (cv, v) of a fresh value put into a full segment leaf that
existed before the transaction, below an inner parent with room, time split
(`GetSplit.lean`'s `writerWP_appendKlongs_timeSplit`): the writer's tree is
kept. -/
theorem writerWP_appendKlongs_timeSplit_tree (base : View BVal) (d' : Nat) (L q : NodeId)
    (n qn : KNode) (k1 cv v : Nat) (c : Ctx) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hqk : (k1, L) ∈ qn.liveAt c.i) (hq : TReach (wNode c.p base w) c.i w.top.rootKey q)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqwf : klongsWf qn.ks = true)
    (hf1 : wNode c.p base w w.next = none) (ht1 : w.taken.contains w.next = false)
    (hvN : wNode c.p base w v = none) (hv1 : v ≠ w.next)
    (hfresh1 : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' w.next)
    (hfreshv : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' v) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by
    simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  have hn1 : w.nodes.lookup w.next = none := by
    unfold wNode at hf1; simp only [ht1, Bool.false_eq_true, ↓reduceIte] at hf1
    split at hf1
    · cases hf1
    · assumption
  refine writerWP_mono (writerWP_appendKlongs_timeSplit d' L q n qn k1 cv v c w hlk hlq hqL hql
    hfirst hfull hsplit hpq hpk hroomq hdeadq hn1) ?_
  intro _ w' hA
  exact treeOK_timeSplitAfter c.p base c w w' L q n qn k1 cv v rfl hT hA hwL hwq hqL hqk hq hnt hqt
    hqwf hf1 ht1 hfresh1 hvN hv1 hfreshv

end SIS.Tree
