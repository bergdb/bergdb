/-
The merge with a full parent (bergdb 024-22): `mergeParent`'s `full`, the
parent's last version with the new pointers, split with its cascade. Here: the
last version's live klongs, the same as `mergeParentNode`'s.
-/
import SIS.Tree.WriterTreeFullSplit
import SIS.Tree.WriterGetMergeTail
import SIS.Tree.PairReplace
import SIS.Tree.SpaceSplitMap
import SIS.Tree.MergeLiveOrder
import SIS.Tree.WriterGetMergeMade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The last version that `mergeParent`'s `full` hands to `handleFull`: the
parent's last version without the right child's compare value (unless the
second new node takes it), the left one's pointer to m1, and m2's. None where
`mergeParent` throws. -/
def mergeFullLast (pn : KNode) (tt : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) : Option KNode :=
  let deleteR := match m2 with
    | some (_, g) => g != cR
    | none => true
  let union := if deleteR then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap
  let last0 := pn.lastVersionGivenDel tt union
  match replaceKlong last0.ks tt cL m1 with
  | .ok (some ks) =>
    let last1 : KNode := { last0 with ks := ks }
    match m2 with
    | some (y, g) =>
      if deleteR then some { last1 with ks := insertSorted last1.ks g y }
      else match replaceKlong last1.ks tt cR y with
        | .ok (some ks2) => some { last1 with ks := ks2 }
        | _ => none
    | none => some last1
  | _ => none

/-- Inserting a pair at its place in pairs ordered by compare value. -/
def insPairs : List (Nat × NodeId) → Nat → NodeId → List (Nat × NodeId)
  | [], cv, y => [(cv, y)]
  | q :: r, cv, y => if cv < q.1 then (cv, y) :: q :: r else q :: insPairs r cv y

theorem insertSorted_pairs (cv : Nat) (y : NodeId) :
    ∀ pairs : List (Nat × NodeId),
      insertSorted (pairs.map (fun q => Klong.key q.1 q.2)) cv y =
        (insPairs pairs cv y).map (fun q => Klong.key q.1 q.2) := by
  intro pairs
  induction pairs with
  | nil => rfl
  | cons q r ih =>
    by_cases hc : cv < q.1
    · simp [insertSorted, insPairs, hc]
    · simp [insertSorted, insPairs, hc, ih]

theorem pairLookupFold_none_match (c : Nat) :
    ∀ (l : List (Nat × NodeId)) (acc : Option NodeId), (∀ q ∈ l, q.1 ≠ c) →
      l.foldl (pairLookupStep c) acc = acc := by
  intro l
  induction l with
  | nil => intro acc _; rfl
  | cons q r ih =>
    intro acc h
    simp only [List.foldl_cons]
    have hq : (q.1 == c) = false := by simpa using h q List.mem_cons_self
    rw [show pairLookupStep c acc q = acc by simp [pairLookupStep, hq]]
    exact ih acc (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

theorem pairLookupFold_insPairs (c cv : Nat) (y : NodeId) :
    ∀ (pairs : List (Nat × NodeId)) (acc : Option NodeId), pairs.Pairwise (fun a b => a.1 < b.1) →
      (insPairs pairs cv y).foldl (pairLookupStep c) acc =
        if c = cv then some y else pairs.foldl (pairLookupStep c) acc := by
  intro pairs
  induction pairs with
  | nil =>
    intro acc _
    by_cases hc : c = cv
    · subst hc; simp [insPairs, pairLookupStep]
    · simp [insPairs, pairLookupStep, hc, Ne.symm hc]
  | cons q r ih =>
    intro acc hs
    by_cases hlt : cv < q.1
    · simp only [insPairs, hlt, ↓reduceIte, List.foldl_cons]
      by_cases hc : c = cv
      · subst hc
        simp only [↓reduceIte]
        have hst : pairLookupStep c acc (c, y) = some y := by simp [pairLookupStep]
        rw [hst]
        apply pairLookupFold_none_match c (q :: r) (some y)
        intro q' hq'
        rcases List.mem_cons.mp hq' with h | h
        · rw [h]; omega
        · have := List.rel_of_pairwise_cons hs h; omega
      · have hst : pairLookupStep c acc (cv, y) = acc := by
          simp [pairLookupStep, Ne.symm hc]
        simp only [hst, hc, ↓reduceIte]
    · simp only [insPairs, hlt, ↓reduceIte, List.foldl_cons]
      exact ih _ (List.Pairwise.of_cons hs)

/-- The live klongs of `mergeFullLast`: those of `mergeParentNode`
(`mpNode_live_lookup`): the second new node at g, the first at the left child's
compare value, the right one's deleted, the others the parent's. -/
theorem mergeFullLast_lookup (pn : KNode) (tt : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (last : KNode) (h : mergeFullLast pn tt cL m1 cR m2 = some last) :
    last.leaf = pn.leaf ∧
    (m2 = none → ∀ c, last.live.lookup c =
      if c = cL then some m1 else if c = cR then none else pn.live.lookup c) ∧
    (∀ y g, m2 = some (y, g) → ∀ c, last.live.lookup c =
      if c = g then some y else if c = cL then some m1 else if c = cR then none else pn.live.lookup c) := by
  unfold mergeFullLast at h
  simp only at h
  generalize hdR : (match m2 with
    | some (_, g) => g != cR
    | none => true) = deleteR at h
  generalize hun : (if deleteR = true then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap) = union at h
  obtain ⟨pairs, hks, hord⟩ := pn.lastVersionGivenDel_order tt union
  have hnd : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hord.imp (by intro a b hab; omega))
  -- the last version's lookups
  have hl0 : ∀ c, pairs.lookup c = if deleteR = true ∧ c = cR then none else pn.live.lookup c := by
    intro c
    have h1 := (pn.lastVersionGivenDel tt union).live_lookup c
    have h2 := KNode.lastVersionGivenDel_live_lookup pn tt union c
    have h3 : (pn.lastVersionGivenDel tt union).live.lookup c = pairs.foldl (pairLookupStep c) none := by
      have he : pn.lastVersionGivenDel tt union = ⟨pn.leaf, newKlongs tt pairs⟩ := by
        cases hv : pn.lastVersionGivenDel tt union with
        | mk lf ks =>
          rw [hv] at hks
          have hlf : lf = pn.leaf := by
            have : (pn.lastVersionGivenDel tt union).leaf = pn.leaf := rfl
            rw [hv] at this; exact this
          simp only at hks
          rw [hlf, hks]; rfl
      rw [he, KNode.newKlongs_live_lookup_fold]
    rw [← pairLookupFold_eq_lookup pairs c hnd, ← h3, h2, ← hun]
    cases deleteR with
    | true =>
      simp only [↓reduceIte, true_and]
      rw [keyLookup_delete_union]
      by_cases hc : c = cR <;> simp [hc]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, false_and]
      exact (KNode.live_lookup pn c).symm
  rw [hks] at h
  change (match replaceKlong (newKlongs tt pairs) tt cL m1 with
    | .ok (some ks) => _
    | _ => none) = some last at h
  rw [replaceKlong_newKlongs] at h
  cases hr1 : replacePairFirst pairs cL m1 with
  | none => rw [hr1] at h; cases h
  | some out =>
    rw [hr1] at h
    simp only [Option.map_some] at h
    obtain ⟨hkeys1, hlk1⟩ := replacePairFirst_some pairs out cL m1 hr1
    have hnd1 : (out.map Prod.fst).Nodup := by rw [hkeys1]; exact hnd
    have hord1 : out.Pairwise (fun a b => a.1 < b.1) := by
      have : (out.map Prod.fst).Pairwise (· < ·) := by
        rw [hkeys1]; exact List.pairwise_map.mpr hord
      exact List.pairwise_map.mp this
    have hlast1 : ∀ c, (⟨pn.leaf, newKlongs tt out⟩ : KNode).live.lookup c =
        if c = cL then some m1 else if deleteR = true ∧ c = cR then none else pn.live.lookup c := by
      intro c
      rw [KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup out c hnd1, hlk1 c, hl0 c]
      by_cases hc : c = cL
      · subst hc; simp
      · simp [hc, Ne.symm hc]
    cases m2 with
    | none =>
      simp only [Option.some.injEq] at h
      rw [← h]
      refine ⟨rfl, fun _ c => ?_, fun y g hh => (by cases hh)⟩
      show (⟨pn.leaf, newKlongs tt out⟩ : KNode).live.lookup c = _
      rw [hlast1 c]
      have hd : deleteR = true := by rw [← hdR]
      simp [hd]
    | some yg =>
      obtain ⟨y, g⟩ := yg
      simp only at h
      cases hd : deleteR with
      | true =>
        rw [hd] at h
        simp only [↓reduceIte, Option.some.injEq] at h
        rw [← h]
        refine ⟨rfl, fun hh => (by cases hh), fun y' g' hh c => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        have hgc : g ≠ cR := by
          have := hdR; simp only at this; rw [hd] at this; simpa using this
        change (⟨pn.leaf, insertSorted (newKlongs tt out) g y⟩ : KNode).live.lookup c = _
        have hins : insertSorted (newKlongs tt out) g y = newKlongs tt (insPairs out g y) := by
          simp only [newKlongs, insertSorted]
          rw [insertSorted_pairs]
        rw [hins, KNode.newKlongs_live_lookup_fold, pairLookupFold_insPairs c g y out none hord1,
          pairLookupFold_eq_lookup out c hnd1, hlk1 c, hl0 c, hd]
        by_cases h1 : c = g
        · simp [h1]
        · by_cases h2 : c = cL
          · subst h2; simp [h1]
          · simp [h1, h2, Ne.symm h2]
      | false =>
        rw [hd] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hgc : g = cR := by
          have := hdR; simp only at this; rw [hd] at this; simpa using this
        change (match replaceKlong (newKlongs tt out) tt cR y with
          | .ok (some ks2) => _
          | _ => none) = some last at h
        rw [replaceKlong_newKlongs] at h
        cases hr2 : replacePairFirst out cR y with
        | none => rw [hr2] at h; cases h
        | some out2 =>
          rw [hr2] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]
          obtain ⟨hkeys2, hlk2⟩ := replacePairFirst_some out out2 cR y hr2
          have hnd2 : (out2.map Prod.fst).Nodup := by rw [hkeys2]; exact hnd1
          refine ⟨rfl, fun hh => (by cases hh), fun y' g' hh c => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          change (⟨pn.leaf, newKlongs tt out2⟩ : KNode).live.lookup c = _
          rw [KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup out2 c hnd2, hlk2 c,
            hlk1 c, hl0 c, hd]
          subst hgc
          by_cases h1 : c = g
          · subst h1; simp
          · by_cases h2 : c = cL
            · subst h2; simp [h1, Ne.symm h1]
            · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem writerWP_ite_cases {α : Type} (b : Prop) [Decidable b] (x y : M α) (c : Ctx) (w : W)
    (post : α → W → Prop) (hx : b → WriterWP x c w post) (hy : ¬ b → WriterWP y c w post) :
    WriterWP (if b then x else y) c w post := by
  by_cases h : b
  · simp only [h, ↓reduceIte]; exact hx h
  · simp only [h, ↓reduceIte]; exact hy h

/-- `mergeFullLast` is a last version: a time klong of tt, then key klongs. -/
theorem mergeFullLast_ks (pn : KNode) (tt : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (last : KNode) (h : mergeFullLast pn tt cL m1 cR m2 = some last) :
    ∃ pairs, last.ks = newKlongs tt pairs := by
  unfold mergeFullLast at h
  simp only at h
  generalize hdR : (match m2 with
    | some (_, g) => g != cR
    | none => true) = deleteR at h
  generalize hun : (if deleteR = true then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap) = union at h
  obtain ⟨pairs, hks, _⟩ := pn.lastVersionGivenDel_order tt union
  rw [hks] at h
  change (match replaceKlong (newKlongs tt pairs) tt cL m1 with
    | .ok (some ks) => _
    | _ => none) = some last at h
  rw [replaceKlong_newKlongs] at h
  cases hr1 : replacePairFirst pairs cL m1 with
  | none => rw [hr1] at h; cases h
  | some out =>
    rw [hr1] at h
    simp only [Option.map_some] at h
    cases m2 with
    | none =>
      simp only [Option.some.injEq] at h
      rw [← h]; exact ⟨out, rfl⟩
    | some yg =>
      obtain ⟨y, g⟩ := yg
      simp only at h
      cases hd : deleteR with
      | true =>
        rw [hd] at h
        simp only [↓reduceIte, Option.some.injEq] at h
        rw [← h]
        refine ⟨insPairs out g y, ?_⟩
        show insertSorted (newKlongs tt out) g y = _
        simp only [newKlongs, insertSorted]
        rw [insertSorted_pairs]
      | false =>
        rw [hd] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        change (match replaceKlong (newKlongs tt out) tt cR y with
          | .ok (some ks2) => _
          | _ => none) = some last at h
        rw [replaceKlong_newKlongs] at h
        cases hr2 : replacePairFirst out cR y with
        | none => rw [hr2] at h; cases h
        | some out2 =>
          rw [hr2] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]; exact ⟨out2, rfl⟩

set_option linter.unusedSimpArgs false in
/-- `mergeParent` by its two ways: with room, the parent's node `mergeParentNode`
in place (`hroomP`); else, or with too many dead klongs, `handleFull` of the
parent's last version `mergeFullLast` (`hfullP`). -/
theorem writerWP_mergeParent_cases (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn)
    (hroomP : ∀ s : String, post () ({ ({ w with trail := s :: w.trail } : W) with
      nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W))
    (hfullP : ∀ (last : KNode) (compact : Bool) (s : String),
      mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull depth p last compact) c ({ w with trail := s :: w.trail } : W) post) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w post := by
  cases m2 with
  | none =>
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_ite_cases
    · intro _
      apply writerWP_ite_cases
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          apply hfullP
          simp only [mergeFullLast] at hks ⊢
          simp only [hks]
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro _
        simp only [note, putNode, writerWP_bind, writerWP_modify]
        exact hroomP _
    · intro _
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        apply hfullP
        simp only [mergeFullLast] at hks ⊢
        simp only [hks]
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
  | some yg =>
    obtain ⟨y, g⟩ := yg
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_ite_cases
    · intro _
      apply writerWP_ite_cases
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          by_cases hg : g = cR
          · have hgb : (g != cR) = false := by simp [hg]
            simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
            split
            · rename_i ks2 hks2
              apply hfullP
              simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
            · exact writerWP_throw _ _ _ _
            · exact writerWP_throw _ _ _ _
          · have hgb : (g != cR) = true := by simp [hg]
            simp only [hgb, ↓reduceIte] at hks ⊢
            apply hfullP
            simp only [mergeFullLast, hgb, ↓reduceIte, hks]
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro _
        simp only [note, putNode, writerWP_bind, writerWP_modify]
        exact hroomP _
    · intro _
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        by_cases hg : g = cR
        · have hgb : (g != cR) = false := by simp [hg]
          simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
          split
          · rename_i ks2 hks2
            apply hfullP
            simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
          · exact writerWP_throw _ _ _ _
          · exact writerWP_throw _ _ _ _
        · have hgb : (g != cR) = true := by simp [hg]
          simp only [hgb, ↓reduceIte] at hks ⊢
          apply hfullP
          simp only [mergeFullLast, hgb, ↓reduceIte, hks]
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _

/-- The merge's last loop with any parent node: each node is taken back (its
parent retargeted to m1) or unlinked; the parent's live klongs after are its
live klongs before, or m1 where one before named a node of the loop. -/
theorem writerWP_mergeCleanup_any (p m1 : NodeId) (t : Time) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W) (n : KNode), (∀ q ∈ xs, q.1 ≠ p) →
    w.nodes.lookup p = some n →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
        (∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.taken.contains y = w.taken.contains y) ∧
        (∀ y, y ≠ p → (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
        ∃ n', w'.nodes.lookup p = some n' ∧ n'.leaf = n.leaf ∧ ∀ c' z, (c', z) ∈ n'.liveAt t →
          (c', z) ∈ n.liveAt t ∨ (z = m1 ∧ ∃ q ∈ xs, (c', q.1) ∈ n.liveAt t)) := by
  intro xs
  induction xs with
  | nil =>
    intro w n _ hlk
    rw [List.forIn_nil]
    refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, n, hlk, rfl, fun _ _ h => Or.inl h⟩
  | cons q qs ih =>
    intro w n hne hlk
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ (w1 : W) (n1 : KNode), w1.top = w.top → w1.next = w.next → w1.vals = w.vals →
        (∀ y, y ≠ q.1 → w1.taken.contains y = w.taken.contains y) →
        (∀ y, y ≠ p → y ≠ q.1 → w1.nodes.lookup y = w.nodes.lookup y) →
        w1.nodes.lookup p = some n1 → n1.leaf = n.leaf →
        (∀ c' z, (c', z) ∈ n1.liveAt t → (c', z) ∈ n.liveAt t ∨ (z = m1 ∧ (c', q.1) ∈ n.liveAt t)) →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
          (∀ y, (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.taken.contains y = w.taken.contains y) ∧
          (∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
          ∃ n', w'.nodes.lookup p = some n' ∧ n'.leaf = n.leaf ∧ ∀ c' z, (c', z) ∈ n'.liveAt t →
            (c', z) ∈ n.liveAt t ∨ (z = m1 ∧ ∃ q' ∈ q :: qs, (c', q'.1) ∈ n.liveAt t)) := by
      intro w1 n1 h1top h1next h1v h1t h1l h1p h1leaf h1sub
      refine writerWP_mono (ih w1 n1 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) h1p) ?_
      intro _ w2 ⟨h2top, h2next, h2v, h2t, h2l, n2, h2p, h2leaf, h2sub⟩
      refine ⟨h2top.trans h1top, h2next.trans h1next, h2v.trans h1v, fun y hy => ?_, fun y hyp hy => ?_,
        n2, h2p, h2leaf.trans h1leaf, fun c' z hm => ?_⟩
      · rw [h2t y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1t y (hy q List.mem_cons_self)]
      · rw [h2l y hyp (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1l y hyp (hy q List.mem_cons_self)]
      · rcases h2sub c' z hm with h | ⟨hz, q', hq', h⟩
        · rcases h1sub c' z h with h' | ⟨hz', h'⟩
          · exact Or.inl h'
          · exact Or.inr ⟨hz', q, List.mem_cons_self, h'⟩
        · rcases h1sub c' q'.1 h with h' | ⟨_, h'⟩
          · exact Or.inr ⟨hz, q', List.mem_cons_of_mem _ hq', h'⟩
          · exact Or.inr ⟨hz, q, List.mem_cons_self, h'⟩
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (writerWP_retarget_frameV p q.1 m1 n c w hlk) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1v, h1l, n1, h1p, h1n⟩
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      refine hrest _ n1 h1top h1next h1v ?_ ?_ h1p ?_ ?_
      · intro y hy
        show (q.1 :: w1.taken).contains y = _
        rw [List.contains_cons, h1t]
        have : (y == q.1) = false := by simpa using hy
        simp [this]
      · intro y hyp _; exact h1l y hyp
      · rcases h1n with he | ⟨ti, he⟩ <;> rw [he]
      · intro c' z hm
        rcases h1n with he | ⟨ti, he⟩
        · rw [he] at hm; exact Or.inl hm
        · rw [he] at hm
          rcases KNode.retarget_liveAt n ti q.1 m1 t c' z hm with h | ⟨hz, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨hz, h⟩
    · have hq2' : q.2 = false := by simpa using hq2
      simp only [writerWP_bind, hq2', Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (writerWP_unlink_frameV q.1 c w) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1v, h1l⟩
      refine (writerWP_pure _ c _ _).mpr ?_
      refine hrest _ n h1top h1next h1v (fun y _ => by rw [h1t]) (fun y hyp hyq => h1l y hyq)
        (by rw [h1l p (Ne.symm hqp)]; exact hlk) rfl (fun c' z hm => Or.inl hm)

/-- After a merge's last loop: the tree is kept when the loop's nodes l and r are
not reached, the parent p's live klongs after are its live klongs before or name
m1 where one before named l or r, and nothing else changed. -/
theorem treeOK_after_cleanup (N N' : NodeId → Option KNode) (t : Time) (root p l r m1 : NodeId)
    (hT : TreeOK N t root) (hl : ¬ TReach N t root l) (hr : ¬ TReach N t root r)
    (hroot : ∃ n, N' root = some n)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ r → N' y = N y)
    (hp : ∀ n', N' p = some n' → ∃ n, N p = some n ∧ ∀ c z, (c, z) ∈ n'.liveAt t →
      (c, z) ∈ n.liveAt t ∨ (z = m1 ∧ ((c, l) ∈ n.liveAt t ∨ (c, r) ∈ n.liveAt t))) :
    TreeOK N' t root := by
  -- every link after from a node reached before is a link before
  have hstep : ∀ x c y, TReach N t root x → TLink N' t x c y → TLink N t x c y := by
    intro x c y hx hlk
    obtain ⟨m, hm, hc⟩ := hlk
    by_cases hxp : x = p
    · subst hxp
      obtain ⟨n, hn, hsub⟩ := hp m hm
      rcases hsub c y hc with h | ⟨_, h | h⟩
      · exact ⟨n, hn, h⟩
      · exact absurd (TReach.link hx ⟨n, hn, h⟩) hl
      · exact absurd (TReach.link hx ⟨n, hn, h⟩) hr
    · have hxl : x ≠ l := fun he => hl (he ▸ hx)
      have hxr : x ≠ r := fun he => hr (he ▸ hx)
      rw [hother x hxp hxl hxr] at hm
      exact ⟨m, hm, hc⟩
  have hreach : ∀ y, TReach N' t root y → TReach N t root y := by
    intro y hy
    induction hy with
    | root => exact TReach.root
    | link hx hlk ih => exact TReach.link ih (hstep _ _ _ ih hlk)
  apply treeOK_of_links N N' t root hT hroot
  · intro x c y hx hlk
    exact ⟨c, hstep x c y (hreach x hx) hlk⟩
  · intro x c c' y hx h1 h2
    have hxN := hreach x hx
    exact (hT.oneLink x c x c' y hxN hxN (hstep x c y hxN h1) (hstep x c' y hxN h2)).2

/-- The tree with a merge's parent p naming the new nodes m1 (and m2) instead of
the merged siblings l and rr: every node it reaches was reached before or is new,
and neither l nor rr is reached. -/
theorem mergeV_reach (N V : NodeId → Option KNode) (t : Time) (root p l rr m1 : NodeId)
    (m2 : Option NodeId) (pn ln rn pn' : KNode) (cL cR : Nat)
    (hT : TreeOK N t root) (hp : TReach N t root p) (hpn : N p = some pn)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn)
    (hVp : V p = some pn')
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t →
      z = m1 ∨ some z = m2 ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hVm : ∀ m mn, (m = m1 ∨ some m = m2) → V m = some mn → ∀ c z, (c, z) ∈ mn.liveAt t →
      (∃ c0, (c0, z) ∈ ln.liveAt t) ∨ (∃ c0, (c0, z) ∈ rn.liveAt t))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → some y ≠ m2 → V y = N y)
    (hm1N : ¬ TReach N t root m1) (hm2N : ∀ m, some m = m2 → ¬ TReach N t root m) :
    ∀ z, TReach V t root z → (TReach N t root z ∨ z = m1 ∨ some z = m2) ∧ z ≠ l ∧ z ≠ rr := by
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t root l := TReach.link hp hlink_l
  have hrR : TReach N t root rr := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  -- a node linked before is neither l nor rr unless p links it by cL or cR
  have hnotLR : ∀ u c z, TReach N t root u → TLink N t u c z → u ≠ p → z ≠ l ∧ z ≠ rr := by
    intro u c z hu hlk hup
    refine ⟨fun he => hup ?_, fun he => hup ?_⟩
    · rw [he] at hlk; exact (hT.oneLink u c p cL l hu hp hlk hlink_l).1
    · rw [he] at hlk; exact (hT.oneLink u c p cR rr hu hp hlk hlink_r).1
  intro z hz
  induction hz with
  | root =>
    refine ⟨Or.inl TReach.root, fun h => ?_, fun h => ?_⟩
    · exact hT.rootFree p cL hp (by rw [← h] at hlink_l; exact hlink_l)
    · exact hT.rootFree p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  | @link u c z hu hlk ih =>
    obtain ⟨hu', hul, hur⟩ := ih
    obtain ⟨un, hun, hcz⟩ := hlk
    by_cases hup : u = p
    · subst hup
      rw [hVp] at hun
      cases hun
      rcases hpn' c z hcz with h | h | ⟨hm, h1, h2⟩
      · subst h
        exact ⟨Or.inr (Or.inl rfl), fun he => hm1N (he ▸ hlR), fun he => hm1N (he ▸ hrR)⟩
      · exact ⟨Or.inr (Or.inr h), fun he => hm2N z h (he ▸ hlR), fun he => hm2N z h (he ▸ hrR)⟩
      · refine ⟨Or.inl (TReach.link hp ⟨pn, hpn, hm⟩), fun he => h1 ?_, fun he => h2 ?_⟩
        · rw [he] at hm; exact (hT.oneLink u c u cL l hp hp ⟨pn, hpn, hm⟩ hlink_l).2
        · rw [he] at hm; exact (hT.oneLink u c u cR rr hp hp ⟨pn, hpn, hm⟩ hlink_r).2
    · by_cases hm : u = m1 ∨ some u = m2
      · rcases hVm u un hm hun c z hcz with ⟨c0, h0⟩ | ⟨c0, h0⟩
        · have hlz : TLink N t l c0 z := ⟨ln, hln, h0⟩
          refine ⟨Or.inl (TReach.link hlR hlz), fun he => ?_, fun he => ?_⟩
          · rw [he] at hlz; exact hT.no_self_link l c0 hlR hlz
          · rw [he] at hlz; exact hpl (hT.oneLink l c0 p cR rr hlR hp hlz hlink_r).1.symm
        · have hrz : TLink N t rr c0 z := ⟨rn, hrn, h0⟩
          refine ⟨Or.inl (TReach.link hrR hrz), fun he => ?_, fun he => ?_⟩
          · rw [he] at hrz; exact hpr (hT.oneLink rr c0 p cL l hrR hp hrz hlink_l).1.symm
          · rw [he] at hrz; exact hT.no_self_link rr c0 hrR hrz
      · have hum1 : u ≠ m1 := fun h => hm (Or.inl h)
        have hum2 : some u ≠ m2 := fun h => hm (Or.inr h)
        have huN : TReach N t root u := by
          rcases hu' with h | h | h
          · exact h
          · exact absurd h hum1
          · exact absurd h hum2
        rw [hother u hup hul hur hum1 hum2] at hun
        have hlk' : TLink N t u c z := ⟨un, hun, hcz⟩
        obtain ⟨h1, h2⟩ := hnotLR u c z huN hlk' hup
        exact ⟨Or.inl (TReach.link huN hlk'), h1, h2⟩

/-- `retarget` read through the writer's nodes: only p's node changes, to itself
or retargeted. -/
theorem writerWP_retarget_wNode (p src dst : NodeId) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) (hpt : w.taken.contains p = false) :
    WriterWP (retarget p src dst) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧
      (∀ y, y ≠ p → wNode c.p base w' y = wNode c.p base w y) ∧ (∃ n', wNode c.p base w' p = some n') ∧
      ∀ n', wNode c.p base w' p = some n' → ∃ n, wNode c.p base w p = some n ∧
        (n' = n ∨ ∃ ti, n' = { n with ks := retargetKlongs n.ks ti src dst })) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_getNode_reads p c w base hvc) ?_
  intro n w1 ⟨hr1, hl1, hw1⟩
  have hwp : wNode c.p base w p = some n := hw1 hpt
  have h1t : w1.taken.contains p = false := by rw [hr1.2.2.1]; exact hpt
  split
  · unfold putNode
    refine (writerWP_modify _ c w1 _).mpr ?_
    refine ⟨hr1.2.2.1, hr1.2.1, hr1.2.2.2.2, hr1.2.2.2.1, fun y hy => ?_,
      ⟨{ n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst }, ?_⟩,
      fun n' hn' => ⟨n, hwp, Or.inr ⟨n.lastTimeIndex.getD 0, ?_⟩⟩⟩
    · rw [← hr1.1]
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
    · simp only [wNode, h1t, Bool.false_eq_true, ↓reduceIte, lookup_upsert]; rfl
    · simp only [wNode, h1t, Bool.false_eq_true, ↓reduceIte, lookup_upsert] at hn'
      exact (Option.some.inj hn').symm
  · refine (writerWP_pure _ c w1 _).mpr ?_
    refine ⟨hr1.2.2.1, hr1.2.1, hr1.2.2.2.2, hr1.2.2.2.1, fun y _ => by rw [hr1.1],
      ⟨n, by rw [hr1.1, hwp]⟩, fun n' hn' => ?_⟩
    rw [hr1.1, hwp] at hn'
    exact ⟨n, hwp, Or.inl (Option.some.inj hn').symm⟩

/-- `unlink` read through the writer's nodes: only o's node changes. -/
theorem writerWP_unlink_wNode (o : NodeId) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w : W) :
    WriterWP (unlink o) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧ w'.next = w.next ∧
      w'.vals = w.vals ∧ ∀ y, y ≠ o → wNode c.p base w' y = wNode c.p base w y) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_getNode_reads o c w base hvc) ?_
  intro n w1 ⟨hr1, _, _⟩
  split
  · unfold putNode
    refine (writerWP_modify _ c w1 _).mpr ?_
    refine ⟨hr1.2.2.1, hr1.2.1, hr1.2.2.2.2, hr1.2.2.2.1, fun y hy => ?_⟩
    rw [← hr1.1]
    simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  · refine (writerWP_pure _ c w1 _).mpr ?_
    exact ⟨hr1.2.2.1, hr1.2.1, hr1.2.2.2.2, hr1.2.2.2.1, fun y _ => by rw [hr1.1]⟩

/-- The merge's last loop read through the writer's nodes, p not taken back and
not a node of the loop: nothing changes but the loop's nodes and p, whose live
klongs after are its live klongs before, or m1 where one before named a node of
the loop. -/
theorem writerWP_mergeCleanup_wNode (p m1 : NodeId) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ q ∈ xs, q.1 ≠ p) → w.taken.contains p = false →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.top = w.top ∧ w'.taken.contains p = false ∧
        (∀ y, y ≠ p → (∀ q ∈ xs, y ≠ q.1) → wNode c.p base w' y = wNode c.p base w y) ∧
        ((∃ n, wNode c.p base w p = some n) → ∃ n', wNode c.p base w' p = some n') ∧
        ∀ n', wNode c.p base w' p = some n' → ∃ n, wNode c.p base w p = some n ∧ n'.leaf = n.leaf ∧
          ∀ c' z, (c', z) ∈ n'.liveAt c.i →
            (c', z) ∈ n.liveAt c.i ∨ (z = m1 ∧ ∃ q ∈ xs, (c', q.1) ∈ n.liveAt c.i)) := by
  intro xs
  induction xs with
  | nil =>
    intro w _ hpt
    rw [List.forIn_nil]
    refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, hpt, fun _ _ _ => rfl, fun h => h, fun n' h => ⟨n', h, rfl, fun _ _ h => Or.inl h⟩⟩
  | cons q qs ih =>
    intro w hne hpt
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ (w1 : W), w1.top = w.top → w1.taken.contains p = false →
        (∀ y, y ≠ p → y ≠ q.1 → wNode c.p base w1 y = wNode c.p base w y) →
        ((∃ n, wNode c.p base w p = some n) → ∃ n1, wNode c.p base w1 p = some n1) →
        (∀ n1, wNode c.p base w1 p = some n1 → ∃ n, wNode c.p base w p = some n ∧ n1.leaf = n.leaf ∧
          ∀ c' z, (c', z) ∈ n1.liveAt c.i → (c', z) ∈ n.liveAt c.i ∨ (z = m1 ∧ (c', q.1) ∈ n.liveAt c.i)) →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.top = w.top ∧ w'.taken.contains p = false ∧
          (∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) → wNode c.p base w' y = wNode c.p base w y) ∧
          ((∃ n, wNode c.p base w p = some n) → ∃ n', wNode c.p base w' p = some n') ∧
          ∀ n', wNode c.p base w' p = some n' → ∃ n, wNode c.p base w p = some n ∧ n'.leaf = n.leaf ∧
            ∀ c' z, (c', z) ∈ n'.liveAt c.i →
              (c', z) ∈ n.liveAt c.i ∨ (z = m1 ∧ ∃ q' ∈ q :: qs, (c', q'.1) ∈ n.liveAt c.i)) := by
      intro w1 h1top h1pt h1l h1ex h1p
      refine writerWP_mono (ih w1 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) h1pt) ?_
      intro _ w2 ⟨h2top, h2pt, h2l, h2ex, h2p⟩
      refine ⟨h2top.trans h1top, h2pt, fun y hyp hy => ?_, fun he => h2ex (h1ex he), fun n' hn' => ?_⟩
      · rw [h2l y hyp (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1l y hyp (hy q List.mem_cons_self)]
      · obtain ⟨n2, hn2, hl2, hs2⟩ := h2p n' hn'
        obtain ⟨n1, hn1, hl1, hs1⟩ := h1p n2 hn2
        refine ⟨n1, hn1, hl2.trans hl1, fun c' z hm => ?_⟩
        rcases hs2 c' z hm with h | ⟨hz, q', hq', h⟩
        · rcases hs1 c' z h with h' | ⟨hz', h'⟩
          · exact Or.inl h'
          · exact Or.inr ⟨hz', q, List.mem_cons_self, h'⟩
        · rcases hs1 c' q'.1 h with h' | ⟨_, h'⟩
          · exact Or.inr ⟨hz, q', List.mem_cons_of_mem _ hq', h'⟩
          · exact Or.inr ⟨hz, q, List.mem_cons_self, h'⟩
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (writerWP_retarget_wNode p q.1 m1 c base hvc w hpt) ?_
      intro _ w1 ⟨h1t, h1top, _, _, h1l, h1ex, h1p⟩
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      have htk : ∀ y, y ≠ q.1 → (q.1 :: w1.taken).contains y = w.taken.contains y := by
        intro y hy
        rw [List.contains_cons, h1t]
        have : (y == q.1) = false := by simpa using hy
        simp [this]
      have hwq : wNode c.p base { w1 with taken := q.1 :: w1.taken } p = wNode c.p base w1 p := by
        have hc : (q.1 :: w1.taken).contains p = w1.taken.contains p := by
          rw [List.contains_cons]
          have : (p == q.1) = false := by simpa using (Ne.symm hqp)
          simp [this]
        simp only [wNode, hc]
      refine hrest _ h1top (by rw [htk p (Ne.symm hqp)]; exact hpt) (fun y hyp hyq => ?_)
        (fun _ => by
          obtain ⟨n1, hn1⟩ := h1ex
          exact ⟨n1, by show wNode c.p base { w1 with taken := q.1 :: w1.taken } p = _; rw [hwq]; exact hn1⟩)
        (fun n1 hn1 => ?_)
      · show wNode c.p base { w1 with taken := q.1 :: w1.taken } y = _
        rw [← h1l y hyp]
        have hc : (q.1 :: w1.taken).contains y = w1.taken.contains y := by
          rw [List.contains_cons]
          have : (y == q.1) = false := by simpa using hyq
          simp [this]
        simp only [wNode, hc]
      · have hn1' : wNode c.p base w1 p = some n1 := by
          have : wNode c.p base { w1 with taken := q.1 :: w1.taken } p = wNode c.p base w1 p := by
            have hc : (q.1 :: w1.taken).contains p = w1.taken.contains p := by
              rw [List.contains_cons]
              have : (p == q.1) = false := by simpa using (Ne.symm hqp)
              simp [this]
            simp only [wNode, hc]
          rw [← this]; exact hn1
        obtain ⟨n, hn, he⟩ := h1p n1 hn1'
        refine ⟨n, hn, ?_, fun c' z hm => ?_⟩
        · rcases he with he | ⟨ti, he⟩ <;> rw [he]
        · rcases he with he | ⟨ti, he⟩
          · rw [he] at hm; exact Or.inl hm
          · rw [he] at hm
            rcases KNode.retarget_liveAt n ti q.1 m1 c.i c' z hm with h | ⟨hz, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨hz, h⟩
    · have hq2' : q.2 = false := by simpa using hq2
      simp only [writerWP_bind, hq2', Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (writerWP_unlink_wNode q.1 c base hvc w) ?_
      intro _ w1 ⟨h1t, h1top, _, _, h1l⟩
      refine (writerWP_pure _ c _ _).mpr ?_
      refine hrest _ h1top (by rw [h1t]; exact hpt) (fun y _ hyq => h1l y hyq)
        (fun he => by rw [h1l p (Ne.symm hqp)]; exact he) (fun n1 hn1 => ?_)
      rw [h1l p (Ne.symm hqp)] at hn1
      exact ⟨n1, hn1, rfl, fun c' z hm => Or.inl hm⟩

/-- The merge's full parent p, at depth D + 1 of the path below the cascade's
nodes X s .. X D: `handleFull` of its last version `mergeFullLast` keeps the
tree, given that the tree with p's node replaced by it is one and reaches
neither merged sibling l nor r (`hV`), and the cascade's premises
(`writerWP_fullSplit_chainG`). After it the siblings are not reached and p is
not taken back. -/
theorem writerWP_mergeFull_branch (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (hsD : s ≤ D)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D + 1 → s ≤ i' → i' ≤ D + 1 → X i = X i' → i = i')
    (p l r m1 : NodeId) (m2 : Option (NodeId × Nat)) (pn : KNode) (cL cR : Nat)
    (hXp : X (D + 1) = p) (hNp : Nn (D + 1) = pn)
    (hhalves : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r0 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r0 < c''))
    (w6 : W) (h6path : w6.path = path0)
    (h6S2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w6.nodes.lookup (X i) = some (Nn i) ∧ w6.taken.contains (X i) = false)
    (h6T : TreeOK (wNode c.p base w6) c.i w6.top.rootKey)
    (h6S4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w6) c.i w6.top.rootKey (X i))
    (h6S5 : ∀ z, w6.next ≤ z → w6.nodes.lookup z = none ∧ w6.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (h6S6 : ∀ u c' z, TLink (wNode c.p base w6) c.i u c' z → z < w6.next)
    (h6R0 : s = 0 → w6.top.rootKey = X 0)
    (hV : ∀ last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      TreeOK (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey ∧
      (∀ z, TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z →
        z ≠ l ∧ z ≠ r) ∧
      ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w6.next)
    (hlr : l < w6.next ∧ r < w6.next) :
    ∀ last compact s', mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull (D + 1) p last compact) c ({ w6 with trail := s' :: w6.trail } : W)
        (fun _ w7 => TreeOK (wNode c.p base w7) c.i w7.top.rootKey ∧
          ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey l ∧
          ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey r ∧
          w7.taken = w6.taken ∧ w7.vals = w6.vals) := by
  intro last compact s' hlast
  obtain ⟨hVt, hVlr, hvx⟩ := hV last hlast
  have hN6 : wNode c.p base ({ w6 with trail := s' :: w6.trail } : W) = wNode c.p base w6 := rfl
  show WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) p [] last compact) c _ _
  rw [← hXp]
  have hVt' : TreeOK (updN (wNode c.p base ({ w6 with trail := s' :: w6.trail } : W)) (X (D + 1))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i ({ w6 with trail := s' :: w6.trail } : W).top.rootKey := by
    rw [hN6, hXp, hNp]; exact hVt
  have hvx' : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
      z < ({ w6 with trail := s' :: w6.trail } : W).next := by
    rw [hNp]; exact hvx
  refine writerWP_mono (writerWP_fullSplit_chainG c base path0 s D X K Nn last compact hsD hX hK hlinkK
    hrange hlen hwf htimes htop hdist (hhalves last hlast) _ h6path h6S2 (by rw [hN6]; exact h6T)
    (by rw [hN6]; exact h6S4) h6S5 (by rw [hN6]; exact h6S6) h6R0 hVt' hvx') ?_
  rintro _ w7 ⟨hT7, ⟨_, ht7, _, _, hv7⟩, _, hreach7⟩
  have hpt := (h6S2 (D + 1) (by omega) (Nat.le_refl _)).2
  refine ⟨hT7, fun hl => ?_, fun hr => ?_, ht7, hv7⟩
  · rcases hreach7 l hl with h | h
    · rw [hN6, hXp, hNp] at h
      exact (hVlr l h).1 rfl
    · have := hlr.1; simp only at h; omega
  · rcases hreach7 r hr with h | h
    · rw [hN6, hXp, hNp] at h
      exact (hVlr r h).2 rfl
    · have := hlr.2; simp only at h; omega

/-- A tree is reached alike in a node map that agrees on its reached nodes. -/
theorem tReach_of_agree_fwd (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ x, TReach L t r x → L' x = L x) : ∀ y, TReach L t r y → TReach L' t r y := by
  intro y hy
  induction hy with
  | root => exact TReach.root
  | @link x c y hx hl ih =>
    obtain ⟨n, hn, hc⟩ := hl
    exact TReach.link ih ⟨n, by rw [h x hx]; exact hn, hc⟩

/-- The merge's state before its parent's change: the nodes below the next id
nx as before, new nodes from nx on naming nodes below nx, the path and the taken
nodes as before. Then the cascade's state facts hold of it. -/
theorem mergeState_facts (c : Ctx) (base : View BVal) (N : NodeId → Option KNode) (root : NodeId)
    (nx : Nat) (w3 S : W) (s D : Nat) (X : Nat → NodeId) (Nn : Nat → KNode)
    (hT : TreeOK N c.i root) (h3top : w3.top.rootKey = root)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hlinksAll : ∀ u c' z, TLink N c.i u c' z → z < nx)
    (hbaseF : ∀ z, nx ≤ z → knodeOf c.p base z = none)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 → w3.nodes.lookup (X i) = some (Nn i) ∧ w3.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach N c.i root (X i))
    (hR0 : s = 0 → root = X 0)
    (hSlook : ∀ i, s ≤ i → i ≤ D + 1 → S.nodes.lookup (X i) = w3.nodes.lookup (X i))
    (hSt : S.taken = w3.taken) (hStop : S.top = w3.top) (hSnx : nx ≤ S.next)
    (hSlow : ∀ y, y < nx → wNode c.p base S y = N y)
    (hSnew : ∀ y yn, nx ≤ y → S.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i → z < nx)
    (hShigh : ∀ y, S.next ≤ y → S.nodes.lookup y = none) :
    (∀ i, s ≤ i → i ≤ D + 1 → S.nodes.lookup (X i) = some (Nn i) ∧ S.taken.contains (X i) = false) ∧
    TreeOK (wNode c.p base S) c.i S.top.rootKey ∧
    (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base S) c.i S.top.rootKey (X i)) ∧
    (∀ z, S.next ≤ z → S.nodes.lookup z = none ∧ S.taken.contains z = false ∧ knodeOf c.p base z = none) ∧
    (∀ u c' z, TLink (wNode c.p base S) c.i u c' z → z < S.next) ∧
    (s = 0 → S.top.rootKey = X 0) := by
  have hroot : S.top.rootKey = root := by rw [hStop, h3top]
  have hNlt : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · rw [(hfree y h).1] at hy; cases hy
  have hagree : ∀ y, TReach N c.i root y → wNode c.p base S y = N y := by
    intro y hy
    cases hy with
    | root =>
      obtain ⟨n, hn⟩ := hT.rootKey
      exact hSlow _ (hNlt _ n hn)
    | link hx hl =>
      obtain ⟨n, hn, hc⟩ := hl
      exact hSlow _ (hlinksAll _ _ _ ⟨n, hn, hc⟩)
  refine ⟨fun i h1 h2 => ⟨by rw [hSlook i h1 h2]; exact (hS2 i h1 h2).1, by rw [hSt]; exact (hS2 i h1 h2).2⟩,
    ?_, ?_, ?_, ?_, fun h => by rw [hroot]; exact hR0 h⟩
  · rw [hroot]; exact treeOK_of_agree N _ c.i root hT hagree
  · intro i h1 h2; rw [hroot]; exact tReach_of_agree_fwd N _ c.i root hagree _ (hS4 i h1 h2)
  · intro z hz
    refine ⟨hShigh z hz, by rw [hSt]; exact (hfree z (by omega)).2, hbaseF z (by omega)⟩
  · intro u c' z hl
    obtain ⟨un, hun, hc⟩ := hl
    rcases Nat.lt_or_ge u nx with hu | hu
    · rw [hSlow u hu] at hun
      have := hlinksAll u c' z ⟨un, hun, hc⟩; omega
    · unfold wNode at hun
      split at hun
      · cases hun
      · cases hlk : S.nodes.lookup u with
        | none =>
          rw [hlk] at hun
          simp only at hun
          rw [hbaseF u hu] at hun; cases hun
        | some yn =>
          rw [hlk] at hun
          simp only [Option.some.injEq] at hun
          subst hun
          have := hSnew u yn hu hlk c' z hc; omega

/-- `ghOf` reads as before. -/
theorem writerWP_ghOf_reads (x : NodeId) (c : Ctx) (w : W) (base : View BVal)
    (hvc : ViewCoherent c base) :
    WriterWP (ghOf x) c w (fun _ v => ReadsAs c.p base w v) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_reads x c w base hvc) ?_
  intro _ v ⟨hr, _, _⟩
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact hr
  · exact writerWP_throw _ _ _ _

/-- The live klongs of the merge's full parent as `treeOK_mergeOneAfter` and
`treeOK_mergeTwoAfter` take them. -/
theorem mergeFullLast_liveAt (pn : KNode) (t : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (last : KNode) (h : mergeFullLast pn t cL m1 cR m2 = some last)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ t) :
    (∀ s, Klong.time s ∈ last.ks → s ≤ t) ∧ last.leaf = pn.leaf ∧
    (m2 = none → ∀ cc z, (cc, z) ∈ last.liveAt t →
      (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt t ∧ cc ≠ cL ∧ cc ≠ cR)) ∧
    (∀ y g, m2 = some (y, g) → ∀ cc z, (cc, z) ∈ last.liveAt t →
      (cc = cL ∧ z = m1) ∨ (cc = g ∧ z = y) ∨ ((cc, z) ∈ pn.liveAt t ∧ cc ≠ cL ∧ cc ≠ cR)) := by
  obtain ⟨pairs, hks⟩ := mergeFullLast_ks pn t cL m1 cR m2 last h
  have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ t := by rw [hks]; exact newKlongs_times t pairs
  obtain ⟨hleaf, hnone, hsome⟩ := mergeFullLast_lookup pn t cL m1 cR m2 last h
  have hpn : ∀ cc z, pn.live.lookup cc = some z → (cc, z) ∈ pn.liveAt t := by
    intro cc z hz
    rw [KNode.liveAt_of_times pn t hpt]
    exact mem_of_lookup_nodup _ cc z hz
  have hl : ∀ cc z, (cc, z) ∈ last.liveAt t → last.live.lookup cc = some z := by
    intro cc z hm
    rw [KNode.liveAt_of_times last t htl] at hm
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup last) cc z hm
  refine ⟨htl, hleaf, fun h0 cc z hm => ?_, fun y g hy cc z hm => ?_⟩
  · have hlk := hl cc z hm
    rw [hnone h0 cc] at hlk
    by_cases h1 : cc = cL
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hlk
      exact Or.inl ⟨h1, (Option.some.inj hlk).symm⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hlk
      by_cases h2 : cc = cR
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hlk; cases hlk
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at hlk
        exact Or.inr ⟨hpn cc z hlk, h1, h2⟩
  · have hlk := hl cc z hm
    rw [hsome y g hy cc] at hlk
    by_cases h0 : cc = g
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at hlk
      exact Or.inr (Or.inl ⟨h0, (Option.some.inj hlk).symm⟩)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at hlk
      by_cases h1 : cc = cL
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hlk
        exact Or.inl ⟨h1, (Option.some.inj hlk).symm⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hlk
        by_cases h2 : cc = cR
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hlk; cases hlk
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)] at hlk
          exact Or.inr (Or.inr ⟨hpn cc z hlk, h1, h2⟩)

end SIS.Tree
