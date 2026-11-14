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
      (fun _ w' => w'.top = w.top ∧ w'.taken.contains p = false ∧ w'.vals = w.vals ∧
        (∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.taken.contains y = w.taken.contains y) ∧
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
    exact ⟨rfl, hpt, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun h => h,
      fun n' h => ⟨n', h, rfl, fun _ _ h => Or.inl h⟩⟩
  | cons q qs ih =>
    intro w hne hpt
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ (w1 : W), w1.top = w.top → w1.taken.contains p = false → w1.vals = w.vals →
        (∀ y, y ≠ q.1 → w1.taken.contains y = w.taken.contains y) →
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
        (fun _ w' => w'.top = w.top ∧ w'.taken.contains p = false ∧ w'.vals = w.vals ∧
          (∀ y, (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.taken.contains y = w.taken.contains y) ∧
          (∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) → wNode c.p base w' y = wNode c.p base w y) ∧
          ((∃ n, wNode c.p base w p = some n) → ∃ n', wNode c.p base w' p = some n') ∧
          ∀ n', wNode c.p base w' p = some n' → ∃ n, wNode c.p base w p = some n ∧ n'.leaf = n.leaf ∧
            ∀ c' z, (c', z) ∈ n'.liveAt c.i →
              (c', z) ∈ n.liveAt c.i ∨ (z = m1 ∧ ∃ q' ∈ q :: qs, (c', q'.1) ∈ n.liveAt c.i)) := by
      intro w1 h1top h1pt h1v h1tk h1l h1ex h1p
      refine writerWP_mono (ih w1 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) h1pt) ?_
      intro _ w2 ⟨h2top, h2pt, h2v, h2tk, h2l, h2ex, h2p⟩
      refine ⟨h2top.trans h1top, h2pt, h2v.trans h1v, fun y hy => ?_, fun y hyp hy => ?_,
        fun he => h2ex (h1ex he), fun n' hn' => ?_⟩
      · rw [h2tk y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')), h1tk y (hy q List.mem_cons_self)]
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
      intro _ w1 ⟨h1t, h1top, _, h1v, h1l, h1ex, h1p⟩
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
      refine hrest _ h1top (by rw [htk p (Ne.symm hqp)]; exact hpt) h1v (fun y hyq => htk y hyq)
        (fun y hyp hyq => ?_)
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
      intro _ w1 ⟨h1t, h1top, _, h1v, h1l⟩
      refine (writerWP_pure _ c _ _).mpr ?_
      refine hrest _ h1top (by rw [h1t]; exact hpt) h1v (fun y _ => by rw [h1t]) (fun y _ hyq => h1l y hyq)
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

set_option maxHeartbeats 1600000 in
/-- The merge's tail keeps the writer's tree, the parent with room or full:
`writerWP_mergeTail_made_tree` without its room premises. A full parent p, at
depth D + 1 of the path below the cascade's nodes X s .. X D, is split with its
last version `mergeFullLast` and the cascade above it (`writerWP_mergeFull_branch`,
with the cascade's premises, `hhalves` for the last version's halves), then the
merged siblings, unreached, are left behind (`treeOK_after_cleanup`). -/
theorem writerWP_mergeTail_any_tree (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hvc : ViewCoherent c base)
    (hlinksAll : ∀ u c' z, TLink N c.i u c' z → z < nx)
    (hbaseF : ∀ z, nx ≤ z → knodeOf c.p base z = none)
    (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hsD : s ≤ D)
    (hd : d - 1 = D + 1)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (w3.path[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → w3.path[i]? = some (some (K i), X i))
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
    (hXp : X (D + 1) = p) (hNp : Nn (D + 1) = pn)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w3.nodes.lookup (X i) = some (Nn i) ∧ w3.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach N c.i root (X i))
    (hR0 : s = 0 → root = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hhalves : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r0 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r0 < c'')) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hlR : TReach N c.i root l := TReach.link hp hlink_l
  have hrR : TReach N c.i root r := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _) (writerWP_ghOf_reads x c _ base hvc)) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4⟩
  have hcl' : ∀ (b1 b2 : Bool) y, y ≠ l → y ≠ r → ∀ q ∈ [(l, b1), (r, b2)], y ≠ (q : NodeId × Bool).1 := by
    intro b1 b2 y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ (b1 b2 : Bool), ∀ q ∈ [(l, b1), (r, b2)], (q : NodeId × Bool).1 ≠ p := by
    intro b1 b2 q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
    intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
    intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
    -- the ids
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
    have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
      intro z hz
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := h3src z (by rw [h']; rfl); omega
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, lookup_append_single_self]
      rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; exact hym), hlk4 y hyx]
    have hpT : w3.taken.contains p = false := by
      have := hN3 ▸ hpn
      unfold wNode at this
      split at this
      · cases this
      · rename_i h; simpa using h
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
    have hhtd := htd_last pn
    -- the parent after
    have hpliveAt : ∀ (m2 : Option (NodeId × Nat)),
        ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR m2).liveAt c.i →
        (mergeParentNode pn c.i il cL m1 ir cR m2).live.lookup cc = some z := by
      intro m2 cc z hm
      rw [KNode.liveAt_of_times _ c.i (by
        rw [mergeParentNode_eq]
        exact mpNode_times pn c.i il cL m1 ir cR m2 _ _ _ (hhtd _) hpt)] at hm
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hm
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
    rw [hw4m1] at hw6m1
    have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
        (first, second) := hmk
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
      intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlr' : ∀ (b1 b2 : Bool) (q : NodeId × Bool), q ∈ [(l, b1), (r, b2)] → q.1 = l ∨ q.1 = r := by
      intro b1 b2 q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr rfl
    -- the full parent's facts, from any state S with the nodes below m1 as before
    have hlnx' : l < m1 := hlnx
    have hrnx' : r < m1 := hrnx
    have hchild : ∀ z, ((∃ c0, (c0, z) ∈ ln.live) ∨ (∃ c0, (c0, z) ∈ rn.live)) → z < m1 := by
      rintro z (⟨c0, h0⟩ | ⟨c0, h0⟩)
      · exact hlinksAll l c0 z ⟨ln, hln, by rw [KNode.liveAt_of_times ln c.i hlt]; exact h0⟩
      · exact hlinksAll r c0 z ⟨rn, hrn, by rw [KNode.liveAt_of_times rn c.i hrt]; exact h0⟩
    have hsnd : ∀ z (E : List (Nat × NodeId)), (∀ q ∈ E, ∃ q' ∈ ln.live ++ rn.live, q'.2 = q.2) →
        ∀ c', (c', z) ∈ E → (∃ c0, (c0, z) ∈ ln.live) ∨ (∃ c0, (c0, z) ∈ rn.live) := by
      intro z E hE c' hm
      obtain ⟨q', hq', he⟩ := hE (c', z) hm
      rcases List.mem_append.mp hq' with h | h
      · exact Or.inl ⟨q'.1, by rw [show z = q'.2 from he.symm]; exact h⟩
      · exact Or.inr ⟨q'.1, by rw [show z = q'.2 from he.symm]; exact h⟩
    have hXlt : ∀ i, s ≤ i → i ≤ D + 1 → X i < m1 := by
      intro i h1 h2
      obtain ⟨hl3, ht3⟩ := hS2 i h1 h2
      have hNX : N (X i) = some (Nn i) := by
        rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3]
      rcases Nat.lt_or_ge (X i) m1 with h | h
      · exact h
      · rw [(hfree _ h).1] at hNX; cases hNX
    have hm1R : ¬ TReach N c.i root m1 := not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    -- the parent after, into one node
    have hchar1 : ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro cc z hm
      have hlk := hpliveAt none cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      simp only at hlk
      by_cases h1 : cc = cL
      · simp only [h1, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inl ⟨h1, hlk.symm⟩
      · by_cases h2 : cc = cR
        · simp [h2, Ne.symm hc] at hlk
        · simp only [h1, h2, ↓reduceIte] at hlk
          right
          refine ⟨?_, h1, h2⟩
          rw [KNode.liveAt_of_times pn c.i hpt]
          exact mem_of_lookup_nodup _ cc z hlk
    -- the parent after, into two nodes
    have hchar2 : ∀ (m2 : NodeId) (g2 : Nat) cc z,
        (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR (some (m2, g2))).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ (cc = g2 ∧ z = m2) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro m2 g2 cc z hm
      have hlk := hpliveAt (some (m2, g2)) cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR (some (m2, g2)) _ _ _ l r
        hpwf hL hLL hR hRL hc ?htd ?hrip cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      case hrip =>
        intro h y g heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simp at h
        exact h.1.1
      simp only at hlk
      by_cases h0 : cc = g2
      · simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inr (Or.inl ⟨h0, hlk.symm⟩)
      · by_cases h1 : cc = cL
        · subst h1
          simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
          exact Or.inl ⟨rfl, hlk.symm⟩
        · by_cases h2 : cc = cR
          · subst h2
            simp [h0, h1] at hlk
          · simp only [h0, h1, h2, ↓reduceIte] at hlk
            right; right
            refine ⟨?_, h1, h2⟩
            rw [KNode.liveAt_of_times pn c.i hpt]
            exact mem_of_lookup_nodup _ cc z hlk
    -- neither merged node is named live by the parent after
    have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
      intro z hz cc hm h1 h2
      rcases hz with hz | hz
      · rw [hz] at hm
        exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hm⟩ hlink_l).2
      · rw [hz] at hm
        exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hm⟩ hlink_r).2
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mergeParent_cases p pn (d - 1) il cL m1 ir cR none c w6 _ hw6p ?_ ?_
      rotate_left
      · intro last compact s7 hlast
        rw [hd]
        have hw6w4 : ∀ y, y ≠ m1 → wNode c.p base w6 y = wNode c.p base w4 y := by
          intro y hym
          unfold wNode
          rw [h6taken, ← h4t, h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym)]
        have hlow6 : ∀ y, y < m1 → wNode c.p base w6 y = N y := by
          intro y hy
          rw [hw6w4 y (by omega), hr4.1, ← hN3]; rfl
        have hnew6 : ∀ y yn, m1 ≤ y → w6.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i →
            z < m1 := by
          intro y yn hy hyn c' z hz
          by_cases hym : y = m1
          · rw [hym, hw6m1] at hyn
            cases hyn
            have hm := liveAt_newKlongs_mem _ c.i c.i first c' z hz
            apply hchild
            apply hsnd z first _ c' hm
            intro q hq
            have : q.2 ∈ (ln.live ++ rn.live).map Prod.snd := by
              rw [List.map_append, ← mergeList_map_snd (!xn.leaf) cR, ← hfirst]
              exact List.mem_map.mpr ⟨q, hq, rfl⟩
            obtain ⟨q', hq', he⟩ := List.mem_map.mp this
            exact ⟨q', hq', he⟩
          · rw [h6old y (by omega) hym, hnone3 y hy] at hyn; cases hyn
        have hhigh6 : ∀ y, w6.next ≤ y → w6.nodes.lookup y = none := by
          intro y hy
          have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
          rw [h6old y (by omega) (by omega), hnone3 y (by omega)]
        obtain ⟨h6S2, h6T, h6S4, h6S5, h6S6, h6R0⟩ := mergeState_facts c base N root m1 w3 w6 s D X Nn
          hT h3top hfree hlinksAll hbaseF hS2 hS4 hR0
          (fun i h1 h2 => h6old _ (hXx i h1 h2) (by have := hXlt i h1 h2; omega)) h6taken
          (by rw [h6top, h5top, h4top]) (by rw [h6next, h5next, hw4m1]; omega) hlow6 hnew6 hhigh6
        have hV6 : ∀ last, mergeFullLast pn c.i cL m1 cR none = some last →
            TreeOK (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey ∧
            (∀ z, TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z →
              z ≠ l ∧ z ≠ r) ∧
            ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w6.next := by
          intro last hlast
          obtain ⟨_, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h6top']
          have hVp : updN (wNode c.p base w6) p last p = some last := updN_self _ _ _
          have hVm1 : updN (wNode c.p base w6) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
            rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
          have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
            intro y hyp hym
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow6 y hy
            · have hyw : wNode c.p base w6 y = none := by
                simp only [wNode, h6taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h6old y (by omega) hym, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          have hmn : ∀ cc z, (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i →
              (cc, z) ∈ mergeList (!xn.leaf) cR ln.live rn.live := by
            intro cc z hm
            have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
            rw [hfirst] at this; exact this
          refine ⟨treeOK_mergeOneAfter N _ c.i root p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩
            (!xn.leaf) cL cR hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
            hVm1 hmn hVp (hnoneL rfl) (fun y hyp _ _ hym => hVN y hyp hym), fun z hz => ?_, fun c' z hm => ?_⟩
          · have := mergeV_reach N _ c.i root p l r m1 none pn ln rn last cL cR hT hp hpn hpL hpR hln hrn hVp
              (fun cc z hm => by
                rcases hnoneL rfl cc z hm with ⟨_, h⟩ | h
                · exact Or.inl h
                · exact Or.inr (Or.inr h))
              (fun m mn hm hmn' cc z hz => by
                rcases hm with hm | hm
                · rw [hm, hVm1] at hmn'
                  cases hmn'
                  have hm2 := hmn cc z hz
                  have hsn := (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
                  have hz' : z ∈ (ln.live ++ rn.live).map Prod.snd := by
                    rw [List.map_append, ← hsn]; exact List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩
                  obtain ⟨q', hq', he⟩ := List.mem_map.mp hz'
                  rcases List.mem_append.mp hq' with h | h
                  · exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact h⟩
                  · exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact h⟩
                · cases hm)
              (fun y hyp _ _ hym _ => hVN y hyp hym) hm1R (fun m hm => by cases hm) z hz
            exact ⟨this.2.1, this.2.2⟩
          · have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
            rcases hnoneL rfl c' z hm with ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        have hbr := writerWP_mergeFull_branch c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen hwf
          htimes htop hdist p l r m1 none pn cL cR hXp hNp (hhalves m1 none) w6
          (by rw [h6p, h5p, h4p]) h6S2 h6T h6S4 h6S5 h6S6 h6R0 hV6
          ⟨by rw [h6next, h5next, hw4m1]; omega, by rw [h6next, h5next, hw4m1]; omega⟩
          last compact s7 hlast
        refine writerWP_mono hbr ?_
        rintro _ w7 ⟨hT7, hl7, hr7, ht7, _⟩
        refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w7 (hne' _ _)
          (by rw [ht7, h6taken]; exact hpT)) ?_
        rintro _ w8 ⟨h8top, _, _, _, h8l, h8ex, h8p⟩
        try simp only [writerWP_pure]
        rw [h8top]
        refine treeOK_after_cleanup (wNode c.p base w7) (wNode c.p base w8) c.i w7.top.rootKey p l r m1
          hT7 hl7 hr7 ?_ (fun y hyp hyl hyr => h8l y hyp (hcl' _ _ y hyl hyr)) (fun n' hn' => ?_)
        · by_cases hrp : w7.top.rootKey = p
          · rw [hrp]; exact h8ex (by rw [← hrp]; exact hT7.rootKey)
          · have hrl : w7.top.rootKey ≠ l := fun h => hl7 (h ▸ TReach.root)
            have hrr : w7.top.rootKey ≠ r := fun h => hr7 (h ▸ TReach.root)
            rw [h8l _ hrp (hcl' _ _ _ hrl hrr)]
            exact hT7.rootKey
        · obtain ⟨n, hn, _, hsub⟩ := h8p n' hn'
          refine ⟨n, hn, fun c' z hm => ?_⟩
          rcases hsub c' z hm with h | ⟨hz, q, hq, h⟩
          · exact Or.inl h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact Or.inr ⟨hz, Or.inl h⟩
            · exact Or.inr ⟨hz, Or.inr h⟩
      intro s7
      generalize hw7 : ({ ({ w6 with trail := s7 :: w6.trail } : W) with
        nodes := upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W) = w7
      have h7n : w7.nodes = upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) := by rw [← hw7]
      have h7t : w7.taken = w6.taken := by rw [← hw7]
      have h7top : w7.top = w6.top := by rw [← hw7]
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
      refine writerWP_mono (writerWP_mergeCleanup_frame p m1 c.i c _ w7 _ (hne' _ _) hlk7
        (fun q hq c' hm => by
          rcases hchar1 c' q.1 hm with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2)) ?_
      intro _ w8 ⟨h8top, _, h8t, h8l, pn8, h8p, h8sub⟩
      try simp only [writerWP_pure]
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' _ _ y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' _ _ y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      rw [h8top, h7top, h6top']
      apply treeOK_mergeOneAfter N (wNode c.p base w8) c.i root p l r m1 pn ln rn pn8
        ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
        hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
      · simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
      · intro cc z hm
        have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
        rw [hfirst] at this; exact this
      · simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
      · intro cc z hm
        exact hchar1 cc z (h8sub cc z hm)
      · intro y hyp hyl hyr hym
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (hyx y hyl hyr) hym]
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
      simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, h7next, _, h7p, _⟩
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
      subst hm2'
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, h8next, _, h8p⟩
      try simp only [writerWP_pure]
      have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
        rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
          hlk4 _ (by omega)]
        exact hnone3 _ (by omega)
      have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
          ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
        intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]
        exact hw6p
      refine writerWP_mergeParent_cases p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p ?_ ?_
      rotate_left
      · intro last compact s9 hlast
        rw [hd]
        have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
        have h8nx : w8.next = m1 + 4 := by rw [h8next, h7next, h6next, h5next, hw4m1]
        have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
          intro y hyx hym hym2
          rw [h8l, lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
        have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
          rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]; exact hw6m1
        have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
          rw [h8l, lookup_append_single_self _ _ _ hw6m2]
        have hw8w4 : ∀ y, y ≠ m1 → y ≠ m1 + 2 → wNode c.p base w8 y = wNode c.p base w4 y := by
          intro y hym hym2
          unfold wNode
          rw [h8taken, ← h4t, h8l, lookup_append_single_ne _ _ _ _ hym2, h6n, h5n,
            lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym)]
        have hlow8 : ∀ y, y < m1 → wNode c.p base w8 y = N y := by
          intro y hy
          rw [hw8w4 y (by omega) (by omega), hr4.1, ← hN3]; rfl
        have hE' : ∀ q ∈ first ++ ks2, ∃ q' ∈ ln.live ++ rn.live, q'.2 = q.2 := by
          intro q hq
          have : q.2 ∈ (ln.live ++ rn.live).map Prod.snd := by
            rw [← hE]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
          obtain ⟨q', hq', he⟩ := List.mem_map.mp this
          exact ⟨q', hq', he⟩
        have hnew8 : ∀ y yn, m1 ≤ y → w8.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i →
            z < m1 := by
          intro y yn hy hyn c' z hz
          by_cases hym : y = m1
          · rw [hym, hw8m1] at hyn
            cases hyn
            have hm := liveAt_newKlongs_mem _ c.i c.i first c' z hz
            exact hchild z (hsnd z (first ++ ks2) hE' c' (List.mem_append_left _ hm))
          · by_cases hym2 : y = m1 + 2
            · rw [hym2, hw8m2] at hyn
              cases hyn
              have hm := liveAt_newKlongs_mem _ c.i c.i ks2 c' z hz
              exact hchild z (hsnd z (first ++ ks2) hE' c' (List.mem_append_right _ hm))
            · rw [h8old y (by omega) hym hym2, hnone3 y hy] at hyn; cases hyn
        have hhigh8 : ∀ y, w8.next ≤ y → w8.nodes.lookup y = none := by
          intro y hy
          rw [h8old y (by omega) (by omega) (by omega), hnone3 y (by omega)]
        obtain ⟨h8S2, h8T, h8S4, h8S5, h8S6, h8R0⟩ := mergeState_facts c base N root m1 w3 w8 s D X Nn
          hT h3top hfree hlinksAll hbaseF hS2 hS4 hR0
          (fun i h1 h2 => h8old _ (hXx i h1 h2) (by have := hXlt i h1 h2; omega)
            (by have := hXlt i h1 h2; omega)) h8taken
          (by rw [h8top, h7top, h6top, h5top, h4top]) (by omega) hlow8 hnew8 hhigh8
        have h8top' : w8.top.rootKey = root := by rw [h8top, h7top, h6top']
        have hm2N : N (m1 + 2) = none := (hfree _ (by omega)).1
        have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
        have hV8 : ∀ last, mergeFullLast pn c.i cL m1 cR (some (m1 + 2, g2)) = some last →
            TreeOK (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey ∧
            (∀ z, TReach (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey z →
              z ≠ l ∧ z ≠ r) ∧
            ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w8.next := by
          intro last hlast
          obtain ⟨_, hleafl, _, hsomeL⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h8top']
          have hVp : updN (wNode c.p base w8) p last p = some last := updN_self _ _ _
          have hVm1 : updN (wNode c.p base w8) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
            rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
          have hVm2 : updN (wNode c.p base w8) p last (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
            rw [updN_ne _ _ _ _ (by omega)]
            simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
          have hVN : ∀ y, y ≠ p → y ≠ m1 → y ≠ m1 + 2 → updN (wNode c.p base w8) p last y = N y := by
            intro y hyp hym hym2
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow8 y hy
            · have hyw : wNode c.p base w8 y = none := by
                simp only [wNode, h8taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h8old y (by omega) hym hym2, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          refine ⟨treeOK_mergeTwoAfter N _ c.i root p l r m1 (m1 + 2) pn ln rn last
            ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
            hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
            hm2N (hfreshT _ (by omega)) (by omega) hE hVm1
            (fun cc z hm => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm) hVm2
            (fun cc z hm => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm) hVp
            (hsomeL (m1 + 2) g2 rfl) (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2),
            fun z hz => ?_, fun c' z hm => ?_⟩
          · have := mergeV_reach N _ c.i root p l r m1 (some (m1 + 2)) pn ln rn last cL cR hT hp hpn hpL
              hpR hln hrn hVp
              (fun cc z hm => by
                rcases hsomeL (m1 + 2) g2 rfl cc z hm with ⟨_, h⟩ | ⟨_, h⟩ | h
                · exact Or.inl h
                · exact Or.inr (Or.inl (by rw [h]))
                · exact Or.inr (Or.inr h))
              (fun m mn hm hmn' cc z hz => by
                have hmem : (cc, z) ∈ first ++ ks2 := by
                  rcases hm with hm | hm
                  · rw [hm, hVm1] at hmn'
                    cases hmn'
                    exact List.mem_append_left _ (liveAt_newKlongs_mem _ c.i c.i first cc z hz)
                  · simp only [Option.some.injEq] at hm
                    rw [hm, hVm2] at hmn'
                    cases hmn'
                    exact List.mem_append_right _ (liveAt_newKlongs_mem _ c.i c.i ks2 cc z hz)
                rcases hsnd z (first ++ ks2) hE' cc hmem with ⟨c0, h0⟩ | ⟨c0, h0⟩
                · exact Or.inl ⟨c0, by rw [KNode.liveAt_of_times ln c.i hlt]; exact h0⟩
                · exact Or.inr ⟨c0, by rw [KNode.liveAt_of_times rn c.i hrt]; exact h0⟩)
              (fun y hyp _ _ hym hym2 => hVN y hyp hym (fun h => hym2 (by rw [h])))
              hm1R (fun m hm => by
                simp only [Option.some.injEq] at hm
                rw [hm]; exact not_reach_fresh N c.i root _ hT hm2N (hfreshT _ (by omega))) z hz
            exact ⟨this.2.1, this.2.2⟩
          · rcases hsomeL (m1 + 2) g2 rfl c' z hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        have hbr := writerWP_mergeFull_branch c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen hwf
          htimes htop hdist p l r m1 (some (m1 + 2, g2)) pn cL cR hXp hNp (hhalves m1 (some (m1 + 2, g2)))
          w8 (by rw [h8p, h7p, h6p, h5p, h4p]) h8S2 h8T h8S4 h8S5 h8S6 h8R0 hV8
          ⟨by omega, by omega⟩ last compact s9 hlast
        refine writerWP_mono hbr ?_
        rintro _ w11 ⟨hT11, hl11, hr11, ht11, _⟩
        refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w11 (hne' _ _)
          (by rw [ht11, h8taken]; exact hpT)) ?_
        rintro _ w12 ⟨h12top, _, _, _, h12l, h12ex, h12p⟩
        try simp only [writerWP_pure]
        rw [h12top]
        refine treeOK_after_cleanup (wNode c.p base w11) (wNode c.p base w12) c.i w11.top.rootKey p l r m1
          hT11 hl11 hr11 ?_ (fun y hyp hyl hyr => h12l y hyp (hcl' _ _ y hyl hyr)) (fun n' hn' => ?_)
        · by_cases hrp : w11.top.rootKey = p
          · rw [hrp]; exact h12ex (by rw [← hrp]; exact hT11.rootKey)
          · have hrl : w11.top.rootKey ≠ l := fun h => hl11 (h ▸ TReach.root)
            have hrr : w11.top.rootKey ≠ r := fun h => hr11 (h ▸ TReach.root)
            rw [h12l _ hrp (hcl' _ _ _ hrl hrr)]
            exact hT11.rootKey
        · obtain ⟨n, hn, _, hsub⟩ := h12p n' hn'
          refine ⟨n, hn, fun c' z hm => ?_⟩
          rcases hsub c' z hm with h | ⟨hz, q, hq, h⟩
          · exact Or.inl h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact Or.inr ⟨hz, Or.inl h⟩
            · exact Or.inr ⟨hz, Or.inr h⟩
      intro s9
      generalize hw9 : ({ ({ w8 with trail := s9 :: w8.trail } : W) with
        nodes := upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) } : W) = w9
      have h9n : w9.nodes = upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [← hw9]
      have h9t : w9.taken = w8.taken := by rw [← hw9]
      have h9top : w9.top = w8.top := by rw [← hw9]
      have hlk9 : w9.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [h9n, lookup_upsert]; simp
      refine writerWP_mono (writerWP_mergeCleanup_frame p m1 c.i c _ w9 _ (hne' _ _) hlk9
        (fun q hq c' hm => by
          rcases hchar2 (m1 + 2) g2 c' q.1 hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h <;> omega
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2)) ?_
      intro _ w10 ⟨h10top, _, h10t, h10l, pn10, h10p, h10sub⟩
      try simp only [writerWP_pure]
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' _ _ y hyl hyr), h9t, h8t, h7t, h6taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' _ _ y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
      rw [h10top, h9top, h8top, h7top, h6top']
      apply treeOK_mergeTwoAfter N (wNode c.p base w10) c.i root p l r m1 (m1 + 2) pn ln rn
        pn10 ⟨!!xn.leaf, newKlongs c.i first⟩
        ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
        hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
        (hfree _ (by omega)).1 (hfreshT _ (by omega)) (by omega) hE
      · simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), h8l,
          lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      · intro cc z hm
        exact liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
      · simp only [wNode, h10tc (m1 + 2) (by omega) (by omega), hm2T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' _ (by omega) (by omega) (by omega), h8l, lookup_append_single_self _ _ _ hw6m2]
      · intro cc z hm
        exact liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm
      · simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      · intro cc z hm
        exact hchar2 (m1 + 2) g2 cc z (h10sub cc z hm)
      · intro y hyp hyl hyr hym hym2
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr, h8l, lookup_append_single_ne _ _ _ _ hym2,
          h6old y (hyx y hyl hyr) hym]


/-- `sibling` keeps the path. -/
theorem writerWP_sibling_path (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W) :
    WriterWP (sibling p pn i inner) c w (fun _ v => v.path = w.path) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_cache _ c w) ?_
    intro sn v ⟨_, _, hp⟩
    split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_pure]; exact hp

/-- The writer's merge keeps the writer's tree, the parent with room or full
(`writerWP_merge_made_tree` without its room premises): a full parent p, at
depth D + 1 of the path, is split with the cascade above it, given the
cascade's premises (`writerWP_mergeTail_any_tree`). -/
theorem writerWP_merge_any_tree (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hsD : s ≤ D)
    (hd : d - 1 = D + 1)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (w.path[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → w.path[i]? = some (some (K i), X i))
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
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hR0 : s = 0 → w.top.rootKey = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hhalves : ∀ cL cR m1 m2 last, mergeFullLast (Nn (D + 1)) c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r0 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r0 < c'')) :
    WriterWP (merge x d) c w (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    exact ⟨by simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz], htz⟩
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    have hXp : X (D + 1) = e.2 := by
      have h1 : (w.path[d - 1]?).map (·.2) = some (X (D + 1)) := by
        rw [hd]; exact hX (D + 1) (by omega) (Nat.le_refl _)
      rw [he] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      exact h1.symm
    refine writerWP_mono (writerWP_and (writerWP_getNode_all e.2 c w base hvc)
      (writerWP_getNode_cache e.2 c w)) ?_
    intro pn w1 ⟨⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩, _, _, hp1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        w3.path = w.path →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL ≠ cR →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hp3 hL hLL hR hRL hc hxlr hln hrn
      have hNp : Nn (D + 1) = pn0 := by
        have h1 := (hS2 (D + 1) (by omega) (Nat.le_refl _)).1
        rw [hXp] at h1
        have h2 := lookup_of_prefix _ _ hpre1 _ _ h1
        rw [hlk1] at h2
        exact (Option.some.inj h2).symm
      apply writerWP_mergeTail_any_tree c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR (hwn1 (hRt _ hpR)) hL hLL hR hRL hc hxlr
        hln hrn hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hvc hlinksAll
        hbaseF s D X K Nn hsD hd (by rw [hp3]; exact hX) (by rw [hp3]; exact hK) hlinkK hrange hlen
        hwf htimes htop hdist hXp hNp
        (fun i h1 h2 => ⟨lookup_of_prefix _ _ (hpre1.trans hpre3) _ _ (hS2 i h1 h2).1,
          by rw [hr3.2.2.1]; exact (hS2 i h1 h2).2⟩)
        hS4
        hR0 hXx (fun m1 m2 last h => hhalves cL cR m1 m2 last (by rw [hNp]; exact h))
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn0, hpn, hm⟩⟩
    have hptrk : ∀ i cv y, LastLive pn0.ks pn0.lastBitmap i cv → pn0.ptr? i = some y →
        pn0.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    refine writerWP_mono (writerWP_and (writerWP_getNode_all x c w1 base hvc)
      (writerWP_getNode_cache x c w1)) ?_
    intro xn w2 ⟨⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩, _, _, hp2⟩
    have hp02 : w2.path = w.path := by rw [hp2, hp1]
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · rcases hsrc1 z h with h' | h'
        · exact hidn z h'
        · exact hidv z h'
      · exact hidv z h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn0 cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn0 cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn0.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- the step after a sibling is read: both nodes known
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (∀ z, (w3.nodes.lookup z).isSome = true → (wb.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes ∧
              (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) := by
          intro wb i cv sn w3 hrb hpreb hsrcb hl hp hr3 hpre3 hsrc3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3, ?_⟩
          · rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
          · intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrcb z h
            · exact hidv z h
        -- the right sibling, read from a state wb
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) → wb.path = w.path →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hsrcb hpb hLa hax
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_all e.2 pn0 ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_path e.2 pn0 ia0 (!xn.leaf) c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨hs1, hr4, _, hwn4, hpre4, hsrc4⟩, hp4⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 (by rw [hp4, hpb]) hkx hLx
            hka hLa
            (by omega) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_all e.2 pn0 ib0 (!xn.leaf) c w2 base hvc)
            (writerWP_sibling_path e.2 pn0 ib0 (!xn.leaf) c w2)) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨⟨hs1, hr3, _, hwn3, hpre3, hsrc3⟩, hp3⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hkb hLb
              hkx hLx
              (by omega) (Or.inr rfl) hln hxn
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hLa hax
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hp02 hLa hax
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
