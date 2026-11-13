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

end SIS.Tree
