/-
The merge's full last version is sorted (bergdb 024-22): `mergeFullLast` is a
time klong and key klongs sorted by compare value, when the second new node's
first compare value g, if it is not the right child's, is no other live compare
value of the parent. This gives `hsorted` of `writerWP_merge_any_get`.
-/
import SIS.Tree.WriterTreeMergeFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem cvSorted_of_fst {a b : List (Nat × NodeId)} (h : a.map Prod.fst = b.map Prod.fst)
    (hb : CvSorted b) : CvSorted a := by
  have hb' : (b.map Prod.fst).Pairwise (· < ·) := List.pairwise_map.mpr hb
  rw [← h] at hb'
  exact List.pairwise_map.mp hb'

/-- Inserting a pair of a new compare value keeps pairs sorted. -/
theorem insPairs_sorted (g : Nat) (y : NodeId) :
    ∀ l : List (Nat × NodeId), CvSorted l → (∀ q ∈ l, q.1 ≠ g) → CvSorted (insPairs l g y) := by
  intro l
  induction l with
  | nil => intro _ _; simp [insPairs, CvSorted]
  | cons q r ih =>
    intro hs hg
    have hq : q.1 ≠ g := hg q List.mem_cons_self
    have hr : CvSorted r := List.Pairwise.of_cons hs
    by_cases hlt : g < q.1
    · simp only [insPairs, hlt, ↓reduceIte]
      refine List.Pairwise.cons ?_ hs
      intro a ha
      rcases List.mem_cons.mp ha with h | h
      · rw [h]; exact hlt
      · have := List.rel_of_pairwise_cons hs h; simp only at this ⊢; omega
    · simp only [insPairs, hlt, Bool.false_eq_true, ↓reduceIte]
      refine List.Pairwise.cons ?_ (ih hr (fun q' hq' => hg q' (List.mem_cons_of_mem _ hq')))
      intro a ha
      have hmem : a = (g, y) ∨ a ∈ r := by
        clear ih hr hs hg
        induction r with
        | nil => simp [insPairs] at ha; exact Or.inl ha
        | cons q2 r2 ih2 =>
          by_cases h2 : g < q2.1
          · simp only [insPairs, h2, ↓reduceIte, List.mem_cons] at ha
            rcases ha with h | h | h
            · exact Or.inl h
            · exact Or.inr (by rw [h]; exact List.mem_cons_self)
            · exact Or.inr (List.mem_cons_of_mem _ h)
          · simp only [insPairs, h2, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at ha
            rcases ha with h | h
            · exact Or.inr (by rw [h]; exact List.mem_cons_self)
            · rcases ih2 h with h' | h'
              · exact Or.inl h'
              · exact Or.inr (List.mem_cons_of_mem _ h')
      rcases hmem with h | h
      · rw [h]; simp only; omega
      · exact List.rel_of_pairwise_cons hs h

/-- `mergeFullLast` is a time klong and key klongs sorted by compare value, when
the second new node's first compare value, if not the right child's, is not live
in the parent. -/
theorem mergeFullLast_sorted (pn : KNode) (tt : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (last : KNode) (h : mergeFullLast pn tt cL m1 cR m2 = some last)
    (hg : ∀ y g, m2 = some (y, g) → g ≠ cR → pn.live.lookup g = none) :
    ∃ pairs, last.ks = newKlongs tt pairs ∧ CvSorted pairs := by
  -- the last version's pairs, without cR if deleteR
  have hbase : ∀ (deleteR : Bool) (union : List Nat),
      union = (if deleteR = true then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap) →
      ∃ pairs, (pn.lastVersionGivenDel tt union).ks = newKlongs tt pairs ∧ CvSorted pairs ∧
        (pairs.map Prod.fst).Nodup ∧
        ∀ c, pairs.lookup c = if deleteR = true ∧ c = cR then none else pn.live.lookup c := by
    intro deleteR union hun
    obtain ⟨pairs, hks, hord⟩ := pn.lastVersionGivenDel_order tt union
    have hnd : (pairs.map Prod.fst).Nodup :=
      List.pairwise_map.mpr (hord.imp (by intro a b hab; omega))
    refine ⟨pairs, hks, hord, hnd, fun c => ?_⟩
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
    rw [← pairLookupFold_eq_lookup pairs c hnd, ← h3, h2, hun]
    cases deleteR with
    | true =>
      simp only [↓reduceIte, true_and]
      rw [keyLookup_delete_union]
      by_cases hc : c = cR <;> simp [hc]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, false_and]
      exact (KNode.live_lookup pn c).symm
  -- the left child's klong to m1
  have hleft : ∀ (union : List Nat) (pairs : List (Nat × NodeId)),
      (pn.lastVersionGivenDel tt union).ks = newKlongs tt pairs → CvSorted pairs →
      ∀ (k : KNode → Option KNode),
      (match replaceKlong (pn.lastVersionGivenDel tt union).ks tt cL m1 with
        | .ok (some ks) => k { pn.lastVersionGivenDel tt union with ks := ks }
        | _ => none) = some last →
      ∃ out, replacePairFirst pairs cL m1 = some out ∧ CvSorted out ∧
        out.map Prod.fst = pairs.map Prod.fst ∧
        k { pn.lastVersionGivenDel tt union with ks := newKlongs tt out } = some last := by
    intro union pairs hks hord k hk
    rw [hks, replaceKlong_newKlongs] at hk
    cases hr1 : replacePairFirst pairs cL m1 with
    | none => rw [hr1] at hk; cases hk
    | some out =>
      rw [hr1] at hk
      obtain ⟨hkeys1, _⟩ := replacePairFirst_some pairs out cL m1 hr1
      exact ⟨out, rfl, cvSorted_of_fst hkeys1 hord, hkeys1, hk⟩
  cases m2 with
  | none =>
    unfold mergeFullLast at h
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_true] at h
    obtain ⟨pairs, hks, hord, _, _⟩ := hbase true _ rfl
    obtain ⟨out, _, hs1, _, hk⟩ := hleft _ pairs hks hord (fun l => some l) h
    simp only [Option.some.injEq] at hk
    rw [← hk]; exact ⟨out, rfl, hs1⟩
  | some yg =>
    obtain ⟨y, g⟩ := yg
    by_cases hgR : g = cR
    · subst hgR
      unfold mergeFullLast at h
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨pairs, hks, hord, _, _⟩ := hbase false _ rfl
      obtain ⟨out, _, hs1, _, hk⟩ := hleft _ pairs hks hord
        (fun l => match replaceKlong l.ks tt g y with
          | .ok (some ks2) => some { l with ks := ks2 }
          | _ => none) h
      simp only at hk
      rw [replaceKlong_newKlongs] at hk
      cases hr2 : replacePairFirst out g y with
      | none => rw [hr2] at hk; cases hk
      | some out2 =>
        rw [hr2] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        obtain ⟨hkeys2, _⟩ := replacePairFirst_some out out2 g y hr2
        rw [← hk]; exact ⟨out2, rfl, cvSorted_of_fst hkeys2 hs1⟩
    · have hb : (g != cR) = true := by simpa using hgR
      unfold mergeFullLast at h
      simp only [hb, ↓reduceIte] at h
      obtain ⟨pairs, hks, hord, hnd, hl0⟩ := hbase true _ rfl
      obtain ⟨out, _, hs1, hkeys1, hk⟩ := hleft _ pairs hks hord
        (fun l => some { l with ks := insertSorted l.ks g y }) h
      simp only [Option.some.injEq] at hk
      rw [← hk]
      refine ⟨insPairs out g y, ?_, ?_⟩
      · show insertSorted (newKlongs tt out) g y = _
        simp only [newKlongs, insertSorted]
        rw [insertSorted_pairs]
      · have hpg := hg y g rfl hgR
        have hng : pairs.lookup g = none := by rw [hl0 g]; simp [hgR, hpg]
        apply insPairs_sorted g y out hs1
        intro q hq hqg
        have hm : q.1 ∈ out.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
        rw [hkeys1, hqg] at hm
        obtain ⟨q', hq', he⟩ := List.mem_map.mp hm
        have := lookup_of_mem_nodup _ hnd g q'.2 (by rw [← he]; exact hq')
        rw [hng] at this; cases this

end SIS.Tree
