/-
`htb`'s sites (bergdb 025-05, step 8): the parent's node after a merge into two. The
parent names both new nodes (with room, `mergeParentNode`; full, its last version), or,
split in place, its first half has two live klongs or names the second new node beside
another node of the transaction (`mergeFullLast` sorted with at most the second new
node's compare value twice).
-/
import SIS.Tree.HtbExcFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.add_getElem_lt (n : KNode) (t : Time) (k : Klong) (i : Nat) (h : i < n.ks.length) :
    (n.add t k).ks[i]? = n.ks[i]? := by
  rcases KNode.add_ks n t k with e | e <;> rw [e] <;> exact List.getElem?_append_left h

theorem KNode.add_last_mem (n : KNode) (t : Time) (k : Klong) : ∃ i : Nat, (n.add t k).ks[i]? = some k := by
  rcases KNode.add_ks n t k with e | e <;> rw [e]
  · exact ⟨n.ks.length + 1, by simp⟩
  · exact ⟨n.ks.length, by simp⟩

theorem KNode.add_length (n : KNode) (t : Time) (k : Klong) : n.ks.length < (n.add t k).ks.length := by
  rcases KNode.add_ks n t k with e | e <;> rw [e] <;> simp

theorem KNode.setAt_getElem_ne (n : KNode) (i : Nat) (k : Klong) (j : Nat) (h : j ≠ i) :
    (n.setAt i k).ks[j]? = n.ks[j]? := by
  simp only [KNode.setAt]; exact List.getElem?_set_ne (Ne.symm h)

theorem KNode.setAt_length (n : KNode) (i : Nat) (k : Klong) : (n.setAt i k).ks.length = n.ks.length := by
  simp [KNode.setAt]

theorem KNode.repoint_getElem_ne (n : KNode) (i : Nat) (y : NodeId) (j : Nat) (h : j ≠ i) :
    (n.repoint i y).ks[j]? = n.ks[j]? := by
  unfold KNode.repoint; split
  · exact KNode.setAt_getElem_ne n i _ j h
  · rfl

theorem KNode.repoint_getElem_self (n : KNode) (i : Nat) (c : Nat) (z y : NodeId)
    (h : n.ks[i]? = some (Klong.key c z)) : (n.repoint i y).ks[i]? = some (Klong.key c y) := by
  unfold KNode.repoint; rw [h]
  simp only [KNode.setAt]
  have hi : i < n.ks.length := (List.getElem?_eq_some_iff.mp h).1
  simp [hi]

theorem KNode.repoint_length (n : KNode) (i : Nat) (y : NodeId) : (n.repoint i y).ks.length = n.ks.length := by
  unfold KNode.repoint; split
  · exact KNode.setAt_length n i _
  · rfl

/-- The parent after a merge into two with room names both new nodes. -/
theorem mpNode_names (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (y : NodeId) (g : Nat) (l r : NodeId) (hL : pn.ks[il]? = some (Klong.key cL l))
    (hR : pn.ks[ir]? = some (Klong.key cR r)) (hc : cL ≠ cR) (htd lip rip : Bool)
    (hhtd : htd = true → ∃ b, pn.ks.getLast? = some (Klong.del b)) :
    (∃ (i cv : Nat), (mpNode pn tt il cL m1 ir cR (some (y, g)) htd lip rip).ks[i]? = some (Klong.key cv m1)) ∧
    (∃ (j cv : Nat), (mpNode pn tt il cL m1 ir cR (some (y, g)) htd lip rip).ks[j]? = some (Klong.key cv y)) := by
  have hne : il ≠ ir := by
    intro e; subst e; rw [hL] at hR; cases hR; exact hc rfl
  have hil : il < pn.ks.length := (List.getElem?_eq_some_iff.mp hL).1
  have hir : ir < pn.ks.length := (List.getElem?_eq_some_iff.mp hR).1
  -- the first step keeps the klongs at il and ir
  have hkeep : ∀ (n1 : KNode), (n1 = pn ∨ (htd = true ∧ ∃ k, n1 = pn.setAt (pn.size - 1) k) ∨
      ∃ k, n1 = pn.add tt k) → ∀ j, (pn.ks[j]? = some (Klong.key cL l) ∨ pn.ks[j]? = some (Klong.key cR r)) →
      n1.ks[j]? = pn.ks[j]? ∧ j < n1.ks.length := by
    intro n1 hn1 j hjk
    have hj : j < pn.ks.length := by
      rcases hjk with h1 | h1 <;> exact (List.getElem?_eq_some_iff.mp h1).1
    rcases hn1 with rfl | ⟨hht, k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨rfl, hj⟩
    · obtain ⟨b, hb⟩ := hhtd hht
      have hjl : j ≠ pn.size - 1 := by
        intro e
        simp only [KNode.size] at e
        subst e
        rw [← List.getLast?_eq_getElem?, hb] at hjk
        rcases hjk with h1 | h1 <;> cases h1
      exact ⟨KNode.setAt_getElem_ne pn _ _ j hjl, by rw [KNode.setAt_length]; exact hj⟩
    · exact ⟨KNode.add_getElem_lt pn tt _ j hj, Nat.lt_trans hj (KNode.add_length pn tt _)⟩
  -- the last two steps
  have hsteps : ∀ (n1 : KNode), n1.ks[il]? = some (Klong.key cL l) → n1.ks[ir]? = some (Klong.key cR r) →
      ir < n1.ks.length → ∀ (cv' : Nat),
      (∃ (i cv : Nat), (if rip = true then (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)).repoint ir y
        else (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)).add tt (Klong.key cv' y)).ks[i]? =
          some (Klong.key cv m1)) ∧
      (∃ (j cv : Nat), (if rip = true then (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)).repoint ir y
        else (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)).add tt (Klong.key cv' y)).ks[j]? =
          some (Klong.key cv y)) := by
    intro n1 hL1 hR1 hir1 cv'
    have hn2 : ∃ i, (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)).ks[i]? =
        some (Klong.key cL m1) ∧ (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)).ks[ir]? =
        some (Klong.key cR r) ∧ i ≠ ir := by
      cases lip
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨i, hi⟩ := KNode.add_last_mem n1 tt (Klong.key cL m1)
        refine ⟨i, hi, by rw [KNode.add_getElem_lt n1 tt _ ir hir1]; exact hR1, ?_⟩
        intro e; subst e
        rw [KNode.add_getElem_lt n1 tt _ i hir1, hR1] at hi; cases hi; exact hc rfl
      · simp only [↓reduceIte]
        exact ⟨il, KNode.repoint_getElem_self n1 il cL l m1 hL1,
          by rw [KNode.repoint_getElem_ne n1 il m1 ir (Ne.symm hne)]; exact hR1, hne⟩
    obtain ⟨i, hi, hir2, hine⟩ := hn2
    generalize (if lip = true then n1.repoint il m1 else n1.add tt (Klong.key cL m1)) = n2 at hi hir2 ⊢
    refine ⟨?_, ?_⟩
    · cases rip
      · have hil2 : i < n2.ks.length := (List.getElem?_eq_some_iff.mp hi).1
        exact ⟨i, cL, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [KNode.add_getElem_lt n2 tt _ i hil2]; exact hi⟩
      · exact ⟨i, cL, by simp only [↓reduceIte]; rw [KNode.repoint_getElem_ne n2 ir y i hine]; exact hi⟩
    · cases rip
      · obtain ⟨j, hj⟩ := KNode.add_last_mem n2 tt (Klong.key cv' y)
        exact ⟨j, cv', by simp only [Bool.false_eq_true, ↓reduceIte]; exact hj⟩
      · exact ⟨ir, cR, by simp only [↓reduceIte]; exact KNode.repoint_getElem_self n2 ir cR r y hir2⟩
  unfold mpNode
  simp only
  generalize hn1e : (if (!(g != cR)) = true then pn
    else if htd = true then pn.setAt (pn.size - 1) (Klong.del (if (g != cR) = true then bitsUnion pn.lastBitmap
      (pn.bitsOf cR) else pn.lastBitmap)) else pn.add tt (Klong.del (if (g != cR) = true then
      bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap))) = n1
  have hn1 : n1 = pn ∨ (htd = true ∧ ∃ k, n1 = pn.setAt (pn.size - 1) k) ∨ ∃ k, n1 = pn.add tt k := by
    rw [← hn1e]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl ⟨by assumption, _, rfl⟩)
      · exact Or.inr (Or.inr ⟨_, rfl⟩)
  obtain ⟨hL1, -⟩ := hkeep n1 hn1 il (Or.inl hL)
  obtain ⟨hR1, hir1⟩ := hkeep n1 hn1 ir (Or.inr hR)
  rw [hL] at hL1
  rw [hR] at hR1
  exact hsteps n1 hL1 hR1 hir1 _

theorem mergeParentNode_names (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (y : NodeId) (g : Nat) (l r : NodeId) (hL : pn.ks[il]? = some (Klong.key cL l))
    (hR : pn.ks[ir]? = some (Klong.key cR r)) (hc : cL ≠ cR) :
    (∃ (i cv : Nat), (mergeParentNode pn tt il cL m1 ir cR (some (y, g))).ks[i]? = some (Klong.key cv m1)) ∧
    (∃ (j cv : Nat), (mergeParentNode pn tt il cL m1 ir cR (some (y, g))).ks[j]? = some (Klong.key cv y)) := by
  rw [mergeParentNode_eq]
  refine mpNode_names pn tt il cL m1 ir cR y g l r hL hR hc _ _ _ ?_
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  split at h1
  · rename_i b hb; exact ⟨b, hb⟩
  · cases h1

/-- The klong at index i after `retargetKlongs`. -/
theorem retargetKlongs_getElem (ks : List Klong) (ti : Nat) (src dst : NodeId) (i : Nat) :
    (retargetKlongs ks ti src dst)[i]? = (ks[i]?).map (fun k => match k with
      | .key cv y => if ti < i && y == src then Klong.key cv dst else k
      | _ => k) := by
  unfold retargetKlongs
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases ks[i]? with
  | none => rfl
  | some k =>
    simp only [Option.map_some, Nat.zero_add]
    cases k <;> rfl

theorem mem_insPairs (l : List (Nat × NodeId)) (g : Nat) (y : NodeId) (q : Nat × NodeId) :
    q ∈ insPairs l g y ↔ q = (g, y) ∨ q ∈ l := by
  induction l with
  | nil => simp [insPairs]
  | cons a r ih =>
    simp only [insPairs]
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- The first two pairs after an insertion into sorted pairs: two compare values, or the
pair inserted after one of its compare value. -/
theorem insPairs_first_two (l : List (Nat × NodeId)) (g : Nat) (y : NodeId) (hs : CvSorted l)
    (a b : Nat × NodeId) (rest : List (Nat × NodeId)) (h : insPairs l g y = a :: b :: rest) :
    a.1 ≠ b.1 ∨ (b = (g, y) ∧ a ∈ l) := by
  cases l with
  | nil => simp [insPairs] at h
  | cons o os =>
    simp only [insPairs] at h
    split at h
    · rename_i hlt
      simp only [List.cons.injEq] at h
      obtain ⟨ha, hb, -⟩ := h
      rw [← ha, ← hb]
      left; simp only [ne_eq]; omega
    · simp only [List.cons.injEq] at h
      obtain ⟨ha, h2⟩ := h
      rw [← ha]
      cases os with
      | nil =>
        simp only [insPairs, List.cons.injEq] at h2
        obtain ⟨hb, -⟩ := h2
        rw [← hb]
        by_cases he : o.1 = g
        · exact Or.inr ⟨rfl, List.mem_cons_self⟩
        · left; simpa using he
      | cons o' os' =>
        simp only [insPairs] at h2
        split at h2
        · simp only [List.cons.injEq] at h2
          obtain ⟨hb, -⟩ := h2
          rw [← hb]
          by_cases he : o.1 = g
          · exact Or.inr ⟨rfl, List.mem_cons_self⟩
          · left; simpa using he
        · simp only [List.cons.injEq] at h2
          obtain ⟨hb, -⟩ := h2
          rw [← hb]
          left
          have := List.rel_of_pairwise_cons hs List.mem_cons_self
          try simp only at this
          simp only [ne_eq]; omega

/-- The full parent's last version after a merge into two: sorted pairs with the left
child's compare value naming m1, one naming the second new node y, the others the
parent's live klongs; its first two pairs are of two compare values, or the second
names y and the first is m1's or the parent's. -/
theorem mergeFullLast_two (pn : KNode) (tt : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (y : NodeId) (g : Nat) (last : KNode) (hc : cL ≠ cR)
    (h : mergeFullLast pn tt cL m1 cR (some (y, g)) = some last) :
    ∃ pairs, last.ks = newKlongs tt pairs ∧ (∃ cv, (cv, m1) ∈ pairs) ∧ (∃ cv, (cv, y) ∈ pairs) ∧
      (∀ q ∈ pairs, q.2 = m1 ∨ q.2 = y ∨ q ∈ pn.live) ∧
      (∀ a b rest, pairs = a :: b :: rest → a.1 ≠ b.1 ∨ (b.2 = y ∧ (a.2 = m1 ∨ a ∈ pn.live))) := by
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
  -- elements of a list with distinct compare values and its lookups
  have hmemL : ∀ (l : List (Nat × NodeId)), (l.map Prod.fst).Nodup → ∀ q ∈ l, l.lookup q.1 = some q.2 :=
    fun l hn q hq => lookup_of_mem_nodup l hn q.1 q.2 hq
  have hsub0 : ∀ (deleteR : Bool) (pairs : List (Nat × NodeId)), (pairs.map Prod.fst).Nodup →
      (∀ c, pairs.lookup c = if deleteR = true ∧ c = cR then none else pn.live.lookup c) →
      ∀ q ∈ pairs, q ∈ pn.live := by
    intro deleteR pairs hnd hl q hq
    have h1 := hmemL pairs hnd q hq
    rw [hl] at h1
    split at h1
    · cases h1
    · exact bk_mem_of_lookup _ _ _ h1
  have hrep : ∀ (pairs out : List (Nat × NodeId)) (cv : Nat) (z : NodeId),
      (pairs.map Prod.fst).Nodup → replacePairFirst pairs cv z = some out →
      (out.map Prod.fst).Nodup ∧ (cv, z) ∈ out ∧ ∀ q ∈ out, q = (cv, z) ∨ q ∈ pairs := by
    intro pairs out cv z hnd hr
    obtain ⟨hk, hl⟩ := replacePairFirst_some pairs out cv z hr
    have hnd' : (out.map Prod.fst).Nodup := by rw [hk]; exact hnd
    refine ⟨hnd', bk_mem_of_lookup _ _ _ (by rw [hl]; simp), fun q hq => ?_⟩
    have h1 := hmemL out hnd' q hq
    rw [hl] at h1
    by_cases hq1 : cv = q.1
    · simp only [hq1, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h1
      left; rw [hq1, h1]
    · have : (cv == q.1) = false := by simpa using hq1
      rw [this] at h1
      exact Or.inr (bk_mem_of_lookup _ _ _ (by simpa using h1))
  unfold mergeFullLast at h
  simp only at h
  by_cases hgR : g = cR
  · subst hgR
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨pairs0, hks, hord, hnd, hl0⟩ := hbase false pn.lastBitmap (by simp)
    rw [hks, replaceKlong_newKlongs] at h
    cases hr1 : replacePairFirst pairs0 cL m1 with
    | none => rw [hr1] at h; cases h
    | some out =>
      rw [hr1] at h
      simp only [Option.map_some] at h
      rw [replaceKlong_newKlongs] at h
      cases hr2 : replacePairFirst out g y with
      | none => rw [hr2] at h; cases h
      | some out2 =>
        rw [hr2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hnd1, hm1, hs1⟩ := hrep pairs0 out cL m1 hnd hr1
        obtain ⟨hnd2, hm2, hs2⟩ := hrep out out2 g y hnd1 hr2
        have hsort : CvSorted out2 := cvSorted_of_fst (replacePairFirst_some out out2 g y hr2).1
          (cvSorted_of_fst (replacePairFirst_some pairs0 out cL m1 hr1).1 hord)
        have hm1' : (cL, m1) ∈ out2 := by
          obtain ⟨-, hl2⟩ := replacePairFirst_some out out2 g y hr2
          have hne : (g == cL) = false := beq_eq_false_iff_ne.mpr (fun e => hc e.symm)
          refine bk_mem_of_lookup _ _ _ ?_
          rw [hl2, hne]; exact hmemL out hnd1 _ hm1
        refine ⟨out2, by rw [← h], ⟨cL, hm1'⟩, ⟨g, hm2⟩, fun q hq => ?_, fun a b rest he => ?_⟩
        · rcases hs2 q hq with h1 | h1
          · rw [h1]; exact Or.inr (Or.inl rfl)
          · rcases hs1 q h1 with h2 | h2
            · rw [h2]; exact Or.inl rfl
            · exact Or.inr (Or.inr (hsub0 false pairs0 hnd hl0 q h2))
        · subst he
          left
          have := List.rel_of_pairwise_cons hsort List.mem_cons_self
          try simp only at this
          simp only [ne_eq]; omega
  · have hb : (g != cR) = true := by simpa using hgR
    simp only [hb, ↓reduceIte] at h
    obtain ⟨pairs0, hks, hord, hnd, hl0⟩ := hbase true (bitsUnion pn.lastBitmap (pn.bitsOf cR)) (by simp)
    rw [hks, replaceKlong_newKlongs] at h
    cases hr1 : replacePairFirst pairs0 cL m1 with
    | none => rw [hr1] at h; cases h
    | some out =>
      rw [hr1] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hnd1, hm1, hs1⟩ := hrep pairs0 out cL m1 hnd hr1
      have hsort1 : CvSorted out := cvSorted_of_fst (replacePairFirst_some pairs0 out cL m1 hr1).1 hord
      refine ⟨insPairs out g y, ?_, ⟨cL, (mem_insPairs out g y _).mpr (Or.inr hm1)⟩,
        ⟨g, (mem_insPairs out g y _).mpr (Or.inl rfl)⟩, fun q hq => ?_, fun a b rest he => ?_⟩
      · rw [← h]
        show insertSorted (newKlongs tt out) g y = _
        simp only [newKlongs, insertSorted]
        rw [insertSorted_pairs]
      · rcases (mem_insPairs out g y q).mp hq with h1 | h1
        · rw [h1]; exact Or.inr (Or.inl rfl)
        · rcases hs1 q h1 with h2 | h2
          · rw [h2]; exact Or.inl rfl
          · exact Or.inr (Or.inr (hsub0 true pairs0 hnd hl0 q h2))
      · rcases insPairs_first_two out g y hsort1 a b rest he with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · refine Or.inr ⟨by rw [h1], ?_⟩
          rcases hs1 a h2 with h3 | h3
          · rw [h3]; exact Or.inl rfl
          · exact Or.inr (hsub0 true pairs0 hnd hl0 a h3)

end SIS.Tree
