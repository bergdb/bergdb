/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)): the
nodes that the delete's steps store meet `NodeHt` (a bitmap set in place or
added, a retarget, a last version given a delete).
-/
import SIS.Tree.WriterHeightsPut
import SIS.Tree.HalvesNil

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

/-! ## The klongs before the transaction -/

/-- Setting a klong after a time klong past t leaves the klongs up to t. -/
theorem ht_prefixAt_set_after (t : Time) :
    ∀ (ks : List Klong) (i j : Nat) (u : Time) (k : Klong), i < j → ks[i]? = some (.time u) →
      t < u → prefixAt (ks.set j k) t = prefixAt ks t
  | [], _, _, _, _, _, h, _ => by simp at h
  | a :: ks, 0, j, u, k, hij, hi, hu => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    unfold prefixAt
    simp only [List.set_cons_succ, List.takeWhile_cons]
    have : decide (u ≤ t) = false := by simp; omega
    simp [this]
  | a :: ks, i + 1, j, u, k, hij, hi, hu => by
    simp only [List.getElem?_cons_succ] at hi
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have ih := ht_prefixAt_set_after t ks i j' u k (by omega) hi hu
    unfold prefixAt at ih ⊢
    simp only [List.set_cons_succ, List.takeWhile_cons]
    rw [ih]

theorem ht_lastTime_index {n : KNode} {t : Time} (h : n.lastTime = some t) :
    ∃ i : Nat, n.ks[i]? = some (Klong.time t) := by
  have hm : Klong.time t ∈ n.ks := lastTimeOf_some_mem n.ks t h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨i, hi⟩

/-! ## The nodes -/

/-- The transaction's own bitmap, set in place to delete cv as well. -/
theorem nodeHt_setAt_del {c : Ctx} {w : W} {h : Nat} {n : KNode} (hpos : 0 < c.i)
    (hn : NodeHt c H w h n) (old : List Nat) (hlast : n.ks.getLast? = some (.del old))
    (ht : n.lastTime = some c.i) (cv : Nat) :
    NodeHt c H w h (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) := by
  refine ⟨fun c' y hy => ?_, fun c' y hy => ?_, fun s hs => ?_⟩
  · have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' y hy
    rw [KNode.setAt_delete_live_lookup n cv c' old hlast] at hl
    split at hl
    · cases hl
    · exact hn.1 c' y (mem_of_lookup_nodup _ c' y hl)
  · obtain ⟨i, hi⟩ := ht_lastTime_index ht
    have hsz : 0 < n.ks.length := by
      cases hks : n.ks with
      | nil => rw [hks] at hlast; simp at hlast
      | cons _ _ => simp
    have hlastIdx : n.ks[n.ks.length - 1]? = some (.del old) := by
      rw [← List.getLast?_eq_getElem?]; exact hlast
    have hij : i < n.size - 1 := by
      have hil := (List.getElem?_eq_some_iff.mp hi).1
      unfold KNode.size
      rcases Nat.lt_or_ge i (n.ks.length - 1) with h1 | h1
      · exact h1
      · have : i = n.ks.length - 1 := by omega
        subst this
        rw [hlastIdx] at hi
        cases hi
    have hpre : prefixAt (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks
        (c.i - 1) = prefixAt n.ks (c.i - 1) :=
      ht_prefixAt_set_after (c.i - 1) n.ks i (n.size - 1) c.i _ hij hi (by omega)
    have he : (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).toPrev (c.i - 1) =
        n.toPrev (c.i - 1) := by
      unfold KNode.toPrev; rw [hpre]; rfl
    rw [he] at hy
    exact hn.2 c' y hy
  · rcases List.mem_or_eq_of_mem_set hs with hs | hs
    · exact hn.3 s hs
    · cases hs

/-- A new bitmap that deletes cv as well. -/
theorem nodeHt_add_del {c : Ctx} {w : W} {h : Nat} {n : KNode} (hpos : 0 < c.i)
    (hn : NodeHt c H w h n) (cv : Nat) :
    NodeHt c H w h (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) := by
  refine ⟨fun c' y hy => ?_, fun c' y hy => ?_, ht_add_times hn.3 (fun t h => by cases h)⟩
  · have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' y hy
    rw [KNode.add_delete_live_lookup n c.i cv c'] at hl
    split at hl
    · cases hl
    · exact hn.1 c' y (mem_of_lookup_nodup _ c' y hl)
  · have he : (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).toPrev (c.i - 1) =
        n.toPrev (c.i - 1) := by
      unfold KNode.toPrev; rw [KNode.add_prefixAt_past n c.i (c.i - 1) (by omega), KNode.add_leaf]
    rw [he] at hy
    exact hn.2 c' y hy

/-- The key klongs of a last version are its live klongs. -/
theorem ht_flat_live {L : KNode} {t : Time}
    (hL : ∃ pairs : List (Nat × NodeId), L.ks = .time t :: pairs.map (fun q => .key q.1 q.2) ∧
      pairs.Pairwise (fun a b => a.1 < b.1)) {cv : Nat} {y : NodeId}
    (hm : Klong.key cv y ∈ L.ks) : (cv, y) ∈ L.live := by
  obtain ⟨pairs, hks, hs⟩ := hL
  have hlive : L.live = pairs := by
    have := KNode.live_newKlongs_sorted L.leaf t pairs hs
    have he : L = ⟨L.leaf, newKlongs t pairs⟩ := by
      cases L; simp only at hks ⊢; rw [hks]; rfl
    rw [he]; exact this
  rw [hlive]
  rw [hks] at hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    cases he
    exact hq

/-- A last version given the delete of cv: klongs of the right height. -/
theorem htKs_lastVersion_del {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n)
    (t : Time) (cv : Nat) :
    kdKs (HtP c H w h) (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks := by
  intro c' y hm
  have hl0 := ht_flat_live (KNode.lastVersionGivenDel_order n t _) hm
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' y hl0
  rw [KNode.delete_live_lookup n t cv c'] at hl
  split at hl
  · cases hl
  · exact hn.1 c' y (mem_of_lookup_nodup _ c' y hl)

/-- A retarget of the transaction's klongs that name src to dst, a node of the
right height. -/
theorem nodeHt_retarget {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n)
    (ti : Nat) (src dst : NodeId) (hd : ∀ cv, HtP c H w h cv dst) :
    NodeHt c H w h { n with ks := retargetKlongs n.ks ti src dst } := by
  have hf : PtrSwapL (fun z => z = dst) n.ks (retargetKlongs n.ks ti src dst) := by
    unfold retargetKlongs
    generalize n.ks = ks
    suffices hs : ∀ (k0 : Nat) (ks : List Klong), PtrSwapL (fun z => z = dst) ks
        ((ks.zipIdx k0).map (fun (k, i) => match k with
          | .key cv y => if ti < i && y == src then Klong.key cv dst else k
          | _ => k)) by exact hs 0 ks
    intro k0 ks
    induction ks generalizing k0 with
    | nil => trivial
    | cons k ks ih =>
      simp only [List.zipIdx_cons, List.map_cons]
      refine ⟨?_, ih (k0 + 1)⟩
      cases k with
      | time u => exact Or.inl rfl
      | del b => exact Or.inl rfl
      | key a y =>
        simp only
        split
        · exact Or.inr ⟨a, y, dst, rfl, rfl, rfl⟩
        · exact Or.inl rfl
  refine ⟨fun cv z hz => ?_, fun cv z hz => ?_, fun s hs => ?_⟩
  · rcases ht_live_swap (n := n) (n' := { n with ks := retargetKlongs n.ks ti src dst }) hf hz with
      h1 | rfl
    · exact hn.1 cv z h1
    · exact hd cv
  · have hf' := ht_swapL_prefixAt (c.i - 1) hf
    rcases ht_live_swap (n := n.toPrev (c.i - 1))
      (n' := ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).toPrev (c.i - 1)) hf' hz with
      h1 | rfl
    · exact hn.2 cv z h1
    · exact hd cv
  · simp only [retargetKlongs] at hs
    obtain ⟨⟨k, i⟩, hki, he⟩ := List.mem_map.mp hs
    have hk : k ∈ n.ks := ht_mem_of_zipIdx hki
    cases k with
    | time u =>
      simp only at he
      cases he
      exact hn.3 s hk
    | del b => simp only at he; cases he
    | key a y =>
      simp only at he
      split at he <;> cases he

/-- A node of the right height with a key klong added at the transaction's time. -/
theorem nodeHt_addKey {c : Ctx} {w : W} {h : Nat} {n : KNode} (hpos : 0 < c.i)
    (hn : NodeHt c H w h n) {cv : Nat} {y : NodeId} (hy : HtP c H w h cv y) :
    NodeHt c H w h (n.add c.i (.key cv y)) :=
  nodeHt_addFold hpos hn [(cv, y)] (kdPairs_cons hy kdPairs_nil')

/-- The merge's parent node, with its three choices free. -/
theorem nodeHt_mpNode {c : Ctx} {w : W} {h : Nat} {pn : KNode} (hpos : 0 < c.i)
    (hN : NodeHt c H w h pn) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool)
    (htdh : htd = true → ∃ old, pn.ks.getLast? = some (.del old) ∧ pn.lastTime = some c.i)
    (hm1 : ∀ cv, HtP c H w h cv m1) (hm2 : ∀ y g, m2 = some (y, g) → ∀ cv, HtP c H w h cv y) :
    NodeHt c H w h (mpNode pn c.i il cL m1 ir cR m2 htd lip rip) := by
  have hn1 : ∀ (dR : Bool), NodeHt c H w h
      (if !dR then pn else if htd then pn.setAt (pn.size - 1)
        (.del (if dR then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap))
       else pn.add c.i (.del (if dR then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap))) := by
    intro dR
    cases dR with
    | false => exact hN
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases htd with
      | true =>
        obtain ⟨old, hl, ht⟩ := htdh rfl
        exact nodeHt_setAt_del hpos hN old hl ht cR
      | false => exact nodeHt_add_del hpos hN cR
  have hn2 : ∀ (dR : Bool), NodeHt c H w h
      (let n1 := if !dR then pn else if htd then pn.setAt (pn.size - 1)
        (.del (if dR then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap))
       else pn.add c.i (.del (if dR then bitsUnion pn.lastBitmap (pn.bitsOf cR) else pn.lastBitmap))
      if lip then n1.repoint il m1 else n1.add c.i (.key cL m1)) := by
    intro dR
    simp only
    cases lip with
    | true => exact nodeHt_repoint (hn1 dR) il m1 hm1
    | false => exact nodeHt_addKey hpos (hn1 dR) (hm1 cL)
  unfold mpNode
  cases m2 with
  | none => exact hn2 true
  | some q =>
    obtain ⟨y, g⟩ := q
    simp only
    have hy := hm2 y g rfl
    cases rip with
    | true => exact nodeHt_repoint (hn2 _) ir y hy
    | false => exact nodeHt_addKey hpos (hn2 _) (hy _)

end SIS.Tree
