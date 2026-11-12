import SIS.Tree.MergeLiveOrder
import SIS.Tree.SortedSegments
import SIS.Tree.MergeRootWrites

namespace SIS.Tree

open SIS SIS.Check

private def lteSearchStep (del : List Nat) (target : Int)
    (acc : Option Time × Option Found) (q : Klong × Nat) : Option Time × Option Found :=
  if del.contains q.2 then acc else
    match q.1 with
    | .time x => (some x,acc.2)
    | .key c y =>
      if bestOr (acc.2.map (·.c)) (fun b => decide (b ≤ c)) && decide ((c : Int) ≤ target) then
        (acc.1,some ⟨c,q.2,acc.1.getD 0,y⟩)
      else acc
    | .del _ => acc

private def FoundLower (c : Nat) (r : Option Found) : Prop :=
  ∃ f, r = some f ∧ c ≤ f.c

private theorem lteSearchStep_preserves (del : List Nat) (target : Int) (c : Nat)
    (acc : Option Time × Option Found) (q : Klong × Nat) (h : FoundLower c acc.2) :
    FoundLower c (lteSearchStep del target acc q).2 := by
  obtain ⟨f,hf,hc⟩ := h
  rcases q with ⟨k,i⟩
  unfold lteSearchStep
  split
  · exact ⟨f,hf,hc⟩
  · cases k with
    | time x => exact ⟨f,hf,hc⟩
    | del bits => exact ⟨f,hf,hc⟩
    | key a y =>
      simp only [hf,Option.map_some,bestOr]
      split
      · rename_i hbetter
        have hboth : f.c ≤ a ∧ (a : Int) ≤ target := by
          simpa only [Bool.and_eq_true,decide_eq_true_eq] using hbetter
        have hab : f.c ≤ a := hboth.1
        exact ⟨_,rfl,Nat.le_trans hc hab⟩
      · exact ⟨f,hf,hc⟩

private theorem lteSearchStep_hit (del : List Nat) (target : Int) (c : Nat) (y : NodeId)
    (i : Nat) (acc : Option Time × Option Found) (hi : i ∉ del) (hc : (c : Int) ≤ target) :
    FoundLower c (lteSearchStep del target acc (.key c y,i)).2 := by
  rcases acc with ⟨tt,best⟩
  cases best with
  | none =>
    simp only [lteSearchStep,List.contains_eq_mem,hi,decide_false,Bool.false_eq_true,
      ↓reduceIte,Option.map_none,bestOr,Bool.true_and,hc,decide_true]
    exact ⟨_,rfl,Nat.le_refl _⟩
  | some f =>
    by_cases hb : c ≤ f.c
    · exact lteSearchStep_preserves del target c (tt,some f) (.key c y,i) ⟨f,rfl,hb⟩
    · have hfc : f.c ≤ c := by omega
      simp only [lteSearchStep,List.contains_eq_mem,hi,decide_false,Bool.false_eq_true,
        ↓reduceIte,Option.map_some,bestOr,hfc,hc,decide_true,Bool.true_and]
      exact ⟨_,rfl,Nat.le_refl _⟩

private theorem lteSearchFold_preserves (del : List Nat) (target : Int) (c : Nat)
    (ks : List (Klong × Nat)) (acc : Option Time × Option Found) (h : FoundLower c acc.2) :
    FoundLower c (ks.foldl (lteSearchStep del target) acc).2 := by
  induction ks generalizing acc with
  | nil => exact h
  | cons q ks ih =>
    exact ih _ (lteSearchStep_preserves del target c acc q h)

private theorem lteSearchFold_hit (del : List Nat) (target : Int) (c : Nat) (y : NodeId)
    (i : Nat) (ks : List (Klong × Nat)) (acc : Option Time × Option Found)
    (hi : i ∉ del) (hc : (c : Int) ≤ target) (hm : (.key c y,i) ∈ ks) :
    FoundLower c (ks.foldl (lteSearchStep del target) acc).2 := by
  induction ks generalizing acc with
  | nil => simp at hm
  | cons q ks ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact lteSearchFold_preserves del target c ks _ (lteSearchStep_hit del target c y i acc hi hc)
    · exact ih _ hm

/-- A live separator at or below the target gives a successful search whose
compare value is at least that separator. -/
theorem KNode.searchLte_lower_bound (n : KNode) (t : Time) (target : Int)
    (c : Nat) (y : NodeId) (i : Nat)
    (hm : (.key c y,i) ∈ (prefixAt n.ks t).zipIdx)
    (hi : i ∉ lastBitmapOf (prefixAt n.ks t)) (hc : (c : Int) ≤ target) :
    ∃ f, n.searchLte t target = some f ∧ c ≤ f.c := by
  exact lteSearchFold_hit (lastBitmapOf (prefixAt n.ks t)) target c y i
    (prefixAt n.ks t).zipIdx (none,none) hi hc hm


private def FoundUpper (target : Int) (r : Option Found) : Prop :=
  ∀ f, r = some f → (f.c : Int) ≤ target

private theorem lteSearchStep_upper (del : List Nat) (target : Int)
    (acc : Option Time × Option Found) (q : Klong × Nat) (h : FoundUpper target acc.2) :
    FoundUpper target (lteSearchStep del target acc q).2 := by
  rcases q with ⟨k,i⟩
  unfold lteSearchStep
  split
  · exact h
  · cases k with
    | time x => exact h
    | del bits => exact h
    | key c y =>
      dsimp only
      split
      · rename_i hb
        have hc : (c : Int) ≤ target := by
          have hh : bestOr (acc.2.map (·.c)) (fun b => decide (b ≤ c)) = true ∧ (c : Int) ≤ target := by
            simpa only [Bool.and_eq_true,decide_eq_true_eq] using hb
          exact hh.2
        intro f hf
        cases hf
        exact hc
      · exact h

private theorem lteSearchFold_upper (del : List Nat) (target : Int)
    (ks : List (Klong × Nat)) (acc : Option Time × Option Found) (h : FoundUpper target acc.2) :
    FoundUpper target (ks.foldl (lteSearchStep del target) acc).2 := by
  induction ks generalizing acc with
  | nil => exact h
  | cons q ks ih => exact ih _ (lteSearchStep_upper del target acc q h)

/-- Every result of searchLte is at or below its integer target. -/
theorem KNode.searchLte_upper_bound (n : KNode) (t : Time) (target : Int) (f : Found)
    (hf : n.searchLte t target = some f) : (f.c : Int) ≤ target := by
  have hi : FoundUpper target (none : Option Found) := by intro a ha; cases ha
  exact lteSearchFold_upper (lastBitmapOf (prefixAt n.ks t)) target
    (prefixAt n.ks t).zipIdx (none,none) hi f hf

private theorem lteSearchFold_origin (del : List Nat) (target : Int)
    (sources ks : List (Klong × Nat)) (acc : Option Time × Option Found)
    (hks : ∀ q ∈ ks, q ∈ sources)
    (hacc : ∀ f, acc.2 = some f →
      (.key f.c f.y,f.idx) ∈ sources ∧ f.idx ∉ del) :
    ∀ f, (ks.foldl (lteSearchStep del target) acc).2 = some f →
      (.key f.c f.y,f.idx) ∈ sources ∧ f.idx ∉ del := by
  induction ks generalizing acc with
  | nil => exact hacc
  | cons q ks ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro a ha
      exact hks a (List.mem_cons_of_mem _ ha)
    · rcases q with ⟨k,i⟩
      unfold lteSearchStep
      split
      · exact hacc
      · rename_i hi
        have hi' : i ∉ del := by simpa only [List.contains_eq_mem,decide_eq_true_eq] using hi
        cases k with
        | time x => exact hacc
        | del bits => exact hacc
        | key a y =>
          dsimp only
          split
          · intro f hf
            cases hf
            exact ⟨hks _ List.mem_cons_self,hi'⟩
          · exact hacc

/-- A successful search names a physical key klong that the bitmap at the
search time does not delete. -/
theorem KNode.searchLte_origin (n : KNode) (t : Time) (target : Int) (f : Found)
    (hf : n.searchLte t target = some f) :
    (.key f.c f.y,f.idx) ∈ (prefixAt n.ks t).zipIdx ∧
      f.idx ∉ lastBitmapOf (prefixAt n.ks t) := by
  exact lteSearchFold_origin (lastBitmapOf (prefixAt n.ks t)) target
    (prefixAt n.ks t).zipIdx (prefixAt n.ks t).zipIdx (none,none)
    (by intro q hq; exact hq) (by intro a ha; cases ha) f hf

/-- On a fixed node, increasing the target cannot move the search to a
smaller compare value. No invariant of the physical history is needed. -/
theorem KNode.searchLte_monotone (n : KNode) (t : Time) (a b : Int)
    (hab : a ≤ b) (f : Found) (hf : n.searchLte t a = some f) :
    ∃ g, n.searchLte t b = some g ∧ f.c ≤ g.c := by
  obtain ⟨hm,hi⟩ := n.searchLte_origin t a f hf
  have hc := n.searchLte_upper_bound t a f hf
  exact n.searchLte_lower_bound t b f.c f.y f.idx hm hi (by omega)

/-- A live divider forces the search into its compare-value interval. -/
theorem KNode.searchLte_separator (n : KNode) (t : Time) (target : Int)
    (c : Nat) (y : NodeId) (i : Nat)
    (hm : (.key c y,i) ∈ (prefixAt n.ks t).zipIdx)
    (hi : i ∉ lastBitmapOf (prefixAt n.ks t)) (hc : (c : Int) ≤ target) :
    ∃ f, n.searchLte t target = some f ∧ c ≤ f.c ∧ (f.c : Int) ≤ target := by
  obtain ⟨f,hf,hlo⟩ := n.searchLte_lower_bound t target c y i hm hi hc
  exact ⟨f,hf,hlo,n.searchLte_upper_bound t target f hf⟩


/-- Once the current key is at or beyond a live separator, strict full-key
order keeps later keys of this segment-prefix group at or beyond it. -/
theorem KNode.searchLte_later_key_separator (n : KNode) (t : Time) (g : Nat)
    (a b : Key) (ca cb sc : Nat) (y : NodeId) (i : Nat)
    (hs : keyLt a b = true) (hp : a.take g = b.take g)
    (ha : a[g]? = some ca) (hb : b[g]? = some cb) (hc : sc ≤ ca)
    (hm : (.key sc y,i) ∈ (prefixAt n.ks t).zipIdx)
    (hi : i ∉ lastBitmapOf (prefixAt n.ks t)) :
    ∃ f, n.searchLte t cb = some f ∧ sc ≤ f.c ∧ f.c ≤ cb := by
  have hab := keyLt_segment_mono g a b ca cb hs hp ha hb
  obtain ⟨f,hf,hlo,hup⟩ := n.searchLte_separator t cb sc y i hm hi (by omega)
  exact ⟨f,hf,hlo,by omega⟩

/-- At or above the divider, the root just made by a space split selects its
right child. -/
theorem newRoot_searchLte_right (t : Time) (x y : NodeId) (sc cv : Nat) (hc : sc ≤ cv) :
    (⟨false,[.time t,.key 0 x,.key sc y]⟩ : KNode).searchLte t cv =
      some ⟨sc,2,t,y⟩ := by
  simp [KNode.searchLte,KNode.searchBy,prefixAt,lastBitmapOf,bestOr,hc]

/-- The right half remains the choice for every later key in the same
segment-prefix group while this newly made root keeps its two klongs. -/
theorem newRoot_searchLte_later_key (t : Time) (x y : NodeId) (g : Nat)
    (a b : Key) (ca cb sc : Nat)
    (hs : keyLt a b = true) (hp : a.take g = b.take g)
    (ha : a[g]? = some ca) (hb : b[g]? = some cb) (hc : sc ≤ ca) :
    (⟨false,[.time t,.key 0 x,.key sc y]⟩ : KNode).searchLte t cb =
      some ⟨sc,2,t,y⟩ := by
  exact newRoot_searchLte_right t x y sc cb (Nat.le_trans hc (keyLt_segment_mono g a b ca cb hs hp ha hb))

/-- The actual descent from a cached split root follows its right child at
or beyond the divider; it does not load or visit the left child. -/
theorem writerWP_descendLte_newRoot_right (cv fuel : Nat) (root x y : NodeId)
    (sc : Nat) (c : Ctx) (w : W) (post : NodeId → W → Prop)
    (hn : w.nodes.lookup root = some ⟨false,[.time c.i,.key 0 x,.key sc y]⟩)
    (hc : sc ≤ cv) :
    WriterWP (descendLte cv (fuel+1) root) c w post ↔
      WriterWP (do pathAdd (some sc) y; descendLte cv fuel y) c w post := by
  rw [descendLte]
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known root _ c w hn]
  simp only [Bool.false_eq_true,↓reduceIte,newRoot_searchLte_right c.i x y sc cv hc,
    writerWP_bind]

/-- Strict full-key order supplies the comparison needed by the writer's
descent when both operations belong to the same segment-prefix group. -/
theorem writerWP_descendLte_newRoot_later_key (fuel : Nat) (root x y : NodeId)
    (g : Nat) (a b : Key) (ca cb sc : Nat) (c : Ctx) (w : W)
    (post : NodeId → W → Prop)
    (hn : w.nodes.lookup root = some ⟨false,[.time c.i,.key 0 x,.key sc y]⟩)
    (hs : keyLt a b = true) (hp : a.take g = b.take g)
    (ha : a[g]? = some ca) (hb : b[g]? = some cb) (hc : sc ≤ ca) :
    WriterWP (descendLte cb (fuel+1) root) c w post ↔
      WriterWP (do pathAdd (some sc) y; descendLte cb fuel y) c w post := by
  exact writerWP_descendLte_newRoot_right cb fuel root x y sc c w post hn
    (Nat.le_trans hc (keyLt_segment_mono g a b ca cb hs hp ha hb))

end SIS.Tree
