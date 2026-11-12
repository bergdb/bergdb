import SIS.Tree.SearchReadProof
import SIS.Tree.MergeLiveKeys

namespace SIS.Tree

open SIS SIS.Check

def intervalBetter (rel : Nat → Nat → Bool) (allowed : Nat → Bool)
    (c : Nat) (best : Option Nat) : Bool :=
  bestOr best (fun b => rel b c) && allowed c

def FoundDominates (rel : Nat → Nat → Bool) (c : Nat) (r : Option Found) : Prop :=
  ∃ f, r = some f ∧ rel c f.c = true

theorem intervalStep_preserves (del : List Nat) (rel : Nat → Nat → Bool)
    (allowed : Nat → Bool)
    (htrans : ∀ a b c, rel a b = true → rel b c = true → rel a c = true)
    (c : Nat) (acc : Option Time × Option Found) (q : Klong × Nat)
    (h : FoundDominates rel c acc.2) :
    FoundDominates rel c (searchReadStep del (intervalBetter rel allowed) acc q).2 := by
  obtain ⟨f,hf,hcf⟩ := h
  rcases q with ⟨k,i⟩
  unfold searchReadStep
  split
  · exact ⟨f,hf,hcf⟩
  · cases k with
    | time x => exact ⟨f,hf,hcf⟩
    | del bits => exact ⟨f,hf,hcf⟩
    | key a y =>
      simp only [hf,Option.map_some,intervalBetter,bestOr]
      split
      · rename_i hbetter
        have hb : rel f.c a = true ∧ allowed a = true := by
          simpa only [Bool.and_eq_true] using hbetter
        exact ⟨_,rfl,htrans c f.c a hcf hb.1⟩
      · exact ⟨f,hf,hcf⟩

theorem intervalStep_hit (del : List Nat) (rel : Nat → Nat → Bool) (allowed : Nat → Bool)
    (hrefl : ∀ a, rel a a = true)
    (htrans : ∀ a b c, rel a b = true → rel b c = true → rel a c = true)
    (htotal : ∀ a b, rel a b = true ∨ rel b a = true)
    (c : Nat) (y : NodeId) (i : Nat) (acc : Option Time × Option Found)
    (hi : i ∉ del) (hc : allowed c = true) :
    FoundDominates rel c (searchReadStep del (intervalBetter rel allowed) acc (.key c y,i)).2 := by
  rcases acc with ⟨tt,best⟩
  cases best with
  | none =>
    simp only [searchReadStep,List.contains_eq_mem,hi,decide_false,Bool.false_eq_true,
      ↓reduceIte,Option.map_none,intervalBetter,bestOr,Bool.true_and,hc]
    exact ⟨_,rfl,hrefl c⟩
  | some f =>
    by_cases hcf : rel c f.c = true
    · exact intervalStep_preserves del rel allowed htrans c (tt,some f) (.key c y,i)
        ⟨f,rfl,hcf⟩
    · have hfc := (htotal c f.c).resolve_left hcf
      simp only [searchReadStep,List.contains_eq_mem,hi,decide_false,Bool.false_eq_true,
        ↓reduceIte,Option.map_some,intervalBetter,bestOr,hfc,hc,Bool.true_and]
      exact ⟨_,rfl,hrefl c⟩

theorem intervalFold_preserves (xs : List (Klong × Nat)) (del : List Nat)
    (rel : Nat → Nat → Bool) (allowed : Nat → Bool)
    (htrans : ∀ a b c, rel a b = true → rel b c = true → rel a c = true)
    (c : Nat) (acc : Option Time × Option Found) (h : FoundDominates rel c acc.2) :
    FoundDominates rel c (xs.foldl (searchReadStep del (intervalBetter rel allowed)) acc).2 := by
  induction xs generalizing acc with
  | nil => exact h
  | cons q qs ih => exact ih _ (intervalStep_preserves del rel allowed htrans c acc q h)

theorem intervalFold_hit (xs : List (Klong × Nat)) (del : List Nat)
    (rel : Nat → Nat → Bool) (allowed : Nat → Bool)
    (hrefl : ∀ a, rel a a = true)
    (htrans : ∀ a b c, rel a b = true → rel b c = true → rel a c = true)
    (htotal : ∀ a b, rel a b = true ∨ rel b a = true)
    (c : Nat) (y : NodeId) (i : Nat) (acc : Option Time × Option Found)
    (hi : i ∉ del) (hc : allowed c = true) (hm : (.key c y,i) ∈ xs) :
    FoundDominates rel c (xs.foldl (searchReadStep del (intervalBetter rel allowed)) acc).2 := by
  induction xs generalizing acc with
  | nil => simp at hm
  | cons q qs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact intervalFold_preserves qs del rel allowed htrans c _
        (intervalStep_hit del rel allowed hrefl htrans htotal c y i acc hi hc)
    · exact ih _ hm

theorem KNode.liveAt_eq_live_prefix (n : KNode) (t : Time) :
    n.liveAt t = (⟨n.leaf,prefixAt n.ks t⟩ : KNode).live := by
  simp [KNode.liveAt,KNode.live,KNode.lastVersion,KNode.lastVersionGivenDel,
    KNode.delAt,KNode.lastBitmap]
  rfl

theorem KNode.liveAt_has_key (n : KNode) (t : Time) (c : Nat) :
    c ∈ (n.liveAt t).map Prod.fst ↔
      ∃ y i, (.key c y,i) ∈ (prefixAt n.ks t).zipIdx ∧ i ∉ n.delAt t := by
  rw [n.liveAt_eq_live_prefix]
  exact KNode.live_has_key _ c

/-- A complete interval-search specification: the selected live pointer is
eligible and dominates every eligible live value; none means none is eligible. -/
def NodeSearchSpec (n : KNode) (t : Time) (r : Option Found)
    (allowed : Nat → Bool) (rel : Nat → Nat → Bool) : Prop :=
  (∀ f, r = some f → (f.c,f.y) ∈ n.liveAt t ∧ allowed f.c = true ∧
    ∀ q ∈ n.liveAt t, allowed q.1 = true → rel q.1 f.c = true) ∧
  (r = none ↔ ∀ q ∈ n.liveAt t, allowed q.1 = false)

theorem KNode.searchBy_spec (n : KNode) (t : Time)
    (rel : Nat → Nat → Bool) (allowed : Nat → Bool)
    (hrefl : ∀ a, rel a a = true)
    (htrans : ∀ a b c, rel a b = true → rel b c = true → rel a c = true)
    (htotal : ∀ a b, rel a b = true ∨ rel b a = true) :
    NodeSearchSpec n t (n.searchBy t (intervalBetter rel allowed)) allowed rel := by
  have htie : ∀ c best, intervalBetter rel allowed c best = true →
      intervalBetter rel allowed c (some c) = true := by
    intro c best hc
    simp only [intervalBetter,Bool.and_eq_true] at hc
    simpa [intervalBetter,bestOr,hrefl] using hc.2
  have hlookup : SearchLookupInv (intervalBetter rel allowed) (none,none) (fun _ => none) := by
    intro f hf
    cases hf
  have hinv := searchReadFold_lookup (prefixAt n.ks t).zipIdx (n.delAt t)
    (intervalBetter rel allowed) htie (none,none) (fun _ => none) hlookup
  have hhit : ∀ c, c ∈ (n.liveAt t).map Prod.fst → allowed c = true →
      FoundDominates rel c (n.searchBy t (intervalBetter rel allowed)) := by
    intro c hc ha
    obtain ⟨y,i,hkey,hdel⟩ := (n.liveAt_has_key t c).mp hc
    exact intervalFold_hit _ _ rel allowed hrefl htrans htotal c y i (none,none) hdel ha hkey
  have hsome : ∀ f, n.searchBy t (intervalBetter rel allowed) = some f →
      (f.c,f.y) ∈ n.liveAt t ∧ allowed f.c = true ∧
        ∀ q ∈ n.liveAt t, allowed q.1 = true → rel q.1 f.c = true := by
    intro f hf
    have hself := (hinv f hf).2
    have ha : allowed f.c = true := by
      simpa only [intervalBetter,bestOr,hrefl,Bool.true_and] using hself
    refine ⟨lookup_some_mem (n.searchBy_liveAt_lookup t _ htie f hf),ha,?_⟩
    intro q hq hqa
    obtain ⟨g,hg,hrel⟩ := hhit q.1 (List.mem_map.mpr ⟨q,hq,rfl⟩) hqa
    rw [hf] at hg
    have he : f = g := Option.some.inj hg
    simpa only [← he] using hrel
  refine ⟨hsome,?_⟩
  constructor
  · intro hn q hq
    cases ha : allowed q.1 with
    | false => rfl
    | true =>
      obtain ⟨g,hg,_⟩ := hhit q.1 (List.mem_map.mpr ⟨q,hq,rfl⟩) ha
      rw [hn] at hg
      cases hg
  · intro hall
    cases hr : n.searchBy t (intervalBetter rel allowed) with
    | none => rfl
    | some f =>
      obtain ⟨hf,ha,_⟩ := hsome f hr
      have hn := hall (f.c,f.y) hf
      rw [ha] at hn
      cases hn

theorem KNode.searchLte_spec (n : KNode) (t : Time) (target : Int) :
    NodeSearchSpec n t (n.searchLte t target) (fun c => decide ((c : Int) ≤ target))
      (fun a b => decide (a ≤ b)) := by
  apply n.searchBy_spec
  · intro a; simp
  · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega
  · intro a b; simp only [decide_eq_true_eq]; omega

theorem KNode.searchLt_spec (n : KNode) (t : Time) (target : Int) :
    NodeSearchSpec n t (n.searchLt t target) (fun c => decide ((c : Int) < target))
      (fun a b => decide (a ≤ b)) := by
  apply n.searchBy_spec
  · intro a; simp
  · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega
  · intro a b; simp only [decide_eq_true_eq]; omega

theorem KNode.searchGt_spec (n : KNode) (t : Time) (target : Int) :
    NodeSearchSpec n t (n.searchGt t target) (fun c => decide (target < (c : Int)))
      (fun a b => decide (b ≤ a)) := by
  apply n.searchBy_spec
  · intro a; simp
  · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega
  · intro a b; simp only [decide_eq_true_eq]; omega

theorem KNode.searchGte_spec (n : KNode) (t : Time) (target : Int) :
    NodeSearchSpec n t (n.searchGte t target) (fun c => decide (target ≤ (c : Int)))
      (fun a b => decide (b ≤ a)) := by
  apply n.searchBy_spec
  · intro a; simp
  · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega
  · intro a b; simp only [decide_eq_true_eq]; omega

end SIS.Tree
