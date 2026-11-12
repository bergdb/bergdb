import SIS.Tree.SearchEqProof

namespace SIS.Tree

open SIS SIS.Check

def searchReadStep (del : List Nat) (better : Nat → Option Nat → Bool)
    (acc : Option Time × Option Found) (q : Klong × Nat) : Option Time × Option Found :=
  if del.contains q.2 then acc else
    match q.1 with
    | .time x => (some x,acc.2)
    | .key c y =>
      if better c (acc.2.map (·.c)) then (acc.1,some ⟨c,q.2,acc.1.getD 0,y⟩) else acc
    | .del _ => acc

def lookupFunctionStep (del : List Nat) (kv : Nat → Option NodeId) (q : Klong × Nat) :
    Nat → Option NodeId := fun c => keyLookupStep del c (kv c) q

def SearchLookupInv (better : Nat → Option Nat → Bool)
    (acc : Option Time × Option Found) (kv : Nat → Option NodeId) : Prop :=
  ∀ f, acc.2 = some f → kv f.c = some f.y ∧ better f.c (some f.c) = true

theorem searchReadStep_lookup (del : List Nat) (better : Nat → Option Nat → Bool)
    (htie : ∀ c best, better c best = true → better c (some c) = true)
    (acc : Option Time × Option Found) (kv : Nat → Option NodeId)
    (hi : SearchLookupInv better acc kv) (q : Klong × Nat) :
    SearchLookupInv better (searchReadStep del better acc q) (lookupFunctionStep del kv q) := by
  rcases q with ⟨k,i⟩
  by_cases hd : i ∈ del
  · cases k <;> simpa [SearchLookupInv,searchReadStep,lookupFunctionStep,keyLookupStep,hd] using hi
  · cases k with
    | time t => simpa [SearchLookupInv,searchReadStep,lookupFunctionStep,keyLookupStep,hd] using hi
    | del bits => simpa [SearchLookupInv,searchReadStep,lookupFunctionStep,keyLookupStep,hd] using hi
    | key a y =>
      by_cases ha : better a (acc.2.map (·.c)) = true
      · intro f hf
        have hf' : (⟨a,i,acc.1.getD 0,y⟩ : Found) = f := by
          simpa [searchReadStep,hd,ha] using hf
        subst f
        exact ⟨by simp [lookupFunctionStep,keyLookupStep,hd],htie a _ ha⟩
      · intro f hf
        have hf' : acc.2 = some f := by simpa [searchReadStep,hd,ha] using hf
        obtain ⟨hkv,hself⟩ := hi f hf'
        have hne : a ≠ f.c := by
          intro he
          subst a
          simp only [hf',Option.map_some] at ha
          exact ha hself
        exact ⟨by simpa [lookupFunctionStep,keyLookupStep,hd,hne] using hkv,hself⟩

theorem searchReadFold_lookup (xs : List (Klong × Nat)) (del : List Nat)
    (better : Nat → Option Nat → Bool)
    (htie : ∀ c best, better c best = true → better c (some c) = true)
    (acc : Option Time × Option Found) (kv : Nat → Option NodeId)
    (hi : SearchLookupInv better acc kv) :
    SearchLookupInv better (xs.foldl (searchReadStep del better) acc)
      (xs.foldl (lookupFunctionStep del) kv) := by
  induction xs generalizing acc kv with
  | nil => exact hi
  | cons q qs ih => exact ih _ _ (searchReadStep_lookup del better htie acc kv hi q)

theorem lookupFunctionFold_apply (xs : List (Klong × Nat)) (del : List Nat)
    (kv : Nat → Option NodeId) (c : Nat) :
    (xs.foldl (lookupFunctionStep del) kv) c = xs.foldl (keyLookupStep del c) (kv c) := by
  exact (List.foldl_hom (fun kv : Nat → Option NodeId => kv c)
    (g₁ := lookupFunctionStep del) (g₂ := keyLookupStep del c)
    (l := xs) (init := kv) (by intro kv q; rfl)).symm

/-- A read search that replaces equal compare values returns the pointer of
that value in liveAt. The four interval searches satisfy the tie premise;
searchFirst deliberately does not. No klong well-formedness is needed. -/
theorem KNode.searchBy_liveAt_lookup (n : KNode) (t : Time)
    (better : Nat → Option Nat → Bool)
    (htie : ∀ c best, better c best = true → better c (some c) = true)
    (f : Found) (hf : n.searchBy t better = some f) :
    (n.liveAt t).lookup f.c = some f.y := by
  have hi : SearchLookupInv better (none,none) (fun _ => none) := by
    intro f hf
    cases hf
  have hh := searchReadFold_lookup (prefixAt n.ks t).zipIdx (n.delAt t)
    better htie (none,none) (fun _ => none) hi
  have hs : ((prefixAt n.ks t).zipIdx.foldl (searchReadStep (n.delAt t) better) (none,none)).2 =
      some f := hf
  have hk := (hh f hs).1
  rw [lookupFunctionFold_apply] at hk
  rw [n.liveAt_lookup]
  exact hk

theorem KNode.searchLte_liveAt_lookup (n : KNode) (t : Time) (target : Int)
    (f : Found) (hf : n.searchLte t target = some f) :
    (n.liveAt t).lookup f.c = some f.y := by
  apply n.searchBy_liveAt_lookup t _ _ f hf
  intro c best ha
  simp only [Bool.and_eq_true] at ha
  simpa [bestOr] using ha.2

theorem KNode.searchLt_liveAt_lookup (n : KNode) (t : Time) (target : Int)
    (f : Found) (hf : n.searchLt t target = some f) :
    (n.liveAt t).lookup f.c = some f.y := by
  apply n.searchBy_liveAt_lookup t _ _ f hf
  intro c best ha
  simp only [Bool.and_eq_true] at ha
  simpa [bestOr] using ha.2

theorem KNode.searchGt_liveAt_lookup (n : KNode) (t : Time) (target : Int)
    (f : Found) (hf : n.searchGt t target = some f) :
    (n.liveAt t).lookup f.c = some f.y := by
  apply n.searchBy_liveAt_lookup t _ _ f hf
  intro c best ha
  simp only [Bool.and_eq_true] at ha
  simpa [bestOr] using ha.2

theorem KNode.searchGte_liveAt_lookup (n : KNode) (t : Time) (target : Int)
    (f : Found) (hf : n.searchGte t target = some f) :
    (n.liveAt t).lookup f.c = some f.y := by
  apply n.searchBy_liveAt_lookup t _ _ f hf
  intro c best ha
  simp only [Bool.and_eq_true] at ha
  simpa [bestOr] using ha.2

end SIS.Tree
