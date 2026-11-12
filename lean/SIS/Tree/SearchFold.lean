import SIS.Tree.MergeLiveOrder

namespace SIS.Tree

open SIS SIS.Check

theorem lookup_setCv (m : List (Nat × NodeId)) (a c : Nat) (y : NodeId) :
    (setCv m a y).lookup c = if a = c then some y else m.lookup c := by
  have hm : (m.map (fun q => if q.1 == a then (a, y) else q)).lookup c =
      if a = c then (m.lookup c).map (fun _ => y) else m.lookup c := by
    simp only [List.lookup_eq_findSome?,List.findSome?_map]
    by_cases hac : a = c
    · subst c
      simp only [↓reduceIte,List.map_findSome?]
      congr 1
      funext q
      rcases q with ⟨b,z⟩
      by_cases hba : b = a
      · subst b; simp
      · simp [hba,Ne.symm hba]
    · simp only [hac,↓reduceIte]
      congr 1
      funext q
      rcases q with ⟨b,z⟩
      by_cases hba : b = a
      · subst b
        simp [Ne.symm hac]
      · simp [hba]
  unfold setCv
  split
  · rename_i ha
    rw [hm]
    split
    · rename_i hac
      subst c
      have hs : (m.lookup a).isSome := by
        simpa [List.lookup_isSome_iff, beq_iff_eq] using List.any_eq_true.mp ha
      cases he : m.lookup a <;> simp_all
    · rfl
  · rename_i ha
    have hn : m.lookup a = none := by
      apply List.lookup_eq_none_iff.mpr
      intro q hq
      have hneq : q.1 ≠ a := by
        intro he
        exact ha (List.any_eq_true.mpr ⟨q,hq,by simp [he]⟩)
      simp [Ne.symm hneq]
    rw [List.lookup_append]
    by_cases hac : a = c
    · subst c; simp [hn]
    · cases m.lookup c <;> simp [hac,Ne.symm hac]

theorem lookup_some_mem {m : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (h : m.lookup c = some y) : (c,y) ∈ m := by
  obtain ⟨pre,post,rfl,_⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem lookup_some_of_mem {m : List (Nat × NodeId)}
    (hn : (m.map Prod.fst).Nodup) {c : Nat} {y : NodeId}
    (hm : (c,y) ∈ m) : m.lookup c = some y := by
  induction m with
  | nil => simp at hm
  | cons q qs ih =>
    rcases q with ⟨a,z⟩
    simp only [List.map_cons,List.nodup_cons] at hn
    simp only [List.mem_cons,Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,rfl⟩ | hm
    · simp
    · have hca : c ≠ a := by
        intro hca
        apply hn.1
        exact List.mem_map.mpr ⟨(c,y),hm,hca⟩
      simpa [List.lookup_cons,show (c == a) = false from beq_eq_false_iff_ne.mpr hca]
        using ih hn.2 hm

theorem lookup_eq_of_perm {a b : List (Nat × NodeId)}
    (hp : a.Perm b) (ha : (a.map Prod.fst).Nodup) (c : Nat) :
    a.lookup c = b.lookup c := by
  have hb := (hp.map Prod.fst).nodup_iff.mp ha
  cases he : a.lookup c with
  | none =>
    have hn := List.lookup_eq_none_iff.mp he
    exact (List.lookup_eq_none_iff.mpr (fun q hq => hn q (hp.mem_iff.mpr hq))).symm
  | some y =>
    exact (lookup_some_of_mem hb (hp.mem_iff.mp (lookup_some_mem he))).symm

/-- A lookup obtained by keeping only physical key klongs outside a supplied
bitmap, with the last matching klong winning. -/
def keyLookupStep (del : List Nat) (c : Nat) (v : Option NodeId)
    (q : Klong × Nat) : Option NodeId :=
  match q.1 with
  | .key a y => if del.contains q.2 then v else if a == c then some y else v
  | _ => v

def keyLookup (ks : List Klong) (del : List Nat) (c : Nat) : Option NodeId :=
  ks.zipIdx.foldl (keyLookupStep del c) none

theorem lookup_liveFold (xs : List (Klong × Nat)) (del : List Nat)
    (c : Nat) (m : List (Nat × NodeId)) :
    (xs.foldl (fun more (k,i) => match k with
      | .key a y => if del.contains i then more else setCv more a y
      | _ => more) m).lookup c = xs.foldl (keyLookupStep del c) (m.lookup c) := by
  induction xs generalizing m with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨k,i⟩
    cases k with
    | time t => exact ih m
    | del bits => exact ih m
    | key a y =>
      simp only [List.foldl_cons]
      by_cases hd : i ∈ del
      · simpa only [keyLookupStep,List.contains_eq_mem,hd,decide_true,↓reduceIte] using ih m
      · simpa only [keyLookupStep,List.contains_eq_mem,hd,decide_false,Bool.false_eq_true,↓reduceIte,
          lookup_setCv,beq_iff_eq] using
          ih (setCv m a y)

/-- Normalizing and sorting the live pairs does not alter a lookup. This
part of TP9 needs no well-formedness assumption. -/
theorem KNode.liveAt_lookup (n : KNode) (t : Time) (c : Nat) :
    (n.liveAt t).lookup c = keyLookup (prefixAt n.ks t) (n.delAt t) c := by
  let xs := (prefixAt n.ks t).zipIdx
  let m := xs.foldl (fun more (k,i) => match k with
    | .key a y => if (n.delAt t).contains i then more else setCv more a y
    | _ => more) []
  have hn : (m.map Prod.fst).Nodup := liveFold_keys_nodup xs (n.delAt t) [] (by simp)
  have he : n.liveAt t = m.mergeSort (fun a b => decide (a.1 ≤ b.1)) := by
    simp [KNode.liveAt,KNode.lastVersionGivenDel,m,xs,List.filterMap_map,Function.comp_def]
    rfl
  rw [he,lookup_eq_of_perm (List.mergeSort_perm m _) (sortedPairs_keys_nodup m hn)]
  exact lookup_liveFold xs (n.delAt t) c []

end SIS.Tree
