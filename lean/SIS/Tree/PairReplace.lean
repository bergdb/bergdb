import SIS.Tree.NodeMap
import SIS.Tree.WriterWP

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The first matching entry, with the physical order retained. -/
def replacePairFirst (pairs : List (Nat × NodeId)) (cv : Nat) (y : NodeId) :
    Option (List (Nat × NodeId)) :=
  match pairs with
  | [] => none
  | q :: rest =>
    if q.1 == cv then some ((cv, y) :: rest)
    else (replacePairFirst rest cv y).map (q :: ·)

theorem replacePairFirst_none (pairs : List (Nat × NodeId)) (cv : Nat) (y : NodeId)
    (hn : replacePairFirst pairs cv y = none) : pairs.lookup cv = none := by
  induction pairs with
  | nil => rfl
  | cons q pairs ih =>
    rcases q with ⟨a,z⟩
    by_cases ha : a = cv
    · simp [replacePairFirst, ha] at hn
    · have hne : cv ≠ a := Ne.symm ha
      have ht : replacePairFirst pairs cv y = none := by
        simp only [replacePairFirst, show (a == cv) = false from beq_eq_false_iff_ne.mpr ha,
          Bool.false_eq_true, ↓reduceIte] at hn
        cases hh : replacePairFirst pairs cv y <;> simp_all
      simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hne] using ih ht

theorem replacePairFirst_some (pairs out : List (Nat × NodeId)) (cv : Nat) (y : NodeId)
    (hr : replacePairFirst pairs cv y = some out) :
    out.map Prod.fst = pairs.map Prod.fst ∧
      ∀ c, out.lookup c = if cv == c then some y else pairs.lookup c := by
  induction pairs generalizing out with
  | nil => simp [replacePairFirst] at hr
  | cons q pairs ih =>
    rcases q with ⟨a,z⟩
    by_cases ha : a = cv
    · have he : (cv,y) :: pairs = out := by simpa [replacePairFirst, ha] using hr
      subst out
      subst a
      refine ⟨rfl, ?_⟩
      intro c
      by_cases hc : c = cv
      · subst c; simp
      · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hc,
          beq_eq_false_iff_ne.mpr (Ne.symm hc), Bool.false_eq_true, ↓reduceIte]
    · simp only [replacePairFirst, show (a == cv) = false from beq_eq_false_iff_ne.mpr ha,
        Bool.false_eq_true, ↓reduceIte] at hr
      cases hh : replacePairFirst pairs cv y with
      | none => simp [hh] at hr
      | some rest =>
        have he : (a,z) :: rest = out := by simpa [hh] using hr
        subst out
        obtain ⟨hkeys, hlookup⟩ := ih rest hh
        refine ⟨by simp [hkeys], ?_⟩
        intro c
        by_cases hc : c = a
        · subst c
          simp only [List.lookup_cons, beq_self_eq_true,
            beq_eq_false_iff_ne.mpr (Ne.symm ha), Bool.false_eq_true, ↓reduceIte]
        · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr hc]
          exact hlookup c

theorem replaceKlong_go_key_pairs (pre : List Klong) (pairs : List (Nat × NodeId))
    (t cv : Nat) (y : NodeId) :
    replaceKlong.go t cv y pre (pairs.map (fun q => .key q.1 q.2)) (some t) =
      .ok ((replacePairFirst pairs cv y).map (fun out => pre ++ out.map (fun q => .key q.1 q.2))) := by
  induction pairs generalizing pre with
  | nil => rfl
  | cons q pairs ih =>
    rcases q with ⟨a,z⟩
    simp only [List.map_cons, replaceKlong.go, beq_self_eq_true, Bool.and_true, replacePairFirst]
    by_cases ha : a = cv
    · subst a; simp
    · simp only [beq_eq_false_iff_ne.mpr ha, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      cases hr : replacePairFirst pairs cv y <;>
        simp [hr, List.append_assoc]

theorem replaceKlong_newKlongs (t cv : Nat) (y : NodeId) (pairs : List (Nat × NodeId)) :
    replaceKlong (newKlongs t pairs) t cv y =
      .ok ((replacePairFirst pairs cv y).map (newKlongs t)) := by
  unfold replaceKlong
  simp only [newKlongs, replaceKlong.go, List.nil_append]
  rw [replaceKlong_go_key_pairs]
  cases hr : replacePairFirst pairs cv y <;> rfl

theorem pair_not_mem_of_lookup_none (pairs : List (Nat × NodeId)) (cv : Nat)
    (hn : pairs.lookup cv = none) : cv ∉ pairs.map Prod.fst := by
  intro hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have hh := List.lookup_eq_none_iff.mp hn q hq
  simp only [bne_iff_ne] at hh
  exact hh he.symm

theorem pair_append_new_nodup (pairs : List (Nat × NodeId)) (cv : Nat) (y : NodeId)
    (hn : (pairs.map Prod.fst).Nodup) (hc : pairs.lookup cv = none) :
    ((pairs ++ [(cv,y)]).map Prod.fst).Nodup := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb he
  have hb' : b = cv := List.mem_singleton.mp hb
  subst b
  subst a
  exact pair_not_mem_of_lookup_none pairs cv hc ha

theorem pair_append_new_lookup (pairs : List (Nat × NodeId)) (cv c : Nat) (y : NodeId)
    (hc : pairs.lookup cv = none) :
    (pairs ++ [(cv,y)]).lookup c = if cv == c then some y else pairs.lookup c := by
  rw [List.lookup_append]
  by_cases he : c = cv
  · subst c; simp [hc]
  · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr he,
      beq_eq_false_iff_ne.mpr (Ne.symm he)]

theorem KNode.newKlongs_live_lookup (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) (c : Nat) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).live.lookup c = pairs.lookup c := by
  rw [KNode.live_lookup]
  change keyLookup (newKlongs t pairs) (lastBitmapOf (newKlongs t pairs)) c = _
  rw [lastBitmapOf_newKlongs, keyLookup_newKlongs t pairs c hn]

theorem KNode.newKlongs_lastTime (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId)) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).lastTime = some t := by
  have hf : ∀ (qs : List (Nat × NodeId)) (acc : Option Time),
      ((qs.map (fun q => Klong.key q.1 q.2)).foldl
        (fun cur k => match k with | .time u => some u | _ => cur) acc) = acc := by
    intro qs
    induction qs with
    | nil => intro acc; rfl
    | cons q qs ih => intro acc; exact ih acc
  simp only [KNode.lastTime, newKlongs, List.foldl_cons]
  exact hf pairs (some t)

theorem KNode.newKlongs_add_key (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (cv : Nat) (y : NodeId) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).add t (.key cv y) =
      ⟨leaf, newKlongs t (pairs ++ [(cv,y)])⟩ := by
  unfold KNode.add
  rw [KNode.newKlongs_lastTime]
  simp [newKlongs, List.map_append]

end SIS.Tree
