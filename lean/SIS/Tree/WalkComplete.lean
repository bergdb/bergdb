import SIS.Tree.NodeKinds
import SIS.Tree.InvConsequences
import SIS.Tree.IntervalSearchProof

namespace SIS.Tree

open SIS SIS.Check

theorem keyLookupStep_source (del : List Nat) (c : Nat) (v : Option NodeId)
    (q : Klong × Nat) (y : NodeId) (he : keyLookupStep del c v q = some y) :
    v = some y ∨ q.1 = .key c y := by
  rcases q with ⟨k,j⟩
  cases k with
  | time t => exact Or.inl he
  | del bits => exact Or.inl he
  | key a z =>
    simp only [keyLookupStep] at he
    split at he
    · exact Or.inl he
    · split at he
      · rename_i hac
        have hac' : a = c := by simpa using hac
        have hzy : z = y := Option.some.inj he
        exact Or.inr (by simp [hac',hzy])
      · exact Or.inl he

theorem keyLookupFold_source (xs : List (Klong × Nat)) (del : List Nat)
    (c : Nat) (v : Option NodeId) (y : NodeId)
    (he : xs.foldl (keyLookupStep del c) v = some y) :
    v = some y ∨ ∃ j, (.key c y,j) ∈ xs := by
  induction xs generalizing v with
  | nil => exact Or.inl he
  | cons q qs ih =>
    rcases ih _ he with hh | ⟨j,hj⟩
    · rcases keyLookupStep_source del c v q y hh with hv | hq
      · exact Or.inl hv
      · exact Or.inr ⟨q.2,by rw [← hq]; exact List.mem_cons_self⟩
    · exact Or.inr ⟨j,List.mem_cons_of_mem _ hj⟩

/-- A live pointer comes from a physical key klong of the same node. -/
theorem KNode.liveAt_key_mem (n : KNode) (t : Time) (c : Nat) (y : NodeId)
    (hm : (c,y) ∈ n.liveAt t) : Klong.key c y ∈ n.ks := by
  have hn : ((n.liveAt t).map Prod.fst).Nodup := by
    rw [n.liveAt_eq_live_prefix]
    exact KNode.live_keys_nodup _
  have hl := lookup_some_of_mem hn hm
  rw [n.liveAt_lookup] at hl
  rcases keyLookupFold_source _ _ _ _ _ hl with hh | ⟨j,hj⟩
  · cases hh
  · have hp : Klong.key c y ∈ prefixAt n.ks t :=
      List.fst_mem_of_mem_zipIdx hj
    exact (List.takeWhile_sublist _).subset hp

theorem walk_current_pointer (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = [])
    (c : Nat) (y : NodeId) (hk : Klong.key c y ∈ klongsOf nd.hist) : (v y).isSome = true := by
  cases hy : v y with
  | some ny => rfl
  | none =>
    have hm : s!"PointersOK: key node {x} names {y}, no node of P" ∈
        walk p v t (f+1) x lo hi isRoot space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp only [List.mem_append]
      left; left; left; left; left; left; left; right
      exact List.mem_filterMap.mpr ⟨.key c y,hk,by simp [hy]⟩
    simp [hw] at hm

end SIS.Tree
