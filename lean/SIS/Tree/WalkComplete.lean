import SIS.Tree.NodeKinds
import SIS.Tree.NodeCountTree
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

/-- A fault-free walk is complete once high nodes are distinguished from
key nodes by their histories. -/
theorem walk_complete_of_highKindsOK (p : Params) (P : Struct BVal) (t f : Nat)
    (hP : HighKindsOK p P) (x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) :
    KeyWalkComplete p (viewOf P) t f x := by
  induction f generalizing x lo hi isRoot space with
  | zero => simp only [walk,List.cons_ne_nil] at hw
  | succ f ih =>
    cases hv : P.get? x with
    | none => simp only [walk,viewOf,hv,List.cons_ne_nil] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp only [walk,viewOf,hv,hd,↓reduceIte,List.cons_ne_nil] at hw
      | false =>
        have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hP hv hd hw
        let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
        have hn : knodeOf p (viewOf P) x = some n := by
          simp [knodeOf,viewOf,hv,hd,Nat.not_lt_of_ge hl,n]
        refine ⟨n,hn,?_⟩
        intro ⟨c,y⟩ hcy hterminal
        have hp := walk_current_pointer p (viewOf P) t f x lo hi isRoot space nd hv hd hw
          c y (n.liveAt_key_mem t c y hcy)
        cases hvy : P.get? y with
        | none => simp [viewOf,hvy] at hp
        | some ny =>
          have hlen : (n.liveAt t).length ≤
              (((n.liveAt t).drop 1).map (fun q => some q.1) ++ [hi]).length := by
            simp only [List.length_append,List.length_map,List.length_drop,List.length_singleton]
            omega
          obtain ⟨hi',hzip⟩ := mem_zip_left_witness _ _ hlen (c,y) hcy
          have hchild := List.flatMap_eq_nil_iff.mp
            (walk_child_faults_nil p (viewOf P) t f x lo hi isRoot space nd hv hd hw)
            ((c,y),hi') hzip
          change walkChildFaults p (viewOf P) t f x n (p.segOf nd.level)
            (p.heightOf nd.level) lo space ((c,y),hi') = [] at hchild
          cases hleaf : n.leaf with
          | true =>
            have hc : segLen c = 7 := by simpa [hleaf] using hterminal
            simp only [walkChildFaults,hleaf,hc,beq_self_eq_true,↓reduceIte,viewOf,hvy] at hchild
            split at hchild
            · cases hchild
            · split at hchild
              · cases hchild
              · exact ih y 0 none true false hchild
          | false =>
            simp only [walkChildFaults,hleaf,Bool.false_eq_true,↓reduceIte,viewOf,hvy] at hchild
            split at hchild
            · cases hchild
            · split at hchild
              · cases hchild
              · exact ih y (if c == 0 then lo else c) hi' false space hchild

theorem treeWalkComplete_of_invOK (p : Params) (P : Struct BVal) (t : Time)
    (hP : HighKindsOK p P) (hi : InvOK p P t) : TreeWalkComplete p P t := by
  unfold InvOK faultsAt at hi
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hi
  | some r =>
    simp only [hr] at hi
    exact ⟨r,hr,walk_complete_of_highKindsOK p P t p.fuel hP r 0 none true true hi⟩

/-- For actual runs, the complete-walk premise follows from InvOK. No
additional assumption on sorting, thresholds or successful transactions is
needed beyond the supplied invariant at this time. -/
theorem treeRun_walkComplete (p : Params) (ts : List Tx) (t : Time)
    (hi : InvOK p (treeRun p ts) t) : TreeWalkComplete p (treeRun p ts) t :=
  treeWalkComplete_of_invOK p _ t (treeRun_highKindsOK p ts) hi

theorem nodeCountBound_of_invariants_and_counts (p : Params) (hinv : InvPreserved p)
    (hterminal : ∀ ts, Within p ts → ∀ t ≤ ts.length,
      terminalEntryCount p (treeRun p ts) t ≤ (refKvs ts t).length)
    (hroots : ∀ ts, Within p ts → ∀ t ≤ ts.length,
      segmentRootCount p (treeRun p ts) t ≤ segTrees (refKvs ts t)) : NodeCountBound p := by
  apply nodeCountBound_of_complete p hinv
  · intro ts hts t ht
    exact treeRun_walkComplete p ts t (hinv ts hts t ht).1
  · exact hroots
  · exact hterminal

end SIS.Tree
