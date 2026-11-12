import SIS.Tree.InvConsequences

namespace SIS.Tree

open SIS SIS.Check

def segmentRootCount (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  ((nodesRootsAt p P t).filter (·.2)).length

def nodeLiveMass (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  ((nodesRootsAt p P t).map (fun q =>
    ((keyNodeAt p P q.1).map (fun n => (n.liveAt t).length)).getD 0)).sum

theorem nodesRootsAt_map_fst (p : Params) (P : Struct BVal) (t : Time) :
    (nodesRootsAt p P t).map Prod.fst = keyNodesAt p P t := by
  unfold nodesRootsAt keyNodesAt
  cases hr : rootAt (viewOf P) t with
  | none => rfl
  | some r => exact nodesRoots_map_fst p (viewOf P) t p.fuel r true

theorem nodesRoots_has_node (p : Params) (v : View BVal) (t f x : Nat) (isRoot : Bool) :
    ∀ q ∈ nodesRoots p v t f x isRoot, ∃ n, knodeOf p v q.1 = some n := by
  induction f generalizing x isRoot with
  | zero => simp [nodesRoots]
  | succ f ih =>
    intro q hq
    simp only [nodesRoots] at hq
    cases hn : knodeOf p v x with
    | none => simp only [hn,List.not_mem_nil] at hq
    | some n =>
      simp only [hn] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨n,hn⟩
      · obtain ⟨⟨c,y⟩,_,hq⟩ := List.mem_flatMap.mp hq
        split at hq
        · split at hq
          · cases hq
          · exact ih y true q hq
        · exact ih y false q hq

theorem nodesRootsAt_has_node (p : Params) (P : Struct BVal) (t : Time) :
    ∀ q ∈ nodesRootsAt p P t, ∃ n, keyNodeAt p P q.1 = some n := by
  intro q hq
  unfold nodesRootsAt at hq
  cases hr : rootAt (viewOf P) t with
  | none => simp only [hr,List.not_mem_nil] at hq
  | some r =>
    rw [hr] at hq
    obtain ⟨n,hn⟩ := nodesRoots_has_node p (viewOf P) t p.fuel r true q hq
    exact ⟨n,by rwa [keyNodeAt_eq_knodeOf]⟩

theorem rootFlag_partition (ns : List (NodeId × Bool)) :
    ns.length = (ns.filter (·.2)).length + (ns.filter (fun q => !q.2)).length := by
  induction ns with
  | nil => rfl
  | cons q ns ih => cases hq : q.2 <;> simp [hq,ih] <;> omega

theorem fill_mass_lower (ns : List (NodeId × Bool)) (weight : NodeId × Bool → Nat)
    (m : Nat) (hf : ∀ q ∈ ns, q.2 = false → m ≤ weight q) :
    m * (ns.filter (fun q => !q.2)).length ≤ (ns.map weight).sum := by
  induction ns with
  | nil => simp
  | cons q ns ih =>
    have ht : ∀ q ∈ ns, q.2 = false → m ≤ weight q := by
      intro q hq
      exact hf q (List.mem_cons_of_mem _ hq)
    have hi := ih ht
    cases hq : q.2 with
    | false =>
      have hq' := hf q List.mem_cons_self hq
      simp only [List.filter_cons,hq,Bool.not_false,↓reduceIte,List.length_cons,
        List.map_cons,List.sum_cons,Nat.mul_add,Nat.mul_one]
      omega
    | true =>
      simp only [List.filter_cons,hq,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        List.map_cons,List.sum_cons]
      omega

/-- V1 gives the lower bound on total live entries needed for BU1's count. -/
theorem nodeLiveMass_lower (p : Params) (P : Struct BVal) (t : Time)
    (hf : FillOK p P t) (hm : p.merges = true) :
    p.mergeBelow * ((keyNodesAt p P t).length - segmentRootCount p P t) ≤
      nodeLiveMass p P t := by
  have hlen : (nodesRootsAt p P t).length = (keyNodesAt p P t).length := by
    simpa only [List.length_map] using congrArg List.length (nodesRootsAt_map_fst p P t)
  have hp := rootFlag_partition (nodesRootsAt p P t)
  have he : ((nodesRootsAt p P t).filter (fun q => !q.2)).length =
      (keyNodesAt p P t).length - segmentRootCount p P t := by
    unfold segmentRootCount
    omega
  rw [← he]
  apply fill_mass_lower
  intro q hq hqr
  obtain ⟨n,hn⟩ := nodesRootsAt_has_node p P t q hq
  simpa only [hn,Option.map_some,Option.getD_some] using hf hm q hq hqr n hn

theorem node_count_arithmetic (m n N R S E : Nat) (hm : 2 ≤ m)
    (hRN : R ≤ N) (hRS : R ≤ S)
    (hfill : m * (N-R) ≤ E) (hentries : E ≤ n+N-1) :
    N ≤ S + (n+S-1)/(m-1) := by
  by_cases hN : N = 0
  · subst N
    exact Nat.zero_le _
  have hpos : 1 ≤ n+R := by
    by_cases hz : n+R = 0
    · have hn : n = 0 := by omega
      have hR : R = 0 := by omega
      have hmN : N ≤ m*N := by
        have h := Nat.mul_le_mul_right N (show 1 ≤ m by omega)
        simpa using h
      simp only [hn,hR,Nat.sub_zero,Nat.zero_add] at hfill hentries
      omega
    · omega
  have hprod : m*(N-R) = (m-1)*(N-R)+(N-R) := by
    calc
      m*(N-R) = ((m-1)+1)*(N-R) := by congr 1; omega
      _ = (m-1)*(N-R)+(N-R) := by rw [Nat.add_mul,Nat.one_mul]
  have hsplit : n+N-1 = (n+R-1)+(N-R) := by omega
  have hb : (N-R)*(m-1) ≤ n+R-1 := by
    rw [Nat.mul_comm]
    omega
  have hd : N-R ≤ (n+R-1)/(m-1) := (Nat.le_div_iff_mul_le (by omega)).mpr hb
  have hmono : (n+R-1)/(m-1) ≤ (n+S-1)/(m-1) := Nat.div_le_div_right (by omega)
  omega

/-- BU1's numerical inequality follows from V1, a count of segment roots,
and the tree's entry/edge accounting. The last two facts are explicit. -/
theorem nodeCount_at_of_mass (p : Params) (P : Struct BVal) (t n S : Nat)
    (hm : 2 ≤ p.mergeBelow) (hf : FillOK p P t)
    (hroots : segmentRootCount p P t ≤ S)
    (hentries : nodeLiveMass p P t ≤ n + (keyNodesAt p P t).length - 1) :
    (keyNodesAt p P t).length ≤ S + (n+S-1)/(p.mergeBelow-1) := by
  have hm' : p.merges = true := by simpa only [Params.merges,decide_eq_true_eq] using hm
  have hlower := nodeLiveMass_lower p P t hf hm'
  have hRN : segmentRootCount p P t ≤ (keyNodesAt p P t).length := by
    have h := List.length_filter_le (fun q : NodeId × Bool => q.2) (nodesRootsAt p P t)
    have he := congrArg List.length (nodesRootsAt_map_fst p P t)
    simp only [List.length_map] at he
    exact he ▸ h
  exact node_count_arithmetic p.mergeBelow n _ _ S _ hm hRN hroots hlower hentries

/-- A precise remaining interface for TP31: TP7 plus the two global counting
facts connects the proved fill/count calculation to the reference map. -/
theorem nodeCountBound_of_mass (p : Params) (hinv : InvPreserved p)
    (hroots : ∀ ts, Within p ts → ∀ t ≤ ts.length,
      segmentRootCount p (treeRun p ts) t ≤ segTrees (refKvs ts t))
    (hentries : ∀ ts, Within p ts → ∀ t ≤ ts.length,
      nodeLiveMass p (treeRun p ts) t ≤
        (refKvs ts t).length + (keyNodesAt p (treeRun p ts) t).length - 1) :
    NodeCountBound p := by
  intro hp ts hts t ht
  exact nodeCount_at_of_mass p _ t (refKvs ts t).length (segTrees (refKvs ts t)) hp.1
    (fillOK_of_invOK p _ t (hinv ts hts t ht).1) (hroots ts hts t ht) (hentries ts hts t ht)

end SIS.Tree
