import SIS.Tree.NodeCountProof

namespace SIS.Tree

open SIS SIS.Check

/-- Every recursive key link is classified as a key node and fits in the
remaining fuel. Terminal entries need no recursive key walk. -/
def KeyWalkComplete (p : Params) (v : View BVal) (t : Time) : Nat → NodeId → Prop
  | 0, _ => False
  | f+1, x => ∃ n, knodeOf p v x = some n ∧
      ∀ q ∈ n.liveAt t, (n.leaf && segLen q.1 != 7) = false → KeyWalkComplete p v t f q.2

def KNode.terminalEntries (n : KNode) (t : Time) : Nat :=
  ((n.liveAt t).filter (fun q => n.leaf && segLen q.1 != 7)).length

def walkWeight (p : Params) (v : View BVal) (t : Time) (weight : KNode → Nat)
    (f x : Nat) (isRoot : Bool) : Nat :=
  ((nodesRoots p v t f x isRoot).map (fun q => ((knodeOf p v q.1).map weight).getD 0)).sum

theorem sum_map_flatMap_nat {α β : Type} (xs : List α) (f : α → List β) (w : β → Nat) :
    ((xs.flatMap f).map w).sum = (xs.map (fun a => ((f a).map w).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,
      List.map_cons,List.sum_cons]

theorem walkWeight_step (p : Params) (v : View BVal) (t : Time) (weight : KNode → Nat)
    (f x : Nat) (isRoot : Bool) (n : KNode) (hn : knodeOf p v x = some n) :
    walkWeight p v t weight (f+1) x isRoot = weight n +
      ((n.liveAt t).map (fun q => if n.leaf && segLen q.1 != 7 then 0
        else walkWeight p v t weight f q.2 n.leaf)).sum := by
  unfold walkWeight
  rw [nodesRoots]
  simp only [hn,List.map_cons,List.sum_cons,Option.map_some,Option.getD_some,
    sum_map_flatMap_nat]
  congr 1
  congr 1
  congr 1
  funext q
  cases hl : n.leaf <;> cases hc : segLen q.1 != 7 <;> simp

theorem nodesRoots_length_step (p : Params) (v : View BVal) (t : Time)
    (f x : Nat) (isRoot : Bool) (n : KNode) (hn : knodeOf p v x = some n) :
    (nodesRoots p v t (f+1) x isRoot).length = 1 +
      ((n.liveAt t).map (fun q => if n.leaf && segLen q.1 != 7 then 0
        else (nodesRoots p v t f q.2 n.leaf).length)).sum := by
  rw [nodesRoots]
  simp only [hn,List.length_cons,List.length_flatMap]
  rw [Nat.add_comm]
  congr 1
  congr 1
  congr 1
  funext q
  cases hl : n.leaf <;> cases hc : segLen q.1 != 7 <;> simp

theorem entry_accounting {α : Type} (xs : List α) (terminal : α → Bool)
    (entries nodes values : α → Nat)
    (h : ∀ q ∈ xs, terminal q = false → entries q+1 = nodes q+values q) :
    xs.length + (xs.map (fun q => if terminal q then 0 else entries q)).sum =
      (xs.map (fun q => if terminal q then 0 else nodes q)).sum +
        (xs.filter terminal).length +
          (xs.map (fun q => if terminal q then 0 else values q)).sum := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    cases hq : terminal q with
    | true =>
      simp only [List.length_cons,List.map_cons,List.sum_cons,List.filter_cons,hq,↓reduceIte]
      omega
    | false =>
      have hc := h q List.mem_cons_self hq
      simp only [List.length_cons,List.map_cons,List.sum_cons,List.filter_cons,hq,
        Bool.false_eq_true,↓reduceIte]
      omega

/-- A complete key walk has one incoming key edge per nonroot node; every
other live entry is terminal. Sharing is counted with multiplicity. -/
theorem walk_entry_identity (p : Params) (v : View BVal) (t f x : Nat) (isRoot : Bool)
    (hc : KeyWalkComplete p v t f x) :
    walkWeight p v t (fun n => (n.liveAt t).length) f x isRoot + 1 =
      (nodesRoots p v t f x isRoot).length +
        walkWeight p v t (fun n => n.terminalEntries t) f x isRoot := by
  induction f generalizing x isRoot with
  | zero => exact hc.elim
  | succ f ih =>
    obtain ⟨n,hn,hchildren⟩ := hc
    have he := entry_accounting (n.liveAt t) (fun q => n.leaf && segLen q.1 != 7)
      (fun q => walkWeight p v t (fun n => (n.liveAt t).length) f q.2 n.leaf)
      (fun q => (nodesRoots p v t f q.2 n.leaf).length)
      (fun q => walkWeight p v t (fun n => n.terminalEntries t) f q.2 n.leaf)
      (by intro q hq ht; exact ih q.2 n.leaf (hchildren q hq ht))
    rw [walkWeight_step p v t _ f x isRoot n hn,
      nodesRoots_length_step p v t f x isRoot n hn,
      walkWeight_step p v t _ f x isRoot n hn]
    change _ + 1 = _ + (((n.liveAt t).filter _).length + _)
    omega

def TreeWalkComplete (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∃ r, rootAt (viewOf P) t = some r ∧ KeyWalkComplete p (viewOf P) t p.fuel r

def terminalEntryCount (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  ((nodesRootsAt p P t).map (fun q =>
    ((keyNodeAt p P q.1).map (fun n => n.terminalEntries t)).getD 0)).sum

theorem nodeLiveMass_identity (p : Params) (P : Struct BVal) (t : Time)
    (hc : TreeWalkComplete p P t) :
    nodeLiveMass p P t + 1 = (keyNodesAt p P t).length + terminalEntryCount p P t := by
  obtain ⟨r,hr,hcomplete⟩ := hc
  have h := walk_entry_identity p (viewOf P) t p.fuel r true hcomplete
  have hlen : (nodesRoots p (viewOf P) t p.fuel r true).length =
      (nodesAt p (viewOf P) t p.fuel r).length := by
    simpa only [List.length_map] using
      congrArg List.length (nodesRoots_map_fst p (viewOf P) t p.fuel r true)
  rw [hlen] at h
  simpa only [nodeLiveMass,terminalEntryCount,nodesRootsAt,keyNodesAt,hr,
    keyNodeAt_eq_knodeOf,walkWeight] using h

/-- BU1's finite-tree count, before identifying terminal entries and segment
roots with the reference map. -/
theorem nodeCount_complete_fill (p : Params) (P : Struct BVal) (t : Time)
    (hm : 2 ≤ p.mergeBelow) (hf : FillOK p P t) (hc : TreeWalkComplete p P t) :
    (keyNodesAt p P t).length ≤ segmentRootCount p P t +
      (terminalEntryCount p P t + segmentRootCount p P t - 1)/(p.mergeBelow-1) := by
  apply nodeCount_at_of_mass p P t _ _ hm hf (Nat.le_refl _)
  have h := nodeLiveMass_identity p P t hc
  omega

theorem nodeCountBound_of_complete (p : Params) (hinv : InvPreserved p)
    (hcomplete : ∀ ts, Within p ts → ∀ t ≤ ts.length, TreeWalkComplete p (treeRun p ts) t)
    (hroots : ∀ ts, Within p ts → ∀ t ≤ ts.length,
      segmentRootCount p (treeRun p ts) t ≤ segTrees (refKvs ts t))
    (hvalues : ∀ ts, Within p ts → ∀ t ≤ ts.length,
      terminalEntryCount p (treeRun p ts) t ≤ (refKvs ts t).length) : NodeCountBound p := by
  apply nodeCountBound_of_mass p hinv hroots
  intro ts hts t ht
  have hi := nodeLiveMass_identity p (treeRun p ts) t (hcomplete ts hts t ht)
  have hv := hvalues ts hts t ht
  omega

end SIS.Tree
