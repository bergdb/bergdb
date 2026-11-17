/-
The contract package (bergdb 030-08): TREE, a clause of the contract that
the reads did not need. To read and to trust, with Statement.lean.

English. Walk the tree from the space root through the live klongs, as the
invariants' walk does, and list every node reached, values too, the root
first. TREE: no node is in the list twice. So every node reached but the
space root is the live child of exactly one node reached, by one live klong.

Why it is a clause: the abstract model's theorems of lazy reading, eviction
and handles assume it (lean/SIS/Phys.lean, `treeAt`), and the invariants do
not give it: across segments nothing rules a shared child out (030-06,
section 3; Contract/ExampleDag.lean meets the contract with two segment
leaves that share the next segment's tree).

`TreeOk` is the statement. `treeOkB` is what the trace checker runs: the
list sorted and checked to increase strictly, which `treeOkB_sound` proves
gives `TreeOk`. Nothing here needs Mathlib.
-/
import Contract.Statement

namespace Contract

/-- The nodes that the walk from node x reaches through live klongs, x first,
in the walk's order; a node reached twice is listed twice. The fuel as for
`listAt`: a key node's children get one less; a node reached with no fuel
left is listed without its children. -/
def reachAt (s : Tree) : Nat → NodeId → List NodeId
  | 0, x => [x]
  | f + 1, x =>
    x :: (match s.obj x with
      | some (.key n) => (live n.ks).flatMap (fun cy => reachAt s f cy.2)
      | _ => [])

/-- The nodes reached from the space root. -/
def reach (s : Tree) : List NodeId :=
  match s.root with
  | some r => reachAt s (s.fuel r) r
  | none => []

/-- TREE: no node is reached twice. The tree at time t meets it if
`TreeOk (s.at t)`. -/
def TreeOk (s : Tree) : Prop := (reach s).Nodup

instance (s : Tree) : Decidable (TreeOk s) := inferInstanceAs (Decidable (reach s).Nodup)

/-! ## The check that runs -/

/-- The numbers increase strictly. -/
def strictUp : List Nat → Bool
  | a :: b :: r => decide (a < b) && strictUp (b :: r)
  | _ => true

/-- TREE, computed: the nodes reached, sorted, increase strictly. -/
def treeOkB (s : Tree) : Bool := strictUp ((reach s).mergeSort (fun a b => decide (a ≤ b)))

theorem strictUp_pairwise : ∀ l : List Nat, strictUp l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: r, h => by
    simp only [strictUp, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictUp_pairwise (b :: r) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

/-- The computed TREE gives TREE. -/
theorem treeOkB_sound (s : Tree) (h : treeOkB s = true) : TreeOk s := by
  have h1 := (strictUp_pairwise _ h).imp (fun hab => Nat.ne_of_lt hab)
  exact (List.mergeSort_perm (reach s) _).nodup_iff.mp h1

end Contract
