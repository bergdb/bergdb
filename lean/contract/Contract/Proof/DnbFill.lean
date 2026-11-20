/-
bergdb 030-29: the trace checker's walk of the writer's fill rules gives
`Filled` (Contract/Proof/DnbDefs.lean).

`shapeFaults` (Contract/Shape.lean) walks the tree from the space root with
the fuel of the root's level and one more, and reports RootsOK and FillOK at
every key node it reaches: a segment leaf's long entries go on as roots of
the next segment's tree, an inner node's children as nodes that are not
roots. With no faults, the walk never runs out of fuel (a walk with no fuel
left reports "fuel"), so every node it reaches meets the two rules, and so
the space root is `Filled` as a segment tree's root:

* `filled_of_shapeWalk`: a walk from x with no faults gives `Filled` of x;
* `filled_of_shapeFaults`: a tree with no faults has its space root
  `Filled` as a root.

Nothing else is assumed: neither the invariants nor the fuel's sufficiency,
since a fault-free walk is itself the proof that the fuel sufficed.
-/
import Contract.Proof.DnbDefs

namespace Contract.PE

/-- The parts of a list of fault lists that are all empty. -/
private theorem flatMap_nil {α : Type} {f : α → List String} {l : List α}
    (h : l.flatMap f = []) : ∀ a ∈ l, f a = [] := by
  intro a ha
  exact List.eq_nil_of_subset_nil (fun z hz => by
    rw [← h]; exact List.mem_flatMap.mpr ⟨a, ha, hz⟩)

/-- **A walk with no faults gives `Filled`**: from key node x, a segment
tree's root if `isRoot`, the walk of the fill rules with any fuel that finds
no fault shows that x and every node below it meet RootsOK and FillOK. -/
theorem filled_of_shapeWalk (cf : Cfg) (s : Tree) :
    ∀ (f : Nat) (x : NodeId) (isRoot : Bool),
      shapeWalk ⟨cf.H, cf.m, cf.theta⟩ s f x isRoot = [] → Filled cf s isRoot x
  | 0, _, _, h => by simp [shapeWalk] at h
  | f + 1, x, isRoot, h => by
    unfold shapeWalk at h
    cases ho : s.obj x with
    | none => exact Filled.other (fun n hn => by rw [ho] at hn; cases hn)
    | some o =>
      cases o with
      | val v => exact Filled.other (fun n hn => by rw [ho] at hn; cases hn)
      | key n =>
        rw [ho] at h
        simp only [List.append_eq_nil_iff] at h
        obtain ⟨⟨⟨⟨⟨_, hR⟩, hF⟩, _⟩, _⟩, hk⟩ := h
        have hkid := flatMap_nil hk
        refine Filled.key ho ?_ ?_ ?_ ?_
        · intro hl hr
          simp only [hl, hr, Bool.not_false, Bool.true_and, decide_eq_true_eq, ite_eq_right_iff,
            List.cons_ne_nil, imp_false, Nat.not_lt] at hR
          exact hR
        · intro hm hr
          simp only [hm, hr, decide_true, Bool.true_and, Bool.not_false,
            decide_eq_true_eq, ite_eq_right_iff, List.cons_ne_nil, imp_false, Nat.not_lt] at hF
          exact hF
        · intro c y hcy hl hlong
          have := hkid (c, y) hcy
          simp only [hl, hlong, ite_true] at this
          exact filled_of_shapeWalk cf s f y true this
        · intro c y hcy hl
          have := hkid (c, y) hcy
          simp only [hl, Bool.false_eq_true, ite_false, List.append_eq_nil_iff] at this
          exact filled_of_shapeWalk cf s f y false this.2

/-- **The space root is `Filled`**: a tree in which the trace checker's walk
of the writer's rules (`shapeFaults`, with the parameters H, m and theta)
finds no fault has its space root `Filled` as a segment tree's root. -/
theorem filled_of_shapeFaults {cf : Cfg} {s : Tree} {r : NodeId}
    (hsf : shapeFaults ⟨cf.H, cf.m, cf.theta⟩ s = []) (hr : s.root = some r) :
    Filled cf s true r := by
  unfold shapeFaults at hsf
  rw [hr] at hsf
  exact filled_of_shapeWalk cf s _ r true hsf

end Contract.PE
