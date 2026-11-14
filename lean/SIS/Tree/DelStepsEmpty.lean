/-
Case (4)'s delete steps, a leaf that empties (the upward delete), the merges
on (bergdb 024-12, TP7 and TP10): when the leaf is not the space root and the
stop node has room for its bitmap or LE-b (`DelEmptyRoomM`), `DelInvF` where
`afterDelete` and the merges' loop start (`delInvF_of_collGetInv`); the walk
with the kinds' books is `writerWP_del_emptyRoomMK` (DelSteps.lean).
-/
import SIS.Tree.DelStepsUpWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A bound above every node the transaction's nodes replaced. -/
def madeForBound (w : W) : NodeId := w.madeFor.foldr (fun q m => max q.2 m) 0 + 1

theorem madeFor_lt_bound (w : W) : ∀ x o, w.madeFor.lookup x = some o → o < madeForBound w := by
  intro x o h
  have hmem : (x, o) ∈ w.madeFor := by
    obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
    rw [he]; simp
  have hle : ∀ (l : List (NodeId × NodeId)) (q : NodeId × NodeId), q ∈ l →
      q.2 ≤ l.foldr (fun q m => max q.2 m) 0 := by
    intro l
    induction l with
    | nil => intro q hq; cases hq
    | cons a l ih =>
      intro q hq
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih q hq) (Nat.le_max_right _ _)
  have := hle w.madeFor (x, o) hmem
  unfold madeForBound
  omega

/-- Room at the stop node of an upward delete along the path X, Nn, K to depth:
the stop node's bitmap (a segment leaf, or an inner node's klong to a chain
node other than the empty key's) or its LE-b fits without a cascade. -/
def StopRoomP (c : Ctx) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) : Prop :=
  ∀ s, s < depth → (∀ i, s < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
      deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
        (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
      deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
        false) ∧
    ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
      ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false)

/-- The upward delete from the leaf L (node n) of w's tree has room: L is not
the space root, and its stop node has room, along the path to L. -/
def UpRoom (c : Ctx) (base : View BVal) (w : W) (L : NodeId) (n : KNode) : Prop :=
  ∀ P, LinkedFrom (wNode c.p base w) c.i w.top.rootKey P → nodeAt w.top.rootKey P P.length = L →
    0 < P.length ∧ StopRoomP c (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length

/-- A delete, the merges on, that empties its leaf, with room for the upward
delete. -/
def DelEmptyRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n

/-- A delete, the merges on, that empties its leaf, without room for the upward
delete: the leaf is the space root, or its stop node cascades. -/
def DelEmptyOtherM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ ¬ UpRoom c base w L n

theorem delEmptyM_split (c : Ctx) (base : View BVal) (w : W) (op : Op) (h : DelEmptyM c base w op) :
    DelEmptyRoomM c base w op ∨ DelEmptyOtherM c base w op := by
  obtain ⟨pre, cv, L, n, hop, hm, hK, hne, hall⟩ := h
  by_cases hr : UpRoom c base w L n
  · exact Or.inl ⟨pre, cv, L, n, hop, hm, hK, hne, hall, hr⟩
  · exact Or.inr ⟨pre, cv, L, n, hop, hm, hK, hne, hall, hr⟩

/-- What holds of the key's leaf and its node holds of every leaf of the descent. -/
theorem keyLeaf_all2 {c : Ctx} {base : View BVal} {w : W} {pre : List Nat} {cv : Nat}
    {L : NodeId} {n : KNode} {rk : NodeId} (hK : KeyLeaf c base w pre cv L n)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (P : NodeId → KNode → Prop) (hP : P L n) :
    ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L' = some n' → n'.leaf = true → P L' n' := by
  obtain ⟨rk', hrk', hL, hn, hnl⟩ := hK
  rw [hrk] at hrk'
  cases hrk'
  intro L' n' hL' hn' hnl'
  have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
  subst he
  rw [hn] at hn'
  cases hn'
  exact hP

end SIS.Tree
