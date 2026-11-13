/-
The take-back's (B), (C) and node facts after a split of a full node with a
last version given by the caller and its cascade (bergdb 024-12, TP7): a
delete's full leaf (`lastVersionGivenDel`) or a merge's full parent
(`mergeFullLast`). `takeJ2_after_lastSplit` is the state-level step: from the
nodes' shapes after it (latest's `CascadeNodeShape` one level up, with no klongs
put) and the reach-back of the tree V with the node's last version (the form of
chainGRVf's last conjuncts), `TakeJ2` before gives `TakeJ2` after.
-/
import SIS.Tree.TakeDeadChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node left behind holds no klong of the transaction's time. -/
theorem time_not_mem_toPrev (n : KNode) (t : Time) (hpos : 0 < t) :
    Klong.time t ∉ (n.toPrev (t - 1)).ks := by
  intro h
  have := time_le_of_mem_prefixAt n.ks (t - 1) t h
  omega

/-- `TakeJ2` after a split with a given last version and its cascade along
X s .. X (D + 1), from `TakeJ2` before and the state facts after: taken ids and
values kept, nodes below the next id off the chain kept, every node new or on
the chain with latest's shape (`CascadeNodeShape` with no klongs put), the
chain cached, and the reach-back of a node map V: a node of the transaction's
time off the chain reached in V (`hVR`) is reached after (`hRB1`), a chain node
is reached after or left behind (`hRB2`), and a new node is reached (`hRB3`). -/
theorem takeJ2_after_lastSplit (c : Ctx) (base : View BVal) (B : NodeId) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode) (s D : Nat) (V : NodeId → Option KNode) (w w' : W)
    (hpos : 0 < c.i) (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hvn : ∀ y ∈ w.vals.map (·.1), y < w.next)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlk : ∀ i, s ≤ i → i ≤ D + 1 → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hwf : ∀ i, s ≤ i → i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (hts : ∀ i, s ≤ i → i ≤ D + 1 → ∀ u, Klong.time u ∈ (Nn i).ks → u ≤ c.i)
    (hR : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hfresh : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (ht' : w'.taken = w.taken) (hv' : w'.vals = w.vals)
    (hframe : ∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
      w'.nodes.lookup z = w.nodes.lookup z)
    (hshape : ∀ z zn, w'.nodes.lookup z = some zn → (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) →
      CascadeNodeShape c X K Nn s (D + 1) [] z zn)
    (hcached : ∀ i, s ≤ i → i ≤ D + 1 → (w'.nodes.lookup (X i)).isSome = true)
    (hVR : ∀ q qn, wNode c.p base w q = some qn → Klong.time c.i ∈ qn.ks →
      (∀ i, s ≤ i → i ≤ D + 1 → q ≠ X i) → TReach V c.i w.top.rootKey q)
    (hRB1 : ∀ z, TReach V c.i w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
      TReach (wNode c.p base w') c.i w'.top.rootKey z)
    (hRB2 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
      w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1)))
    (hRB3 : ∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
      TReach (wNode c.p base w') c.i w'.top.rootKey z) :
    TakeJ2 c base B w' := by
  obtain ⟨_, hD, hO, hS, hM, hV0⟩ := hJ
  have hN : ∀ i, s ≤ i → i ≤ D + 1 → wNode c.p base w (X i) = some (Nn i) := fun i a b => by
    simp only [wNode, (hlk i a b).2, Bool.false_eq_true, ↓reduceIte, (hlk i a b).1]
  have hoff : ∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
      wNode c.p base w' z = wNode c.p base w z := by
    intro z hz hnc
    simp only [wNode, ht', hframe z hz hnc]
  -- the lookup of a node after, new or on the chain
  have hlkz : ∀ z zn, wNode c.p base w' z = some zn →
      (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → w'.nodes.lookup z = some zn := by
    intro z zn hzn hz
    have htz : w'.taken.contains z = false := by
      rw [ht']
      rcases hz with hz | ⟨i, a, b, rfl⟩
      · exact (hfresh z hz).2.1
      · exact (hlk i a b).2
    unfold wNode at hzn
    rw [htz] at hzn
    simp only [Bool.false_eq_true, ↓reduceIte] at hzn
    cases hl : w'.nodes.lookup z with
    | some m => rw [hl] at hzn; exact hzn
    | none =>
      exfalso
      rw [hl] at hzn
      rcases hz with hz | ⟨i, a, b, rfl⟩
      · rw [(hfresh z hz).2.2] at hzn; cases hzn
      · have := hcached i a b
        rw [hl] at this; cases this
  unfold TakeJ2
  rw [hv']
  refine ⟨?_, ?_⟩
  · -- (B): a node of the transaction's time is reached
    intro q qn hq hm
    by_cases hc : w.next ≤ q ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ q = X i
    · rcases hc with hc | ⟨i, a, b, rfl⟩
      · exact hRB3 q hc (by rw [hlkz q qn hq (Or.inl hc)]; rfl)
      · rcases hRB2 i a b with h | h
        · exact h
        · exfalso
          have := hlkz _ qn hq (Or.inr ⟨i, a, b, rfl⟩)
          rw [h] at this
          cases this
          exact time_not_mem_toPrev (Nn i) c.i hpos hm
    · have hlt : q < w.next := by
        rcases Nat.lt_or_ge q w.next with h | h
        · exact h
        · exact absurd (Or.inl h) hc
      have hnc : ∀ i, s ≤ i → i ≤ D + 1 → q ≠ X i := fun i a b he => hc (Or.inr ⟨i, a, b, he⟩)
      rw [hoff q hlt hnc] at hq
      exact hRB1 q (hVR q qn hq hm hnc) hnc
  · refine j2rest_cascade2 (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey B _ X Nn s (D + 1)
      w.next hpos hT hD hO hS hM hV0 hN hwf hts hR hvn hoff ?_
    intro z zn hzn hz
    exact cascadeShapeJ2_of c (wNode c.p base w) B _ X K Nn s (D + 1) [] w.next hS hM hN hts hBn
      (by simp) (by simp) z zn hz (hshape z zn (hlkz z zn hzn hz) hz)

end SIS.Tree
