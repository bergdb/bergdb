/-
The take-back's (B) through a cascade of splits (bergdb 024-12, TP4;
`TtReachedN`, TakeInvTree.lean): latest's `writerWP_appendKlongs_chainGRV`
gives that the tree with the klongs put in reaches what it reached but the
chain's nodes, every chain node is reached or holds its version before the
transaction, and every node the cascade made is reached (R2, R3). With the
writer's tree's nodes reached in the tree with the klongs put in
(`reach_updN_keep`), every node with a klong of the transaction's time is
reached after: `writerWP_appendKlongs_take`.
-/
import SIS.Tree.GetCascadeChainG
import SIS.Tree.TakeInvTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (B) after a change that keeps what a tree U reaches but a set Ch of nodes,
each of which is reached after or has no klong of t, and makes new nodes at or
above nx that are reached; the nodes below nx not in Ch as before, and what N
reaches U reaches, or it is no node. -/
theorem ttReachedN_cascade (N N' U : NodeId → Option KNode) (t : Time) (r r' : NodeId)
    (nx : NodeId) (Ch : NodeId → Prop) (hTt : TtReachedN N t r)
    (hU : ∀ u, TReach N t r u → TReach U t r u ∨ N u = none)
    (hkeepR : ∀ z, TReach U t r z → ¬ Ch z → TReach N' t r' z)
    (hch : ∀ z, Ch z → TReach N' t r' z ∨ ∀ zn, N' z = some zn → Klong.time t ∉ zn.ks)
    (hnew : ∀ z zn, nx ≤ z → N' z = some zn → TReach N' t r' z)
    (hold : ∀ z, z < nx → ¬ Ch z → N' z = N z) : TtReachedN N' t r' := by
  intro u un hu hm
  by_cases hc : Ch u
  · rcases hch u hc with h | h
    · exact h
    · exact absurd hm (h un hu)
  · rcases Nat.lt_or_ge u nx with hlt | hge
    · rw [hold u hlt hc] at hu
      rcases hU u (hTt u un hu hm) with h | h
      · exact hkeepR u h hc
      · rw [h] at hu; cases hu
    · exact hnew u un hge hu

/-- A cascade of splits keeps the take-back's (B) (`TtReachedN`): latest's
`writerWP_appendKlongs_chainGRV` with its premises, given `ChainOrd` along the
chain and that the node appended to keeps its live children with the klongs put
in, or loses only children that are no nodes (a value replaced). -/
theorem writerWP_appendKlongs_take (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', s < i' → i' < i → ChainOrd c K Nn i')))) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      (s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0) →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      (∀ cc u, (cc, u) ∈ (Nn (s + e)).liveAt c.i →
        (∃ c', (c', u) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i) ∨
        wNode c.p base w u = none) →
      (∀ i, s < i → i ≤ s + e → ChainOrd c K Nn i) → 0 < c.i →
      TtReachedN (wNode c.p base w) c.i w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w
        (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
  intro e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV hkeepL hOrd hpos hTt
  refine writerWP_mono (writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV) ?_
  rintro _ w' ⟨_, ⟨_, ht', _, _, _⟩, hf, _, _, _, _, hRK, hRN⟩
  obtain ⟨hR2, hR3⟩ := hRN hOrd
  have hR := hRK hOrd
  have hx : wNode c.p base w (X (s + e)) = some (Nn (s + e)) := by
    simp only [wNode, (h4 (s + e) (by omega) (Nat.le_refl _)).2, Bool.false_eq_true, ↓reduceIte,
      (h4 (s + e) (by omega) (Nat.le_refl _)).1]
  apply ttReachedN_cascade (wNode c.p base w) (wNode c.p base w') _ c.i w.top.rootKey w'.top.rootKey
    w.next (fun z => ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i) hTt
    (reach_updN_keep (wNode c.p base w) c.i w.top.rootKey (X (s + e)) (Nn (s + e)) _ hx hkeepL)
  · intro z hz hnc
    exact hR z hz (fun i hi1 hi2 he => hnc ⟨i, hi1, hi2, he⟩)
  · rintro z ⟨i, hi1, hi2, rfl⟩
    rcases hR2 i hi1 hi2 with h | h
    · exact Or.inl h
    · right
      intro zn hzn
      have hw' : wNode c.p base w' (X i) = some ((Nn i).toPrev (c.i - 1)) := by
        simp only [wNode, ht', (h4 i hi1 hi2).2, Bool.false_eq_true, ↓reduceIte, h]
      rw [hw'] at hzn
      cases hzn
      exact time_not_mem_prefixAt (Nn i).ks c.i hpos
  · intro z zn hz hzn
    apply hR3 z hz
    obtain ⟨_, htz, hkz⟩ := h7 z hz
    unfold wNode at hzn
    rw [ht', htz] at hzn
    simp only [Bool.false_eq_true, ↓reduceIte] at hzn
    cases hl : w'.nodes.lookup z with
    | none => rw [hl, hkz] at hzn; cases hzn
    | some _ => rfl
  · intro z hz hnc
    unfold wNode
    rw [ht', hf z hz (fun i hi1 hi2 he => hnc ⟨i, hi1, hi2, he⟩)]

end SIS.Tree
