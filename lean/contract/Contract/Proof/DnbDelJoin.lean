/-
bergdb 030-36: one join of two planned segment leaves. A small changed
leaf joined with a neighbour costs at most two more writes than their
separate decisions, and at most three more new parent entries. Its list
cannot remain small if the neighbour has at least m entries. Inner joins
rebalance one level down and do not satisfy that last argument.
-/
import Contract.Proof.DnbDelFacts
import Contract.Proof.DnbDelTree

namespace Contract.PE

open DNB PeProof

/-- A list of payload ids has no planned key-node writes. -/
theorem vcostL_payloads {es : List (Nat × VN)} (he : ∀ e ∈ es, ∃ y, e.2 = .old y) :
    vcostL es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨y, hy⟩ := he e List.mem_cons_self
    simp only [vcostL, hy, vcost, zero_add]
    exact ih (fun e he' => he e (List.mem_cons_of_mem _ he'))

/-- The two-write and three-entry allowances for a join of two planned
leaves. The left leaf is the small one; the arithmetic is symmetric in the
two list lengths. This is a local join result, not an iteration bound. -/
theorem leaf_join_cost {b G H : Nat} (hb : 8 ≤ b) {s : Tree} {i : Time} {g c yL yR : Nat}
    {nL nR : KNode} {esL esR : List (Nat × VN)} {v : VN}
    (hL : nL.ks.length ≤ b) (hR : nR.ks.length ≤ b)
    (hpL : ∀ e ∈ esL, ∃ y, e.2 = .old y) (hpR : ∀ e ∈ esR, ∃ y, e.2 = .old y)
    (hlenL : (esL.flatMap (fun e => ents e.1 e.2)).length ≤ (live nL.ks).length +
      ((esL.flatMap (fun e => ents e.1 e.2)).filter (isAdded (live nL.ks))).length)
    (hlenR : (esR.flatMap (fun e => ents e.1 e.2)).length ≤ (live nR.ks).length +
      ((esR.flatMap (fun e => ents e.1 e.2)).filter (isAdded (live nR.ks))).length)
    (hs : (esL.flatMap (fun e => ents e.1 e.2)).length < (Cfg.java b G H).m)
    (hc : decideNode (Cfg.java b G H) i (some nL) false
      (esL.flatMap (fun e => ents e.1 e.2)) ≠ .same)
    (hm : mkNode (Cfg.java b G H) i s none g 0 true (esL ++ esR) = some v) :
    let FL := esL.flatMap (fun e => ents e.1 e.2)
    let FR := esR.flatMap (fun e => ents e.1 e.2)
    let wL := VN.node (some yL) g 0 false esL FL (decideNode (Cfg.java b G H) i (some nL) false FL)
    let wR := VN.node (some yR) g 0 false esR FR (decideNode (Cfg.java b G H) i (some nR) false FR)
    vcost v ≤ vcost wL + vcost wR + 2 ∧
      noneCount c v ≤ noneCount c wL + noneCount c wR + 3 ∧
      (v.size < (Cfg.java b G H).m → FR.length < (Cfg.java b G H).m) := by
  intro FL FR wL wR
  obtain ⟨_, hmc, _, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc1 : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  have hdL := decide_facts (G := G) (H := H) (i := i) (g := g) (h := 0) (y := yL) (c := c) (es := esL) hb hL hlenL
  have hdR := decide_facts (G := G) (H := H) (i := i) (g := g) (h := 0) (y := yR) (c := c) (es := esR) hb hR hlenR
  have hdL1 := hdL.2.1 hc
  have hdR1 := hdR.2.2.1
  have hdR2 := hdR.2.2.2.1
  change FL.length < (Cfg.java b G H).m at hs
  have hk := nParts_add_le (c := (Cfg.java b G H).c) (a := FL.length) (n := FR.length)
    hc1 (by omega)
  have hvL := vcostL_payloads hpL
  have hvR := vcostL_payloads hpR
  have hF : (esL ++ esR).flatMap (fun e => ents e.1 e.2) = FL ++ FR := List.flatMap_append
  unfold mkNode at hm
  simp only [beq_self_eq_true, ↓reduceIte, Bool.or_eq_true] at hm
  split at hm
  · cases hm
  · simp only [Option.some.injEq] at hm
    subst hm
    rw [hF]
    simp only [decideNode, ↓reduceIte]
    have hj := joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := c)
      (es := esL ++ esR) (F := FL ++ FR)
    simp only [List.length_append] at hj
    obtain ⟨_, _, hjn, _⟩ := hj
    refine ⟨?_, ?_, ?_⟩
    · have hv : vcostL (esL ++ esR) = 0 := vcostL_payloads (by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hpL e he
        · exact hpR e he)
      simp only [List.length_append]
      change nParts (Cfg.java b G H).c (FL.length + FR.length) + vcostL (esL ++ esR) ≤
        (dcost (decideNode (Cfg.java b G H) i (some nL) false FL) + vcostL esL) +
        (dcost (decideNode (Cfg.java b G H) i (some nR) false FR) + vcostL esR) + 2
      rw [hv, hvL, hvR]
      change 1 ≤ dcost (decideNode (Cfg.java b G H) i (some nL) false FL) at hdL1
      change nParts (Cfg.java b G H).c FR.length ≤
        dcost (decideNode (Cfg.java b G H) i (some nR) false FR) + 2 at hdR1
      omega
    · simp only [List.length_append]
      rw [hjn]
      change nParts (Cfg.java b G H).c FR.length ≤ noneCount c wR + 2 at hdR2
      omega
    · simp only [VN.size, List.length_append]
      omega

end Contract.PE
