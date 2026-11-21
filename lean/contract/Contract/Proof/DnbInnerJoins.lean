/-
bergdb 030-37: one level of inner joins, including the leaf rebalance
inside each join. A group's potential counts its small inner node and
its remaining small leaf. A small inner group may absorb more than one
non-small neighbour; the potential accounts for that case.
-/
import Contract.Proof.DnbInnerLeaves

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

def ownCost : VN → Nat
  | .old _ => 0
  | .node _ _ _ _ _ _ d => dcost d

/-- Inner nodes whose children are leaves and have finished rebalance.
The three constructors include untouched neighbours and joined groups. -/
inductive JoinInner (b G H : Nat) (i : Time) (s : Tree) : VN → Prop where
  | old {y : NodeId} {n : KNode} : getKey s y = some n → n.ks.length ≤ b →
      (Cfg.java b G H).m ≤ (live n.ks).length →
      LeafReady b G H i s ((live n.ks).map (fun q => (q.1, VN.old q.2))) →
      JoinInner b G H i s (.old y)
  | planned {y g : Nat} {n : KNode} {es : List (Nat × VN)} :
      n.ks.length ≤ b → LeafReady b G H i s es →
      (renameHead 0 (entries es)).length ≤ (live n.ks).length +
        ((renameHead 0 (entries es)).filter (isAdded (live n.ks))).length →
      (decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es)) = .same →
        (Cfg.java b G H).m ≤ (renameHead 0 (entries es)).length) →
      JoinInner b G H i s (.node (some y) g 1 false es (renameHead 0 (entries es))
        (decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es))))
  | joined {g : Nat} {es : List (Nat × VN)} : LeafReady b G H i s es →
      JoinInner b G H i s (.node none g 1 true es (renameHead 0 (entries es))
        (.parts (nParts (Cfg.java b G H).c (renameHead 0 (entries es)).length)))

def innerPotential (cf : Cfg) (s : Tree) (v : VN) : Nat :=
  (if smallLeaf cf v then 1 else 0) + smallLeaves cf ((openEs s v).getD [])

def innerPotentials (cf : Cfg) (s : Tree) (es : List (Nat × VN)) : Nat :=
  (es.map (fun e => innerPotential cf s e.2)).sum

theorem innerPotentials_cons (cf : Cfg) (s : Tree) (e : Nat × VN) (es : List (Nat × VN)) :
    innerPotentials cf s (e :: es) = innerPotential cf s e.2 + innerPotentials cf s es := by
  simp [innerPotentials]

theorem innerPotentials_append (cf : Cfg) (s : Tree) (A B : List (Nat × VN)) :
    innerPotentials cf s (A ++ B) = innerPotentials cf s A + innerPotentials cf s B := by
  simp [innerPotentials]

theorem JoinInner.open {b G H : Nat} {v : VN} (hv : JoinInner b G H i s v) :
    ∃ es, openEs s v = some es ∧ LeafReady b G H i s es ∧
      (entries es).length = cntOf s v ∧ vcost v = ownCost v + vcostL es := by
  cases hv with
  | @old y n hk _ _ hr =>
    refine ⟨_, by simp [openEs, hk], hr, ?_, ?_⟩
    · simp [entries, cntOf, hk, List.flatMap_map, ents]
    · have hz := vcostL_payloads (es := (live n.ks).map (fun q => (q.1, VN.old q.2))) (by
        intro e he
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
        exact ⟨q.2, rfl⟩)
      simp [vcost, ownCost, hz]
  | planned _ hr _ _ => exact ⟨_, rfl, hr, by simp [cntOf, VN.size, renameHead_length], rfl⟩
  | joined hr => exact ⟨_, rfl, hr, by simp [cntOf, VN.size, renameHead_length], rfl⟩

theorem JoinInner.small {b G H : Nat} {v : VN} (hv : JoinInner b G H i s v) :
    smallLeaf (Cfg.java b G H) v = true ↔ cntOf s v < (Cfg.java b G H).m := by
  cases hv with
  | old hk _ hf _ => simp [smallLeaf, VN.changed, cntOf, hk]; omega
  | @planned y g n es _ _ _ hf =>
    change ((decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es)) != .same) &&
      decide ((renameHead 0 (entries es)).length < (Cfg.java b G H).m)) = true ↔
      (renameHead 0 (entries es)).length < (Cfg.java b G H).m
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨fun he => by have := hf he; omega, h⟩⟩
  | @joined g es _ =>
    change ((Dec.parts _ != Dec.same) && decide ((renameHead 0 (entries es)).length <
      (Cfg.java b G H).m)) = true ↔ _
    simp [cntOf, VN.size]

theorem JoinInner.cost {b G H : Nat} (hb : 8 ≤ b) {v : VN}
    (hv : JoinInner b G H i s v) (cv : Nat) :
    nParts (Cfg.java b G H).c (cntOf s v) ≤ ownCost v + 2 ∧
      nParts (Cfg.java b G H).c (cntOf s v) ≤ noneCount cv v + 2 ∧
      (smallLeaf (Cfg.java b G H) v = true → 1 ≤ ownCost v) ∧
      (ents cv v).length ≤ 1 + noneCount cv v := by
  obtain ⟨_, _, hM, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  change b ≤ 2 * (Cfg.java b G H).c at hM
  cases hv with
  | @old y n hk hks _ _ =>
    have hlen := live_length_le n.ks
    have ht := nParts_two hc (n := (live n.ks).length) (by omega)
    simpa [cntOf, hk, ownCost, noneCount, ents, smallLeaf, VN.changed] using ht
  | @planned y g n es hks _ hlen _ =>
    have hd := decide_facts (G := G) (H := H) (i := i) (g := g) (h := 1) (y := y) (c := cv)
      (es := es) hb hks hlen
    refine ⟨hd.2.2.1, hd.2.2.2.1, ?_, hd.2.2.2.2.2⟩
    intro hs
    have hne : decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es)) ≠ .same := by
      simp only [smallLeaf, Bool.and_eq_true] at hs
      exact bne_iff_ne.mp hs.1
    exact hd.2.1 hne
  | @joined g es _ =>
    have hj := joined_facts (b := b) (G := G) (H := H) (g := g) (h := 1) (c := cv)
      (es := es) (F := renameHead 0 (entries es))
    simp only [cntOf, VN.size, ownCost, dcost]
    exact ⟨by omega, by rw [hj.2.2.1]; omega, fun _ => hj.1, by rw [hj.2.2.1, hj.2.2.2]; omega⟩

/-- A complete inner join with its recursive leaf rebalance. The output
can remain small after absorbing a non-small neighbour. Each such step
still consumes one unit of the combined inner/leaf potential. -/
theorem inner_leaf_join_pair {b G H : Nat} (hb : 8 ≤ b) {f g cL cR : Nat}
    {l r v : VN} {L R J : List (Nat × VN)}
    (hl : JoinInner b G H i s l) (hr : JoinInner b G H i s r)
    (hoL : openEs s l = some L) (hoR : openEs s r = some R)
    (hs : smallLeaf (Cfg.java b G H) l = true ∨ smallLeaf (Cfg.java b G H) r = true)
    (hd : rebalance (Cfg.java b G H) i s f g 0 (L ++ renameHead cR R) = some J)
    (hm : mkNode (Cfg.java b G H) i s none g 1 true J = some v) :
    JoinInner b G H i s v ∧ vcost v ≤ vcost l + vcost r + 4 ∧
      noneCount cL v ≤ noneCount cL l + noneCount cR r + 3 ∧
      innerPotential (Cfg.java b G H) s v + 1 ≤
        innerPotential (Cfg.java b G H) s l + innerPotential (Cfg.java b G H) s r := by
  obtain ⟨L', hL, hRL, hnL, hcL⟩ := hl.open
  obtain ⟨R', hR, hRR, hnR, hcR⟩ := hr.open
  rw [hoL] at hL; cases hL
  rw [hoR] at hR; cases hR
  obtain ⟨j, hj, hJ, hcostJ, hlenJ, hsmallJ, hsameJ⟩ := rebalance_leaf_pair hb hRL (leafReady_rename hRR cR) hd
  rw [vcostL_renameHead] at hcostJ
  rw [entries_renameHead, renameHead_length, hnL, hnR] at hlenJ
  rw [smallLeaves_rename] at hsmallJ
  obtain ⟨hm2, hmc, _, hcap, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc : 1 ≤ (Cfg.java b G H).c := le_trans hcap1 hcap
  have hcl := hl.cost hb cL
  have hcr := hr.cost hb cR
  have hparts : nParts (Cfg.java b G H).c (entries J).length ≤ ownCost l + ownCost r + 2 ∧
      nParts (Cfg.java b G H).c (entries J).length ≤ noneCount cL l + noneCount cR r + 3 := by
    rcases hs with hs | hs
    · have hsm := hl.small.mp hs
      have hsum := nParts_add_le hc (n := cntOf s r) (a := cntOf s l + j) (by omega)
      have hmono := nParts_mono hc (show (entries J).length ≤ cntOf s l + j + cntOf s r by omega)
      have hpos := hcl.2.2.1 hs
      omega
    · have hsm := hr.small.mp hs
      have hsum := nParts_add_le hc (n := cntOf s l) (a := cntOf s r + j) (by omega)
      have hmono := nParts_mono hc (show (entries J).length ≤ cntOf s r + j + cntOf s l by omega)
      have hpos := hcr.2.2.1 hs
      omega
  have hpot : (if (entries J).length < (Cfg.java b G H).m then 1 else 0) +
      smallLeaves (Cfg.java b G H) J + 1 ≤
      (if smallLeaf (Cfg.java b G H) l then 1 else 0) + smallLeaves (Cfg.java b G H) L +
      ((if smallLeaf (Cfg.java b G H) r then 1 else 0) + smallLeaves (Cfg.java b G H) R) := by
    have hz : j = 0 → (entries J).length = cntOf s l + cntOf s r := by
      intro hj0
      rw [hsameJ hj0, entries_append, List.length_append, entries_renameHead,
        renameHead_length, hnL, hnR]
    have hls := hl.small
    have hrs := hr.small
    by_cases hvsmall : (entries J).length < (Cfg.java b G H).m
    · rw [ite_eq_left hvsmall]
      cases hsl : smallLeaf (Cfg.java b G H) l <;>
        cases hsr : smallLeaf (Cfg.java b G H) r
      · simp [hsl, hsr] at hs
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnr : ¬cntOf s l < (Cfg.java b G H).m := by
          intro h; have := hls.mpr h; simp [hsl] at this
        have hj1 : j ≠ 0 := by intro hj0; have := hz hj0; omega
        omega
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnr : ¬cntOf s r < (Cfg.java b G H).m := by
          intro h; have := hrs.mpr h; simp [hsr] at this
        have hj1 : j ≠ 0 := by intro hj0; have := hz hj0; omega
        omega
      · simp only [↓reduceIte]; omega
    · rw [ite_eq_right hvsmall]
      rcases hs with hs | hs <;> simp only [hs, ↓reduceIte] <;> omega
  have hform : v = .node none g 1 true (renameHead 0 J) (renameHead 0 (entries J))
      (.parts (nParts (Cfg.java b G H).c (renameHead 0 (entries J)).length)) := by
    unfold mkNode at hm
    simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte] at hm
    split at hm
    · cases hm
    · simp only [decideNode, ↓reduceIte] at hm
      change some (.node none g 1 true (renameHead 0 J)
        (renameHead 0 (entries (renameHead 0 J)))
        (.parts (nParts (Cfg.java b G H).c (renameHead 0 (entries (renameHead 0 J))).length))) = some v at hm
      rw [entries_renameHead, renameHead_renameHead] at hm
      exact (Option.some.inj hm).symm
  rw [hform]
  ·
    have hFlen : (renameHead 0 (entries J)).length = (entries J).length := renameHead_length _ _
    have hJR : JoinInner b G H i s (.node none g 1 true (renameHead 0 J)
        (renameHead 0 (entries J)) (.parts (nParts (Cfg.java b G H).c (renameHead 0 (entries J)).length))) := by
      simpa only [entries_renameHead, renameHead_renameHead] using
        (JoinInner.joined (g := g) (leafReady_rename hJ 0))
    refine ⟨hJR, ?_, ?_, ?_⟩
    · simp only [vcost, dcost, vcostL_renameHead, hFlen]
      omega
    · rw [(joined_facts (b := b) (G := G) (H := H) (g := g) (h := 1) (c := cL)
        (es := renameHead 0 J) (F := renameHead 0 (entries J))).2.2.1, hFlen]
      exact hparts.2
    · have hsmallNode : smallLeaf (Cfg.java b G H)
          (.node none g 1 true (renameHead 0 J) (renameHead 0 (entries J))
            (.parts (nParts (Cfg.java b G H).c (renameHead 0 (entries J)).length))) =
          decide ((entries J).length < (Cfg.java b G H).m) := by
        simp only [smallLeaf, VN.changed, VN.size, hFlen]
        rfl
      simp only [innerPotential]
      rw [hoL, hoR]
      simp only [hsmallNode, openEs, Option.getD_some, smallLeaves_rename, decide_eq_true_eq]
      exact hpot

end Contract.PE
