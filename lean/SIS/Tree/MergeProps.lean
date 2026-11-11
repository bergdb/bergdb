/-
The tree model with merges at the delete (bergdb 024-22; the algorithm of
024-11, section 5, as P5 of 023-05 placed it in `Dag.deleteUpward`): the
stated properties of the merges, TP28 to TP35, in 024-12's series. Each is a
definition of type `Prop`; those proved here are proved in full, with nothing
assumed (TP28 for 024-11's thresholds from M = 8, TP34 and TP35). The others
are computed on small cases by `treetest` (with `merge`), and on Java's traces
by `treecheck` through the invariants' walk. Trusted part: the statements.

024-11's other invariants and theorems are statements of 024-12 already, which
take the parameters, so with `Params.withMerges` they speak of the merged tree
(024-22, section 2.7): V2 to V5 are in `walk` (TP6), V6, V7 and V9 are TP14,
TP16 and TP19, V8 is TP4, TH1 is TP10 and TP11, I2 of 024-07 is TP27.
-/
import SIS.Tree.Bound

namespace SIS.Tree

open SIS SIS.Check

/-! ## TP28: the thresholds -/

/-- TP28. What the thresholds must meet for V1 (024-22, section 2.1): merges on,
m >= 2; a merge into two nodes (more than c live klongs) gives each at least m
(so one node of 2m - 1 or more is possible too); a space split (a last version
of more than h klongs) gives each half at least m; a merged node and a time
split's last version leave room for the klongs a change adds, c and h at most M
- 2 (Java's check in 024-14's build); each node of two holds at most ceil((m -
1 + M - 1) / 2) live klongs and a time klong, and fits. -/
def MergeParamsOK (p : Params) : Prop :=
  2 ≤ p.mergeBelow ∧ p.mergeBelow ≤ (p.mergeMax + 1) / 2 ∧
    p.mergeBelow ≤ p.splitAbove / 2 ∧ p.mergeMax + 2 ≤ p.M ∧ p.splitAbove + 2 ≤ p.M ∧
    (p.mergeBelow + p.M - 1) / 2 + 1 ≤ p.M

/-- Record format 7's thresholds (`withMerges`: m = max(2, 8 M / 30), h = c =
17 M / 30) meet TP28 for every node size from 8. -/
theorem mergeParamsOK_withMerges (p : Params) (h : 8 ≤ p.M) : MergeParamsOK p.withMerges := by
  simp only [MergeParamsOK, Params.withMerges, show ¬ p.M < 8 from by omega, ↓reduceIte]
  rcases Nat.le_total 2 (8 * p.M / 30) with hm | hm
  · rw [Nat.max_eq_right hm]; omega
  · rw [Nat.max_eq_left hm]; omega

/-- And 024-11's earlier set, m = max(2, M / 4), h = c = M / 2 (P5's, the
model's from 11:44 to 14:34), meets it from 8 too. -/
theorem mergeParamsOK_p5 (p : Params) (h : 8 ≤ p.M) :
    MergeParamsOK { p with mergeBelow := max 2 (p.M / 4), mergeMax := p.M / 2,
                           splitAbove := p.M / 2 } := by
  simp only [MergeParamsOK]
  rcases Nat.le_total 2 (p.M / 4) with hm | hm
  · rw [Nat.max_eq_right hm]; omega
  · rw [Nat.max_eq_left hm]; omega

/-- 024-11's formulas do not meet TP28 at node size 6: m = max(2, 1) = 2, and a
space split of three live klongs leaves a half of one. (So `withMerges`, as
Java's `Dag.minFill`, sets m = 1 there: no merge.) -/
theorem not_mergeParamsOK_six (g h : Nat) :
    ¬ MergeParamsOK ({ M := 6, G := g, H := h, mergeBelow := 2, mergeMax := 3,
                       splitAbove := 3 } : Params) := by
  simp [MergeParamsOK]

/-- Nor at node size 4: m = 2 and c = 2, so two nodes of a merge hold 2 and 1. -/
theorem not_mergeParamsOK_four (g h : Nat) :
    ¬ MergeParamsOK ({ M := 4, G := g, H := h, mergeBelow := 2, mergeMax := 2,
                       splitAbove := 2 } : Params) := by
  simp [MergeParamsOK]

/-! ## TP29 to TP31: the fill, the invariants, the count (V1, TH2, TH3) -/

/-- The key nodes reachable at time t from x, each with whether it is the root
of its segment tree, in the walk's order. -/
def nodesRoots (p : Params) (view : View BVal) (t : Time) :
    Nat → NodeId → Bool → List (NodeId × Bool)
  | 0, _, _ => []
  | f + 1, x, isRoot =>
    match knodeOf p view x with
    | none => []
    | some n =>
      (x, isRoot) :: (n.liveAt t).flatMap (fun (c, y) =>
        if n.leaf then (if segLen c != 7 then [] else nodesRoots p view t f y true)
        else nodesRoots p view t f y false)

/-- The key nodes reachable at time t, with whether each is a segment root. -/
def nodesRootsAt (p : Params) (P : Struct BVal) (t : Time) : List (NodeId × Bool) :=
  match rootAt (viewOf P) t with
  | some r => nodesRoots p (viewOf P) t p.fuel r true
  | none => []

/-- TP29, V1 of 024-11 (BU1 (a)): with merges on, at time t every reachable key
node that is not the root of its segment tree has at least m live klongs.
`walk` checks it (`FillOK`), so it is part of `InvOK` (TP6) with merges on. -/
def FillOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  p.merges = true → ∀ q ∈ nodesRootsAt p P t, q.2 = false →
    ∀ n, keyNodeAt p P q.1 = some n → p.mergeBelow ≤ (n.liveAt t).length

/-- TP30, TH2 of 024-11: with thresholds that meet TP28, a run within reach
keeps the tree's invariants at every time, V1 among them: TP7 for the merged
tree. -/
def MergeInvPreserved (p : Params) : Prop :=
  MergeParamsOK p → ∀ ts, Within p ts → ∀ t ≤ ts.length,
    InvOK p (treeRun p ts) t ∧ FillOK p (treeRun p ts) t ∧ PointersOK (treeRun p ts)

/-- The number of segment trees of a set of live keys: the space root's, and
one for each prefix of one or more long segments of a key longer than it. -/
def segTrees (kvs : List (Key × Nat)) : Nat :=
  1 + ((kvs.flatMap (fun q => (List.range (q.1.length - 1)).map (fun j => q.1.take (j + 1)))).eraseDups).length

/-- TP31, TH3 of 024-11 (BU1's count): with merges on and thresholds that meet
TP28, at every time the reachable key nodes are at most S + (n + S - 1) / (m - 1)
for n live keys in S segment trees: a function of the live keys alone. It
follows from V1, V2 and V4 (a segment tree with e live klongs in its leaves has
at most 1 + e / (m - 1) nodes). -/
def NodeCountBound (p : Params) : Prop :=
  MergeParamsOK p → ∀ ts, Within p ts → ∀ t ≤ ts.length,
    (keyNodesAt p (treeRun p ts) t).length ≤
      segTrees (refKvs ts t) + ((refKvs ts t).length + segTrees (refKvs ts t) - 1) / (p.mergeBelow - 1)

/-! ## TP32, TP33: the costs (CB1, CB3) -/

/-- The writer's run of a transaction at time i from P@(i-1): for each operation
whether it was a noop, and the writer's state at its end. -/
def execW (p : Params) (tx : Tx) (i : Time) (view : View BVal) : Except String (List Bool × W) :=
  runOps p tx.base tx.ops i view

/-- The deletes of a transaction that deleted (not noops). -/
def deletesOf (tx : Tx) (noops : List Bool) : Nat :=
  (tx.ops.zip noops).countP (fun (q : Op × Bool) => match q.1 with
    | .del _ => !q.2
    | .put _ _ => false)

/-- TP32, CB1 of 024-11: a delete merges at most once a level of its segment
tree below the root, so a transaction's merges are at most its deletes times
H + 1. -/
def MergeOpBound (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (tx : Tx) noops w,
    execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w) →
    w.merges ≤ deletesOf tx noops * (p.H + 1)

/-- The merges, the deletes that deleted and the space splits of each
transaction of a run. -/
def runCosts (p : Params) (ts : List Tx) : List (Nat × Nat × Nat) :=
  ts.zipIdx.filterMap (fun (q : Tx × Nat) =>
    match execW p q.1 (q.2 + 1) (view (treeSpec p) (treeRun p (ts.take q.2)) q.2) with
    | .ok (noops, w) => some (w.merges, deletesOf q.1 noops, w.spaceSplits)
    | .error _ => none)

/-- TP33, CB3 of 024-11 (amortized): over every run within reach from R(0), the
merges are at most the deletes and twice the space splits. Its argument: give a
node that is not a root max(0, m + 1 - cnt) units; a delete adds at most one, a
space split at most two; a merge takes two at the merged node and adds at most
one. -/
def MergeAmortized (p : Params) : Prop :=
  MergeParamsOK p → ∀ ts, Within p ts →
    ((runCosts p ts).map (fun q : Nat × Nat × Nat => q.1)).foldl (· + ·) 0 ≤
      ((runCosts p ts).map (fun q : Nat × Nat × Nat => q.2.1)).foldl (· + ·) 0 +
        2 * ((runCosts p ts).map (fun q : Nat × Nat × Nat => q.2.2)).foldl (· + ·) 0

/-! ## TP34, TP35: the merge's new nodes (V5; the key set kept) -/

/-- TP34, V5 for a merge (024-11, M3): of n live klongs, one node holds all,
when n is at most c; else two hold ceil(n / 2) and the rest. -/
def MergeSizeOK : Prop :=
  ∀ (inner : Bool) (cap cR : Nat) (lvL lvR : List (Nat × NodeId)),
    let n := lvL.length + lvR.length
    let r := mergeKlongs inner cap cR lvL lvR
    (n ≤ cap → r.1.length = n ∧ r.2 = none) ∧
    (cap < n → r.1.length = (n + 1) / 2 ∧
      ∃ rest g, r.2 = some (rest, g) ∧ rest.length = n - (n + 1) / 2)

theorem renameHead_length (c : Nat) (l : List (Nat × NodeId)) :
    (renameHead c l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a r => rfl

theorem renameHead_ptrs (c : Nat) (l : List (Nat × NodeId)) :
    (renameHead c l).map (·.2) = l.map (·.2) := by
  cases l with
  | nil => rfl
  | cons a r => rfl

theorem mergeList_length (inner : Bool) (cR : Nat) (lvL lvR : List (Nat × NodeId)) :
    (mergeList inner cR lvL lvR).length = lvL.length + lvR.length := by
  cases inner <;> simp [mergeList, renameHead_length]

theorem mergeList_ptrs (inner : Bool) (cR : Nat) (lvL lvR : List (Nat × NodeId)) :
    (mergeList inner cR lvL lvR).map (·.2) = (lvL ++ lvR).map (·.2) := by
  cases inner <;> simp [mergeList, renameHead_ptrs]

theorem mergeSizeOK : MergeSizeOK := by
  intro inner cap cR lvL lvR
  have hl := mergeList_length inner cR lvL lvR
  simp only [mergeKlongs, splitMerged]
  constructor
  · intro h
    have h' : (mergeList inner cR lvL lvR).length ≤ cap := by omega
    simp only [h', ↓reduceIte]
    exact ⟨hl, trivial⟩
  · intro h
    have h' : ¬ (mergeList inner cR lvL lvR).length ≤ cap := by omega
    simp only [h', ↓reduceIte]
    refine ⟨by simp only [List.length_take, hl]; omega, _, _, rfl, ?_⟩
    cases inner <;> simp [renameHead_length, hl]

/-- TP35. A merge keeps the klongs: the new nodes' pointers are the two nodes'
live pointers, in order; in a segment leaf the klongs themselves (in an inner
node all compare values but the two empty keys': the right node's first gets
its compare value in the parent, and a second node's first is the empty key).
So a merge changes no key's value at tt, and no node below it. -/
def MergeKeepsKlongs : Prop :=
  ∀ (inner : Bool) (cap cR : Nat) (lvL lvR : List (Nat × NodeId)),
    let r := mergeKlongs inner cap cR lvL lvR
    let all := r.1 ++ (r.2.map (·.1)).getD []
    all.map (·.2) = (lvL ++ lvR).map (·.2) ∧ (inner = false → all = lvL ++ lvR)

theorem mergeKeepsKlongs : MergeKeepsKlongs := by
  intro inner cap cR lvL lvR
  simp only [mergeKlongs, splitMerged]
  by_cases h : (mergeList inner cR lvL lvR).length ≤ cap
  · simp only [h, ↓reduceIte]
    refine ⟨by simp [mergeList_ptrs], fun hi => ?_⟩
    subst hi
    simp [mergeList]
  · simp only [h, ↓reduceIte]
    constructor
    · cases inner
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some,
          List.take_append_drop, mergeList_ptrs]
      · simp only [↓reduceIte, Option.map_some, Option.getD_some, List.map_append,
          renameHead_ptrs]
        rw [← List.map_append, List.take_append_drop, mergeList_ptrs, List.map_append]
    · intro hi
      subst hi
      simp [mergeList]

/-- TP36, V1 and V5 at a merge (the local part of 024-11's "why V1 holds"):
with thresholds that meet TP28, a merge of nodes whose live klongs number at
least m (x has m - 1, its sibling m or more) and at most m - 1 + M - 1 (a
sibling holds at most M - 1) makes nodes that each hold at least m live klongs
and fit in a node with their time klong. -/
def MergeFillOK : Prop :=
  ∀ (p : Params) (inner : Bool) (cR : Nat) (lvL lvR : List (Nat × NodeId)),
    MergeParamsOK p → p.mergeBelow ≤ lvL.length + lvR.length →
    lvL.length + lvR.length ≤ p.mergeBelow - 1 + (p.M - 1) →
    let r := mergeKlongs inner p.mergeMax cR lvL lvR
    p.mergeBelow ≤ r.1.length ∧ r.1.length + 1 ≤ p.M ∧
      ∀ rest g, r.2 = some (rest, g) → p.mergeBelow ≤ rest.length ∧ rest.length + 1 ≤ p.M

theorem mergeFillOK : MergeFillOK := by
  intro p inner cR lvL lvR hp hlo hhi
  dsimp only
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  have hs0 := mergeSizeOK inner p.mergeMax cR lvL lvR
  dsimp only at hs0
  obtain ⟨hone, htwo⟩ := hs0
  by_cases hc : lvL.length + lvR.length ≤ p.mergeMax
  · obtain ⟨hl, hr⟩ := hone hc
    refine ⟨by omega, by omega, fun rest g hs => ?_⟩
    rw [hr] at hs
    exact absurd hs (by simp)
  · obtain ⟨hl, rest', g', hs', hlen⟩ := htwo (by omega)
    refine ⟨by omega, by omega, fun rest g hs => ?_⟩
    rw [hs'] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    omega

/-- TP37, V1 at a space split (the other half of 024-11's "why V1 holds"): with
thresholds that meet TP28, the two halves of a last version of more than h
klongs (rule O's space split, `halves`) each hold at least m key klongs besides
their time klong. (A last version's key klongs are its live klongs, one a
compare value.) -/
def SplitFillOK : Prop :=
  ∀ (p : Params) (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)),
    MergeParamsOK p → p.splitAbove < last.size →
    p.mergeBelow + 1 ≤ (halves leaf t last ins).1.size ∧
      p.mergeBelow + 1 ≤ (halves leaf t last ins).2.1.size

/-- A bound on a function of either branch of an `if` bounds it of the `if`. -/
theorem ite_len {α : Type} {b : Prop} {d : Decidable b} {x y : α} (f : α → Nat) {k : Nat}
    (hx : k ≤ f x) (hy : k ≤ f y) : k ≤ f (@ite α b d x y) := by
  cases d <;> assumption

theorem splitFillOK : SplitFillOK := by
  intro p leaf t last ins hp h
  obtain ⟨_, _, h3, _, _, _⟩ := hp
  simp only [KNode.size] at h
  have hb : (last.ks.drop 1).length = last.ks.length - 1 := by simp
  constructor
  · simp only [halves, KNode.size]
    apply ite_len (f := fun q : KNode × KNode × Nat => q.1.ks.length)
    · simp only [List.length_cons, List.length_take, hb]; omega
    · simp only [List.length_cons, List.length_append, List.length_take, List.length_map, hb]
      omega
  · simp only [halves, KNode.size]
    apply ite_len (f := fun q : KNode × KNode × Nat => q.2.1.ks.length)
    · cases leaf
      · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_append,
          List.length_map]
        split
        · rename_i heq
          have hl := congrArg List.length heq
          simp only [List.length_drop, List.length_cons, hb] at hl
          simp only [List.length_cons]
          omega
        · simp only [List.length_drop, hb]
          omega
      · simp only [↓reduceIte, List.length_cons, List.length_append, List.length_drop,
          List.length_map, hb]
        omega
    · cases leaf
      · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
        split
        · rename_i heq
          have hl := congrArg List.length heq
          simp only [List.length_drop, List.length_cons, hb] at hl
          simp only [List.length_cons]
          omega
        · simp only [List.length_drop, hb]
          omega
      · simp only [↓reduceIte, List.length_cons, List.length_drop, hb]
        omega

/-- Compare values strictly increasing along a list of live klongs. -/
abbrev CvSorted (l : List (Nat × NodeId)) : Prop := l.Pairwise (fun a b => a.1 < b.1)

/-- TP38, the order of a merge's nodes (V3 at a merge): when the two nodes'
live klongs are in compare order, the left node's below cR, the right node's
compare value in the parent, and the right node's at or above it (its first, in
an inner node the empty key, standing for cR), the merge's first node is in
compare order; and if it makes two, every compare value of the first is below
g, the second's compare value in the parent, and the second is in order too
(in an inner node with its first klong the empty key). -/
def MergeOrderOK : Prop :=
  ∀ (inner : Bool) (cap cR : Nat) (lvL lvR : List (Nat × NodeId)),
    1 ≤ cap → CvSorted lvL → CvSorted lvR → (∀ q ∈ lvL, q.1 < cR) →
    (∀ q ∈ lvR.tail, cR < q.1) → (inner = false → ∀ q ∈ lvR, cR ≤ q.1) →
    let r := mergeKlongs inner cap cR lvL lvR
    CvSorted r.1 ∧ ∀ rest g, r.2 = some (rest, g) → (∀ q ∈ r.1, q.1 < g) ∧ CvSorted rest

theorem renameHead_sorted (c : Nat) (l : List (Nat × NodeId)) (hl : CvSorted l)
    (hc : ∀ q ∈ l.tail, c < q.1) : CvSorted (renameHead c l) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a r =>
    simp only [renameHead, CvSorted, List.pairwise_cons] at hl ⊢
    exact ⟨fun b hb => hc b hb, hl.2⟩

theorem mem_renameHead (c : Nat) (l : List (Nat × NodeId)) (q : Nat × NodeId)
    (hq : q ∈ renameHead c l) : q.1 = c ∨ q ∈ l.tail := by
  cases l with
  | nil => simp [renameHead] at hq
  | cons a r =>
    simp only [renameHead, List.mem_cons] at hq
    rcases hq with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h

theorem mergeList_sorted (inner : Bool) (cR : Nat) (lvL lvR : List (Nat × NodeId))
    (hL : CvSorted lvL) (hR : CvSorted lvR) (hLc : ∀ q ∈ lvL, q.1 < cR)
    (hRt : ∀ q ∈ lvR.tail, cR < q.1) (hRl : inner = false → ∀ q ∈ lvR, cR ≤ q.1) :
    CvSorted (mergeList inner cR lvL lvR) := by
  simp only [mergeList, CvSorted, List.pairwise_append]
  cases inner with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨hL, hR, fun a ha b hb => Nat.lt_of_lt_of_le (hLc a ha) (hRl rfl b hb)⟩
  | true =>
    simp only [↓reduceIte]
    refine ⟨hL, renameHead_sorted cR lvR hR hRt, fun a ha b hb => ?_⟩
    rcases mem_renameHead cR lvR b hb with h | h
    · rw [h]; exact hLc a ha
    · exact Nat.lt_trans (hLc a ha) (hRt b h)

theorem mergeOrderOK : MergeOrderOK := by
  intro inner cap cR lvL lvR hcap hL hR hLc hRt hRl
  have he := mergeList_sorted inner cR lvL lvR hL hR hLc hRt hRl
  simp only [mergeKlongs, splitMerged]
  generalize hE : mergeList inner cR lvL lvR = e at he
  by_cases h : e.length ≤ cap
  · simp only [h, ↓reduceIte]
    refine ⟨he, fun rest g hs => ?_⟩
    simp at hs
  · simp only [h, ↓reduceIte]
    have hsplit := he
    rw [← List.take_append_drop ((e.length + 1) / 2) e] at hsplit
    simp only [CvSorted, List.pairwise_append] at hsplit
    obtain ⟨htake, hdrop, hcross⟩ := hsplit
    refine ⟨htake, fun rest g hs => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hrest, hg⟩ := hs
    -- the rest is not empty: e has more than cap >= 1 klongs
    have hne : e.drop ((e.length + 1) / 2) ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      simp only [List.length_drop, List.length_nil] at this
      omega
    obtain ⟨b, tl, hbt⟩ := List.exists_cons_of_ne_nil hne
    have hgb : g = b.1 := by
      rw [← hg, hbt]; rfl
    have hfirst : ∀ q ∈ e.take ((e.length + 1) / 2), q.1 < g := by
      intro q hq
      rw [hgb]
      exact hcross q hq b (by rw [hbt]; exact List.mem_cons_self)
    refine ⟨hfirst, ?_⟩
    rw [← hrest]
    have hdrop' : CvSorted (e.drop ((e.length + 1) / 2)) := hdrop
    cases inner with
    | false => simpa using hdrop'
    | true =>
      simp only [↓reduceIte]
      apply renameHead_sorted 0 _ hdrop'
      intro q hq
      rw [hbt] at hq hdrop'
      simp only [List.tail_cons] at hq
      have h1 : b.1 < q.1 := by
        simp only [CvSorted, List.pairwise_cons] at hdrop'
        exact hdrop'.1 q hq
      omega

end SIS.Tree
