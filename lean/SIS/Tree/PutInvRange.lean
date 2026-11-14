import SIS.Tree.PutInvDel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The order part of `PutInv` and the merges (bergdb 024-12, TP10).

`PutInv`'s order is local: below a reachable inner node q, a leaf child's
compare values lie between q's klong to it and q's next klong (`LeafOrderAt`).
The put rules keep it (`PutInvRoom.lean` to `PutInvNewSeg.lean`). A merge of two
inner nodes does not keep it from `PutInv` alone: the right node's first klong,
the empty key to its child X, gets the right node's compare value cR in the
parent (`mergeList`), and X's compare values must then be at least cR. That is
true of every state a run reaches (TP7's walk gives each node of the tree its
range), but nothing in `PutInv` bounds X's compare values from below by cR:
`LeafOrderAt` of the right node and X says only 0 ≤ c. `leafOrder_not_kept`
(below, `#guard`) shows the merged list on such nodes.

The weakest invariant that works is the walk's ranges themselves
(`RangeOrder`: every node reached from the space root, with the range that
its path gives it, has its live compare values in that range, as TP7's
`RangeOK`). It holds at a transaction's first state (`rangeOrder_init`, from
`InvOK`) and gives `PutInv`'s order (`leafOrder_of_rangeOrder`). -/

/-! ## The merge: an example -/

/-- `LeafOrderAt` on lists, decidable: the leaf child's compare values `cs`
under the parent's klong k1, the parent's live compare values `ps`. -/
def leafOrderList (ps : List Nat) (k1 : Nat) (cs : List Nat) : Bool :=
  cs.all (fun c' => decide (k1 ≤ c') && ps.all (fun c'' => !decide (k1 < c'') || decide (c' < c'')))

-- Parent p: klongs 0 to the left node l and 100 to the right node r. r has the
-- empty key to the leaf X and 150 to Y; X holds the compare value 50, below r's
-- bound 100 (a state that `PutInv` allows, no run reaches). Before the merge,
-- the order at r and X holds; after the merge of l and r into one node, the
-- klong of X is 100 and the order at X fails.
#guard leafOrderList [0, 150] 0 [50] = true
#guard (mergeList true 100 [(0, 1)] [(0, 2), (150, 3)]) = [(0, 1), (100, 2), (150, 3)]
#guard leafOrderList ((mergeList true 100 [(0, 1)] [(0, 2), (150, 3)]).map (·.1)) 100 [50] = false

/-! ## The ranges of the tree -/

/-- The nodes reached from r at time t, each with the range of compare values
that its path gives it: from an inner node by a live klong c, from c (the
empty key: the node's own low bound) to the next live klong (the node's own
high bound after the last); from a segment leaf, a new segment tree. -/
inductive ReachR (N : NodeId → Option KNode) (t : Time) (r : NodeId) :
    NodeId → Nat → Option Nat → Prop
  | root : ReachR N t r r 0 none
  | inner (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat) (c : Nat) (y : NodeId)
      (b : Option Nat) : ReachR N t r x lo hi → N x = some n → n.leaf = false →
      ((c, y), b) ∈ childBounds (n.liveAt t) hi → ReachR N t r y (if c == 0 then lo else c) b
  | seg (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat) (c : Nat) (y : NodeId) :
      ReachR N t r x lo hi → N x = some n → n.leaf = true → (c, y) ∈ n.liveAt t →
      ReachR N t r y 0 none

/-- The search tree's order, everywhere: every node reached has its live
compare values in the range its path gives it (TP7's `RangeOK`). -/
def RangeOrder (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  ∀ x lo hi n, ReachR N t r x lo hi → N x = some n → NodeRange n t lo hi

theorem reachR_of_reachS (N : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (h : ReachS N t r x) : ∃ lo hi, ReachR N t r x lo hi := by
  induction h with
  | root => exact ⟨0, none, ReachR.root⟩
  | step x n c z _ hn hc ih =>
    obtain ⟨lo, hi, hx⟩ := ih
    cases hl : n.leaf with
    | true => exact ⟨0, none, ReachR.seg x n lo hi c z hx hn hl hc⟩
    | false =>
      obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (c, z) hc
      exact ⟨_, _, ReachR.inner x n lo hi c z b hx hn hl hb⟩

/-- The ranges give `PutInv`'s order at the leaves. -/
theorem leafOrder_of_rangeOrder (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N t r)
    (htimes : ∀ x n, N x = some n → ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ q qn L n k1, ReachS N t r q → N q = some qn → qn.leaf = false → N L = some n →
      n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n := by
  intro q qn L n k1 hq hqn hql hn hnl hk
  obtain ⟨lo, hi, hqr⟩ := reachR_of_reachS N t r q hq
  have hqt := htimes q qn hqn
  have hnt := htimes L n hn
  have hk' : (k1, L) ∈ qn.liveAt t := by rw [KNode.liveAt_of_times qn t hqt]; exact hk
  obtain ⟨b, hb⟩ := childBounds_exists (qn.liveAt t) hi (k1, L) hk'
  have hLr := ReachR.inner q qn lo hi k1 L b hqr hqn hql hb
  have hrange := hR L _ b n hLr hn
  have hsorted := KNode.liveAt_order qn t
  intro c' z hz
  have hz' : (c', z) ∈ n.liveAt t := by rw [KNode.liveAt_of_times n t hnt]; exact hz
  obtain ⟨hlow, hhigh⟩ := hrange (c', z) hz'
  simp only [hnl, ↓reduceIte] at hlow
  refine ⟨?_, ?_⟩
  · by_cases h0 : k1 = 0
    · omega
    · have : (k1 == 0) = false := by simpa using h0
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hlow
      exact hlow
  · intro c'' z' hz'' hlt
    have hz''' : (c'', z') ∈ qn.liveAt t := by rw [KNode.liveAt_of_times qn t hqt]; exact hz''
    obtain ⟨upper, hub, hle⟩ := childBounds_next_le (qn.liveAt t) hi hsorted (k1, L) b hb
      (c'', z') hz''' hlt
    rw [hub] at hhigh
    simp only [UpperBound] at hhigh
    simp only at hle
    omega

/-- Every node reached with a range from P's space root at t + 1 (P without
entries after t) has a walk without faults with that range. -/
theorem walk_of_reachR (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (r : NodeId) (hr : rootAt (viewOf P) t = some r) (hI : InvOK p P t) :
    ∀ x lo hi, ReachR (knodeOf p (viewOf P)) (t + 1) r x lo hi →
      ∀ m, knodeOf p (viewOf P) x = some m →
        ∃ f isRoot space, walk p (viewOf P) t (f + 1) x lo hi isRoot space = [] := by
  intro x lo hi hx
  induction hx with
  | root =>
    intro m _
    unfold InvOK faultsAt at hI
    rw [hr] at hI
    simp only at hI
    have hf : p.fuel = (p.G + 1) * (p.H + 2) + 1 + 1 := by unfold Params.fuel; omega
    rw [hf] at hI
    exact ⟨_, true, true, hI⟩
  | inner x n lo hi c y b _ hn hl hb ih =>
    intro m hm
    obtain ⟨f, isRoot, space, hw⟩ := ih n hn
    rw [liveAt_succ_of_timesLE p P t hP x n hn] at hb
    have h := walk_child p P t f x lo hi isRoot space n hn hw (c, y) b hb m hm
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨f', hf'⟩ := walk_succ_of_nil p _ t f _ _ _ _ _ h
    subst hf'
    exact ⟨f', _, _, h⟩
  | seg x n lo hi c y _ hn hl hc ih =>
    intro m hm
    obtain ⟨f, isRoot, space, hw⟩ := ih n hn
    rw [liveAt_succ_of_timesLE p P t hP x n hn] at hc
    obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (c, y) hc
    have h := walk_child p P t f x lo hi isRoot space n hn hw (c, y) b hb m hm
    simp only [hl, ↓reduceIte] at h
    obtain ⟨f', hf'⟩ := walk_succ_of_nil p _ t f _ _ _ _ _ h
    subst hf'
    exact ⟨f', _, _, h⟩

/-- `RangeOrder` at a transaction's first state, from TP7's invariant at the
time before. -/
theorem rangeOrder_init (p : Params) (ts : List Tx) (tx : Tx) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    RangeOrder (wNode p (viewOf (treeRun p ts)) (wInit tx top)) (ts.length + 1)
      (wInit tx top).top.rootKey := by
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  have hroot := rootAt_of_writerTop p ts z top hz htop
  have hP := treeRun_timesLE p ts
  rw [hlook]
  intro x lo hi n hx hn
  obtain ⟨f, isRoot, space, hw⟩ := walk_of_reachR p (treeRun p ts) ts.length hP top.rootKey hroot
    hI x lo hi hx n hn
  obtain ⟨nd, hg, hd, _, hnd⟩ := knodeOf_viewOf p _ x n hn
  have hrange := walk_current_range p (viewOf (treeRun p ts)) ts.length f x lo hi isRoot space nd
    hg hd hw
  rw [← hnd] at hrange
  intro q hq
  rw [liveAt_succ_of_timesLE p _ ts.length hP x n hn] at hq
  exact hrange q hq

end SIS.Tree
