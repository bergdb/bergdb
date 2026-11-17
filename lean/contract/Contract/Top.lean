/-
The contract package (bergdb 030-08): the top of the tree as Java has it, the
top nodes with their skip pointers (`TopNode`, `TopDs`), and the readers that
start from Java's search through them (`TopDs.findSuperRootAtTime`). To read
and to trust, with Tree.lean and Read.lean. Everything here runs; nothing
needs Mathlib.

Until 030-08 the contract's tree had only its space roots, each with its time
(`Tree.roots`), and a reader at time t started from the last one at or before
t: "one root per time", 030-06, section 7. Java's reader does not have that
list. It has the super root, the newest top node, and searches back from it
through the skip pointers. Here the top nodes are in the contract's state,
the search is Java's, and the theorems on reads speak of readers that use it
(TheoremsTop.lean).

Times are the model's, the records' indexes (bergdb 027-02). Java's reader
looks up at a clock time: at a record's own time, or between two records.
Between records t and t + 1 the model calls the time t, and the search is
asked with `mid` true ("t and a half"): a root time is then at or after the
lookup time only if it is after t, and no root time is equal to it.
-/
import Contract.Reach

namespace Contract

/-- A top node (`TopNode`): its root time (`rootTime`, the time of the
transaction that made it), its root pointer (the space root it names), and
its skip pointers, the slots of `pointers` that are set, in the order of
their index, each as its index j, the top node it names and the time cached
with it (`pointersTime[j]`, which a search reads without following the
pointer). -/
structure TopNode where
  time : Time
  root : NodeId
  skips : List (Nat × NodeId × Time)
  deriving DecidableEq, Repr, Inhabited

/-- The top: the top nodes with their ids, in the order they were made. The
last one is the super root (`TopDs.superRoot`), the only one that Java's
reader holds; it reaches the others through skip pointers. The list is the
model's root and its entries (bergdb 027-02, section 2: `ADD 0 i T z`). -/
abbrev Top := List (NodeId × TopNode)

/-- The top node with id z (Java follows a pointer to it). -/
def Top.node (tp : Top) (z : NodeId) : Option TopNode := tp.lookup z

/-! ## Java's search -/

/-- A root time x is at or after the lookup time: t, or t and a half. -/
def atOrAfter (x t : Time) (mid : Bool) : Bool := if mid then decide (t < x) else decide (t ≤ x)

/-- `TopDs.rightMostGte`: the skip pointer with the highest index whose cached
time is at or after the lookup time; the top node it names. -/
def rightMostGte (n : TopNode) (t : Time) (mid : Bool) : Option NodeId :=
  (n.skips.reverse.find? (fun q => atOrAfter q.2.2 t mid)).map (·.2.1)

/-- The first loop of `TopDs.findSuperRootAtTime`: from top node z, along the
highest skip pointers that stay at or after the lookup time, as long as there
is one. The fuel bounds the steps; Java's loop ends because a skip pointer
names an older top node (`TopDs.skipTo`). -/
def skipDown (tp : Top) (t : Time) (mid : Bool) : Nat → NodeId → NodeId
  | 0, z => z
  | f + 1, z =>
    match tp.node z with
    | some n =>
      match rightMostGte n t mid with
      | some y => skipDown tp t mid f y
      | none => z
    | none => z

/-- `TopDs.findSuperRootAtTime`: the top node that was the super root at the
lookup time, none if there is none old enough. The super root if its root
time is at or before the lookup time; else down the skip pointers, and then
the node reached if its root time is the lookup time, or else the target of
its lowest skip pointer (`TopDs.leftMost`) if that one's cached time is at or
before the lookup time. -/
def findTop (tp : Top) (t : Time) (mid : Bool) : Option NodeId :=
  match tp.getLast? with
  | none => none
  | some (w, nw) =>
    if nw.time ≤ t then some w
    else
      let z := skipDown tp t mid tp.length w
      match tp.node z with
      | none => none
      | some n =>
        if !mid && n.time == t then some z
        else
          match n.skips.head? with
          | some (_, y, ty) => if ty ≤ t then some y else none
          | none => none

/-- `TopDs.findRoot`: the space root that Java's reader at the lookup time
starts from, the root pointer of the top node found. -/
def findRoot (tp : Top) (t : Time) (mid : Bool) : Option NodeId :=
  match findTop tp t mid with
  | some z => (tp.node z).map (·.root)
  | none => none

/-! ## The readers, from Java's search -/

/-- `Dag.getOne` at time t (`mid`: between the records t and t + 1): from the
space root that the search finds, the get of Read.lean on the tree at t. -/
def jget (s : Tree) (tp : Top) (t : Time) (mid : Bool) (key : Key) : Option Nat :=
  match findRoot tp t mid with
  | some r => getGo (s.at t) ((s.at t).fuel r) key r
  | none => none

/-- `Dag.getMany` at time t with `GetN(limit)`: from the space root that the
search finds, the scan of Read.lean on the tree at t. -/
def jscan (s : Tree) (tp : Top) (t : Time) (mid : Bool) (req : ScanReq) (limit : Nat) :
    List (Key × Nat) :=
  match findRoot tp t mid with
  | some r =>
    scanGo (s.at t) req (2 * (s.at t).fuel r + 2) limit (chainSetup (s.at t) req ((s.at t).fuel r) r)
  | none => []

/-! ## What the search should find -/

/-- The space roots of the top, each with its time: the root pointers of the
top nodes, in order. The contract's tree has these (`Tree.roots`). -/
def rootsOf (tp : Top) : List (Time × NodeId) := tp.map (fun zn => (zn.2.time, zn.2.root))

/-- The top node of time t: the last one made at or before t. -/
def topAt (tp : Top) (t : Time) : Option (NodeId × TopNode) :=
  (tp.filter (fun zn => decide (zn.2.time ≤ t))).getLast?

/-! ## The top's clauses of the contract

English. The top of the transaction at time i, from the top before it to the
top after it (`TopStep`):

* T1. Either no top node is made, or one: it is added at the end, and becomes
  the super root. Every top node before it stays as it was, with its root
  pointer and its skip pointers (R3 of the abstract model: a top node gets
  entries only in the transaction that makes it), and the root gets the
  entry for the new top node and no other (R2). At most one new space root a
  transaction: `TopDs.newSuperRoot` updates the transaction's own top node in
  place when a transaction makes a second space root.
* T2. The new top node's id is not one of a top node before it; its root
  time is i.
* T3. Its skip pointers (`skipsOk`): in increasing order of their index;
  each names a top node before it, and caches that node's root time; the
  first names the super root before it. `TopDs.newSuperRoot` gives this:
  each skip pointer is the super root's at the same index, or names the super
  root, and the lowest one names it.

The start (`TopStart`): one top node, of time 0, with no skip pointer.

The space roots of the contract's tree are the top nodes' root pointers
(`Tree.roots = rootsOf tp`, in `MeetsTop`, ShapeStatement.lean).

Not here, because no reader needs them: the ordinals and which indexes the
skip pointers have (one for each bit set in the ordinal, `TopNode.height`),
which make the search take about log n steps; like the fill, a cost
property. -/

/-- T3: the skip pointers of a top node made after the top tp. -/
def skipsOk (tp : Top) (n : TopNode) : Bool :=
  strictUp (n.skips.map (·.1)) &&
  n.skips.all (fun q => (tp.node q.2.1).map (·.time) == some q.2.2) &&
  (match tp.getLast?, n.skips.head? with
   | some (w, _), some (_, y, _) => y == w
   | none, none => true
   | _, _ => false)

/-- T1 to T3: the top of the transaction at time i, from tp to tp'. -/
def TopStep (i : Time) (tp tp' : Top) : Prop :=
  tp' = tp ∨ ∃ z n, tp' = tp ++ [(z, n)] ∧ tp.node z = none ∧ n.time = i ∧ skipsOk tp n = true

/-- The top of the start tree. -/
def TopStart (tp : Top) : Prop := ∃ z n, tp = [(z, n)] ∧ n.time = 0 ∧ n.skips = []

/-! ## The clauses, computed -/

/-- `TopStep`, computed. -/
def topStepB (i : Time) (tp tp' : Top) : Bool :=
  tp' == tp ||
  match tp'.getLast? with
  | some (z, n) => tp'.dropLast == tp && (tp.node z).isNone && n.time == i && skipsOk tp n
  | none => false

/-- `TopStart`, computed. -/
def topStartB (tp : Top) : Bool :=
  match tp with
  | [(_, n)] => n.time == 0 && n.skips.isEmpty
  | _ => false

theorem dropLast_append_of_getLast? {α : Type} :
    ∀ {l : List α} {a : α}, l.getLast? = some a → l.dropLast ++ [a] = l
  | [], _, h => by simp at h
  | [b], a, h => by simp at h; simp [h]
  | b :: c :: r, a, h => by
    have h' : (c :: r).getLast? = some a := by
      rw [List.getLast?_cons_cons] at h
      exact h
    rw [List.dropLast_cons_cons, List.cons_append, dropLast_append_of_getLast? h']

theorem topStepB_sound (i : Time) (tp tp' : Top) (h : topStepB i tp tp' = true) :
    TopStep i tp tp' := by
  unfold topStepB at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : tp'.getLast? with
    | none => simp [hl] at h
    | some zn =>
      obtain ⟨z, n⟩ := zn
      simp only [hl, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨z, n, ?_, h2, h3, h4⟩
      rw [← dropLast_append_of_getLast? hl, h1]

theorem topStartB_sound (tp : Top) (h : topStartB tp = true) : TopStart tp := by
  match tp, h with
  | [(z, n)], h =>
    simp only [topStartB, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    exact ⟨z, n, rfl, h.1, h.2⟩

end Contract
