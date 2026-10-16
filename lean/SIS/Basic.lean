/-
Self-indexed streams in Lean: the structure P.

Section numbers refer to theory/sis-model.md. This file is part of the
trusted part: the definitions that the theorems are about.
-/

namespace SIS

/-- Node ids are natural numbers. The entry node, root, has id 0 (3.3). -/
notation "NodeId" => Nat

/-- Time is a natural number: time i means just after transaction T(i) (2). -/
notation "Time" => Nat

/-- The id of the entry node (3.3). -/
def root : NodeId := 0

/-- An entry of a node's history: a value added at a time (3.1). -/
structure Entry (V : Type) where
  time : Time
  val : V
  deriving DecidableEq, Repr

/-- A node's history: its entries, in the order they were added (3.1). -/
abbrev History (V : Type) := List (Entry V)

/-- x@t: the entries with a time <= t (3.1). -/
def History.upTo {V : Type} (h : History V) (t : Time) : History V :=
  h.filter (fun e => decide (e.time ≤ t))

/-- A node of P: its level (A4), whether it is a data node (3.2), and its
history (3.1). -/
structure Node (V : Type) where
  level : Nat
  isData : Bool
  hist : History V
  deriving DecidableEq, Repr

/-- The structure P: the nodes that exist, by id. -/
abbrev Struct (V : Type) := List (NodeId × Node V)

/-- The node with id x, if it exists. -/
def Struct.get? {V : Type} (P : Struct V) (x : NodeId) : Option (Node V) :=
  List.lookup x P

/-- A node created by a transaction (3.1). New nodes start with an empty
history; their entries come with the transaction's other entries. -/
structure NewNode where
  id : NodeId
  level : Nat
  isData : Bool
  deriving DecidableEq, Repr

/-- What a transaction does to P (A1): the nodes it creates, and the entries
it adds, all at the transaction's time. -/
structure Changes (V : Type) where
  new : List NewNode
  adds : List (NodeId × V)
  deriving Repr

/-- What a transaction may read: P@(i-1), as a function from node id to the
node with its content at that time, or none if the node is not reachable
then (3.3, A1). -/
abbrev View (V : Type) := NodeId → Option (Node V)

/-- What self-indexed streams need to know about the structure. Everything
specific to BergDB (klongs, key nodes, TopDs) is hidden in these four
functions and the types V (entry values) and T (transactions). -/
structure Spec (V T : Type) where
  /-- The node ids an entry value points to, live or dead (3.1). -/
  ptrs : V → List NodeId
  /-- children(x, t): the live pointers of a node with content x@t (3.1). -/
  live : History V → List NodeId
  /-- A1: the changes made by transaction T(i) at time i, as a function of
  T(i), i and P@(i-1) only. New ids must be made from i (and a counter). -/
  exec : T → Time → View V → Changes V
  /-- The initial structure, made by T(0). Its entries have time 0. -/
  init : Struct V
  /-- Option (a) of Q7: the root is virtual, as in BergDB, which has no root
  node but a chain of top nodes. The root is never in D and never written;
  startup rebuilds it from its children, the root children. With false, the
  root is an ordinary node. Added 2026-10-16 (F1-008-11, WP E3;
  docs/level2-alignment.md, section 8). -/
  virt : Bool := false
  /-- With `virt`: the root children (BergDB's top nodes) are the nodes other
  than the root on level `topLevel` or above. -/
  topLevel : Nat := 0
  /-- With `virt`: the root's entry value for its child z (BergDB's `top(z)`). -/
  rootVal : NodeId → V

variable {V T : Type}

/-- With `Spec.virt`: x is a root child, a node other than the root on level
`topLevel` or above (BergDB: a top node). -/
def isTop (sp : Spec V T) (P : Struct V) (x : NodeId) : Bool :=
  x != root && match P.get? x with
    | some n => decide (sp.topLevel ≤ n.level)
    | none => false

/-- Add entry values at time i to node x. -/
def Struct.addEntry (P : Struct V) (i : Time) (x : NodeId) (v : V) : Struct V :=
  P.map (fun p => if p.1 = x then (p.1, { p.2 with hist := p.2.hist ++ [⟨i, v⟩] }) else p)

/-- Apply a transaction's changes at time i (6.1, step 1). -/
def Struct.apply (P : Struct V) (i : Time) (c : Changes V) : Struct V :=
  let P := P ++ c.new.map (fun n => (n.id, { level := n.level, isData := n.isData, hist := [] }))
  c.adds.foldl (fun P a => P.addEntry i a.1 a.2) P

/-- The nodes reachable at time t from node x, x included (3.3). A pointer
to a node that is not on a lower level is not followed (A4); this makes the
recursion end, and changes nothing for a structure that has A4. -/
def reachFrom (sp : Spec V T) (P : Struct V) (t : Time) (x : NodeId) (n : Node V) :
    List NodeId :=
  x :: (sp.live (n.hist.upTo t)).flatMap (fun y =>
    match P.get? y with
    | some m => if m.level < n.level then reachFrom sp P t y m else []
    | none => [])
termination_by n.level

/-- The nodes reachable at time t (3.3). -/
def reachList (sp : Spec V T) (P : Struct V) (t : Time) : List NodeId :=
  match P.get? root with
  | some n => reachFrom sp P t root n
  | none => []

/-- x is reachable at time t (3.3). -/
def reachable (sp : Spec V T) (P : Struct V) (t : Time) (x : NodeId) : Bool :=
  (reachList sp P t).contains x

/-- P@t: each node reachable at t, with its content at t (3.3). -/
def view (sp : Spec V T) (P : Struct V) (t : Time) : View V := fun x =>
  if reachable sp P t x then
    (P.get? x).map (fun n => { n with hist := n.hist.upTo t })
  else none

/-- Equivalence, P ≈ P' up to time k: P@t = P'@t for every t <= k (3.3).
Equivalent structures give the same answer to every lookup. -/
def Equiv (sp : Spec V T) (k : Time) (P P' : Struct V) : Prop :=
  ∀ t ≤ k, view sp P t = view sp P' t

end SIS
