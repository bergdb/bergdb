/-
Self-indexed streams in Lean: the assumptions of the theorems, and runs with
restarts.

Section numbers refer to theory/sis-model.md. Trusted part.
-/
import SIS.Startup

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- With a virtual root: the root children that can be reached from root
child x (with node n) through pointers, live or dead, between root children;
x included. -/
def topClosure (sp : Spec V T) (P : Struct V) (x : NodeId) (n : Node V) : List NodeId :=
  x :: (pointees sp n.hist).flatMap (fun y =>
    match P.get? y with
    | some m => if sp.topLevel ≤ m.level ∧ m.level < n.level then topClosure sp P y m else []
    | none => [])
termination_by n.level

/-- The assumptions on the initial structure with a virtual root (option (a)
of Q7; bergdb 011-11, 8.2). BergDB's primordial record has one top
node. Added 2026-10-16 (F1-008-11, WP E3). -/
structure VirtInit (sp : Spec V T) : Prop where
  /-- R1: the root's entry for a child points to that child. -/
  rootPtrs : ∀ z, sp.ptrs (sp.rootVal z) = [z]
  /-- The root is an index node. -/
  rootIndex : ∀ n, sp.init.get? root = some n → n.isData = false
  /-- At most one initial root child; it is an index node with entries. -/
  initTop : ∀ p ∈ sp.init, p.1 ≠ root → sp.topLevel ≤ p.2.level →
    p.2.isData = false ∧ p.2.hist ≠ [] ∧
    ∀ q ∈ sp.init, q.1 ≠ root → sp.topLevel ≤ q.2.level → q.1 = p.1
  /-- R2: the root's initial history is the entry for the initial root child,
  if there is one. -/
  initRootHist : ∀ n, sp.init.get? root = some n →
    n.hist = (sp.init.filter (fun p => p.1 != root && decide (sp.topLevel ≤ p.2.level))).map
      (fun p => (⟨0, sp.rootVal p.1⟩ : Entry V))

/-- Assumptions on the four functions of the structure (3.1). -/
structure SpecOK (sp : Spec V T) : Prop where
  /-- A live pointer is a pointer of some entry. -/
  liveSub : ∀ h y, y ∈ sp.live h → ∃ e ∈ h, y ∈ sp.ptrs e.val
  /-- The initial structure: distinct ids, root exists, entries at time 0. -/
  initDistinct : (sp.init.map (·.1)).Nodup
  initRoot : (sp.init.get? root).isSome
  initTime : ∀ p ∈ sp.init, ∀ e ∈ p.2.hist, e.time = 0
  /-- Data nodes have no pointers (3.2). -/
  initData : ∀ p ∈ sp.init, p.2.isData → ∀ e ∈ p.2.hist, sp.ptrs e.val = []
  /-- A4: every pointer goes to a node on a lower level. -/
  initLevels : ∀ p ∈ sp.init, ∀ e ∈ p.2.hist, ∀ y ∈ sp.ptrs e.val,
    ∃ m, sp.init.get? y = some m ∧ m.level < p.2.level
  /-- A3: every initial node is reachable at time 0. -/
  initReachable : ∀ p ∈ sp.init, reachable sp sp.init 0 p.1 = true
  /-- With a virtual root: `VirtInit`. -/
  virtInit : sp.virt = true → VirtInit sp

/-- The assumptions on one transaction with a virtual root, R1 to R4
(bergdb 011-11, 8.2): the changes c made at time i to the
structure P. BergDB meets them, and the trace checker checks them (C-A).
Added 2026-10-16 (F1-008-11, WP E3). -/
structure VirtStep (sp : Spec V T) (P : Struct V) (i : Time) (c : Changes V) : Prop where
  /-- At most one new root child (BergDB's `TopDs.newSuperRoot` updates the
  transaction's top node in place); it is an index node and gets entries. -/
  newTop : ∀ nn ∈ c.new, sp.topLevel ≤ nn.level →
    nn.isData = false ∧ (∃ a ∈ c.adds, a.1 = nn.id) ∧
    ∀ nn' ∈ c.new, sp.topLevel ≤ nn'.level → nn' = nn
  /-- R3: a root child gets entries only in the transaction that creates it. -/
  topFixed : ∀ a ∈ c.adds, ∀ n, P.get? a.1 = some n → a.1 ≠ root → n.level < sp.topLevel
  /-- R2: the root gets the entry for the new root child, and no other. -/
  rootAdds : c.adds.filter (fun a => a.1 == root) =
    (c.new.filter (fun nn => decide (sp.topLevel ≤ nn.level))).map (fun nn => (root, sp.rootVal nn.id))
  /-- R4: every older root child can be reached from the new one through
  pointers between root children (BergDB's skip list). -/
  closure : ∀ nn ∈ c.new, sp.topLevel ≤ nn.level → ∀ n, (P.apply i c).get? nn.id = some n →
    ∀ y m, P.get? y = some m → y ≠ root → sp.topLevel ≤ m.level →
      y ∈ topClosure sp (P.apply i c) nn.id n
  /-- A root child that a root child points to is not reachable now (BergDB
  follows skip pointers only to find older top nodes, which are dead). -/
  dead : ∀ z n, (P.apply i c).get? z = some n → isTop sp (P.apply i c) z = true →
    ∀ y ∈ pointees sp n.hist, isTop sp (P.apply i c) y = true →
      reachable sp (P.apply i c) i y = false

/-- Assumptions A2 to A4 and the data node rules for one transaction: the
changes c made at time i to the structure P (3.2, 3.4). A1 holds by the type
of `Spec.exec`. -/
structure StepOK (sp : Spec V T) (P : Struct V) (i : Time) (c : Changes V) : Prop where
  /-- New nodes get ids that are not in use, and distinct. -/
  fresh : ∀ n ∈ c.new, P.get? n.id = none
  distinct : (c.new.map (·.id)).Nodup
  /-- A2: entries are added only to nodes that are reachable at time i, after
  the change. -/
  current : ∀ a ∈ c.adds, reachable sp (P.apply i c) i a.1 = true
  /-- Data nodes (3.2): no entries after creation, and no pointers. -/
  dataFixed : ∀ a ∈ c.adds, ∀ n, P.get? a.1 = some n → n.isData = false
  dataNoPtrs : ∀ a ∈ c.adds, ∀ n ∈ c.new, n.id = a.1 → n.isData → sp.ptrs a.2 = []
  /-- A4: every pointer goes to a node on a lower level. -/
  levels : ∀ a ∈ c.adds, ∀ y ∈ sp.ptrs a.2, ∃ n m,
    (P.apply i c).get? a.1 = some n ∧ (P.apply i c).get? y = some m ∧ m.level < n.level
  /-- A3: new nodes are reachable at time i. -/
  newReachable : ∀ n ∈ c.new, reachable sp (P.apply i c) i n.id = true
  /-- A5, no resurrection: a node reachable at time i was reachable at time
  i-1, or is created by T(i). Marking needs it (step 3 with `Algo.mark`, T13):
  a node that becomes reachable again without a change below it could be dirty
  without being on the access path of the change. Added 2026-10-15
  (bergdb 011-11, WP E1); BergDB meets it (checker, C-A). -/
  noRes : ∀ y, reachable sp (P.apply i c) i y = true →
    reachable sp P (i - 1) y = true ∨ y ∈ c.new.map (·.id)
  /-- With a virtual root: `VirtStep`. -/
  virt : sp.virt = true → VirtStep sp P i c
  /-- The touch (bergdb item 001, WP R3; `Changes.touch`): the touched nodes
  are index nodes reachable at time i-1, before the change; and a node
  reachable then with a touched node below it then (through live pointers) is
  touched too, or is a virtual root (Java's touch walks down from the super
  root along the paths of the step's own puts, `Db.touchPaths`, bergdb 024-07).
  Without a touch these say nothing. -/
  touchIndex : ∀ x ∈ c.touch, isIndex P x = true
  touchReach : ∀ x ∈ c.touch, reachable sp P (i - 1) x = true
  touchUp : ∀ x ∈ c.touch, ∀ p np, reachable sp P (i - 1) p = true → P.get? p = some np →
    x ∈ reachFrom sp P (i - 1) p np → p ∈ c.touch ∨ (sp.virt = true ∧ p = root)

/-- The assumptions hold for a run: for the structure, and for every
transaction of the run. -/
def RunOK (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
  SpecOK sp ∧ ∀ j (h : j < ts.length),
    let db := run sp al (ts.take j)
    StepOK sp db.P (j + 1) (sp.exec ts[j] (j + 1) (view sp db.P j))

/-- A run with restarts: after each transaction marked true, the database
crashes and starts again from its stream (6.2). -/
def runRestarts (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool)) : DB V T :=
  ts.foldl (fun db p =>
    let db := step sp al db p.1
    if p.2 then startup sp db.S else db) (init sp)

end SIS
