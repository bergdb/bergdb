/-
Self-indexed streams in Lean: the assumptions of the theorems, and runs with
restarts.

Section numbers refer to theory/sis-model.md. Trusted part.
-/
import SIS.Startup

namespace SIS

variable {V T : Type} [DecidableEq V]

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
