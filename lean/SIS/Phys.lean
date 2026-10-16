/-
Self-indexed streams in Lean: the physical layer, what Java holds in memory
(bergdb item 001, stages 1 and 2; its plan, section 8.6;
docs/level2-alignment.md, section 13, "Lazy reading"). Trusted part.

Stage 1 (WP L1) models how BergDB reads today, without eviction. After a
restart, Java holds in memory the canonical objects of the startup section's
index nodes, of the nodes of D, and of the nodes the rerun reaches; every
other node is read from the stream when a pointer to it is first followed
(`NodeCollection.followStreamPointer`). The model's P (Basic.lean) stays the
specification: the theorems of PhysTheorems.lean say that what is read through
this layer is P.

What is left out: concurrency (readers beside the writer), access data, bytes,
and the search of the TopDs skip list (the root's object stands for it: reads
start at the root's live child at their time, as in the logical model).
-/
import SIS.Startup

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Version w cut back to time s: its history up to s, its references as they
are. Java cuts back a key node version of the startup section to the startup
time when it reads one (`KeyNode.toPreviousState`; `DbStarter`,
`NodeCollection.followStreamPointer`). -/
def Version.cutTo (w : Version V) (s : Time) : Version V :=
  { w with hist := w.hist.upTo s }

/-! ## Objects and memory -/

/-- What a pointer slot of an object holds (Java's pair of `pointers[i]` and
`pos[i]`): an object in memory, by its handle (a memory slot), or a reference
to a version in the stream (a stream slot): the record of the version, or none
for a node that had not been written when the pointer was written (a vpos). -/
inductive Slot where
  | mem (h : Nat)
  | stream (r : Option Nat)
  deriving DecidableEq, Repr

/-- An object in memory, a Java `Node` object. -/
structure Obj (V : Type) where
  node : NodeId
  level : Nat
  isData : Bool
  hist : History V
  /-- The one object of its node that holds the node's whole history and may
  change (`Node.isCanonical`); otherwise a snapshot of a version. -/
  canonical : Bool
  /-- Java's spos: the record of the version that the object holds, or none
  for a node not yet written. -/
  pos : Option Nat
  /-- One slot for each pointee of the history, live or dead. -/
  slots : List (NodeId × Slot)
  deriving Repr

/-- Java's memory: the objects, by handle; the node table (`Cache3`), one
object per node; Rule R of the last startup (`NodeCollection.section`); the
object of the root. -/
structure Mem (V : Type) where
  objs : List (Nat × Obj V)
  table : List (NodeId × Nat)
  /-- The startup pos of the last startup: Rule R takes the newest version in
  R(s), ..., R(k); a key node version of the section read at startup is cut
  back to s. -/
  s : Nat
  root : Nat
  next : Nat

/-- The object with handle h. -/
def Mem.obj? (m : Mem V) (h : Nat) : Option (Obj V) := m.objs.lookup h

/-- Replace the object with handle h. -/
def Mem.setObj (m : Mem V) (h : Nat) (o : Obj V) : Mem V :=
  { m with objs := (h, o) :: m.objs.filter (fun p => p.1 != h) }

/-- Add an object; returns its handle. -/
def Mem.addObj (m : Mem V) (o : Obj V) : Mem V × Nat :=
  ({ m with objs := (m.next, o) :: m.objs, next := m.next + 1 }, m.next)

/-- The node table's object for node y. -/
def Mem.tableOf (m : Mem V) (y : NodeId) : Option Nat := m.table.lookup y

/-- Set the node table's object for node y. -/
def Mem.setTable (m : Mem V) (y : NodeId) (h : Nat) : Mem V :=
  { m with table := (y, h) :: m.table.filter (fun p => p.1 != y) }

/-- The slot of an object for pointee y. -/
def Obj.slot? (o : Obj V) (y : NodeId) : Option Slot := o.slots.lookup y

/-- Set the slot of an object for pointee y (Java's `setPointer`). -/
def Obj.setSlot (o : Obj V) (y : NodeId) (sl : Slot) : Obj V :=
  { o with slots := o.slots.map (fun p => if p.1 == y then (y, sl) else p) }

/-- A key node (`Node.TYPE_KEY_NODE`): an index node that is not the root or,
with a virtual root, a root child (BergDB's top nodes). Java cuts back only
key node versions. -/
def isKeyLevel (sp : Spec V T) (isData : Bool) (level : Nat) : Bool :=
  !isData && (!sp.virt || decide (level < sp.topLevel))

/-- The object read from version w (`StoredKeyNode.parse`, `StoredTopNode.parse`):
its history, cut back to time s if `cut` is some s, its record, and for each
pointee of that history a stream slot with w's reference. A snapshot. -/
def Obj.ofVersion (sp : Spec V T) (w : Version V) (cut : Option Nat) : Obj V :=
  let h := match cut with
    | some s => w.hist.upTo s
    | none => w.hist
  { node := w.node, level := w.level, isData := w.isData, hist := h, canonical := false,
    pos := some w.recNo, slots := (pointees sp h).map (fun y => (y, Slot.stream (w.ref? y))) }

/-! ## The first touch (stage 1: Java's rule today, Q7 of the plan) -/

/-- Rule R for the whole process (`NodeCollection.followStreamPointer`, step 2,
and `resolvePointers`): a stream slot naming record r of node y leads to y's
newest version in R(s), ..., R(k) if that is newer, and from a vpos (none)
to it whenever there is one. -/
def ruleRRef (S : Stream V T) (s : Nat) (y : NodeId) (r : Option Nat) : Option Nat :=
  match newest S s y with
  | some w =>
    match r with
    | some r => if r < w.recNo then some w.recNo else some r
    | none => some w.recNo
  | none => r

/-- The node table's object can serve a stream slot that leads to record r
(step 3): it is canonical, or a snapshot at least as new as r. -/
def Obj.usable (o : Obj V) (r : Option Nat) : Bool :=
  o.canonical || match r, o.pos with
    | some r, some p => decide (r ≤ p)
    | _, _ => false

/-- `Cache3.isBetter`: object o should replace the table's object o0 for their
node: never a canonical one, never for a data node (one version); otherwise when o
is canonical or newer. -/
def Obj.better (o o0 : Obj V) : Bool :=
  !o.isData && !o0.canonical && (o.canonical || match o.pos, o0.pos with
    | some p, some p0 => decide (p0 < p)
    | some _, none => true
    | _, _ => false)

/-- `Cache3.register`: object h goes into the node table, unless the table
has a better object for its node. Returns the memory and the table's object
after. -/
def Mem.register (m : Mem V) (h : Nat) : Mem V × Nat :=
  match m.obj? h with
  | none => (m, h)
  | some o =>
    match m.tableOf o.node with
    | none => (m.setTable o.node h, h)
    | some h0 =>
      if h0 == h then (m, h) else
      match m.obj? h0 with
      | some o0 => if o.better o0 then (m.setTable o.node h, h) else (m, h0)
      | none => (m.setTable o.node h, h)

/-- `Cache3.makeCanonical` and `NodeCollection.makeCanonical`, when the writer
reaches object h of node y through the slot of object hp: the table's
canonical object, if there is one; else the newer of h and the table's object,
which becomes canonical and the table's. The slot then names it. -/
def Mem.makeCanonical (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) : Mem V × Nat :=
  let pick : Nat := match m.tableOf y with
    | none => h
    | some h0 =>
      if h0 == h then h else
      match m.obj? h0, m.obj? h with
      | some o0, some o =>
        if o0.canonical then h0 else
        match o0.pos, o.pos with
        | some p0, some p => if p < p0 then h0 else h
        | some _, none => h0
        | _, _ => h
      | _, _ => h
  let m1 := match m.obj? pick with
    | some o => (m.setObj pick { o with canonical := true }).setTable y pick
    | none => m
  let m2 := match m1.obj? hp with
    | some op => m1.setObj hp (op.setSlot y (Slot.mem pick))
    | none => m1
  (m2, pick)

/-- Follow the slot of object hp for pointee y (`NodeCollection.followPointer`
for readers, `WriterFollower` for the writer). A memory slot gives its object
(made canonical for the writer). A stream slot is a first touch: Rule R; then
the node table's object if it is canonical or at least as new; else the
version read, cut back to s if it is a key node version of R(s), ..., R(k),
and entered in the table; the slot then names the object (it is swizzled);
and the writer makes it canonical. none: no such slot, or a vpos with
nothing to read (Java throws). -/
def Mem.follow (sp : Spec V T) (S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId)
    (writer : Bool) : Mem V × Option Nat :=
  match (m.obj? hp).bind (·.slot? y) with
  | none => (m, none)
  | some (Slot.mem h) =>
    match m.obj? h with
    | some o => if writer && !o.canonical then
        let r := m.makeCanonical hp y h
        (r.1, some r.2)
      else (m, some h)
    | none => (m, none)
  | some (Slot.stream r) =>
    let r' := ruleRRef S m.s y r
    let fromTable : Option Nat := match m.tableOf y with
      | some h0 => match m.obj? h0 with
        | some o0 => if o0.usable r' then some h0 else none
        | none => none
      | none => none
    let loaded : Option (Mem V × Nat) := match fromTable with
      | some h0 => some (m, h0)
      | none =>
        match r' with
        | none => none
        | some r'' =>
          match S.versionAt r'' y with
          | none => none
          | some w =>
            let cut := if m.s ≤ r'' && isKeyLevel sp w.isData w.level then some m.s else none
            let (m1, h1) := m.addObj (Obj.ofVersion sp w cut)
            some (m1.register h1)
    match loaded with
    | none => (m, none)
    | some (m1, h1) =>
      let m2 := match m1.obj? hp with
        | some op => m1.setObj hp (op.setSlot y (Slot.mem h1))
        | none => m1
      match m2.obj? h1 with
      | some o1 => if writer && !o1.canonical then
          let r := m2.makeCanonical hp y h1
          (r.1, some r.2)
        else (m2, some h1)
      | none => (m2, some h1)

/-- Read at time t from object h, down (`Dag.getOne`, `getMany`, through the
readers' follower): each object reached, by node, with its history at t; the
memory after the first touches on the way. As `readFrom`, a pointer to an
object that is not on a lower level is not followed. fuel bounds the depth. -/
def Mem.readAt (sp : Spec V T) (S : Stream V T) : Nat → Mem V → Time → Nat →
    Mem V × List (NodeId × History V)
  | 0, m, _, _ => (m, [])
  | fuel + 1, m, t, h =>
    match m.obj? h with
    | none => (m, [])
    | some o =>
      (sp.live (o.hist.upTo t)).foldl (fun (acc : Mem V × List (NodeId × History V)) y =>
        match acc.1.follow sp S h y false with
        | (m1, some h1) =>
          match m1.obj? h1 with
          | some o1 =>
            if o1.level < o.level then
              let r := Mem.readAt sp S fuel m1 t h1
              (r.1, acc.2 ++ r.2)
            else (m1, acc.2)
          | none => (m1, acc.2)
        | (m1, none) => (m1, acc.2)) (m, [(o.node, o.hist.upTo t)])

/-- A read at time t from the root's object. -/
def Mem.read (sp : Spec V T) (S : Stream V T) (m : Mem V) (t : Time) :
    Mem V × List (NodeId × History V) :=
  match m.obj? m.root with
  | some o => m.readAt sp S (o.level + 1) t m.root
  | none => (m, [])

/-! ## Startup (`DbStarter.doOrdinaryStartup`) -/

/-- The canonical object of node x made from version w, cut back to s, with
Rule R in its stream slots (`DbStarter.updateStreamPointers`). -/
def canonOfVersion (sp : Spec V T) (S : Stream V T) (s : Nat) (w : Version V) : Obj V :=
  let o := Obj.ofVersion sp w (if isKeyLevel sp w.isData w.level then some s else none)
  { o with
    canonical := true
    slots := o.slots.map (fun p => match p.2 with
      | Slot.stream r => (p.1, Slot.stream (ruleRRef S s p.1 r))
      | sl => (p.1, sl)) }

/-- The index nodes with a version in R(s), ..., R(k), each once, by id. -/
def sectionNodes (S : Stream V T) (s : Nat) : List NodeId :=
  ((S.drop s).flatMap (fun R => (R.vers.filter (fun v => !v.isData)).map (·.node))).eraseDups

/-- Make memory slots between canonical objects: a stream slot of a canonical
object that names the record of the version a canonical object was made from
names that object (`DbStarter.createMemoryPointers`). -/
def Mem.linkCanonical (m : Mem V) : Mem V :=
  { m with objs := m.objs.map (fun p =>
      if !p.2.canonical then p else
      (p.1, { p.2 with slots := p.2.slots.map (fun q => match q.2 with
        | Slot.stream (some r) =>
          match m.tableOf q.1 with
          | some h0 =>
            match m.obj? h0 with
            | some o0 => if o0.canonical && o0.pos == some r then (q.1, Slot.mem h0) else q
            | none => q
          | none => q
        | _ => q) })) }

/-- The nodes on the writer's paths for the change c at time j, in P before
it (Java's put path, through `WriterFollower`): the nodes reachable at j - 1
with a node below them, themselves included, that c changes or that is no
longer reachable at j (a node the transaction replaces). -/
def pathOf (sp : Spec V T) (P : Struct V) (c : Changes V) (j : Time) : List NodeId :=
  let P' := P.apply j c
  let touched := fun z => changed c z || (reachable sp P (j - 1) z && !reachable sp P' j z)
  ((reachList sp P (j - 1)).eraseDups.filter (fun x => match P.get? x with
    | some n => (reachFrom sp P (j - 1) x n).any touched
    | none => false))

/-- The canonical object of node x, if there is one. -/
def Mem.canonicalOf (m : Mem V) (x : NodeId) : Option Nat :=
  match m.tableOf x with
  | some h => match m.obj? h with
    | some o => if o.canonical then some h else none
    | none => none
  | none => none

/-- The writer reaches node x of the path: from the canonical object of a
node of the path that x is a live child of at j - 1, through that object's
slot (the writer's follow). -/
def Mem.reachOnPath (sp : Spec V T) (S : Stream V T) (P : Struct V) (j : Time)
    (path : List NodeId) (m : Mem V) (x : NodeId) : Mem V :=
  match m.canonicalOf x with
  | some _ => m
  | none =>
    let parent := path.find? (fun p => match P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (j - 1))).contains x
      | _, _ => false)
    match parent with
    | some p => match m.canonicalOf p with
      | some hp => (m.follow sp S hp x true).1
      | none => m
    | none => m

/-- Object p (by handle) is one that a new pointer to y may copy its slot from:
canonical, with a slot for y, of a node reachable at j - 1 that has y as a
live child then. -/
def srcOK (sp : Spec V T) (P : Struct V) (j : Time) (y : NodeId) (p : Nat × Obj V) : Bool :=
  p.2.canonical && (p.2.slot? y).isSome && reachable sp P (j - 1) p.2.node &&
    match P.get? p.2.node with
    | some n => (sp.live (n.hist.upTo (j - 1))).contains y
    | none => false

/-- The slot that a new pointer of object o to y gets (Java: the pointer of a
new klong, which the writer has in hand: the object it created or reached, or a
copy of a pointer of a node it reached, as a split copies the split node's
pointers): a memory slot to y's canonical object; else a copy of the slot for
y of the canonical object of a node that is reachable at j - 1 and has y as a
live child then; else o's own slot for y; else a copy of any canonical
object's slot for y (BergDB's skip pointers, copied from the super root);
else none. -/
def Mem.newSlot (sp : Spec V T) (P : Struct V) (j : Time) (m : Mem V) (o : Obj V) (y : NodeId) :
    Option Slot :=
  match m.canonicalOf y with
  | some h => some (Slot.mem h)
  | none =>
    match m.objs.find? (srcOK sp P j y) with
    | some p => p.2.slot? y
    | none =>
      match o.slot? y with
      | some sl => some sl
      | none => (m.objs.find? (fun p => p.2.canonical && (p.2.slot? y).isSome)).bind
          (fun p => p.2.slot? y)

/-- Give object o the slot sl for pointee y: replace its slot for y, or add one. -/
def Obj.putSlot (o : Obj V) (y : NodeId) (sl : Slot) : Obj V :=
  if (o.slot? y).isSome then o.setSlot y sl else { o with slots := o.slots ++ [(y, sl)] }

/-- Apply the change c of transaction j to the canonical objects: a new
canonical object for each new node, the entries appended, and for each
pointee of a new entry the slot of a new pointer (`Dag.putKv` and its splits,
through the writer). The slots that new pointers copy are taken from the
objects as they were before the entries (m1): a split copies the pointers its
node had; the pointers the transaction creates are to new or reached objects,
which are canonical. -/
def Mem.applyChange (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) :
    Mem V :=
  let m1 := c.new.foldl (fun (m : Mem V) nn =>
    let o : Obj V :=
      { node := nn.id, level := nn.level, isData := nn.isData, hist := [], canonical := true,
        pos := none, slots := [] }
    let (m', h) := m.addObj o
    m'.setTable nn.id h) m
  c.adds.foldl (fun (m : Mem V) a =>
    match m.canonicalOf a.1 with
    | none => m
    | some h =>
      match m.obj? h with
      | none => m
      | some o =>
        let o1 := { o with hist := o.hist ++ [⟨j, a.2⟩] }
        let o2 := (sp.ptrs a.2).foldl (fun (o' : Obj V) y =>
          match m1.newSlot sp P j o' y with
          | some sl => o'.putSlot y sl
          | none => o') o1
        m.setObj h o2) m1

/-- Make node x of D canonical (`DbStarter.canonicalNode`): the table's
canonical object; else its newest version in the section, or its latest
version, cut back to s. -/
def Mem.canonicalNode (sp : Spec V T) (S : Stream V T) (m : Mem V) (x : NodeId) : Mem V :=
  match m.canonicalOf x with
  | some _ => m
  | none =>
    match (newest S m.s x).or (S.lv x) with
    | some w =>
      let (m1, h) := m.addObj (canonOfVersion sp S m.s w)
      m1.setTable x h
    | none => m

/-- Java's startup from the stream S (`DbStarter.doOrdinaryStartup`), lazy:
1. the canonical objects of the section's index nodes, from their newest
   versions in R(s), ..., R(k), cut back to s, with Rule R in their slots
   (`createMaps`, `updateStreamPointers`, `changeKeyNodesToStateAtStartupTime`,
   `registerSectionNodes`), linked by memory slots (`createMemoryPointers`);
   but not the nodes with no entries up to s, which Java leaves out as
   created in the rerun section (`wasCreatedInRerunSection`: a top node
   created after s, a key node whose first klong is after s; Java keeps a key
   node with no klongs at all, which reads the same);
2. the root's object: with a virtual root, rebuilt from the root children
   read from top(k) (`rootVersion`, `topsRead`), canonical, with memory slots
   to the root children that have canonical objects; otherwise the root's
   canonical object;
3. the rerun of T(s+1), ..., T(k): for each, the writer reaches the nodes of
   its paths, which become canonical, and the change is applied to the
   canonical objects; the nodes of gd(j) get canonical objects
   (`rerunTransaction`, `canonicalNode`).
The P that directs the writer is the logical startup's (`baseStruct` and
`rerun`). -/
def lazyStartup (sp : Spec V T) (S : Stream V T) : Mem V :=
  let s := lastSp S
  let m0 : Mem V := { objs := [], table := [], s := s, root := 0, next := 1 }
  -- 1. The section, but the nodes with no entries up to s.
  let m1 := (sectionNodes S s).foldl (fun (m : Mem V) x =>
    match newest S s x with
    | some w =>
      if (w.hist.upTo s).isEmpty then m else
      let (m', h) := m.addObj (canonOfVersion sp S s w)
      m'.setTable x h
    | none => m) m0
  -- 2. The root.
  let m2 : Mem V :=
    if sp.virt then
      let rv := rootVersion sp s (topsRead sp S s true)
      let (m', h) := m1.addObj { (canonOfVersion sp S s rv) with hist := rv.hist, pos := none }
      { m'.setTable root h with root := h }
    else
      match m1.canonicalOf root with
      | some h => { m1 with root := h }
      | none =>
        match topVersion S s true with
        | some w =>
          let (m', h) := m1.addObj (canonOfVersion sp S s w)
          { m'.setTable root h with root := h }
        | none => m1
  let m3 := m2.linkCanonical
  -- 3. The rerun.
  let r := (sectionIdx S s).foldl (fun (acc : Mem V × Struct V) j =>
    match S[j]? with
    | some R =>
      match R.trans with
      | some tr =>
        let P := acc.2
        let c := sp.exec tr j (view sp P (j - 1))
        let path := pathOf sp P c j
        let path' := path.mergeSort (fun a b => decide
          (((P.get? b).map (·.level)).getD 0 ≤ ((P.get? a).map (·.level)).getD 0))
        let m := path'.foldl (Mem.reachOnPath sp S P j path) acc.1
        let m := m.applyChange sp P j c
        let m := R.gd.foldl (Mem.canonicalNode sp S) m
        (m, P.apply j c)
      | none => acc
    | none => acc) (m3, baseStruct sp S s true)
  r.1

/-! ## Operations after startup (for the theorems) -/

/-- An operation on the memory after a startup: a read at time t, or the
writer's follow of the slot for y of object h (the writer's walk down from
the root, before a transaction changes anything). -/
inductive Op where
  | read (t : Time)
  | write (h : Nat) (y : NodeId)

/-- The memory after operation op. -/
def Mem.step (sp : Spec V T) (S : Stream V T) (m : Mem V) : Op → Mem V
  | .read t => (m.read sp S t).1
  | .write h y => (m.follow sp S h y true).1

/-- The writer may follow the slot for y of object h at time k: h is a
canonical object of a node reachable at k (in P), and y is a live child of it
then. -/
def Mem.writable (sp : Spec V T) (P : Struct V) (k : Time) (m : Mem V) (h : Nat) (y : NodeId) :
    Prop :=
  ∃ o, m.obj? h = some o ∧ o.canonical = true ∧ reachable sp P k o.node = true ∧
    y ∈ sp.live o.hist

/-- The operations ops, applied in turn to memory m, are admissible at time k:
every read is at a time up to k, and the writer follows only slots it may
follow. -/
def OpsOK (sp : Spec V T) (S : Stream V T) (P : Struct V) (k : Time) : Mem V → List Op → Prop
  | _, [] => True
  | m, .read t :: ops => t ≤ k ∧ OpsOK sp S P k (m.step sp S (.read t)) ops
  | m, .write h y :: ops => m.writable sp P k h y ∧ OpsOK sp S P k (m.step sp S (.write h y)) ops

/-! ## The assumptions of the physical layer -/

/-- What the physical layer assumes of one transaction, the changes c made at
time i to the structure P (bergdb item 001, WP L3). BergDB meets both: a key
node's pointer (its klong) is live until a later klong of the same key; and a
split's new nodes take the children of the node they split, which stops being
current or changes (docs/level4-alignment.md, M43: no path moves a child from
one current node to another). With TREE and A5, `adopt` follows. -/
structure PhysStep (sp : Spec V T) (P : Struct V) (i : Time) (c : Changes V) : Prop where
  /-- A node's new live children at i are pointees of its new entries. -/
  liveNew : ∀ x n, (P.apply i c).get? x = some n → ∀ y ∈ sp.live (n.hist.upTo i),
    (∃ n0, P.get? x = some n0 ∧ y ∈ sp.live (n0.hist.upTo (i - 1))) ∨
      ∃ a ∈ c.adds, a.1 = x ∧ y ∈ sp.ptrs a.2
  /-- A new live child at i of a node reachable at i, that c does not create,
  was at i - 1 a live child of a node reachable then that c changes or that is
  not reachable at i (the node a split takes it from). -/
  adopt : ∀ x n, reachable sp (P.apply i c) i x = true → (P.apply i c).get? x = some n →
    ∀ y ∈ sp.live (n.hist.upTo i), (∀ n0, P.get? x = some n0 → y ∉ sp.live (n0.hist.upTo (i - 1))) →
      y ∉ c.new.map (·.id) →
      ∃ z nz, P.get? z = some nz ∧ reachable sp P (i - 1) z = true ∧
        (changed c z = true ∨ reachable sp (P.apply i c) i z = false) ∧
        y ∈ sp.live (nz.hist.upTo (i - 1))

/-- The assumptions of the physical layer hold for every transaction of a run. -/
def PhysRunOK (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
  ∀ j (h : j < ts.length),
    let db := run sp al (ts.take j)
    PhysStep sp db.P (j + 1) (sp.exec ts[j] (j + 1) (view sp db.P j))

end SIS
