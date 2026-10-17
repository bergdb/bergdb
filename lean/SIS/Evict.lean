/-
Self-indexed streams in Lean: the physical layer, part 2, with eviction
(bergdb item 001, stage 2, WP E2; the design is docs/level4-alignment.md,
section 5). Trusted part.

Stage 1 (Phys.lean) models what BergDB holds in memory and how it reads a node
it does not hold; nothing ever leaves memory there. This file adds what Level 4
needs:

* the pinned objects (the canonical objects of D's nodes, and the root's);
* unswizzling: a memory slot to an object that is not pinned and has been
  written becomes a stream slot naming that object's position, which is what
  the slot serialized before;
* release: an object that no memory slot points to leaves memory, and the
  node table forgets it;
* the Level 4 loader (Q7 of the plan): the canonical object, or exactly the
  version the slot names after Rule R; never a snapshot from the node table,
  never cut back after startup;
* the writer's walk and the change: the writer follows the slot to each node
  of its paths, and a new pointer copies its slot only from what the writer
  has in hand (A-COPY);
* the physical writer: each version from its node's canonical object, with
  references from its slots and, for pinned pointees, from their canonical
  objects (Java's `resolvePointers` at Level 4);
* startup with rule 4: the slots of D's objects linked by node id;
* runs with any cache operations (reads, unswizzles, releases) between
  transactions.

The theorems of stage 2 (T-CACHE, T-READ, T2-C, T-PIN) are to say that the
records and the reads are the model's, whatever the cache operations.

Left out, as in stage 1: concurrency, access data, bytes, and the search of
the TopDs skip list (the root's object stands for it).
-/
import SIS.Phys

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Pins, unswizzle and release -/

/-- The pinned objects: the canonical objects of the nodes of D, and the
root's object. Cache operations never change them. (Java pins more, which the
model treats as atomic: the record being written, the objects of an operation
in progress.) -/
def Mem.pinned (m : Mem V) (D : Dirty) (h : Nat) : Bool :=
  h == m.root || match m.obj? h with
    | some o => o.canonical && inD D o.node
    | none => false

/-- Some object in memory has a memory slot to object h. -/
def Mem.incoming (m : Mem V) (h : Nat) : Bool :=
  m.objs.any (fun p => p.2.slots.any (fun q => q.2 == Slot.mem h))

/-- Object h may be detached from the slots that point to it: it is in
memory, not pinned, and written (it has a position). -/
def Mem.detachable (m : Mem V) (D : Dirty) (h : Nat) : Bool :=
  match m.obj? h with
  | some o => !m.pinned D h && o.pos.isSome
  | none => false

/-- Object h may be released: detachable, and no memory slot points to it. -/
def Mem.eligible (m : Mem V) (D : Dirty) (h : Nat) : Bool :=
  m.detachable D h && !m.incoming h

/-- Unswizzle the slot of object hp for pointee y: if it is a memory slot to a
detachable object h, it becomes a stream slot naming h's position, which is
what the slot serialized before (Java's `Pointer.getSposForStream`).
Otherwise nothing changes. -/
def Mem.unswizzle (m : Mem V) (D : Dirty) (hp : Nat) (y : NodeId) : Mem V :=
  match m.obj? hp with
  | some op =>
    match op.slot? y with
    | some (Slot.mem h) =>
      match m.obj? h with
      | some o => if m.detachable D h then m.setObj hp (op.setSlot y (Slot.stream o.pos)) else m
      | none => m
    | _ => m
  | none => m

/-- Release object h if it is eligible: it leaves memory, and the node table
forgets it (Java also clears its canonical flag, since a reader may still hold
it). Otherwise nothing changes. -/
def Mem.release (m : Mem V) (D : Dirty) (h : Nat) : Mem V :=
  if m.eligible D h then
    { m with objs := m.objs.filter (fun p => p.1 != h), table := m.table.filter (fun p => p.2 != h) }
  else m

/-! ## The Level 4 loader -/

/-- The writer makes the object h, which it reached through the slot of object
hp for y, canonical: the node table's canonical object of y if there is one,
else h, which becomes canonical and the table's. The slot then names it. (The
table names canonical objects only, so stage 1's "the newer of h and the
table's object" is gone.) -/
def Mem.promote (m : Mem V) (hp : Nat) (y : NodeId) (h : Nat) : Mem V × Nat :=
  let pick := (m.canonicalOf y).getD h
  let m1 := match m.obj? pick with
    | some o => (m.setObj pick { o with canonical := true }).setTable y pick
    | none => m
  let m2 := match m1.obj? hp with
    | some op => m1.setObj hp (op.setSlot y (Slot.mem pick))
    | none => m1
  (m2, pick)

/-- Follow the slot of object hp for pointee y, Level 4. A memory slot gives
its object. A stream slot is a first touch: the node table's canonical object
of y if there is one; else the version that the slot names after Rule R, read
exactly (not cut back, and not entered in the node table); the slot then names
it. The writer then promotes the object reached. Rule R is that of the last
startup: its stream S0, of which the stream now, S, is an extension; versions
are read from S, since after an eviction a slot can name a record written
since the startup. none: no such slot, or a vpos with nothing to read. -/
def Mem.follow4 (sp : Spec V T) (S0 S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId)
    (writer : Bool) : Mem V × Option Nat :=
  let reached : Option (Mem V × Nat) :=
    match (m.obj? hp).bind (·.slot? y) with
    | none => none
    | some (Slot.mem h) => if (m.obj? h).isSome then some (m, h) else none
    | some (Slot.stream r) =>
      match m.canonicalOf y with
      | some h0 => some (m, h0)
      | none =>
        match ruleRRef S0 m.s y r with
        | none => none
        | some r' =>
          match S.versionAt r' y with
          | none => none
          | some w => some (m.addObj (Obj.ofVersion sp w none))
  match reached with
  | none => (m, none)
  | some (m1, h1) =>
    let m2 := match m1.obj? hp with
      | some op => m1.setObj hp (op.setSlot y (Slot.mem h1))
      | none => m1
    if writer then
      let r := m2.promote hp y h1
      (r.1, some r.2)
    else (m2, some h1)

/-- Read at time t from object h, down, through the Level 4 loader: as
`Mem.readAt`. -/
def Mem.readAt4 (sp : Spec V T) (S0 S : Stream V T) : Nat → Mem V → Time → Nat →
    Mem V × List (NodeId × Node V)
  | 0, m, _, _ => (m, [])
  | fuel + 1, m, t, h =>
    match m.obj? h with
    | none => (m, [])
    | some o =>
      (sp.live (o.hist.upTo t)).foldl (fun (acc : Mem V × List (NodeId × Node V)) y =>
        match acc.1.follow4 sp S0 S h y false with
        | (m1, some h1) =>
          match m1.obj? h1 with
          | some o1 =>
            if o1.level < o.level then
              let r := Mem.readAt4 sp S0 S fuel m1 t h1
              (r.1, acc.2 ++ r.2)
            else (m1, acc.2)
          | none => (m1, acc.2)
        | (m1, none) => (m1, acc.2)) (m, [(o.node, o.nodeAt t)])

/-- A read at time t from the root's object, Level 4. -/
def Mem.read4 (sp : Spec V T) (S0 S : Stream V T) (m : Mem V) (t : Time) :
    Mem V × List (NodeId × Node V) :=
  match m.obj? m.root with
  | some o => m.readAt4 sp S0 S (o.level + 1) t m.root
  | none => (m, [])

/-- The writer's view of P at time t through the Level 4 loader. -/
def Mem.view4 (sp : Spec V T) (S0 S : Stream V T) (m : Mem V) (t : Time) : Mem V × View V :=
  let r := m.read4 sp S0 S t
  (r.1, fun x => r.2.lookup x)

/-- The writer reaches node x of the path, as `Mem.reachOnPath`, through the
Level 4 loader: from the canonical object of the node of the path that x is a
live child of at j - 1, through that object's slot (the writer's follow), which
then names x's canonical object. Unlike stage 1, the writer follows the slot
also when x has a canonical object already, as Java's writer does, which walks
down from the root: after an unswizzle, the slot may be a stream slot, or name
another object of x (docs/level4-alignment.md, 5.10). -/
def Mem.reachOnPath4 (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (j : Time)
    (path : List NodeId) (m : Mem V) (x : NodeId) : Mem V :=
  let parent := path.find? (fun p => match P.get? p, m.canonicalOf p with
    | some n, some _ => (sp.live (n.hist.upTo (j - 1))).contains x
    | _, _ => false)
  match parent with
  | some p => match m.canonicalOf p with
    | some hp => (m.follow4 sp S0 S hp x true).1
    | none => m
  | none => m

/-- An object that a new pointer to y may copy its slot from, Level 4: a
canonical object of a node reachable at j - 1, with y a pointee of its history
and a slot for it; if it is a virtual root's (never written, so that its slots
for dead pointees may be stale), with y a live child of it at j - 1. Stage 1's
`srcOK` asks for a live child always; Java's writer also copies dead pointers
(the skip slots of `TopDs.newSuperRoot`). -/
def srcOK4 (sp : Spec V T) (P : Struct V) (j : Time) (y : NodeId) (p : Nat × Obj V) : Bool :=
  p.2.canonical && (p.2.slot? y).isSome && (pointees sp p.2.hist).contains y &&
    reachable sp P (j - 1) p.2.node &&
    (written sp p.2.node || match P.get? p.2.node with
      | some n => (sp.live (n.hist.upTo (j - 1))).contains y
      | none => false)

/-- The slot that a new pointer of object o to y gets, Level 4 (Java: the
pointer of a new klong, which the writer has in hand): a memory slot to y's
canonical object; else a copy of the slot for y of an object that `srcOK4`
allows; else o's own slot for y; else none. Stage 1's last resort, a copy of
any canonical object's slot for y, is gone: a canonical object that is not
current may hold a stale slot, and Java copies only from the nodes its writer
reached (A-COPY, `CopyStep`). -/
def Mem.newSlot4 (sp : Spec V T) (P : Struct V) (j : Time) (m : Mem V) (o : Obj V) (y : NodeId) :
    Option Slot :=
  match m.canonicalOf y with
  | some h => some (Slot.mem h)
  | none =>
    match m.objs.find? (srcOK4 sp P j y) with
    | some p => p.2.slot? y
    | none => o.slot? y

/-- Apply the change c of transaction j to the canonical objects, Level 4: as
`Mem.applyChange`, with `newSlot4`. -/
def Mem.applyChange4 (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) :
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
          match m1.newSlot4 sp P j o' y with
          | some sl => o'.putSlot y sl
          | none => o') o1
        m.setObj h o2) m1

/-! ## Startup, Level 4 -/

/-- The position of each canonical object made by the startup from S, as Java's
startup sets it (`DbStarter`'s `newById`): the record of its node's newest
version in R(s), ..., R(k), if there is one; otherwise it stays (a node of D
made from its latest version, or a virtual root, never written). -/
def Mem.sectionPos (m : Mem V) (S : Stream V T) : Mem V :=
  { m with objs := m.objs.map (fun p =>
      if !p.2.canonical then p else
      match newest S m.s p.2.node with
      | some w => (p.1, { p.2 with pos := some w.recNo })
      | none => p) }

/-- Rule 4: each stream slot of a canonical object of a node of D that names a
node with a canonical object becomes a memory slot to it. Java's startup links
the section's objects by exact position only (`createMemoryPointers`); rule 4
links D's objects by node id, as Java's `resolvePointers` does today at every
write, with a node table that never forgets. -/
def Mem.linkD (m : Mem V) (D : Dirty) : Mem V :=
  { m with objs := m.objs.map (fun p =>
      if !(p.2.canonical && inD D p.2.node) then p else
      (p.1, { p.2 with slots := p.2.slots.map (fun q => match q.2 with
        | Slot.stream _ => match m.canonicalOf q.1 with
          | some h0 => (q.1, Slot.mem h0)
          | none => q
        | _ => q) })) }

/-- Java's startup from S, Level 4: stage 1's lazy startup, the positions of its
canonical objects, and rule 4 for D (the D of the model's startup, which is the
run's: T1). -/
def evictStartup (sp : Spec V T) (S : Stream V T) : Mem V :=
  ((lazyStartup sp S).sectionPos S).linkD (startup sp S).D

/-! ## The physical writer -/

/-- The reference that the physical writer gives pointee y of object o (Java's
`resolvePointers` at Level 4): if y is pinned (in D, which here holds the nodes
in D before this record's writes, those taken by it included), the position of
its canonical object, a version written earlier in the same record included;
otherwise the slot's: the position of a memory slot's object, or a stream
slot's record after Rule R (of the last startup, S0). -/
def Mem.refOf (S0 : Stream V T) (m : Mem V) (D : Dirty) (o : Obj V) (y : NodeId) : Option Nat :=
  let fromSlot : Option Nat := match o.slot? y with
    | some (Slot.mem h) => (m.obj? h).bind (·.pos)
    | some (Slot.stream r) => ruleRRef S0 m.s y r
    | none => none
  if inD D y then
    match m.canonicalOf y with
    | some h => (m.obj? h).bind (·.pos)
    | none => fromSlot
  else fromSlot

/-- Write node x into record i from its canonical object: the version (the
object's history, and for each pointee the reference `refOf` gives) and the
memory after, where the object names record i and its slots to pinned
pointees are memory slots to their canonical objects, as `resolvePointers`
leaves them. none if x has no canonical object. -/
def Mem.writeNode (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat) (m : Mem V)
    (x : NodeId) : Mem V × Option (Version V) :=
  match m.canonicalOf x with
  | none => (m, none)
  | some h =>
    match m.obj? h with
    | none => (m, none)
    | some o =>
      let refs := (pointees sp o.hist).filterMap (fun y => (m.refOf S0 D o y).map (fun r => (y, r)))
      let v : Version V :=
        { node := x, recNo := i, level := o.level, isData := o.isData, hist := o.hist, refs := refs }
      let slots := o.slots.map (fun q =>
        if inD D q.1 then
          match m.canonicalOf q.1 with
          | some h0 => (q.1, Slot.mem h0)
          | none => q
        else q)
      (m.setObj h { o with pos := some i, slots := slots }, some v)

/-- Write the nodes xs in turn into record i: the memory after, and the
versions, in that order. -/
def Mem.writeNodes (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat) (m : Mem V)
    (xs : List NodeId) : Mem V × List (Version V) :=
  xs.foldl (fun (acc : Mem V × List (Version V)) x =>
    match acc.1.writeNode sp S0 D i x with
    | (m', some v) => (m', acc.2 ++ [v])
    | (m', none) => (m', acc.2)) (m, [])

/-- One transaction of BergDB's writer with eviction (Level 4), from the memory
m after the startup from S0 and the operations since: as `lazyTrans`, through
the Level 4 loader; then the versions of the record from the objects
(`writeNodes`), the data nodes the change creates first (step 2), then the taken
nodes (step 6); the rest is step's (steps 3 to 5, 7 and 8), with those
versions. T-CACHE is to say that the record is the model's. -/
def evictTrans (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (m : Mem V)
    (tr : T) : DB V T × Mem V :=
  let i := db.S.length
  let r := m.view4 sp S0 db.S (i - 1)
  let c := sp.exec tr i r.2
  let path := pathOf sp db.P c i
  let path' := path.mergeSort (fun a b => decide
    (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0))
  let m2 := path'.foldl (Mem.reachOnPath4 sp S0 db.S db.P i path) r.1
  let m3 := m2.applyChange4 sp db.P i c
  let P := db.P.apply i c
  -- 2. Write data, from the objects.
  let w2 := m3.writeNodes sp S0 db.D i ((c.new.filter (·.isData)).map (·.id))
  let vs0 := w2.2
  -- 3. to 5., as step.
  let gd3 := (if al.mark then markOf sp P c db.D i else gotDirtyOf sp (db.S.building vs0) P db.D i).filter
    (written sp)
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  -- 6. Write index, from the objects; D1 is the pinned set during the writes.
  let w6 := w2.1.writeNodes sp S0 D1 i taken
  let vs := vs0 ++ w6.2
  let S' : Stream V T := db.S.building vs
  -- 7. and 8., as step.
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s }
  ({ P := P, D := r7.1, S := db.S ++ [R] }, w6.1)

/-! ## Cache operations and runs -/

/-- An operation of a cache schedule, between transactions: a read at time t, the
unswizzling of the slot of object h for y, or the release of object h. An
operation that its conditions do not allow does nothing. -/
inductive CacheOp where
  | read (t : Time)
  | unswizzle (h : Nat) (y : NodeId)
  | release (h : Nat)
  deriving Repr

/-- The memory after cache operation op, with D the current D. -/
def Mem.cacheOp (sp : Spec V T) (S0 S : Stream V T) (D : Dirty) (m : Mem V) : CacheOp → Mem V
  | .read t => (m.read4 sp S0 S t).1
  | .unswizzle h y => m.unswizzle D h y
  | .release h => m.release D h

/-- A run with eviction: R(0) and the Level 4 startup from it; each transaction
by `evictTrans`, followed by its cache operations; after a transaction marked
true, a restart (the logical startup for ⟨P, D, S⟩, the Level 4 startup for the
memory, and its stream for Rule R), which drops the cache operations' effects
with the rest of memory. -/
def runEvict (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp)) :
    DB V T × Mem V × Stream V T :=
  ts.foldl (fun (acc : DB V T × Mem V × Stream V T) p =>
    let r := evictTrans sp al acc.2.2 acc.1 acc.2.1 p.1
    if p.2.1 then (startup sp r.1.S, evictStartup sp r.1.S, r.1.S) else
    (r.1, p.2.2.foldl (Mem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
    (init sp, evictStartup sp (init sp).S, (init sp).S)

/-! ## The assumptions of stage 2 -/

/-- TREE at time i: every node reachable at i, the root aside, is the live
child at i of exactly one node reachable at i (sis-model.md, section 11). -/
def treeAt (sp : Spec V T) (P : Struct V) (i : Time) : Prop :=
  ∀ y, reachable sp P i y = true → y ≠ root →
    ((reachList sp P i).eraseDups.filter (fun x => match P.get? x with
      | some n => (sp.live (n.hist.upTo i)).contains y
      | none => false)).length = 1

/-- A6' at time i (no adoption, the weaker form; docs/level4-alignment.md,
section 4): for every node x reachable at i and every pointee y of x that is
not a live child of x at i, y is a data node, or is not reachable at i, or is
reachable at i from x through live pointers (below x). -/
def adoptAt (sp : Spec V T) (P : Struct V) (i : Time) : Prop :=
  ∀ x n, reachable sp P i x = true → P.get? x = some n →
    ∀ y ∈ pointees sp n.hist, y ∉ sp.live (n.hist.upTo i) →
      (∃ ny, P.get? y = some ny ∧ ny.isData = true) ∨ reachable sp P i y = false ∨
        y ∈ reachFrom sp P i x n

/-- The assumptions of stage 2 at time i, on P after transaction i: TREE and
A6'. BergDB's Dag meets both (checked on Java by A4: TREE in every transaction,
A6' in every transaction of 68,901, where A6 fails in 5). -/
structure EvictStep (sp : Spec V T) (P : Struct V) (i : Time) : Prop where
  tree : treeAt sp P i
  adopt : adoptAt sp P i

/-- A-COPY for the change c at time i to P: a pointer of a new entry to a node
that c does not create names a node of the writer's paths, or a pointee at
i - 1 of one, live there if that node is a virtual root. This is what Java's
writer has in hand when it makes the pointer of a new klong: the object it
created or reached, or a pointer of a node it reached, which a split copies to
the new nodes and a new super root inherits (`TopDs.newSuperRoot`). The
physical writer has no other way to know a node's latest version (T-INDEX). -/
def CopyStep (sp : Spec V T) (P : Struct V) (i : Time) (c : Changes V) : Prop :=
  ∀ a ∈ c.adds, ∀ y ∈ sp.ptrs a.2, y ∉ c.new.map (·.id) →
    y ∈ pathOf sp P c i ∨ ∃ z ∈ pathOf sp P c i, ∃ nz, P.get? z = some nz ∧
      y ∈ pointees sp nz.hist ∧ (written sp z = true ∨ y ∈ sp.live (nz.hist.upTo (i - 1)))

/-- The assumptions of stage 2 hold in every transaction of a run: TREE and A6'
after it, A-COPY for its change. -/
def EvictRunOK (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
  (∀ j ≤ ts.length, EvictStep sp (run sp al (ts.take j)).P j) ∧
  ∀ j (h : j < ts.length),
    let db := run sp al (ts.take j)
    CopyStep sp db.P (j + 1) (sp.exec ts[j] (j + 1) (view sp db.P j))

end SIS
