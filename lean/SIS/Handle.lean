/-
Self-indexed streams in Lean: the physical layer with handles (bergdb item 009,
phase 2, step 2a; the design is items/009-handles/02-implementation-plan.md,
section 4, here called 02). Trusted part, like Evict.lean. Work in progress: the
statements are in HandleTheorems.lean, not yet proved.

Evict.lean models BergDB's memory as it is at Level 4: a pointer of an object
is a memory pointer to an object, or a stream pointer, and eviction unswizzles
memory pointers and releases objects that no memory pointer names. This file
models 009's design instead:

* A *handle* (02, 4.1) is one per index node that is resident or that a
  resident pointer names: the node id, the node's one object or none, the
  position this process last wrote the node at (`writtenPos`), and whether it
  is dead. One live handle per node, in the table (02, 4.3). A dead handle is
  never live again.
* A *pointer* of an object (02, 4.2) holds a reference, Java's `pos[i]`: the
  record of the version it names, or none for a vpos (a node not written when
  the pointer was written); never access data. And a handle, or none until the
  pointer is first followed.
* The objects are numbered. Phys.lean calls an object's number a handle
  (`Slot.mem h`); here it is an *address*, since a handle is 009's.

The operations, each mirroring one of Evict.lean:

* following a pointer (02, 4.4; `HMem.followR`, `HMem.follow`): the fast path,
  and the slow path: resolve (`HMem.resolve`), load and install (`HMem.load`);
* the writer's promote (02, 4.5; `HMem.promote`), its walk and its change
  (`HMem.reachOnPath`, `HMem.newPtr`, `HMem.applyChange`; A-COPY as in
  Evict.lean);
* the record rule (02, 4.6; `HMem.ptrRef`, `HMem.refOf`) and the physical
  writer (`HMem.writeNode`, `HMem.writeNodes`, `handleTrans`);
* eviction (02, 4.7; `HMem.evictable`, `HMem.evict`);
* startup (02, 4.9; `handleStartup`): stage 1's reads unchanged, then rule 4,
  D's pointers resolved to handles by node id (`HMem.linkD`);
* runs with reads and evictions between transactions (`HCacheOp`,
  `runHandles`).

Where 02 is vague, the model takes the simplest option that is faithful to it,
and says so in the comment of the definition. The choices:

1. A re-resolve keeps the written position: when a pointer that holds a dead
   handle is resolved to the node's live handle, the live handle's written
   position becomes the larger of its own and the dead handle's
   (`HMem.resolve`). 02 does not say this; without it, the record rule of 4.6
   and the slow path lose the position this process last wrote the node at
   (HandleExample.lean has the case, and counts it in its runs; runs of the
   model without it give wrong records and reads). So readers change a written
   position too, which 02 (4.6) says they do not: only to the larger of two
   positions at which this process wrote the node.
2. The writer's `resolvePointers` (`HMem.writeNode`): a pinned pointee's
   pointer takes the node's live handle (by id) and, as its reference, the
   position of the node's canonical object, which is what the record names for
   it (02, 4.2: `pos[i]` holds the reference the pointer was "last resolved by
   the writer" with); any other pointer's reference is set to its reference
   after Rule R, as today. Keeping the old reference of a pinned pointee's
   pointer gives the same records and reads in the runs of HandleExample.lean,
   but leaves more pointers whose reference is older than their record, or a
   vpos, which the fast path sends to the slow path.
3. A vpos is none, below every position: the larger of a vpos and a position is
   the position (`maxRef`), and Rule R replaces a vpos by the newest version in
   the startup section, as Rule R does in the model (`ruleRRef`).
4. There are no readers in the middle of an operation, so an object that leaves
   its handle (a newer version installed, or an eviction) leaves memory. Java's
   garbage collector keeps it for a reader that still holds it.
5. Data nodes (BergDB's values) get handles like index nodes. Java keeps
   direct pointers from leaves to values (02, 4.8); a data node has one
   version, so its references are the same either way.
6. A load that finds no version (Java throws) changes nothing.
7. The slow path compares the handle's object with the larger of the
   pointer's reference after Rule R and the live handle's written position,
   which a re-resolve may just have raised (choice 1); 02 compares with the
   reference after Rule R only (4.4, step 2). With 02's test, a snapshot older
   than the version this process last wrote, which a reader installed through
   an older pointer after an eviction, serves a pointer whose record is that
   newer version: reads at the last time and the writer's view then go wrong,
   and so do the records (HandleExample.lean has the case; runs of the model
   with 02's test found it).

Left out, as in Evict.lean: concurrency (the fast path's barriers of 02, 3.3
and 3.4, the handle's LOADING state, the monitors and the map locks: every
operation here is atomic), the CLOCK bit and the order of eviction (any
schedule of evictions is allowed), bytes and the accounting, the eviction
thread, and the search of the TopDs skip list (the root's object stands for
it).
-/
import SIS.Evict

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The state -/

/-- The larger of two references, none (a vpos) below every position. The
record rule of 02, 4.6, takes the larger of a pointer's reference after Rule R
and its handle's written position; a vpos never wins (choice 3 of the header). -/
def maxRef : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, b => b

/-- A pointer of an object for one pointee (Java's pair `pointers[i]` and
`pos[i]`, 02, 4.2): `ref`, the serialized reference that the pointer was made,
loaded or last resolved by the writer with (the record of a version, or none for
a vpos); and `handle`, the number of a handle, or none until the pointer is
first followed. Readers change only `handle`. -/
structure HPtr where
  ref : Option Nat
  handle : Option Nat
  deriving DecidableEq, Repr

/-- An object in memory, a Java `Node` object, with pointers that hold handles:
as Evict.lean's `Obj`, with `ptrs` for its `slots`. `canonical` and `pos` are
Java's `isCanonical()` and `spos`. One pointer for each pointee of the history,
live or dead. -/
structure HObj (V : Type) where
  node : NodeId
  level : Nat
  isData : Bool
  hist : History V
  canonical : Bool
  pos : Option Nat
  ptrs : List (NodeId × HPtr)
  deriving Repr

/-- A handle (02, 4.1, Java's `Handle`): the node id (Java's final `id`), the
address of the node's one object or none (`obj`), the record this process last
wrote the node in or none (Java's `writtenPos`), and whether it is dead. A dead
handle has no object and is not in the table; it is never live again. The
LOADING state and the CLOCK bit are left out (see the header). -/
structure Handle where
  node : NodeId
  obj : Option Nat
  written : Option Nat
  dead : Bool
  deriving DecidableEq, Repr

/-- Java's memory with handles: the objects by address; the handles by number;
the table (02, 4.3), from node id to the node's live handle; Rule R's startup
pos of the last startup, as in Evict.lean; the address of the root's object;
the next free address and handle number. -/
structure HMem (V : Type) where
  objs : List (Nat × HObj V)
  handles : List (Nat × Handle)
  table : List (NodeId × Nat)
  s : Nat
  root : Nat
  nextObj : Nat
  nextHandle : Nat

/-- The object at address a. -/
def HMem.obj? (m : HMem V) (a : Nat) : Option (HObj V) := m.objs.lookup a

/-- Replace the object at address a. -/
def HMem.setObj (m : HMem V) (a : Nat) (o : HObj V) : HMem V :=
  { m with objs := (a, o) :: m.objs.filter (fun p => p.1 != a) }

/-- The object at address a leaves memory. -/
def HMem.dropObj (m : HMem V) (a : Nat) : HMem V :=
  { m with objs := m.objs.filter (fun p => p.1 != a) }

/-- Handle number n. -/
def HMem.handle? (m : HMem V) (n : Nat) : Option Handle := m.handles.lookup n

/-- Replace handle number n. -/
def HMem.setHandle (m : HMem V) (n : Nat) (hd : Handle) : HMem V :=
  { m with handles := (n, hd) :: m.handles.filter (fun p => p.1 != n) }

/-- The table's handle for node y: its live handle. -/
def HMem.tableOf (m : HMem V) (y : NodeId) : Option Nat := m.table.lookup y

/-- Set the table's handle for node y. -/
def HMem.setTable (m : HMem V) (y : NodeId) (n : Nat) : HMem V :=
  { m with table := (y, n) :: m.table.filter (fun p => p.1 != y) }

/-- The address of the object that handle n holds, if any. -/
def HMem.objOf (m : HMem V) (n : Nat) : Option Nat := (m.handle? n).bind (·.obj)

/-- The canonical object of node y, by address: the object of y's live handle,
if it is canonical. One live handle per node gives one canonical object per
node (02, 4.5). -/
def HMem.canonicalOf (m : HMem V) (y : NodeId) : Option Nat :=
  match (m.tableOf y).bind m.objOf with
  | some a => match m.obj? a with
    | some o => if o.canonical then some a else none
    | none => none
  | none => none

/-- The pointer of an object for pointee y. -/
def HObj.ptr? (o : HObj V) (y : NodeId) : Option HPtr := o.ptrs.lookup y

/-- Set the pointer of an object for pointee y (Java's `setPointer`, or the
resolver's compareAndSet). -/
def HObj.setPtr (o : HObj V) (y : NodeId) (p : HPtr) : HObj V :=
  { o with ptrs := o.ptrs.map (fun q => if q.1 == y then (y, p) else q) }

/-- Give an object the pointer p for pointee y: replace its pointer for y, or
add one. -/
def HObj.putPtr (o : HObj V) (y : NodeId) (p : HPtr) : HObj V :=
  if (o.ptr? y).isSome then o.setPtr y p else { o with ptrs := o.ptrs ++ [(y, p)] }

/-- The node that object o gives at time t: its level and kind, its history
at t. -/
def HObj.nodeAt (o : HObj V) (t : Time) : Node V :=
  { level := o.level, isData := o.isData, hist := o.hist.upTo t }

/-- The object read from version w (`StoredKeyNode.parse`, `StoredTopNode.parse`):
its history, its record, and for each pointee of that history a pointer with
w's reference and no handle. A snapshot, not cut back (the Level 4 loader). -/
def HObj.ofVersion (sp : Spec V T) (w : Version V) : HObj V :=
  { node := w.node, level := w.level, isData := w.isData, hist := w.hist, canonical := false,
    pos := some w.recNo,
    ptrs := (pointees sp w.hist).map (fun y => (y, ({ ref := w.ref? y, handle := none } : HPtr))) }

/-- Object o can serve a pointer whose reference is r: it is canonical, or a
snapshot at least as new as r. A vpos (none) is served only by a canonical
object. The fast path's test (02, 4.4) with r the pointer's own reference; the
slow path's with the larger of r after Rule R and the handle's written
position (choice 7 of the header). -/
def HObj.usable (o : HObj V) (r : Option Nat) : Bool :=
  o.canonical || match r, o.pos with
    | some r, some p => decide (r ≤ p)
    | _, _ => false

/-! ## Following a pointer (02, 4.4) -/

/-- The slow path's step 1, resolve (02, 4.4), for the pointer of the object
at address a for pointee y. If the pointer holds a live handle, that one.
Otherwise (no handle, or a dead one): the node's live handle from the table, by
node id (Java: a vpos is the id, else the dead handle's id, else the header at
`pos[i]`; the model's pointer knows its pointee), or a new live handle with no
object, entered in the table; the pointer then holds it (Java: compareAndSet).
Returns the memory after and the live handle.

Choice 1 of the header: when the pointer held a dead handle, the live handle's
written position becomes the larger of its own and the dead handle's. 02 says
that the slow path reads "the newest this process wrote, `writtenPos`", but not
how a new handle learns it; the dead handle is the only place that knows it,
and the record rule (02, 4.6) reads the written position of the handle the
pointer holds, which is now the live one. -/
def HMem.resolve (m : HMem V) (a : Nat) (y : NodeId) : HMem V × Nat :=
  let cur : Option Nat := ((m.obj? a).bind (·.ptr? y)).bind (·.handle)
  let live : Option Nat := match cur with
    | some n => match m.handle? n with
      | some hd => if hd.dead then none else some n
      | none => none
    | none => none
  match live with
  | some n => (m, n)
  | none =>
    -- The written position of the dead handle the pointer holds, if any.
    let wpDead : Option Nat := (cur.bind m.handle?).bind (·.written)
    -- The node's live handle, the table's, or a new one.
    let r1 : HMem V × Nat := match m.tableOf y with
      | some n => match m.handle? n with
        | some hd => (m.setHandle n { hd with written := maxRef hd.written wpDead }, n)
        | none => (m, n)
      | none =>
        let n := m.nextHandle
        let m' := (m.setHandle n { node := y, obj := none, written := wpDead, dead := false }).setTable y n
        ({ m' with nextHandle := n + 1 }, n)
    -- The pointer takes it.
    let m2 := match r1.1.obj? a with
      | some o => match o.ptr? y with
        | some p => r1.1.setObj a (o.setPtr y { p with handle := some r1.2 })
        | none => r1.1
      | none => r1.1
    (m2, r1.2)

/-- The slow path's step 2, load and install (02, 4.4), on the live handle n:
the handle's object if it can serve the reference `target` (`HObj.usable`);
otherwise the version at the larger of `target` and the handle's written
position ("the pointer's, or the newest this process wrote, if newer"), read
from the stream S exactly (a snapshot, not cut back), installed in the handle
in place of the object it held, which leaves memory (choice 4 of the header).
The readers' slow path and the writer's promote pass the larger of the
pointer's reference after Rule R and the handle's written position as `target`
(choice 7 of the header). Returns the memory after and the address of the
object; none if there is no version to read (Java throws; choice 6). In Java
the loader holds the handle's monitor, with the state LOADING; here the load is
atomic, so the handle is still live and "a canonical or newer object got there
first" cannot happen. -/
def HMem.load (sp : Spec V T) (S : Stream V T) (m : HMem V) (n : Nat) (target : Option Nat) :
    HMem V × Option Nat :=
  match m.handle? n with
  | none => (m, none)
  | some hd =>
    let cur : Option Nat := match hd.obj with
      | some b => match m.obj? b with
        | some o => if o.usable target then some b else none
        | none => none
      | none => none
    match cur with
    | some b => (m, some b)
    | none =>
      match maxRef target hd.written with
      | none => (m, none)
      | some r =>
        match S.versionAt r hd.node with
        | none => (m, none)
        | some w =>
          let b := m.nextObj
          let m1 := match hd.obj with
            | some old => m.dropObj old
            | none => m
          let m2 : HMem V := { m1 with objs := (b, HObj.ofVersion sp w) :: m1.objs, nextObj := b + 1 }
          (m2.setHandle n { hd with obj := some b }, some b)

/-- The readers' follow of the pointer of the object at address a for pointee
y (02, 4.4). The fast path: the pointer holds a handle, the handle holds an
object, and the object is canonical or at least as new as the pointer's own
reference, without Rule R and without the written position (`HObj.usable`);
then nothing changes (Java sets the CLOCK bit, left out). A dead handle holds no
object, so it fails the test, as in Java, which reads only the handle's object.
Otherwise the slow path: resolve, then load with the larger of the pointer's
reference after Rule R, of the last startup (its stream S0), and the live
handle's written position (choice 7 of the header). Versions are read from S,
the stream now, as in Evict.lean's `follow4`. Returns the memory after, the live
handle and the address of the object reached; none if there is no such pointer
or nothing to read.

Open point 1 of 02 (section 7), Rule R on the fast path, is this test: it
compares with the pointer's own reference only. HandleTheorems.lean states why
that is enough (`HRuleROK`, `HSnapWrittenOK`, `HFastOK`): every snapshot in a
handle was loaded after the last startup by the slow path, so it is at least as
new as its node's newest version in the startup section and as its handle's
written position; for a reference that is not a vpos, the fast path's test then
gives the slow path's answer. -/
def HMem.followR (sp : Spec V T) (S0 S : Stream V T) (m : HMem V) (a : Nat) (y : NodeId) :
    Option (HMem V × Nat × Nat) :=
  match (m.obj? a).bind (·.ptr? y) with
  | none => none
  | some p =>
    let fast : Option (Nat × Nat) := match p.handle with
      | some n => match m.objOf n with
        | some b => match m.obj? b with
          | some o => if o.usable p.ref then some (n, b) else none
          | none => none
        | none => none
      | none => none
    match fast with
    | some nb => some (m, nb.1, nb.2)
    | none =>
      let r1 := m.resolve a y
      let wp : Option Nat := (r1.1.handle? r1.2).bind (·.written)
      match r1.1.load sp S r1.2 (maxRef (ruleRRef S0 m.s y p.ref) wp) with
      | (m2, some b) => some (m2, r1.2, b)
      | (_, none) => none

/-- The writer's promote (02, 4.5; Evict.lean's `Mem.promote`), after its
follow of the pointer of the object at address a for pointee y has reached
the live handle n: the handle's object, if canonical. Otherwise it is lv(y) or
older: if it is older than the larger of the pointer's reference after Rule R
and the handle's written position (which is lv(y) for the pointers the writer
follows; the invariant `HSlotOK` of HandleTheorems.lean), the writer loads that
version (`HMem.load`), and then marks the handle's object canonical. One live
handle per node gives one canonical object per node. -/
def HMem.promote (sp : Spec V T) (S0 S : Stream V T) (m : HMem V) (a : Nat) (y : NodeId)
    (n : Nat) : HMem V × Option Nat :=
  let r : Option Nat := ((m.obj? a).bind (·.ptr? y)).bind (·.ref)
  let target := maxRef (ruleRRef S0 m.s y r) ((m.handle? n).bind (·.written))
  match m.load sp S n target with
  | (m1, some b) => match m1.obj? b with
    | some o => (m1.setObj b { o with canonical := true }, some b)
    | none => (m1, some b)
  | (_, none) => (m, none)

/-- Follow the pointer of the object at address a for pointee y: the readers'
follow, then, for the writer, its promote (02, 4.5: "follows as a reader, then
needs the canonical object"). Returns the memory after and the address of the
object reached; none if there is no such pointer or nothing to read. -/
def HMem.follow (sp : Spec V T) (S0 S : Stream V T) (m : HMem V) (a : Nat) (y : NodeId)
    (writer : Bool) : HMem V × Option Nat :=
  match m.followR sp S0 S a y with
  | none => (m, none)
  | some (m1, n, b) => if writer then m1.promote sp S0 S a y n else (m1, some b)

/-- Read at time t from the object at address a, down, through the handles: as
Evict.lean's `Mem.readAt4`. Each object reached, by node, with the node it gives
at t; the memory after the follows on the way. A pointer to an object that is
not on a lower level is not followed. fuel bounds the depth. -/
def HMem.readAt (sp : Spec V T) (S0 S : Stream V T) : Nat → HMem V → Time → Nat →
    HMem V × List (NodeId × Node V)
  | 0, m, _, _ => (m, [])
  | fuel + 1, m, t, a =>
    match m.obj? a with
    | none => (m, [])
    | some o =>
      (sp.live (o.hist.upTo t)).foldl (fun (acc : HMem V × List (NodeId × Node V)) y =>
        match acc.1.follow sp S0 S a y false with
        | (m1, some b) =>
          match m1.obj? b with
          | some o1 =>
            if o1.level < o.level then
              let r := HMem.readAt sp S0 S fuel m1 t b
              (r.1, acc.2 ++ r.2)
            else (m1, acc.2)
          | none => (m1, acc.2)
        | (m1, none) => (m1, acc.2)) (m, [(o.node, o.nodeAt t)])

/-- A read at time t from the root's object. -/
def HMem.read (sp : Spec V T) (S0 S : Stream V T) (m : HMem V) (t : Time) :
    HMem V × List (NodeId × Node V) :=
  match m.obj? m.root with
  | some o => m.readAt sp S0 S (o.level + 1) t m.root
  | none => (m, [])

/-- The writer's view of P at time t through the handles. -/
def HMem.view (sp : Spec V T) (S0 S : Stream V T) (m : HMem V) (t : Time) : HMem V × View V :=
  let r := m.read sp S0 S t
  (r.1, fun x => r.2.lookup x)

/-! ## The writer's walk and change (02, 4.5) -/

/-- The writer reaches node x of the path, as Evict.lean's `Mem.reachOnPath4`:
from the canonical object of the node of the path that x is a live child of at
j - 1, through that object's pointer (the writer's follow, which promotes). -/
def HMem.reachOnPath (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (j : Time)
    (path : List NodeId) (m : HMem V) (x : NodeId) : HMem V :=
  let parent := path.find? (fun p => match P.get? p, m.canonicalOf p with
    | some n, some _ => (sp.live (n.hist.upTo (j - 1))).contains x
    | _, _ => false)
  match parent with
  | some p => match m.canonicalOf p with
    | some a => (m.follow sp S0 S a x true).1
    | none => m
  | none => m

/-- An object that a new pointer to y may copy its pointer from, as Evict.lean's
`srcOK4`: a canonical object of a node reachable at j - 1, with y a pointee of
its history and a pointer for it; if it is a virtual root's, with y a live child
of it at j - 1. -/
def srcOKH (sp : Spec V T) (P : Struct V) (j : Time) (y : NodeId) (p : Nat × HObj V) : Bool :=
  p.2.canonical && (p.2.ptr? y).isSome && (pointees sp p.2.hist).contains y &&
    reachable sp P (j - 1) p.2.node &&
    (written sp p.2.node || match P.get? p.2.node with
      | some n => (sp.live (n.hist.upTo (j - 1))).contains y
      | none => false)

/-- The pointer that a new pointer of object o to y gets, as Evict.lean's
`newSlot4`: if y has a canonical object, y's live handle, with that object's
position as the reference (02, 4.5: `pointerCreated` becomes "the pointee's
live handle into the pointer"); else a copy of the pointer for y of an object
that `srcOKH` allows, the pair as it is (02, 4.2: "a split copies the pairs
(handle, reference)"); else o's own pointer for y; else none. -/
def HMem.newPtr (sp : Spec V T) (P : Struct V) (j : Time) (m : HMem V) (o : HObj V) (y : NodeId) :
    Option HPtr :=
  match m.canonicalOf y with
  | some b => some { ref := (m.obj? b).bind (·.pos), handle := m.tableOf y }
  | none =>
    match m.objs.find? (srcOKH sp P j y) with
    | some p => p.2.ptr? y
    | none => o.ptr? y

/-- Apply the change c of transaction j to the canonical objects, as
Evict.lean's `Mem.applyChange4`: for each new node a new canonical object, with
a new live handle in the table at once (02, 4.5: "a node the writer makes gets
its handle at once"); the entries appended; and for each pointee of a new entry
the pointer of `newPtr`, taken from the memory as it was before the entries. -/
def HMem.applyChange (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : HMem V) :
    HMem V :=
  let m1 := c.new.foldl (fun (m : HMem V) nn =>
    let o : HObj V :=
      { node := nn.id, level := nn.level, isData := nn.isData, hist := [], canonical := true,
        pos := none, ptrs := [] }
    let a := m.nextObj
    let n := m.nextHandle
    let m' : HMem V := { m with objs := (a, o) :: m.objs, nextObj := a + 1, nextHandle := n + 1 }
    (m'.setHandle n { node := nn.id, obj := some a, written := none, dead := false }).setTable nn.id n) m
  c.adds.foldl (fun (m : HMem V) e =>
    match m.canonicalOf e.1 with
    | none => m
    | some a =>
      match m.obj? a with
      | none => m
      | some o =>
        let o1 := { o with hist := o.hist ++ [⟨j, e.2⟩] }
        let o2 := (sp.ptrs e.2).foldl (fun (o' : HObj V) y =>
          match m1.newPtr sp P j o' y with
          | some p => o'.putPtr y p
          | none => o') o1
        m.setObj a o2) m1

/-! ## Records (02, 4.6) -/

/-- The serialized reference of pointer p to node y, the record rule of 02, 4.6,
without the rule for pinned pointees: the position of the canonical object if
p's handle holds a canonical object; else the larger of p's reference after Rule
R (of the last startup, S0) and the handle's written position; with no handle,
the reference after Rule R. A vpos (none) is below every position (`maxRef`).

Open point 3 of 02 (section 7), a vpos in `pos[i]`: Rule R replaces a vpos by
the newest version in the startup section, if there is one (`ruleRRef`); and in
the larger of the two, a vpos never wins. HandleExample.lean has runs in which a
pointer's reference is a vpos and its record is its handle's written position;
Java's rule must not compare such a vpos with the written position as numbers
unless a vpos is always below the positions its node is written at. -/
def HMem.ptrRef (S0 : Stream V T) (m : HMem V) (y : NodeId) (p : HPtr) : Option Nat :=
  let rr := ruleRRef S0 m.s y p.ref
  match p.handle.bind m.handle? with
  | some hd =>
    match hd.obj.bind m.obj? with
    | some o => if o.canonical then o.pos else maxRef rr hd.written
    | none => maxRef rr hd.written
  | none => rr

/-- The reference that the physical writer gives pointee y of object o (02, 4.6;
Evict.lean's `Mem.refOf`): if y is pinned (in D, which holds the nodes in D
before this record's writes, those taken by it included), the position of its
canonical object, found by node id (`resolvePointers` keeps this rule); otherwise
the record rule for o's pointer for y (`ptrRef`). Readers change neither a
pointer's reference nor a written position; they change which handle a pointer
holds, which the record rule reads too. -/
def HMem.refOf (S0 : Stream V T) (m : HMem V) (D : Dirty) (o : HObj V) (y : NodeId) : Option Nat :=
  let fromPtr : Option Nat := (o.ptr? y).bind (m.ptrRef S0 y)
  if inD D y then
    match m.canonicalOf y with
    | some b => (m.obj? b).bind (·.pos)
    | none => fromPtr
  else fromPtr

/-- Write node x into record i from its canonical object (Evict.lean's
`Mem.writeNode`): the version (the object's history, and for each pointee the
reference `refOf` gives) and the memory after. The object names record i, and
its node's live handle gets record i as its written position (02, 4.5: "when the
writer writes a node, it sets the handle's writtenPos"). Choice 2 of the header,
Java's `resolvePointers` with handles: a pointer to a pinned pointee that has a
canonical object takes that node's live handle, and that object's position as
its reference (what the version names); the reference of any other pointer
becomes its reference after Rule R, as today's `resolvePointers` does for a
stream pointer. none if x has no canonical object. -/
def HMem.writeNode (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat) (m : HMem V)
    (x : NodeId) : HMem V × Option (Version V) :=
  match m.canonicalOf x with
  | none => (m, none)
  | some a =>
    match m.obj? a with
    | none => (m, none)
    | some o =>
      let refs := (pointees sp o.hist).filterMap (fun y => (m.refOf S0 D o y).map (fun r => (y, r)))
      let v : Version V :=
        { node := x, recNo := i, level := o.level, isData := o.isData, hist := o.hist, refs := refs }
      let ptrs := o.ptrs.map (fun q =>
        if inD D q.1 then
          match m.canonicalOf q.1 with
          | some b => (q.1, { ref := (m.obj? b).bind (·.pos), handle := m.tableOf q.1 })
          | none => q
        else (q.1, { q.2 with ref := ruleRRef S0 m.s q.1 q.2.ref }))
      let m1 := m.setObj a { o with pos := some i, ptrs := ptrs }
      let m2 := match m1.tableOf x with
        | some n => match m1.handle? n with
          | some hd => m1.setHandle n { hd with written := some i }
          | none => m1
        | none => m1
      (m2, some v)

/-- Write the nodes xs in turn into record i: the memory after, and the
versions, in that order. -/
def HMem.writeNodes (sp : Spec V T) (S0 : Stream V T) (D : Dirty) (i : Nat) (m : HMem V)
    (xs : List NodeId) : HMem V × List (Version V) :=
  xs.foldl (fun (acc : HMem V × List (Version V)) x =>
    match acc.1.writeNode sp S0 D i x with
    | (m', some v) => (m', acc.2 ++ [v])
    | (m', none) => (m', acc.2)) (m, [])

/-- One transaction of BergDB's writer with handles, from the memory m after
the startup from S0 and the operations since: Evict.lean's `evictTrans`, word for
word, through the handles: the view, the walk highest level first, the change,
then the versions of the record from the objects (`writeNodes`), the data nodes
the change creates first (step 2), then the taken nodes (step 6); the rest is
step's. T-CACHE for handles (`TC_handles`, HandleTheorems.lean) is to say that
the record is the model's. -/
def handleTrans (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (m : HMem V)
    (tr : T) : DB V T × HMem V :=
  let i := db.S.length
  let r := m.view sp S0 db.S (i - 1)
  let c := sp.exec tr i r.2
  let path := pathOf sp db.P c i
  let path' := path.mergeSort (fun a b => decide
    (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0))
  let m2 := path'.foldl (HMem.reachOnPath sp S0 db.S db.P i path) r.1
  let m3 := m2.applyChange sp db.P i c
  let P := db.P.apply i c
  -- 2. Write data, from the objects.
  let w2 := m3.writeNodes sp S0 db.D i ((c.new.filter (·.isData)).map (·.id))
  let vs0 := w2.2
  -- 3. to 5., as step.
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let fa : Nat := firstAvail al db.S D1 i tr s
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  -- 6. Write index, from the objects; D1 is the pinned set during the writes.
  let w6 := w2.1.writeNodes sp S0 D1 i taken
  let vs := vs0 ++ w6.2
  let S' : Stream V T := db.S.building vs
  -- 7. and 8., as step.
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s, fa := fa }
  ({ P := P, D := r7.1, S := db.S ++ [R] }, w6.1)

/-! ## Eviction (02, 4.7) -/

/-- The pinned objects, as Evict.lean's `Mem.pinned`: the canonical objects of
the nodes of D, and the root's object. (Java pins more, which the model treats
as atomic: the record being written, the newest written top node, the objects
of an operation in progress.) -/
def HMem.pinned (m : HMem V) (D : Dirty) (a : Nat) : Bool :=
  a == m.root || match m.obj? a with
    | some o => o.canonical && inD D o.node
    | none => false

/-- Handle n may be evicted (02, 4.7): it is live, and its object is not pinned
and is written (it has a position). Nothing is asked about the pointers that
hold the handle. -/
def HMem.evictable (m : HMem V) (D : Dirty) (n : Nat) : Bool :=
  match m.handle? n with
  | some hd => !hd.dead && match hd.obj with
    | some a => match m.obj? a with
      | some o => !m.pinned D a && o.pos.isSome
      | none => false
    | none => false
  | none => false

/-- Evict handle n, if it may be evicted (02, 4.7, `evict(h)`): the handle dies;
its written position is set from a canonical object's position (a snapshot's
leaves it as it is); it holds no object; the table's entry goes; the object
leaves memory (Java also clears its canonical flag, since a reader may still
hold it; choice 4 of the header). Otherwise nothing changes. Local: no walk,
nothing about incoming pointers. -/
def HMem.evict (m : HMem V) (D : Dirty) (n : Nat) : HMem V :=
  if m.evictable D n then
    match m.handle? n with
    | some hd =>
      match hd.obj with
      | some a =>
        let wp : Option Nat := match m.obj? a with
          | some o => if o.canonical then o.pos else hd.written
          | none => hd.written
        let m1 := m.setHandle n { hd with obj := none, written := wp, dead := true }
        { m1 with objs := m1.objs.filter (fun p => p.1 != a),
                  table := m1.table.filter (fun p => p.2 != n) }
      | none => m
    | none => m
  else m

/-! ## Startup (02, 4.9) -/

/-- The memory with handles that holds the objects of Evict.lean's memory m
(after a startup, where every object is canonical and the node table's): each
object that the node table names keeps its address and gets a live handle, the
table's for its node, with the same number as the address and no written
position (nothing written by this process yet); a memory slot to such an object
becomes a pointer that holds its handle, with the object's position as its
reference (what the slot serializes); a stream slot becomes a pointer with the
slot's reference and no handle. An object that the node table does not name is
left out (after a startup there is none). -/
def Mem.toH (m : Mem V) : HMem V :=
  let held := fun (a : Nat) => m.table.any (fun e => e.2 == a)
  let ptrOf := fun (q : NodeId × Slot) => match q.2 with
    | Slot.mem a =>
      (q.1, ({ ref := (m.obj? a).bind (·.pos), handle := if held a then some a else none } : HPtr))
    | Slot.stream r => (q.1, ({ ref := r, handle := none } : HPtr))
  { objs := (m.objs.filter (fun p => held p.1)).map (fun p =>
      (p.1, ({ node := p.2.node, level := p.2.level, isData := p.2.isData, hist := p.2.hist,
               canonical := p.2.canonical, pos := p.2.pos, ptrs := p.2.slots.map ptrOf } : HObj V))),
    handles := m.table.map (fun e =>
      (e.2, ({ node := e.1, obj := some e.2, written := none, dead := false } : Handle))),
    table := m.table,
    s := m.s, root := m.root, nextObj := m.next, nextHandle := m.next }

/-- Rule 4 with handles (02, 4.9; Evict.lean's `Mem.linkD`): each pointer of a
pinned object (the canonical object of a node of D, or the root's object) that
holds no handle, to a node that has a canonical object, takes that node's live
handle, by node id; its reference stays. -/
def HMem.linkD (m : HMem V) (D : Dirty) : HMem V :=
  { m with objs := m.objs.map (fun p =>
      if !(p.2.canonical && (inD D p.2.node || p.1 == m.root)) then p else
      (p.1, { p.2 with ptrs := p.2.ptrs.map (fun q => match q.2.handle with
        | none => match m.canonicalOf q.1 with
          | some _ => (q.1, { q.2 with handle := m.tableOf q.1 })
          | none => q
        | some _ => q) })) }

/-- Java's startup from S with handles (02, 4.9: "Unchanged reads. Rule 4 ...
D's pointers resolved to their nodes' handles by id"): stage 1's lazy startup
and the positions of its canonical objects, as in Evict.lean's `evictStartup`;
the handles (`Mem.toH`); and rule 4 with handles for D (the D of the model's
startup) and the root's object. -/
def handleStartup (sp : Spec V T) (S : Stream V T) : HMem V :=
  (((lazyStartup sp S).sectionPos S).toH).linkD (startup sp S).D

/-! ## Cache operations and runs -/

/-- An operation between transactions, with handles: a read at time t, or the
eviction of handle n. An eviction that `HMem.evictable` does not allow does
nothing. (Evict.lean's `CacheOp` has unswizzles and releases instead.) -/
inductive HCacheOp where
  | read (t : Time)
  | evict (n : Nat)
  deriving Repr

/-- The memory after operation op, with D the current D. -/
def HMem.cacheOp (sp : Spec V T) (S0 S : Stream V T) (D : Dirty) (m : HMem V) : HCacheOp → HMem V
  | .read t => (m.read sp S0 S t).1
  | .evict n => m.evict D n

/-- A run with handles, as Evict.lean's `runEvict`: R(0) and the startup with
handles from it; each transaction by `handleTrans`, followed by its operations;
after a transaction marked true, a restart (the logical startup for ⟨P, D, S⟩,
the startup with handles for the memory, and its stream for Rule R). -/
def runHandles (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp)) :
    DB V T × HMem V × Stream V T :=
  ts.foldl (fun (acc : DB V T × HMem V × Stream V T) p =>
    let r := handleTrans sp al acc.2.2 acc.1 acc.2.1 p.1
    if p.2.1 then (startup sp r.1.S, handleStartup sp r.1.S, r.1.S) else
    (r.1, p.2.2.foldl (HMem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
    (init sp, handleStartup sp (init sp).S, (init sp).S)

end SIS
