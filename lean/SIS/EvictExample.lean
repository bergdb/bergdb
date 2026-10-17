/-
The physical layer with eviction by running (bergdb item 001, WP E2): the
invariants of docs/level4-alignment.md, section 5.3, and the records and reads of
runs with cache schedules, with `#guard` checks. Not part of the trusted part.
-/
import SIS.Evict
import SIS.PhysExample

namespace SIS.EvictExample

open SIS SIS.Example SIS.PhysExample

variable {T : Type}

/-! ## The invariants by running -/

/-- The record of the latest version of y. -/
def lvRec (S : SIS.Stream Val T) (y : NodeId) : Option Nat := (S.lv y).map (·.recNo)

/-- INV-CAN: one canonical object per node, the node table's; each holds its
node's whole history; every node of D has one; a written canonical object of a
node not in D holds its node's latest version. -/
def invCanB (db : DB Val T) (m : Mem Val) : Bool :=
  let canon := m.objs.filter (·.2.canonical)
  canon.all (fun p => m.tableOf p.2.node == some p.1) &&
  (canon.map (·.2.node)).eraseDups.length == canon.length &&
  canon.all (fun p => ((db.P.get? p.2.node).map (·.hist)) == some p.2.hist) &&
  db.D.all (fun e => (m.canonicalOf e.1).isSome) &&
  canon.all (fun p => inD db.D p.2.node || p.2.pos.isNone ||
    (p.2.pos == lvRec db.S p.2.node && ((db.S.lv p.2.node).map (·.hist)) == some p.2.hist))

/-- INV-SNAP: every other object is the version of S at its position. -/
def invSnapB (db : DB Val T) (m : Mem Val) : Bool :=
  m.objs.all (fun p => p.2.canonical || match p.2.pos with
    | some r => match db.S.versionAt r p.2.node with
      | some w => w.hist == p.2.hist
      | none => false
    | none => false)

/-- No dangling slot: every memory slot names an object in memory, of its
pointee. -/
def noDanglingB (m : Mem Val) : Bool :=
  m.objs.all (fun p => p.2.slots.all (fun q => match q.2 with
    | .mem h => match m.obj? h with
      | some o => o.node == q.1
      | none => false
    | .stream _ => true))

/-- INV-SLOT (design, 5.4): for every canonical object of a node that is
current at the last time or in D (a virtual root aside, which is never
written), and every pointee y: the slot serializes lv(y), or y is in D; and if y
is in D and the slot is not a memory slot to y's canonical object, the object's
node is in D with an index at most y's (it is written no later than y). -/
def invSlotB (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : Mem Val) : Bool :=
  let k := db.S.length - 1
  let dOf := fun x => (db.D.find? (·.1 == x)).map (·.2)
  m.objs.all (fun p =>
    let o := p.2
    !o.canonical || (sp.virt && o.node == root) ||
    !(reachable sp db.P k o.node || inD db.D o.node) ||
    (pointees sp o.hist).all (fun y =>
      let ser := m.refOf S0 [] o y
      let memCanon := match o.slot? y with
        | some (.mem h) => m.canonicalOf y == some h
        | _ => false
      (inD db.D y || ser == lvRec db.S y) &&
      (!inD db.D y || memCanon ||
        (inD db.D o.node && match dOf o.node, dOf y with
          | some a, some b => decide (a ≤ b)
          | _, _ => false))))

/-- Reads at the times ts through the Level 4 loader, one after the other on
the same memory; the memory after, and whether each read gave P at its time. -/
def reads4 (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : Mem Val)
    (ts : List Time) : Mem Val × Bool :=
  ts.foldl (fun (acc : Mem Val × Bool) t =>
    let (m', l) := acc.1.read4 sp S0 db.S t
    (m', acc.2 && readOK sp db l t)) (m, true)

/-! ## Cache schedules for the tests -/

/-- Evict object h: unswizzle every memory slot that points to it, then release
it (each step only if its conditions allow). -/
def evictObj (m : Mem Val) (D : Dirty) (h : Nat) : Mem Val :=
  let m1 := m.objs.foldl (fun (mm : Mem Val) p =>
    p.2.slots.foldl (fun (mm2 : Mem Val) q =>
      if q.2 == Slot.mem h then mm2.unswizzle D p.1 q.1 else mm2) mm) m
  m1.release D h

/-- The objects that may be detached now. -/
def candidates (m : Mem Val) (D : Dirty) : List Nat :=
  (m.objs.map (·.1)).filter (m.detachable D)

/-- A cache schedule after transaction j: 0, none; 1, every object that may be
detached, in three passes (a release can free the objects below); 2, each one
with probability 0.3; 3, unswizzles and releases apart (E3): each memory slot to
an object that may be detached is unswizzled with probability 0.5, then each
object that may be released is, with probability 0.3, so that objects stay in
memory with some of their slots unswizzled. -/
def schedule (policy seed j : Nat) (D : Dirty) (m : Mem Val) : Mem Val :=
  match policy with
  | 0 => m
  | 1 => (List.range 3).foldl (fun mm _ =>
      (candidates mm D).foldl (fun mm2 h => evictObj mm2 D h) mm) m
  | 2 => (candidates m D).foldl (fun mm h =>
      if (lcg (seed * 1000003 + j * 97 + h)) / 65536 % 10 < 3 then evictObj mm D h else mm) m
  | _ =>
    let m1 := m.objs.foldl (fun (mm : Mem Val) p =>
      p.2.slots.foldl (fun (mm2 : Mem Val) q =>
        match q.2 with
        | .mem h => if mm2.detachable D h && (lcg (seed * 7919 + j * 131 + p.1 * 17 + h)) / 65536 % 2 == 0
            then mm2.unswizzle D p.1 q.1 else mm2
        | .stream _ => mm2) mm) m
    (m1.objs.map (·.1)).foldl (fun (mm : Mem Val) h =>
      if mm.eligible D h && (lcg (seed * 1000003 + j * 97 + h)) / 65536 % 10 < 3 then mm.release D h
      else mm) m1

/-! ## Runs with eviction, checked after every transaction -/

/-- A run with restarts and the cache schedule `policy` (as `checkLazy`): after
every transaction, the records and D are those of the run without restarts or
eviction; then the schedule, reads at three times, the schedule again; then the
invariants, the reads (they give P), and after a restart the invariants of the
new memory. Returns (transactions, failures). -/
def checkEvict [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Bool))
    (policy seed : Nat) : Nat × Nat :=
  let ts1 := ts.map (·.1)
  let r := ts.zipIdx.foldl
    (fun (acc : (DB Val T × Mem Val × SIS.Stream Val T) × Nat × Nat) (p, j) =>
      let ((db, m, S0), n, bad) := acc
      let (db', m') := evictTrans sp al S0 db m p.1
      let after := run sp al (ts1.take (j + 1))
      let k := db'.S.length - 1
      let m1 := schedule policy seed j db'.D m'
      let (m2, readsOK) := reads4 sp S0 db' m1 [k, k / 2, lcg (seed + j) % (k + 1)]
      let m3 := schedule policy (seed + 7) j db'.D m2
      let ok := db'.S == after.S && db'.D == after.D && readsOK &&
        invCanB db' m3 && invSnapB db' m3 && noDanglingB m3 && invSlotB sp S0 db' m3
      let st' := if p.2 then (startup sp db'.S, evictStartup sp db'.S, db'.S) else (db', m3, S0)
      let ok' := ok && (!p.2 ||
        (invCanB st'.1 st'.2.1 && noDanglingB st'.2.1 && invSlotB sp st'.2.2 st'.1 st'.2.1))
      (st', n + 1, bad + (if ok' then 0 else 1)))
    ((init sp, evictStartup sp (init sp).S, (init sp).S), 0, 0)
  (r.2.1, r.2.2)

/-- Example 3's algorithm of the stage 1 checks. -/
def al3 : Algo Val Tr3 :=
  { policy := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5, stillDirty := javaTest spec3, mark := true }

-- Example 3 (a virtual root), the three schedules.
#guard checkEvict spec3 al3 (randomTs3 1 12) 0 1 == (12, 0)
#guard checkEvict spec3 al3 (randomTs3 1 12) 1 1 == (12, 0)
#guard checkEvict spec3 al3 (randomTs3 1 12) 2 1 == (12, 0)
#guard checkEvict spec3 al3 (randomTs3 1 12) 3 1 == (12, 0)

-- Example 2 (a written root), BergDB's still-dirty test (algos2's odd entries).
#guard [1, 3].all (fun a => match algos2[a]? with
  | some al => [0, 1, 2, 3].all (fun pol => checkEvict spec2 al (randomTs 1 10) pol 1 == (10, 0))
  | none => false)

/-! ## The assumptions of stage 2 by running -/

/-- TREE at time i, by running. -/
def treeB (sp : Spec Val T) (P : Struct Val) (i : Time) : Bool :=
  let xs := (reachList sp P i).eraseDups
  xs.all (fun y => y == root ||
    (xs.filter (fun x => match P.get? x with
      | some n => (sp.live (n.hist.upTo i)).contains y
      | none => false)).length == 1)

/-- A6' at time i, by running. -/
def adoptB (sp : Spec Val T) (P : Struct Val) (i : Time) : Bool :=
  (reachList sp P i).eraseDups.all (fun x => match P.get? x with
    | some n => (pointees sp n.hist).all (fun y =>
        (sp.live (n.hist.upTo i)).contains y ||
        ((P.get? y).map (·.isData)).getD false || !reachable sp P i y ||
        (reachFrom sp P i x n).contains y)
    | none => true)

/-- A-COPY for the change c at time i, by running. -/
def copyB (sp : Spec Val T) (P : Struct Val) (i : Time) (c : Changes Val) : Bool :=
  let path := pathOf sp P c i
  c.adds.all (fun a => (sp.ptrs a.2).all (fun y =>
    (c.new.map (·.id)).contains y || path.contains y ||
    path.any (fun z => match P.get? z with
      | some nz => (pointees sp nz.hist).contains y &&
          (written sp z || (sp.live (nz.hist.upTo (i - 1))).contains y)
      | none => false)))

/-- `EvictRunOK` by running: TREE and A6' after every transaction, A-COPY for
its change. -/
def evictRunOKB (sp : Spec Val T) (al : Algo Val T) (ts : List T) : Bool :=
  (states sp al ts).zipIdx.all (fun (db, j) => treeB sp db.P j && adoptB sp db.P j) &&
  ts.zipIdx.all (fun (tr, j) =>
    let db := run sp al (ts.take j)
    copyB sp db.P (j + 1) (sp.exec tr (j + 1) (view sp db.P j)))

#guard evictRunOKB spec3 al3 ((randomTs3 1 20).map (·.1))
#guard [1, 3].all (fun a => match algos2[a]? with
  | some al => evictRunOKB spec2 al ((randomTs 1 20).map (·.1))
  | none => false)

/-! ## Example 5: example 3 with drops

As example 3 (a virtual root, top nodes above tree roots, mid nodes, leaves and
data nodes), with one more kind of transaction, for the cases of the design
(docs/level4-alignment.md, 5.4): a drop replaces a leaf by a new, empty one, so
that the old leaf and its data nodes are no longer reachable (BergDB's delete of
a long key, whose segment subtree goes cold). The plan's example 5 also asks for
two root changes in one transaction; the model's assumptions exclude it (every
node a transaction creates or changes is reachable after it, `stepOKB`), and
Java splits a node of the same transaction in place (F1-008-11's D1), so the
second change is not a node of its own. Ids of new nodes from i: 20000 + 8i and
up. -/

structure Tr5 where
  k : Nat
  n : Nat
  /-- 0: put; 1: root split; 2: drop. -/
  op : Nat
  deriving DecidableEq, Repr

def exec5 (tr : Tr5) (i : Time) (view : View Val) : Changes Val :=
  let none' : Changes Val := { new := [], adds := [] }
  let base := 20000 + 8 * i
  match (view 0).bind (fun r => slotOf r.hist 0) with
  | none => none'
  | some z =>
    match (view z).bind (fun zn => (live zn.hist).head?) with
    | none => none'
    | some t0 =>
      match view t0 with
      | none => none'
      | some tn =>
        if tr.op == 1 then
          let t' := base + 2
          let z' := base + 3
          { new := [⟨t', 3, false⟩, ⟨z', 100 + i, false⟩],
            adds := ((slotOf tn.hist 0).toList.map (fun m => (t', Val.slot 0 m))) ++
              ((slotOf tn.hist 1).toList.map (fun m => (t', Val.slot 1 m))) ++
              [(z', .ref t'), (z', .dead z), (0, .slot 0 z')] }
        else
          match slotOf tn.hist (tr.k / 2 % 2) with
          | none => none'
          | some m =>
            if tr.op == 2 then
              let l'' := base + 6
              { new := [⟨l'', 1, false⟩], adds := [(m, .slot (tr.k % 2) l'')] }
            else
              match (view m).bind (fun mn => slotOf mn.hist (tr.k % 2)) with
              | none => none'
              | some leaf =>
                match view leaf with
                | none => none'
                | some ln =>
                  let d := base
                  if (live ln.hist).length ≥ cap then
                    let l' := base + 1
                    { new := [⟨d, 0, true⟩, ⟨l', 1, false⟩],
                      adds := [(d, .dat tr.n), (l', .ref d), (m, .slot (tr.k % 2) l')] }
                  else
                    { new := [⟨d, 0, true⟩], adds := [(d, .dat tr.n), (leaf, .ref d)] }

def spec5 : Spec Val Tr5 where
  ptrs := ptrs
  live := live
  exec := exec5
  virt := true
  topLevel := 100
  rootVal := fun z => .slot 0 z
  init := spec3.init

/-- n pseudo-random transactions for example 5, with restart marks: about 60
percent puts, 20 root splits, 20 drops. -/
def randomTs5 (seed n : Nat) : List (Tr5 × Bool) :=
  (List.range n).foldl (fun acc _ =>
    let x := lcg acc.2
    let y := lcg x
    let r := y / 1024 % 10
    let op := if r < 6 then 0 else if r < 8 then 1 else 2
    (acc.1 ++ [(⟨x / 65536 % 4, y / 65536 % 100, op⟩, (x / 1024) % 3 == 0)], y))
    ([], seed)
  |>.1

def al5 : Algo Val Tr5 :=
  { policy := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5, stillDirty := javaTest spec5, mark := true }

-- Example 5 meets the model's assumptions, the physical layer's and stage 2's.
#guard runOKB spec5 al5 ((randomTs5 1 20).map (·.1))
#guard physRunOKB spec5 al5 ((randomTs5 1 20).map (·.1))
#guard evictRunOKB spec5 al5 ((randomTs5 1 20).map (·.1))
-- And with eviction, the three schedules.
#guard [0, 1, 2, 3].all (fun pol => checkEvict spec5 al5 (randomTs5 1 16) pol 1 == (16, 0))

end SIS.EvictExample
