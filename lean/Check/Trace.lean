/-
The trace checker (docs/level2-alignment.md, sections 2 and 9): the BergDB
instance of the model's `Spec`, and the reading of a trace written by
java/stress/TraceExport.java.

Not part of the trusted part. The checker evaluates the model's own
definitions (SIS/*.lean) on a Java run; this file only says how a trace
becomes the model's objects. Written 2026-10-15 for F1-008-11, WP C2.
-/
import SIS.Assumptions

namespace SIS.Check

open SIS

/-- The entry values of the BergDB instance (docs, 2.4 and 9.1). -/
inductive BVal where
  /-- A key klong: compare value c, child y. -/
  | key (c y : Nat)
  /-- A delete bitmap: the key entries before it with these compare values are
  deleted. -/
  | del (cs : List Nat)
  /-- A top node's pointer to its root key node. -/
  | rootKey (y : Nat)
  /-- A top node's skip pointer j to an older top node. -/
  | skip (j z : Nat)
  /-- The root's entry for a top node. -/
  | top (z : Nat)
  /-- A value node's data, as a hash. -/
  | data (h : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The nodes an entry points to. -/
def bptrs : BVal → List NodeId
  | .key _ y => [y]
  | .rootKey y => [y]
  | .skip _ z => [z]
  | .top z => [z]
  | _ => []

/-- Sets the value for compare value c in an association list, keeping the
order of first appearance. -/
def setAssoc (m : List (Nat × Option Nat)) (c : Nat) (v : Option Nat) :
    List (Nat × Option Nat) :=
  if m.any (fun p => p.1 == c) then m.map (fun p => if p.1 == c then (c, v) else p)
  else m ++ [(c, v)]

/-- The live children of a node with history h: for a key node, the child of
the last key entry of each compare value that no later delete entry names; for
a top node, its last root pointer; for the root, its last top node. -/
def blive (h : History BVal) : List NodeId :=
  let st := h.foldl (fun (acc : List (Nat × Option Nat) × Option Nat × Option Nat) e =>
    match e.val with
    | .key c y => (setAssoc acc.1 c (some y), acc.2.1, acc.2.2)
    | .del cs =>
      (cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) acc.1,
        acc.2.1, acc.2.2)
    | .rootKey y => (acc.1, some y, acc.2.2)
    | .top z => (acc.1, acc.2.1, some z)
    | _ => acc) ([], none, none)
  ((st.1.filterMap (·.2)) ++ st.2.1.toList ++ st.2.2.toList).eraseDups

/-! ## Reading a trace -/

/-- A version as the trace gives it. -/
structure TVer where
  node : NodeId
  isData : Bool
  hist : Array (Entry BVal) := #[]
  refs : Array (NodeId × Nat) := #[]
  /-- A top node's skip slots and the times they cache (SKIPT lines, trace format
  2; bergdb item 001, WP L5). -/
  skipt : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- A first touch after a restart (a FIRST line, trace format 2; bergdb item 001,
WP L5): the node; the record the pointer names after Rule R (none for a vpos);
the record Java took (none for a canonical object); the kind (canonical,
version or snapshot); whether the version read was cut back to the startup
time. -/
structure TFirst where
  node : NodeId
  named : Option Nat
  took : Option Nat
  kind : String
  cut : Bool
  deriving Inhabited

/-- A slot of a resident canonical object of run E, at the end of the
transaction (a SLOT line, trace format 2; bergdb item 001, WP J4): the object's
node, the pointee, the record the slot serializes (none for a vpos), and the
slot's kind: `canon` (a memory slot to the pointee's canonical object), `mem`
(to another object, or to a value), `stream`, or `dead` (a stream slot below the
stream's first position, M33). -/
structure TSlot where
  node : NodeId
  pointee : NodeId
  ser : Option Nat
  kind : String
  deriving Inhabited

/-- A handle of run E's state at the end of the transaction (a HANDLE line, trace format 2;
bergdb item 009, step 4c): its number, the same in every state of run E; its node; its state
(`live`, `loading` or `dead`); the number of the object it holds, if any; and the record of its
written position, if any. -/
structure THandle where
  num : Nat
  node : NodeId
  state : String
  obj : Option Nat
  written : Option Nat
  deriving Inhabited

/-- An object of run E's state (a HOBJ line; bergdb item 009, step 4c): its number in the
state, its node, whether it is canonical, the record of its position (none if it has not been
written: a vpos), the number of entries of its history, and the history's hash
(`historyHash`; none if the line has none, as the first traces with handle lines). -/
structure TObj where
  num : Nat
  node : NodeId
  canonical : Bool
  pos : Option Nat
  entries : Nat
  hash : Option Nat := none
  deriving Inhabited

/-- A pointer of an object of run E's state to an index node (a HPTR line; bergdb item 009,
step 4c): the object's number, the pointee, the record that its reference names (none for a
vpos), and the number of the handle it holds, if any. -/
structure TPtr where
  obj : Nat
  pointee : NodeId
  ref : Option Nat
  handle : Option Nat
  deriving Inhabited

/-- One transaction of the trace: `TX i` to `END i`. -/
structure TRec where
  idx : Nat
  new : Array (NodeId × Nat × Bool) := #[]
  adds : Array (NodeId × Nat × BVal) := #[]
  sp : Nat := 0
  top : Option Nat := none
  /-- The node of the version that top names (trace lines from 2026-10-16 on). -/
  topNode : Option Nat := none
  topSrc : String := ""
  vers : Array TVer := #[]
  gd : List NodeId := []
  dirty : List (NodeId × Nat) := []
  live : Array (NodeId × Nat × List NodeId) := #[]
  probes : Array (Nat × Bool × String) := #[]
  /-- The first touches after the restart after this transaction, up to the next. -/
  firsts : Array TFirst := #[]
  /-- Run E's slots at the end of this transaction (bergdb item 001, WP J4). -/
  slots : Array TSlot := #[]
  /-- Run E's handle state at the end of this transaction (bergdb item 009, step 4c): the
  HMEM line (the last record that the state's startup read, R(0) for run E's first, and the
  stream's first record), the node table (HTABLE: node, handle), the handles (HANDLE), the
  objects (HOBJ) and their pointers to index nodes (HPTR). -/
  hmem : Option (Nat × Nat) := none
  htable : Array (NodeId × Nat) := #[]
  handles : Array THandle := #[]
  hobjs : Array TObj := #[]
  hptrs : Array TPtr := #[]
  /-- With reclaim (trace format 2; bergdb item 001, WPs R2 and R7): the nodes
  T(i)'s touch visited (TOUCH), fa(i) when it changes (FA), a cut decided at
  R(i), as the first record kept and the first available time (CUT), and the
  stream's first record after the physical cut after R(i) (PHYSCUT). -/
  touch : List NodeId := []
  fa : Option Nat := none
  cut : Option (Nat × Nat) := none
  physcut : Option Nat := none
  deriving Inhabited

structure Trace where
  config : String := ""
  errors : Array String := #[]
  recs : Array TRec := #[]
  bad : Array String := #[]
  done : Option Nat := none

def toks (line : String) : List String :=
  (line.splitOn " ").filter (fun s => !s.isEmpty)

def parseVal : List String → Option BVal
  | ["K", c, y] => do some (.key (← c.toNat?) (← y.toNat?))
  | "D" :: n :: cs => do
    let n ← n.toNat?
    let cs ← cs.mapM String.toNat?
    if cs.length == n then some (.del cs) else none
  | ["R", y] => y.toNat?.map .rootKey
  | ["S", j, z] => do some (.skip (← j.toNat?) (← z.toNat?))
  | ["T", z] => z.toNat?.map .top
  | ["V", h] => h.toNat?.map .data
  | _ => none

def parseNats (ts : List String) : Option (List Nat) := ts.mapM String.toNat?

def pairs : List Nat → Option (List (Nat × Nat))
  | [] => some []
  | a :: b :: r => (pairs r).map ((a, b) :: ·)
  | _ => none

/-- Changes the last transaction of the trace. -/
def modCur (t : Trace) (f : TRec → TRec) : Trace :=
  if t.recs.isEmpty then { t with bad := t.bad.push "a line outside TX ... END" }
  else { t with recs := t.recs.modify (t.recs.size - 1) f }

/-- Changes the last version of the last transaction. -/
def modVer (t : Trace) (f : TVer → TVer) : Trace :=
  modCur t (fun r =>
    if r.vers.isEmpty then r else { r with vers := r.vers.modify (r.vers.size - 1) f })

def parseLine (t : Trace) (n : Nat) (line : String) : Trace :=
  let bad := fun (s : String) => { t with bad := t.bad.push s!"line {n}: {s}: {line}" }
  if line.startsWith "#" then t else
  match toks line with
  | [] => t
  | "TRACE" :: v :: _ => if v == "1" || v == "2" then t else bad "unknown trace format"
  | "CONFIG" :: r => { t with config := " ".intercalate r }
  | "ERROR" :: r => { t with errors := t.errors.push (" ".intercalate r) }
  | ["TX", i] => match i.toNat? with
    | some i => { t with recs := t.recs.push { idx := i } }
    | none => bad "bad TX"
  | ["NEW", x, l, k] => match x.toNat?, l.toNat? with
    | some x, some l => modCur t (fun r => { r with new := r.new.push (x, l, k == "D") })
    | _, _ => bad "bad NEW"
  | "ADD" :: x :: tm :: v => match x.toNat?, tm.toNat?, parseVal v with
    | some x, some tm, some v => modCur t (fun r => { r with adds := r.adds.push (x, tm, v) })
    | _, _, _ => bad "bad ADD"
  | ["REC", _, s, tp, src] => match s.toNat? with
    | some s => modCur t (fun r => { r with sp := s, top := tp.toNat?, topSrc := src })
    | none => bad "bad REC"
  | ["REC", _, s, tp, src, z] => match s.toNat? with
    | some s => modCur t (fun r => { r with sp := s, top := tp.toNat?, topSrc := src, topNode := z.toNat? })
    | none => bad "bad REC"
  | ["VER", x, k] => match x.toNat? with
    | some x => modCur t (fun r => { r with vers := r.vers.push { node := x, isData := k == "D" } })
    | none => bad "bad VER"
  | "H" :: tm :: v => match tm.toNat?, parseVal v with
    | some tm, some v => modVer t (fun w => { w with hist := w.hist.push ⟨tm, v⟩ })
    | _, _ => bad "bad H"
  | ["F", y, rr] => match y.toNat?, rr.toNat? with
    | some y, some rr => modVer t (fun w => { w with refs := w.refs.push (y, rr) })
    | _, _ => bad "bad F"
  | ["SKIPT", j, tm] => match j.toNat?, tm.toNat? with
    | some j, some tm => modVer t (fun w => { w with skipt := w.skipt.push (j, tm) })
    | _, _ => bad "bad SKIPT"
  | ["FIRST", x, nn, rr, k, c] => match x.toNat? with
    | some x =>
      if (nn != "-" && nn.toNat?.isNone) || (rr != "-" && rr.toNat?.isNone) || (c != "0" && c != "1") then
        bad "bad FIRST"
      else modCur t (fun r =>
        { r with firsts := r.firsts.push (TFirst.mk x nn.toNat? rr.toNat? k (c == "1")) })
    | none => bad "bad FIRST"
  | ["SLOT", x, y, rr, k] => match x.toNat?, y.toNat? with
    | some x, some y =>
      if (rr != "-" && rr.toNat?.isNone) || !(["canon", "mem", "stream", "dead"].contains k) then
        bad "bad SLOT"
      else modCur t (fun r => { r with slots := r.slots.push (TSlot.mk x y rr.toNat? k) })
    | _, _ => bad "bad SLOT"
  | ["HMEM", k, c] => match k.toNat?, c.toNat? with
    | some k, some c => modCur t (fun r => { r with hmem := some (k, c) })
    | _, _ => bad "bad HMEM"
  | ["HTABLE", y, h] => match y.toNat?, h.toNat? with
    | some y, some h => modCur t (fun r => { r with htable := r.htable.push (y, h) })
    | _, _ => bad "bad HTABLE"
  | ["HANDLE", h, y, st, a, w] => match h.toNat?, y.toNat? with
    | some h, some y =>
      if !(["live", "loading", "dead"].contains st) || (a != "-" && a.toNat?.isNone) ||
          (w != "-" && w.toNat?.isNone) then bad "bad HANDLE"
      else modCur t (fun r => { r with handles := r.handles.push (THandle.mk h y st a.toNat? w.toNat?) })
    | _, _ => bad "bad HANDLE"
  | "HOBJ" :: a :: y :: k :: p :: e :: hs => match a.toNat?, y.toNat?, e.toNat? with
    | some a, some y, some e =>
      let hash := match hs with
        | [h] => h.toNat?.map some
        | [] => some none
        | _ => none
      match hash with
      | some hash =>
        if !(["canon", "snap"].contains k) || (p != "-" && p.toNat?.isNone) then bad "bad HOBJ"
        else modCur t (fun r => { r with hobjs := r.hobjs.push (TObj.mk a y (k == "canon") p.toNat? e hash) })
      | none => bad "bad HOBJ"
    | _, _, _ => bad "bad HOBJ"
  | ["HPTR", a, y, rr, h] => match a.toNat?, y.toNat? with
    | some a, some y =>
      if (rr != "-" && rr.toNat?.isNone) || (h != "-" && h.toNat?.isNone) then bad "bad HPTR"
      else modCur t (fun r => { r with hptrs := r.hptrs.push (TPtr.mk a y rr.toNat? h.toNat?) })
    | _, _ => bad "bad HPTR"
  | "GD" :: xs => match parseNats xs with
    | some xs => modCur t (fun r => { r with gd := xs })
    | none => bad "bad GD"
  | "DIRTY" :: xs => match (parseNats xs).bind pairs with
    | some ps => modCur t (fun r => { r with dirty := ps })
    | none => bad "bad DIRTY"
  | "LIVE" :: x :: tm :: ys => match x.toNat?, tm.toNat?, parseNats ys with
    | some x, some tm, some ys => modCur t (fun r => { r with live := r.live.push (x, tm, ys) })
    | _, _, _ => bad "bad LIVE"
  | "TOUCH" :: xs => match parseNats xs with
    | some xs => modCur t (fun r => { r with touch := xs })
    | none => bad "bad TOUCH"
  | ["FA", f] => match f.toNat? with
    | some f => modCur t (fun r => { r with fa := some f })
    | none => bad "bad FA"
  | ["CUT", c, f] => match c.toNat?, f.toNat? with
    | some c, some f => modCur t (fun r => { r with cut := some (c, f) })
    | _, _ => bad "bad CUT"
  | ["PHYSCUT", c] => match c.toNat? with
    | some c => modCur t (fun r => { r with physcut := some c })
    | none => bad "bad PHYSCUT"
  | "PROBE" :: i :: res :: r => match i.toNat? with
    | some i => modCur t (fun rr => { rr with probes := rr.probes.push (i, res == "ok", " ".intercalate r) })
    | none => bad "bad PROBE"
  | ["END", _] => t
  | ["DONE", d] => { t with done := d.toNat? }
  | _ => bad "unknown line"

def parseTrace (s : String) : Trace :=
  ((s.splitOn "\n").zipIdx).foldl (fun t (l, n) => parseLine t (n + 1) l) {}

/-! ## The hash of a history (bergdb item 009, step 4c) -/

/-- An entry value as on an H or ADD line (9.1): `K c y`, `D n c1 ... cn`, `R y`, `S j z`,
`T z`, `V h`. -/
def showVal : BVal → String
  | .key c y => s!"K {c} {y}"
  | .del cs => " ".intercalate (s!"D {cs.length}" :: cs.map toString)
  | .rootKey y => s!"R {y}"
  | .skip j z => s!"S {j} {z}"
  | .top z => s!"T {z}"
  | .data h => s!"V {h}"

/-- The hash of a history, as TraceExport's `historyHash` writes it on a HOBJ line: FNV-1a
with 64 bits (offset basis 0xcbf29ce484222325, prime 0x100000001b3, arithmetic modulo 2^64,
`UInt64`) over the bytes of the entries in their order, each as on an H line, then a newline
(0x0a): the time (the record index), a space, and the value (`showVal`: K c y, a key klong
with compare value c and child y; D n c1 ... cn, a delete bitmap with the n compare values it
deletes, ascending; R y, a top node's root pointer; S j z, its skip pointer j; T z, a root
entry; V h, a value's data, h its hash); numbers in decimal ASCII, tokens separated by one
space. The trace writes it as an unsigned decimal. -/
def historyHash (h : History BVal) : UInt64 :=
  h.foldl (fun x e => s!"{e.time} {showVal e.val}\n".toUTF8.foldl
    (fun x b => (x ^^^ b.toUInt64) * 0x100000001b3) x) 0xcbf29ce484222325

/-! ## The model's objects -/

/-- The level of every node, from the NEW lines. -/
def levelMap (t : Trace) : List (NodeId × Nat × Bool) :=
  t.recs.toList.flatMap (fun r => r.new.toList)

/-- The changes of transaction i, its touch included. -/
def changesOf (r : TRec) : Changes BVal :=
  { new := r.new.toList.map (fun (x, l, d) => ⟨x, l, d⟩),
    adds := r.adds.toList.map (fun (x, _, v) => (x, v)),
    touch := r.touch }

/-- fa(i) of every record: the last FA line at or before it, 0 before the first. -/
def faSeq (recs : Array TRec) : Array Nat :=
  (recs.foldl (fun (acc : Array Nat × Nat) r =>
    let f := r.fa.getD acc.2
    (acc.1.push f, f)) (#[], 0)).1

/-- The level of the root children (top nodes) of a BergDB trace: that of the
primordial top node, the lowest level of a node with a root pointer (docs,
8.4). -/
def topLevelOf (p0 : Struct BVal) : Nat :=
  ((p0.filter (fun p => p.2.hist.any (fun e => match e.val with
    | .rootKey _ => true
    | _ => false))).map (·.2.level)).foldl min (2 ^ 62)

/-- The BergDB instance for one trace: `exec` gives the changes of the trace's
transaction i; the initial structure is the one of `TX 0`. With `virt`, the
root is virtual (option (a) of Q7, `Spec.virt`). -/
def bspec (chs : Array (Changes BVal)) (p0 : Struct BVal) (virt : Bool := true) : Spec BVal Nat where
  ptrs := bptrs
  live := blive
  exec := fun tr _ _ => chs.getD tr { new := [], adds := [] }
  init := p0
  virt := virt
  topLevel := topLevelOf p0
  rootVal := .top

/-- A version of the trace as the model's version. -/
def toVersion (lv : List (NodeId × Nat × Bool)) (i : Nat) (w : TVer) : Version BVal :=
  { node := w.node, recNo := i,
    level := ((lv.lookup w.node).map (·.1)).getD 0,
    isData := w.isData, hist := w.hist.toList, refs := w.refs.toList }

/-- A record of the trace as the model's record; fa is its first available time
(`faSeq`). -/
def toRecord (lv : List (NodeId × Nat × Bool)) (fa : Nat) (r : TRec) : Record BVal Nat :=
  { trans := if r.idx == 0 then none else some r.idx, sp := r.sp,
    vers := r.vers.toList.map (toVersion lv r.idx), gd := r.gd,
    top := r.top.map (fun j => (r.topNode.getD 0, j)), fa := fa }

end SIS.Check
