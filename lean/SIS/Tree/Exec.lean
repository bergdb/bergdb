/-
The tree model (bergdb 024-12): the writer. What a transaction does to BergDB's
key tree, `Tree.exec`: Java's `Dag.putKv` and everything below it, as a function
of the transaction, its time and P@(i-1) (A1), giving the model's `Changes`.
Trusted part.

Each definition names the Java method it restates (java/src/bergdb/dag/Dag.java,
TopDs.java); the order of the steps is Java's wherever a node id is made, since
ids are given in the order of the calls (024-12, D8). Java's `Bug` and "corrupt
data" exceptions are errors here: `exec` then returns the text.
-/
import SIS.Tree.Node

namespace SIS.Tree

open SIS SIS.Check

/-! ## Transactions -/

/-- A key: its segments' compare values (`Keys.toSegments`), at least one. -/
abbrev Key := List Nat

/-- An operation of a transaction, as the Dag gets it: a put of a key with a
value (its hash), or a delete. -/
inductive Op where
  | put (key : Key) (h : Nat)
  | del (key : Key)
  deriving DecidableEq, Repr, Inhabited

def Op.key : Op → Key
  | .put k _ => k
  | .del k => k

/-- The order of keys (`Keys.compareArrays`): by segments, a prefix first. -/
def keyLt : Key → Key → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: r, b :: s => a < b || (a == b && keyLt r s)

/-- The keys are strictly increasing. -/
def sortedKeys : List Key → Bool
  | a :: b :: r => keyLt a b && sortedKeys (b :: r)
  | _ => true

/-- `Key.wf`: a key as `Keys.toSegments` makes it: every segment but the last
has 7 bytes, the last has fewer. -/
def keyWf : Key → Bool
  | [] => false
  | [c] => segLen c != 7
  | c :: r => segLen c == 7 && keyWf r

/-- A transaction: the id of the first node it makes (024-12, D8: Java's record
position plus one), its operations in the order the Dag gets them, and the
bounds of its touch, if it has one (reclaim's steps, `Trans.touchFrom` and
`touchTo`: after the first, up to the second; none: no bound). -/
structure Tx where
  base : NodeId
  ops : List Op
  touch : Option (Option Key × Option Key) := none
  deriving Repr, Inhabited

/-! ## The writer's state within a transaction (024-12, D7) -/

/-- The super root, a top node (`TopNode`, `TopDs.superRoot`): its id, ordinal,
root time, root key node and skip pointers (index and target). -/
structure Top where
  id : NodeId
  ord : Nat
  time : Time
  rootKey : NodeId
  skips : List (Nat × NodeId)
  deriving DecidableEq, Repr, Inhabited

/-- The writer's state: the key nodes read, made or changed so far, as klongs,
with the segment and the height of each; the nodes made, in order; the values
made, with their hashes; the nodes taken back; for a node that a split made, the
node it replaces (`PutData.madeFor`); the next id; the key access path of the
operation (`KeyAccessPath`: the compare value of the klong followed, none for the
space root, and the node); the super root, and whether the transaction made it. -/
structure W where
  nodes : List (NodeId × KNode) := []
  gh : List (NodeId × Nat × Nat) := []
  made : List NewNode := []
  vals : List (NodeId × Nat) := []
  taken : List NodeId := []
  madeFor : List (NodeId × NodeId) := []
  next : NodeId
  path : List (Option Nat × NodeId) := []
  top : Top
  newTop : Bool := false
  /-- Which rules ran, by name, for the checker's counts of what a run reached.
  No rule reads it. -/
  trail : List String := []
  deriving Repr, Inhabited

/-- What the writer reads and does not change: the parameters, the
transaction's time, and P@(i-1), without the root (`rootless`). -/
structure Ctx where
  p : Params
  i : Time
  view : View BVal

/-- The writer's steps: a state, and an error, a text that starts with its
kind: `Bug:` for a state that Java's `Dag` excludes and throws a `Bug` for;
`corrupt:` for a P that is no tree of BergDB's, where Java reports corrupt data
or cannot go on; `bounds:` for a tree that leaves the level bounds G and H. -/
abbrev M := ReaderT Ctx (StateT W (Except String))

/-- A bound on the length of any path of key nodes within G and H; the fuel of
the descents. -/
def Params.fuel (p : Params) : Nat := (p.G + 1) * (p.H + 2) + 2

/-- Notes that a rule ran (`W.trail`). -/
def note (s : String) : M Unit := modify (fun w => { w with trail := s :: w.trail })

/-- The next id (`Db.setIdOfNode`). -/
def fresh : M NodeId := do
  let w ← get
  set { w with next := w.next + 2 }
  pure w.next

/-- Key node x as it is now: from the overlay, or read from P@(i-1) by its
history (`klongsOf`), a segment leaf if its level says height 0 (024-12, D5). -/
def getNode (x : NodeId) : M KNode := do
  let w ← get
  match w.nodes.lookup x with
  | some n => pure n
  | none =>
    let c ← read
    match c.view x with
    | some nd =>
      if nd.isData || c.p.keyMax < nd.level then
        throw s!"corrupt: node {x} is no key node (a value, a top node or the root)" else
        let n : KNode := { leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist }
        set { w with nodes := w.nodes ++ [(x, n)],
                     gh := (x, c.p.segOf nd.level, c.p.heightOf nd.level) :: w.gh }
        pure n
    | none => throw s!"corrupt: key node {x} is not in P@(i-1)"

/-- Sets node x in a list of nodes by id, at its place, or at the end. -/
def upsert (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode) : List (NodeId × KNode) :=
  if ns.any (fun q => q.1 == x) then ns.map (fun q => if q.1 == x then (x, n) else q)
  else ns ++ [(x, n)]

/-- Stores key node x in the overlay. -/
def putNode (x : NodeId) (n : KNode) : M Unit :=
  modify (fun w => { w with nodes := upsert w.nodes x n })

/-- The segment and the height of key node x. -/
def ghOf (x : NodeId) : M (Nat × Nat) := do
  let _ ← getNode x
  match (← get).gh.lookup x with
  | some v => pure v
  | none => throw s!"corrupt: key node {x} has no segment and height"

/-- A new key node in segment g at height h (`keyNodeCreated`). Outside the
bounds G and H its level would not be below its parent's (A4; 024-12, D5): an
error. -/
def newKey (g h : Nat) (leaf : Bool) (ks : List Klong) : M NodeId := do
  let c ← read
  if c.p.G < g || c.p.H < h then
    throw s!"bounds: the tree leaves the level bounds: segment {g}, height {h}; G = {c.p.G}, H = {c.p.H}"
  let x ← fresh
  modify (fun w => { w with nodes := w.nodes ++ [(x, ⟨leaf, ks⟩)], gh := (x, g, h) :: w.gh,
                            made := w.made ++ [⟨x, c.p.keyLevel g h, false⟩] })
  pure x

/-- A new value (`valueNodeCreated`). -/
def newValue (h : Nat) : M NodeId := do
  let x ← fresh
  modify (fun w => { w with vals := w.vals ++ [(x, h)], made := w.made ++ [⟨x, 0, true⟩] })
  pure x

/-- `PutData.madeFor`: `made`, made by a split, replaces `old`. -/
def setMadeFor (made : NodeId) (old : Option NodeId) : M Unit :=
  match old with
  | some o => modify (fun w => { w with madeFor := (made, o) :: w.madeFor })
  | none => pure ()

/-- `PutData.replacedBy`. -/
def replacedBy (x : NodeId) : M (Option NodeId) := do
  pure ((← get).madeFor.lookup x)

/-- `keyNodeTakenBack`: x is no node of the transaction. -/
def takenBack (x : NodeId) : M Unit :=
  modify (fun w => { w with taken := x :: w.taken })

def pathClear : M Unit := modify (fun w => { w with path := [] })

/-- `KeyAccessPath.add`, which the writer's follow of a pointer calls. -/
def pathAdd (c : Option Nat) (x : NodeId) : M Unit :=
  modify (fun w => { w with path := w.path ++ [(c, x)] })

def pathSize : M Nat := do pure (← get).path.length

/-- `KeyAccessPath.get`. -/
def pathNode (d : Nat) : M NodeId := do
  match (← get).path[d]? with
  | some e => pure e.2
  | none => throw s!"corrupt: the key access path has no depth {d}"

/-- `KeyAccessPath.getKlong`, as a compare value; the space root has none. -/
def klongAt (d : Nat) : M Nat := do
  match (← get).path[d]? with
  | some (some c, _) => pure c
  | _ => throw s!"corrupt: the key access path has no klong at depth {d}"

/-- `PutData.getParent`. -/
def parentAt (d : Nat) : M (Option NodeId) := do
  match d with
  | 0 => pure none
  | e + 1 => pure (some (← pathNode e))

/-! ## The top node (`TopDs.newSuperRoot`) -/

/-- `TopNode.height`: the number of skip pointers of the top node with ordinal o. -/
def topHeight (o : Nat) : Nat := if o == 0 then 0 else Nat.log2 o + 1

/-- `TopDs.newSuperRoot`: y is the space root at the transaction's time. The
transaction's own top node gets it in place; else a new top node is made, with
the next ordinal, and a skip pointer at each set bit of the ordinal: the old
super root's skip pointer of that index, or the old super root. -/
def newSuperRoot (y : NodeId) : M Unit := do
  let c ← read
  let w ← get
  if c.i == w.top.time then
    set { w with top := { w.top with rootKey := y } }
    note "top.inplace"
  else
    note "top.new"
    let z ← fresh
    let o := if w.top.ord == 0 then 1 else w.top.ord + 1
    let skips := (List.range (topHeight o)).filterMap (fun j =>
      if o.testBit j then
        match w.top.skips.lookup j with
        | some t => some (j, t)
        | none => some (j, w.top.id)
      else none)
    modify (fun w => { w with top := ⟨z, o, c.i, y, skips⟩, newTop := true,
                              made := w.made ++ [⟨z, c.p.topLevel o, false⟩] })

/-- `TopDs.findRoot` at the transaction's time, by the writer: the space root,
which starts the key access path. -/
def findRoot : M NodeId := do
  let y := (← get).top.rootKey
  pathAdd none y
  pure y

/-! ## A full node: the splits (`Dag.appendKlongs`, `handleFullNode`) -/

/-- Adds key klongs to a node with room for them (`KeyNode.addKlong`). -/
def addKeys (x : NodeId) (ins : List (Nat × NodeId)) : M Unit := do
  let c ← read
  let n ← getNode x
  putNode x (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n)

/-- The loop of `Dag.timeSplit`: each klong to add replaces the last version's
klong of its compare value, or is added. -/
def replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) : M KNode := do
  let c ← read
  ins.foldlM (fun last (cv, y) =>
    match replaceKlong last.ks c.i cv y with
    | .error e => throw e
    | .ok (some ks) => pure { last with ks := ks }
    | .ok none => pure (last.add c.i (.key cv y))) last

/-- `Dag.handleFullNode` for node x at `depth` of the key access path, with its
last version `last` and the klongs `ins` to insert; `up` gives klongs to the
parent (`appendKlongs` one level up).

More than M/2 klongs in the last version: a space split (`spaceSplit`; in place
for a node that the transaction made, `spaceSplitInPlace`). Else a time split
(`timeSplit`, `timeSplitInPlace`). A node that existed before the transaction
then loses its klongs of the transaction (`toPreviousState`). -/
def handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat) (x : NodeId)
    (ins : List (Nat × NodeId)) (last : KNode) : M Unit := do
  let c ← read
  let tt := c.i
  let n ← getNode x
  let (g, h) ← ghOf x
  let newInTrans := n.firstTime == some tt
  let parent ← parentAt depth
  let parentLeaf ← match parent with
    | some q => do pure (← getNode q).leaf
    | none => pure false
  if last.size > c.p.M / 2 then
    if newInTrans then
      -- Dag.spaceSplitInPlace: x keeps the first half.
      let second ← newKey g h n.leaf []
      setMadeFor second (← replacedBy x)
      let (f, s, sc) := halves n.leaf tt last ins
      putNode x f
      putNode second s
      match parent with
      | none =>
        note "split.space3.inplace"
        let r ← newKey g (h + 1) false [.time tt, .key 0 x, .key sc second]
        setMadeFor r (← replacedBy x)
        newSuperRoot r
      | some q =>
        if parentLeaf then
          -- A segment root made and split in one transaction: the segment leaf's
          -- klong of tt is pointed to the new root in place (fault 12's fix).
          note "split.space2.inplace"
          let r ← newKey g (h + 1) false [.time tt, .key 0 x, .key sc second]
          setMadeFor r (← replacedBy x)
          let k1 ← klongAt depth
          let pn ← getNode q
          match pn.linkIndex x k1 with
          | some j =>
            if pn.lastTime != some tt then
              throw s!"Bug: space split at {tt}: no klong of tt to segment root {x}"
            putNode q (pn.repoint j r)
          | none => throw s!"Bug: space split at {tt}: no klong of tt to segment root {x}"
        else
          note "split.space1.inplace"
          up q [(sc, second)]
    else
      -- Dag.spaceSplit: two new halves replace x.
      let first ← newKey g h n.leaf []
      let second ← newKey g h n.leaf []
      setMadeFor first (some x)
      setMadeFor second (some x)
      match parent with
      | none =>
        -- space-split-3: a new space root.
        note "split.space3"
        let r ← newKey g (h + 1) false []
        setMadeFor r (some x)
        let (f, s, sc) := halves n.leaf tt last ins
        putNode first f
        putNode second s
        putNode r ⟨false, [.time tt, .key 0 first, .key sc second]⟩
        newSuperRoot r
      | some q =>
        if parentLeaf then
          -- space-split-2: a new segment root.
          note "split.space2"
          let r ← newKey g (h + 1) false []
          setMadeFor r (some x)
          let (f, s, sc) := halves n.leaf tt last ins
          putNode first f
          putNode second s
          putNode r ⟨false, [.time tt, .key 0 first, .key sc second]⟩
          let k1 ← klongAt depth
          up q [(k1, r)]
        else
          -- space-split-1.
          note "split.space1"
          let (f, s, sc) := halves n.leaf tt last ins
          putNode first f
          putNode second s
          let k1 ← klongAt depth
          up q [(k1, first), (sc, second)]
  else
    if newInTrans then
      -- Dag.timeSplitInPlace: x becomes its last version.
      note "split.time.inplace"
      let l ← replaceOrAdd last ins
      if l.size == 1 then note "lone-time-klong"
      putNode x { l with leaf := n.leaf }
    else
      -- Dag.timeSplit: the last version replaces x.
      let l ← replaceOrAdd last ins
      if l.size == 1 then note "lone-time-klong"
      let y ← newKey g h n.leaf l.ks
      setMadeFor y (some x)
      match parent with
      | none =>
        note "split.time2"
        newSuperRoot y
      | some q =>
        note "split.time1"
        let k1 ← klongAt depth
        up q [(k1, y)]
  if !newInTrans then
    let n ← getNode x
    putNode x (n.toPrev (tt - 1))

/-- `Dag.appendKlongs`: the key klongs `ins` (one or two) go into node x at
`depth` of the key access path, if it has room for them and a time klong; else
the node is full. -/
def appendKlongs : Nat → NodeId → List (Nat × NodeId) → M Unit
  | depth, x, ins => do
    let c ← read
    let n ← getNode x
    if n.size + ins.length + 1 > c.p.M then
      let up : NodeId → List (Nat × NodeId) → M Unit := match depth with
        | 0 => fun _ _ => throw "corrupt: a split's parent above depth 0"
        | d + 1 => fun q more => appendKlongs d q more
      handleFullWith up depth x ins (n.lastVersion c.i)
    else addKeys x ins

/-- `Dag.handleFullNode` with a last version made by the caller (a delete). -/
def handleFull (depth : Nat) (x : NodeId) (last : KNode) : M Unit :=
  let up : NodeId → List (Nat × NodeId) → M Unit := match depth with
    | 0 => fun _ _ => throw "corrupt: a split's parent above depth 0"
    | d + 1 => fun q more => appendKlongs d q more
  handleFullWith up depth x [] last

/-! ## The delete: UP, LE-b, the take-back, RC -/

/-- `Dag.appendDeleteKlong`: a bitmap in node x that deletes compare value cv.
Returns true for a noop. The transaction's own bitmap, if it is the node's last
klong, gets the bits in place; a full node is replaced by its last version. -/
def appendDeleteKlong (x : NodeId) (depth : Nat) (cv : Nat) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode x
  if n.ks.any (fun k => match k with
      | .time t => decide (tt < t)
      | _ => false) then
    throw s!"Bug: key node {x} has a time after the transaction's"
  let arrayDel := n.lastBitmap
  let hasTransDel := (match n.ks.getLast? with
    | some (.del _) => true
    | _ => false) && n.lastTime == some tt
  let union := bitsUnion arrayDel (n.bitsOf cv)
  let isNoop := union == arrayDel
  if !isNoop then
    if hasTransDel then
      note "bitmap.inplace"
      putNode x (n.setAt (n.size - 1) (.del union))
    else if n.size + 1 < c.p.M then
      note "bitmap.new"
      putNode x (n.add tt (.del union))
    else
      note "bitmap.full"
      handleFull depth x (n.lastVersionGivenDel tt union)
  pure isNoop

/-- `Dag.emptyKeyNext`, LE-b: the child of the empty key of the inner node x has
emptied. The empty key gets the pointer of the next live klong (the smallest
live compare value but the empty key's, its last klong), by a new klong or in
place if its klong is of the transaction, and that klong's compare value is
deleted. A full node is replaced by its last version, the empty key in the next
klong's place. -/
def emptyKeyNext (x : NodeId) (depth : Nat) : M Unit := do
  let c ← read
  let tt := c.i
  let n ← getNode x
  let arrayDel := n.lastBitmap
  let hasTransDel := (match n.ks.getLast? with
    | some (.del _) => true
    | _ => false) && n.lastTime == some tt
  let e := (n.bitsOf 0).getLast?
  let del0 := bitsUnion arrayDel (n.bitsOf 0)
  let j := n.ks.zipIdx.foldl (fun (best : Option (Nat × Nat × NodeId)) (k, i) =>
    match k with
    | .key cv y =>
      if del0.contains i then best else
        match best with
        | none => some (i, cv, y)
        | some (_, jcv, _) => if cv ≤ jcv then some (i, cv, y) else best
    | _ => best) none
  match e, j with
  | some e, some (_, jcv, jy) =>
    if arrayDel.contains e then
      throw s!"Bug: LE-b at {tt} in key node {x}: no live klong of the empty key"
    let union := bitsUnion arrayDel (n.bitsOf jcv)
    let ofTt := n.lastTime == some tt
    let inPlace := ofTt && (match n.lastTimeIndex with
      | some ti => decide (ti < e)
      | none => false)
    let need := (if hasTransDel then 0 else 1) + (if inPlace then 0 else 1) + (if ofTt then 0 else 1)
    if n.size + need ≤ c.p.M then
      note (if inPlace then "leb.inplace" else "leb.newklong")
      let n1 := if hasTransDel then n.setAt (n.size - 1) (.del union) else n.add tt (.del union)
      let n2 := if inPlace then n1.repoint e jy else n1.add tt (.key 0 jy)
      putNode x n2
    else
      let last := n.lastVersionGivenDel tt del0
      match last.ks with
      | t :: .key c1 y1 :: r =>
        if c1 != jcv then
          throw s!"Bug: LE-b at {tt} in key node {x}: the last version does not start with the next child"
        note "leb.full"
        handleFull depth x { last with ks := t :: .key 0 y1 :: r }
      | _ => throw s!"Bug: LE-b at {tt} in key node {x}: the last version does not start with the next child"
  | none, _ => throw s!"Bug: LE-b at {tt} in key node {x}: no live klong of the empty key"
  | _, none => throw s!"Bug: LE-b at {tt} in key node {x}: no next child"

/-- `Dag.unlink`: x, which existed before the transaction, loses its klongs of
the transaction. -/
def unlink (x : NodeId) : M Unit := do
  let c ← read
  let n ← getNode x
  if n.lastTime == some c.i then putNode x (n.toPrev (c.i - 1))

/-- `Dag.retarget`: every key klong of the transaction in p that names `src`
names `dst` instead. -/
def retarget (p : NodeId) (src dst : NodeId) : M Unit := do
  let c ← read
  let n ← getNode p
  if n.lastTime == some c.i then
    let ti := n.lastTimeIndex.getD 0
    let ks := n.ks.zipIdx.map (fun (k, i) => match k with
      | .key cv y => if ti < i && y == src then Klong.key cv dst else k
      | _ => k)
    putNode p { n with ks := ks }

/-- `Dag.canTakeBack`. -/
def canTakeBack (x parent : NodeId) (cv : Nat) : M Bool := do
  let pn ← getNode parent
  pure ((← replacedBy x).isSome && (pn.linkIndex x cv).isSome)

/-- `Dag.takeBack`: x, made by a split of the transaction and emptied in it, is
taken back: its parent's klongs of the transaction that name it name the node it
replaced, and it is no node of the transaction. -/
def takeBack (x parent : NodeId) (cv : Nat) : M Unit := do
  let c ← read
  let pn ← getNode parent
  match (← replacedBy x), pn.linkIndex x cv with
  | some old, some _ =>
    if pn.lastTime != some c.i then
      throw s!"Bug: take back of key node {x} at {c.i}: no klong of tt to it"
    retarget parent x old
    takenBack x
    note "up.takeback"
  | _, _ => throw s!"Bug: take back of key node {x} at {c.i}: no node it replaces, or no klong to it"

/-- Down from key node x to the segment leaf for compare value cv, by
`searchLte` at the transaction's time, each node followed onto the key access
path (the loops of `Dag.setValue`, `setNode` and `descendToSegmentRoot`). No
klong at or below cv is `checkFound`'s "corrupt data". -/
def descendLte (cv : Nat) : Nat → NodeId → M NodeId
  | 0, x => throw s!"bounds: a descent from key node {x} went below the height bound"
  | f + 1, x => do
    let c ← read
    let n ← getNode x
    if n.leaf then pure x else
      match n.searchLte c.i cv with
      | none => throw s!"corrupt: key node {x}, not a segment leaf, has no klong at or below the key at {c.i}"
      | some fd =>
        pathAdd (some fd.c) fd.y
        descendLte cv f fd.y

/-- `Dag.descendToSegmentRoot` (and `descendToRootQuietly`, which differs only
in what it marks): from the space root by the key's first `segment` segments to
the root of the next segment's tree; rebuilds the key access path. -/
def descendToSegmentRoot (key : Key) (segment : Nat) : M NodeId := do
  let c ← read
  pathClear
  let root ← findRoot
  (key.take segment).foldlM (fun node cv => do
    let leaf ← descendLte cv c.p.fuel node
    let n ← getNode leaf
    match n.searchEq c.i cv with
    | none => throw s!"Bug: descent at {c.i}: segment {cv} not found"
    | some fd =>
      pathAdd (some fd.c) fd.y
      pure fd.y) root

/-- `Dag.takeBackRoot`: the root x, made by a split of the transaction, has one
live child, of its klong `only`: the klong of the transaction that links x names
the child instead, and x is taken back. -/
def takeBackRoot (x : NodeId) (depth only : Nat) : M Unit := do
  let c ← read
  let n ← getNode x
  match n.ptr? only with
  | none => throw s!"corrupt: root collapse at {c.i}: klong {only} of {x} is no key klong"
  | some child =>
    match depth with
    | 0 =>
      note "rc.takeback.space"
      newSuperRoot child
    | d + 1 =>
      note "rc.takeback.segment"
      let leaf ← pathNode d
      let ln ← getNode leaf
      let k ← klongAt (d + 1)
      match ln.linkIndex x k with
      | some j =>
        if ln.lastTime != some c.i then
          throw s!"Bug: root collapse at {c.i}: no klong of tt to root {x}"
        putNode leaf (ln.repoint j child)
      | none => throw s!"Bug: root collapse at {c.i}: no klong of tt to root {x}"
    takenBack x

/-- `Dag.replaceRoot`: the root x, which existed before the transaction, is
replaced by its one live child: the space root through the top node, a segment
root through a klong of its compare value in the segment leaf above. -/
def replaceRoot (x : NodeId) (depth only : Nat) : M Unit := do
  let c ← read
  let n ← getNode x
  match n.ptr? only with
  | none => throw s!"corrupt: root collapse at {c.i}: klong {only} of {x} is no key klong"
  | some child =>
    match depth with
    | 0 =>
      note "rc.replace.space"
      unlink x
      newSuperRoot child
    | d + 1 =>
      note "rc.replace.segment"
      let leaf ← pathNode d
      let k ← klongAt (d + 1)
      unlink x
      appendKlongs d leaf [(k, child)]

/-- `Dag.collapseRoot`, RC: while the root of the tree of segment `segment` on
the key's path is an inner node with one live klong, and not a node that the
transaction made otherwise than by a split, its child takes its place. -/
def collapseRoot (key : Key) (segment : Nat) : Nat → M Unit
  | 0 => throw "bounds: root collapse went below the height bound"
  | fuel + 1 => do
    let c ← read
    let root ← descendToSegmentRoot key segment
    let n ← getNode root
    if n.leaf then return
    let made := n.firstTime == some c.i
    if made && (← replacedBy root).isNone then return
    match n.onlyLiveKlong with
    | none => return
    | some only =>
      if n.cv? only != some 0 then
        throw s!"Bug: root collapse at {c.i}: the one live klong of root {root} is not the empty key"
      let depth := (← pathSize) - 1
      if made then takeBackRoot root depth only else replaceRoot root depth only
      collapseRoot key segment fuel

/-- The climb of `Dag.deleteUpward`: from the emptied node at `top` of the key
access path, the depth of the first node above that keeps a live klong; nothing
is changed. -/
def climb : Nat → M Nat
  | 0 => do
    let c ← read
    let x ← pathNode 0
    let n ← getNode x
    if !n.leaf then throw s!"Bug: the upward unlink at {c.i}: inner space root {x} is emptied"
    pure 0
  | t + 1 => do
    let c ← read
    let x ← pathNode (t + 1)
    let n ← getNode x
    let q ← pathNode t
    let k ← klongAt (t + 1)
    if n.firstTime == some c.i && !(← canTakeBack x q k) then
      throw s!"Bug: the upward unlink at {c.i}: key node {x}, made by the transaction and not by a split, is emptied"
    let pn ← getNode q
    if pn.allKeysIn (bitsUnion pn.lastBitmap (pn.bitsOf k)) then climb t else pure t

/-- `Dag.deleteUpward`: the delete of compare value cv, the key's last segment,
in the segment leaf at `depth` of the key access path. Returns true for a noop:
the key has no live klong. -/
def deleteUpward (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let _ ← appendDeleteKlong leaf depth cv
    return false
  -- The leaf is empty after the delete: UP.
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  -- The segment of the stop node's tree, from the path before it changes.
  let path := (← get).path
  let segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  -- The nodes below the stop node, lowest first: taken back, or unlinked.
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBack x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  if sn.leaf then
    note "up.stop-at-segment-leaf"
    let _ ← appendDeleteKlong s stop cs
    return false
  if sn.smallestLive != some 0 then
    throw s!"Bug: the upward unlink at {tt}: inner node {s} has no live klong of the empty key"
  if cs != 0 then
    let _ ← appendDeleteKlong s stop cs
  else
    emptyKeyNext s stop
  collapseRoot key segment (c.p.fuel)
  return false

/-! ## A put or a delete (`Dag.putKv`) -/

/-- `Dag.setValue`: the key's last segment, in the tree of `segRoot`. A put
makes the value, then adds its klong; a delete that deletes uses an id for its
marker. Returns true for a noop. -/
def setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  match value with
  | none =>
    let noop ← deleteUpward leaf ((← pathSize) - 1) cv key
    if !noop then
      let _ ← fresh
    pure noop
  | some h =>
    let v ← newValue h
    let n ← getNode leaf
    if n.size + 1 < c.p.M then putNode leaf (n.add c.i (.key cv v))
    else appendKlongs ((← pathSize) - 1) leaf [(cv, v)]
    pure false

/-- `Dag.setNode`: the tree of the next segment below compare value cv in the
tree of `segRoot`; a new segment leaf if there is none and `create`. -/
def setNode (segRoot : NodeId) (cv : Nat) (create : Bool) : M (Option NodeId) := do
  let c ← read
  let cur ← descendLte cv c.p.fuel segRoot
  let n ← getNode cur
  match n.searchEq c.i cv with
  | some fd =>
    pathAdd (some fd.c) fd.y
    pure (some fd.y)
  | none =>
    if !create then pure none else
      let (g, _) ← ghOf cur
      note "segment.new"
      let child ← newKey (g + 1) 0 true []
      if n.size + 1 < c.p.M then putNode cur (n.add c.i (.key cv child))
      else appendKlongs ((← pathSize) - 1) cur [(cv, child)]
      pure (some child)

/-- The loop of `Dag.putKv` over the key's segments. -/
def putSegs (key : Key) (value : Option Nat) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValue segRoot cv key value
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv value.isSome with
    | none => pure true
    | some next => putSegs key value rest next

/-- `Dag.putKv`: one operation. Returns true if it changed nothing (a delete of
a key with no live value). -/
def putKv (op : Op) : M Bool := do
  pathClear
  let root ← findRoot
  match op with
  | .put key h => putSegs key (some h) key root
  | .del key => putSegs key none key root

/-! ## A transaction (`Db.putKvs`) -/

/-- The super root as the writer has it (`TopDs.superRoot`): the top node of the
root's last entry. In P@(i-1) it is the root's live child. -/
def lastTop (view : View BVal) : Option NodeId :=
  match view root with
  | some r =>
    match r.hist.getLast? with
    | some ⟨_, .top z⟩ => some z
    | _ => none
  | none => none

/-- P@(i-1) without the root. The writer gets the root's last top node
(`lastTop`) and this view: it sees the root only through its live child, which is
the model's `ExecRootOK` (TP17). -/
def rootless (view : View BVal) : View BVal := fun x => if x == root then none else view x

/-- Top node z of P@(i-1), as the writer's super root. -/
def topOf (p : Params) (view : View BVal) (z : NodeId) : Except String Top :=
  match view z with
  | none => .error s!"corrupt: top node {z} is not in P@(i-1)"
  | some nd =>
    match nd.hist.findSome? (fun e => match e.val with
      | .rootKey y => some (e.time, y)
      | _ => none) with
    | some (t, y) =>
      let skips := nd.hist.filterMap (fun e => match e.val with
        | .skip j s => some (j, s)
        | _ => none)
      .ok { id := z, ord := p.ordOf nd.level, time := t, rootKey := y, skips := skips }
    | none => .error s!"corrupt: top node {z} has no root pointer"

/-- The changes of the writer's state w at time i (024-12, D7): the nodes made
and not taken back, by id; the entries of time i of every key node of the
overlay, the values' data, and the new top node's entries with the root's entry
for it, by node id. -/
def changesOf (i : Time) (w : W) : Changes BVal :=
  let new := (w.made.filter (fun n => !w.taken.contains n.id)).mergeSort
    (fun a b => decide (a.id ≤ b.id))
  let keyAdds := (w.nodes.filter (fun q => !w.taken.contains q.1)).flatMap (fun q =>
    ((entriesOf q.2.ks).filter (fun e => e.time == i)).map (fun e => (q.1, e.val)))
  let valAdds := w.vals.map (fun q => (q.1, BVal.data q.2))
  let topAdds : List (NodeId × BVal) :=
    if w.newTop then
      (root, BVal.top w.top.id) :: (w.top.id, BVal.rootKey w.top.rootKey) ::
        w.top.skips.map (fun q => (w.top.id, BVal.skip q.1 q.2))
    else []
  { new := new,
    adds := (keyAdds ++ valAdds ++ topAdds).mergeSort (fun a b => decide (a.1 ≤ b.1)) }

/-- The writer's run from its super root z and the view without the root. -/
def runOpsFrom (p : Params) (base : NodeId) (ops : List Op) (i : Time) (z : Option NodeId)
    (v : View BVal) : Except String (List Bool × W) :=
  match z with
  | none => .error "corrupt: the root has no top node"
  | some z =>
    match topOf p v z with
    | .error e => .error e
    | .ok top => ((ops.mapM putKv).run { p := p, i := i, view := v }).run { next := base, top := top }

/-- The writer's run of a list of operations at time i from P@(i-1): the final
state, and for each operation whether it was a noop. -/
def runOps (p : Params) (base : NodeId) (ops : List Op) (i : Time) (view : View BVal) :
    Except String (List Bool × W) :=
  runOpsFrom p base ops i (lastTop view) (rootless view)

/-- The tree's `exec`, with its errors: the changes of transaction tx at time i
from P@(i-1). The touch's nodes are added in SIS/Tree/Spec.lean (`exec`). -/
def exec? (p : Params) (tx : Tx) (i : Time) (view : View BVal) : Except String (Changes BVal) :=
  (runOps p tx.base tx.ops i view).map (fun r => changesOf i r.2)

end SIS.Tree
