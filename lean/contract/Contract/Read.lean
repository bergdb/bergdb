/-
The contract package (bergdb 030-04): the readers, a get (`Dag.getOne`) and a
scan (`GetMany.Chain`, `Dag.getMany`), on a tree. A read at time t is the
reader on the tree at t: `get (s.at t) key`, `scan (s.at t) req limit`.

The scan is copied from the old model (lean/SIS/Tree/Read.lean, bergdb
024-12: `setupGo`, `chainEq`, `pastEnd`, `nextGo`, `scanGo`) and adapted to
this package's tree; the get is the old `getEq` and `getFrom` as one loop.
Everything here runs; nothing needs Mathlib.
-/
import Contract.Tree

namespace Contract

/-! ## Get (`Dag.getOne`) -/

/-- The loop of `Dag.getOne` from key node x, for the key segments left: in
an inner node the child of the last klong at or below the segment
(`searchLte`), in a segment leaf the klong of the segment (`searchEq`), which
names the value for the key's last segment and the next segment's tree for
any other. -/
def getGo (s : Tree) : Nat → Key → NodeId → Option Nat
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | f + 1, c :: rest, x =>
    match s.obj x with
    | some (.key n) =>
      if n.leaf then
        match searchEq n.ks c with
        | none => none
        | some y =>
          match rest with
          | [] => s.val y
          | _ :: _ => getGo s f rest y
      else
        match searchLte n.ks (.at c) with
        | none => none
        | some (_, y) => getGo s f (c :: rest) y
    | _ => none

/-- `Dag.getOne`: the value of the key, as its hash; none if it has none. -/
def get (s : Tree) (key : Key) : Option Nat :=
  match s.root with
  | some r => getGo s (s.fuel r) key r
  | none => none

/-! ## Scan (`GetMany.Chain`, `Dag.getMany`) -/

/-- What a scan is asked (`GetMany`'s input): the start key (none: from the
first key, or backward from the last), whether it is inclusive, the direction,
and for a forward scan the end key, if any, and whether it is inclusive. -/
structure ScanReq where
  start : Option Key := none
  inclusive : Bool := true
  forward : Bool := true
  endKey : Option Key := none
  endInclusive : Bool := true
  deriving Repr, Inhabited

/-- `GetMany.Chain`: the links, the last one first, each a node and a
position in it; the key segments passed; whether `next` has not run yet;
whether the setup ended at the start key (`setupEqMatch`). -/
structure Chain where
  links : List (NodeId × Pos) := []
  segs : List Nat := []
  first : Bool := true
  eqMatch : Bool := false
  deriving Repr, Inhabited

/-- The segment of the start key that `Chain.setup` looks for with `index`
segments passed: past the key's end, `Long.MAX_VALUE` forward and -1
backward. -/
def startSeg (forward : Bool) (start : List Pos) (index : Nat) : Pos :=
  match start[index]? with
  | some p => p
  | none => if forward then .hi else .lo

/-- The search of `Chain.setup` in one node: once the chain has left the
start key, the last klong forward and the first one backward; else the last
klong at or below the start key's segment, but backward in a segment leaf the
first one at or above it. -/
def setupSearch (forward hasDiff leaf : Bool) (ks : List Klong) (sks : Pos) :
    Option (Nat × NodeId) :=
  if hasDiff then (if forward then searchLt ks .hi else searchGt ks .lo)
  else if forward then searchLte ks sks
  else if leaf then searchGte ks sks
  else searchLte ks sks

/-- The loop of `Chain.setup`: down from node x, with `index` segments of the
start key passed and `hasDiff` true once the chain has left the start key. -/
def setupGo (s : Tree) (forward : Bool) (start : List Pos) :
    Nat → NodeId → Nat → Bool → Chain → Chain
  | 0, _, _, _, ch => ch
  | f + 1, x, index, hasDiff, ch =>
    match s.obj x with
    | some (.key n) =>
      match setupSearch forward hasDiff n.leaf n.ks (startSeg forward start index) with
      | none =>
        let beforeFirst := !forward && !hasDiff && !n.leaf
        { ch with links := (x, if forward || beforeFirst then .lo else .hi) :: ch.links }
      | some (c, y) =>
        if n.leaf && !isLong c then { ch with links := (x, .at c) :: ch.links }
        else if n.leaf then
          setupGo s forward start f y (index + 1)
            (hasDiff || !(startSeg forward start index).is c)
            { ch with links := (x, .at c) :: ch.links, segs := ch.segs ++ [c] }
        else setupGo s forward start f y index hasDiff
          { ch with links := (x, .at c) :: ch.links }
    | _ => ch

/-- `Chain.eqMatch`: the setup ended at the start key itself. -/
def chainEq (ch : Chain) (start : Option Key) : Bool :=
  match start, ch.links.head? with
  | some k, some (_, .at lc) =>
    ch.segs.length + 1 == k.length && ch.segs == k.take ch.segs.length &&
      k.getLast? == some lc
  | _, _ => false

/-- The start key as `Chain.setup` has it: its segments; without a start key,
the one segment -1 forward and `Long.MAX_VALUE` backward. -/
def startPos (req : ScanReq) : List Pos :=
  match req.start with
  | some k => k.map Pos.at
  | none => [if req.forward then .lo else .hi]

/-- `Chain.setup`: the chain at or before the start key, from the space root
r with fuel f. -/
def chainSetup (s : Tree) (req : ScanReq) (f : Nat) (r : NodeId) : Chain :=
  let ch := setupGo s req.forward (startPos req) f r 0 false {}
  { ch with eqMatch := chainEq ch req.start }

/-- The order of keys: that of their segments' compare values, the first
difference deciding, a key before its extensions (`Keys.compareKeys`). -/
def keyLt : Key → Key → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: l₁, b :: l₂ => decide (a < b) || (a == b && keyLt l₁ l₂)

/-- `Chain.isPastEnd`: the key segments passed and compare value cv, a lower
bound of every key from the klong found on, are after the end key, or at it
when the end is not inclusive. -/
def pastEnd (segs : List Nat) (cv : Nat) (endKey : Key) (endInclusive : Bool) : Bool :=
  let k := segs ++ [cv]
  keyLt endKey k || (k == endKey && !endInclusive)

/-- The chain when a scan has ended. -/
def Chain.done (ch : Chain) : Chain := { ch with links := [], segs := [], first := false }

/-- The search of `Chain.next` in the last link's node, from the link's
position: the next klong in the scan's order, or the klong at the position
itself for the first `next` of a scan that includes its start key and was set
up at it. -/
def nextSearch (forward incl : Bool) (ks : List Klong) (lc : Pos) : Option (Nat × NodeId) :=
  if incl then (if forward then searchGte ks lc else searchLte ks lc)
  else (if forward then searchGt ks lc else searchLt ks lc)

/-- `Chain.isPastEnd` with the request's end key, if it has one. -/
def past (req : ScanReq) (segs : List Nat) (c : Nat) : Bool :=
  match req.endKey with
  | some e => pastEnd segs c e req.endInclusive
  | none => false

/-- The key segments passed, after the last link is removed
(`removeKeySegment` if the link below it is a segment leaf's). -/
def segsUp (s : Tree) (rest : List (NodeId × Pos)) (segs : List Nat) : List Nat :=
  match rest with
  | (q, _) :: _ =>
    (match s.obj q with
     | some (.key m) => if m.leaf then segs.dropLast else segs
     | _ => segs)
  | [] => segs

/-- `Chain.next`: the next key and value in the scan's order, and the chain
after it; none at the end. A step goes up a link, goes down one, or ends; the
fuel bounds the steps. -/
def nextGo (s : Tree) (req : ScanReq) : Nat → Chain → Option (Key × Nat) × Chain
  | 0, ch => (none, ch.done)
  | f + 1, ch =>
    match ch.links with
    | [] => (none, ch)
    | (x, lc) :: rest =>
      match s.obj x with
      | some (.key n) =>
        match nextSearch req.forward (ch.first && req.inclusive && ch.eqMatch) n.ks lc with
        | none =>
          nextGo s req f { ch with first := false, links := rest, segs := segsUp s rest ch.segs }
        | some (c, y) =>
          if past req ch.segs c then (none, ch.done)
          else
            match s.obj y with
            | none => (none, ch.done)
            | some (.val h) =>
              (some (ch.segs ++ [c], h),
                { ch with first := false, links := (x, Pos.at c) :: rest })
            | some (.key _) =>
              nextGo s req f
                { ch with first := false,
                          links := (y, if req.forward then .lo else .hi) :: (x, Pos.at c) :: rest,
                          segs := if n.leaf then ch.segs ++ [c] else ch.segs }
      | _ => (none, ch.done)

/-- The loop of `Dag.getMany` with `GetMany.GetN`: at most `limit` keys and
values; `nf` is the fuel of each `next`. -/
def scanGo (s : Tree) (req : ScanReq) (nf : Nat) : Nat → Chain → List (Key × Nat)
  | 0, _ => []
  | limit + 1, ch =>
    match nextGo s req nf ch with
    | (none, _) => []
    | (some kv, ch') => kv :: scanGo s req nf limit ch'

/-- `Dag.getMany` with `GetN(limit)`: the first `limit` keys and values of the
scan. A `next` climbs at most the chain and descends at most one path, each
at most the root's fuel. -/
def scan (s : Tree) (req : ScanReq) (limit : Nat) : List (Key × Nat) :=
  match s.root with
  | some r =>
    scanGo s req (2 * s.fuel r + 2) limit (chainSetup s req (s.fuel r) r)
  | none => []

end Contract
