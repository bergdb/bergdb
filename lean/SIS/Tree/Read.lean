/-
The tree model (bergdb 024-12): the readers. A get of a key at a time
(`Dag.getOne`), on P. Trusted part.

A reader gets P as a function from node id to node, as `Tree.exec` gets
P@(i-1); a lookup at time t reads a node's klongs up to t (`prefixAt`, in the
searches).
-/
import SIS.Tree.Exec

namespace SIS.Tree

open SIS SIS.Check

/-- The top node at time t: the one of the root's last entry at or before t
(`TopDs.findSuperRootAtTime`, without its search through the skip pointers;
024-12, D6). -/
def topAt (view : View BVal) (t : Time) : Option NodeId :=
  match view root with
  | some r =>
    match (r.hist.upTo t).getLast? with
    | some ⟨_, .top z⟩ => some z
    | _ => none
  | none => none

/-- The root key node of top node z. -/
def rootKeyOf (view : View BVal) (z : NodeId) : Option NodeId :=
  (view z).bind (fun nd => nd.hist.findSome? (fun e => match e.val with
    | .rootKey y => some y
    | _ => none))

/-- `TopDs.findRoot`: the space root at time t. -/
def rootAt (view : View BVal) (t : Time) : Option NodeId :=
  (topAt view t).bind (rootKeyOf view)

/-- Key node x of P, as klongs. -/
def knodeOf (p : Params) (view : View BVal) (x : NodeId) : Option KNode :=
  match view x with
  | some nd =>
    if nd.isData then none
    else some { leaf := p.heightOf nd.level == 0, ks := klongsOf nd.hist }
  | none => none

/-- The value of data node y, as its hash. -/
def valueOf (view : View BVal) (y : NodeId) : Option Nat :=
  match view y with
  | some nd =>
    if nd.isData then nd.hist.findSome? (fun e => match e.val with
      | .data h => some h
      | _ => none)
    else none
  | none => none

/-- `Dag.getEqNodeInSegment`: what compare value cv names at time t in the
segment tree of x: `searchLte` down to the segment leaf, `searchEq` in it. -/
def getEq (p : Params) (view : View BVal) (t : Time) (cv : Nat) : Nat → NodeId → Option NodeId
  | 0, _ => none
  | f + 1, x =>
    match knodeOf p view x with
    | none => none
    | some n =>
      if n.leaf then (n.searchEq t cv).map (·.y)
      else
        match n.searchLte t cv with
        | none => none
        | some fd => getEq p view t cv f fd.y

/-- The loop of `Dag.getOne` over the key's segments, from a segment root. -/
def getFrom (p : Params) (view : View BVal) (t : Time) : List Nat → NodeId → Option Nat
  | [], _ => none
  | [cv], r => (getEq p view t cv p.fuel r).bind (valueOf view)
  | cv :: rest, r =>
    match getEq p view t cv p.fuel r with
    | some y => if (knodeOf p view y).isSome then getFrom p view t rest y else none
    | none => none

/-- `Dag.getOne`: the value of the key at time t, as its hash; none if it has
none. -/
def get (p : Params) (view : View BVal) (t : Time) (key : Key) : Option Nat :=
  (rootAt view t).bind (getFrom p view t key)

/-! ## The scan (`GetMany.Chain`, `Dag.getMany`) -/

/-- Java's -1 as a compare value: before every key. -/
def cvLo : Int := -1

/-- Java's `Long.MAX_VALUE` as a compare value: after every key. -/
def cvHi : Int := 2 ^ 63 - 1

/-- What a scan is asked (`GetMany`'s input): the start key (none: from the first
key, or backward from the last), whether it is inclusive, the direction, and for
a forward scan the end key, if any, and whether it is inclusive. -/
structure ScanReq where
  start : Option Key := none
  inclusive : Bool := true
  forward : Bool := true
  endKey : Option Key := none
  endInclusive : Bool := true
  deriving Repr, Inhabited

/-- `GetMany.Chain`: the links, the last one first, each a node and a compare
value; the key segments passed; whether `next` has not run yet; whether the setup
ended at the start key (`setupEqMatch`); and the key nodes followed so far, for
the touch. -/
structure Chain where
  links : List (NodeId × Int) := []
  segs : List Nat := []
  first : Bool := true
  eqMatch : Bool := false
  seen : List NodeId := []
  deriving Repr, Inhabited

/-- The loop of `Chain.setup`: down from node x, with `index` segments of the
start key passed and `hasDiff` true once the chain has left the start key. -/
def setupGo (p : Params) (view : View BVal) (t : Time) (forward : Bool) (start : List Int) :
    Nat → NodeId → Nat → Bool → Chain → Chain
  | 0, _, _, _, ch => ch
  | f + 1, x, index, hasDiff, ch =>
    match knodeOf p view x with
    | none => ch
    | some n =>
      let sks : Int := match start[index]? with
        | some s => s
        | none => if forward then cvHi else cvLo
      let fd :=
        if hasDiff then (if forward then n.searchLt t cvHi else n.searchGt t cvLo)
        else if forward then n.searchLte t sks
        else if n.leaf then n.searchGte t sks
        else n.searchLte t sks
      match fd with
      | none =>
        let beforeFirst := !forward && !hasDiff && !n.leaf
        { ch with links := (x, if forward || beforeFirst then cvLo else cvHi) :: ch.links }
      | some fd =>
        let ch := { ch with links := (x, (fd.c : Int)) :: ch.links }
        if n.leaf && segLen fd.c < 7 then ch
        else
          let ch := { ch with seen := fd.y :: ch.seen }
          if n.leaf then
            setupGo p view t forward start f fd.y (index + 1) (hasDiff || (fd.c : Int) != sks)
              { ch with segs := ch.segs ++ [fd.c] }
          else setupGo p view t forward start f fd.y index hasDiff ch

/-- `Chain.eqMatch`: the setup ended at the start key itself. -/
def chainEq (ch : Chain) (start : Option Key) : Bool :=
  match start, ch.links.head? with
  | some k, some (_, lc) =>
    ch.segs.length + 1 == k.length && ch.segs == k.take ch.segs.length &&
      (k.getLast?.map (fun (c : Nat) => (c : Int))) == some lc
  | _, _ => false

/-- `Chain.setup`: the chain at or before the start key, from the space root. -/
def chainSetup (p : Params) (view : View BVal) (t : Time) (req : ScanReq) (rootKey : NodeId) :
    Chain :=
  let start : List Int := match req.start with
    | some k => k.map (fun (c : Nat) => (c : Int))
    | none => [if req.forward then cvLo else cvHi]
  let ch := setupGo p view t req.forward start p.fuel rootKey 0 false {}
  { ch with eqMatch := chainEq ch req.start }

/-- `Chain.isPastEnd`: the key segments passed and compare value cv, a lower
bound of every key from the klong found on, are after the end key, or at it when
the end is not inclusive. -/
def pastEnd (segs : List Nat) (cv : Nat) (endKey : Key) (endInclusive : Bool) : Bool :=
  let k := segs ++ [cv]
  keyLt endKey k || (k == endKey && !endInclusive)

/-- A KV that a scan gives: the key, the value's hash, the time of the key's
klong (`Kvt`). -/
structure Kvt where
  key : Key
  h : Nat
  time : Time
  deriving DecidableEq, Repr, Inhabited

/-- The chain when a scan has ended. -/
def Chain.done (ch : Chain) : Chain := { ch with links := [], segs := [] }

/-- `Chain.next`: the next KV in the scan's order, and the chain after it; none
at the end. The first argument bounds the steps: each one goes up a link, goes
down one, or ends. -/
def nextGo (p : Params) (view : View BVal) (t : Time) (req : ScanReq) :
    Nat → Chain → Option Kvt × Chain
  | 0, ch => (none, ch.done)
  | f + 1, ch =>
    match ch.links with
    | [] => (none, ch)
    | (x, lc) :: rest =>
      match knodeOf p view x with
      | none => (none, ch.done)
      | some n =>
        let fd :=
          if ch.first && req.inclusive && ch.eqMatch then
            (if req.forward then n.searchGte t lc else n.searchLte t lc)
          else (if req.forward then n.searchGt t lc else n.searchLt t lc)
        let ch := { ch with first := false }
        match fd with
        | none =>
          let segs := match rest with
            | (q, _) :: _ =>
              if ((knodeOf p view q).map (·.leaf)) == some true then ch.segs.dropLast else ch.segs
            | [] => ch.segs
          nextGo p view t req f { ch with links := rest, segs := segs }
        | some fd =>
          let past := match req.endKey with
            | some e => pastEnd ch.segs fd.c e req.endInclusive
            | none => false
          if past then (none, ch.done)
          else
            let links := (x, (fd.c : Int)) :: rest
            match view fd.y with
            | none => (none, ch.done)
            | some nd =>
              if nd.isData then
                match valueOf view fd.y with
                | some h => (some ⟨ch.segs ++ [fd.c], h, fd.time⟩, { ch with links := links })
                | none => (none, ch.done)
              else
                nextGo p view t req f
                  { ch with links := (fd.y, if req.forward then cvLo else cvHi) :: links,
                            segs := if n.leaf then ch.segs ++ [fd.c] else ch.segs,
                            seen := fd.y :: ch.seen }

/-- The steps a scan may take before it is cut short; no run reaches it. -/
def scanFuel : Nat := 2 ^ 40

/-- The loop of `Dag.getMany` with `GetMany.GetN`: at most `limit` KVs. -/
def scanGo (p : Params) (view : View BVal) (t : Time) (req : ScanReq) (limit : Nat) :
    Nat → Chain → List Kvt → List Kvt
  | 0, _, acc => acc
  | f + 1, ch, acc =>
    if acc.length ≥ limit then acc else
      match nextGo p view t req scanFuel ch with
      | (none, _) => acc
      | (some kv, ch') => scanGo p view t req limit f ch' (acc ++ [kv])

/-- `Dag.getMany` at time t with `GetN(limit)`: the first `limit` KVs of the scan. -/
def scan (p : Params) (view : View BVal) (t : Time) (req : ScanReq) (limit : Nat) : List Kvt :=
  match rootAt view t with
  | none => []
  | some r => scanGo p view t req limit limit (chainSetup p view t req r) []

/-- The loop of `Db.touchRange`: the scan goes on until a key after `to`, or the
end; the chain then has every key node it followed. -/
def touchGo (p : Params) (view : View BVal) (t : Time) (req : ScanReq) (to : Option Key) :
    Nat → Chain → Chain
  | 0, ch => ch
  | f + 1, ch =>
    match nextGo p view t req scanFuel ch with
    | (none, ch') => ch'
    | (some kv, ch') =>
      let stop := match to with
        | some e => keyLt e kv.key
        | none => false
      if stop then ch' else touchGo p view t req to f ch'

/-- The touch of a reclaim step (`Db.touchRange`): the index nodes that the
writer's scan follows at time t for the keys after `src` up to the first key
after `to`: the super root, the space root, and the key nodes of the chain;
sorted by id. -/
def touchOf (p : Params) (view : View BVal) (t : Time) (src to : Option Key) : List NodeId :=
  match topAt view t with
  | none => []
  | some z =>
    match rootKeyOf view z with
    | none => [z]
    | some r =>
      let req : ScanReq := { start := src, inclusive := false }
      let ch := touchGo p view t req to scanFuel (chainSetup p view t req r)
      ((z :: r :: ch.seen).eraseDups).mergeSort (fun a b => decide (a ≤ b))

end SIS.Tree
