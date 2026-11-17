/-
The contract package (bergdb 030-04, section 7.4 (d)): a reader of trace
format 3 (bergdb 027-02, section 4), written from that description. It reads
what the contract needs: the TREE line, and of each transaction the
operations (OP), the nodes made with their levels (NEW), the values and the
top's root pointers (ADD), the key nodes as klongs (KN), the dirty nodes
(GD: the nodes that got dirty; DIRTY: D after the record), and Java's reads
(GET, SCAN).
-/
import Contract.Check
import Contract.Shape

namespace Contract

/-- A GET line: the time, the key, Java's answer. -/
structure GetLine where
  t : Time
  key : Key
  v : Option Nat

/-- A SCAN line: the time, the request, the limit, Java's answer. -/
structure ScanLine where
  t : Time
  req : ScanReq
  limit : Nat
  res : List (Key × Nat)

/-- One transaction of a trace. -/
structure TxLines where
  i : Nat := 0
  ops : List Op := []
  news : List (NodeId × Nat) := []
  vals : List (NodeId × Nat) := []
  tops : List NodeId := []
  rootPtrs : List (NodeId × NodeId) := []
  kns : List (NodeId × Bool × List Klong) := []
  gd : List NodeId := []
  dirty : List NodeId := []
  gets : List GetLine := []
  scans : List ScanLine := []
  /-- The top (bergdb 030-08): the skip pointers made (`ADD z i S j y`), the
  LIVE 0 lines (Java's top node at time t, none if it found none), the node
  of the last VER line, and the SKIPT lines of its version (z, j, t). -/
  skipLines : List (NodeId × Nat × NodeId) := []
  lives : Array (Time × Option NodeId) := #[]
  ver : NodeId := 0
  skipts : List (NodeId × Nat × Time) := []

/-- A trace: the node size, the writer's parameters, the transactions. -/
structure Trace where
  M : Nat := 0
  shape : ShapeParams := ⟨0, 0, 0⟩
  txs : Array TxLines := #[]

def num (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"not a number: {s}"

/-- A key `n c1 ... cn` or `-` at the front of the tokens. -/
def readKey : List String → Except String (Option Key × List String)
  | "-" :: r => .ok (none, r)
  | n :: r => do
    let n ← num n
    if r.length < n then throw "a key is cut short"
    let cs ← (r.take n).mapM num
    return (some cs, r.drop n)
  | [] => .error "a key is missing"

/-- The bits of a bitmap written as a number. -/
def bitsOf (b : Nat) : List Nat := (List.range 64).filter (fun j => b.testBit j)

/-- n klongs at the front of the tokens. -/
def readKlongs : Nat → List String → Except String (List Klong)
  | 0, _ => .ok []
  | n + 1, "T" :: t :: r => do
    let t ← num t
    let ks ← readKlongs n r
    return .time t :: ks
  | n + 1, "K" :: c :: y :: r => do
    let c ← num c
    let y ← num y
    let ks ← readKlongs n r
    return .key c y :: ks
  | n + 1, "B" :: b :: r => do
    let b ← num b
    let ks ← readKlongs n r
    return .del (bitsOf b) :: ks
  | _, _ => .error "a KN line's klongs"

/-- r keys with their values at the front of the tokens. -/
def readKvs : Nat → List String → Except String (List (Key × Nat))
  | 0, _ => .ok []
  | n + 1, toks => do
    let (k, r) ← readKey toks
    match k, r with
    | some k, v :: r' =>
      let v ← num v
      let rest ← readKvs n r'
      return (k, v) :: rest
    | _, _ => throw "a SCAN line's results"

def readLine (tr : Trace) (cur : TxLines) (line : String) : Except String (Trace × TxLines) := do
  match (line.splitOn " ").filter (· ≠ "") with
  | "TREE" :: m :: _ :: h :: _ :: rest =>
    let m ← num m
    let h ← num h
    let mb ← match rest with
      | mb :: _ => num mb
      | [] => pure 0
    let th ← match rest with
      | _ :: _ :: _ :: th :: _ => num th
      | _ => pure 0
    return ({ tr with M := m, shape := ⟨h, mb, th⟩ }, cur)
  | ["TX", i] => return (tr, { i := (← num i) })
  | ["END", _] => return ({ tr with txs := tr.txs.push cur }, {})
  | ["NEW", x, l, "I"] => return (tr, { cur with news := cur.news ++ [((← num x), (← num l))] })
  | ["ADD", y, _, "V", h] => return (tr, { cur with vals := cur.vals ++ [((← num y), (← num h))] })
  | ["ADD", "0", _, "T", z] => return (tr, { cur with tops := cur.tops ++ [(← num z)] })
  | ["ADD", z, _, "R", y] =>
    return (tr, { cur with rootPtrs := cur.rootPtrs ++ [((← num z), (← num y))] })
  | "KN" :: x :: l :: n :: rest =>
    let ks ← readKlongs (← num n) rest
    return (tr, { cur with kns := cur.kns ++ [((← num x), l == "1", ks)] })
  | "OP" :: "P" :: rest =>
    match ← readKey rest with
    | (some k, [v]) => return (tr, { cur with ops := cur.ops ++ [.put k (← num v)] })
    | _ => throw "an OP P line"
  | "OP" :: _ :: rest =>
    match ← readKey rest with
    | (some k, []) => return (tr, { cur with ops := cur.ops ++ [.del k] })
    | _ => throw "an OP D or OP N line"
  | "GD" :: rest => return (tr, { cur with gd := ← rest.mapM num })
  | "DIRTY" :: rest =>
    let xs ← rest.mapM num
    return (tr, { cur with dirty := (xs.zipIdx.filter (fun q => q.2 % 2 == 0)).map (·.1) })
  | "GET" :: t :: rest =>
    match ← readKey rest with
    | (some k, ["-"]) => return (tr, { cur with gets := cur.gets ++ [⟨(← num t), k, none⟩] })
    | (some k, [v]) =>
      return (tr, { cur with gets := cur.gets ++ [⟨(← num t), k, some (← num v)⟩] })
    | _ => throw "a GET line"
  | "SCAN" :: t :: d :: a :: b :: n :: rest =>
    let (start, r1) ← readKey rest
    let (endKey, r2) ← readKey r1
    match r2 with
    | r :: kvs =>
      let res ← readKvs (← num r) kvs
      let req : ScanReq := { start := start, inclusive := a == "1", forward := d == "F",
                             endKey := endKey, endInclusive := b == "1" }
      return (tr, { cur with scans := cur.scans ++ [⟨(← num t), req, (← num n), res⟩] })
    | [] => throw "a SCAN line"
  | ["ADD", z, _, "S", j, y] =>
    return (tr, { cur with skipLines := cur.skipLines ++ [((← num z), (← num j), (← num y))] })
  | "LIVE" :: "0" :: t :: rest =>
    let z ← match rest with
      | [z] => pure (some (← num z))
      | [] => pure none
      | _ => throw "a LIVE 0 line"
    return (tr, { cur with lives := cur.lives.push ((← num t), z) })
  | ["VER", x, _] => return (tr, { cur with ver := ← num x })
  | ["SKIPT", j, t] =>
    return (tr, { cur with skipts := cur.skipts ++ [(cur.ver, (← num j), (← num t))] })
  | _ => return (tr, cur)

/-- Reads a trace from its lines. -/
def readTrace (lines : Array String) : Except String Trace := do
  let mut tr : Trace := {}
  let mut cur : TxLines := {}
  for line in lines do
    (tr, cur) ← readLine tr cur line
  return tr

/-- The heap after a transaction's lines, from the heap before it: the values
made, the key nodes made or changed as their KN lines give them (a node made
has the level of its NEW line, a node changed keeps its level), and the space
root of each top node made. -/
def applyTx (h : Heap) (tx : TxLines) : Heap :=
  let objs := tx.vals.foldl (fun m (y, v) => m.insert y (.val v)) h.objs
  let objs := tx.kns.foldl (fun m (x, leaf, ks) =>
    let level := match tx.news.lookup x with
      | some l => l
      | none =>
        match h.objs[x]? with
        | some (.key n) => n.level
        | _ => 0
    m.insert x (.key { level := level, leaf := leaf, ks := ks })) objs
  let roots := tx.tops.foldl (fun rs z => match tx.rootPtrs.lookup z with
    | some y => rs ++ [(tx.i, y)]
    | none => rs) h.roots
  { objs := objs, roots := roots }

end Contract
