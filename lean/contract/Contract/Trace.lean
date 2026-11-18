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
  /-- LIVE lines (with the exporter's live=1): Java's live children of a node
  at a time (bergdb 030-09). -/
  lives : List (NodeId × Time × List NodeId) := []
  /-- The top (bergdb 030-08): the skip pointers made (`ADD z i S j y`), the
  node of the last VER line, and the SKIPT lines of its version (z, j, t). -/
  skipLines : List (NodeId × Nat × NodeId) := []
  ver : NodeId := 0
  skipts : List (NodeId × Nat × Time) := []

/-- A trace: the node size, the writer's parameters, the transactions. -/
structure Trace where
  M : Nat := 0
  shape : ShapeParams := ⟨0, 0, 0⟩
  txs : Array TxLines := #[]

/-- A token is a number: one or more decimal digits and nothing else (`toNat?`
alone also takes `1_000`; bergdb 030-15). -/
def isNum (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

def num (s : String) : Except String Nat :=
  if isNum s then
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"not a number: {s}"
  else .error s!"not a number: {s}"

/-- A key `n c1 ... cn` or `-` at the front of the tokens. -/
def readKey : List String → Except String (Option Key × List String)
  | "-" :: r => .ok (none, r)
  | n :: r => do
    let n ← num n
    if r.length < n then throw "a key is cut short"
    let cs ← (r.take n).mapM num
    return (some cs, r.drop n)
  | [] => .error "a key is missing"

/-- The width of a delete bitmap: Java's has 62 bits, for the klongs at index 0 to
61 (Klong; `Dag.MAX_NODE_SIZE` is 62), so the number b of a `B b` klong is below
2^62 (bergdb 027-02, section 4; 030-19). -/
def bitmapBits : Nat := 62

/-- A token is a delete bitmap: a number below 2^62 (bergdb 030-19). -/
def isBitmap (s : String) : Bool := isNum s && decide (s.toNat?.getD 0 < 2 ^ bitmapBits)

/-- The bits of a bitmap written as a number, every one of them. Until bergdb 030-19
only bits 0 to 63 were read, so that a wider number was read in part (an independent
review, Codex 3: `B 2^64` was read as an empty bitmap); a bitmap of 2^62 or more is
now refused (`readKlongs`, and `klongToksOk` in Complete.lean). -/
def bitsOf (b : Nat) : List Nat := (List.range (b.log2 + 1)).filter (fun j => b.testBit j)

/-- `bitsOf b` holds bit j exactly if b has it. -/
theorem mem_bitsOf_iff {b j : Nat} : j ∈ bitsOf b ↔ b.testBit j = true := by
  simp only [bitsOf, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h
  refine Nat.lt_of_not_le fun hj => ?_
  have : b < 2 ^ j :=
    Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) hj)
  rw [Nat.testBit_lt_two_pow this] at h
  exact Bool.false_ne_true h

/-- n klongs at the front of the tokens. -/
def readKlongs : Nat → List String → Except String (List Klong)
  | 0, [] => .ok []
  | 0, _ :: _ => .error "a KN line with more tokens than its klongs"
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
    if 2 ^ bitmapBits ≤ b then throw s!"a delete bitmap wider than {bitmapBits} bits: B {b}"
    let ks ← readKlongs n r
    return .del (bitsOf b) :: ks
  | _, _ => .error "a KN line's klongs"

/-- r keys with their values at the front of the tokens. -/
def readKvs : Nat → List String → Except String (List (Key × Nat))
  | 0, [] => .ok []
  | 0, _ :: _ => .error "a SCAN line with more tokens than its results"
  | n + 1, toks => do
    let (k, r) ← readKey toks
    match k, r with
    | some k, v :: r' =>
      let v ← num v
      let rest ← readKvs n r'
      return (k, v) :: rest
    | _, _ => throw "a SCAN line's results"

/-- The kinds of line of trace format 3 that `readLine` does not read: their
grammar is checked by `lineFault` (Complete.lean; bergdb 030-15). -/
def skippedKinds : List String :=
  ["TRACE", "CONFIG", "DONE", "BASE", "TOUCH", "REC", "H", "F", "FA", "CUT", "PHYSCUT",
   "PROBE", "FIRST", "SLOT", "HMEM", "HTABLE", "HANDLE", "HOBJ", "HPTR"]

/-- One line. A line of a kind that the contract reads is read whole or the
trace is unreadable (bergdb 030-15: until then a line of an unmatched form,
such as `OP` alone or a SCAN in direction `BANANA`, was passed over or read
in part); a line of another kind of format 3 is passed over here, and its
grammar is `lineFault`'s. -/
def readLine (tr : Trace) (cur : TxLines) (line : String) : Except String (Trace × TxLines) := do
  let toks := (line.splitOn " ").filter (· ≠ "")
  if toks.head?.any (·.startsWith "#") then return (tr, cur)
  match toks with
  | "TREE" :: m :: g :: h :: k :: rest =>
    if !(g :: k :: rest).all isNum || !([0, 2, 3, 4].contains rest.length) then
      throw s!"a TREE line: {line}"
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
  | ["END", j] =>
    let _ ← num j
    return ({ tr with txs := tr.txs.push cur }, {})
  | ["NEW", x, l, "I"] => return (tr, { cur with news := cur.news ++ [((← num x), (← num l))] })
  | ["NEW", x, l, "D"] =>
    let _ ← num x
    let _ ← num l
    return (tr, cur)
  | ["ADD", y, t, "V", h] =>
    let _ ← num t
    return (tr, { cur with vals := cur.vals ++ [((← num y), (← num h))] })
  | ["ADD", "0", t, "T", z] =>
    let _ ← num t
    return (tr, { cur with tops := cur.tops ++ [(← num z)] })
  | ["ADD", z, t, "R", y] =>
    let _ ← num t
    return (tr, { cur with rootPtrs := cur.rootPtrs ++ [((← num z), (← num y))] })
  | ["ADD", z, t, "S", j, y] =>
    let _ ← num t
    return (tr, { cur with skipLines := cur.skipLines ++ [((← num z), (← num j), (← num y))] })
  | "ADD" :: x :: t :: "K" :: r =>
    if !(x :: t :: r).all isNum || r.length != 2 then throw s!"an ADD K line: {line}"
    return (tr, cur)
  | "ADD" :: x :: t :: "D" :: n :: r =>
    if !(x :: t :: r).all isNum || r.length != (← num n) then throw s!"an ADD D line: {line}"
    return (tr, cur)
  | "KN" :: x :: l :: n :: rest =>
    if l != "0" && l != "1" then throw s!"a KN line's kind: {line}"
    let ks ← readKlongs (← num n) rest
    return (tr, { cur with kns := cur.kns ++ [((← num x), l == "1", ks)] })
  | "OP" :: "P" :: rest =>
    match ← readKey rest with
    | (some k, [v]) => return (tr, { cur with ops := cur.ops ++ [.put k (← num v)] })
    | _ => throw "an OP P line"
  | "OP" :: d :: rest =>
    if d != "D" && d != "N" then throw s!"an OP line of kind {d}"
    match ← readKey rest with
    | (some k, []) => return (tr, { cur with ops := cur.ops ++ [.del k] })
    | _ => throw "an OP D or OP N line"
  | "LIVE" :: x :: t :: ys =>
    return (tr, { cur with lives := cur.lives ++ [((← num x), (← num t), ← ys.mapM num)] })
  | "GD" :: rest => return (tr, { cur with gd := ← rest.mapM num })
  | "DIRTY" :: rest =>
    let xs ← rest.mapM num
    if xs.length % 2 != 0 then throw s!"a DIRTY line: {line}"
    return (tr, { cur with dirty := (xs.zipIdx.filter (fun q => q.2 % 2 == 0)).map (·.1) })
  | "GET" :: t :: rest =>
    match ← readKey rest with
    | (some k, ["-"]) => return (tr, { cur with gets := cur.gets ++ [⟨(← num t), k, none⟩] })
    | (some k, [v]) =>
      return (tr, { cur with gets := cur.gets ++ [⟨(← num t), k, some (← num v)⟩] })
    | _ => throw "a GET line"
  | "SCAN" :: t :: d :: a :: b :: n :: rest =>
    if d != "F" && d != "B" then throw s!"a SCAN line's direction {d}"
    if a != "0" && a != "1" || b != "0" && b != "1" then throw s!"a SCAN line's ends: {line}"
    let (start, r1) ← readKey rest
    let (endKey, r2) ← readKey r1
    match r2 with
    | r :: kvs =>
      let res ← readKvs (← num r) kvs
      let req : ScanReq := { start := start, inclusive := a == "1", forward := d == "F",
                             endKey := endKey, endInclusive := b == "1" }
      return (tr, { cur with scans := cur.scans ++ [⟨(← num t), req, (← num n), res⟩] })
    | [] => throw "a SCAN line"
  | ["VER", x, k] =>
    if k != "I" && k != "D" then throw s!"a VER line: {line}"
    return (tr, { cur with ver := ← num x })
  | ["SKIPT", j, t] =>
    return (tr, { cur with skipts := cur.skipts ++ [(cur.ver, (← num j), (← num t))] })
  | k :: _ =>
    if skippedKinds.contains k then return (tr, cur)
    throw s!"a line the reader cannot read: {line}"
  | [] => return (tr, cur)

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
