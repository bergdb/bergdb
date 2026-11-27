/-
The tree checker (bergdb 024-12, section 2.7; 027-02, section
4): reads the lines of trace format 3 and runs the tree model
(SIS/Tree/*.lean) against Java's run. Not part of the trusted part: this file
only says how a trace becomes the model's objects, and what is compared.
-/
import Check.Trace
import SIS.Tree.DeadProps
import SIS.Tree.Top
import SIS.Tree.Pe
import Std.Data.HashMap

namespace SIS.Check

/-- The key of reclaim's row, the iteration in progress (bergdb 030-35): Java's
`Reclaim.CURRENT_KEY_NAME`, `-current.txt` under `/#i/dreclaim/`, as `Keys.toSegments`
makes it, which is how a trace writes a key; the model's `Contract.reclaimRow` (lean/contract's
Contract/ReclaimSteps.lean), the key at which `StepTx` requires every step to put its row.
Contract/ReclaimValuesExample.lean proves the two equal (`checker_row`). Until 2026-11-23
C-STEP took the row's key from the trace's first step, so that a changed value of a key
met could pass as the row (bergdb 030-39, F1). In this file since bergdb 031-06 (until then
in Check/Steps.lean): a step's touch is the paths of its copies and of the row (C-T5, C-T9). -/
def reclaimRowKey : SIS.Tree.Key :=
  [0x495ac0599d19f8, 0x195b98dadbc04bf8, 0x195ddd1d19dc1db8, 0xc1d9e9d80000020]

/-- A key of reclaim's reserved prefix, `/#i/dreclaim/` (the row, the table, the settings):
the bounds of the model's `Contract.reclaimKey` (Contract/ReclaimSteps.lean), its byte-key
encoding as compare values, the upper bound with its last byte incremented (bergdb 031-06). -/
def reclaimReserved (k : SIS.Tree.Key) : Bool :=
  !SIS.Tree.keyLt k [0x495ac0599d19f8, 0x195b98dadbc04030] &&
    SIS.Tree.keyLt k [0x495ac0599d19f8, 0x195b98dadbc08030]

#guard reclaimReserved reclaimRowKey
#guard !reclaimReserved [8]

end SIS.Check

namespace SIS.Check.Tree

open SIS SIS.Check SIS.Tree

/-- A SCAN line: the time, what was asked, the limit, and Java's KVs, each a key
and its value's hash. -/
structure TScan where
  t : Nat
  req : ScanReq
  limit : Nat
  results : List (Key × Nat)
  deriving Inhabited

/-- A STEP line (bergdb 030-27; 027-02, section 4): a step of reclaim, from its
iteration's row in Java's memory: t0, the record of the iteration's tStart; c, the first
record at or after its pCut; lastKey before the step and after it (none: `-`); and eod,
whether the step's scan passed the end and ended the iteration. -/
structure TStep where
  t0 : Nat
  c : Nat
  last : Option Key
  next : Option Key
  eod : Bool
  deriving BEq, Repr, Inhabited

/-- A RESUME line (bergdb 030-31; 027-02, section 4): the iteration in progress that the
start after a restart read from the stream: t0, c, lastKey (none: `-`) and endKey, E (none:
`-`, no key was live at tStart). -/
structure TResume where
  t0 : Nat
  c : Nat
  last : Option Key
  e : Option Key
  deriving BEq, Repr, Inhabited

/-- The tree lines of one transaction, `TX i` to `END i`. -/
structure TTx where
  idx : Nat
  base : Option Nat := none
  /-- The OP lines, in order; true for `OP N`, a delete that was a noop. An `OP C` (a copy of
  reclaim's step, the copy mark of its value node; bergdb 031-06) is a put here, and its key is
  in `copies` too. -/
  ops : Array (SIS.Tree.Op × Bool) := #[]
  /-- The keys of the `OP C` lines, in order: the record's copies (bergdb 031-06). -/
  copies : Array Key := #[]
  /-- ACT lines (bergdb 031-06; with the exporter's steps=1): the record's action as submitted,
  its puts with their values' hashes and its deletes, in the order given. -/
  acts : Array SIS.Tree.Op := #[]
  /-- KN lines: Java's key nodes after the transaction. -/
  kns : Array (NodeId × KNode) := #[]
  /-- GET lines: the time, the key, and Java's answer (a value's hash). -/
  gets : Array (Nat × Key × Option Nat) := #[]
  /-- SCAN lines. -/
  scans : Array TScan := #[]
  /-- STEP lines (bergdb 030-27): one in a step of reclaim, with the exporter's steps=1. -/
  steps : Array TStep := #[]
  /-- RESTART (bergdb 030-31): run A's database was started again after this transaction,
  after a stop (`stop`) or a crash right after its record's commit (`crash`). -/
  restart : Option String := none
  /-- The RESUME line after a restart (bergdb 030-31): `some none` for `RESUME -`, no
  iteration in progress. -/
  resume : Option (Option TResume) := none
  deriving Inhabited

/-- The tree lines of a trace. -/
structure TTrace where
  /-- The TREE line: M, G, H and the primordial key node's id; with merges, m and
  c, and rule O's h (024-22, section 2.5); and option 2's theta (024-23). -/
  tree : Option (Params × NodeId) := none
  txs : Array TTx := #[]
  bad : Array String := #[]

/-- A key as `n c1 ... cn` at the head of a token list: the key, and the rest. -/
def takeKey : List String → Option (Key × List String)
  | n :: r => do
    let n ← n.toNat?
    if r.length < n then none else
      let k ← (r.take n).mapM String.toNat?
      some (k, r.drop n)
  | [] => none

/-- A key or `-`. -/
def takeKeyOpt : List String → Option (Option Key × List String)
  | "-" :: r => some (none, r)
  | ts => (takeKey ts).map (fun (k, r) => (some k, r))

/-- The indexes of the bits of a bitmap given as a number. -/
def bitsOfMask (m : Nat) : List Nat := (List.range 62).filter (fun i => m.testBit i)

/-- The klongs of a KN line: `T t`, `K c y`, `B b`. -/
def parseKlongs : List String → Option (List Klong)
  | [] => some []
  | "T" :: t :: r => do
    let t ← t.toNat?
    let ks ← parseKlongs r
    some (.time t :: ks)
  | "K" :: c :: y :: r => do
    let c ← c.toNat?
    let y ← y.toNat?
    let ks ← parseKlongs r
    some (.key c y :: ks)
  | "B" :: b :: r => do
    let b ← b.toNat?
    let ks ← parseKlongs r
    some (.del (bitsOfMask b) :: ks)
  | _ => none

/-- k results of a SCAN line: each a key and a hash. -/
def takeResults : Nat → List String → Option (List (Key × Nat))
  | 0, [] => some []
  | 0, _ :: _ => none
  | k + 1, r => do
    let (key, r) ← takeKey r
    match r with
    | h :: r => do
      let h ← h.toNat?
      let rest ← takeResults k r
      some ((key, h) :: rest)
    | [] => none

/-- A SCAN line after its first token: `t d a b n start end r kv1 ... kvr`. -/
def parseScan : List String → Option TScan
  | t :: d :: a :: b :: n :: r => do
    let t ← t.toNat?
    let n ← n.toNat?
    let (start, r) ← takeKeyOpt r
    let (endKey, r) ← takeKeyOpt r
    match r with
    | cnt :: r => do
      let cnt ← cnt.toNat?
      let res ← takeResults cnt r
      if (d != "F" && d != "B") || (a != "0" && a != "1") || (b != "0" && b != "1") then none
      else some { t := t, limit := n, results := res,
                  req := { start := start, inclusive := a == "1", forward := d == "F",
                           endKey := endKey, endInclusive := b == "1" } }
    | [] => none
  | _ => none

def modTx (t : TTrace) (f : TTx → TTx) : TTrace :=
  if t.txs.isEmpty then { t with bad := t.bad.push "a tree line outside TX ... END" }
  else { t with txs := t.txs.modify (t.txs.size - 1) f }

def parseTreeLine (t : TTrace) (n : Nat) (line : String) : TTrace :=
  let bad := fun (s : String) => { t with bad := t.bad.push s!"line {n}: {s}: {line}" }
  if line.startsWith "#" then t else
  match toks line with
  | ["TREE", m, g, h, k] => match m.toNat?, g.toNat?, h.toNat?, k.toNat? with
    | some m, some g, some h, some k => { t with tree := some ({ M := m, G := g, H := h }, k) }
    | _, _, _, _ => bad "bad TREE"
  -- With the merges' thresholds m and c (bergdb 024-22, section 2.5). Rule O's h
  -- is c: h = c in every set that a writer of format 7 has had (P5's B / 2, 024-14's
  -- m8 17 B / 30); a line of 8 tokens gives h of its own.
  | ["TREE", m, g, h, k, mb, mm] =>
    match m.toNat?, g.toNat?, h.toNat?, k.toNat?, mb.toNat?, mm.toNat? with
    | some m, some g, some h, some k, some mb, some mm =>
      { t with tree := some ({ M := m, G := g, H := h, mergeBelow := mb, mergeMax := mm,
                               splitAbove := mm }, k) }
    | _, _, _, _, _, _ => bad "bad TREE"
  -- And rule O's h (record format 7, 024-14's m8: h is no longer M / 2).
  | ["TREE", m, g, h, k, mb, mm, sa] =>
    match m.toNat?, g.toNat?, h.toNat?, k.toNat?, mb.toNat?, mm.toNat?, sa.toNat? with
    | some m, some g, some h, some k, some mb, some mm, some sa =>
      { t with tree := some ({ M := m, G := g, H := h, mergeBelow := mb, mergeMax := mm,
                               splitAbove := sa }, k) }
    | _, _, _, _, _, _, _ => bad "bad TREE"
  -- And option 2's theta (bergdb 024-23): 0 off; the older forms have none.
  | ["TREE", m, g, h, k, mb, mm, sa, th] =>
    match m.toNat?, g.toNat?, h.toNat?, k.toNat?, mb.toNat?, mm.toNat?, sa.toNat?, th.toNat? with
    | some m, some g, some h, some k, some mb, some mm, some sa, some th =>
      { t with tree := some ({ M := m, G := g, H := h, mergeBelow := mb, mergeMax := mm,
                               splitAbove := sa, theta := th }, k) }
    | _, _, _, _, _, _, _, _ => bad "bad TREE"
  | ["TX", i] => match i.toNat? with
    | some i => { t with txs := t.txs.push { idx := i } }
    | none => t
  | ["BASE", b] => match b.toNat? with
    | some b => modTx t (fun x => { x with base := some b })
    | none => bad "bad BASE"
  | "OP" :: "P" :: r => match takeKey r with
    | some (k, [h]) => match h.toNat? with
      | some h => modTx t (fun x => { x with ops := x.ops.push (.put k h, false) })
      | none => bad "bad OP P"
    | _ => bad "bad OP P"
  | "OP" :: "C" :: r => match takeKey r with
    | some (k, [h]) => match h.toNat? with
      | some h => modTx t (fun x => { x with ops := x.ops.push (.put k h, false), copies := x.copies.push k })
      | none => bad "bad OP C"
    | _ => bad "bad OP C"
  | "OP" :: "D" :: r => match takeKey r with
    | some (k, []) => modTx t (fun x => { x with ops := x.ops.push (.del k, false) })
    | _ => bad "bad OP D"
  | "OP" :: "N" :: r => match takeKey r with
    | some (k, []) => modTx t (fun x => { x with ops := x.ops.push (.del k, true) })
    | _ => bad "bad OP N"
  | "ACT" :: "P" :: r => match takeKey r with
    | some (k, [h]) => match h.toNat? with
      | some h => modTx t (fun x => { x with acts := x.acts.push (.put k h) })
      | none => bad "bad ACT P"
    | _ => bad "bad ACT P"
  | "ACT" :: "D" :: r => match takeKey r with
    | some (k, []) => modTx t (fun x => { x with acts := x.acts.push (.del k) })
    | _ => bad "bad ACT D"
  | "KN" :: x :: l :: cnt :: r => match x.toNat?, cnt.toNat?, parseKlongs r with
    | some x, some cnt, some ks =>
      if ks.length != cnt || (l != "0" && l != "1") then bad "bad KN"
      else modTx t (fun tx => { tx with kns := tx.kns.push (x, ⟨l == "1", ks⟩) })
    | _, _, _ => bad "bad KN"
  | "GET" :: tm :: r => match tm.toNat?, takeKey r with
    | some tm, some (k, [v]) =>
      if v != "-" && v.toNat?.isNone then bad "bad GET"
      else modTx t (fun x => { x with gets := x.gets.push (tm, k, v.toNat?) })
    | _, _ => bad "bad GET"
  | "SCAN" :: r => match parseScan r with
    | some sc => modTx t (fun x => { x with scans := x.scans.push sc })
    | none => bad "bad SCAN"
  | "STEP" :: t0 :: c :: r => match t0.toNat?, c.toNat?, takeKeyOpt r with
    | some t0, some c, some (l, r) => match takeKeyOpt r with
      | some (l', [e]) =>
        if e != "0" && e != "1" then bad "bad STEP"
        else modTx t (fun x => { x with steps := x.steps.push ⟨t0, c, l, l', e == "1"⟩ })
      | _ => bad "bad STEP"
    | _, _, _ => bad "bad STEP"
  | ["RESTART", k] =>
    if k != "stop" && k != "crash" then bad "bad RESTART"
    else if t.txs.back?.any (·.restart.isSome) then bad "two RESTART lines in a transaction"
    else modTx t (fun x => { x with restart := some k })
  | ["RESUME", "-"] => modTx t (fun x => { x with resume := some none })
  | "RESUME" :: t0 :: c :: r => match t0.toNat?, c.toNat?, takeKeyOpt r with
    | some t0, some c, some (l, r) => match takeKeyOpt r with
      | some (e, []) => modTx t (fun x => { x with resume := some (some ⟨t0, c, l, e⟩) })
      | _ => bad "bad RESUME"
    | _, _, _ => bad "bad RESUME"
  | _ => t

def parseTree (s : String) : TTrace :=
  ((s.splitOn "\n").zipIdx).foldl (fun t (l, n) => parseTreeLine t (n + 1) l) {}

/-! ## What is compared -/

/-- P as a hash map, for the tree's `exec` and reads. -/
abbrev PMap := Std.HashMap NodeId (Node BVal)

/-- The changes of a transaction of the trace, applied to P. A key node made
without an entry gets the marker entry (024-12, D4; `SIS.Tree.marker`): its
klongs are a time klong alone, which the exporter's entries do not show. -/
def applyRec (p : Params) (P : PMap) (r : TRec) : PMap :=
  let P := r.new.foldl (fun (P : PMap) (x, l, d) =>
    let lone := !d && x != root && l ≤ p.keyMax && !r.adds.any (fun a => a.1 == x)
    P.insert x { level := l, isData := d, hist := if lone then [⟨r.idx, marker⟩] else [] }) P
  r.adds.foldl (fun (P : PMap) (x, tm, v) =>
    match P[x]? with
    | some n => P.insert x { n with hist := n.hist ++ [⟨tm, v⟩] }
    | none => P) P

/-- The entries without the markers, as the exporter writes them. -/
def noMarkers (adds : List (NodeId × BVal)) : List (NodeId × BVal) :=
  adds.filter (fun a => a.2 != marker)

/-- The result of checking one transaction: the failures, by check. -/
structure TxResult where
  change : List String := []
  klongs : List String := []
  noops : List String := []
  reads : List String := []
  touch : List String := []
  inv : List String := []
  bound : List String := []
  form : List String := []
  errors : List String := []
  knCount : Nat := 0
  getCount : Nat := 0
  scanCount : Nat := 0
  touchCount : Nat := 0
  opCount : Nat := 0
  noopCount : Nat := 0
  splitNodes : Nat := 0
  takenBack : Nat := 0
  trail : List String := []
  markedSum : Nat := 0
  /-- The nodes made for each operation that changed the tree, rounded up. -/
  madeMax : Nat := 0
  boundSum : Nat := 0

def showNew (n : NewNode) : String := s!"{n.id}/{n.level}/{if n.isData then "D" else "I"}"

def showAdd (a : NodeId × BVal) : String := s!"{a.1}: {showVal a.2}"

def showKlong : Klong → String
  | .time t => s!"T{t}"
  | .key c y => s!"K{c}:{y}"
  | .del b => s!"B{b}"

def showKs (ks : List Klong) : String := " ".intercalate (ks.map showKlong)

/-- The first difference of two lists, as a text. -/
def firstDiff {α : Type} [BEq α] (sh : α → String) (model java : List α) : String :=
  let rec go (i : Nat) : List α → List α → String
    | [], [] => "none"
    | a :: _, [] => s!"at {i}: the model has {sh a}, Java nothing more"
    | [], b :: _ => s!"at {i}: Java has {sh b}, the model nothing more"
    | a :: r, b :: s => if a == b then go (i + 1) r s else s!"at {i}: the model has {sh a}, Java {sh b}"
  go 0 model java

/-- The keys whose paths a step's touch visits (bergdb 031-06; Maintenance.Plan.touchKeys):
its copies (the `OP C` lines) and reclaim's row. Until 031-06 a step was a record of its own,
and its touch the paths of all its keys, the copies and the row. -/
def stepTouchKeys (x : TTx) : List Key := x.copies.toList ++ [reclaimRowKey]

/-- Checks transaction r (i ≥ 1) of the trace against the model, from P, Java's
structure before it; `after` is P with the trace's changes of r. -/
def checkTx (p : Params) (P after : PMap) (r : TRec) (x : TTx) : TxResult := Id.run do
  let mut res : TxResult := {}
  let i := r.idx
  let ops := x.ops.toList
  let viewA : View BVal := fun y => after[y]?
  -- C-T7: the form of the transaction.
  if !sortedKeys (ops.map (·.1.key)) then
    res := { res with form := res.form ++ [s!"T({i}): the keys of the operations are not strictly increasing"] }
  for (op, _) in ops do
    if !keyWf op.key then
      res := { res with form := res.form ++ [s!"T({i}): a key that Keys.toSegments does not make: {op.key}"] }
  match x.base with
  | none => res := { res with errors := res.errors ++ [s!"T({i}): no BASE line"] }
  | some base =>
    let view : View BVal := fun y => P[y]?
    -- The writer since record format 8: PE (SIS/Tree/Pe.lean; bergdb 026-25).
    match SIS.Tree.Pe.runOps p base (ops.map (·.1)) i view with
    | .error e => res := { res with errors := res.errors ++ [s!"T({i}): the model's error: {e}"] }
    | .ok (flags, w) =>
      -- C-T3: the noops.
      for ((op, noop), flag) in ops.zip flags do
        if noop != flag then
          res := { res with noops := res.noops ++
            [s!"T({i}): {repr op}: Java {if noop then "a noop" else "changed"}, the model {if flag then "a noop" else "changed"}"] }
      res := { res with opCount := ops.length, noopCount := (flags.filter id).length,
                        takenBack := w.taken.length, trail := w.trail,
                        splitNodes := (w.made.filter (fun n => !n.isData && n.level ≤ p.keyMax)).length }
      -- C-T1: the change.
      let c : Changes BVal := SIS.Tree.changesOf i w
      let jnew := r.new.toList.map (fun (y, l, d) => (⟨y, l, d⟩ : NewNode))
      let jadds := r.adds.toList.map (fun (y, _, v) => (y, v))
      if c.new != jnew then
        res := { res with change := res.change ++
          [s!"T({i}): nodes made differ, {firstDiff showNew c.new jnew}"] }
      if noMarkers c.adds != jadds then
        res := { res with change := res.change ++
          [s!"T({i}): entries added differ, {firstDiff showAdd (noMarkers c.adds) jadds}"] }
      -- C-T8: Dag.dirtyNodeBound, on the tree before, bounds the key nodes marked.
      let bound := dirtyNodeBound p view (i - 1) (ops.map (·.1))
      let marked := markedKeyNodes p viewA i c
      res := { res with markedSum := marked, boundSum := bound }
      if marked > bound then
        res := { res with bound := res.bound ++
          [s!"T({i}): {marked} key nodes marked, dirtyNodeBound {bound}"] }
      -- TP26: the bound from the transaction's own sizes as its limits.
      let lim : Limits := { maxOps := ops.length, maxSegs := (ops.map (·.1.key.length)).foldl max 0,
                            maxTxSegs := (ops.map (·.1.key.length)).foldl (· + ·) 0 }
      if bound > lim.dirtyNodes p then
        res := { res with bound := res.bound ++
          [s!"T({i}): DirtyBoundFromLimits: dirtyNodeBound {bound}, the limits allow {lim.dirtyNodes p}"] }
      -- TP20, on the operations that changed the tree.
      let changing := (flags.filter (fun b => !b)).length
      if c.new.length > changing * (4 * p.fuel + 1) + 1 then
        res := { res with bound := res.bound ++
          [s!"T({i}): MadeBound: {c.new.length} nodes made by {changing} operations"] }
      res := { res with madeMax := if changing == 0 then 0 else (c.new.length + changing - 1) / changing }
      -- C-T2: the klongs.
      for (y, jn) in x.kns do
        res := { res with knCount := res.knCount + 1 }
        match w.nodes.lookup y with
        | none => res := { res with klongs := res.klongs ++ [s!"T({i}): KN {y}: the model did not read or change this node"] }
        | some mn =>
          if w.taken.contains y then
            res := { res with klongs := res.klongs ++ [s!"T({i}): KN {y}: the model took this node back"] }
          else if mn.leaf != jn.leaf || mn.ks != jn.ks then
            res := { res with klongs := res.klongs ++
              [s!"T({i}): KN {y}: the model has leaf={mn.leaf} {showKs mn.ks}, Java leaf={jn.leaf} {showKs jn.ks}"] }
  -- C-T2, second part: Java's klongs are those of the node's history (D3, D4).
  for (y, jn) in x.kns do
    match after[y]? with
    | none => res := { res with klongs := res.klongs ++ [s!"T({i}): KN {y}: no such node in P"] }
    | some nd =>
      let ks := klongsOf nd.hist
      if ks != jn.ks || (p.heightOf nd.level == 0) != jn.leaf then
        res := { res with klongs := res.klongs ++
          [s!"T({i}): KN {y}: the history gives {showKs ks}, Java has {showKs jn.ks}"] }
      if entriesOf jn.ks != nd.hist then
        res := { res with klongs := res.klongs ++ [s!"T({i}): KN {y}: Java's klongs do not give the node's history"] }
  -- C-T4: the reads.
  for (t, key, jv) in x.gets do
    res := { res with getCount := res.getCount + 1 }
    let mv := get p viewA t key
    if mv != jv then
      res := { res with reads := res.reads ++ [s!"T({i}): GET at {t} of {key}: the model {mv}, Java {jv}"] }
    -- The search through the skip pointers finds the top node of the time (TP24), at
    -- the record's time and between it and the next record's.
    for mid in (if t < i then [false, true] else [false]) do
      let z := findSuperRootAt viewA t mid
      if z != topAt viewA t then
        res := { res with reads := res.reads ++
          [s!"T({i}): the skip search at {t}{if mid then " and a half" else ""}: {z}, the root's entry {topAt viewA t}"] }
  for sc in x.scans do
    res := { res with scanCount := res.scanCount + 1 }
    let ms := (scan p viewA sc.t sc.req sc.limit).map (fun kv => (kv.key, kv.h))
    if ms != sc.results then
      res := { res with reads := res.reads ++
        [s!"T({i}): SCAN at {sc.t} {repr sc.req} limit {sc.limit}: the model {ms}, Java {sc.results}"] }
  -- C-T5: the touch, on Java's structure before the transaction: a transaction with a
  -- TOUCH line touches the paths of its copies' keys and of reclaim's row (Db.touchPaths,
  -- bergdb 024-07; since bergdb 031-06 a step is in a commit's record beside the action's
  -- operations, whose paths it does not touch: `stepTouchKeys`).
  if !r.touch.isEmpty then
    res := { res with touchCount := res.touchCount + 1 }
    let mt := SIS.Tree.touchOf p (fun y => P[y]?) (i - 1) (stepTouchKeys x)
    if mt != r.touch then
      res := { res with touch := res.touch ++
        [s!"T({i}): the touch of the paths of its copies and the row: the model {mt}, Java {r.touch}"] }
  -- C-T6: the invariants, on Java's structure after the transaction, at its time; and
  -- every pointer of an entry added names a node of P (live or dead: TP4).
  for f in faultsAt p viewA i do
    res := { res with inv := res.inv ++ [s!"T({i}): {f}"] }
  -- With merges, BU1's count (TP31, bergdb 024-22): the key nodes reachable at i are
  -- at most S + (n + S - 1) / (m - 1), for the n keys the tree holds at i (its scan) in
  -- S segment trees.
  if p.merges then
    let kvs := (scan p viewA i {} 1000000000).map (fun kv => (kv.key, kv.h))
    let trees := segTrees kvs
    let bound := trees + (kvs.length + trees - 1) / (p.mergeBelow - 1)
    let nodes := match rootAt viewA i with
      | some r => (nodesAt p viewA i p.fuel r).length
      | none => 0
    if bound < nodes then
      res := { res with inv := res.inv ++
        [s!"T({i}): BU1: {nodes} key nodes reachable, more than {bound}: {kvs.length} keys, {trees} segment trees"] }
  for (y, _, v) in r.adds do
    for z in bptrs v do
      if (after[z]?).isNone then
        res := { res with inv := res.inv ++ [s!"T({i}): PointersOK: node {y} names {z}, no node of P"] }
  return res

end SIS.Check.Tree
