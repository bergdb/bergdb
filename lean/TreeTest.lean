/-
Runs the tree model (SIS/Tree/*.lean) on small cases, without Java (bergdb
024-12, section 4): every sequence of single operations on a few keys up to a
depth (exhaustive), and pseudo-random transactions on more keys. After every
transaction it checks the stated properties that can be computed
(SIS/Tree/Props.lean): the invariants of the tree at the latest time (TP6),
pointers to nodes of P (TP4), every key's get at every time against the
reference map (TP10), scans against it (TP11), a noop delete (TP12), the search
through the skip pointers at every time (TP24), and that
`exec` on P@(i-1) and on P give the same change (TP19, in the exhaustive runs
up to depth 4). An error of the writer other than the level bounds is a failure
(TP8).

Usage: lake exe treetest [exhaustive M depth keys prefix [pairs] | random M seeds steps keys
                           | model M seeds steps keys]
An exhaustive run starts from the primordial structure (prefix 0), or after
every key was put: in one transaction (1), each in its own (2), or both (3), so
that the sequences start in a tree of several levels; with `pairs` a
transaction is one operation or two, on two keys. Without arguments: eleven
exhaustive runs at node sizes 4, 6 and 8, random 8 20 150 14, and two `model`
runs; about 11 minutes on one core. Node sizes
below 8 are not Java's; the rules are the same. Each run prints how often each
rule of the writer ran.

`model` runs the whole model, `SIS.run`, on the tree (`treeSpec`): the records,
D and the startup of SIS/Algorithm.lean and Startup.lean with the tree's `exec`;
it checks the model's assumptions on every transaction and T1 and T2 (see
`modelRun`).
-/
import SIS.Tree.Props
import SIS.Tree.Top
import Check.Steps

open SIS SIS.Check SIS.Tree

/-- A state of a run: P, and the transactions so far. -/
structure St where
  P : Struct BVal
  ts : List Tx
  /-- The rules that the last transaction ran (`W.trail`). -/
  trail : List String := []

/-- What a run found. -/
structure Stats where
  states : Nat := 0
  bounds : Nat := 0
  fails : List String := []
  /-- How often each rule ran, by name. -/
  reached : List (String × Nat) := []

/-- Counts the rules of a transaction. -/
def Stats.reach (s : Stats) (trail : List String) : Stats :=
  { s with reached := trail.foldl (fun r name =>
      if r.any (fun q => q.1 == name) then r.map (fun q => if q.1 == name then (name, q.2 + 1) else q)
      else r ++ [(name, 1)]) s.reached }

def Stats.fail (s : Stats) (msgs : List String) : Stats :=
  if msgs.isEmpty then s else { s with fails := (s.fails ++ msgs).take 20 }

/-- The test keys: the empty key, short keys of one segment, and keys of two
segments below one long first segment. Compare values as `Klong` makes them:
the length in the three bits above the lowest three. -/
def testKeys (n : Nat) : List Key :=
  ([[0], [64 + 8], [2 * 64 + 8], [3 * 64 + 8], [64 + 56, 8], [64 + 56, 64 + 8], [4 * 64 + 8],
    [2 * 64 + 56, 2 * 64 + 8], [5 * 64 + 8], [64 + 56, 2 * 64 + 16], [6 * 64 + 8], [7 * 64 + 8],
    [2 * 64 + 56, 0], [8 * 64 + 8], [9 * 64 + 8], [10 * 64 + 8]] : List Key).take n

/-- One transaction from a state; the base leaves room for 500 nodes. -/
def stepSt (p : Params) (st : St) (ops : List Tree.Op) : Except String St :=
  let i := st.ts.length + 1
  let tx : Tx := { base := 1000 * i, ops := ops }
  match runOps p tx.base tx.ops i (viewOf st.P) with
  | .error e => .error e
  | .ok (_, w) => .ok { P := st.P.apply i (SIS.Tree.changesOf i w), ts := st.ts ++ [tx], trail := w.trail }

/-- The scans to compare at a time: forward and backward from every key and
from none, inclusive and not; forward to every end key, inclusive and not. -/
def testReqs (keys : List Key) : List ScanReq :=
  let starts : List (Option Key) := none :: keys.map some
  (starts.flatMap (fun s => [true, false].flatMap (fun inc => [true, false].map (fun fw =>
    ({ start := s, inclusive := inc, forward := fw } : ScanReq))))) ++
  (keys.flatMap (fun e => [true, false].flatMap (fun einc =>
    [({ endKey := some e, endInclusive := einc } : ScanReq),
     ({ start := keys.head?, inclusive := einc, endKey := some e, endInclusive := einc } : ScanReq)])))

/-- The checks of a state. `full`: gets at every time and all the scans; else
gets at the latest time and three scans. -/
def checkSt (p : Params) (keys : List Key) (st : St) (full : Bool) : List String :=
  let n := st.ts.length
  let v := viewOf st.P
  let inv := faultsAt p v n
  let ptrs :=
    if st.P.all (fun q => q.2.hist.all (fun e => (bptrs e.val).all (fun y => (st.P.get? y).isSome)))
    then [] else ["PointersOK: an entry names a node that is not in P"]
  let times := if full then List.range (n + 1) else [n, n / 2]
  let gets := times.flatMap (fun t => keys.filterMap (fun k =>
    let m := get p v t k
    let r := refGet st.ts t k
    if m == r then none else some s!"GetOK: at {t} of {k}: the model {m}, the reference {r}"))
  let reqs := if full then testReqs keys else (testReqs keys).take 3
  let scans := [n, n / 2].flatMap (fun t => reqs.flatMap (fun req => [100, 2].filterMap (fun limit =>
    let m := (scan p v t req limit).map (fun kv => (kv.key, kv.h))
    let r := refScan st.ts t req limit
    if m == r then none
    else some s!"ScanOK: at {t} {repr req} limit {limit}: the model {m}, the reference {r}")))
  let noops := keys.filterMap (fun k =>
    if (refGet st.ts n k).isSome then none else
      match exec? p { base := 1000 * (n + 1), ops := [.del k] } (n + 1) v with
      | .ok c => if c.new.isEmpty && c.adds.isEmpty then none else some s!"NoopOK: a delete of {k} without a value changes P"
      | .error e => some s!"NoopOK: a delete of {k}: {e}")
  let skips := (List.range (n + 1)).flatMap (fun t => [false, true].filterMap (fun mid =>
    if findSuperRootAt v t mid == topAt v t then none
    else some s!"SkipSearchOK: at {t}{if mid then " and a half" else ""}: {findSuperRootAt v t mid}, the root's entry {topAt v t}"))
  -- TP21 and TP22: the key nodes and the klongs reachable, against the live keys.
  let nodes := keyNodesAt p st.P n
  let allow := 1 + (refKvs st.ts n).length * p.fuel
  let klongs := (nodes.filterMap (keyNodeAt p st.P)).foldl (fun s nd => s + nd.size) 0
  let costs :=
    (if nodes.length ≤ allow then [] else
      [s!"DeletedNoNode: {nodes.length} key nodes reachable, {(refKvs st.ts n).length} live keys"]) ++
    (if klongs ≤ p.M * allow then [] else
      [s!"KlongBound: {klongs} klongs reachable, {(refKvs st.ts n).length} live keys"])
  inv ++ ptrs ++ gets ++ scans ++ noops ++ skips ++ costs

/-- The names of the operations so far, for a failure's text. -/
def showOps (ts : List Tx) : String :=
  " ".intercalate (ts.map (fun tx => "[" ++ " ".intercalate (tx.ops.map (fun op => match op with
    | .put k _ => s!"put{k}"
    | .del k => s!"del{k}")) ++ "]"))

/-- The transactions to try at time i: one operation, a put or a delete of one
of the keys; with `pairs` also two operations, on two keys in key order, each a
put or a delete (a split and a delete in one transaction: the take-back). -/
def choicesAt (keys : List Key) (pairs : Bool) (i : Nat) : List (List Tree.Op) :=
  let sorted := (keys.mergeSort (fun a b => !keyLt b a)).zipIdx
  let one (q : Key × Nat) : List Tree.Op := [Tree.Op.put q.1 (1000 * i + q.2), Tree.Op.del q.1]
  let singles := sorted.flatMap (fun q => (one q).map (fun op => [op]))
  if !pairs then singles else
    singles ++ sorted.flatMap (fun a => (sorted.filter (fun b => a.2 < b.2)).flatMap (fun b =>
      (one a).flatMap (fun x => (one b).map (fun y => [x, y]))))

/-- Every sequence of `depth` transactions from `choicesAt`, from state st; each
state checked. A delete of a key without a value is run too: it must be a noop,
which `checkSt` and the state's equality with the one before show. -/
def exhaust (p : Params) (keys : List Key) (pairs : Bool) : Nat → St → Stats → Stats
  | 0, _, acc => acc
  | d + 1, st, acc =>
    let i := st.ts.length + 1
    (choicesAt keys pairs i).foldl (fun acc ops =>
      -- A transaction holds no noop (Java's record leaves them out).
      let ops := ops.filter (fun op => match op with
        | .del k => (refGet st.ts (i - 1) k).isSome
        | .put _ _ => true)
      match stepSt p st ops with
      | .error e =>
        if e.startsWith "bounds:" then { acc with bounds := acc.bounds + 1 }
        else acc.fail [s!"{showOps st.ts} then {repr ops}: {e}"]
      | .ok st' =>
        let msgs := checkSt p keys st' true
        -- TP19: exec on P@(i-1), the model's view, gives the same change.
        let same := if i ≤ 4 then
            (match exec? p { base := 1000 * i, ops := ops } i (view (treeSpec p) st.P (i - 1)) with
            | .ok c => (viewOf (st.P.apply i c)) 0 == (viewOf st'.P) 0 &&
                (st.P.apply i c).length == st'.P.length &&
                (st.P.apply i c).all (fun q => st'.P.get? q.1 == some q.2)
            | .error _ => false)
          else true
        let acc := { acc with states := acc.states + 1 }
        let acc := acc.reach st'.trail
        let acc := acc.fail (msgs.map (fun m => s!"{showOps st'.ts}: {m}"))
        let acc := if same then acc else acc.fail [s!"{showOps st'.ts}: ExecReadsReachable: exec on P@(i-1) differs"]
        exhaust p keys pairs d st' acc) acc

/-- A pseudo-random number generator (a linear congruential one). -/
def nextRand (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Pseudo-random transactions of up to `maxOps` operations, normalized as
`Db.sortByKey` does; each state checked, in full every tenth. -/
def randomRun (p : Params) (keys : List Key) (maxOps delPct : Nat) : Nat → Nat → St → Stats → Stats
  | 0, _, _, acc => acc
  | n + 1, seed, st, acc =>
    let i := st.ts.length + 1
    let s1 := nextRand seed
    let count := 1 + (s1 / 65536) % maxOps
    let (ops, s2) := (List.range count).foldl (fun (q : List Tree.Op × Nat) j =>
      let a := nextRand q.2
      let b := nextRand a
      let k := keys.getD ((a / 65536) % keys.length) [0]
      (q.1 ++ [if (b / 65536) % 100 < delPct then Tree.Op.del k else Tree.Op.put k (1000 * i + j)], b)) ([], s1)
    let raw := ops
    let ops := normalize ops
    if !sortedKeys (ops.map (·.key)) || !keys.all (fun k => ops.find? (fun op => op.key == k) == ruleFor raw k) then
      acc.fail [s!"NormalizeOK: {repr raw} gives {repr ops}"] else
      -- The noops are not part of a transaction: left out, as Java's record leaves them.
      let ops := ops.filter (fun op => match op with
        | .del k => (refGet st.ts (i - 1) k).isSome
        | .put _ _ => true)
      match stepSt p st ops with
      | .error e =>
        if e.startsWith "bounds:" then { acc with bounds := acc.bounds + 1 }
        else acc.fail [s!"seed state {i}: {repr ops}: {e}"]
      | .ok st' =>
        let msgs := checkSt p keys st' (i % 10 == 0)
        let acc := { acc with states := acc.states + 1 }
        let acc := acc.reach st'.trail
        randomRun p keys maxOps delPct n s2 st' (acc.fail (msgs.map (fun m => s!"T({i}) {repr ops}: {m}")))

/-! ## The whole model on the tree: `SIS.run (treeSpec p)` -/

/-- The tree as a `Spec` whose transactions are indexes into `txs` (the
checker's functions and the model's records take transactions that can be
compared): `treeSpec`, with transaction j the j-th of `txs`. -/
def treeSpecNat (p : Params) (txs : Array Tx) : Spec BVal Nat where
  ptrs := bptrs
  live := blive
  exec := fun j i v => SIS.Tree.exec p (txs.getD j { base := 0, ops := [] }) i v
  init := initStruct p
  virt := true
  topLevel := p.topLevel 0
  rootVal := .top

/-- Pseudo-random transactions, made before the run: transaction j (time j + 1)
has the base 1000 (j + 1) and up to `maxOps` operations, normalized. A delete of
a key without a value may be among them: a noop. -/
def genTxs (keys : List Key) (maxOps delPct seed n : Nat) : Array Tx :=
  ((List.range n).foldl (fun (acc : Array Tx × Nat) j =>
    let s1 := nextRand acc.2
    let count := 1 + (s1 / 65536) % maxOps
    let r := (List.range count).foldl (fun (q : List Tree.Op × Nat) k =>
      let a := nextRand q.2
      let b := nextRand a
      let key := keys.getD ((a / 65536) % keys.length) [0]
      (q.1 ++ [if (b / 65536) % 100 < delPct then Tree.Op.del key
               else Tree.Op.put key (1000 * (j + 1) + k)], b)) ([], s1)
    (acc.1.push { base := 1000 * (j + 1), ops := normalize r.1 }, r.2)) (#[], seed)).1

/-- P ≈ P' up to time k, by comparing the views of every node at every time. -/
def equivB (sp : Spec BVal Nat) (k : Time) (P P' : Struct BVal) : Bool :=
  let ids := (P.map (·.1) ++ P'.map (·.1)).eraseDups
  (List.range (k + 1)).all (fun t => ids.all (fun x => view sp P t x == view sp P' t x))

/-- One run of the whole model on the tree: n pseudo-random transactions. Checks
the model's assumptions on every transaction, with the trace checker's
functions (Check/Steps.lean: `SpecOK` and `VirtInit` of the primordial
structure; `StepOK` with `VirtStep`, A2 to A5; TREE and A6' after it; A-COPY:
TP13, TP14, TP16), that the model's `run` has the tree's P (TP19), and, with
BergDB's algorithm (marking, Java's still-dirty test, a startup pos two records
back), T1 (startup from the stream gives P and D, here and every tenth
transaction) and T2 (the run with restarts appends the same records). -/
def modelRun (p : Params) (keys : List Key) (seed n : Nat) : List String :=
  let txs := genTxs keys (1 + seed % 5) (20 + 10 * (seed % 5)) (seed * 7919) n
  let sp := treeSpecNat p txs
  let al : Algo BVal Nat := { policy := fun _ _ i _ => i - 2, stillDirty := javaTest sp, mark := true }
  let ts := List.range n
  let initF := (SIS.Check.initFailures sp).map (fun f => s!"R(0): {f}")
  let r := ts.foldl (fun (acc : Struct BVal × List String) j =>
    let P := acc.1
    let i := j + 1
    let c := sp.exec j i (view sp P (i - 1))
    let P' := P.apply i c
    let rlPrev := reachList sp P (i - 1)
    let rlNow := reachList sp P' i
    let prevSet : Std.HashSet NodeId := Std.HashSet.ofList rlPrev
    let nowSet : Std.HashSet NodeId := Std.HashSet.ofList rlNow
    let sf := (SIS.Check.stepFailures sp P i c prevSet nowSet rlNow).map (fun f => s!"T({i}): {f.1} {f.2}")
    let tf := SIS.Check.treeFailures sp P' i rlNow
    let af := (SIS.Check.adoptFailures sp P' i nowSet rlNow).1
    let cf := SIS.Check.copyFailures sp P i c rlPrev nowSet
    (P', acc.2 ++ sf ++
      (if tf.isEmpty then [] else [s!"T({i}): TREE {tf}"]) ++
      (if af.isEmpty then [] else [s!"T({i}): A6' {af}"]) ++
      (if cf.isEmpty then [] else [s!"T({i}): A-COPY {cf}"]))) (sp.init, [])
  let sts := ts.scanl (step sp al) (init sp)
  let last := sts.getLastD (init sp)
  let sameP := if last.P == r.1 then [] else ["RunPSame: the model's run has another P than the tree's"]
  let t1 := sts.zipIdx.filterMap (fun (db, k) =>
    if k % 10 != 0 && k != n then none else
      let db' := startup sp db.S
      if equivB sp (db.S.length - 1) db'.P db.P && db'.D == db.D then none
      else some s!"T1 after T({k}): startup from the stream gives another P or D")
  let flags := ts.map (fun j => (j, (seed + j) % 3 == 0))
  let t2 := if (runRestarts sp al flags).S == last.S then []
    else ["T2: the run with restarts has another stream"]
  initF ++ r.2 ++ sameP ++ t1 ++ t2

def runModel (m seeds steps nkeys : Nat) : IO Bool := do
  let p : Params := { M := m, G := 1, H := 8 }
  let mut fails : List String := []
  for seed in [1:seeds + 1] do
    fails := (fails ++ (modelRun p (testKeys nkeys) seed steps).map (fun f => s!"seed {seed}: {f}")).take 20
  IO.println s!"model M={m} seeds={seeds} steps={steps} keys={nkeys}: C-A on every transaction, T1, T2: {fails.length} failures"
  for f in fails.take 6 do
    IO.println s!"  {f}"
  pure fails.isEmpty

def report (name : String) (s : Stats) : IO Bool := do
  IO.println s!"{name}: {s.states} states, {s.bounds} beyond the level bounds, {s.fails.length} failures"
  let names := s.reached.mergeSort (fun a b => decide (a.1 ≤ b.1))
  IO.println ("  reached: " ++ ", ".intercalate (names.map (fun (n, k) => s!"{n} {k}")))
  for f in s.fails.take 6 do
    IO.println s!"  {f}"
  pure s.fails.isEmpty

/-- A state to start the exhaustive runs from: `pre` 0, the primordial structure;
1, every key put in one transaction; 2, every key put in a transaction of its
own, in key order; 3, as 2 and then every key put again in one transaction. -/
def prefixSt (p : Params) (keys : List Key) (pre : Nat) : Except String St :=
  let st0 : St := { P := initStruct p, ts := [] }
  let sorted := keys.mergeSort (fun a b => !keyLt b a)
  let all (i : Nat) : List Tree.Op := sorted.zipIdx.map (fun (k, j) => Tree.Op.put k (1000 * i + j))
  match pre with
  | 0 => .ok st0
  | 1 => stepSt p st0 (all 1)
  | _ =>
    let r := sorted.zipIdx.foldl (fun (acc : Except String St) (k, j) =>
      acc.bind (fun st => stepSt p st [Tree.Op.put k (1000 * (st.ts.length + 1) + j)])) (.ok st0)
    if pre == 2 then r else r.bind (fun st => stepSt p st (all (st.ts.length + 1)))

def runExhaustive (m depth nkeys pre : Nat) (pairs : Bool := false) : IO Bool := do
  let p : Params := { M := m, G := 1, H := 8 }
  let keys := testKeys nkeys
  match prefixSt p keys pre with
  | .error e =>
    IO.println s!"exhaustive M={m} depth={depth} keys={nkeys} prefix={pre}: the prefix fails: {e}"
    pure false
  | .ok st =>
    let first := checkSt p keys st true
    let s := (exhaust p keys pairs depth st {}).fail (first.map (fun msg => s!"after the prefix: {msg}"))
    report s!"exhaustive M={m} depth={depth} keys={nkeys} prefix={pre}{if pairs then " pairs" else ""}" s

def runRandom (m seeds steps nkeys : Nat) : IO Bool := do
  let p : Params := { M := m, G := 1, H := 8 }
  let mut ok := true
  let mut total : Stats := {}
  for seed in [1:seeds + 1] do
    let st : St := { P := initStruct p, ts := [] }
    let s := randomRun p (testKeys nkeys) (1 + seed % 6) (20 + 10 * (seed % 5)) steps (seed * 7919) st {}
    total := { states := total.states + s.states, bounds := total.bounds + s.bounds,
               fails := (total.fails ++ s.fails).take 20,
               reached := s.reached.foldl (fun r (q : String × Nat) =>
                 if r.any (fun z => z.1 == q.1) then r.map (fun z => if z.1 == q.1 then (z.1, z.2 + q.2) else z)
                 else r ++ [q]) total.reached }
    if !s.fails.isEmpty then ok := false
  let _ ← report s!"random M={m} seeds={seeds} steps={steps} keys={nkeys}" total
  pure ok

def main (args : List String) : IO UInt32 := do
  let nat := fun (i : Nat) (d : Nat) => (args[i]?.bind String.toNat?).getD d
  let ok ← match args.head? with
    | some "exhaustive" => runExhaustive (nat 1 4) (nat 2 5) (nat 3 4) (nat 4 0) (args[5]? == some "pairs")
    | some "random" => runRandom (nat 1 8) (nat 2 20) (nat 3 150) (nat 4 14)
    | some "model" => runModel (nat 1 8) (nat 2 10) (nat 3 40) (nat 4 10)
    | _ => do
      let a ← runExhaustive 4 5 4 0
      let b ← runExhaustive 6 5 4 0
      let c ← runExhaustive 8 4 5 0
      let e ← runExhaustive 4 4 6 1
      let f ← runExhaustive 4 4 6 2
      let g ← runExhaustive 6 4 7 2
      let h ← runExhaustive 6 3 9 3
      let k ← runExhaustive 8 3 12 3
      let l ← runExhaustive 4 3 5 2 true
      let m ← runExhaustive 6 2 8 3 true
      let q ← runExhaustive 4 2 6 2 true
      let d ← runRandom 8 20 150 14
      let n ← runModel 4 6 30 8
      let o ← runModel 8 6 40 12
      pure (a && b && c && d && e && f && g && h && k && l && m && n && o && q)
  if ok then
    IO.println "TREETEST OK"
    return 0
  else
    IO.println "TREETEST FAILED"
    return 1
