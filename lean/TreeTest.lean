/-
Runs the tree model (SIS/Tree/*.lean) on small cases, without Java (bergdb
024-12, section 4): every sequence of single operations on a few keys up to a
depth (exhaustive), and pseudo-random transactions on more keys. After every
transaction it checks the stated properties that can be computed
(SIS/Tree/Props.lean): the invariants of the tree at the latest time (TP6),
pointers to nodes of P (TP4), every key's get at every time against the
reference map (TP10), scans against it (TP11), a noop delete (TP12), the search
through the skip pointers at every time (TP24), A6 (since bergdb 024-22), and that
`exec` on P@(i-1) and on P give the same change (TP19, in the exhaustive runs
up to depth 4). An error of the writer other than the level bounds is a failure
(TP8).

Usage: lake exe treetest [exhaustive M depth keys prefix [pairs] | random M seeds steps keys
                           | model M seeds steps keys | subsets ... | merges]
An exhaustive run starts from the primordial structure (prefix 0), or after
every key was put: in one transaction (1), each in its own (2), or both (3), so
that the sequences start in a tree of several levels; with `pairs` a
transaction is one operation or two, on two keys. Without arguments: eleven
exhaustive runs at node sizes 4, 6 and 8, random 8 20 150 14, and two `model`
runs, about 11 minutes on one core; then the set with merges. Node sizes
below 8 are not Java's; the rules are the same. Each run prints how often each
rule of the writer ran.

`model` runs the whole model, `SIS.run`, on the tree (`treeSpec`): the records,
D and the startup of SIS/Algorithm.lean and Startup.lean with the tree's `exec`;
it checks the model's assumptions on every transaction and T1 and T2 (see
`modelRun`).

Merges at the delete (bergdb 024-22): the word `merge` among the arguments runs
with 024-11's thresholds (`Params.withMerges`; below node size 8, forced, to
show what TP28 excludes). Then each state is checked also for V1 (in the walk),
BU1's count (TP31), CB1 and CB3 (TP32, TP33), TP23 with the count of record
format 7 and TP26; `model` checks A6 too. More forms:
  subsets M keys prefix depth [puts] [merge]: every transaction that deletes
    (with `puts`: or puts) any set of the keys, from the prefix (4: every key
    put in its own transaction, twice), then `depth` single operations;
  random M seeds steps keys [merge] [maxOps] [delete percent];
  merges: the default set with merges (`runMergeSet`), about 15 minutes.
Option 2 of dead klongs (bergdb 024-23): the word `theta` runs with
`Params.withTheta` (below node size 8, forced to 1); then each state is checked
also for TP39 (at most theta dead klongs a node, in the walk), and TP23 with
the count of 024-23, 2.6. `thetas`: the set with option 2 and the merges
(`runThetaSet`), also part of the default set.
Key sets: up to 16 keys `testKeys`, to 100 `manyKeys`, to 200 `segKeys` of n -
100 keys (three 7-byte prefixes), above `oneSegKeys` of n - 200 (one prefix).
-/
import SIS.Tree.Bound
import SIS.Tree.Top
import Check.Steps

open SIS SIS.Check SIS.Tree

/-- A state of a run: P, and the transactions so far. -/
structure St where
  P : Struct BVal
  ts : List Tx
  /-- The rules that the last transaction ran (`W.trail`). -/
  trail : List String := []
  /-- Since the primordial structure: the merges, the deletes that deleted, the
  space splits (for CB3 of bergdb 024-11). -/
  merges : Nat := 0
  deletes : Nat := 0
  spaceSplits : Nat := 0
  /-- The merges of each operation of the last transaction (CB1). -/
  opMerges : List Nat := []
  /-- TP23 on the last transaction: the key nodes it marked, and
  `dirtyNodeBound` on the tree before it. -/
  marked : Nat := 0
  bound : Nat := 0
  /-- TP26: the transaction's own limits (its operations, its longest key, its
  keys' segments) allow
  `dirtyNodeBound`. -/
  limitsOk : Bool := true

/-- What a run found. -/
structure Stats where
  states : Nat := 0
  bounds : Nat := 0
  fails : List String := []
  /-- How often each rule ran, by name. -/
  reached : List (String × Nat) := []
  /-- Transactions where `dirtyNodeBound` (2026.4's count) is below the key
  nodes marked (TP23), and the first of them; reported, not failures, as the
  count is Java's to change for merges (bergdb 024-22). -/
  tp23 : Nat := 0
  tp23ex : List String := []
  /-- The most merges of one operation, and of one transaction. -/
  maxOpMerges : Nat := 0
  maxTxMerges : Nat := 0

/-- Counts the rules of a transaction. -/
def Stats.reach (s : Stats) (trail : List String) : Stats :=
  { s with reached := trail.foldl (fun r name =>
      if r.any (fun q => q.1 == name) then r.map (fun q => if q.1 == name then (name, q.2 + 1) else q)
      else r ++ [(name, 1)]) s.reached }

def Stats.fail (s : Stats) (msgs : List String) : Stats :=
  if msgs.isEmpty then s else { s with fails := (s.fails ++ msgs).take 20 }

/-- Notes TP23 and the most merges of a state's last transaction; `what` names
the transactions for the first examples. -/
def Stats.note (s : Stats) (marked bound : Nat) (opMerges : List Nat) (what : String) : Stats :=
  let s := { s with maxOpMerges := opMerges.foldl max s.maxOpMerges,
                    maxTxMerges := max s.maxTxMerges (opMerges.foldl (· + ·) 0) }
  if marked ≤ bound then s else
    { s with tp23 := s.tp23 + 1,
             tp23ex := (s.tp23ex ++ [s!"{what}: {marked} key nodes marked, dirtyNodeBound {bound}"]).take 5 }

/-- The test keys: the empty key, short keys of one segment, and keys of two
segments below one long first segment. Compare values as `Klong` makes them:
the length in the three bits above the lowest three. -/
def testKeys (n : Nat) : List Key :=
  ([[0], [64 + 8], [2 * 64 + 8], [3 * 64 + 8], [64 + 56, 8], [64 + 56, 64 + 8], [4 * 64 + 8],
    [2 * 64 + 56, 2 * 64 + 8], [5 * 64 + 8], [64 + 56, 2 * 64 + 16], [6 * 64 + 8], [7 * 64 + 8],
    [2 * 64 + 56, 0], [8 * 64 + 8], [9 * 64 + 8], [10 * 64 + 8]] : List Key).take n

/-- The number of merges in a trail. -/
def mergesIn (trail : List String) : Nat :=
  trail.countP (fun s => s == "merge.one" || s == "merge.two")

/-- `putKv`, and the number of its merges. -/
def putCounted (op : Tree.Op) : M Nat := do
  let w0 : W ← get
  let _ ← putKv op
  let w1 : W ← get
  pure (w1.merges - w0.merges)

/-- `runOps`, with the merges of each operation counted (CB1). -/
def runCounted (p : Params) (base : NodeId) (ops : List Tree.Op) (i : Time) (view : View BVal) :
    Except String (List Nat × W) :=
  match lastTop view with
  | none => .error "corrupt: the root has no top node"
  | some z =>
    match topOf p (rootless view) z with
    | .error e => .error e
    | .ok top =>
      match ((ops.mapM putCounted).run { p := p, i := i, view := rootless view }).run
          { next := base, top := top } with
      | .error e => .error e
      | .ok (per, w) => (boundsOK p (.ok ([], w))).map (fun r => (per, r.2))

/-- One transaction from a state; the base leaves room for 500 nodes. -/
def stepSt (p : Params) (st : St) (ops : List Tree.Op) : Except String St :=
  let i := st.ts.length + 1
  let tx : Tx := { base := 1000 * i, ops := ops }
  match runCounted p tx.base tx.ops i (viewOf st.P) with
  | .error e => .error e
  | .ok (per, w) =>
    let c := SIS.Tree.changesOf i w
    let P' := st.P.apply i c
    let dels := ops.countP (fun op => match op with
      | .del _ => true
      | .put _ _ => false)
    .ok { P := P', ts := st.ts ++ [tx], trail := w.trail,
          merges := st.merges + w.merges, deletes := st.deletes + dels,
          spaceSplits := st.spaceSplits + w.spaceSplits, opMerges := per,
          marked := markedKeyNodes p (viewOf P') i c,
          bound := dirtyNodeBound p (viewOf st.P) (i - 1) ops,
          limitsOk := dirtyNodeBound p (viewOf st.P) (i - 1) ops ≤
            ({ maxOps := ops.length, maxSegs := (ops.map (·.key.length)).foldl max 0,
               maxTxSegs := (ops.map (·.key.length)).foldl (· + ·) 0 } : Limits).dirtyNodes p }

/-- The scans to compare at a time: forward and backward from every key and
from none, inclusive and not; forward to every end key, inclusive and not. -/
def testReqs (keys : List Key) : List ScanReq :=
  let starts : List (Option Key) := none :: keys.map some
  (starts.flatMap (fun s => [true, false].flatMap (fun inc => [true, false].map (fun fw =>
    ({ start := s, inclusive := inc, forward := fw } : ScanReq))))) ++
  (keys.flatMap (fun e => [true, false].flatMap (fun einc =>
    [({ endKey := some e, endInclusive := einc } : ScanReq),
     ({ start := keys.head?, inclusive := einc, endKey := some e, endInclusive := einc } : ScanReq)])))

/-- The tree as a `Spec` for the checks of pointers alone (A6), whose `exec` is
not used. -/
def ptrSpec (p : Params) : Spec BVal Nat where
  ptrs := bptrs
  live := blive
  exec := fun _ i v => SIS.Tree.exec p { base := 0, ops := [] } i v
  init := initStruct p
  virt := true
  topLevel := p.topLevel 0
  rootVal := .top

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
  -- With merges (bergdb 024-22): BU1's count (TH3 of 024-11), CB1 and CB3.
  let merges : List String := if !p.merges then [] else
    let live := refKvs st.ts n
    let trees := 1 + ((live.flatMap (fun q => (List.range (q.1.length - 1)).map
      (fun j => q.1.take (j + 1)))).eraseDups).length
    let bu1 := trees + (live.length + trees - 1) / (p.mergeBelow - 1)
    let maxH := [n - 1, n].foldl (fun acc t => (keyNodesAt p st.P t).foldl (fun acc x =>
      match st.P.get? x with
      | some nd => max acc (p.heightOf nd.level)
      | none => acc) acc) 0
    (if nodes.length ≤ bu1 then [] else
      [s!"BU1: {nodes.length} key nodes reachable, more than {bu1}: {live.length} live keys, {trees} segment trees"]) ++
    (if st.merges ≤ st.deletes + 2 * st.spaceSplits then [] else
      [s!"CB3: {st.merges} merges, more than {st.deletes} deletes and twice {st.spaceSplits} space splits"]) ++
    -- A delete's own rule O can raise its tree by one (a split up to a new root)
    -- before its merges, which RC then lowers again (024-22, MF1).
    (if st.opMerges.all (· ≤ maxH + 1) then [] else
      [s!"CB1: an operation made {st.opMerges} merges, the trees' height is at most {maxH}"])
  -- TP23 with the count of record format 7 (Java's since 024-21, restated in
  -- Bound.lean), and TP26 with its limits: failures. (2026.4's count: noted only.)
  let bounds : List String := if !p.format7 then [] else
    (if st.marked ≤ st.bound then [] else
      [s!"DirtyBoundOK: {st.marked} key nodes marked, dirtyNodeBound {st.bound}"]) ++
    (if st.limitsOk then [] else [s!"DirtyBoundFromLimits: dirtyNodeBound {st.bound}"])
  -- A6 (bergdb 024-12, 6.2: the gates will require it; 024-22, section 4, B): no
  -- pointer of a reachable node, live or dead, to a reachable node that is not
  -- its live child (A6' is the part where the node is not below it).
  let sp := ptrSpec p
  let rl := reachList sp st.P n
  let ad := SIS.Check.adoptFailures sp st.P n (Std.HashSet.ofList rl) rl
  let a6 := (if ad.1.isEmpty then [] else [s!"A6': {ad.1}"]) ++
    (if ad.2.isEmpty then [] else [s!"A6: {ad.2}"])
  inv ++ ptrs ++ gets ++ scans ++ noops ++ skips ++ costs ++ merges ++ bounds ++ a6

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
        let acc := acc.note st'.marked st'.bound st'.opMerges (showOps st'.ts)
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
        let acc := acc.note st'.marked st'.bound st'.opMerges s!"seed state {i}: {repr ops}"
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
    let ad := SIS.Check.adoptFailures sp P' i nowSet rlNow
    let af := ad.1
    let cf := SIS.Check.copyFailures sp P i c rlPrev nowSet
    (P', acc.2 ++ sf ++
      (if tf.isEmpty then [] else [s!"T({i}): TREE {tf}"]) ++
      (if af.isEmpty then [] else [s!"T({i}): A6' {af}"]) ++
      -- With merges, A6 itself (bergdb 024-12, section 6.2: the gates will
      -- require it): no pointer to a reachable node below that is not a live child.
      (if !p.merges || ad.2.isEmpty then [] else [s!"T({i}): A6 {ad.2}"]) ++
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

/-- Option 2 (bergdb 024-23) on p with `theta`: `Params.withTheta`; below node
size 8, where record format 7 has none, forced to 1, so that the small sizes
run the rule too. -/
def addTheta (p : Params) (theta : Bool) : Params :=
  if !theta then p else if p.M < 8 then { p with theta := 1 } else p.withTheta

def runModel (m seeds steps nkeys : Nat) (merges : Bool := false) (theta : Bool := false) :
    IO Bool := do
  let p0 : Params := { M := m, G := 1, H := 8 }
  let p := addTheta (if merges then p0.withMerges else p0) theta
  let keys := if nkeys ≤ 16 then testKeys nkeys else
    ([0] :: (List.range (nkeys - 1)).map (fun j =>
      if j % 4 == 3 then [64 + 56, (j / 4) * 64 + 8] else [(j + 2) * 64 + 8]))
  let mut fails : List String := []
  for seed in [1:seeds + 1] do
    fails := (fails ++ (modelRun p keys seed steps).map (fun f => s!"seed {seed}: {f}")).take 20
  IO.println s!"model M={m} seeds={seeds} steps={steps} keys={nkeys}{if merges then " merges" else ""}{if theta then s!" theta={p.theta}" else ""}: C-A on every transaction{if merges then " (A6 too)" else ""}, T1, T2: {fails.length} failures"
  for f in fails.take 6 do
    IO.println s!"  {f}"
  pure fails.isEmpty

def report (name : String) (s : Stats) : IO Bool := do
  IO.println s!"{name}: {s.states} states, {s.bounds} beyond the level bounds, {s.fails.length} failures"
  if s.maxTxMerges > 0 || s.tp23 > 0 then
    IO.println s!"  merges: at most {s.maxOpMerges} in one operation, {s.maxTxMerges} in one transaction; TP23 (dirtyNodeBound) exceeded in {s.tp23} transactions"
    for e in s.tp23ex.take 3 do
      IO.println s!"    {e}"
  let names := s.reached.mergeSort (fun a b => decide (a.1 ≤ b.1))
  IO.println ("  reached: " ++ ", ".intercalate (names.map (fun (n, k) => s!"{n} {k}")))
  for f in s.fails.take 6 do
    IO.println s!"  {f}"
  (← IO.getStdout).flush
  pure s.fails.isEmpty

/-- The parameters of a run: node size m, G = 1, H = 8; with merges, 024-11's
thresholds (`Params.withMerges`). Below node size 8, where `withMerges` (as
Java) merges nothing, `merge` forces 024-11's formulas, m = 2 and c = M / 2:
to show what TP28 excludes (024-22, section 3.3). -/
def mkParams (m : Nat) (merges : Bool) (theta : Bool := false) : Params :=
  let p : Params := { M := m, G := 1, H := 8 }
  addTheta (if !merges then p
    else if m < 8 then { p with mergeBelow := 2, mergeMax := m / 2 }
    else p.withMerges) theta

/-- More keys than `testKeys` has: the empty key, and keys of one segment, every
fourth of two segments below one long first segment. -/
def manyKeys (n : Nat) : List Key :=
  ([0] :: (List.range (n - 1)).map (fun j =>
    if j % 4 == 3 then [64 + 56, (j / 4) * 64 + 8] else [(j + 2) * 64 + 8])).take n

/-- Keys of two segments below three long first segments, and the empty key:
segment trees that empty and fill again, and a new segment root made and split
in one transaction (fault 12's case, 024-22, section 4). -/
def segKeys (n : Nat) : List Key :=
  ([0] :: (List.range (n - 1)).map (fun j => [(j % 3 + 1) * 64 + 56, (j / 3) * 64 + 8])).take n

/-- The empty key and keys of two segments below one long first segment: a
transaction of their puts makes a segment root and splits it (fault 12's case,
`split.space2.inplace`). -/
def oneSegKeys (n : Nat) : List Key :=
  ([0] :: (List.range (n - 1)).map (fun j => [64 + 56, j * 64 + 8])).take n

/-- The key set of a run: up to 16, `testKeys`; 17 to 100, `manyKeys`; 101 to
200, `segKeys` of n - 100 keys; above 200, `oneSegKeys` of n - 200. -/
def keysFor (n : Nat) : List Key :=
  if n ≤ 16 then testKeys n else if n ≤ 100 then manyKeys n
  else if n ≤ 200 then segKeys (n - 100) else oneSegKeys (n - 200)

def mergeName (merges : Bool) (theta : Bool := false) (p : Params := default) : String :=
  (if merges then " merges" else "") ++ (if theta then s!" theta={p.theta}" else "")

/-- A state to start the exhaustive runs from: `pre` 0, the primordial structure;
1, every key put in one transaction; 2, every key put in a transaction of its
own, in key order; 3, as 2 and then every key put again in one transaction; 4,
as 2 twice (overwrites: nodes full of dead klongs, so that a delete's rule O
makes a time split before a merge). -/
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
    if pre == 2 then r
    else if pre == 4 then
      sorted.zipIdx.foldl (fun (acc : Except String St) (k, j) =>
        acc.bind (fun st => stepSt p st [Tree.Op.put k (1000 * (st.ts.length + 1) + j)])) r
    else r.bind (fun st => stepSt p st (all (st.ts.length + 1)))

def runExhaustive (m depth nkeys pre : Nat) (pairs : Bool := false) (merges : Bool := false)
    (theta : Bool := false) : IO Bool := do
  let p := mkParams m merges theta
  let keys := keysFor nkeys
  let name := s!"exhaustive M={m} depth={depth} keys={nkeys} prefix={pre}{if pairs then " pairs" else ""}{mergeName merges theta p}"
  match prefixSt p keys pre with
  | .error e =>
    IO.println s!"{name}: the prefix fails: {e}"
    pure false
  | .ok st =>
    let first := checkSt p keys st true
    let s := (exhaust p keys pairs depth st {}).fail (first.map (fun msg => s!"after the prefix: {msg}"))
    report name s

/-- Every transaction that does, for each key, nothing, a delete (`dels`: of a
key that has a value), or with `puts` also a put: one transaction from the
prefix, its operations in key order; then every sequence of `depth` single
operations after it. With merges this reaches nodes made and merged in one
transaction (the take-back of 024-11, M5). -/
def runSubsets (m nkeys pre depth : Nat) (puts merges : Bool) (theta : Bool := false) :
    IO Bool := do
  let p := mkParams m merges theta
  let keys := keysFor nkeys
  let name := s!"subsets M={m} keys={nkeys} prefix={pre} depth={depth}{if puts then " puts" else ""}{mergeName merges theta p}"
  match prefixSt p keys pre with
  | .error e =>
    IO.println s!"{name}: the prefix fails: {e}"
    pure false
  | .ok st =>
    let i := st.ts.length + 1
    let sorted := (keys.mergeSort (fun a b => !keyLt b a)).zipIdx
    let choices : List (List Tree.Op) := sorted.foldr (fun (q : Key × Nat) acc =>
      let mine : List (List Tree.Op) := [[]] ++
        (if (refGet st.ts (i - 1) q.1).isSome then [[Tree.Op.del q.1]] else []) ++
        (if puts then [[Tree.Op.put q.1 (1000 * i + q.2)]] else [])
      mine.flatMap (fun a => acc.map (fun b => a ++ b))) [[]]
    let s := (choices.filter (!·.isEmpty)).foldl (fun acc ops =>
      match stepSt p st ops with
      | .error e =>
        if e.startsWith "bounds:" then { acc with bounds := acc.bounds + 1 }
        else acc.fail [s!"{showOps st.ts} then {repr ops}: {e}"]
      | .ok st' =>
        let msgs := checkSt p keys st' true
        let acc := { acc with states := acc.states + 1 }
        let acc := acc.reach st'.trail
        let acc := acc.note st'.marked st'.bound st'.opMerges (showOps st'.ts)
        let acc := acc.fail (msgs.map (fun msg => s!"{showOps st'.ts}: {msg}"))
        exhaust p keys false depth st' acc) {}
    report name s

def runRandom (m seeds steps nkeys : Nat) (merges : Bool := false) (maxOps : Nat := 6)
    (delPct : Nat := 0) (theta : Bool := false) : IO Bool := do
  let p := mkParams m merges theta
  let mut ok := true
  let mut total : Stats := {}
  for seed in [1:seeds + 1] do
    let st : St := { P := initStruct p, ts := [] }
    let s := randomRun p (keysFor nkeys) (1 + seed % maxOps)
      (if delPct == 0 then 20 + 10 * (seed % 5) else delPct) steps (seed * 7919) st {}
    total := { states := total.states + s.states, bounds := total.bounds + s.bounds,
               fails := (total.fails ++ s.fails).take 20,
               tp23 := total.tp23 + s.tp23, tp23ex := (total.tp23ex ++ s.tp23ex).take 5,
               maxOpMerges := max total.maxOpMerges s.maxOpMerges,
               maxTxMerges := max total.maxTxMerges s.maxTxMerges,
               reached := s.reached.foldl (fun r (q : String × Nat) =>
                 if r.any (fun z => z.1 == q.1) then r.map (fun z => if z.1 == q.1 then (z.1, z.2 + q.2) else z)
                 else r ++ [q]) total.reached }
    if !s.fails.isEmpty then ok := false
  let _ ← report s!"random M={m} seeds={seeds} steps={steps} keys={nkeys} ops<={maxOps}{if delPct == 0 then "" else s!" deletes {delPct}%"}{mergeName merges theta p}" total
  pure ok

/-- The runs with merges at the delete (bergdb 024-22, section 3): node sizes 8
and 10, where 024-11's thresholds meet `MergeParamsOK` (at 4 and 6 they do not:
m = max(2, M / 4) = 2 is more than a space split's smaller half); prefix 4 and
the random runs reach the merge's take-back of a right node (section 4). -/
def runMergeSet : IO Bool := do
  let a ← runExhaustive 8 3 12 2 false true
  let b ← runExhaustive 8 3 12 4 false true
  let c ← runExhaustive 10 2 14 4 false true
  let d ← runExhaustive 8 2 12 2 true true
  let e ← runSubsets 8 12 2 0 false true
  let f ← runSubsets 8 9 3 0 true true
  let g ← runSubsets 8 210 0 1 true true
  let h ← runRandom 8 20 200 40 true 12
  let k ← runRandom 8 10 200 124 true 20 50
  let l ← runModel 8 6 60 30 true
  pure (a && b && c && d && e && f && g && h && k && l)

/-- The runs with option 2 of dead klongs (bergdb 024-23, section 3), with the
merges, as record format 7 has them: node sizes 8, 10 and 12 (theta 2; at 8
theta 1 until 2026-11-12, 024-19, Q4) and 14 (theta 3); prefix 4 (every key put twice) starts in nodes full of dead
klongs; and option 2 alone, at node size 4 (theta 1, forced) and 8. -/
def runThetaSet : IO Bool := do
  let a ← runExhaustive 8 3 12 2 false true true
  let b ← runExhaustive 8 3 12 4 false true true
  let c ← runExhaustive 10 2 14 4 false true true
  let d ← runExhaustive 12 2 14 4 false true true
  let e ← runExhaustive 8 2 12 2 true true true
  let f ← runSubsets 8 12 2 0 false true true
  let g ← runSubsets 8 9 3 0 true true true
  let h ← runSubsets 8 210 0 1 true true true
  let k ← runRandom 8 20 200 40 true 12 0 true
  let l ← runRandom 8 10 200 124 true 20 50 true
  let m ← runRandom 14 10 300 60 true 12 30 true
  let n ← runModel 8 6 60 30 true true
  let o ← runExhaustive 4 4 6 2 false false true
  let q ← runExhaustive 8 3 12 4 false false true
  pure (a && b && c && d && e && f && g && h && k && l && m && n && o && q)

def main (args : List String) : IO UInt32 := do
  let flags := ["merge", "pairs", "puts", "theta"]
  let nums := args.filter (fun a => !flags.contains a)
  let nat := fun (i : Nat) (d : Nat) => (nums[i]?.bind String.toNat?).getD d
  let mg := args.contains "merge"
  let th := args.contains "theta"
  let ok ← match args.head? with
    | some "exhaustive" => runExhaustive (nat 1 4) (nat 2 5) (nat 3 4) (nat 4 0) (args.contains "pairs") mg th
    | some "subsets" => runSubsets (nat 1 8) (nat 2 10) (nat 3 1) (nat 4 0) (args.contains "puts") mg th
    | some "random" => runRandom (nat 1 8) (nat 2 20) (nat 3 150) (nat 4 14) mg (nat 5 6) (nat 6 0) th
    | some "model" => runModel (nat 1 8) (nat 2 10) (nat 3 40) (nat 4 10) mg th
    | some "merges" => runMergeSet
    | some "thetas" => runThetaSet
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
      let r ← runMergeSet
      let t ← runThetaSet
      pure (a && b && c && d && e && f && g && h && k && l && m && n && o && q && r && t)
  if ok then
    IO.println "TREETEST OK"
    return 0
  else
    IO.println "TREETEST FAILED"
    return 1
