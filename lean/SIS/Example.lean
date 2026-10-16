/-
Self-indexed streams in Lean: examples and checks by running the model.

Not part of the trusted part. These are tests: they run the definitions on
small structures, which catches mistakes in the definitions early. They do
not prove anything for all runs; the theorems do that.
-/
import SIS.Assumptions

namespace SIS.Example

open SIS

/-- Entry values of the example structures. -/
inductive Val where
  /-- Slot k points to y. A later entry for the same slot replaces it, so
  the earlier pointer is dead from then on. -/
  | slot (k : Nat) (y : NodeId)
  /-- A pointer that stays live. -/
  | ref (y : NodeId)
  /-- Data, no pointer. -/
  | dat (n : Nat)
  /-- A pointer that is never live (example 3: a top node's pointer to the
  previous top node, as BergDB's skip pointers). -/
  | dead (y : NodeId)
  deriving DecidableEq, Repr

def ptrs : Val → List NodeId
  | .slot _ y => [y]
  | .ref y => [y]
  | .dat _ => []
  | .dead y => [y]

/-- The live pointer of slot k: the latest slot entry for k. -/
def slotOf (h : History Val) (k : Nat) : Option NodeId :=
  h.foldl (fun acc e => match e.val with
    | .slot k' y => if k' = k then some y else acc
    | _ => acc) none

/-- children(x, t): all ref pointers, and the latest pointer of each slot. -/
def live (h : History Val) : List NodeId :=
  let refs := h.filterMap (fun e => match e.val with | .ref y => some y | _ => none)
  let slots := (h.filterMap (fun e => match e.val with | .slot k _ => some k | _ => none)).eraseDups
  (refs ++ slots.filterMap (slotOf h)).eraseDups

/-- Build a node with all entries at time 0. -/
def mk (level : Nat) (vals : List Val) : Node Val :=
  { level := level, isData := false, hist := vals.map (fun v => ⟨0, v⟩) }

/-! ## Example 1: section 7 of sis-model.md

A root R (id 0, level 1) with two leaves A (id 1) and B (id 2), level 0.
A transaction adds an entry to a leaf. -/

inductive Tr1 where
  | add (leaf : NodeId) (n : Nat)
  deriving DecidableEq, Repr

def spec1 : Spec Val Tr1 where
  ptrs := ptrs
  live := live
  exec := fun tr _ view => match tr with
    | .add leaf n => if (view leaf).isSome then { new := [], adds := [(leaf, .dat n)] }
                     else { new := [], adds := [] }
  init := [(0, mk 1 [.ref 1, .ref 2]), (1, mk 0 []), (2, mk 0 [])]
  rootVal := .ref

/-- The policy of section 7: s(i) = i - 2 (clamped by the algorithm). -/
def algo1 : Algo Val Tr1 := { policy := fun _ _ i _ => i - 2, stillDirty := exactTest spec1 }

def run1 : DB Val Tr1 := run spec1 algo1 [.add 1 10, .add 2 20, .add 1 30, .add 1 40]

-- D after T(4): {R: 3, A: 4}.
#guard run1.D == [(0, 3), (1, 4)]
-- gd(1) = {R, A}, gd(2) = {B}, gd(3) = {R}, gd(4) = {A}.
#guard run1.S.map (·.gd) == [[], [0, 1], [2], [0], [1]]
-- s(1), ..., s(4) = 0, 0, 1, 2.
#guard run1.S.map (·.sp) == [0, 0, 0, 1, 2]

/-- The view of P at time t, for the nodes 0 to 2, as a list. -/
def views1 (P : Struct Val) (t : Time) : List (Option (Node Val)) :=
  [0, 1, 2].map (view spec1 P t)

-- Startup gives back D, and the same view at every time 0 to 4.
#guard (startup spec1 run1.S).D == run1.D
#guard (List.range 5).all (fun t => views1 (startup spec1 run1.S).P t == views1 run1.P t)
-- Without Rule R, startup gets time 2 wrong: B misses the entry of T(2).
#guard views1 (startupWith spec1 false run1.S).P 2 != views1 run1.P 2

/-! ## Example 2: a tree with splits and data nodes

Root (id 0, level 3) with slots 0 and 1 for two mid nodes (ids 1, 2, level 2),
each with slots 0 and 1 for leaves (ids 3 to 6, level 1). A leaf has ref
entries to data nodes (level 0). put k n, for k in 0 to 3, creates a data
node with value n and adds a ref to it to leaf k. A leaf with `cap` refs is
replaced (time split): a new leaf gets the ref, and the mid node's slot is
repointed, so the old leaf is dead from then on. Ids of new nodes are made
from i: 1000 + 2i (data node) and 1001 + 2i (new leaf). -/

structure Tr2 where
  k : Nat
  n : Nat
  deriving DecidableEq, Repr

def cap : Nat := 3

def exec2 (tr : Tr2) (i : Time) (view : View Val) : Changes Val :=
  let none' : Changes Val := { new := [], adds := [] }
  match view 0 with
  | none => none'
  | some r =>
    match slotOf r.hist (tr.k / 2 % 2) with
    | none => none'
    | some m =>
      match (view m).bind (fun mn => slotOf mn.hist (tr.k % 2)) with
      | none => none'
      | some leaf =>
        match view leaf with
        | none => none'
        | some ln =>
          let d := 1000 + 2 * i
          if (live ln.hist).length ≥ cap then
            let l' := 1001 + 2 * i
            { new := [⟨d, 0, true⟩, ⟨l', 1, false⟩],
              adds := [(d, .dat tr.n), (l', .ref d), (m, .slot (tr.k % 2) l')] }
          else
            { new := [⟨d, 0, true⟩], adds := [(d, .dat tr.n), (leaf, .ref d)] }

def spec2 : Spec Val Tr2 where
  ptrs := ptrs
  live := live
  exec := exec2
  rootVal := .ref
  init := [(0, mk 3 [.slot 0 1, .slot 1 2]),
           (1, mk 2 [.slot 0 3, .slot 1 4]), (2, mk 2 [.slot 0 5, .slot 1 6]),
           (3, mk 1 []), (4, mk 1 []), (5, mk 1 []), (6, mk 1 [])]

/-- The conservative still-dirty test: the node points to a node in D. -/
def conservative (sp : Spec Val T) : Stream Val T → Struct Val → Dirty → Time → NodeId → Bool :=
  fun _ P D _ x => match P.get? x with
    | some n => (pointees sp n.hist).any (inD D)
    | none => true

/-! ## Checks -/

variable {T : Type}

/-- The assumptions on the initial structure (SpecOK in Assumptions.lean),
checked by running. LiveSub holds for `live` above by construction. -/
def specOKB (sp : Spec Val T) : Bool :=
  let P := sp.init
  let ids := P.map (·.1)
  ids.eraseDups.length == ids.length &&
  (P.get? root).isSome &&
  P.all (fun p => p.2.hist.all (fun e => e.time == 0)) &&
  P.all (fun p => !p.2.isData || p.2.hist.all (fun e => (sp.ptrs e.val).isEmpty)) &&
  P.all (fun p => p.2.hist.all (fun e => (sp.ptrs e.val).all (fun y =>
    match P.get? y with
    | some m => decide (m.level < p.2.level)
    | none => false))) &&
  P.all (fun p => reachable sp P 0 p.1)

/-- With a virtual root: the assumptions on the initial structure (VirtInit),
checked by running (R1 for the ids of the initial structure). -/
def virtInitB (sp : Spec Val T) : Bool :=
  let P := sp.init
  let tops := P.filter (fun p => p.1 != root && decide (sp.topLevel ≤ p.2.level))
  P.all (fun p => sp.ptrs (sp.rootVal p.1) == [p.1]) &&
  (match P.get? root with
   | some n => !n.isData && n.hist == tops.map (fun p => (⟨0, sp.rootVal p.1⟩ : Entry Val))
   | none => false) &&
  decide (tops.length ≤ 1) && tops.all (fun p => !p.2.isData && !p.2.hist.isEmpty)

/-- With a virtual root: the assumptions on one transaction (VirtStep),
checked by running. -/
def virtStepB (sp : Spec Val T) (P : Struct Val) (i : Time) (c : Changes Val) : Bool :=
  let P' := P.apply i c
  let tops := c.new.filter (fun nn => decide (sp.topLevel ≤ nn.level))
  decide (tops.length ≤ 1) &&
  tops.all (fun nn => !nn.isData && c.adds.any (fun a => a.1 == nn.id)) &&
  c.adds.all (fun a => match P.get? a.1 with
    | some n => a.1 == root || decide (n.level < sp.topLevel)
    | none => true) &&
  c.adds.filter (fun a => a.1 == root) == tops.map (fun nn => (root, sp.rootVal nn.id)) &&
  tops.all (fun nn => match P'.get? nn.id with
    | some n => P.all (fun p => p.1 == root || !(decide (sp.topLevel ≤ p.2.level)) ||
        (topClosure sp P' nn.id n).contains p.1)
    | none => false) &&
  P'.all (fun p => !(isTop sp P' p.1) || (pointees sp p.2.hist).all (fun y =>
    !(isTop sp P' y) || !(reachable sp P' i y)))

/-- The assumptions on one transaction (StepOK in Assumptions.lean), checked
by running. -/
def stepOKB (sp : Spec Val T) (P : Struct Val) (i : Time) (c : Changes Val) : Bool :=
  let P' := P.apply i c
  let ids := c.new.map (·.id)
  c.new.all (fun n => (P.get? n.id).isNone) &&
  ids.eraseDups.length == ids.length &&
  c.adds.all (fun a => reachable sp P' i a.1) &&
  c.adds.all (fun a => match P.get? a.1 with
    | some n => !n.isData
    | none => true) &&
  c.adds.all (fun a => c.new.all (fun n => n.id != a.1 || !n.isData || (sp.ptrs a.2).isEmpty)) &&
  c.adds.all (fun a => (sp.ptrs a.2).all (fun y =>
    match P'.get? a.1, P'.get? y with
    | some n, some m => decide (m.level < n.level)
    | _, _ => false)) &&
  c.new.all (fun n => reachable sp P' i n.id) &&
  (reachList sp P' i).all (fun y => reachable sp P (i - 1) y || c.new.any (fun n => n.id == y)) &&
  (!sp.virt || virtStepB sp P i c)

/-- The assumptions hold for a run (RunOK), checked by running. -/
def runOKB (sp : Spec Val T) (al : Algo Val T) (ts : List T) : Bool :=
  specOKB sp && (!sp.virt || virtInitB sp) &&
  (List.range ts.length).all (fun j =>
    match ts[j]? with
    | some tr =>
      let db := run sp al (ts.take j)
      stepOKB sp db.P (j + 1) (sp.exec tr (j + 1) (view sp db.P j))
    | none => false)

/-- All node ids of two structures. -/
def ids (P P' : Struct Val) : List NodeId := (P.map (·.1) ++ P'.map (·.1)).eraseDups

/-- P ≈ P' up to time k, decided by comparing views. -/
def equivB (sp : Spec Val T) (k : Time) (P P' : Struct Val) : Bool :=
  (List.range (k + 1)).all (fun t => (ids P P').all (fun x => view sp P t x == view sp P' t x))

/-- T1 for one state: startup from its stream gives an equivalent P and the
same D. -/
def checkT1 (sp : Spec Val T) (ruleR : Bool) (db : DB Val T) : Bool :=
  let db' := startupWith sp ruleR db.S
  equivB sp (db.S.length - 1) db'.P db.P && db'.D == db.D

/-- All states of a run: after T(0), T(1), and so on. -/
def states (sp : Spec Val T) (al : Algo Val T) (ts : List T) : List (DB Val T) :=
  ts.scanl (step sp al) (init sp)

/-- A small pseudo-random generator (linear congruential). -/
def lcg (x : Nat) : Nat := (1103515245 * x + 12345) % 2147483648

/-- n pseudo-random transactions for example 2, with restart marks. -/
def randomTs (seed n : Nat) : List (Tr2 × Bool) :=
  (List.range n).foldl (fun acc _ =>
    let x := lcg acc.2
    let y := lcg x
    (acc.1 ++ [(⟨x / 65536 % 4, y / 65536 % 100⟩, (x / 1024) % 3 == 0)], y)) ([], seed)
  |>.1

/-- Startup pos policies: keep the last d transactions in the section, or
an erratic one that depends on the transaction (as BergDB's does, M10). -/
def policies : List (Stream Val Tr2 → Dirty → Time → Tr2 → Nat) :=
  [fun _ _ i _ => i - 1, fun _ _ i _ => i - 2, fun _ _ i _ => i - 4,
   fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5]

/-- The algorithms checked: each policy with the exact test and BergDB's
(`javaTest`), and step 3 by testing or by marking (`Algo.mark`). -/
def algos2 : List (Algo Val Tr2) :=
  policies.flatMap (fun p =>
    [false, true].flatMap (fun m =>
      [{ policy := p, stillDirty := exactTest spec2, mark := m },
       { policy := p, stillDirty := javaTest spec2, mark := m }]))

/-- Marking gives the same records as testing (T13), for every policy and both
still-dirty tests, on one random run. -/
def markSame (seed n : Nat) : Bool :=
  let ts := (randomTs seed n).map (·.1)
  policies.all (fun p =>
    [exactTest spec2, javaTest spec2].all (fun sd =>
      (run spec2 { policy := p, stillDirty := sd, mark := true } ts).S ==
        (run spec2 { policy := p, stillDirty := sd, mark := false } ts).S))

/-- Results for one seed and one algorithm: (the assumptions hold, T1 holds
in every state, T2 holds, number of states where startup without Rule R
fails T1). -/
def checkOne (al : Algo Val Tr2) (seed n : Nat) : Bool × Bool × Bool × Nat :=
  let ts := randomTs seed n
  let sts := states spec2 al (ts.map (·.1))
  let ok := runOKB spec2 al (ts.map (·.1))
  let t1 := sts.all (checkT1 spec2 true)
  let t2 := (runRestarts spec2 al ts).S == (run spec2 al (ts.map (·.1))).S
  let noR := (sts.filter (fun db => !checkT1 spec2 false db)).length
  (ok, t1, t2, noR)

-- The example of section 7 meets the assumptions.
#guard runOKB spec1 algo1 [.add 1 10, .add 2 20, .add 1 30, .add 1 40]

/-! ## Example 3: a virtual root (option (a) of Q7), as in BergDB

The root (id 0, level 1000) is virtual: never written; startup rebuilds it.
Its children are top nodes (level 100 and up, `topLevel`): each points to a
tree root (live) and to the previous top node (dead, BergDB's skip pointer).
The root's entry for top node z is `slot 0 z`, so its live child is the newest
top node. A transaction puts into a tree as in example 2, or, with `split`,
makes a new tree root (a copy of the live slots of the current one) and a new
top node above it, as BergDB does when the root key node splits. Ids of new
nodes are made from i: 10000 + 4i (data node), 10001 + 4i (new leaf),
10002 + 4i (new tree root), 10003 + 4i (new top node). -/

structure Tr3 where
  k : Nat
  n : Nat
  split : Bool
  deriving DecidableEq, Repr

def exec3 (tr : Tr3) (i : Time) (view : View Val) : Changes Val :=
  let none' : Changes Val := { new := [], adds := [] }
  match (view 0).bind (fun r => slotOf r.hist 0) with
  | none => none'
  | some z =>
    match (view z).bind (fun zn => (live zn.hist).head?) with
    | none => none'
    | some t0 =>
      match view t0 with
      | none => none'
      | some tn =>
        if tr.split then
          let t' := 10002 + 4 * i
          let z' := 10003 + 4 * i
          { new := [⟨t', 3, false⟩, ⟨z', 100 + i, false⟩],
            adds := ((slotOf tn.hist 0).toList.map (fun m => (t', Val.slot 0 m))) ++
              ((slotOf tn.hist 1).toList.map (fun m => (t', Val.slot 1 m))) ++
              [(z', .ref t'), (z', .dead z), (0, .slot 0 z')] }
        else
          match slotOf tn.hist (tr.k / 2 % 2) with
          | none => none'
          | some m =>
            match (view m).bind (fun mn => slotOf mn.hist (tr.k % 2)) with
            | none => none'
            | some leaf =>
              match view leaf with
              | none => none'
              | some ln =>
                let d := 10000 + 4 * i
                if (live ln.hist).length ≥ cap then
                  let l' := 10001 + 4 * i
                  { new := [⟨d, 0, true⟩, ⟨l', 1, false⟩],
                    adds := [(d, .dat tr.n), (l', .ref d), (m, .slot (tr.k % 2) l')] }
                else
                  { new := [⟨d, 0, true⟩], adds := [(d, .dat tr.n), (leaf, .ref d)] }

def spec3 : Spec Val Tr3 where
  ptrs := ptrs
  live := live
  exec := exec3
  virt := true
  topLevel := 100
  rootVal := fun z => .slot 0 z
  init := [(0, { level := 1000, isData := false, hist := [⟨0, .slot 0 10⟩] }),
           (10, { level := 100, isData := false, hist := [⟨0, .ref 20⟩] }),
           (20, mk 3 [.slot 0 1, .slot 1 2]),
           (1, mk 2 [.slot 0 3, .slot 1 4]), (2, mk 2 [.slot 0 5, .slot 1 6]),
           (3, mk 1 []), (4, mk 1 []), (5, mk 1 []), (6, mk 1 [])]

/-- n pseudo-random transactions for example 3, with restart marks. -/
def randomTs3 (seed n : Nat) : List (Tr3 × Bool) :=
  (List.range n).foldl (fun acc _ =>
    let x := lcg acc.2
    let y := lcg x
    (acc.1 ++ [(⟨x / 65536 % 4, y / 65536 % 100, (y / 1024) % 5 == 0⟩, (x / 1024) % 3 == 0)], y))
    ([], seed)
  |>.1

def policies3 : List (Stream Val Tr3 → Dirty → Time → Tr3 → Nat) :=
  [fun _ _ i _ => i - 1, fun _ _ i _ => i - 2, fun _ _ i _ => i - 4,
   fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5]

/-- The algorithms checked with the virtual root: BergDB's still-dirty test
(the theorems need it with a virtual root), step 3 by testing or by marking. -/
def algos3 : List (Algo Val Tr3) :=
  policies3.flatMap (fun p =>
    [false, true].map (fun m => { policy := p, stillDirty := javaTest spec3, mark := m }))

/-- As `checkOne`, for example 3. -/
def checkOne3 (al : Algo Val Tr3) (seed n : Nat) : Bool × Bool × Bool × Nat :=
  let ts := randomTs3 seed n
  let sts := states spec3 al (ts.map (·.1))
  let ok := runOKB spec3 al (ts.map (·.1))
  let t1 := sts.all (checkT1 spec3 true)
  let t2 := (runRestarts spec3 al ts).S == (run spec3 al (ts.map (·.1))).S
  let noR := (sts.filter (fun db => !checkT1 spec3 false db)).length
  (ok, t1, t2, noR)

/-- The number of states of a run of example 3 with the exact still-dirty test
where startup fails T1: the theorems do not cover the exact test with a
virtual root, because a top node can then keep a stale reference to an older
top node (`VInv.fresh`). -/
def exactFails3 (seed n : Nat) : Nat :=
  let ts := (randomTs3 seed n).map (·.1)
  policies3.foldl (fun acc p =>
    let al : Algo Val Tr3 := { policy := p, stillDirty := exactTest spec3 }
    acc + ((states spec3 al ts).filter (fun db => !checkT1 spec3 true db)).length) 0

/-- A run of example 3 where the exact still-dirty test breaks T1 with the
virtual root, and BergDB's test does not: seed 3, the first 41 transactions,
a policy that keeps up to 8 transactions in the section. Found by search on
2026-10-16. Returns (the assumptions hold, T1 fails with the exact test, T1
holds with BergDB's test). -/
def exactWitness3 : Bool × Bool × Bool :=
  let ts := ((randomTs3 3 45).map (·.1)).take 41
  let pol : SIS.Stream Val Tr3 → Dirty → Time → Tr3 → Nat := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 8
  let ex : Algo Val Tr3 := { policy := pol, stillDirty := exactTest spec3 }
  let jv : Algo Val Tr3 := { policy := pol, stillDirty := javaTest spec3 }
  (runOKB spec3 ex ts, !checkT1 spec3 true (run spec3 ex ts), checkT1 spec3 true (run spec3 jv ts))

-- Example 3 meets the assumptions, a virtual root's included.
#guard runOKB spec3 { policy := fun _ _ i _ => i - 1, stillDirty := javaTest spec3 }
  ((randomTs3 1 12).map (·.1))

end SIS.Example
