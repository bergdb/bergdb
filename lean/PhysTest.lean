/-
Random runs of the physical layer (bergdb item 001, WPs L1 and L3): in states
of random runs of examples 2 and 3, the lazy startup from the stream, or from
a prefix of it (a crash), then random reads and writer walks in random order;
every read must give P at its time, and every canonical object must hold its
node's whole history. Usage: lake exe phystest [seeds] [n]
-/
import SIS.PhysExample

open SIS SIS.Example SIS.PhysExample

/-- Random operations on the memory after startup from the stream of db: reads at
random times and the writer's walks to random nodes reachable at the last time.
Returns (reads, reads that gave P, canonical checks passed, operations). -/
def randomOps {T : Type} (sp : Spec Val T) (db : DB Val T) (seed ops : Nat) : Nat × Nat × Nat × Nat :=
  let k := db.S.length - 1
  let xs := (reachList sp db.P k).eraseDups
  let r := (List.range ops).foldl (fun (acc : Mem Val × Nat × Nat × Nat × Nat × Nat) _ =>
    let (m, x, reads, good, canon, n) := acc
    let x1 := lcg x
    if x1 / 1024 % 3 == 0 && !xs.isEmpty then
      -- The writer walks to a node reachable at the last time.
      let target := xs[(x1 / 4096) % xs.length]!
      let m' := match pathTo sp db.P k target 4000 root with
        | some p => writerWalk sp db.S m p
        | none => m
      (m', x1, reads, good, canon + (if canonOK db m' && memInvB sp db m' then 1 else 0), n + 1)
    else
      let t := (x1 / 4096) % (k + 1)
      let (m', l) := m.read sp db.S t
      (m', x1, reads + 1, good + (if readOK sp db l t then 1 else 0),
        canon + (if memInvB sp db m' then 1 else 0), n + 1))
    (lazyStartup sp db.S, seed, 0, 0, if memInvB sp db (lazyStartup sp db.S) then 0 else 1000000, 0)
  let (_, _, reads, good, canon, n) := r
  (reads, good, canon, n)

def main (args : List String) : IO UInt32 := do
  let seeds := (args[0]?.bind String.toNat?).getD 10
  let n := (args[1]?.bind String.toNat?).getD 30
  let mut bad := 0
  -- Example 3, a virtual root: four policies, every state, and prefixes (crashes).
  for (pol, a) in policies3.zipIdx do
    let al : Algo Val Tr3 := { policy := pol, stillDirty := javaTest spec3, mark := true }
    let mut reads := 0
    let mut good := 0
    let mut canonBad := 0
    let mut nStates := 0
    for seed in [1:seeds + 1] do
      let ts := (randomTs3 seed n).map (·.1)
      for db in states spec3 al ts do
        nStates := nStates + 1
        let (r, g, c, o) := randomOps spec3 db (seed * 7919 + db.S.length) 12
        reads := reads + r
        good := good + g
        canonBad := canonBad + (o - c)
    let physOK := (List.range seeds).all (fun i => physRunOKB spec3 al ((randomTs3 (i + 1) n).map (·.1)))
    if good != reads || canonBad != 0 || !physOK then bad := bad + 1
    IO.println s!"example 3, policy {a}: {nStates} states, reads {good}/{reads} give P, canonical objects not whole or invariant broken: {canonBad}, PhysRunOK: {physOK}"
  -- Crashes: startup from the first j + 1 records of the last state's stream gives P after j.
  let mut crashStates := 0
  let mut crashGood := 0
  for seed in [1:seeds + 1] do
    let ts := (randomTs3 seed n).map (·.1)
    let al : Algo Val Tr3 :=
      { policy := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5,
        stillDirty := javaTest spec3, mark := true }
    let sts := states spec3 al ts
    match sts.getLast? with
    | none => pure ()
    | some last =>
      for (db, j) in sts.zipIdx do
        crashStates := crashStates + 1
        let S := last.S.take (j + 1)
        let m := lazyStartup spec3 S
        let ok := readsOK spec3 db m (List.range (j + 1))
        if ok then crashGood := crashGood + 1
  if crashGood != crashStates then bad := bad + 1
  IO.println s!"example 3, crashes: {crashGood}/{crashStates} prefixes read P"
  -- Example 2, a written root: the 16 algorithms.
  for (al, a) in algos2.zipIdx do
    let mut reads := 0
    let mut good := 0
    let mut canonBad := 0
    for seed in [1:seeds + 1] do
      let ts := (randomTs seed n).map (·.1)
      for db in states spec2 al ts do
        let (r, g, c, o) := randomOps spec2 db (seed * 104729 + db.S.length) 8
        reads := reads + r
        good := good + g
        canonBad := canonBad + (o - c)
    let physOK := (List.range seeds).all (fun i => physRunOKB spec2 al ((randomTs (i + 1) n).map (·.1)))
    if good != reads || canonBad != 0 || !physOK then bad := bad + 1
    IO.println s!"example 2, algorithm {a}: reads {good}/{reads} give P, canonical objects not whole or invariant broken: {canonBad}, PhysRunOK: {physOK}"
  IO.println (if bad == 0 then "all checks pass" else s!"{bad} failures")
  return (if bad == 0 then 0 else 1)
