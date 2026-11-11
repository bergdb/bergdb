/-
Random runs of Level 3, reclaim (bergdb item 001, WP R3; SIS/ReclaimExample.lean):
example 4 with pseudo-random puts, splits and reclaim iterations, restarting at
random transactions from the stream cut at the largest safe position (`CutOK`
checked by running). For each startup pos policy: the assumptions and
`PolicyCutOK`, T8 at every restart, T12; and with handles (bergdb 005-62,
SIS/HandleReclaimExample.lean) and five eviction schedules, the records and D
after every transaction (T12 over handles), reads from the first available time
on, on the cut stream too (T9 over handles), and after the restarts, and the
lookups at the end; and at every restart, rule 4 by position
with the cut as the stream's first position against rule 4 by node id
(bergdb 005-62, `posCutCounts`). And T-SCHEME by running
(WP R6, `checkSchemeB`): for every iteration whose scheme conditions hold,
`CutOK` at its cut position in every later state past the waits. And the same
with the cover in place of the touch's (bergdb 024-07, `checkSchemeC`), on
example 4 and on example 4 without any touch (`spec4n`): the iterations with a
data node below every index node all have the cover (T-COVER), and `CutOK`
holds past the waits for every iteration with the cover and the rewrites.
Usage: lake exe reclaimtest [seeds] [n] [scheme]
  scheme: T-SCHEME only (for larger runs).
-/
import SIS.ReclaimExample
import SIS.HandleReclaimExample

open SIS SIS.Example SIS.PhysExample SIS.ReclaimExample SIS.HandleReclaimExample

def main (args : List String) : IO UInt32 := do
  let seeds := (args[0]?.bind String.toNat?).getD 20
  let n := (args[1]?.bind String.toNat?).getD 30
  let schemeOnly := args[2]? == some "scheme"
  let mut bad := 0
  for (pol, a) in policies4.zipIdx do
    let al := algo4 pol
    let mut okok := 0
    let mut t8ok := 0
    let mut t12ok := 0
    let mut cuts : List Nat := []
    let mut hist := 0
    let mut htrans := 0
    let mut hfails := 0
    let mut pc : List Nat := [0, 0, 0, 0, 0, 0, 0]
    let mut sIters := 0
    let mut sStates := 0
    let mut sFails := 0
    let mut cT : Nat × Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0, 0)
    let mut cN : Nat × Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0, 0)
    for seed in [1:seeds + 1] do
      let ts := randomTs4 seed n
      let (si, ss, sf) := checkSchemeB spec4 al (ts.map (·.1))
      sIters := sIters + si
      sStates := sStates + ss
      sFails := sFails + sf
      cT := addC cT (checkSchemeC spec4 al (ts.map (·.1)))
      cN := addC cN (checkSchemeC spec4n al (ts.map (·.1)))
      if !schemeOnly then
        let cs := cutsFor spec4 al ts
        let (ok, t8, t12, cm) := checkCut spec4 al cs
        if ok then okok := okok + 1 else bad := bad + 1
        if t8 then t8ok := t8ok + 1 else bad := bad + 1
        if t12 then t12ok := t12ok + 1 else bad := bad + 1
        cuts := cuts ++ [cm]
        hist := hist + historicalAtCuts spec4 al cs
        for sched in [0, 1, 2, 3, 4] do
          let (n2, f2) := checkHandleCut spec4 al cs sched seed
          htrans := htrans + n2
          hfails := hfails + f2
        pc := List.zipWith (· + ·) pc (posCutCounts spec4 al cs)
    if hfails != 0 then bad := bad + 1
    if sFails != 0 then bad := bad + 1
    if pc.getD 3 0 + pc.getD 4 0 + pc.getD 5 0 != 0 then bad := bad + 1
    if cT.2.1 + cT.2.2.2.2.2 + cN.2.1 + cN.2.2.2.2.2 != 0 then bad := bad + 1
    let cover := fun (c : Nat × Nat × Nat × Nat × Nat × Nat) =>
      s!"{c.1} iterations with a data node below every index node, {c.2.1} of them without the cover; {c.2.2.1} iterations with the cover and the rewrites ({c.2.2.2.1} with the touch's cover too), CutOK checked in {c.2.2.2.2.1} states past the waits, {c.2.2.2.2.2} fail"
    let scheme := s!"T-SCHEME: {sIters} iterations with the scheme's conditions, CutOK checked in {sStates} states past the waits, {sFails} fail; with the cover (024-07): {cover cT}; without any touch: {cover cN}"
    if schemeOnly then
      IO.println s!"policy {a}: {scheme}"
    else
      IO.println s!"policy {a}: assumptions {okok}/{seeds}, T8 {t8ok}/{seeds}, T12 {t12ok}/{seeds} seeds; largest cut per seed: {cuts}; cuts with a node in D not reachable from the first available time on: {hist}; with handles: {htrans} transactions, {hfails} fail; rule 4 by position after a cut: {pc.getD 0 0} restarts, {pc.getD 1 0} with a cut above 0, {pc.getD 2 0} pointers of D below the cut, {pc.getD 3 0} of them to a node with a canonical object, {pc.getD 4 0 + pc.getD 5 0} restarts where it differs from rule 4 by node id ({pc.getD 6 0} without the skip); {scheme}"
  IO.println (if bad == 0 then "all checks pass" else s!"{bad} failures")
  return (if bad == 0 then 0 else 1)
