/-
Random runs of Level 3, reclaim (bergdb item 001, WP R3; SIS/ReclaimExample.lean):
example 4 with pseudo-random puts, splits and reclaim iterations, restarting at
random transactions from the stream cut at the largest safe position (`CutOK`
checked by running). For each startup pos policy: the assumptions and
`PolicyCutOK`, T8 at every restart, T12; and with eviction and the four cache
schedules, after every transaction, the records and D, reads from the first
available time on (on the cut stream from the running memory too, T9), the
invariants, and the restarts from the cut streams. And T-SCHEME by running
(WP R6, `checkSchemeB`): for every iteration whose scheme conditions hold,
`CutOK` at its cut position in every later state past the waits.
Usage: lake exe reclaimtest [seeds] [n] [scheme]
  scheme: T-SCHEME only (for larger runs).
-/
import SIS.ReclaimExample

open SIS SIS.Example SIS.PhysExample SIS.EvictExample SIS.ReclaimExample

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
    let mut trans := 0
    let mut fails := 0
    let mut sIters := 0
    let mut sStates := 0
    let mut sFails := 0
    for seed in [1:seeds + 1] do
      let ts := randomTs4 seed n
      let (si, ss, sf) := checkSchemeB spec4 al (ts.map (·.1))
      sIters := sIters + si
      sStates := sStates + ss
      sFails := sFails + sf
      if !schemeOnly then
        let cs := cutsFor spec4 al ts
        let (ok, t8, t12, cm) := checkCut spec4 al cs
        if ok then okok := okok + 1 else bad := bad + 1
        if t8 then t8ok := t8ok + 1 else bad := bad + 1
        if t12 then t12ok := t12ok + 1 else bad := bad + 1
        cuts := cuts ++ [cm]
        hist := hist + historicalAtCuts spec4 al cs
        for sched in [0, 1, 2, 3] do
          let (n1, f1) := checkEvictCut spec4 al cs sched seed
          trans := trans + n1
          fails := fails + f1
    if fails != 0 then bad := bad + 1
    if sFails != 0 then bad := bad + 1
    let scheme := s!"T-SCHEME: {sIters} iterations with the scheme's conditions, CutOK checked in {sStates} states past the waits, {sFails} fail"
    if schemeOnly then
      IO.println s!"policy {a}: {scheme}"
    else
      IO.println s!"policy {a}: assumptions {okok}/{seeds}, T8 {t8ok}/{seeds}, T12 {t12ok}/{seeds} seeds; largest cut per seed: {cuts}; cuts with a node in D not reachable from the first available time on: {hist}; with eviction: {trans} transactions, {fails} fail; {scheme}"
  IO.println (if bad == 0 then "all checks pass" else s!"{bad} failures")
  return (if bad == 0 then 0 else 1)
