/-
Runs the model on pseudo-random transactions for example 2 and checks T1
and T2 in every state (SIS/Example.lean). Usage: lake exe sistest [seeds] [n]
-/
import SIS.Example

open SIS SIS.Example

def main (args : List String) : IO UInt32 := do
  let seeds := (args[0]?.bind String.toNat?).getD 10
  let n := (args[1]?.bind String.toNat?).getD 30
  let mut bad := 0
  for (al, a) in algos2.zipIdx do
    let mut okok := 0
    let mut t1ok := 0
    let mut t2ok := 0
    let mut noR := 0
    for seed in [1:seeds + 1] do
      let (ok, t1, t2, nr) := checkOne al seed n
      if ok then okok := okok + 1 else bad := bad + 1
      if t1 then t1ok := t1ok + 1 else bad := bad + 1
      if t2 then t2ok := t2ok + 1 else bad := bad + 1
      noR := noR + nr
    IO.println s!"algorithm {a}: assumptions {okok}/{seeds}, T1 {t1ok}/{seeds}, T2 {t2ok}/{seeds} seeds; states where startup without Rule R fails: {noR}"
  let mut same := 0
  for seed in [1:seeds + 1] do
    if markSame seed n then same := same + 1 else bad := bad + 1
  IO.println s!"marking and testing give the same records (T13): {same}/{seeds} seeds"
  -- Example 3: a virtual root.
  for (al, a) in algos3.zipIdx do
    let mut okok := 0
    let mut t1ok := 0
    let mut t2ok := 0
    let mut noR := 0
    for seed in [1:seeds + 1] do
      let (ok, t1, t2, nr) := checkOne3 al seed n
      if ok then okok := okok + 1 else bad := bad + 1
      if t1 then t1ok := t1ok + 1 else bad := bad + 1
      if t2 then t2ok := t2ok + 1 else bad := bad + 1
      noR := noR + nr
    IO.println s!"virtual root, algorithm {a}: assumptions {okok}/{seeds}, T1 {t1ok}/{seeds}, T2 {t2ok}/{seeds} seeds; states where startup without Rule R fails: {noR}"
  let mut ex := 0
  for seed in [1:seeds + 1] do
    ex := ex + exactFails3 seed n
  IO.println s!"virtual root with the exact still-dirty test (not covered by the theorems): states where startup fails T1: {ex}"
  let (wok, wex, wjv) := exactWitness3
  IO.println s!"witness (seed 3, 41 transactions): assumptions {wok}, the exact test fails T1 {wex}, BergDB's test passes T1 {wjv}"
  if !(wok && wex && wjv) then bad := bad + 1
  IO.println (if bad == 0 then "all checks pass" else s!"{bad} failures")
  return (if bad == 0 then 0 else 1)
