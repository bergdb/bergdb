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
  IO.println (if bad == 0 then "all checks pass" else s!"{bad} failures")
  return (if bad == 0 then 0 else 1)
