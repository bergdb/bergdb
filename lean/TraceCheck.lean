/-
The trace checker: checks a trace of a Java run (java/stress/TraceExport.java)
against the model (docs/level2-alignment.md, sections 8.5 and 9).

Usage: lake exe tracecheck TRACE [options]
  --step3 exact|mark    step 3: the exact dirty test, or marking (default mark)
  --step7 exact|java    step 7: the exact test, or Java's (default java)
  --root model|virtual  a written root, or the virtual root of option (a)
                        (Spec.virt; default virtual)
  --model               the Level 2 model before F1-008-11: --step3 exact
                        --step7 exact --root model
  --inv                 also check INV-2 (every dirty index node is in D); slow

The checker runs the model's own `init` and `step` (since 2026-10-16, WP E3;
before, it had checker-local definitions for the switches).

Checks, per transaction i (R(0) included):
  C-A  the assumptions: SpecOK for R(0); StepOK (A2, A3, A4, fresh and distinct
       ids, data nodes) and A5 for every transaction; with a virtual root also
       VirtInit and VirtStep (R1 to R4, dead top nodes)
  C-S  the model's step from Java's state before T(i), with Java's startup pos,
       gives Java's record R(i) and D (gd and the versions compared as sets)
  C-V  the LIVE lines: Java's live children equal the instance's `live`
  C-R  the PROBE lines of the exporter: restarts, lookups, stream identity
and the exporter's ERROR lines. Diagnostics: D closed upward, and with --inv,
INV-2. The last line is TRACECHECK OK or TRACECHECK FAILED.
-/
import Check.Steps

open SIS SIS.Check

def parseOpts : List String → Opts → Opts
  | "--step3" :: "exact" :: r, o => parseOpts r { o with mark := false }
  | "--step3" :: "mark" :: r, o => parseOpts r { o with mark := true }
  | "--step7" :: "exact" :: r, o => parseOpts r { o with java7 := false }
  | "--step7" :: "java" :: r, o => parseOpts r { o with java7 := true }
  | "--root" :: "model" :: r, o => parseOpts r { o with virtual := false }
  | "--root" :: "virtual" :: r, o => parseOpts r { o with virtual := true }
  | "--model" :: r, o => parseOpts r { o with mark := false, java7 := false, virtual := false }
  | "--inv" :: r, o => parseOpts r { o with inv := true }
  | _ :: r, o => parseOpts r o
  | [], o => o

/-- Counts failures by name, and keeps the first examples. -/
structure Tally where
  failing : Nat := 0
  byName : List (String × Nat) := []
  examples : Array String := #[]

def Tally.add (t : Tally) (step : Nat) (fails : List (String × String)) : Tally :=
  if fails.isEmpty then t else
  let names := (fails.map (·.1)).eraseDups
  let byName := names.foldl (fun acc n =>
    match acc.lookup n with
    | some k => acc.map (fun p => if p.1 == n then (n, k + 1) else p)
    | none => acc ++ [(n, 1)]) t.byName
  let ex := if t.examples.size < 12 then
      fails.foldl (fun (a : Array String) f => if a.size < 12 then a.push s!"T({step}) {f.2}" else a)
        t.examples
    else t.examples
  { failing := t.failing + 1, byName := byName, examples := ex }

def Tally.show (t : Tally) (name : String) (total : Nat) : IO Unit := do
  let parts := t.byName.map (fun p => s!"{p.1} {p.2}")
  IO.println (s!"{name}: {t.failing} of {total} transactions fail" ++
    (if parts.isEmpty then "" else s!" ({", ".intercalate parts})"))
  for e in t.examples do
    IO.println s!"  {e}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "usage: lake exe tracecheck TRACE [--step3 exact|mark] [--step7 exact|java] [--root model|virtual] [--model] [--inv]"
    return 2
  | file :: rest =>
    let o := parseOpts rest {}
    let t := parseTrace (← IO.FS.readFile file)
    IO.println s!"TRACECHECK {file}"
    IO.println s!"CONFIG {t.config}"
    IO.println s!"options: step3 {if o.mark then "mark" else "exact"}, step7 {if o.java7 then "java" else "exact"}, root {if o.virtual then "virtual" else "model"}{if o.inv then ", INV-2" else ""}"
    if !t.bad.isEmpty then
      for b in t.bad.toList.take 10 do IO.println s!"PARSE {b}"
      IO.println "TRACECHECK FAILED: the trace could not be read"
      return 1
    let recs := t.recs
    if recs.isEmpty then
      IO.println "TRACECHECK FAILED: no transactions"
      return 1
    let lv := levelMap t
    let chs := recs.map changesOf
    let p0 := Struct.apply (V := BVal) [] 0 (chs.getD 0 { new := [], adds := [] })
    let sp := bspec chs p0 o.virtual
    let jrecs := recs.map (toRecord lv)
    let pol := fun (j : Nat) => (recs.getD j default).sp
    let al := algoOf sp o pol
    let mut ca : Tally := {}
    let mut cs : Tally := {}
    let mut cv : Tally := {}
    let mut diag : Tally := {}
    let mut liveCount := 0
    -- R(0)
    let initF := initFailures sp
    ca := ca.add 0 (initF.map (fun n => (n, s!"{n} fails for R(0)")))
    let mi := init sp
    match mi.S.getLast?, jrecs[0]? with
    | some m, some j => cs := cs.add 0 (diffRecord m j)
    | _, _ => cs := cs.add 0 [("record", "no R(0)")]
    -- T(1), ..., T(k)
    let mut P := p0
    for i in [1:recs.size] do
      let r := recs.getD i default
      if r.idx != i then
        cs := cs.add i [("order", s!"TX {r.idx} at position {i}")]
      let c := chs.getD i { new := [], adds := [] }
      let rlPrev := reachList sp P (i - 1)
      let P' := P.apply i c
      let rlNow := reachList sp P' i
      -- C-A
      let sf := stepFailures sp P i c (Std.HashSet.ofList rlPrev) (Std.HashSet.ofList rlNow) rlNow
      ca := ca.add i (sf.map (fun p => (p.1, s!"{p.1} fails for nodes {showIds p.2}")))
      let badTimes := r.adds.toList.filter (fun a => a.2.1 != i)
      if !badTimes.isEmpty then
        ca := ca.add i [("time", s!"entries not at time {i}")]
      -- C-S
      let db : DB BVal Nat := { P := P, D := (recs.getD (i - 1) default).dirty, S := (jrecs.toList.take i) }
      let res := step sp al db i
      let mfails := match res.S.getLast?, jrecs[i]? with
        | some m, some j => diffRecord m j
        | _, _ => [("record", "missing")]
      let dfails := if sameList res.D r.dirty then []
        else [("D", s!"D: model only {(res.D.filter (!r.dirty.contains ·)).take 8}, Java only {(r.dirty.filter (!res.D.contains ·)).take 8}")]
      cs := cs.add i (mfails ++ dfails)
      -- C-V
      for (x, tm, ys) in r.live do
        liveCount := liveCount + 1
        let ml := match P'.get? x with
          | some n => blive (n.hist.upTo tm)
          | none => []
        if !sameList ml ys then
          cv := cv.add i [("live", s!"live of {x} at {tm}: model {ml}, Java {ys}")]
      -- diagnostics
      let cl := closedFailures sp P' i r.dirty
      if !cl.isEmpty then
        diag := diag.add i [("closed", s!"D not closed upward at {showIds cl}")]
      if o.inv then
        let S' := jrecs.toList.take (i + 1)
        let iv := inv2Failures sp S' P' i r.dirty
        if !iv.isEmpty then
          diag := diag.add i [("INV-2", s!"dirty index nodes not in D: {showIds iv}")]
      P := P'
    let probes := recs.toList.flatMap (fun r => r.probes.toList)
    let probeFails := probes.filter (fun p => !p.2.1)
    let total := recs.size
    ca.show "C-A assumptions" total
    cs.show "C-S steps" total
    IO.println s!"C-V live: {cv.failing} transactions with differences, {liveCount} LIVE lines"
    for e in cv.examples do IO.println s!"  {e}"
    IO.println s!"C-R probes: {probeFails.length} of {probes.length} fail"
    for p in probeFails.take 8 do IO.println s!"  PROBE {p.1}: {p.2.2}"
    IO.println s!"exporter errors: {t.errors.size}"
    for e in t.errors.toList.take 8 do IO.println s!"  {e}"
    diag.show "diagnostics" total
    let failed := (if ca.failing > 0 then ["C-A"] else []) ++ (if cs.failing > 0 then ["C-S"] else []) ++
      (if cv.failing > 0 then ["C-V"] else []) ++ (if probeFails.length > 0 then ["C-R"] else []) ++
      (if t.errors.size > 0 then ["exporter"] else []) ++
      (if t.done != some (total - 1) then ["incomplete"] else [])
    if failed.isEmpty then
      IO.println "TRACECHECK OK"
      return 0
    else
      IO.println s!"TRACECHECK FAILED: {" ".intercalate failed}"
      return 1
