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
  C-L  the FIRST lines (trace format 2; bergdb item 001, WP L5): every first
       touch after a restart follows the rule of SIS/Phys.lean (Rule R, the
       node table, the version read, cut back to the startup time)
  C-L4 a diagnostic, not part of the verdict (bergdb item 001, WP R8, change
       3): the FIRST lines against the Level 4 loader (`Mem.follow4`,
       SIS/Evict.lean): no snapshot from the node table
  C-CUT with reclaim (bergdb item 001, WP R7): CutOK (SIS/Reclaim.lean) at every
       CUT line, in the model's state after its transaction, and the CUT's
       first available time is the record's; the physical cut (PHYSCUT) is at
       or below the decided one. Since WP R6, part 2 covers the versions that
       a physical read may follow (ReadsPhys; before, the diagnostic C-CUT+),
       but for the versions of D that Rule A put back
With reclaim, also: C-A checks TouchOK (`StepOK.touchIndex`, `touchReach`,
`touchUp`) for the TOUCH lines; C-S compares fa(i) (FA lines; the model clamps
Java's value, `firstAvail`), and from a CUT on runs the model's step on the
stream cut there (`cutStream`: version stubs before the cut).
and in C-S, with SKIPT lines, the top nodes' skip slots: the layout (slot j
of the top with ordinal n is populated exactly when bit j of n is set, and
names the formula's target) and the cached times (the target's creation)
and the exporter's ERROR lines. Diagnostics: D closed upward; A6 (no adoption)
and TREE (one current parent), for Option K of bergdb item 001 (WP A4); and with
--inv, INV-2. The last line is TRACECHECK OK or TRACECHECK FAILED.
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
    let fas := faSeq recs
    let jrecs := (recs.toList.zipIdx.map (fun (r, i) => toRecord lv (fas.getD i 0) r)).toArray
    let pol := fun (j : Nat) => (recs.getD j default).sp
    let al := algoOf sp o pol (fun j => fas.getD j 0)
    let r0 : Record BVal Nat := { trans := none, sp := 0, vers := [], gd := [], top := none }
    let mut ca : Tally := {}
    let mut cs : Tally := {}
    let mut cv : Tally := {}
    let mut clt : Tally := {}
    let mut diag : Tally := {}
    let mut ccut : Tally := {}
    let mut cutCount := 0
    -- The stream as the model sees it from a CUT on: version stubs before the cut.
    let mut Sc := jrecs
    let mut cutNow := 0
    -- The latest version of each node so far: its record and references (C-CUT).
    let mut lvMap : Std.HashMap NodeId (Nat × List (NodeId × Nat)) :=
      ((jrecs.getD 0 r0).vers.foldl (fun m w => m.insert w.node (0, w.refs)) {})
    let fuel := jrecs.foldl (fun n R => n + R.vers.length) 0 + 1
    -- The records of each node's versions so far (C-CUT's part 2, since WP R6).
    let mut recsMap : Std.HashMap NodeId (Array Nat) :=
      ((jrecs.getD 0 r0).vers.foldl (fun m w => m.insert w.node #[0]) {})
    let mut liveCount := 0
    let mut firstCount := 0
    let mut firstFail := 0
    let mut first4Fail := 0
    let mut first4Ex : Array String := #[]
    let Sall := jrecs.toList
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
      let rlNowSet := Std.HashSet.ofList rlNow
      -- C-A
      let rlPrevSet := Std.HashSet.ofList rlPrev
      let sf := stepFailures sp P i c rlPrevSet rlNowSet rlNow ++ touchFailures sp P i c rlPrev rlPrevSet
      ca := ca.add i (sf.map (fun p => (p.1, s!"{p.1} fails for nodes {showIds p.2}")))
      let badTimes := r.adds.toList.filter (fun a => a.2.1 != i)
      if !badTimes.isEmpty then
        ca := ca.add i [("time", s!"entries not at time {i}")]
      -- C-S
      let db : DB BVal Nat := { P := P, D := (recs.getD (i - 1) default).dirty, S := (Sc.toList.take i) }
      let res := step sp al db i
      let mfails := match res.S.getLast?, jrecs[i]? with
        | some m, some j => diffRecord m j
        | _, _ => [("record", "missing")]
      let dfails := if sameList res.D r.dirty then []
        else [("D", s!"D: model only {(res.D.filter (!r.dirty.contains ·)).take 8}, Java only {(r.dirty.filter (!res.D.contains ·)).take 8}")]
      let tfails := r.vers.toList.flatMap (fun w => (topFailures sp P' lv w).map (fun m => ("skip", m)))
      cs := cs.add i (mfails ++ dfails ++ tfails)
      -- C-CUT
      for w in (jrecs.getD i r0).vers do
        lvMap := lvMap.insert w.node (i, w.refs)
        recsMap := recsMap.insert w.node ((recsMap.getD w.node #[]).push i)
      match r.cut with
      | some (cc, f) =>
        cutCount := cutCount + 1
        let faFail := if f == fas.getD i 0 then [] else
          [("CUT-fa", s!"CUT's first available time {f}, the record's {fas.getD i 0}")]
        let m := lvMap
        -- The newest record of each node in R(s), ..., R(i), for Rule R.
        let sec : Std.HashMap NodeId Nat := (List.range' r.sp (i + 1 - r.sp)).foldl (fun mm q =>
          (jrecs.getD q r0).vers.foldl (fun mm w => mm.insert w.node q) mm) {}
        let verAt := fun (q : Nat) (y : NodeId) => (jrecs.getD q r0).vers.find? (·.node == y)
        -- Part 2 over the versions that a read from f on may follow (`ReadsPhys`, since
        -- WP R6): a lookup's, with Rule R (`readsBelow`), and a physical read's
        -- (`readsBelowPhys`, before WP R6 the diagnostic C-CUT+).
        let rm := recsMap
        let below := (List.range' f (i + 1 - f)).flatMap (fun tm =>
          readsBelow sp tm cc (reachList sp P' tm) (fun x => (m.get? x).map (·.1)) verAt
            (fun y => sec.get? y) fuel ++
          readsBelowPhys sp tm cc (reachList sp P' tm) (fun x => (m.get? x).map (·.1)) verAt
            (fun y => (rm.getD y #[]).toList) (fun y => sec.get? y) r.dirty fuel)
        let cf := cutFailures cc f r.dirty below.eraseDups (jrecs.getD i r0).top (fun x => m.get? x)
        ccut := ccut.add i (faFail ++ cf)
        if cutNow < cc then
          for q in [cutNow:cc] do
            Sc := Sc.modify q Record.cut
          cutNow := cc
      | none => pure ()
      match r.physcut with
      | some pc =>
        if cutNow < pc then
          ccut := ccut.add i [("PHYSCUT", s!"the physical cut at R({pc}), above the decided one, R({cutNow})")]
      | none => pure ()
      -- C-L
      let lfails := r.firsts.toList.flatMap (fun f => firstFailures sp Sall i r.sp f)
      firstCount := firstCount + r.firsts.size
      firstFail := firstFail + (r.firsts.toList.filter (fun f => !(firstFailures sp Sall i r.sp f).isEmpty)).length
      clt := clt.add i (lfails.map (fun m => ("first", m)))
      -- C-L4
      let l4 := r.firsts.toList.flatMap loader4Failures
      first4Fail := first4Fail + l4.length
      for m in l4 do
        if first4Ex.size < 8 then
          first4Ex := first4Ex.push s!"T({i}) {m}"
      -- C-V
      for (x, tm, ys) in r.live do
        liveCount := liveCount + 1
        let ml := match P'.get? x with
          | some n => blive (n.hist.upTo tm)
          | none => []
        if !sameList ml ys then
          cv := cv.add i [("live", s!"live of {x} at {tm}: model {ml}, Java {ys}")]
      -- diagnostics, one tally entry per transaction: D closed upward; A6 and
      -- TREE (bergdb item 001, WP A4); A-COPY (the same item, WPs E2 and E3);
      -- INV-2 with --inv
      let cl := closedFailures sp P' i r.dirty
      let a6 := adoptionFailures sp P' i rlNowSet rlNow
      let tr := treeFailures sp P' i rlNow
      let cp := copyFailures sp P i c rlPrev rlNowSet
      let iv := if o.inv then inv2Failures sp (jrecs.toList.take (i + 1)) P' i r.dirty else []
      diag := diag.add i ((if cl.isEmpty then [] else [("closed", s!"D not closed upward at {showIds cl}")]) ++
        (if a6.isEmpty then [] else [("A6", s!"A6 (no adoption) fails for nodes {showIds a6}")]) ++
        (if tr.isEmpty then [] else [("TREE", s!"TREE (one current parent) fails for nodes {showIds tr}")]) ++
        (if cp.isEmpty then [] else [("A-COPY", s!"A-COPY fails for pointers {cp.take 8}")]) ++
        (if iv.isEmpty then [] else [("INV-2", s!"dirty index nodes not in D: {showIds iv}")]))
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
    IO.println s!"C-L first touches: {firstFail} of {firstCount} FIRST lines fail"
    for e in clt.examples do IO.println s!"  {e}"
    IO.println s!"C-L4 (a diagnostic, the Level 4 loader; WP R8, change 3): {first4Fail} of {firstCount} FIRST lines take a snapshot from the node table"
    for e in first4Ex do IO.println s!"  {e}"
    IO.println s!"exporter errors: {t.errors.size}"
    for e in t.errors.toList.take 8 do IO.println s!"  {e}"
    if cutCount > 0 || ccut.failing > 0 then
      IO.println (s!"C-CUT cuts: {ccut.failing} of {cutCount} CUT lines (and PHYSCUT lines) fail" ++
        (if ccut.byName.isEmpty then "" else s!" ({", ".intercalate (ccut.byName.map (fun p => s!"{p.1} {p.2}"))})"))
      for e in ccut.examples do IO.println s!"  {e}"
    diag.show "diagnostics" total
    let failed := (if ca.failing > 0 then ["C-A"] else []) ++ (if cs.failing > 0 then ["C-S"] else []) ++
      (if cv.failing > 0 then ["C-V"] else []) ++ (if probeFails.length > 0 then ["C-R"] else []) ++
      (if clt.failing > 0 then ["C-L"] else []) ++
      (if ccut.failing > 0 then ["C-CUT"] else []) ++
      (if t.errors.size > 0 then ["exporter"] else []) ++
      (if t.done != some (total - 1) then ["incomplete"] else [])
    if failed.isEmpty then
      IO.println "TRACECHECK OK"
      return 0
    else
      IO.println s!"TRACECHECK FAILED: {" ".intercalate failed}"
      return 1
