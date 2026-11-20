/-
The trace checker: checks a trace of a Java run (java/stress/TraceExport.java)
against the model (bergdb 011-11, section 8.5; 027-02).

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
       VirtInit and VirtStep (R1 to R4, dead top nodes); and those of stage 2
       (`EvictRunOK`, SIS/Phys.lean; since bergdb 005-04, before diagnostics):
       TREE and A6' after every transaction, R(0) included, and A-COPY for
       each change. A6' allows adoptions below the old parent, which A6, the
       stronger form, does not; they are counted, not a failure
  C-S  the model's step from Java's state before T(i), with Java's startup pos,
       gives Java's record R(i) and D (gd and the versions compared as sets)
  C-V  the LIVE lines: Java's live children equal the instance's `live`
  C-R  the PROBE lines of the exporter: restarts, lookups, stream identity
  C-L  the FIRST lines (trace format 2; bergdb item 001, WP L5): every first
       touch after a restart follows the rule of SIS/Phys.lean (Rule R, the
       node table, the version read, cut back to the startup time)
  C-L4 a diagnostic, not part of the verdict (bergdb item 001, WP R8, change
       3): the FIRST lines against the Level 4 loader of the design before
       handles (`Mem.follow4`, SIS/Evict.lean until bergdb 005-62): no
       snapshot from the node table
  C-CUT with reclaim (bergdb item 001, WP R7): CutOK (SIS/Reclaim.lean) at every
       CUT line, in the model's state after its transaction, and the CUT's
       first available time is the record's; the physical cut (PHYSCUT) is at
       or below the decided one. Since WP R6, part 2 covers the versions that
       a physical read may follow (ReadsPhys; before, the diagnostic C-CUT+),
       but for the versions of D that Rule A put back. Since bergdb 024-07
       also CUT-live, T-COVER's second premise (`liveBelowFailures`): every
       index node reachable at the first available time has a data node
       below it then (BergDB's delete unlinks the nodes it empties; no touch
       of a key range writes an empty node again). Since bergdb 030-23 also
       reclaim's contract RC (030-22): RC1-order, the cut at or after the
       earlier ones; RC2-rewrites, every data node reachable at the first
       available time with its version at the cut or later; RC4-waits, the
       startup pos of R(i) after v, the first record whose startup pos
       reached the first available time (Java's two waits); RC3 is CUT-live
  C-STEP with STEP lines (trace format 3 with the exporter's steps=1; bergdb 030-27):
       Java's steps of reclaim are the model's steps of bergdb 030-25 (`StepsOK`), on
       the tree model's reads: per STEP line, at the step's state, L is the L' of the
       iteration's step before (none for its first), c <= t0 + 1, L' is L or a key of
       the range (the live keys after L up to E, the greatest key live after T(t0)),
       with eod the range's last, the step puts every KV of the range up to L' whose
       value node was made before c, and its operations have distinct keys and a put
       (STEP-chain, STEP-c, STEP-range, STEP-puts, STEP-ops); a STEP line in every
       record with a TOUCH line and in no other (STEP-line); and per CUT line, the
       iteration with its c has its last step, with eod, at the CUT's first available
       time (CUT-steps). Since bergdb 030-31, at each restart of run A (RESTART, after
       a stop or a crash), the RESUME line: the row that the start read is the
       iteration's row as its last step left it (the same c, lastKey its L', not
       ended), or a new iteration's without a step (lastKey none), with E the
       greatest key live after T(t0); and the first step after the restart goes on
       from that row (STEP-resume)
  C-P  with run E's SLOT lines (bergdb item 001, WP J4): INV-SLOT on Java's
       physical states (`slotFailures`; INV-SLOT of the design before handles,
       SIS/EvictExample.lean's `invSlotB`, which `TC_records` proved, until
       bergdb 005-62): every slot of a resident canonical object of a
       node current at i or in D names the pointee's latest version, or, for a
       pointee in D, is a memory slot to its canonical object or belongs to a
       node of D that got dirty no later; the object has a slot for every
       pointee of its history
  C-H  with run E's handle state (HMEM, HTABLE, HANDLE, HOBJ and HPTR lines;
       bergdb item 009, step 4c): the model's invariants with handles
       (SIS/HandleTheorems.lean; `handleFailures`) on Java's states, as the
       model's memory with handles (`toHMem`): the table and the handles
       (HTableOK), the canonical objects and D (HCanOK, by position, number of
       entries and the history's hash), the snapshots (HSnapOK, the same), the
       record rule for the pointers of canonical objects of nodes current at i
       or in D, computed by the model's `HMem.refOf` (HSlotOK), the snapshots
       against Rule R (HRuleROK), live
       handles without a written position (HLiveWrittenOK), written positions
       and references that name versions (HWrittenOK), the fast path's test
       (HFastOK), the unpinned objects written (T-PIN); no handle loading, and
       a dead handle never live again
With reclaim, also: C-A checks TouchOK (`StepOK.touchIndex`, `touchReach`,
`touchUp`) for the TOUCH lines, and the bound of the touch (`touchPath`,
`TouchOnPaths`: every touched node is on a path of the step's own change;
bergdb 024-07); C-S compares fa(i) (FA lines; the model clamps
Java's value, `firstAvail`), and from a CUT on runs the model's step on the
stream cut there (`cutStream`: version stubs before the cut).
and in C-S, with SKIPT lines, the top nodes' skip slots: the layout (slot j
of the top with ordinal n is populated exactly when bit j of n is set, and
names the formula's target) and the cached times (the target's creation)
and the exporter's ERROR lines. Diagnostics: D closed upward; and with --inv,
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
    let text ← IO.FS.readFile file
    -- RESTART and RESUME lines (bergdb 030-31) are read by Check/Tree.lean only: the trace
    -- parser of Check/Trace.lean is pinned (lean/contract/statements.pin), and a restart
    -- changes nothing that its checks read.
    let t := parseTrace ("\n".intercalate ((text.splitOn "\n").filter (fun l =>
      !(l.startsWith "RESTART " || l.startsWith "RESUME "))))
    IO.println s!"TRACECHECK {file}"
    IO.println s!"CONFIG {t.config}"
    IO.println s!"options: step3 {if o.mark then "mark" else "exact"}, step7 {if o.java7 then "java" else "exact"}, root {if o.virtual then "virtual" else "model"}{if o.inv then ", INV-2" else ""}"
    if !t.bad.isEmpty then
      for b in t.bad.toList.take 10 do IO.println s!"PARSE {b}"
      IO.println "TRACECHECK FAILED: the trace could not be read"
      return 1
    let recs := t.recs
    -- C-STEP (bergdb 030-27): with STEP lines, Java's steps of reclaim, on the tree lines.
    let stepRep : Option StepReport := if t.stepLines == 0 then none
      else some (stepCheck t (SIS.Check.Tree.parseTree text))
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
    let mut cpt : Tally := {}
    let mut slotCount := 0
    let mut slotChecked := 0
    let mut cht : Tally := {}
    let mut hStates := 0
    let mut hHandles := 0
    let mut hObjs := 0
    let mut hPtrs := 0
    let mut hCounts : HCounts := {}
    -- The handles seen dead in run E's states so far (C-H: a dead handle is never live again).
    let mut deadSeen : Std.HashSet Nat := {}
    let mut diag : Tally := {}
    let mut ccut : Tally := {}
    let mut cutCount := 0
    -- RC (bergdb 030-23): CUT lines checked, the least margin sp(i) - v of RC4, and
    -- the CUT lines with a margin of 1.
    let mut rcCount := 0
    let mut rcMargin := 0
    let mut rcTight := 0
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
    -- The transactions with an adoption below the old parent (A6' allows it, A6 not).
    let mut belowCount := 0
    let mut belowEx : Array String := #[]
    let mut firstCount := 0
    let mut firstFail := 0
    let mut first4Fail := 0
    let mut first4Ex : Array String := #[]
    let Sall := jrecs.toList
    -- R(0)
    let initF := initFailures sp
    -- The assumptions of stage 2 at time 0 (`EvictRunOK`'s EvictStep for j = 0).
    let rl0 := reachList sp p0 0
    let (a60, below0) := adoptFailures sp p0 0 (Std.HashSet.ofList rl0) rl0
    let tr0 := treeFailures sp p0 0 rl0
    ca := ca.add 0 (initF.map (fun n => (n, s!"{n} fails for R(0)")) ++
      (if tr0.isEmpty then [] else [("TREE", s!"TREE (one current parent) fails for nodes {showIds tr0}")]) ++
      (if a60.isEmpty then [] else [("A6'", s!"A6' (no adoption) fails for pointers {a60.take 8}")]))
    if !below0.isEmpty then
      belowCount := belowCount + 1
      belowEx := belowEx.push s!"T(0) adoptions below the old parent: {below0.take 8}"
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
      -- C-A, with the assumptions of stage 2: TREE and A6' after the transaction,
      -- A-COPY for its change (bergdb 005-04)
      let rlPrevSet := Std.HashSet.ofList rlPrev
      let sf := stepFailures sp P i c rlPrevSet rlNowSet rlNow ++
        touchFailures sp P i c rlPrev rlPrevSet rlNowSet
      let (a6', belowP) := adoptFailures sp P' i rlNowSet rlNow
      let tr := treeFailures sp P' i rlNow
      let cp := copyFailures sp P i c rlPrev rlNowSet
      ca := ca.add i (sf.map (fun p => (p.1, s!"{p.1} fails for nodes {showIds p.2}")) ++
        (if tr.isEmpty then [] else [("TREE", s!"TREE (one current parent) fails for nodes {showIds tr}")]) ++
        (if a6'.isEmpty then [] else [("A6'", s!"A6' (no adoption) fails for pointers {a6'.take 8}")]) ++
        (if cp.isEmpty then [] else [("A-COPY", s!"A-COPY fails for pointers {cp.take 8}")]))
      if !belowP.isEmpty then
        belowCount := belowCount + 1
        if belowEx.size < 8 then
          belowEx := belowEx.push s!"T({i}) adoptions below the old parent: {belowP.take 8}"
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
        -- T-COVER's second premise at the first available time (bergdb 024-07).
        let rlF := reachList sp P' f
        let live := liveBelowFailures sp P' f rlF
        let lf := if live.isEmpty then [] else
          [("CUT-live", s!"reachable at {f} without a data node below it: {showIds live}")]
        -- Reclaim's contract RC (bergdb 030-23): RC1's order of the cuts, RC2, RC4.
        let dataOld := rlF.eraseDups.filter (fun x => match P'.get? x with
          | some n => n.isData && (match m.get? x with
            | some (q, _) => decide (q < cc)
            | none => true)
          | none => false)
        let sps := (recs.toList.take (i + 1)).map (·.sp)
        let (rcf, v) := rcFailures cc f cutNow i sps dataOld
        rcCount := rcCount + 1
        match v with
        | some v =>
          let mg := r.sp - v
          rcMargin := if rcCount == 1 then mg else min rcMargin mg
          if mg == 1 then rcTight := rcTight + 1
        | none => pure ()
        ccut := ccut.add i (faFail ++ cf ++ lf ++ rcf)
        if cutNow < cc then
          for q in [cutNow:cc] do
            Sc := Sc.modify q Record.cut
          cutNow := cc
      | none => pure ()
      -- C-P
      let lvNow := lvMap
      let (pf, pn) := slotFailures sp P' rlNowSet r.dirty (fun y => (lvNow.get? y).map (·.1)) r.slots.toList
      slotCount := slotCount + r.slots.size
      slotChecked := slotChecked + pn
      cpt := cpt.add i (pf.map (fun m => ("slot", m)))
      -- C-H (bergdb item 009, step 4c): the stream that the state's startup read, R(0) to
      -- R(k), gives Rule R; the whole stream so far gives the versions.
      match r.hmem with
      | some (k, first) =>
        let g := SIS.Fast.nodeMap P'
        let verAt := fun (q : Nat) (y : NodeId) => (jrecs.getD q r0).vers.find? (·.node == y)
        let (hf, hc) := handleFailures sp (fun x => g[x]?) rlNowSet r.dirty
          (fun y => (lvNow.get? y).map (·.1)) verAt (jrecs.toList.take (k + 1)) first deadSeen r
        hStates := hStates + 1
        hHandles := hHandles + r.handles.size
        hObjs := hObjs + r.hobjs.size
        hPtrs := hPtrs + r.hptrs.size
        hCounts := hCounts.add hc
        cht := cht.add i hf
        deadSeen := r.handles.foldl (fun ds h => if h.state == "dead" then ds.insert h.num else ds) deadSeen
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
      -- diagnostics, one tally entry per transaction: D closed upward; INV-2 with
      -- --inv. Before bergdb 005-04 also A6, TREE and A-COPY, now in C-A (A6' for A6).
      let cl := closedFailures sp P' i r.dirty
      let iv := if o.inv then inv2Failures sp (jrecs.toList.take (i + 1)) P' i r.dirty else []
      diag := diag.add i ((if cl.isEmpty then [] else [("closed", s!"D not closed upward at {showIds cl}")]) ++
        (if iv.isEmpty then [] else [("INV-2", s!"dirty index nodes not in D: {showIds iv}")]))
      P := P'
    let probes := recs.toList.flatMap (fun r => r.probes.toList)
    let probeFails := probes.filter (fun p => !p.2.1)
    let total := recs.size
    ca.show "C-A assumptions" total
    IO.println s!"C-A adoptions below the old parent (A6' allows them, A6 not; bergdb 005-04): {belowCount} of {total} transactions"
    for e in belowEx do IO.println s!"  {e}"
    cs.show "C-S steps" total
    IO.println s!"C-V live: {cv.failing} transactions with differences, {liveCount} LIVE lines"
    for e in cv.examples do IO.println s!"  {e}"
    IO.println s!"C-R probes: {probeFails.length} of {probes.length} fail"
    for p in probeFails.take 8 do IO.println s!"  PROBE {p.1}: {p.2.2}"
    IO.println s!"C-L first touches: {firstFail} of {firstCount} FIRST lines fail"
    for e in clt.examples do IO.println s!"  {e}"
    IO.println s!"C-L4 (a diagnostic, the Level 4 loader; WP R8, change 3): {first4Fail} of {firstCount} FIRST lines take a snapshot from the node table"
    for e in first4Ex do IO.println s!"  {e}"
    if slotCount > 0 || cpt.failing > 0 then
      IO.println s!"C-P slots (INV-SLOT on run E's states): {cpt.failing} of {total} transactions fail; {slotCount} SLOT lines, {slotChecked} checked (of objects current or in D)"
      for e in cpt.examples do IO.println s!"  {e}"
    if hStates > 0 || cht.failing > 0 then
      IO.println (s!"C-H handles (the model's invariants with handles on run E's states): {cht.failing} of {total} transactions fail; {hStates} states, {hHandles} handles, {hObjs} objects, {hCounts.hashed} histories compared, {hPtrs} pointers, {hCounts.checked} checked by the record rule" ++
        (if cht.byName.isEmpty then "" else s!" ({", ".intercalate (cht.byName.map (fun p => s!"{p.1} {p.2}"))})"))
      for e in cht.examples do IO.println s!"  {e}"
      IO.println (s!"C-H cases (SIS/HandleExample.lean's pointCounts): {hCounts.snaps} snapshots, {hCounts.snapsSection} of nodes in the startup section after a restart; " ++
        s!"{hCounts.ptrSnaps} pointers to snapshots, {hCounts.olderSnap} with a reference older than the section's (open point 1); " ++
        s!"{hCounts.written} pointers checked written with their handle's written position (choice 1), {hCounts.writtenVpos} with a vpos (open point 3)")
    IO.println s!"exporter errors: {t.errors.size}"
    for e in t.errors.toList.take 8 do IO.println s!"  {e}"
    if cutCount > 0 || ccut.failing > 0 then
      IO.println (s!"C-CUT cuts: {ccut.failing} of {cutCount} CUT lines (and PHYSCUT lines) fail" ++
        (if ccut.byName.isEmpty then "" else s!" ({", ".intercalate (ccut.byName.map (fun p => s!"{p.1} {p.2}"))})"))
      for e in ccut.examples do IO.println s!"  {e}"
      IO.println s!"C-CUT RC (bergdb 030-23): RC1 to RC4 at {rcCount} CUT lines (RC3 is CUT-live); RC4's least margin, the startup pos past v: {rcMargin}, CUT lines with a margin of 1: {rcTight}"
    let mut cstep : Tally := {}
    match stepRep with
    | some rep =>
      for (i, f) in rep.fails do cstep := cstep.add i f
      IO.println (s!"C-STEP reclaim's steps (bergdb 030-27): {cstep.failing} of {total} transactions fail" ++
        (if cstep.byName.isEmpty then "" else s!" ({", ".intercalate (cstep.byName.map (fun p => s!"{p.1} {p.2}"))})") ++
        s!"; {rep.steps} STEP lines, {rep.iterations} iterations ({rep.ended} ended by a step with eod), {rep.old} old KVs met and checked put again, {rep.cuts} CUT lines with their iteration's last step" ++
        (if rep.restarts == 0 then "" else
          s!"; {rep.restarts} restarts ({rep.crashes} crashes), {rep.resumed} with an iteration in progress, {rep.spans} iterations with a step before a restart and the next after it"))
      for e in cstep.examples do IO.println s!"  {e}"
    | none => pure ()
    diag.show "diagnostics" total
    let failed := (if ca.failing > 0 then ["C-A"] else []) ++ (if cs.failing > 0 then ["C-S"] else []) ++
      (if cv.failing > 0 then ["C-V"] else []) ++ (if probeFails.length > 0 then ["C-R"] else []) ++
      (if clt.failing > 0 then ["C-L"] else []) ++
      (if cpt.failing > 0 then ["C-P"] else []) ++
      (if cht.failing > 0 then ["C-H"] else []) ++
      (if ccut.failing > 0 then ["C-CUT"] else []) ++
      (if cstep.failing > 0 then ["C-STEP"] else []) ++
      (if t.errors.size > 0 then ["exporter"] else []) ++
      (if t.done != some (total - 1) then ["incomplete"] else [])
    if failed.isEmpty then
      IO.println "TRACECHECK OK"
      return 0
    else
      IO.println s!"TRACECHECK FAILED: {" ".intercalate failed}"
      return 1
