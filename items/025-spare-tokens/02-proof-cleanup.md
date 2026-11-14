# 025-02. The proofs' cleanup: one name per route, one top theorem

Created 2026-11-14 by Frans Lundberg. Status: running (the plan being
written).

The cleanup of the key tree's Lean proofs after the night of 13 to 14
November (024-12, section 1, the follow-ups; 006-24, section 5,
decision 7): one name for each route instead of its F2, F3 and F4
versions, one top theorem in place of `invGetScanOK_merges` and
`invGetScanOK_merges_flat`, and the stale Lean comments of 007-09, Q2.

Frans, 2026-11-14, 12:16: "cleanup will be the focus today. Don't start
yet." 12:53: the study 026-16 (simpler algorithms for the remaining
premises) in parallel with the cleanup. 13:00, to the plan (a planning
agent now, the provers tonight under the 92 % ceiling, then the timing
pass 026-15): "Yes, good. Go ahead."


# 1. The plan in short

Written 2026-11-14, 13:00 to 13:35, by coord-1114's planning agent, from main at `eb1a04a0`
(lean/ unchanged up to `4aed39df`). The provers carry it out in the evening of 14 November,
started by the coordinator; nothing lands on main before 14:30; they end by 22:00, and the
timing pass 026-15 then has F53.

- **Step 1, prune** (prover "prune", 14:35 to 18:00 at the latest): remove every declaration
  of lean/SIS/Tree that nothing uses: no root reaches it (the top theorem, the model, the
  checkers, every file outside SIS/Tree) and no plan for the open premises names it. This
  also removes the earlier top theorem `invGetScanOK_merges` and the superseded versions of
  each route. Measured: about 1,960 declarations and 90,000 lines go, 73 files.
- **Step 2, notes** (prover "notes", in parallel, 14:35 to 16:30): the stale comments of
  007-09, Q2 and 006-26, section 6.2: `bounded_startup`'s docstring, BoundCold.lean's and
  BoundColdDrop.lean's headers, Props.lean's `Small.lean`, and lean/README.md on the bounds
  and the top theorem.
- **Step 3, names** (prover "names", after step 1 lands, until 21:00): one name for each
  route: the F2, F3, F4 marks and the numbers of an assembly's versions go from the names
  that are left, and `invGetScanOK_merges_flat` becomes the one top theorem,
  `invGetScanOK_merges`, in LatestTop.lean. The name map is written.
- **Step 4, dups** (prover "dups", optional, after step 3 lands, until 21:00): theorems with
  the same statement under two names, one kept. Small: about 57 groups, 450 lines. The first
  thing cut.
- **Step 5, close** (prover "close", after step 3 lands, until 22:00): lean/README.md's tree
  part to the new names, stale names in lean/ comments, the tools and the name map into this
  item, the counts after, a clean build's time, level 2's Lean steps, a note in 024-12 and
  024-22.

The target: lean/SIS/Tree from 227,923 lines in 507 files to at most 140,000 lines in about
434 files (expected 137,500); lean/ from 296,684 to at most 210,000 lines; a full build
from 10.5 minutes to about 7. The premises stay 10, with their names and statements.


# 2. What does not change, and how it is checked

- **The trusted statements.** TP7, TP10 and TP11 (`InvPreserved`, `GetOK`, `ScanOK`,
  `LatestGetOK`, `LatestScanOK`), the model they speak of (Props.lean, Read.lean, Exec.lean,
  Spec.lean and the other model files that SIS.lean imports), the general model, and the
  statements of the theorems that 006-26 audits (T1, T2, T3, T4, `bounded_startup` and
  their like). Checked at every gate by Guard.lean's fingerprint (section 4): every constant
  of a module outside SIS/Tree, of the model's SIS/Tree modules (Val, Node, Exec, Read, Spec,
  Inv, Props, Bound, Top, MergeProps, DeadProps), and every definition that the audited
  theorems' statements use, through definitions' bodies, has the same name, the same type and
  (for a definition) the same body as at the base: 10,710 constants, compared line by line
  with base/guard-base.txt. A difference fails the gate.
- **The 10 premises.** Their names (d4, l4, hchk, htb, hU, hHL, hMSF, hCoF, hCoU, hMF) and
  their statements stay; the definitions in their statements keep their names, also
  `OpDelChk2OK`, whose "2" is a version mark (two reports for Frans cite it). Checked at
  every gate: the top theorem's statement, printed, and its binders' names equal the base's
  `invGetScanOK_merges_flat` (`p hp hth hchk htb d4 l4 hU hHL hMSF hCoF hCoU hMF`), and the
  fingerprint covers the definitions. No premise changes name or form, so the name map has
  no premise in it.
- **What is proved.** Nothing is weakened: every audited theorem keeps its statement and
  stays on Lean's standard axioms. Removed declarations are those no kept one uses, so no
  proof of a kept theorem loses a step.
- **Kept although unused** (prune.py's rules, section 4): the building blocks that the open
  premises' plans name (keep.txt: d4's and l4's step lemmas, TP32's and TP33's counts, the
  heights for `htb`, `UpUnlinkOK` for `hU`, `checkPathFree` for `hchk`); F1's building
  blocks (026-16, section 4.2: `segFits_of_seenHeight`, `SeenHeightBound`, `ht_merge`); the
  refutations and examples (006-26, section 6.3: every file named for a counterexample or an
  example, every name with `not_` or `counterexample`); every `@[simp]` lemma; every name in
  the text between declarations (attribute lines, macros, `#guard`); a file that defines a
  macro or notation.
- **F1, if Frans takes it** (026-16, section 4.2, not decided, not a step here): it would go
  as a new theorem beside the top one in LatestTop.lean, with NoOutside in place of `htb`,
  `hMSF` and `hCoF`, on HeightsUnder.lean's `txSegFitsOK_of_takeBelowDelR2U` route and
  HeightsFuel.lean's `segFits_of_seenHeight`; the cleanup keeps all of these, and step 3
  does not rename them (they carry no F-mark).


# 3. Measured before, and the target

At `eb1a04a0` (lines of .lean files, by tools/lines.sh):

- lean/SIS/Tree: 507 files, 227,923 lines; 7,246 declarations, of which 4,567 are reached
  from the roots.
- lean/SIS/Proof: 108 files, 50,364 lines.
- lean/SIS's own files: 51 files, 9,222 lines.
- lean/BergDB: 11 files, 5,220 lines. lean/Check: 8 files, 2,413 lines. The programs at the
  top: 9 files, 1,542 lines.
- All: 694 files, 296,684 lines; lean/README.md 1,306 lines.
- A full build (737 jobs) from the main tree's older cache: 10 minutes 30 seconds, 3,520 s
  of CPU (580 %), in the plan clone at 13:02; last night's checks took 9.7 to 10.5 minutes.

Expected after (prune.py's report, applied to a copy of the sources at 13:23; not built):

- Step 1: lean/SIS/Tree 137,550 lines in 434 files; 1,961 declarations removed (73 files
  whole). The build's CPU time about 2,100 s instead of 3,300 s for the same modules
  (by the modules' build times, weighted by the lines left).
- Step 3: about the same lines; about 70 names and 7 files renamed.
- Step 4: about 450 lines less.
- The other areas: unchanged but comments.

Target, checked by step 5 (lines.sh and one clean build) and written in section 13:
lean/SIS/Tree at most 140,000 lines, lean/ at most 210,000, the build at most 8 minutes on a quiet
F53. Each step's gate prints the counts, so the progress is visible in each gate's summary.

Not a target tonight, a follow-up for spare tokens: the delete's two walks (one for what a
get reads, `kd_`, `_delF`; one for the take-back, `kr_`, `_j`) are near copies with
different statements; joining them is a refactor of the proofs, not a cleanup.


# 4. The tools

In /Users/f/fl/bench/2026-11-14/cleanup/tools/, written and tried by the planning agent on
the plan clone (/Users/f/fl/bench/2026-11-14/cleanup/plan-clone, built at `eb1a04a0`).
Step 5 copies them into items/025-spare-tokens/02-proof-cleanup/.

- **Reach.lean** (run with `lake env lean`, 30 s): every declaration of SIS/Tree with its
  lines, whether a root reaches it through proof terms and definitions, and what it uses.
  Roots: every constant of a module outside SIS/Tree, and roots.txt (the top theorem,
  `mergeParamsOK_java`, `theta_java`). A matcher or auxiliary proof that a kept declaration
  uses keeps its owner (the shared-matcher gotcha). Its output for the base is
  reach-decls.tsv.
- **prune.py**: adds the uses that terms do not show (names in a kept declaration's source
  text, comments stripped: rfl simp lemmas, `simp only`, `unfold`), the kept-although-unused
  rules of section 2, and keep.txt; cuts what is left, with a `set_option ... in` before it;
  removes a file left without declarations and replaces each `import` of it by its own
  imports. Report: prune-report.txt (FILE, TOTAL, GONE and DEAD lines).
- **keep.txt** (46 names) and **superseded.txt** (41 cited names that are earlier versions,
  each with its successor; 37 of them go, 4 stay as kept declarations still use them).
- **Guard.lean** (30 s): no `axiom` of ours and no `sorryAx` in any constant of ours; the
  axioms of every theorem in audit.txt (006-26's 23, the earlier top theorem left out); the
  trusted closure's fingerprint; the audited theorems' statements and binders' names. Its
  output for the base is /Users/f/fl/bench/2026-11-14/cleanup/base/guard-base.txt.
- **gate.sh CLONE OUTDIR [TOP]**: one heavy slot; `lake build` (all default targets) and
  `lake build treetest`; no sorry, admit, axiom, native_decide, implemented_by or extern in
  lean/; Guard.lean, with the fingerprint and the top theorem's statement and premises'
  names compared with the base; test-traces/run.sh (the trace checker's 41 tests); every
  SIS/Tree module imported; the line counts. Ends with GATE PASS or GATE FAIL. Tried on the
  plan clone: GATE PASS in 1 minute 48 with a built tree.
- **land.sh CLONE GATEOUT STEP**: section 7.
- **rename.py TABLE [--apply]**: whole-identifier renames over lean/ and lean/README.md, and
  file renames with their imports (git mv); refuses a clash with any identifier.
- **names.py**: writes the name map from prune's report, superseded.txt and step 3's table,
  for every name that an item cites (212 entries before step 3).
- **Dups.lean**: groups of theorems with the same statement (93 groups at the base, 57 left
  after the prune).
- **lines.sh**: lines and files per area.


# 5. The steps

## 5.1 Step 1, prune

- **What.** From the clone's lean/: `python3 $T/prune.py $T/reach-decls.tsv --keep
  KEEP --apply` with KEEP the prover's copy of keep.txt; `lake build`; for an error that a
  removed declaration causes, add its name to KEEP with a reason, restore the sources
  (`git checkout -- . && git clean -fdq SIS`) and apply again; a fix by hand (an attribute
  line, an `include`) only after the last apply, each listed in the State note. Then the
  gate, a commit, the landing.
- **Rule for doubt.** Keep, never remove by hand: a name is removed only by prune.py. A name
  the prover keeps beyond keep.txt goes in its KEEP file with one line of reason.
- **Done when** the gate passes on the pruned tree and it has landed; READY.
- **Size.** 1.5 to 3 hours: an apply takes seconds, each build round 7 to 10 minutes.

## 5.2 Step 2, notes

- **What.** Comments only, in: SIS/BoundStartupTheorems.lean (`bounded_startup`'s docstring:
  F grows with H, the logarithm of the keys, and Q and Hp are not known to be bounded with
  age; D's nodes reach nodes on the access paths of the last Hp + 1 sections, through
  pointers, as the theorem says); SIS/BoundCold.lean's header (rule 4 reads headers for a
  top node's pointers, the Pt term; Java parses every version, repeats included);
  SIS/BoundColdDrop.lean's header (`DropStep` is false for Java: one delete bitmap removes
  several children, the upward delete unlinks a parent with its children; replaced by
  `DropStepJ`, BoundColdDropJ.lean); SIS/Tree/Props.lean (the mention of `Small.lean`, which
  does not exist); lean/README.md (the bounds paragraph names `DropStepJ`, `lazyReads`,
  `RecordGdBound`, `T3_takeB`, `bounded_startup`; "Not done" no longer calls `DropStep`
  unchecked nor T3 without its record limit; the tree's properties are proved up to the top
  theorem's 10 premises, 024-12, section 1). Each text says only what the Lean states.
- **Q2 of 007-09.** This is its option B (comments fixed, no definition changed), done as
  part of 025-02, which Frans started at 13:00; option C (removing `DropStep` and its
  theorems) is not done. The State note says so, for Frans to overturn.
- **Names.** It uses the names as of the base (`invGetScanOK_merges_flat`); step 5 brings
  README to step 3's names.
- **Done when** the gate passes (an empty fingerprint difference shows that only comments
  changed) and it has landed; READY.
- **Size.** About 1 hour.

## 5.3 Step 3, names

- **What is renamed.** In the names left after step 1 (about 70 declarations, 7 files):
  - the marks F2, F3, F4 (`DelStepsOKF3` → `DelStepsOK`, `writerWP_mergeUp_delF3` →
    `writerWP_mergeUp_del`, `writerWP_handleFull_lastVF2` → `writerWP_handleFull_lastV`), with
    a letter glued after the mark only when it names the version, not what the variant adds;
  - the numbers of an assembly's versions (`delStepsOKF3_of_open16` → `delStepsOK_of_open`,
    `delStepsJ2OKF3_of_openR11` → `delStepsJ2OK_of_openR`, `delStepsQdL_of_openR4` →
    `delStepsQdL_of_openR`);
  - `invGetScanOK_merges_flat` → `invGetScanOK_merges`, and LatestTopFlat.lean →
    LatestTop.lean, its header rewritten for one top theorem;
  - files with the marks: DelMergeCaseF3, DelStepsCascF3, DelStepsF3, TakeDelMergeF4,
    TakeDelStepsF4, TakeRunQF4 lose them when the name is free.
- **What is not renamed.** Letters that say what a variant adds (J and J2 the take-back's, R
  at the induction's runs, L with the live counts, U, H, HG, S): they carry meaning. The
  definitions in the trusted closure (`OpDelChk2OK` stays). The premises' binders.
- **Clashes.** A stripped name must be free: rename.py refuses a name that is already an
  identifier anywhere in lean/. Then the prover keeps the shortest free form that says what
  differs and writes the choice in its table with a comment. A name that an item used for an
  earlier, removed statement may be reused; the map marks it.
- **The name map.** names.py over the clone (items as at the base), the applied prune report,
  superseded.txt and the table, to items/025-spare-tokens/02-proof-cleanup/names.md, in the
  same commit. rename.py also changes the names in lean/ comments and README.
- **Done when** the gate passes with TOP `SIS.Tree.invGetScanOK_merges` and it has landed.
- **Size.** 2 to 2.5 hours.

## 5.4 Step 4, dups (optional)

- **What.** Dups.lean on the built clone; for each group of theorems with the same statement,
  keep the one in the module that the others' users import (the earliest in the import
  graph; if none, move it to the lowest common file), point the others' uses to it with
  rename.py's table (old → kept), remove the copies; the map gets the rows of cited names.
- **Started** by the coordinator only if the week is below the start's level plus 8 points
  when step 3 lands (section 9). Time-boxed to 1.5 hours; it lands what passes.

## 5.5 Step 5, close

- **What.**
  - lean/README.md: every SIS/Tree file name and every Lean name in it exists after steps 1
    and 3 (a script lists the backquoted names and file paths that do not); the tree's
    section names the one top theorem and its 10 premises; its counts updated.
  - Comments in lean/ that name a removed declaration (names.md, sections 2 and 3): fixed.
  - The tools, keep.txt, superseded.txt, step 3's table and the applied prune report into
    items/025-spare-tokens/02-proof-cleanup/; names.md regenerated after step 4.
  - This file: section 13 with the counts after (lines.sh), one clean build's time (a copy of
    the clone with lean/.lake/build removed, `time lake build`, one slot), the gates' paths,
    what was kept and why; Status.
  - 024-12, section 1, and 024-22, section 11.1: one dated line each: "Names since 025-02
    (2026-11-14): 025-02's name map."
  - The last gate: gate.sh, then `sh java/stress/level2.sh` in the clone (its steps 7 and 8
    are the Lean steps: `lake build`, treeconf.sh and conformance.sh, about 15 minutes and
    one slot), its log path in section 13. level3.sh's Lean step is the same `lake build`
    and tracecheck; it runs in the next night.sh.
- **Size.** 1.5 hours, the text in parallel with step 4, the last gate after it.


# 6. Provers, order and times

- **Provers:** five runs, on Opus 5.5 at xhigh, background subagents of the coordinator, at
  most two at once: prune and notes (from 14:35), then names (from step 1's landing, about
  17:00), then dups and close (from step 3's landing, about 19:30).
- **Order:** 1 and 2 in parallel (their files are disjoint: step 1 changes SIS/Tree's proof
  files, MergeProofBundle.lean and other imports; step 2 SIS's own files, Props.lean's
  comment and README); 3 after 1 (it renames what 1 leaves); 4 and 5 after 3; 5's last gate
  after 4 lands or is dropped.
- **End times** (each prover's own, checked with `date`): prune 18:00, notes 16:30, names
  21:00, dups 21:00, close 22:00. If prune lands late, names starts late and the rest moves;
  no end time moves past 22:00.
- **Clones:** /Users/f/fl/bench/2026-11-14/cleanup/NAME/clone, branch `025-02-NAME`, cloned
  from the main tree when the prover starts; lean/.lake copied with `cp -Rc` from the plan
  clone (prune, notes) or from the clone of the step that landed last (names, dups, close),
  so the first build only rebuilds what changed.
- **Markers:** /Users/f/fl/bench/2026-11-14/cleanup/NAME/READY when the step has landed (one
  line: step, landed commit, gate directory), or NAME/STOPPED when it ended without landing
  (one line: why, the branch's head). NAME/STATE.md is the State note: what was done, the
  numbers, every decision taken by rule, what is left. Then a message to the coordinator.


# 7. The gate and the landing

- **Gate.** Every commit that lands passes gate.sh on the clone, with nothing uncommitted in
  lean/: a full build of the default targets and treetest, the forbidden words, the axiom
  audit of 23 theorems and of every constant of ours (no sorryAx, no axiom), the trusted
  closure's fingerprint, the top theorem's statement and premises' names, the trace
  checker's tests, the import graph, the counts. This keeps last night's rule (a full build
  and an axiom audit before every push) and adds the statements' check.
- **Who lands.** Each prover lands its own step with land.sh, after its gate passes, as last
  night's provers did; then it tells the coordinator ("LANDED step commit"). land.sh:
  - refuses before 14:30 on 14 November (006-26 is written in the main tree until about
    14:15; 026-16 reads its snapshot at `7ced25db` in its own clone and is not disturbed);
  - refuses while STOP exists, unless the coordinator runs it with `STOPOK=1`;
  - lands only the gated commit, or one that adds only a merge of main without lean/
    changes after it;
  - fast-forwards the main tree's main (it refuses if main moved: the prover then merges
    main with `git pull --no-rebase origin main` and gates again if that brought lean/
    changes) and pushes it to origin;
  - refuses a commit message with an AI's name; logs to cleanup/landed.log.
- **What a cleanup commit touches:** lean/ and items/025-spare-tokens/02-proof-cleanup*;
  step 5 also one line each in 024-12 and 024-22. So a fast-forward never meets another
  session's uncommitted edits in the main tree (006-26, the coordinator's day file).
- **Commits:** in Frans's name, message "025-02: ..." in plain words, no AI attribution.
- **The coordinator** commits this plan before the start; after that it leaves this file
  alone until "close" has landed (close writes section 13 here), and keeps its own notes in
  its day file (006-25). It may land a gated step itself (land.sh, `STOPOK=1` after STOP)
  when a prover ended without landing.


# 8. How the provers stop

- **STOP file:** /Users/f/fl/bench/2026-11-14/cleanup/STOP. The coordinator creates it at
  22:00, at the usage limit (section 9), or when Frans says so. Each prover checks it, and
  its end time, before every build or gate and at least every 20 minutes.
- **On STOP or the end time:** no new build or gate; a build of its own still running is
  stopped (TaskStop on its background task); its slots released (`sh
  /Users/f/fl/bench/2026-11-11/slot.sh release DIR`); its work committed on its branch (not
  landed); STATE.md and STOPPED written; a message to the coordinator; the prover ends.
  After STOP a prover lands nothing; the coordinator may land a gated commit with
  `STOPOK=1 sh land.sh ...`. Before STOP, a gate that passed before the prover's end time
  may still land just after it.
- **The coordinator, then:** when every prover started tonight has READY or STOPPED, no
  `lake` or `lean` process runs (`ps -axo pid,etime,command | grep -E '[l]ake|bin/[l]ean'`),
  and every heavy slot is free, it starts the timing pass (026-15, section 8, with its END).


# 9. Usage

- **Budget:** 12 points of the week for the cleanup, within Frans's ceiling of 92 %
  (resets Monday 16 November, 22:00). The coordinator notes the week's level U0 when it
  starts the provers and creates STOP at U0 + 12 points or 91 %, whichever comes first.
- **Estimate**, from last night's rate (about 3.7 points an hour for three provers proving
  at once, so about 1.2 an hour each) and lighter work tonight (scripts and builds, with
  idle waits):
  - prune: 2.5 points (2.5 hours, much of it waiting on builds);
  - notes: 1 point;
  - names: 2.5 points;
  - dups: 1 point (optional);
  - close: 1.5 points;
  - the coordinator's check-ins and landings: 1.5 points.
- **In all** about 10 points, 9 without step 4: within the 12, with 2 to spare for a prune
  that needs more build rounds.
- **What to cut first:** step 4; then step 5's README pass to only the stale names and
  counts; then step 2's README part (its four Lean comments stay). Never cut: the gates,
  the name map for what has landed.


# 10. The name map

- **Where:** items/025-spare-tokens/02-proof-cleanup/names.md, written by step 3 with
  names.py and regenerated by step 5 (after step 4).
- **What:** every declaration of SIS/Tree that an item cites (in backquotes, at the base) and
  that the cleanup renamed or removed: renamed (old → new, with "the name of an earlier
  statement" where a name is reused), removed as an earlier version (with its successor's
  new name), removed as used by no root. Each with the items that cite it. About 212 entries
  from step 1 and 70 from step 3.
- **Readers:** 026-16 (names as of `7ced25db`; lean/ is the same at `eb1a04a0`) and 006-26
  (names as of this morning) translate through it; neither file is edited by the cleanup.


# 11. Rules for every prover

1. Read first: AGENTS.md; this file, sections 1 to 12, and your brief's section of 5; the
   gotchas of Lean without Mathlib
   (/Users/f/.claude/projects/-Users-f-fl-repos-bergdb/memory/lean-no-mathlib-gotchas.md).
2. Work only in your clone. Never write in the main tree, and never push, except through
   land.sh. Do not edit a shell script while it runs; copy a tool before you change it, and
   say so in your State note.
3. Every full `lake build` runs inside gate.sh or holds a slot (`S=$(sh
   /Users/f/fl/bench/2026-11-11/slot.sh take NAME "what")`, then `release $S`); single
   modules (`lake build SIS.Tree.X`, `lake env lean F`) need none. Run builds as background
   commands; never wait with `sleep` loops on `pgrep -f` of your own command line.
4. No statement changes: the gate's fingerprint and the top theorem's statement must equal
   the base's. Do not touch the trusted files but comments (step 2 only). No sorry, admit,
   axiom, native_decide, implemented_by, extern.
5. Commit in Frans's name, "025-02: ..." in plain words; no AI names anywhere in files or
   messages.
6. A choice the plan does not settle: decide by the plan's aims (smaller, clearer, nothing
   trusted changes), write it in STATE.md for Frans to overturn, go on. Do not wait for
   Frans or the coordinator.
7. Keep it simple (Frans, 2026-11-13: "KISS. Complexity and code size are costs too.").
8. Stop on STOP or your end time (section 8).


# 12. Risks

- **The prune's build rounds take longer than planned.** A use that neither terms nor text
  show (a rfl simp lemma without `@[simp]` in its range, an instance found by unification, a
  macro's expansion) breaks a proof. The loop always ends: each round keeps more. If step 1
  has not landed by 18:00, the prover writes STOPPED with what is left, and names starts from
  it the next time spare tokens come.
- **A false alarm of the fingerprint.** A trusted definition whose body uses a matcher of a
  removed declaration would change its body's name; Reach.lean keeps every owner of a used
  matcher, so this should not happen. If it does: add the owner to KEEP.
- **Renames that confuse a reader.** A name reused for a later statement (`DelStepsOK` for
  what was `DelStepsOKF3`); the map marks each reuse.
- **Main moves in lean/** (another session): land.sh refuses; merge main, gate again.
- **The timing pass starts late** if a prover overruns: the end times and STOP at 22:00
  bound it; 026-15's END stays Sunday 09:00.
- **Usage.** Step 4 first to cut; STOP at U0 + 12.
- **A stale heavy slot:** heavy2.lock was held from 02:55 by last night's "cost"; it was
  free at 13:28. A slot held by no running process blocks a gate; the coordinator frees it.


# 13. Result

(Step 5 writes the counts after, the build's time, the gates and what was kept.)


# 14. The briefs

The coordinator pastes each brief as the prover's prompt. Each prover is a background
subagent, Opus 5.5 at xhigh.

## 14.1 Brief for "prune" (step 1)

```
You are "prune", a prover of coord-1114 for BergDB's Lean proofs (repo
/Users/f/fl/repos/bergdb, Lean 4 without Mathlib). Your job: step 1 of 025-02, the
proofs' cleanup: remove every declaration of lean/SIS/Tree that nothing uses, with the
script prune.py, until lean/ builds and the gate passes; then land it.

Read first: AGENTS.md; items/025-spare-tokens/02-proof-cleanup.md (025-02), sections 1
to 12, and 5.1 closely; the Lean gotchas in
/Users/f/.claude/projects/-Users-f-fl-repos-bergdb/memory/lean-no-mathlib-gotchas.md.

Setup:
  C=/Users/f/fl/bench/2026-11-14/cleanup; T=$C/tools
  git clone -q /Users/f/fl/repos/bergdb $C/prune/clone; cd $C/prune/clone
  git checkout -q -b 025-02-prune
  git diff --stat eb1a04a0 HEAD -- lean   # must be empty: reach-decls.tsv is of eb1a04a0;
      # if not, build, then rerun Reach.lean (header of $T/Reach.lean) to a tsv of your own
  cp -Rc $C/plan-clone/lean/.lake lean/.lake
  cp $T/keep.txt $C/prune/keep.txt        # your KEEP file; add names, never remove

The loop (in lean/):
  1. python3 $T/prune.py $T/reach-decls.tsv --keep $C/prune/keep.txt \
       --report $C/prune/prune-report.txt --apply
  2. A full build, as a background command, with a slot:
       S=$(sh /Users/f/fl/bench/2026-11-11/slot.sh take prune "025-02 prune build")
       lake build > $C/prune/build-N.txt 2>&1; sh /Users/f/fl/bench/2026-11-11/slot.sh release $S
  3. For each error caused by a removed declaration (unknown identifier or constant, a
     simp that made no progress, an unknown tactic): add the removed name(s) to KEEP with
     a comment "# build-N: used by X", then restore (git checkout -- . && git clean -fdq SIS)
     and go to 1. Prefer KEEP over hand edits; fix by hand (an attribute line, an include,
     a stray set_option) only after the last apply, and list each fix in STATE.md.
  4. When the build passes: commit ("025-02: the prune: N declarations of lean/SIS/Tree
     that no root uses removed, M files; ..."), then the gate:
       sh $T/gate.sh $C/prune/clone $C/prune/gate-1
  5. On GATE PASS: from 14:30, sh $T/land.sh $C/prune/clone $C/prune/gate-1 prune.
     If main moved: git pull --no-rebase origin main; gate again if lean/ changed.

Expected (prune.py on a copy at 13:23): SIS/Tree 227,923 -> about 137,550 lines, 73 files
and about 1,960 declarations removed, among them the earlier top theorem
invGetScanOK_merges and LatestTop.lean. If you keep more than 60 names beyond keep.txt,
or end above 150,000 lines, say why in STATE.md. Never remove a name by hand; never
change a statement (the gate checks it); keep F1's names (keep.txt).

End: 18:00 (check date), or when $C/STOP exists: check both before each build and at
least every 20 minutes; then section 8 of 025-02 (no new build, release slots, commit on
your branch, STOPPED). When landed: write $C/prune/READY ("prune <commit> <gate dir>")
and $C/prune/STATE.md (counts, the names you added to KEEP and why, hand fixes, build
times), copy your KEEP and the applied prune-report.txt next to it, and SendMessage to
"main": "LANDED prune <commit>: <lines before -> after>".
Rules of 025-02, section 11 apply: clone only, slots, no statement change, commits in
Frans's name with no AI names, decide by rule and write it down, do not wait for anyone.
```

## 14.2 Brief for "notes" (step 2)

```
You are "notes", an agent of coord-1114 for BergDB's Lean model (repo
/Users/f/fl/repos/bergdb). Your job: step 2 of 025-02: fix stale comments in lean/,
comments only, no definition or statement changed; then land it.

Read first: AGENTS.md; items/025-spare-tokens/02-proof-cleanup.md (025-02), sections 1
to 12, and 5.2 closely; items/007-bounds/09-t4-in-lean.md, Q2 and section 2;
items/007-bounds/09-t4-in-lean/second-review.md; items/006-2026-q4/26-proofs-status.md,
sections 3.4, 3.5 and 6.2.

Setup:
  C=/Users/f/fl/bench/2026-11-14/cleanup; T=$C/tools
  git clone -q /Users/f/fl/repos/bergdb $C/notes/clone; cd $C/notes/clone
  git checkout -q -b 025-02-notes; cp -Rc $C/plan-clone/lean/.lake lean/.lake

The comments (read each theorem's statement before you write; say only what it states):
  1. lean/SIS/BoundStartupTheorems.lean, bounded_startup's docstring: not "F does not grow
     with the database's size or its age": H grows with the logarithm of the keys, Q and
     Hp are not known to be bounded with age (007-09, Q4); and D's nodes reach, through
     pointers, nodes on the access paths of the last Hp + 1 sections (not "holds only").
  2. lean/SIS/BoundCold.lean's header: rule 4 reads headers for a top node's pointers (the
     Pt term); Java parses every version, repeats included; not "rule 4 reads nothing".
  3. lean/SIS/BoundColdDrop.lean's header: DropStep is not BergDB's: false for Java (one
     delete bitmap removes several children; the upward delete unlinks a parent with its
     children); it is replaced by DropStepJ (BoundColdDropJ.lean); the old definition and
     theorems stay, true of the model (007-09, Q2, option B).
  4. lean/SIS/Tree/Props.lean: the mention of Small.lean, a file that does not exist
     (a comment in a trusted file: change the comment only).
  5. lean/README.md: the bounds paragraph names DropStepJ, lazyReads, RecordGdBound,
     T3_takeB and bounded_startup; "Not done" no longer calls DropStep unchecked nor T3
     without its record limit; the tree's properties: proved up to the top theorem
     invGetScanOK_merges_flat and its 10 named premises (024-12, section 1), not "without
     proofs". Use the names as they are now; step 5 renames.
In Lean comments cite documents as "bergdb 007-09, section N".

Then: commit ("025-02: stale comments of 007-09, Q2 (option B) and 006-26, 6.2 ..."),
  sh $T/gate.sh $C/notes/clone $C/notes/gate-1     # fp-diff must be empty
and from 14:30: sh $T/land.sh $C/notes/clone $C/notes/gate-1 notes. If main moved (step 1
may land first): git pull --no-rebase origin main; gate again (lean/ changed); land.

End: 16:30, or when $C/STOP exists (check before each gate and every 20 minutes); then
025-02, section 8. When landed: $C/notes/READY ("notes <commit> <gate dir>"),
$C/notes/STATE.md (what each comment now says, and: "007-09 Q2: option B applied as part
of 025-02; option C not done; for Frans to overturn"), SendMessage to "main":
"LANDED notes <commit>". Rules of 025-02, section 11 apply.
```

## 14.3 Brief for "names" (step 3)

```
You are "names", a prover of coord-1114 for BergDB's Lean proofs (repo
/Users/f/fl/repos/bergdb, Lean 4 without Mathlib). Your job: step 3 of 025-02: one name
for each route, one top theorem, and the name map; then land it.

Read first: AGENTS.md; items/025-spare-tokens/02-proof-cleanup.md (025-02), sections 1
to 12, and 5.3 closely; /Users/f/fl/bench/2026-11-14/cleanup/prune/STATE.md; the Lean
gotchas in /Users/f/.claude/projects/-Users-f-fl-repos-bergdb/memory/lean-no-mathlib-gotchas.md.

Setup (step 1 has landed):
  C=/Users/f/fl/bench/2026-11-14/cleanup; T=$C/tools
  git clone -q /Users/f/fl/repos/bergdb $C/names/clone; cd $C/names/clone
  git checkout -q -b 025-02-names; cp -Rc $C/prune/clone/lean/.lake lean/.lake

The table ($C/names/renames.txt, rename.py's format):
  1. List the declarations of lean/SIS/Tree that are left (grep, or Reach.lean after a
     build) with a version mark: F2, F3, F4 in the name; the number of an assembly's
     version (_of_open16, _of_openR11, _of_openR4); _flat. Also the files with F2 to F4 or
     Flat in their names.
  2. For each, the new name without the mark (and the letters glued to the mark that only
     name the version). Keep letters that say what a variant adds: J, J2 (the take-back),
     R, L, U, H, HG, S. Never rename OpDelChk2OK or any other definition in the premises'
     statements, nor the premises' binders.
  3. Rows: invGetScanOK_merges_flat -> invGetScanOK_merges; FILE
     SIS/Tree/LatestTopFlat.lean SIS/Tree/LatestTop.lean; the other files as their marks go.
  4. python3 $T/rename.py $C/names/renames.txt (dry run, in lean/). It counts comments
     too: first rewrite LatestTopFlat.lean's header for one top theorem (no "flat", no
     "earlier form": it names invGetScanOK_merges), and any comment that names a removed
     declaration whose name you reuse. On another clash, choose the shortest free form
     that says what differs, with a comment in the table.
Then: python3 $T/rename.py $C/names/renames.txt --apply; a full build with a slot
(background); fix; then the name map:
  mkdir -p ../items/025-spare-tokens/02-proof-cleanup
  python3 $T/names.py $C/names/clone $C/prune/prune-report.txt $T/superseded.txt \
    $C/names/renames.txt > ../items/025-spare-tokens/02-proof-cleanup/names.md
Commit ("025-02: one name for each route ..., one top theorem invGetScanOK_merges; the name
map"), then:
  sh $T/gate.sh $C/names/clone $C/names/gate-1 SIS.Tree.invGetScanOK_merges
and land: sh $T/land.sh $C/names/clone $C/names/gate-1 names (merge main and gate again
if main moved in lean/).

Expected: about 70 declarations and 7 files renamed; the lines about the same. F1's names
(txSegFitsOK_of_takeBelowDelR2U, segFits_of_seenHeight) carry no F-mark and stay.

End: 21:00, or when $C/STOP exists (check before each build and every 20 minutes); then
025-02, section 8. When landed: $C/names/READY, $C/names/STATE.md (the table's choices,
each clash and how you chose), SendMessage to "main": "LANDED names <commit>". Rules of
025-02, section 11 apply.
```

## 14.4 Brief for "dups" (step 4, optional)

```
You are "dups", a prover of coord-1114 for BergDB's Lean proofs (repo
/Users/f/fl/repos/bergdb, Lean 4 without Mathlib). Your job: step 4 of 025-02: theorems
with the same statement under two names; keep one, point the uses to it, remove the
copies; time-boxed to 1.5 hours; land what passes.

Read first: AGENTS.md; items/025-spare-tokens/02-proof-cleanup.md (025-02), sections 1
to 12, and 5.4; /Users/f/fl/bench/2026-11-14/cleanup/names/STATE.md.

Setup (step 3 has landed):
  C=/Users/f/fl/bench/2026-11-14/cleanup; T=$C/tools
  git clone -q /Users/f/fl/repos/bergdb $C/dups/clone; cd $C/dups/clone
  git checkout -q -b 025-02-dups; cp -Rc $C/names/clone/lean/.lake lean/.lake
  (in lean/) lake build with a slot if anything is stale, then
  DUPS_OUT=$C/dups/dups.txt lake env lean $T/Dups.lean

For each group (expect about 57, about 450 lines in the copies):
  - keep the member whose module the other members' users can import: the earliest in
    the import graph; a SIS/Proof or SIS theorem before a SIS/Tree one; if none fits,
    leave the group;
  - a row "copy kept" in $C/dups/renames.txt for each other member, then, after the
    copies' declarations are removed by hand, python3 $T/rename.py
    $C/dups/renames.txt --apply --join (in lean/); add an import where the build asks;
  - a group whose members are in files that do not import each other and whose kept
    member would need a new import cycle: leave it.
A full build with a slot; the gate:
  sh $T/gate.sh $C/dups/clone $C/dups/gate-1 SIS.Tree.invGetScanOK_merges
commit ("025-02: N duplicated lemmas joined ..."), land with
sh $T/land.sh $C/dups/clone $C/dups/gate-1 dups. Then tell "close" nothing: the
coordinator does.

End: 21:00 or 1.5 hours after your start, whichever first, or when $C/STOP exists; then
025-02, section 8. When landed: $C/dups/READY, $C/dups/STATE.md (the groups joined, those
left and why), $C/dups/renames.txt kept for the name map, SendMessage to "main": "LANDED
dups <commit>". Rules of 025-02, section 11 apply.
```

## 14.5 Brief for "close" (step 5)

```
You are "close", an agent of coord-1114 for BergDB's Lean model (repo
/Users/f/fl/repos/bergdb). Your job: step 5 of 025-02: bring lean/README.md and the
comments in lean/ to the cleanup's names, put the tools and the name map in the item,
measure the result, run the last gate with level 2's Lean steps, and land.

Read first: AGENTS.md; items/025-spare-tokens/02-proof-cleanup.md (025-02), all of it,
5.5 closely; the State notes in /Users/f/fl/bench/2026-11-14/cleanup/{prune,notes,names}/
STATE.md (and dups/ if it ran).

Setup (step 3 has landed; step 4 may be running):
  C=/Users/f/fl/bench/2026-11-14/cleanup; T=$C/tools
  git clone -q /Users/f/fl/repos/bergdb $C/close/clone; cd $C/close/clone
  git checkout -q -b 025-02-close; cp -Rc $C/names/clone/lean/.lake lean/.lake

Part A (now):
  1. lean/README.md: list every backquoted name and every SIS/Tree file path in it that no
     longer exists (a script over names.md and lean/); fix each; the tree's section names
     the one top theorem invGetScanOK_merges, its 10 premises (d4, l4, hchk, htb, hU, hHL,
     hMSF, hCoF, hCoU, hMF) and Java's parameters (mergeParamsOK_java, theta_java).
  2. Comments in lean/ that name a removed declaration (names.md, sections 2 and 3): fix.
  3. items/025-spare-tokens/02-proof-cleanup/: copy the tools of $T (Reach.lean,
     Guard.lean, Dups.lean, prune.py, rename.py, names.py, gate.sh, land.sh, lines.sh,
     keep.txt, superseded.txt, audit.txt), prune's KEEP and applied report, names'
     renames.txt; a short readme.md there: what each is.
  4. One line each, dated, in items/024-release-2026-5/12-tree-model.md, section 1, and
     22-merges-lean.md, section 11.1: "Names since 025-02 (2026-11-14): 025-02's name map."
Part B (when step 4 has landed, or the coordinator says it will not):
  5. git pull --no-rebase origin main; regenerate names.md with names.py (025-02, section
     5.3), adding dups' table if it ran.
  6. Counts: sh $T/lines.sh lean. One clean build's time: cp -Rc the clone to
     $C/close/cleanbuild, rm -rf its lean/.lake/build, then with a slot
     (cd lean && time lake build).
  7. 025-02, section 13: the counts before and after per area, the build's time, the
     target met or not, the gates' paths, what was kept and why (from the State notes),
     the decisions taken by rule; the Status line.
  8. Commit ("025-02: the close: ..."); sh $T/gate.sh $C/close/clone $C/close/gate-1
     SIS.Tree.invGetScanOK_merges; then, with a slot, sh java/stress/level2.sh in the
     clone (java/build.sh first if it asks), log path in section 13; land with
     sh $T/land.sh $C/close/clone $C/close/gate-1 close.

End: 22:00, or when $C/STOP exists (check before each build and every 20 minutes); then
025-02, section 8. When landed: $C/close/READY, $C/close/STATE.md, SendMessage to "main":
"LANDED close <commit>: lean/SIS/Tree <before> -> <after> lines, build <time>". Rules of
025-02, section 11 apply.
```


# 15. For the coordinator, to start

1. Commit this file (the plan changed nothing else in the main tree; 006-26 is another
   session's work in progress).
2. Check `git diff --stat eb1a04a0 HEAD -- lean` in the main tree is empty; if not, rebuild
   the plan clone at main and rerun Reach.lean and Guard.lean (their headers say how) to
   new reach-decls.tsv and base/guard-base.txt before the start.
3. Check that every heavy slot is free or held by a running process (heavy2.lock, held
   from 02:55 by last night's "cost", was free at 13:28).
4. Note the week's level U0; start "prune" and "notes" (14.1, 14.2) at 14:30 or soon after;
   "names" on prune's LANDED; "close" and, if the week is below U0 + 8, "dups" on names'
   LANDED.
5. Hourly check-ins: the markers, landed.log, the week; STOP at 22:00 or U0 + 12 or 91 %.
6. When all have READY or STOPPED and nothing runs: the timing pass (026-15, section 8);
   a news entry with tools/news.sh (025-02 and the counts from close's message).
