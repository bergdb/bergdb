030-proofs
==========

Created 2026-11-16 by Frans Lundberg. Status: open.

The home of BergDB's proof work: one map of every direction, with its
state, its next step and the decision it waits for, kept up to date by
the day's coordinator, and the rules that all proof work follows. The
proofs and their notes stay where the work is done (`lean/`, the items
the map names); this item says how they hang together.

Frans, 2026-11-16, 14:25: "I want all proof work to be synched somehow.
Now we have multiple directions. The main work should go on as well,
right? We don't know if we need to make any simplificaitons yet. Perhaps
the current model and Java will be proven if we continue with that work."
14:32: "About 030-proofs, good idea, set it up as suggested."


The aim
=======

**The core algorithms are proved** (Frans, 2026-11-18, 13:12): every
correctness claim reads "proved, given the tested assumptions" of 030-04,
section 3.5. Two parts are left for it: the writer meets the contract
(030-04's assumption 1; the direction is chosen after the PE trial,
026-24), and reclaim chooses only safe cuts (assumption 11, T-SCHEME).
Frans: ""the core algorithms are proved". Yes, this is the result to aim
for. This is how far we would wish to go. If maintenable at a reasonable
cost, this would be great. That is a valuable garantee." Beyond it, and
not aimed for: Java against the model (tested by design), the platform's
assumptions (tested), the cost and bounded-startup statements, and what
the model leaves out (threads, the Pub layer, the cache's budget).

**Reached (2026-11-19).** The writer's part by PE (030-21; Java's writer
is PE since 026-25), reclaim's part by 030-24 and 030-25, each given the
tested assumptions, which 030-26, section 5, lists as they now stand.
030-26 states the claim for publication, in the words Frans chose,
"BergDB's core algorithms are proved", with the model and its limits.

**From 2026-11-20 on** (Frans decided, 2026-11-20), with the scope
unchanged (the Core's algorithms; threads, the Pub layer, Java's code
itself and the costs stay outside):

1. **Keep it true.** 030-26 stays current with `main`; the proofs change
   with the code; the gate, the pins and the nightly checks run.
2. **Strengthen the tested links where a fault would hurt users most.**
   Wider testing of Java against the model: new trace seeds each day,
   each recorded so that a failure can be reproduced, and Java's commit
   check in week.sh on a subset that adds less than an hour (030-30);
   traces of the user apps' workloads and of reclaim's steps across
   restarts (030-31). Proofs of the bounds that keep a transaction within
   the record limit: `dirtyNodeBound` against PE, and the acceptance
   argument of 030-28, section 5 (030-29).
3. **The stream format of release 2026.8 designed model first** (032):
   the model and the proofs change with the format's design, not after it.

Not now: RC1 and RC4 in Lean (arithmetic, checked at every cut), a model
of threads, the cost and bounded-startup statements (D4, D5), the Pub
layer.

Before: a fully proved model: "We still try to prove everything now.
Once that work is done, I may decide on a general policy on this."
(Frans, 2026-11-15, 08:47.) The goals in order were 006-26, section 8;
what each word means (proved, reduced, tested) is 006-26's.


The rules
=========

Every direction follows these; a direction's item may add its own.

* **One gate.** A step lands only if the build passes with no `sorry`,
  no `admit`, no `native_decide`, no axiom of its own (the standard
  three only), and the trusted closure and the top theorems' statements
  are unchanged against the gate's base. The gate is a script of the
  day (such as `/Users/f/fl/bench/2026-11-15/day/gate-1115.sh`); the
  coordinator re-bases it on `main` when it starts a night.
* **Statements change only on Frans's word.** A premise is removed by
  proving it or by changing its consumer, not by restating it. A
  statement found false is reported with a counterexample in Lean.
* **Statements speak of reached states**, or carry the writer's books
  they need. On 15 November three premises were false as stated because
  they spoke of any state (006-26, the correction).
* **Only the coordinator lands** on `main`. A prover reports GATED with a
  commit; the coordinator merges, gates the combined tree and pushes.
* **Branches for trials.** Work that tries a changed algorithm (such as
  MT) stays on its own branch and never lands on `main`'s `lean/`
  unless Frans decides the change.
* **Each direction keeps its State note** in its item, so that a new
  agent can go on from it.
* **The coordinator updates this map** when a direction's state changes
  and at the end of its day (the "Days" section below).
* **030-26 stays true.** A change to a proof, to the tested assumptions
  or to the checks that cover them updates 030-26, the public statement,
  in the same change (Frans, 2026-11-20; at least until release 2026.6).


The map
=======

D0. The contract approach, a fresh start
----------------------------------------

* **Goal:** claims of the form "proved, given five stated assumptions,
  each of which is tested". The writer's contract says what holds when
  a transaction ends: the invariants, the old contents with the
  transaction's net change, only nodes in D changed. Proved from it:
  every get and scan right at every time, for any history of
  transactions that meet the contract; then recovery, restarts,
  eviction and reclaim's cut. That the writer meets the contract is
  tested, one transaction at a time, not proved (030-04, section 3).
* **State (2026-11-17, 11:26):** decided by Frans (10:56, 11:00, 11:14)
  and written down in 030-04; not started. The new proofs are written
  from scratch in a Lake package of their own, `lean/contract/`, with
  Mathlib (the coordinator's decision, delegated by Frans). The old
  Lean is a quarry; the executable model and the trace checkers stay as
  the test oracle.
* **Next:** the spike (030-04, section 7): one agent, about a day; Frans
  decides when. If it succeeds, 030-04's step 4 follows without asking.
* **The writer proof** (030-10, 030-16; every put proved, deletes in
  part) was taken off `main` on 2026-11-18 (Frans, 08:42; 030-18): it is
  at the tag `writer-proof-2026-11-18`. No proof nights for now (006-31,
  D4).
* **PE's writer proved** (030-21, 2026-11-19): PE (026-24) as total
  functions on the contract's tree, the trial's tree on all 288 traces;
  every history it writes from the empty tree meets `MeetsTop`
  (`Contract.PE.pe_meetsTop_start`) and `MeetsFull` (`pe_full`: recovery,
  restarts, eviction, cuts), the standard axioms only; and PE accepts every
  transaction but a put of a key the tree cannot hold, within named bounds
  of H and of the fuel (`pe_accepts`). Left for the writer's part of the
  aim: Java.
* **State (2026-11-19): the goal is reached.** PE's writer meets the
  contract (030-21) and Java's writer is PE (026-25, record format 8);
  reclaim's cuts are safe given RC1, RC4 and Java's steps (030-24,
  030-25). What stays tested is 030-26, section 5; 030-26 is the public
  statement of the claim.
* **Beyond the aim, the dirty-node bound** (030-29, 2026-11-20; Frans
  decided to prove it): Java's `Dag.dirtyNodeBound` modelled in Lean and
  proved to bound the key nodes PE writes, for transactions of puts, given
  the fill rules (`pe_dirtyNodeBound_puts`); with deletes tested, not
  proved (the joins one level down are open). And 030-28, section 5, in
  Lean: PE accepts every transaction Java admits at H = 126
  (`pe_accepts_java`).
* **What it changes here:** D1 is paused; D3's goal moves to 030-04's
  step 4. "The aim" above is as written on 16 November; D0's aim is its
  goal. The rules above hold for `lean/` as before; the new package's
  gate is 030-04, section 7.6.
* **Items:** 030-04.

D1. The key tree, today's model (the main line until 2026-11-17; paused)
------------------------------------------------------------------------

* **Deleted** from `main` on 2026-11-18 (Frans, 08:42, 006-31, D1;
  030-18): `lean/` keeps the executable model, the checkers, the test
  programs and the abstract model's proofs that `lean/contract/` imports.
  The old line is at the tag `proofs-2026-11-17` (f4d73289).
* **Paused** since 2026-11-17 (Frans, 09:13 and 11:14; 030-04). Frozen
  at the tag `proofs-2026-11-17` (f4d73289). The
  state and the next step below are as the night left them, for a
  restart.
* **Goal:** TP7, TP10 and TP11 proved for the key tree with Java's
  parameters and the merges on: after any run, the tree keeps its
  invariants and every get and scan, at the latest time and at every
  earlier one, returns what a plain map returns.
* **State (2026-11-17, 04:18):** `htbL` is PROVED
  (`takeBelowFuelDelSL_holds`, from `hp` only; 025-05, step 8). The best
  top theorem with no premise known false is `invGetScanOK_merges_noTb`
  (lean/SIS/Tree/HtbNoTb.lean): TP7, TP10 and TP11 for Java's parameters
  from `hp`, `hth` and `l4`. `l4` is in pieces by 030-01's route B: the
  night's top `invGetScanOK_merges_noL4Night` (LiveNightTop.lean) has
  four named premises, the merge's full parent's rest
  (`MergeTailRuns10`), R4 at the leaf and at the stop node, and
  `R3Calls`, which is believed false at unreached states, so that
  theorem is believed vacuous (030-01's log, 01:56 to 02:22). R3's plan
  is 030-03; R4's pieces are proved but the merge tail with the hole
  (030-01's log, 03:54, 04:13).
* **Next:** R3 by 030-03's route M0 to M5 (one night); R4's merge tail
  with the hole and its leaf and stop-node forms; then the close step
  (the vacuous lemmas, the `noL4` family, the superseded corollaries).
* **Items:** 024-12, section 1; 025-04; 025-05; 006-27, section 8.

D2. Simpler algorithms: MT and subtransactions
----------------------------------------------

* **Goal:** to know, with evidence, whether a simpler algorithm makes
  the proofs much smaller, before 2026.6's format is fixed (026-12,
  SF10); 2026.6's theme is "simpler algorithms" (026).
* **State (2026-11-16):**
  * 006-28: the study; where the proofs' complexity is; MT.
  * 026-17: MT's trial in the model, done: MT passes every check, one
    rule added (A1, the model's scan budget) for Frans to rule on.
  * 026-18: Frans's idea, main transactions as atomic sequences of
    subtransactions; readers see only the states between main
    transactions (A1 then not needed).
  * 026-19: the proof trial's plan; it runs from 2026-11-16, 22:05, on
    the branch `026-19-proof-trial`.
  * 026-19 done 2026-11-17, 00:55: gain not supported; 026-19's Result.
* **Next:** 026-19's result; then Frans decides MT, NW or neither, with
  SF10 (006-28, section 7.7).
* **Items:** 006-28; 026-17; 026-18; 026-19.

D3. The bridges to the abstract model
-------------------------------------

* **Goal:** TP14 (`RunOK`), TP16 (TREE, A6', A-COPY) and TP19 proved for
  the tree, so that recovery, restarts, lazy reading and eviction are
  proved for BergDB's tree, not only for any structure that meets the
  assumptions (006-26, sections 5.2 and 8, item 4).
* **State (2026-11-16, 22:30):** open, not started; tested on traces.
  The plan is 030-02: all three bridges rest on one bundle of D1's facts,
  so on `l4` and `htbL` only. Its finding, by reading, not built: TP14
  and TP19 are false as stated, since the model's writer has no guard at
  the top node ordinal 2^48, which Java has refused since 005-02; TP16
  holds. Frans's question 1 in 030-02 (default: prove the bounded forms
  as new statements now; add the guard to the model later).
* **Next:** 030-02's steps 0 to 3 when a prover is free and Frans agrees;
  steps 4 to 8 after D2's decision (with MT, 006-28 says the take-back
  drops out of these).

D4. Bounded startup's premises
------------------------------

* **Goal:** `bounded_startup`'s open premises (006-26, section 5.1).
* **State:** deferred by Frans (2026-11-13, 16:14). Q and Hp may grow
  with the database's age; nobody knows.
* **Next:** measure Q and Hp on Java's traces first (026-16, S1; 006-28,
  RT); then decide the statement.

D5. The rest
------------

* The costs (TP20 to TP33), the model's scope (026-14): open, not
  started; 006-26, sections 6 and 8. Reclaim's scheme (T-SCHEME): D6.
* Java against the model: tested only, by the trace checkers; it stays
  a test.

D6. Reclaim's safe cuts (T-SCHEME)
----------------------------------

* **Goal:** the second part of the aim: reclaim chooses only safe cuts,
  so that the reads after cuts (`full_cut`, `cut_java_reads`,
  `cut_keeps_top`) rest on tested, local conditions instead of `CutOK`
  (030-04, 3.5, assumption 11).
* **State (2026-11-19):** written down in 030-22: reclaim's contract RC,
  four conditions at each cut that a trace can test (the order, the
  rewrites at the iteration's end, a value below every index node, Java's
  two waits); RC gives `CutOK` is T-SCHEME in the model, half proved since
  024-07 (`T_latest`), the other half open (the older versions that reads
  at earlier times follow; an invariant on superseded versions); T-SCHEME
  with Java's exact waits held by running in the model. Not started in
  Lean.
* **State (2026-11-19, 030-23):** step 1 done. T-SCHEME stated in
  lean/contract (`TScheme`, with RC as `RC`); the theorems after cuts
  restated with RC in place of `CutOK` (`full_cut_rc`, `cut_keeps_top_rc`,
  `cut_java_reads_rc`); proved under RC: `CutOK`'s parts 1, 3 and 4 and
  part 2 for the latest versions (`rc_parts`; `rc_dref` for runs with A6'),
  so the open half is part 2 alone (`TSchemeReads`). RC checked at every
  CUT line by `tracecheck` (954 CUT lines of the reclaim traces, 0
  failures). The invariant that gives part 2, found by running: GIS-J
  (030-23, section 4), no failure in the model or on the traces; in Lean,
  with the proof that it gives part 2 (`reads_of_gis`), so what is open is
  that RC gives GIS-J's three clauses (`TSchemeGis`); of them proved: Lemma
  G (`rc_goodc`), clause (i) up to the startup pos, clause (ii)'s case 1;
  open: clause (ii)'s case 2 (a child made after e, seen only on Java's
  traces) and Rule A's chains.
* **State (2026-11-19, 030-24):** RC gives `CutOK`, proved, for runs with
  A6' (`cutOK_of_rc`): the read half by the independent search's read
  invariant (`old_reads_good`, `rc_part2`; `TSchemeReads` holds), so the
  theorems after cuts need only RC at each cut (`full_cut_of_rc`,
  `cut_keeps_top_of_rc`, `cut_java_reads_of_rc`; for PE
  `PE.pe_cut_java_reads`). `TScheme` as stated (RunOK alone) is false, in
  Lean (`AdoptionExample.tscheme_false`). RC3 and RC2 for the key tree
  proved (`rc3_tree`; `rc2_of_iteration` from `IterationOK`, the iteration
  in the contract's words, and VAL-NEW, which PE meets, `PE.pe_valNew`);
  so for every history PE writes, Java's reads after reclaim's cuts are
  right (`PE.pe_reclaim_reads`). **Reclaim's part of the aim is proved**,
  given the tested assumptions: RC1 and RC4 at each cut (Java's
  arithmetic) and `IterationOK` (Java's steps; its consequence RC2 is
  checked at every cut).
* **Next:** none needed for the aim; 030-24, section 5 lists options.
* **Items:** 030-22; 030-23; 030-24; 001-07, section 5; 024-07, section 4.

Where the contract's checks run
-------------------------------

The tested half of D0 (030-04, section 3), kept running as the code
changes (030-13):

* `java/before-commit.sh`, the commit gate: Java's own check of the
  contract (TransCheck) in the unit tests; no Lean.
* `java/stress/level2.sh`, step 8b: `lean/contract/check.sh` (the contract,
  with its fault tests) and `lean/contract/bridge-check.sh` (the bridge,
  with its fault test) on the small and drain tree sets that step 8 writes.
  Step 8c (030-28): `lean/pecmp/check.sh`, the tree checker's writer (the
  copy lean/SIS/Tree/Pe.lean, which step 8 compares with Java node for
  node) against the proved writer, on the small, drain and reclaim sets,
  with its own tests. Step 0 (030-28): `lean/contract/pins.sh`, the
  hashes of statements.pin (the statements, the copy, pecmp), no build.
* `java/night.sh`: `java/stress/transcheck.sh` (TransCheck in the unit and
  f-tests); level2.sh full; `java/stress/contractconf.sh medium`, the
  medium tree set (written without the tree model's check), the contract
  and the bridge; and `lean/pecmp/check.sh medium` on its traces (030-28,
  since 2026-11-20).
* By hand: `bridgecheck --model` and the large set.

How the directions hang together
--------------------------------

* D1 and D2 share today's reader proofs and the merge's lemmas: 026-19
  reuses them through a bridge.
* D1 lands additions on `main`; D2 works on branches. They do not touch
  the same files.
* If MT is decided, D1's `l4` and `htbL` change what they say; what D1
  has proved stays as the proof of today's model, the algorithm of
  2026.5 and of Java until MT ships.
* The next decision point: Tuesday 2026-11-17, morning. Side by side:
  `htbL` proved or how far it got, `l4`'s plan and size (030-01), and
  026-19's evidence. Frans decides the direction.
* Its outcome (2026-11-17, 09:13 to 11:14): D0; D1 paused (030-04).


Days
====

One line a day by the coordinator: what moved, where.

* 2026-11-16 (coord-1116): 006-28 written; MT's trial (026-17) done;
  026-18 written down; 026-19 planned; this map made. Provers paused
  since the morning (Frans, 10:29); the night from 22:05: 026-19 (two
  provers), `htbL`'s step 8 (one prover), `l4`'s plan (030-01).
* 2026-11-17 (coord-1116, the night): `htbL` proved; `l4` in pieces
  (about 60 landings, `lean/` 236k to 279k lines); 026-19 done (MT not
  supported nor refuted as a proof saving); `UpHtWalk` refuted; R3 found
  to need a made-for invariant (030-03); 030-02 and 030-03 written.
* 2026-11-17 (coord-1117): Frans paused the main line (09:13) and chose
  the contract approach with a fresh start (10:56 to 11:14): D0, written
  down in 030-04; D1 frozen at the tag `proofs-2026-11-17`; Mathlib
  decided for the new package; `lean/README.md` labelled work in
  progress (050f6d93).


Files
=====

* [030-01](01-l4-plan.md). The plan for `l4`, the live counts' premise
  of D1's top theorem: route B (hu's option (b) done route P's way, as
  additions), no statement change; 8 steps, 3,000 to 5,500 lines; step 1
  (`l4` reduced to its case at the induction's runs) proved in scratch.
  Written 2026-11-16, 22:04 to 22:30. Status: open.
* [030-02](02-bridges-plan.md). The plan for D3, the bridges to the
  abstract model (TP14, TP16, TP19): all three rest on `l4` and `htbL`
  only; TP14 and TP19 found false as stated after 2^48 top nodes (no
  guard in the model's writer), so proved below that bound by default;
  10 steps, 9,000 to 22,000 lines, tests first. Written 2026-11-16, 22:04
  to 22:31. Status: open.
* [030-03](03-r3-made-for-plan.md). The plan for R3, `l4`'s made-root
  branch: `R3Calls` false as stated by reading; MFI (a made-for link
  invariant, stratum-wide like MFB, and ValOld, a narrowed premise at the
  runs) used at the delete's start, SegOld carried to the call and
  through the merges' loop; no statement change; 6 steps, 3,200 to 7,200
  lines, one night for three provers; what else is left of `l4` (R4).
  Written 2026-11-17, 02:36 to 03:15. Status: open.
* [030-04](04-contract-fresh-start.md). The contract approach and a
  fresh start (Frans, 2026-11-17): the writer's contract, what is proved
  from it and what is tested; the five assumptions in one list; new
  proofs from scratch in `lean/contract/`, with Mathlib; the old line
  paused and frozen at the tag `proofs-2026-11-17`; the steps; the
  spike's brief. Waits for Frans: the spike's time. Written 2026-11-17,
  11:19 to 11:26. Status: open.
* [030-05](05-contract-spike.md). The report of 030-04's spike: the
  writer's contract settled (the invariants, the contents, the frame;
  the fill rule not in it), `inv_right`, `get_right` and `scan_right`
  proved from it in `lean/contract/` (4,900 lines, Mathlib, the standard
  axioms only), the contract checked on the 180 traces of the level 2
  sets with no failure; what is next for step 4. On the branch
  `030-04-spike`. Written 2026-11-17, 11:31 to 12:56. Status: done.
* [030-06](06-contract-review.md). An independent review of 030-05: sound,
  with fixes. The theorems proved and not vacuous (a history of three
  transactions added in Lean); the checker is the contract; Java met it
  on 120 traces (20,154 transactions, node sizes 8 to 62). Must fix
  before step 4: the checker passes ERROR lines and does not check that a
  trace is a history; the clauses step 4 needs (TREE shown not implied,
  in Lean). Written 2026-11-17, 14:48 to 15:40. Status: done.
* [030-07](07-bridge.md). The bridge from the contract to the abstract
  model (step 4a): the klongs as entries, the clauses the model assumes
  (`MeetsBridge`, `MeetsEvict`, and with 030-08's top `MeetsBridgeTop`),
  each checked on the traces; `RunOK`, TREE and `EvictRunOK` proved for the
  key tree, and by the old proofs recovery (T1), restart invariance (T2),
  lazy reading, eviction with handles and reclaim's cut; the top's premise
  proved from 030-08's top; D as state; what of bounded startup follows.
  Started 2026-11-17, 15:09. Status: open.
* [030-08](08-shape-top.md). The tree's shape and its top in the
  contract (step 4b): TREE as a clause, Java's top nodes and skip
  pointers with the readers' top search (TP24), the reads' theorems over
  the tree with its top; the step from trace lines to Java's tree reduced
  to one named premise. Written 2026-11-17, 15:09 to 15:50. Status: done.
* [030-09](09-trace-java-check.md). Step 4c, the night of 17 November: the
  trace's completeness (ERROR and unknown lines fail, TX 0, 1, 2, ... and
  DONE, every change in NEW, ADD and KN lines; KN from a klong diff;
  `historyOk_meets`), LIVE lines checked, the assumptions reads rest on in
  030-04, 3.5, Java's own check of the contract in its tests (TransCheck),
  the medium set checked (27 of 27). Status: done.
* [030-11](11-night-review.md). An independent review of 030-07 to 030-09:
  sound, with fixes. The top theorems say what the items claim, with no
  hidden premise; the bridge's instance is `tracecheck`'s; one history of
  four transactions meets every statement (`BridgeExample4`). Should fix:
  the restart and eviction theorems take each change as given (the writer's
  repeatability is 030-04, 3.5, item 9); three tested assumptions missing
  from 3.5; reads after a crash not stated end to end. Fixed: the bridge
  checker now requires a whole trace; `PolicyCutOK` proved for policies
  that read no stream. Written 2026-11-17, 17:02 to 17:55. Status: done.
* [030-12](12-contract-large.md). The contract check on the reclaim,
  medium and large sets of `treeconf.sh`, with `live=1`: more evidence
  that Java meets the writer's contract: 222 traces, 532,402
  transactions, both checkers, no failure; the medium and large sets
  with LIVE lines too (220 and 203 million). Status: done.
* [030-13](13-contract-in-levels.md). The contract's checks in the routine
  tests: the contract and the bridge checks in `level2.sh` (small and drain
  sets) and in `night.sh` (the medium set, `java/stress/contractconf.sh`);
  where each check runs; the checkers four at a time (par.sh). Written
  2026-11-17, 17:03 to 21:05. Status: done.

* [030-10](10-writer-spike.md). A spike of 030-04's optional step 5, the
  night of 17 November: does the model's writer meet the contract? The
  refinement map from the writer's state to the contract's tree, checked on
  the traces; the statement; how far a proof got and what the rest costs.
  Taken off `main` 2026-11-18 (030-18); the code is at the tag
  `writer-proof-2026-11-18`. Status: open.
* [030-14](14-reads-after-crash.md). Reads after a crash, a restart and
  under eviction, end to end (030-11, finding 3): a reader of the model's
  view at a time, with each key node's kind from its level (K-LEVEL, a new
  clause checked by `bridgecheck`, after an independent review's
  `FullLeafGap`), proved right for any history that meets `MeetsFull`, so
  that after a crash, restarts, a lazy startup, eviction with handles and
  safe cuts every get and scan at every available time gives the plain
  map's value; Java's readers after a crash, with their search through the
  skip pointers over the top that the stream holds; closed examples from
  `BridgeExample4`; 030-04, 3.5, item 13. The night of 17 November.
  Status: open.
* [030-15](15-strict-checkers.md). Strict trace parsing, one verdict, and a
  gate that pins the statements: every trace line by the grammar of format
  3 or the trace fails (an independent review's faults); `contractVerdict`
  with `contractVerdict_sound` (MeetsTop); `check.sh` runs both checkers;
  `gate.sh` step 5 pins the trusted closure of the main theorems
  (`statements.pin`). Status: open.
* [030-16](16-writer-delete.md). The model's writer meets the contract for a
  delete, beside 030-10's puts: the delete's full node (time and space split
  from a delete), the bitmap in every form, a delete of a one-segment key whose
  leaf keeps a live klong (`putKv_del1_keep`, the merges as a premise);
  030-10's `BalancedAll` shown false for a dead klong (`writerMeets_false`).
  The night of 17 November. Taken off `main` 2026-11-18 (030-18); the code
  is at the tag `writer-proof-2026-11-18`. Status: open.
* [030-17](17-readers-eviction-cut.md). Java's readers under eviction, after
  a lazy startup and after reclaim's safe cuts, end to end, with Java's
  search through the skip pointers; what that search reads (`TopFrom`), so
  what it does after a cut, when the top nodes before it are gone, and that
  the cut stream keeps what it reads; K-LEVEL in `contractcheck` too
  (`checkVerdict_sound`, a fault); Java's reads with one premise for every
  time (`HoldsP`, the tree holds the structure whole); `bridge-faults.sh`
  fixed (it failed on main 3f1e2fea). The night of 17 November. Status:
  done.
* [030-18](18-off-main.md). The writer proof (030-10, 030-16) taken off
  `main` (at the tag `writer-proof-2026-11-18`; 51 Lean files of
  `lean/contract/`) and the old proofs deleted (006-31, D1; at the tag
  `proofs-2026-11-17`): `lean/` keeps the executable model, the checkers,
  the test programs and the abstract model's proofs that the contract
  package imports, 159 files and 65,852 lines of 747 and 279,136. Written
  2026-11-18. Status: done.
* [030-19](19-codex3-points.md). The three points of Codex review 3 fixed
  in the checkers (006-31, D5): a delete bitmap of 2^62 or more refused
  (Java's has 62 bits; `B 2^64` was read as empty), a PROBE line that fails
  and a transaction without its GET and SCAN lines fail both checkers, with
  fault tests; 030-09's "4.3 million" is 3.96 million. No statement
  changed. Written 2026-11-18. Status: done.
* [030-20](20-commit-check.md). CC, the commit check as the writer's
  guarantee (026-23, section 1.4; Frans, 2026-11-18, 13:42): a proved
  check at every commit refuses a transaction that breaks the contract,
  so every record meets it whatever the writer does; what Java's
  `TransCheck` does today, what it would take, and the cost, not yet
  measured. Written 2026-11-18. Status: a note.
* [030-21](21-pe-proof.md). The complete proof that PE's writer meets the
  writer's contract: PE as total functions on the contract's tree
  (`Contract/PeWriter.lean`), the trial's tree at all 221,142 transactions
  of 288 traces; `pe_step` (a transaction PE accepts meets the contract,
  TREE and the top's clauses, and PE keeps its state), `pe_meetsTop` and
  `pe_meetsTop_start` (every history PE writes from the empty tree meets
  `MeetsTop`); 15,003 lines, the standard axioms only, gated. Part 2:
  `MeetsFull` for PE (`pe_full`, `pe_crash_reads`). Part 3: PE's
  acceptance (`pe_accepts`: every transaction whose puts' keys the tree can
  hold, if H leaves room and the fuel suffices). Left: Java. The night of
  18 November. Status: done.
* [030-22](22-reclaim-contract.md). Reclaim's contract, written down: four
  conditions at each cut that a trace can test (RC1 the order, RC2 the
  rewrites at the iteration's end, RC3 a value below every index node, RC4
  Java's two waits); that they give `CutOK` is T-SCHEME, half proved
  (`T_latest`), the rest needing an invariant on superseded versions; RC3
  from the writer's contract, RC2 from the iteration with one more writer
  property (a put makes a new value node); T-SCHEME with Java's exact waits
  checked by running in the model (0 failures); 4,000 to 9,000 lines, 2 to
  4 nights; the proof recommended after Monday's reset. Written
  2026-11-19. Status: open.
* [030-23](23-reclaim-step1.md). Reclaim's proof, step 1: T-SCHEME stated
  in Lean (`TScheme`, RC as `RC`) with the theorems after cuts restated
  with RC (`full_cut_rc`, ...); proved under RC: `CutOK` but part 2's
  versions besides the latest ones (`rc_parts`, `rc_dref`), so the open
  half is part 2 alone (`TSchemeReads`); RC1 to RC4 in `tracecheck`, 954
  CUT lines of the reclaim traces, 0 failures; the invariant found by
  running, GIS-J, in Lean with the proof that it gives part 2
  (`reads_of_gis`), so what is open is `TSchemeGis`, of which Lemma G, most
  of clause (i) and clause (ii)'s case 1 are proved; the candidates
  refuted, with counterexamples; 1,688 lines of Lean. Written 2026-11-19.
  Status: done.
* [030-24](24-reclaim-step2.md). Reclaim's proof, step 2: RC gives
  `CutOK` (the read half by the independent search's invariant), so the
  reads after cuts need only RC at each cut; `TScheme` without A6' false,
  in Lean; RC2 and RC3 for the key tree, from the iteration and VAL-NEW,
  which PE meets; the top theorem for PE (`PE.pe_reclaim_reads`); 3,991
  lines of Lean. Written 2026-11-19. Status: done.
* [030-25](25-iteration-ok.md). Reclaim's iteration proved: a model of
  the iteration's steps (027-13, section 1.4: each step's scan at its own
  time from lastKey up to E, any stops before or after a KV, the rewrites
  and the row, the last step's scan past the end; `StepsOK`) and the proof
  that a history whose steps follow it meets `IterationOK`, given VAL-NEW
  (`iterationOK_of_stepsOK`); the top theorem with the steps in place of
  `IterationOK` (`PE.pe_reclaim_reads_steps`); an example; how Java's steps
  could be checked on traces; 730 lines of Lean. Written 2026-11-19.
  Status: done.
* [030-26](26-core-algorithms-proved.md). The public statement that
  BergDB's core algorithms are proved (Frans, 2026-11-19): the claim and
  what it means for a user; what is proved, each part with its top
  theorem; the model and what "proved" means; the limits; 030-04's 13
  tested assumptions as they now stand, each with its test and where it
  runs; how it stays true; the history. Written 2026-11-19; kept up to
  date with `main`, at least until release 2026.6 (Frans, 2026-11-20).
* [030-27](27-step-check.md). Java's reclaim steps checked on the
  traces: the exporter's STEP line (t0, c, lastKey before and after, eod,
  from the row in memory) and `tracecheck`'s C-STEP, which checks every
  step at its state against the model of 030-25 (`StepsOK`) on the tree
  model's reads, and every cut against its iteration's last step; a fault
  test of 10 faults in level 3; on level 3's 35 reclaim traces 1,014
  steps in 907 iterations and 775 cuts, 0 failures. Written 2026-11-19.
  Status: done.
* [030-28](28-writer-copy-checked.md). The tested writer is the proved
  writer, checked routinely: the tree checker's writer, the copy
  lean/SIS/Tree/Pe.lean, compared with the proved writer at every
  transaction of level 2's tree sets (`pecmp`, lean/pecmp/, step 8c of
  `level2.sh`: the writes in their order, the ids' order, the trees, the
  top node), (B) chosen over running the proved writer in the checkers;
  the copy and pecmp pinned in statements.pin (no statement changed); the
  pins checked every night without a build (`pins.sh`, step 0); Java's
  depth guard unreachable on an undamaged stream, and `pe_accepts`'
  premises met by every transaction Java admits (G = 8,192, H = 100); the
  digests of record format 8. Written 2026-11-19. Status: done.
* [030-29](29-dirty-bound-proof.md). The dirty-node bound proved for PE:
  Java's `Dag.dirtyNodeBound` modelled on the contract's tree, function for
  function (`Contract/DirtyBound.lean`), and proved to bound the key nodes
  PE writes for every transaction of puts PE accepts, from a state PE keeps
  whose tree meets the fill rules (`pe_dirtyNodeBound_puts`); deletes tested
  (224,000 random transactions, none above), not proved; 030-28, section 5,
  in Lean, with H = 126 in place of 100 (`pe_accepts_java`). Written
  2026-11-20. Status: open.
* [030-30](30-seeds-and-contract-check.md). Two changes to the testing
  of Java against the model (Frans, 2026-11-20): `night.sh` runs the
  sets of traces on new seeds each day as well (the conformance sets and
  the tree sets with the tree check, the contract and bridge checkers
  and `pecmp`; 406 traces, 13 minutes), every seed recorded, a failing
  trace kept with the command that makes it again; and `week.sh` runs
  Java's commit-time check (CC) on the apps' soak and kill rounds, one
  kill-restart seed and three harness-soak rounds, switched on in every
  JVM by the environment variable `BERGDB_TRANSCHECK`; its cost
  measured. Written 2026-11-20. Status: done.
* [030-31](31-app-traces.md). The user apps' workloads and reclaim
  across restarts, against the model (Frans, 2026-11-20): AppRecord
  records an app's Core transactions and TraceExport replays them
  (`workload=F`), checked by tracecheck, the contract checker and the
  bridge checker (`apptraces.sh`, in `night.sh` and `week.sh`); run A
  restarts and crashes (`restart=K`, `crash=K`), RESTART and RESUME
  lines, and C-STEP's STEP-resume (`conformance.sh crash`, in
  `level3.sh`). Written 2026-11-20. Status: done.
* [030-32](32-week-47-diary.md). The proof week of 16 to 20 November, a
  diary: one heading a day, from a large step-by-step model close to
  being given up, through the contract approach (Tuesday), to the core
  algorithms proved; and the idea of a contract tested after every
  operation. Written 2026-11-20. Status: done.
* [030-33](33-statements-review.md). An independent review of the
  statements against 030-26 (Codex, 2026-11-20): four findings, one high
  (reclaim's step model does not require the value written back to be the
  value read; C-STEP neither), two medium (values as hashes; TransCheck's
  coverage), one low. Status: done, all four acted on (030-34, 030-35,
  030-26).
* [030-34](34-c-step-values.md). 030-33's F1 in the trace checker
  (Frans decided, 2026-11-20): C-STEP checks that each step of reclaim
  writes back, at every old key its scan met, the value the scan read
  (STEP-values), and that it puts nothing else than those rewrites and its
  row and deletes nothing (STEP-ops); three faults more in the fault test;
  the Lean model of the steps unchanged. Written 2026-11-20. Status: done.
* [030-35](35-reclaim-preserves-values.md). Reclaim preserves users'
  values (030-33, F1): steps put the old keys met with their pre-step
  values, plus the current row, and no other operations; reads after cuts
  proved against a reference excluding maintenance, at every retained
  time (`PE.pe_reclaim_user_reads_steps`). The changes to pinned
  statements and proposed sentences for 030-26, section 2.5. Written
  2026-11-20. Status: done.
* [030-36](36-dirty-bound-deletes.md). The dirty-node bound for mixed
  transactions without joins, including empty-child removal and root
  collapse (`pe_dirtyNodeBound_noJoins`, its history form); a leaf-root
  corollary and one local planned-leaf join. The general joins and removal
  of the fill premise remain open. Written 2026-11-20. Status: open.
* [030-37](37-dirty-bound-joins.md). The dirty-node bound through all leaf
  joins and one level of inner joins, including recursive leaf rebalances,
  untouched neighbours and groups already joined; transaction and history
  theorems (`pe_dirtyNodeBound_twoJoinLevels`). Higher inner joins and
  removal of the fill and original-key premises remain open. Written
  2026-11-21. Status: open.


Log
===

2026-11-16. Created the item (Frans, 14:32), by coord-1116.
