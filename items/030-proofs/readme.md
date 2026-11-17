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

A fully proved model: "We still try to prove everything now. Once that
work is done, I may decide on a general policy on this." (Frans,
2026-11-15, 08:47.) The goals in order are 006-26, section 8; what each
word means (proved, reduced, tested) is 006-26's.


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
* **What it changes here:** D1 is paused; D3's goal moves to 030-04's
  step 4. "The aim" above is as written on 16 November; D0's aim is its
  goal. The rules above hold for `lean/` as before; the new package's
  gate is 030-04, section 7.6.
* **Items:** 030-04.

D1. The key tree, today's model (the main line until 2026-11-17; paused)
------------------------------------------------------------------------

* **Paused** since 2026-11-17 (Frans, 09:13 and 11:14; 030-04). Frozen
  at the tag `proofs-2026-11-17` (f4d73289); nothing is deleted. The
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

* The costs (TP20 to TP33), reclaim's scheme (T-SCHEME), the model's
  scope (026-14): open, not started; 006-26, sections 6 and 8.
* Java against the model: tested only, by the trace checkers; it stays
  a test.

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

* [030-10](10-writer-spike.md). A spike of 030-04's optional step 5, the
  night of 17 November: does the model's writer meet the contract? The
  refinement map from the writer's state to the contract's tree, checked on
  the traces; the statement; how far a proof got and what the rest costs.
  Status: open.
* [030-15](15-strict-checkers.md). Strict trace parsing, one verdict, and a
  gate that pins the statements: every trace line by the grammar of format
  3 or the trace fails (an independent review's faults); `contractVerdict`
  with `contractVerdict_sound` (MeetsTop); `check.sh` runs both checkers;
  `gate.sh` step 5 pins the trusted closure of the main theorems
  (`statements.pin`). Status: open.

Log
===

2026-11-16. Created the item (Frans, 14:32), by coord-1116.
