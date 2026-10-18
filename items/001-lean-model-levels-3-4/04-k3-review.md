001-04. The K3 review: the Level 3 alignment
=============================================

By Claude (Opus 5.5, Claude Code), 2026-10-18, for Frans Lundberg. WP R9 of
the plan [01-plan.md](01-plan.md) (section 3, K3); the work is logged in
[02-progress.md](02-progress.md). Stage 3 of the plan, Level 3 (reclaim) on
the model with the cache, is done. K3 has passed: by the agent, on your go of
2026-10-17 19:59 ("Why wait for me? If things work as expected"), since its
conditions for an automatic pass hold (section 1). This guide says what was
decided, the evidence, and how to check it.


1. What was decided
===================

K3 accepts the Level 3 alignment and adds a conformance step to
`level3.sh`. Its conditions for an automatic pass (plan, section 3): T8, T9
and T12 proved; T-SCHEME proved or checked at every cut; R9's conformance
passes; no Java change beyond E7's list. All four hold:

* **T8, T9 and T12 are proved** (section 2), T12 also with eviction.
* **T-SCHEME is checked at every cut, not proved** (the plan's fallback for
  R6): C-CUT checks `CutOK` at every cut Java decides, in every run of the
  conformance sets, and in the new gate step; and by running on the model's
  example 4 (222,857 states). Why not proved: section 3.
* **R9's conformance passes** (section 4): every record of both reclaim sets
  is the model's, every cut is safe, every probe after a restart from a cut
  stream answers right; the gates pass.
* **No Java change beyond E7's list**: R8's six changes make E7's six
  (level4-alignment.md, 6.1; its change 1 makes rows 1 and 4) and the red
  list's one (M17, change 6, which R7 found on Java's reclaim traces); nothing
  else in `java/src/` changed for Level 3 but R2's test-only hooks.

So: (1) the Level 3 alignment as `docs/level3-alignment.md` records it,
section 7 point by point; (2) a step 8 in `level3.sh`, "Conformance with the
Lean model, with reclaim" (its section 8): `conformance.sh reclaim`, the
small reclaim set, 2 seeds quick (10 traces) and 5 full (25 traces), about 70
seconds in quick mode and 2 minutes in full mode. J1 may start.

If you want K3 otherwise (another gate step, or the T-SCHEME proof before
stage 4), say so and record it in [02-progress.md](02-progress.md).


2. What is proved
=================

All in `lean/SIS/ReclaimTheorems.lean`, the trusted statements, each with a
comment in plain English; only Lean's standard axioms.

| Theorem | In plain English | WP |
|---|---|---|
| T13' (`T13_markTouch`) | With reclaim's touches, step 3 gives exactly the index nodes not in D that are dirty or touched | R3 |
| T8 (`T8_recoverCut`) | After a safe cut, startup from the cut stream gives the same lookups at every time from the first available time on, and the same D | R4 |
| T9 (`T9_readCut`) | With eviction, after a safe cut, a read in the running process at any time from the first available time on gives the same on the cut stream as on the whole stream, and gives P | R4 |
| T12 (`T12_restartCut`) | A run that restarts from safe cut streams appends the records of the run without restarts (only the records before the largest cut are gone), with its D and its lookups from the first available time on | R5 |
| T12 with eviction (`T12_evictCut`) | The same for the run with eviction, any cache schedules whose reads are from the first available time on, and the Level 4 startup at each restart | R5 |

"Safe" is `CutOK` (`lean/SIS/Reclaim.lean`): the cut is at or before the
first available time f; every version that a read from f on may follow, a
lookup's or a physical read's (`ReadsPhys`, your decision (a) of M48), is at
the cut or later; every node of D has its latest version at the cut or
later, and its references below the cut name latest versions; the top is
after the cut.


3. What is checked, not proved
==============================

**T-SCHEME**: Java's scheme (an iteration's touches cover the old index
nodes, its rewrites the old values, and the cut waits for pEnd, then pSafe)
gives `CutOK`. R6 examined a proof: after the waits every node reachable from
f on has its latest version at the cut or later, which gives `CutOK`'s parts
1, 3 and 4. Part 2's physical-read rule also reaches versions that later ones
superseded (written while a node below was still in D with a version before
the cut), and a proof needs an invariant over those that the existing ones
do not give; R6 part 1b had found the first form of the statement false by
running. I judged a proof several days with an uncertain outcome and took
the plan's fallback (level3-alignment.md, section 5, "T-SCHEME: checked, not
proved"). Checked:

* at every cut Java decides: R9's runs (section 4), and the new gate step;
* by running on example 4 (`lake exe reclaimtest`, `checkSchemeB`): 5,156
  iterations with the scheme's conditions, `CutOK` in all 222,857 states past
  the waits (100 runs of 100 transactions, 4 startup pos policies).

The coverage of the touches (a step touches every index node whose key range
meets its range) is a condition in the model; Java's key ranges are not in
the trace, so C-CUT checks the conclusion instead.


4. R9's conformance
===================

The reclaim traces of R2's sets made again with the current Java (`java/`
as at `5b1abdd`, R8's last change), each checked by the checker at
`970c996`: C-A (the assumptions, the touch's included, and the diagnostics D
closed upward, A6, TREE, A-COPY), C-S (every record and D the model's step,
on the stream cut at the largest cut so far), C-CUT (`CutOK` at every cut,
the record's first available time, physical cuts at or below the decided
ones), C-R (run B's probes: restarts every ten transactions and right after
each cut, lookups at every available time), C-L and C-L4 (first touches).

| Set | Traces | Transactions | Cuts | Failures |
|---|---|---|---|---|
| Small (5 configurations, 5 seeds) | 25 | 14,448 | 288 | none |
| Medium (3 configurations, 2 seeds) | 6 | 22,460 | 175 | none |

The Java tier, the gates, full, on `970c996` (2026-10-17 23:04 to 23:24):
`LEVEL 1 OK`, `LEVEL 2 OK` (unit tests 918, F tests 37; 60 of 60 small
traces TRACECHECK OK), `LEVEL 3 OK` (ReclaimStress 200 random configurations,
RestartInvariance with reclaim, CrashTest with reclaim, ReclaimReaders,
LoadTest with a restart at every cut, PowerLossTest). With the new step:
`LEVEL 3 OK` full (484 s; the step 25 of 25 traces, 288 cuts, no failure) and
quick (151 s), and `LEVEL 2 OK` with the changed `conformance.sh` (715 s).
The quick performance suite: R8's comparison against `l34-base`, no
regression (2026-10-17 19:12 to 19:41).


5. The changes
==============

Stage 3's changes to the trusted Lean model are listed in `lean/README.md`,
"Changes to the trusted part": `SIS/Reclaim.lean` (R3: the touch, the first
available time, cuts, `CutOK`; R7: part 2 over the versions a lookup may
read; R4: `VirtLiveOK`; R6: part 2 over `ReadsPhys`, with the exception for
versions that Rule A put back) and the statements in
`SIS/ReclaimTheorems.lean`.

To `java/src/`: R2's test-only hooks (`Db.TestHooks`, `Reclaim.lastCutRow`)
and R8's six changes (level4-alignment.md, 6.1; change 6 is the red list's,
`Db.endOfTrans`, level3-alignment.md section 6), each with its gates and the
byte comparison against `l34-base` (the Level 2 configurations byte for byte
the same; only runs with reclaim differ, by M17's change). K3 adds the gate
step: `java/stress/level3.sh` (step 8) and `java/stress/conformance.sh` (a
`reclaim` set).

The commits of stage 3: R1 to R9 and K3, listed in 02-progress.md.


6. How to reproduce the decisive checks
=======================================

In `lean/`: `lake build`, `lake exe reclaimtest 20 30` (T8, T12, eviction,
T-SCHEME by running; 1 minute), `lake exe reclaimtest 100 100 scheme` (9
minutes), and `#print axioms` as `lean/README.md` shows. In `java/`:

    java/stress/level3.sh quick         # with the new step 8 (about 2.5 minutes)
    java/stress/conformance.sh reclaim  # the small reclaim set alone (2.5 minutes)
    PAR=4 java/stress/reclaimtraces.sh medium   # the medium set's traces; then the
                                        # checker, lean/.lake/build/bin/tracecheck, on each

The medium set's checks take about 6.5 hours for its two largest traces.


7. Open risks
=============

1. **T-SCHEME is not proved.** A change to Java's reclaim (its waits, the
   touch, the rewrites) is caught only by C-CUT on the traces of the gate
   step and the sets; the gate step runs the small set only.
2. **The touch's coverage is assumed in the model** and not checked on Java
   (it needs key ranges); C-CUT checks its consequence at every cut.
3. **M33, M41**: Java's skip of slots below the cut and its startup's reads
   after a restart from a cut stream are argued for Java and checked by the
   probes; the model's part is proved (T8, T12).
4. **Stage 4 changes the cache**: T9 and T12 with eviction say that the
   model's physical layer stays safe after cuts; Java's eviction (J1 to J10)
   must keep INV-SLOT, which J1's audit and J4's C-P check.
