001-06. Report: Levels 3 and 4 in the Lean model and in Java, aligned
====================================================================

By Claude (Opus 5.5, Claude Code, Max effort) for Frans Lundberg,
2026-10-18. The final report of the plan [01-plan.md](01-plan.md) (its WP
F3), for checkpoint K5. The work ran from 2026-10-16 15:23 (G0) to
2026-10-18 16:53 in bergdb's main work tree, unattended after G0 except
for K1 (yours, 2026-10-17 07:56) and your decisions of 2026-10-17 (M48,
M46, M49, and the go of 19:59). Every WP is committed, one commit per WP
(J2 and J3 in one); the log of every session is in
[02-progress.md](02-progress.md); the details
are in bergdb's
[docs/level3-alignment.md](../../docs/level3-alignment.md) and
[docs/level4-alignment.md](../../docs/level4-alignment.md).


Summary
=======

BergDB now has Level 3 (reclaim) and Level 4 (eviction: data and index
larger than memory) both in the Lean model, with proofs, and in Java,
aligned with the model in the sense of the plan's section 1.2.

* **The model** has a physical layer: objects, slots and a node table,
  read lazily after a restart (stage 1); eviction of any object outside the
  pinned set at any transaction boundary (stage 2); and reclaim, the cut of
  the stream's front (stage 3). Proved: with any eviction schedule the
  physical writer appends the model's records and leaves its D, and reads
  give P (T-CACHE, T-READ, also with restarts, T2-C); every object outside
  the pinned set may be evicted (T-PIN); after a safe cut, recovery, reads
  and restarts give the same answers from the first available time on (T8,
  T9, T12, also with eviction). That Java's reclaim scheme gives safe cuts
  (T-SCHEME) is checked at every cut Java makes, not proved (the plan's
  fallback).
* **Java** got the six corrections the model required before eviction
  (R8), and Level 4: a registry of resident objects, eviction of values
  and index nodes at transaction boundaries and after loads, a capacity
  controller with the budget `cacheSizeInMb`, on by default, readers and
  reclaim under eviction, and a fourth gate, `level4.sh`. No change to the
  record format or the public API.
* **The checks**: a trace checker runs the model's own definitions on
  Java's runs; on the final code every transaction checked is the model's
  step, every cut is safe, every restart invisible, and Java's physical
  states meet the model's INV-SLOT. With every eviction schedule the
  streams are byte for byte those without eviction. A database of 20
  million keys runs on disk in a 2 GB JVM with a 500 MB budget; the
  quick performance suite is within the plan's targets against Level 3.

What is not proven: the mapping α from Java to the model (written down and
checked on many runs); T-SCHEME (checked); TREE, A6' and A-COPY for Java
(checked); concurrency (Java's protocol, tested). What does not perform
well yet: the capacity controller's sweep walks every resident object, so
under a read-heavy workload whose working set exceeds the budget it stalls
the writer (P4, finding 10).


The outcome, point by point
===========================

| Point of 1.2 | Level 3 | Level 4 | Evidence |
|---|---|---|---|
| 1. Correspondence | Done: α for reclaim; every register row resolved | Done: α for the cache; every register row resolved (M43 by checks; M46 and M49 deferred by you to items 002 and 003) | level3-alignment.md, 1 to 3 and 7; level4-alignment.md, 2, 3, 5 to 8 |
| 2. Java runs meet the assumptions | Done: the touch assumptions and D closed upward in every transaction; every cut safe (`CutOK`) | Done: TREE, A6' and A-COPY in every transaction checked (A6 fails in 5, as K1 accepted) | F1; C-A, C-CUT; the Java tier |
| 3. Java's steps are the model's | Done: every record (user, reclaim steps, table) and D the model's on the cut stream | Done: C-S, and with eviction C-P (INV-SLOT on Java's states) and the audit | F1; C-S, C-P; J1 to J9 |
| 4. Restarts | Done: from cut streams, every available time gives the model's answer | Done: with eviction too | C-R probes; `EvictionInvariance` with restarts; T12, T2-C |
| 5. Cache invariance | — | Done: the same stream byte for byte with the schedules none, values, every, random and the controller; T-CACHE | `EvictionInvariance`, F1 |
| 6. Proofs | Done but T-SCHEME (checked at every cut, not proved) | Done | `lake build`; `#print axioms`: standard only |
| 7. No regressions, Level 4 works | Done: the gates; the soak (P2) | Done: four gates; Q13's targets (J10); larger than memory (J8); the soak with eviction (P4, with its throughput finding) | F1, J8, J10, P4 |

The checks in numbers, on the final code and model (F1,
[docs/evidence/level34-conformance.txt](../../docs/evidence/level34-conformance.txt)):
the Level 2 sets, 81 traces with 44,141 transactions; the reclaim sets made
again, 31 traces with 36,908 transactions and 463 cuts; the eviction set,
30 traces with 7,794 transactions and 472,829 slots checked by C-P; every
trace `TRACECHECK OK`. The Java tier, 68,901 transactions on 21
configurations. `EvictionInvariance` with every schedule, 24 runs. The four
gates in full, and every record of `StreamDigest`'s 36 runs the same as
R8's. Along the way, the audit checked INV-CAN, the pins and INV-SLOT about
6 million times in the stress runs with and without eviction, with no
failure.


What changed
============

**Java** (bergdb `java/src/`; one commit per WP):

* A3 (`280525a`): top node ordinals of 32,768 and more were written wrong
  (an `int` shifted before widening); fixed, with two parser checks and
  tests (M30).
* R8's six changes, each with the byte comparison against the Level 3
  baseline (`l34-base`): change 6 (`ab8dc7a`, M17: a reclaim step's marks
  of replaced nodes leave D, so a step's D is the model's); change 2
  (`dcf6a4d`, M22: no cut back at runtime); change 1 (`d540066`, M20, M21,
  M26, M44: the writer's references from the pinned set and the slots, and
  the startup's links by node id); change 3 (`b8bb541`, M27: the Level 4
  loader); change 5 (`059dbf1`, M28: reclaim's maintenance reads); change 4
  (`5b1abdd`, M23, M24: a slot read once, the access clock).
* Level 4, J1 to J10 (`c3590ce` to `70c1801`): `Residents` (the resident
  objects and their bytes; the pins), `Audit` (test-only: INV-CAN, the pins,
  INV-SLOT), `Eviction` (unswizzle, release, the forced schedules for tests,
  the capacity controller), the readers' protocol (Q8) and the writer's
  checks under the node's monitor, reclaim's step reserve, the cache size in
  `long` (M45), JMX; eviction on by default (Q10). About 2,950 lines in
  `java/src/`, 1,750 of them tests; with A3 and R8, item 001 changed 20
  files of `java/src/`, 3,796 lines added and 87 removed.

**The model** (bergdb `lean/SIS/`, the trusted part): the physical layer
(`Phys.lean`), eviction (`Evict.lean`), reclaim (`Reclaim.lean`), and their
theorems (`PhysTheorems.lean`, `ReclaimTheorems.lean`): 37,300 lines added
in `lean/SIS/` (83 files), most of them proofs in `SIS/Proof/`. Nothing of
Level 2's model was weakened; its theorems are kept.

**Tools**: the checker's new checks (C-L and C-L4 for first touches, C-CUT
for cuts, C-P for INV-SLOT on Java's states, the reclaim checks; fast
versions proven equal to the model's definitions, C2); the exporter's
trace format 2 (reclaim) and run E (eviction); the sets
(`conformance.sh reclaim` and `evict`, `reclaimtraces.sh`); `StreamDigest`
(the byte comparison); `EvictionInvariance`, `LargerThanMemory`,
`ReclaimHitRate`; `performance.sh`'s A/B runs and `JFLAGS`; the soak
(`Soak.java`, `soak.sh`); and the gates: `level3.sh`'s conformance step
(K3) and `level4.sh` (J9, required since K4).


Findings
========

1. **Top node ordinals from 32,768 on were written wrong** (M30, A3): a
   database past 65,536 top node versions could restart silently wrong.
   Fixed before anything else.
2. **A6 (no adoption) fails** in 5 of 68,901 Java transactions (A4): an
   in-place split of a new segment root. The model assumes the weaker A6'
   with A-COPY instead, which every Java transaction meets; you accepted it
   at K1.
3. **A reclaim step left replaced nodes in D** (M17, R7's red list): Java's
   D differed from the model's after some steps, and with it later records.
   Fixed by R8's change 6.
4. **CutOK needed a stronger part 2** for physical reads (M48): a read may
   follow older versions of a child than the one a pointer names. Your
   decision (a); T9 proved with it.
5. **The node table could name a snapshot** (M26, J1's audit): a split
   copied a memory slot to a snapshot, and the table entered it. Fixed: the
   table names canonical objects only.
6. **The public cache size overflowed above 2,147 MB** (M45, found in A2):
   fixed in J7.
7. **A transaction that throws inside `putKvs` is half committed** (M49,
   found beside this work): left for item 003, as you decided.
8. **The top node ordinal bound** of 2^30 limits a database's lifetime
   under reclaim (M46): left for item 002.
9. **Faults found in the new code by its own checks**: values that only
   the node table held were never released (J7's scan test); the writer's
   own `-ea` checks read a pointer's pair without the node's monitor (J5;
   the nodes were never wrong); pinned state above the budget made every
   load sweep (J7); and a sweep counted only what it released, not what
   left memory with it, so after reads it could empty the cache down to D
   (J8's first run). Each fixed with a test.
10. **The sweep's cost under read churn** (P4): a sweep walks every
    resident object (3.2 s on average at a budget of 1.6 GB) each time a
    quarter of the budget has been loaded, under the write lock. In P2's
    soak workload with eviction (an 8 GB heap, the budget a fifth of it,
    below what the readers touch) the sweeps took 35 percent of the time,
    and the paced writer reached 123.5 of its 200 commits a second, the
    readers 60 percent of their pace; G1 needed 81 full collections in the
    two hours, as the evicted objects are old garbage. Every read was right
    and the memory stayed bounded (1.5 to 1.9 GB live, against P2's growth
    to 15 GB).
11. **Startup is about 8 percent slower** than Level 3's (R8 and J10),
    within the target; not looked at further.


Where the work differs from the plan
====================================

* **T-SCHEME is checked, not proved** (R6, the plan's fallback): a proof
  needs an invariant over versions that later ones superseded, which the
  existing invariants do not give. It is checked at every cut Java decides
  (C-CUT) and by running on the model's example 4.
* **A6 became A6' with A-COPY** (finding 2; K1).
* **J7's sweep is not incremental**, which the plan's J7 asked for: it
  walks every resident object, once per quarter of the budget loaded
  (finding 10).
* **J10's run under pressure** is the read scenario's first run only (the
  whole suite would have taken hours at 30 to 90 times slower reads), and
  writes under pressure are J8's.
* **P4 ran with an 8 GB heap and a 1.6 GB budget**, after a first attempt
  with 4 GB and 800 MB reached half the paced commit rate in its first
  minutes (stopped after 200 s).
* **K3 and K4 were passed by the agent**, on your go of 2026-10-17 19:59,
  each with the plan's recommended option, recorded with its evidence and a
  review guide (04 and 05). At K5 the agent accepted the outcome; closing
  the item and what comes next are yours (below).
* `level4.sh`'s quick mode runs 6 rounds of `ReclaimStress` instead of 20
  (J9: 4 minutes instead of 9).
* Machine time: the conformance checker is slow on the larger traces (the
  medium reclaim set took 6.5 hours, the large Level 2 set's biggest traces
  4.5 hours each), so the campaigns ran in the background beside other WPs,
  in scratch copies of the work tree.


For K5: what you decide
=======================

1. **Accept the outcome** of 1.2 (level3-alignment.md, section 7;
   level4-alignment.md, section 8). The agent accepted it on your go
   (02-progress.md); say so if you want otherwise.
2. **Close the item, or not.** The plan's 1.3 counts the item done when
   every WP is done or dropped with your agreement. All are done but R6,
   which is partial: T-SCHEME is checked at every cut and by running, not
   proved (the plan allows this fallback in its 1.4, but the WP's status
   needs your word). Either accept R6 as it is, and the item is done, or ask
   for the proof (proposal 3 below).
3. **What comes next.** My proposals, none started:
   1. *The sweep* (finding 10): an incremental sweep, or the
      incoming-reference lists of Q9, or handles (bergdb item 004, opened
      the same day, studies indirect swizzling for this), so that eviction
      costs in proportion to what it frees, not to what stays. P4's
      workload is the test. A cheap first step: since J7's fix the sweep's
      count of what it frees is exact (it equals the resync's in every
      sweep measured), so the second walk, the resync after the sweep,
      could go; and the walk's lists and maps could be kept between sweeps
      instead of built each time.
   2. *Loads*: keep the node's id in an unswizzled slot, so that a load
      reads the node once, not its header first (level4-evidence.md).
   3. *T-SCHEME*: prove it, with an invariant over superseded versions; or
      keep it checked (it is a gate step since K3).
   4. *Items 002 and 003* (M46, M49), when you choose.
   5. *The gates' time*: `level4.sh` adds 16 minutes; with the other three,
      a full check of a Java change takes about 45 minutes.
