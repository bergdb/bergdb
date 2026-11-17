001-01. Plan: Levels 3 and 4, in the Lean model and in Java
============================================================

Created 2026-10-16 by Claude (Opus 5.5, Claude Code) for Frans Lundberg,
from the discussion of that day, as an overview. Extended the same day
(14:05 to 14:48) into the detailed plan, at Frans's request: a plan that
Claude Code (Opus) can carry out unattended for a long time, to the goal
below. Based on bergdb at `f050833` (read, not changed), bergdb's `docs/`
and `lean/`, and the f1 repo's F1-008 (07 to 13, and Codex's review of 09).

**Status: plan only.** No work package has started. Work in bergdb waits
for Frans's go (G0, section 3). The state of the work is in 001-02,
[02-progress.md](02-progress.md).

The sections down to "Stages" are the overview; sections 0 to 11 are the
detailed plan. Section 0 is the agent's entry point.


Decisions (Frans, 2026-10-16)
-----------------------------

1. One plan for both levels, in stages, each stage with its own theorems.
2. Caching (Level 4) before reclaim (Level 3).
3. Level 4's model may change Java's Level 3 (reclaim) where it requires it.


The goal
--------

Frans, 2026-10-16: when this work is completed, "we will have an
implementation in Java with a matching Lean model that covers all levels
including Level 3 and Level 4. All tests should run successfully."

In the terms of this plan:

* **Java.** BergDB implements Levels 0 to 4. Level 3, reclaim, works as
  today, changed only where the Level 4 model requires it. Level 4,
  eviction, keeps data and index larger than memory under a managed memory
  budget, with concurrent readers, reclaim, crashes and restarts.
* **Lean.** bergdb's model covers the same: lazy reading after a restart
  (lemma M), the cache with eviction, and reclaim with cuts, on top of the
  Level 2 model, with the theorems of each stage proved (section 1.4).
* **Matching.** Java's runs are runs of the model at every level, in the
  sense of section 1.2, checked by the trace checker and the Java tier.
* **All tests pass.** `level1.sh` to `level4.sh` print `LEVEL n OK`;
  `lake build` passes with no `sorry`; the random model tests, the
  checker's tests and the conformance sets pass.


How the levels depend on each other
-----------------------------------

At Level 2, the model and Java rely on two simplifications:

* The writer knows the newest version of every node it points to, because
  everything stays in memory (register rows M4 and M5 of
  [docs/level2-alignment.md](../011-docs-archive/11-level2-alignment.md)).
* Everything ever written can still be read.

Level 4 removes the first and Level 3 the second. Both then meet the same
question: what does a reference name, and when is it safe to follow it?

* Level 4, eviction. An evicted node is read back lazily, which is lemma M
  (M8: argued and checked, not in the model). A parent may hold only an
  older reference for a dead pointer. M4 breaks: Java's still-dirty test
  sees only the children in memory.
* Level 3, reclaim. The cut removes old versions, so every version still
  needed must lie after the cut, and reclaim's touch must rewrite the
  others. With eviction, reclaim must find and read nodes that are not in
  memory.

So the dependency runs mostly from Level 4 to Level 3: caching decides the
reference rule, and reclaim's safety depends on that rule. Aligning Level 3
first could validate reclaim code that Level 4 then forces us to change.


Stages
------

0. **The checker's speed** (WPs C1 to C3). The trace checker evaluates the
   model's `markOf`, quadratic in the nodes of P; the medium set takes about
   two hours, and runs with eviction and cuts are larger. Add fast versions
   of the model's functions, proven equal (`@[csimp]`), so the trusted
   definitions stay as they are.
1. **Lazy reading in the Level 2 model** (L1 to L5). Read nodes on first
   touch instead of at startup, and prove lemma M. Both levels need it, it
   closes the one open gap at Level 2, and the existing checker can test it
   against today's Java. This is also the first part of the physical layer
   (section 8.6): what Java holds in memory.
2. **Level 4 in the model, before any Level 4 code** (E1 to E7, checkpoint
   K1). Eviction, what a written version names, pinned nodes. Here the
   model leads, since there is no Java to match. Design work as much as
   proof work, and the hardest stage: a time box (5.3), with stops for
   Frans's decisions. The leading candidate keeps today's reference rule and
   today's records (Option K, 8.5).
3. **Level 3 on that model, aligned with Java's reclaim** (R1 to R9, K3), by
   the Level 2 method: α extended, the checker on runs with cuts. Java's
   reclaim changes where stage 2 requires it, before any Level 4 code is
   written.
4. **Level 4 in Java** (J1 to J10, K4), implemented against the model, with
   the checker.

Before stage 0: a baseline and early probes (A1 to A4). After stage 4: the
conformance campaign over all levels, the documents and the final report
(F1 to F3, K5). In parallel, as machine time (P1 to P4): Level 3's
performance reference and long disk soak, a measurement of the bounds, and
the soak again with eviction.


0. For the agent: how to use this plan
======================================

At the start of every session, and after the conversation has been
summarized:

1. Read sections 0 to 5 of this plan, and the parts of sections 6 to 8 that
   your work package (WP) needs. Then read [02-progress.md](02-progress.md):
   Frans's go and decisions (they override this plan's defaults), the status
   table, and the last three log entries.
2. Run `git status --short` in bergdb and compare it with the uncommitted
   files that the progress log names (2.1).
3. Choose the WP: the one the prompt names; otherwise the first in the order
   of section 5.1 that is not done, whose dependencies are done, and that no
   checkpoint blocks. If a checkpoint blocks the next WP, take the first
   that can start in another track (5.2). If none can start, write a
   progress entry that says why, and stop.
4. Read the WP's inputs. Do the WP within its scope and the rules of
   section 2.
5. End with a progress entry (2.6), also when you stop early. Leave the work
   tree in a state where the build and the checks you ran pass, or say
   exactly what fails and why.

Long jobs (the full gates, the medium conformance set, the soak, a
performance session) run in the background while you do other work. Never
run two gates, or a gate and `performance.sh`, at the same time (2.7).

A prompt Frans can use: "Carry out the next work packages of bergdb item
001 (items/001-lean-model-levels-3-4/01-plan.md). Follow the plan's rules,
and work unattended as far as possible."

Terms:

* **bergdb**, **f1**: the repositories `/Users/f/fl/repos/bergdb` and
  `/Users/f/fl/repos/f1`. Paths such as `java/src/bergdb/core/Db.java` or
  `lean/SIS/Algorithm.lean` are in bergdb.
* **The model**: bergdb's `lean/`, the Level 2 model as F1-008-11 left it:
  DB = ⟨P, D, S⟩, marking in step 3, BergDB's still-dirty test, the virtual
  root, T1, T2 and T13.
* **The logical model** is that model. **The physical layer** (stages 1 and
  2, section 8.6) is the new part of the model that holds what Java holds in
  memory: objects with identity, pointer slots, the node table, pins. The
  logical model stays the specification.
* **α**: the mapping from Java's state to the model's state
  ([docs/level2-alignment.md](../011-docs-archive/11-level2-alignment.md), section 2),
  extended in `docs/level4-alignment.md` and `docs/level3-alignment.md` (new,
  WP A2).
* **The register**: the mismatches between Java and the model. M1 to M19
  are Level 2's (level2-alignment.md, section 6). This plan reopens M8 and
  M17 and adds M20 to M44 (section 7).
* **The gates**: `java/stress/level1.sh`, `level2.sh`, `level3.sh`, and
  `level4.sh` once WP J9 has made it.
* **The exporter** (`java/stress/TraceExport.java`), **the checker** (`lake
  exe tracecheck`), `conformance.sh`, and **the Java tier** (`A2A3Check2`,
  `RestartInvariance` and the other stress programs).
* **Option K, Option F**: the two candidate reference rules for Level 4
  (8.5).
* **Sizes**, in agent working time: S up to 2 hours, M 2 to 8 hours, L 8 to
  24 hours.


1. Goal and scope
=================

1.1 Direction
-------------

* One plan, in stages, each with its own theorems (decision 1).
* The model leads where Java does not exist yet (Level 4). Where Java exists
  (lazy reading, reclaim), the model is tied to real Java runs through the
  checker. F1-008-07 and F1-008-08 modeled caching and reclaim together and
  drifted away from the Java code; this plan must not repeat that.
* The code never moves backwards. Java changes only where the alignment or
  Level 4 needs it, one change at a time, with the gates green.
* Prefer what keeps Java's records, byte for byte: a model change that
  describes Java's behavior beats a Java change; a Java change that keeps the
  stream format beats one that changes it.
* A working, performant database first (Frans, 2026-10-13); theory where it
  reduces risk.

1.2 What "aligned at Levels 3 and 4" means
------------------------------------------

This extends section 1.2 of F1-008-11 (Level 2). The outcome is recorded,
point by point, in `docs/level3-alignment.md` and `docs/level4-alignment.md`
(WPs R9 and F2).

1. **Correspondence.** α covers the cache (resident objects, slots, the
   node table, pins) and reclaim (internal transactions, the touch, the first
   available time, cuts). Every step of the extended model and every
   assumption is mapped to Java code. Every register row is resolved: by a
   code change, by a model change with proofs, by an argument with checks,
   or by Frans's explicit acceptance.
2. **Java runs meet the assumptions.** In the conformance campaign, every
   transaction meets the model's assumptions, now also A6 (no adoption, 8.5)
   and the touch assumptions (R3, R6), and every cut Java makes is safe by the
   model's definition (`CutOK`).
3. **Java's steps are the model's steps.** For every record, of user
   transactions, reclaim steps and table stores alike, the model's step from
   α of Java's state gives Java's record and D. Java cuts only where the
   model allows.
4. **Restarts.** After a restart at any point, also from a cut stream and
   whatever the cache held before, α of Java's state equals that of the run
   without the restart, and lookups at every available time give the model's
   answers.
5. **Cache invariance.** The same transactions with different eviction
   schedules (none, after every transaction, random) give the same stream,
   byte for byte, the same D and the same answers; Lean proves that the
   physical writer's records and D do not depend on the cache (T-CACHE).
6. **Proofs.** Lean proves the theorems of 1.4 under the assumptions of
   point 2. No `sorry`, only Lean's standard axioms. The existing theorems
   are kept, as instances where they are generalized.
7. **No regressions, and Level 4 works.** The gates pass in full; the quick
   performance suite stays within the targets of Q13 against the Level 3
   reference; a database whose data and whose index are several times larger
   than the memory budget runs on disk with stable memory.

Not claimed: that every possible Java run is a run of the model (α is
written down and checked on many runs, not proven); concurrency (readers
beside the writer and beside eviction: a Java protocol with targeted tests,
Q8); bytes, torn records and durability (the gates and `PowerLossTest`);
resource bounds (measured, P3); the B-tree's lookup correctness (INV-LOOKUP
of [docs/problem.md](../011-docs-archive/01-problem.md): the model abstracts the Dag
through `Spec`, as at Level 2, and DagFuzz, RestartStress and the checker's
C-V test it).

1.3 Done
--------

The item is done when the outcome of 1.2 is recorded point by point with
its evidence, every WP of section 5 is done (or dropped with Frans's
agreement), the final report (F3) is written, and Frans accepts it at K5.

1.4 The theorems, stage by stage
--------------------------------

Lean names are proposals; the WPs may choose others and record them.

| Stage | Theorem | In plain English | Proved or checked |
|---|---|---|---|
| 0 | C-EQ, one per fast version | The checker's fast version computes the same value as the model's definition | Proved (C2) |
| 1 | LM (`LM_newer`), lemma M | A later version of a node serves every lookup time that an earlier version serves, also when cut back to the startup time, for times up to it | Proved (L2) |
| 1 | T1-L (`T1_lazy`) | After startup from any prefix of the stream, reads at any time through Java's first-touch rule, in any order, give P at that time | Proved (L3) |
| 1 | CC (`CC_canonical`) | Every object the writer makes canonical holds its node's whole history | Proved (L4) |
| 1 | T2-L (`T2_lazy`) | With a lazy startup, restarts change no record | Proved (L4) |
| 1 | — | Java's first touches after restarts follow the rule | Checked (C-L, L5) |
| 2 | A6, TREE | No adoption; one current parent (assumptions, 8.5) | Checked on Java (A4, C-A), and by running on the model's examples |
| 2 | T-CACHE (`TC_records`) | For any cache schedule, the physical writer appends the model's record and leaves the model's D; INV-SLOT holds throughout | Proved (E3) |
| 2 | T-READ (`TR_view`) | For any reachable cache state, a physical read at any time gives P at that time | Proved (E4) |
| 2 | T2-C (`T2_cache`) | Restarts with any cache schedules change no record | Proved (E5) |
| 2 | T-PIN (`TP_pins`) | Any clean object outside the pinned set may be evicted at any transaction boundary, and the theorems above still hold | Proved (E6) |
| 2 | T-INDEX | The physical writer reads only slots, the pinned set, and maps bounded by the startup section (Rule R's, and the window of 8.5 if E1 adopts it), never a map from every node id | By the definitions, stated in E6 |
| 2 | — | INV-SLOT on Java's own physical states; the same streams with and without eviction | Checked (C-P, J4; EvictionInvariance, J2 to J4) |
| 3 | T13' (`T13_markTouch`) | With touches, step 3 marks the dirty index nodes not in D and the touched ones | Proved (R3) |
| 3 | T8 (`T8_recoverCut`) | After a safe cut, startup from the cut stream gives P at every available time, and D | Proved (R4) |
| 3 | T9 (`T9_readCut`) | After a safe cut, physical reads at available times read no record before the cut and give P | Proved (R4) |
| 3 | T12 (`T12_restartCut`) | Restarts from safe cut streams change no record; only the records before the cut are gone | Proved (R5) |
| 3 | T-SCHEME (`TS_safe`) | Java's scheme (the touch, the rewrites, the waits for pEnd and pSafe, f = tEnd) gives safe cuts | Proved under TouchCover (R6), or checked at every cut (C-CUT) if the proof stalls |
| 3 | — | Every Java cut is safe; every record of a reclaim run is the model's | Checked (C-CUT, C-S, R7, R9) |
| 4 | — | Java implements the physical layer | Checked: EvictionInvariance, the audits, C-P, the gates, the larger-than-memory run (J1 to J10) |

1.5 Scope
---------

In scope: everything needed for 1.2 at Levels 2 (lazy reading), 3 and 4:
the model, the checker and the exporter, the Java changes, the Level 4
implementation, its tests and gate, and the Level 3 validation that
[docs/level3-plan.md](../011-docs-archive/06-level3-plan.md) requires before Level 4
(the performance reference and the soak).

Out of scope (write ideas down in the progress entry; do not work on them):
protected snapshots (decision D1 = B of levels.md); exact value write times;
proofs of the bounds T3 and T4; a Lean model of the TopDs skip list
(F1-008-13; an optional later item); reclaim option B (F1-008-07, 6); a
second stream for cold data; replication with cuts; platforms other than
macOS and Linux; tuning beyond the targets of Q13; incoming-reference lists
for eviction, unless J10 shows the sweep is too slow.


2. Rules for agents
===================

2.1 Repositories and files
--------------------------

* **This item** (`items/001-lean-model-levels-3-4/`). Write
  [02-progress.md](02-progress.md) (the status table and new log entries),
  and the new subitems that WPs name (review guides, the final report), with
  their lines in the readme's Files and Log sections. Do not change this
  plan; if it is wrong or unclear, say so in your progress entry, and Frans
  edits it.
* **bergdb.** Read freely. After G0, write only where the WP says:
  `java/src/` (production code: WPs A3, R8 and J1 to J8; test-only hooks
  that do nothing when off: L5, R2, J4), `java/stress/` and `java/src-dev/`
  (tests and tools), `lean/`, `docs/`.
  * Commits: as Q2 says. Never push, rebase, reset, stash, or delete files
    you did not create.
  * Before writing, run `git status --short`. Every change listed must be an
    uncommitted output of an earlier WP, named in the progress log, or yours.
    If not, stop: someone else may be working there.
  * Do not weaken, remove or skip a step of a gate. New gate steps need
    Frans (K3, K4).
  * Test code in `java/stress/` must compile against the production code of
    the same work tree: `build.sh` compiles every file there, and every gate
    builds first.
  * Java 8 language level (`--release 8`). Follow the style of the
    surrounding code and documents: plain English, short sentences, comments
    that explain why.
  * A hook in production code for a test tool only if there is no other way;
    it must do nothing when off.
  * Do not edit a shell script while it runs; `sh` reads it as it goes.
    Replace it by a rename instead, as F1-008-11's F1 did.
  * Preserve unrelated work tree changes.
* **f1.** Read only. F1-008 is history for this plan.
* **Scratch.** Builds of other versions, experiments and large outputs go to
  the session's scratch directory, never into a repository. Changes to the
  trusted part of the model are developed in a scratch copy of `lean/` and
  brought into bergdb only when every Lean check passes there (F1-008-11, E3,
  did so).
* **Another agent on the same WP.** Use separate files (suffix `-claude`,
  `-codex`) and do not read the other's work until yours is done; then add a
  dated comparison.

2.2 When a WP is done
---------------------

A WP is done when its "Done when" list holds and these checks pass:

* **Changes to `java/src/`:** `level1.sh`, `level2.sh`, `level3.sh`, and
  `level4.sh` once it exists, full, one after the other. Quote the last line
  of each and the unit and f-test counts. Also the conformance checks that
  exist at that time, and, for a change that must not change the records,
  the byte comparison against `l34-base` (8.9).
* **Changes to `java/stress/` or `java/src-dev/` only:** `java/build.sh`
  passes; the unit tests pass if `src-dev` changed; a new tool runs on at
  least one small and one medium configuration (8.4).
* **Changes to `lean/`:** `lake build` passes with no warnings; `lake exe
  sistest 20 40` passes, and the stage's own random tests (`phystest`,
  `reclaimtest`) once they exist; `#print axioms` of every public theorem
  (the list in `lean/README.md`, which each WP extends) prints only
  `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit`,
  `axiom` or `unsafe` in `lean/SIS/` and `lean/Check/` (grep); `sh
  test-traces/run.sh` passes.
* **Documents:** the links resolve; statements about code cite file and
  method (and line, at a named commit).

If a check cannot be run, the WP is not done. Report it as "done except
<check>", with the reason and the command to run.

2.3 Lean
--------

* Lean 4 with the toolchain in `lean/lean-toolchain` (v4.34.1), core only,
  no Mathlib.
* The trusted part is the definitions and the theorem statements:
  `SIS/Basic.lean`, `Stream.lean`, `Algorithm.lean`, `Startup.lean`,
  `Assumptions.lean`, `Theorems.lean`, and the files this plan adds to it:
  `SIS/Phys.lean` and `SIS/PhysTheorems.lean` (L1, L2), `SIS/Evict.lean`
  (E2), `SIS/Reclaim.lean` and `SIS/ReclaimTheorems.lean` (R3). Change it
  only where a register row's resolution says "model", and list every change
  in plain English, with its reason, under "Changes to the trusted part" in
  `lean/README.md`.
* Keep the existing theorems; generalize, do not replace. The Level 2
  statements must still hold, as instances where needed.
* Pair every new trusted definition and theorem statement with a comment in
  plain English. Frans reads the statements, not the proofs, and is new to
  Lean.
* State a theorem first, check it by running on the examples and random
  runs, then prove it. A counterexample found by running is cheap; one found
  after a week of proof is not.
* The checker uses fast versions of the model's definitions only through
  proven equalities (C2). Code that is not proved equal is labelled
  checker-local and cross-checked.
* Without Mathlib there is no `set`, `by_contra`, `tauto`, `swap` (use
  `rotate_left`) or `conv_lhs`. `omega` does not see through `abbrev`
  aliases of `Nat`; the model uses `notation` for `NodeId` and `Time` so
  that it does; keep it that way. `cases h : e` generalizes `e` in the goal
  only; revert hypotheses that mention it first. F1-008-08's
  `lean/README.md` has more.

2.4 Stop and report
-------------------

Stop the WP, write the progress entry, and leave the rest for Frans, when:

1. a decision that section 4 marks open, or a checkpoint (section 3), is
   needed and the progress file does not record it;
2. a gate fails after your change and the fix is not clearly inside the WP;
3. the checker finds a mismatch that is not in the register and that you
   cannot explain within the WP: describe it, with the smallest
   configuration that shows it;
4. a proof needs an assumption that Java may not meet, or a change to the
   trusted part that the register does not list;
5. a change would alter the stream format, break existing databases, or
   change the public API or a default (Q4, Q10);
6. a WP takes more than twice the upper bound of its size, or stage 2 has
   used its time box (5.3);
7. what you find suggests that the direction of 1.1 is wrong, for example
   that Option K fails and only Option F, which changes the records, remains;
8. a run would need more than the machine allows (more than 100 GB of disk,
   a heap above 24 GB), or the machine is busy with Frans's work (the quiet
   check of `performance.sh` fails three times; never use `FORCE=1` for a
   reference).

Stopping early with a clear report is a good outcome. Pushing through with a
weaker claim is not. Stopping a WP is not stopping the session: go on with a
WP of another track that does not depend on it (5.2).

2.5 Evidence
------------

* Name the bergdb commit, and the uncommitted files (`git diff --stat`), for
  every run.
* Quote the commands and the decisive lines of their output. Keep full logs
  in bergdb's ignored `java/build/` directories or in scratch. Put short
  summaries in bergdb's `docs/evidence/` when a WP asks for them.
* Say for each claim whether it is proved (Lean, with the theorem's name),
  checked (which tool, which configurations, the counts), argued (where), or
  assumed.
* Give counts as they are: "0 of 3,000" and "3 of 3,000" are different
  results.

2.6 Progress entries
--------------------

Append to [02-progress.md](02-progress.md), newest last, and update its
status table and its current state (checkpoints, uncommitted files, long jobs
running, the time box):

    ### YYYY-MM-DD HH:MM to HH:MM. WP Xn, done | partial | blocked
    Agent: name, model, effort. bergdb at <commit>, uncommitted: <files>.
    Did: ...
    Files changed: ...
    Checks: <command>: <result>
    Register: <rows added, changed or closed>
    Open, next: ...

2.7 Environment
---------------

On Frans's Mac, 2026-10-16:

* JDK: `export JAVA_HOME=/opt/homebrew/opt/openjdk; export
  PATH=$JAVA_HOME/bin:$PATH` (OpenJDK 27). bergdb compiles with `--release
  8`: no Java 9 or later language features or APIs.
* Lean: `elan` and `lake` are in `/opt/homebrew/bin`.
* The machine: 10 cores, 32 GB of memory, about 680 GB of free disk.
* Times measured in F1-008-11 (2026-10-16): `level1.sh` about 1.5 minutes,
  `level2.sh` about 11 minutes, `level3.sh` about 5 minutes (full); `lake exe
  sistest 20 40` about 7 minutes; `conformance.sh small` 5 minutes 20
  seconds; `conformance.sh medium` 1 hour 53 minutes (before stage 0).
* The gates share `java/build/`, and `build.sh` deletes its outputs first:
  run them one at a time. To run a gate while another job uses `java/build/`,
  run it on a scratch copy of the work tree, as F1-008-11's F1 did.
* `java/stress/performance.sh` needs a quiet machine (90 percent idle):
  never with the gates, a full Lean build, the soak, or another agent's
  jobs.
* If a test hangs only in Claude's sandbox (`StorageManagerTester` did once,
  F1-008-11, 2.2), run it outside the sandbox with permission, or report
  "done except".
* Context: a session's conversation may be summarized during long work.
  Section 0 and the progress file are what carries the state; write the
  progress entry before a long job, not only after it.


3. Checkpoints for Frans
========================

| | When | Frans decides | Until then |
|---|---|---|---|
| G0 | Before any WP | Go for work in bergdb. Confirm or override the defaults of section 4, Q2 in particular | No WP starts. Reading is fine |
| K1 | After E7, the end of stage 2 | The Level 4 design: the reference rule (Option K or F), the Java changes of E7's list, any format change | R3 to R8 and all of stage 4 wait. K1 passes automatically if: Option K, every theorem of stage 2 proved, A6 and TREE hold on every Java run checked, and no format or public API change is needed. Meanwhile: R1, R2, P1 to P3, and the rest of stages 0 and 1 |
| K2 | After each WP that changes `java/src/` | Review and commit (Q2) | With Q2 (a), the next WP that changes the behavior of `java/src/` waits; other tracks go on, and test-only hooks that do nothing when off (L5, R2, J4) may go on top of uncommitted work. With Q2 (b) or (c), nothing waits |
| K3 | After R9, the end of stage 3 | Accept the Level 3 alignment; a conformance step in `level3.sh` | K3 passes automatically for J1 if: T8, T9 and T12 proved, T-SCHEME proved or checked at every cut, R9's conformance passes, and no Java change beyond E7's list was needed. Otherwise J1 waits. The new gate step always waits for Frans |
| K4 | After J10 | Level 4 in Java: eviction on by default (Q10); `level4.sh` as a required gate (AGENTS.md, README.md) | F1 to F3 may run; the defaults, AGENTS.md and README.md wait |
| K5 | After F3 | Accept the outcome of 1.2; what comes next | — |

An automatic pass (K1, K3) is recorded in the progress file, under Frans's
go and decisions, with the evidence that met the condition. For K1, K3, K4
and K5 the agent writes a review guide, a new subitem of this item: what to
decide, the evidence (theorem names, checks with their counts), the changes
(files, lines, why), how to reproduce the decisive checks, and the open
risks. Frans records each result in the progress file, or gives it in the
prompt. An agent that gets a go or a decision in the prompt writes it into
the progress file first, with the date and Frans's words.


4. Decisions and their defaults
===============================

Agents use the default unless the progress file records Frans's choice. G0
is the natural moment to confirm or change them.

| | Decision | Default | Why | Used in |
|---|---|---|---|---|
| Q1 | Where the model and the checker live | bergdb's `lean/`: extend the model in place; the Level 2 theorems stay as instances | Code, model and checker change together, as at Level 2 | All Lean WPs |
| Q2 | Commits | (a) Frans commits: the agent works uncommitted in the main work tree, and Frans commits at K2 (AGENTS.md). (b) The agent commits each finished WP whose checks passed, as a local commit on `main` (never pushes, never amends or rewrites history), with the attribution lines of the session, and lists the commits in the progress file. (c) As (b), on a branch `item-001` in a separate worktree (`git worktree add`), which Frans merges. **Default (a); recommended for long unattended runs: (b)** | With (a), every WP that changes `java/src/` waits for Frans; about ten do | K2, all Java WPs |
| Q3 | The reference rule for Level 4 | Option K: keep Level 2's rule (a version names the latest version of every pointee) and prove that Java can compute it from its slots and the pinned nodes, under A6 (8.5). Option F (F1-008-07's Rule F with a window and anchor logs) only if K fails, and then at K1 | K keeps the records, the format and today's databases, and the Level 2 alignment stays valid | E1 to E7, R8 |
| Q4 | Stream format | No change, unless a register row requires it and Frans agrees (K1 or K3). Then new databases only: the format byte bumped, older streams refused with a clear message, as F1-008-11's Q5 | Java has no external users; a changed format still needs a reason and a decision | Any Java WP |
| Q5 | The first available time f in the model | Records carry fa(i), which α derives from Java's reclaim table (the cut row's tEnd as stored at or before R(i)). Java keeps its table; that Java reads it after reconstruction (Codex's review of 09, finding 5) is settled by an argument (R1). If the proofs need f before reconstruction and the argument fails: a record field (Q4) | No format change; startup reads nothing before the cut anyway | R1, R3 |
| Q6 | The touch | Model Java's touch as it is: it marks nodes without adding entries (M17), and the cut waits for pEnd and pSafe (R6). A touch that adds entries only through K3 | Keeps node sizes and records; Codex's review of 09, finding 6, asks for this proof | R3 to R6 |
| Q7 | The first-touch rule | Stage 1 models Java's rule as it is: the canonical object, else the newest of the named version, the section's version and a table snapshot; section versions cut back to the startup time. For Level 4 (stage 2, R8): the canonical object, or the exact version the pointer names after Rule R; no cut-back after startup | Stage 1 proves today's Java correct; Level 4 needs a rule that does not depend on what readers left in memory | L1, E1, R8 |
| Q8 | Concurrency of eviction | Eviction runs only under the write lock, at transaction boundaries and in load-triggered batches; each slot changes under its pointer lock, which readers already take on every follow (`NodeCollection.followPointer`); a reader may finish with an object it holds; a load never asks for the write lock while it holds a slot lock. Not modeled in Lean; checked by deterministic interleaving tests and stress (J5). A Lean state machine of the slot (level4-plan 4.5.1) is optional | The smallest protocol that keeps today's reader path | J2 to J7 |
| Q9 | Eviction policy, first release | Clean, unpinned, written objects; values first, then index nodes; age by an access clock kept apart from the position field; a fair, complete sweep under pressure; no background thread; no incoming-reference lists unless J10 shows the sweep is too slow | As level4-plan.md, section 10 | J2 to J7 |
| Q10 | Memory budget and defaults | `cacheSizeInMb` (`DbBuilder.cacheSizeIndicator`, today without effect) becomes a soft target for evictable memory; pinned state is never evicted and is reported when it exceeds the target. Eviction on by default with the existing default: decided at K4. Until then on only where a test or benchmark asks for it | A default that changes memory and speed for every database is Frans's call | J7, K4 |
| Q11 | Readers and cuts | Keep D1 = A: an admitted read may expire; no protected snapshots | Frans's decision of 2026-10-13 | R3, R4, J5 |
| Q12 | Level 3 validation | Tasks 2 and 3 of level3-plan.md run as P2 and P1, on A1's code, before J1; P4 repeats the soak with eviction | level3-plan asks for them before Level 4; on today's code they validate Level 3 as it is | P1, P2, P4, J1 |
| Q13 | Performance targets for Level 4 | Against the Level 3 quick reference (P1), with eviction off and with a budget larger than the data: warm gets and scans within 10 percent (investigate above 5), commits within 10 percent, startup within 20 percent. Cold reads under pressure: measured, no target | level3-performance.md asks for "10 to 20 percent, by eye"; level4-plan proposes 5 | J10 |


5. Order of the work
====================

5.1 The order
-------------

| Order | WP | Title | Depends on | Size | Track |
|---|---|---|---|---|---|
| 1 | A1 | Baseline and environment | G0 | S | D |
| 2 | A2 | The registers, checked against the code | A1 | M | D |
| 3 | A3 | The TopNode ordinal defect | A1 | S | J |
| 4 | A4 | Probe H1: no adoption | A1 | S | M |
| 5 | P1 | The Level 3 quick performance reference | A1 | S | P |
| 6 | C1 | Profile the checker | A1 | S | M |
| 7 | C2 | Fast versions, proven equal | C1 | M | M |
| 8 | C3 | Larger sets and parallel runs | C2 | S | D |
| 9 | L2 | Lemma M | A1 | S to M | M |
| 10 | L1 | The physical layer, part 1: loading | A2 | M | M |
| 11 | L3 | Lazy startup and reads: T1-L | L1, L2 | M | M |
| 12 | L4 | The writer after a lazy startup: CC, T2-L | L3 | M | M |
| 13 | L5 | Lazy reading checked against Java | L3 (C2 for the medium set) | M | D |
| 14 | P2 | The Level 3 soak | A1 | M, plus 2 h or more of machine time | P |
| 15 | P3 | Bounds, measured | A1 | S to M | P |
| 16 | R1 | α and the register for reclaim | A2 | M | D |
| 17 | E1 | Design: eviction, references, pins | L1, A4 | M | M |
| 18 | E2 | The physical model with eviction, executable | E1 | M | M |
| 19 | E3 | INV-SLOT and the physical writer: T-CACHE | E2, L4 | L | M |
| 20 | E4 | Reads under eviction: T-READ | E2, L3 | M | M |
| 21 | E5 | Restarts with eviction: T2-C | E3, E4 | M | M |
| 22 | E6 | Pins and index-freedom | E3 | S to M | M |
| 23 | E7 | The Java change list; the K1 review | E3 to E6 | S | D |
| — | K1 | | E7 | | |
| 24 | R2 | Trace format 2; the exporter for reclaim runs | R1, C2 | M | D |
| 25 | R3 | The Level 3 model: touch, first available time, cuts | K1, R1 | M | M |
| 26 | R7 | The red list on Java's reclaim | R2, R3 | S | D |
| 27 | R4 | Recovery and reads after a cut: T8, T9 | R3 | M to L | M |
| 28 | R5 | Restarts across cuts: T12 | R4 | L | M |
| 29 | R6 | Java's scheme gives safe cuts: T-SCHEME | R3 | M to L | M |
| 30 | R8 | Java: the corrections the model requires, before eviction | K1, R7 | M | J |
| 31 | R9 | Level 3 conformance; the gate proposal | R5, R6, R8 | S | D |
| — | K3 | | R9 | | |
| 32 | J1 | Registry, pins and audits | R9, P1, P2 | M | J |
| 33 | J2 | Eviction of values | J1 | M | J |
| 34 | J3 | Eviction of index nodes | J2 | L | J |
| 35 | J4 | Eviction invariance; conformance with eviction | J3 | M | D |
| 36 | J5 | Readers under eviction | J3 | M | J |
| 37 | J6 | Reclaim under eviction | J3, J5 | M | J |
| 38 | J7 | The capacity controller | J4, J5, J6 | M to L | J |
| 39 | J8 | Larger than memory | J7 | M | J |
| 40 | J9 | `level4.sh` | J8 | S | J |
| 41 | J10 | Performance | J9, P1 | S to M | J |
| — | K4 | | J10 | | |
| 42 | P4 | The soak with eviction | J8 | M, plus machine time | P |
| 43 | F1 | The conformance campaign, all levels | J10, R9 | S to M | D |
| 44 | F2 | Documents | F1 | S | D |
| 45 | F3 | The final report | F2 | S | D |
| — | K5 | | F3 | | |

The sizes add up to about 80 to 380 hours of agent time, over many
sessions; F1-008-11's pace suggests the lower half. Frans's time goes into
the checkpoints.

5.2 Tracks and parallel work
----------------------------

* **M, the model**: A4, C1, C2, L1 to L4, E1 to E6, R3 to R6.
* **J, Java**: A3, R8, J1 to J10 (J4 is test tooling, track D).
* **D, documents and tools**: A1, A2, C3, L5, R1, R2, R7, R9, E7, J4, F1 to
  F3.
* **P, machine time**: P1 to P4.

When a checkpoint or a long proof blocks one track, continue on another.
Typical moments: while the medium conformance set or the soak runs, write
documents or proofs; while waiting for K1, do R1, R2, P1 to P3; while
waiting for a K2 commit, do Lean or tool work.

With two agents (allowed, not required): one on track M, the other on J, D
and P, following 2.1. Never run the gates while the other agent edits
`java/`; never change the trusted Lean files from both at once.

5.3 Stage gates and the time box of stage 2
-------------------------------------------

* **Stage 0 is done** when every fast version is proved equal to the
  model's definition (or marked "checked, not proved", as C2 allows) and the
  medium set takes under 15 minutes (or C2 records why not).
* **Stage 1 is done** when LM, T1-L, CC and T2-L are proved, C-L passes on
  the small and medium sets, and M8 is closed by proof.
* **Stage 2 is done** at K1: T-CACHE, T-READ, T2-C and T-PIN are proved for
  the chosen rule, A6 and TREE hold on every Java run checked, and E7's
  change list is written.
* **The time box of stage 2.** E1 to E7 add up to about 20 to 70 hours of
  agent time. The box is **60 hours**, counted from the start of E1 in the
  progress log. When it is used up, finish the WP in progress only if it is
  within 4 hours of done; then write the K1 review with what is proved, what
  is open, and the options (more time, a narrower claim, checks instead of
  proofs for the rest, or Option F), and wait for Frans. Also stop early, at
  any time, if A6 is refuted and no weaker property is found (E1), or if
  E2's random runs find a counterexample to Option K that E1 cannot repair
  within 8 hours.
* **Stage 3 is done** at K3: T8, T9 and T12 are proved, T-SCHEME is proved
  or checked at every cut, R9's conformance passes, and the gates pass.
* **Stage 4 is done** at K4: `level4.sh` passes; eviction invariance holds on
  every configuration; the larger-than-memory run passes; the performance
  targets are met or every miss is explained.


6. Work packages
================

Each WP has: goal, inputs, what to do, output, when it is done, and when to
stop, where that is special. Sizes are in section 5.1. Every WP that changes
`java/src/` ends with checkpoint K2 (section 3), whether or not it says so.

### A1. Baseline and environment (S)

Goal: a pinned, reproducible starting point, and the tool for the byte
comparison of 8.9.

Inputs: bergdb's `README.md` and `AGENTS.md`; `docs/levels.md` (Levels,
Level 2, Level 3); `java/stress/level*.sh`, `conformance.sh`;
`docs/performance-harness.md`, `docs/level3-performance.md`;
`lean/README.md`; F1-008-11's progress, entry A1.

Do:

1. Record bergdb's HEAD and `git status --short`.
2. Write `java/stress/StreamDigest.java` (8.9): the deterministic workloads
   of `RestartInvariance`'s configurations in `level2.sh` (step 4) and
   `level3.sh` (step 3, reclaim on), each run once without restarts,
   printing the SHA-256 of the stream from its first position. Use only API
   that this plan does not change (`DbBuilder.testSetup`, `Db`, `Trans`,
   `MemoryStream`, `CoreTestClock`), so that one compiled copy runs against
   both the preserved and the current jar.
3. Preserve the baseline build: `java/stress/performance.sh build l34-base`,
   after step 2. Record the digests of every configuration with it.
4. Run `level1.sh`, `level2.sh` and `level3.sh`, full, one after the other.
   Record the last lines, the times, and the unit and f-test counts.
5. Lean: `lake build`; `lake exe sistest 20 40`; the axioms check of
   `lean/README.md`; `sh test-traces/run.sh`. Record the summary of the
   conformance small set from `level2.sh`, step 7.
6. Read `docs/level3-plan.md`, tasks 2 and 3, and `docs/level3-performance.md`,
   and write down what P1 and P2 must still do.

Output: a progress entry with every result. In the repository:
`StreamDigest.java` only.

Done when: all of the above is recorded, and every failure is explained.

Stop if: a gate fails on the unchanged code.

### A2. The registers, checked against the code (M)

Goal: the two new documents, each with its scope and its register:
`docs/level4-alignment.md` and `docs/level3-alignment.md`.

Inputs: section 7 and 8.1 here; `docs/level2-alignment.md` (all);
`docs/level4-plan.md`, sections 2, 2.1, 4, 5.1 and 6;
`docs/reference-theory.md`, sections 2 to 7; Codex's review of 09, findings
2 and 4 to 7; F1-008-13, sections 5 and 5.1. Java, in `java/src/bergdb/`:
`core/Cache3`, `NodeCollection`, `DbStarter`, `Db` (`store`,
`getOneInternal`, `getMany`, `touchRange`, `markAtEndOfOp`, `endOfOp`,
`endOfTrans`, `getAccessData`), `DbHelper`, `TransSeq`, `Reclaim`, `Trans`,
`StoredKeyNode`, `StoredTopNode`, `DbBuilder`; `dag/Pointer`, `KeyNode` and
`TopNode` (the slot methods), `TopDs`, `Dag` (`handleFullNode` and the
splits), `GetMany`, `AccessData`; `storage/StorageManager`,
`BufferedStream`; `stream/FileStream`, `CutStream`,
`ReadBelowFirstPosException`.

Do:

1. Check every row of section 7 against the code at A1's commit: confirm,
   correct or close it, with file, method and line; add the rows you find.
   Level 4 rows (M20 to M31, M39, M40, M43, M44) go to
   `level4-alignment.md`, Level 3 rows (M17, M32 to M38, M41) to
   `level3-alignment.md`. M8 and M42 stay in `level2-alignment.md`, where
   stage 1 closes them.
2. Drafts of α for the cache (`level4-alignment.md`) and for reclaim
   (`level3-alignment.md`), from 8.1. L1, E1 and R1 complete them.
3. One-line pointers to the new documents from `docs/levels.md` (Level 3,
   Level 4, Next) and from `docs/level2-alignment.md` (M8, M17).

Output: the two documents; the pointers.

Done when: every row has a proposed resolution, a stage and a WP, and L1,
E1 and R1 have what they need.

### A3. The TopNode ordinal defect (S)

Goal: fix F1-008-13's finding (its section 5.1, register M30):
`StoredTopNode.toLongs` shifts the top node ordinal as an `int`, so the
32,769th top node and later ones are written wrong, and a database with that
many top nodes cannot be read.

Do:

1. A unit test that fails today: top nodes built through
   `TopDs.newSuperRoot` with ordinals 0, 1, 32,767, 32,768, 65,535, 65,536
   and `TopNode.MAX_TOP_NODE_ID_VALUE`, written and parsed with the
   production codec (`StoredTopNode`), comparing the ordinal, the skip slots
   and their cached times.
2. The fix: widen to `long` before the shift. Check the parser's own range
   checks.
3. Compatibility, in `docs/log.md` and the K2 note: streams with ordinals
   below 32,768 are unchanged; streams with more top nodes could not be read
   before.

Checks: the gates (2.2); the byte comparison of 8.9 (no change expected).

Output: the fix, the test, `docs/levels.md` (the bugs fixed), `docs/log.md`.
M30 closed.

Then K2.

### A4. Probe H1: no adoption (S)

Goal: test, before any model work depends on it, the structural property
that Option K needs (8.5).

Do:

1. The checker: two diagnostics for every transaction i, computed with the
   model's own `reachList`, `pointees` and the instance's `live`:
   * A6, no adoption: for every node x reachable at i, every pointee y of x
     that is not a live child of x at i is a data node or not reachable at i;
   * TREE: every node reachable at i, other than the root, is a live child
     of exactly one node reachable at i.

   Checker-local definitions in `lean/Check/Steps.lean`, reported as
   diagnostics: they do not yet fail a trace (E1 decides whether A6 becomes
   an assumption).
2. The Java tier: the same two checks in `A2A3Check2`, as new counters in
   its summary.
3. Run `conformance.sh small` and `medium`, and the Java tier on F1-008-11's
   21 configurations (level2-alignment.md, 10.5).

Output: the results in `level4-alignment.md`, section "Probes"; the progress
entry.

Done when: both checks ran on every set.

If A6 or TREE fails: record the smallest configuration and the kind of node
and change. Do not stop the other tracks. E1 must then find a weaker
property that still gives INV-SLOT, or prepare Option F for K1.

### C1. Profile the checker (S)

Goal: know where the checker's time goes before making it faster.

Do: in a scratch copy, time the checker's phases (parsing, C-A, the model's
`step` and its parts, the C-S comparison, the diagnostics) with
`IO.monoNanosNow`, on one medium trace (`m-long`, 500 transactions) and on a
long trace of the small kind (2,000 transactions, node size 8). Name the
model definitions that dominate, with their cost in nodes, versions and
records. Expected (F1-008-11, E3): `markOf` (quadratic in the nodes),
`reachList` and `reachable`, `Struct.get?` (list lookups), `Stream.lv`
(scans every record).

Output: a table in the progress entry. No repository change.

### C2. Fast versions, proven equal (M)

Goal: a much faster checker that still computes the model's own definitions.

Do:

1. For each dominant definition f of C1, a fast version f' and a Lean proof
   that it computes the same value. Either unconditionally, as `@[csimp]
   theorem f_eq : @f = @f'`, so that the compiled checker runs f' wherever
   the model calls f; or, where the fast version needs an index kept along
   the trace (a map from node id to the record of its latest version, the
   reachable set at i), as a checker step with a theorem of the form: if the
   index agrees with the state, the fast step's record and D are the model's,
   and the new index agrees with the new state.
2. Use core's `Std.HashMap` and `Std.HashSet` and their lemmas; no Mathlib.
3. The trusted part does not change. The fast versions and their proofs live
   in `lean/Check/` (or `lean/SIS/Fast/`, outside the trusted list).
4. Regression: on the small set, the checker's output before and after is
   the same apart from timing lines; `sh test-traces/run.sh` passes.

Targets: the medium set in under 15 minutes; a trace of 5,000 transactions
(node size 30, 1,000 keys) in under 10 minutes; at most 2 GB of memory.

Output: the fast versions and their proofs; `lean/README.md` (the checker's
fast paths, and that they are proven equal).

Done when: the Lean checks of 2.2 pass and the targets are met, or the best
reached is recorded with the reason.

Stop if: the proof for one definition takes more than about 12 hours. That
definition then stays slow, or gets a checker-local fast version that is
compared with the model's definition at runtime on a sample of calls; say
"checked, not proved" and go on.

### C3. Larger sets and parallel runs (S)

Do: `conformance.sh` gets a `large` set (8.4) and an option to check N
traces at once (default 4). Time the small, medium and large sets and
`level2.sh`'s step 7 again, and update the times in level2-alignment.md,
section 12, and in `docs/evidence/`.

Done when: all three sets pass, with their times recorded.

### L1. The physical layer, part 1: loading (M)

Goal: trusted Lean definitions of what Java holds in memory after a restart,
and of how it reads a node on first touch, as Java does today (Q7).

Inputs: level2-alignment.md, sections 2.9, 4 and 7.4 (M8); 8.6 here. Java:
`NodeCollection.followPointer`, `followStreamPointer`, `WriterFollower`,
`makeCanonical`, `resolvePointers`, `setStartupSection`; `Cache3.register`,
`makeCanonical`, `isBetter`; `DbStarter.doOrdinaryStartup` and the methods
it calls, `canonicalNode`, `topNodeOfLastTransaction`,
`findSuperNodeAtStartupTime`, `rerunTransaction`.

Do:

1. The design, as a new section "Lazy reading" of `level2-alignment.md`:
   objects (identity, node id, history, a slot per pointee: memory or
   stream), the node table, the canonical flag; the startup state (the
   section's newest versions registered canonical and cut back to the
   startup time; the objects of D's nodes by `canonicalNode`'s rule; the root
   chain from top(k)); the first-touch rule; the writer's follower; Rule R
   for the whole process (M42). What is left out (concurrency, access data,
   bytes), and why.
2. `lean/SIS/Phys.lean` (trusted, executable): the state and the operations
   (startup, follow, read at time t, the writer's follow), each with a
   comment in plain English. Import it in `SIS.lean`.
3. Examples with `#guard` checks (`lean/SIS/PhysExample.lean`): example 3
   (the virtual root), restarted and read in two different orders; a node
   whose section version is newer than its reference; a newer snapshot in
   the table; a node of D that the rerun does not reach.
4. The statements of L2 to L4, in plain English, in the design section. In
   Lean only once they are proved.

Output: the section; `Phys.lean`; the examples; `lean/README.md` (changes to
the trusted part).

Done when: `lake build` passes and the examples' checks pass.

### L2. Lemma M (S to M)

Goal: prove the monotonicity that Java's first touch relies on (M8).

Statement (`LM_newer`): in every run with the assumptions, after every
transaction: if a version v of node x is good for time t, with Rule R from
the startup pos s, and w is a version of x written at or after v, then w is
good for t with Rule R; and if w lies in R(s), ..., R(k) and t ≤ s, so is w
cut back to s.

Inputs: `SIS/Stream.lean` (`good`), `SIS/Startup.lean` (`follow`,
`readFrom`); `Proof/StreamLemmas.lean`, `Proof/Recon.lean`,
`Proof/Read.lean`.

Do: check it by running first (random v, w and t in random runs); then
prove it, by induction on the level, in `lean/SIS/Proof/Newer.lean`. State
it in `SIS/PhysTheorems.lean` (new, trusted statements).

Note: lemma M is a fact about the stream and does not need L1; it can start
right after A1.

Done when: the Lean checks of 2.2.

### L3. Lazy startup and reads: T1-L (M)

Goal: Java's lazy startup and first-touch rule, proved to read P.

Statement (`T1_lazy`): after startup from the stream of any run, or from any
prefix of it (a crash), and after any sequence of reads and writer follows,
a read at any time t up to the last record, through `Phys.lean`'s rule, gives
P@t of the run; every object it reaches is canonical with its node's whole
history, or a version that is good for the times at which its parents use
it.

Do: prove it from L2, L-OUT and L-SEC (`Inv.lout`, `Inv.recon`) and the
reading lemmas. First a random test (`lake exe phystest`, new in
`lakefile.toml`): random read orders after random restarts, compared with
`view`.

Done when: the Lean checks of 2.2; `phystest` passes 20 seeds.

### L4. The writer after a lazy startup: CC and T2-L (M)

Goal: the writer, working on Java's canonical objects after a lazy startup,
makes the model's changes.

Statements: CC (`CC_canonical`): every object that the writer's follower
makes canonical holds its node's whole history (that of the node in P).
T2-L (`T2_lazy`): a run with restarts that starts lazily, and whose writer
reaches nodes through the physical layer, appends the same records as the
run without restarts.

Do: prove both. Note in `lean/README.md` what T2-L does not cover yet: the
references the writer writes still come from `mkVersion` (`S.lv`); computing
them from slots is stage 2 (E3).

Done when: the Lean checks of 2.2.

### L5. Lazy reading checked against Java (M)

Goal: the checker tests Java's first touches after restarts against
`Phys.lean`'s rule.

Do:

1. `TraceExport`, run B: after each restart, record each first touch of a
   stream pointer as a FIRST line (8.2): the node, the record the pointer
   names after Rule R, the record or canonical object Java chose, and whether
   it was cut back. `followStreamPointer` overwrites the slot's position when
   it swizzles, so the exporter cannot see the named record from outside: add
   a test-only listener in `NodeCollection` that does nothing when off (2.1),
   unless a way without a hook turns up.
2. The checker: C-L, every FIRST line allowed by the rule. The trace format
   goes to version 2 (8.2); version 1 traces are still read. A test trace
   with a bad FIRST line in `lean/test-traces/`.
3. Export the cached times of top node skip slots (M29, SKIPT lines) and
   compare them in C-S with the target's time.
4. Run the small and medium sets. Record the results in
   `level2-alignment.md`; close M8 ("proved: LM, T1-L, CC, T2-L; checked:
   C-L") and M42; update `docs/levels.md` (Level 2, "Argued, not proved") and
   `lean/README.md` ("Not done").

Done when: `CONFORMANCE OK`, with C-L, on the small and medium sets.

### E1. Design: eviction, references, pins (M)

Goal: the design of the Level 4 model, settled as far as the evidence allows
before proofs.

Inputs: L1's design; A4's results; 8.5 to 8.8 here; `docs/level4-plan.md`,
sections 1 to 7 and 10; `docs/reference-theory.md` and `lean/References/`
(`Model.lean`, `SISCase.lean`); F1-008-07, sections 3, 4 and 8; F1-008-08,
sections 2, 9 and 10; Codex's review of 09, findings 2, 4 and 7.

Do:

1. The physical layer, part 2 (8.6): unswizzle (a memory slot becomes a
   stream slot naming the target's position); release (the node table
   forgets the object, and its canonical flag is cleared); eligibility
   (clean, not pinned, written; the pins of 8.6); the Level 4 loader (Q7);
   the physical writer (references from slots; Rule A by node id against the
   pinned set only); startup.
2. The reference rule (Q3): Option K's argument of 8.5 worked out on the
   definitions: INV-SLOT, and the assumptions it needs (A5, A6, TREE,
   BergDB's bookkeeping, D closed upward). Close the gap after restarts that
   8.5 describes (the window, or startup resolving D's slots), and search
   for other states where a slot that matters names an older version than
   lv(y): every way a slot changes (load, writer follow, split copy,
   unswizzle, restart) against every way lv(y) moves (a write of y). Check
   the result by hand on SISCase (A6 excludes it) and on the two component
   cases of level4-plan.md, section 2.1 (INV-SLOT, or R8's changes, exclude
   them).
3. The statements of 1.4, stage 2, in plain English. A6 and TREE as
   assumptions: where they go (`StepOK`, or a structure of their own).
4. What Java must change (the list for R8 and the J WPs), and what it keeps.

Output: `level4-alignment.md`, "The design"; the register rows updated.

Done when: E2 can implement the design and E3 to E6 can state their
theorems.

Stop if: A4 found A6 false and no weaker property gives INV-SLOT. Then write
the design for Option F instead and go to K1 early (stop rule 7).

### E2. The physical model with eviction, executable (M)

Goal: counterexamples before proofs.

Do:

1. `lean/SIS/Evict.lean` (trusted, executable): part 2 of the physical
   layer, as E1 designed it.
2. `phystest` extended: random transactions on examples 2 and 3 and on a new
   example 5 (8.6); random cache schedules (none; every eligible object after
   every transaction; each eligible object with probability 0.3); random
   reads at random times; random restarts. In every state, check: physical
   reads equal `view`; the physical writer's record and D equal `step`'s;
   INV-SLOT; at most one canonical object per node.

Done when: 20 seeds of 40 transactions with each of the three schedules
pass on every example; or a counterexample is found and explained in
`level4-alignment.md`, and E1 is revised (within the time box).

### E3. INV-SLOT and the physical writer: T-CACHE (L)

Statement (`TC_records`): in every run with the assumptions (A1 to A6,
TREE, those of the virtual root), and for any cache schedule (any sequence
of loads, reads, unswizzles and releases between transactions), INV-SLOT
holds after every operation, and every transaction of the physical writer
appends the model's record R(i) and leaves the model's D.

Do: prove it. Expect to need D closed upward (F1-008-08's T15) for BergDB's
bookkeeping in this model: prove it here if so. The checker's diagnostics
check it on every Java transaction today (F1-008-12).

Done when: the Lean checks of 2.2.

### E4. Reads under eviction: T-READ (M)

Statement (`TR_view`): from any state reachable as in E3, a physical read at
any time t up to the last record gives P@t.

Do: prove it from L3 (T1-L) and INV-SLOT.

Done when: the Lean checks of 2.2.

### E5. Restarts with eviction: T2-C (M)

Statement (`T2_cache`): a run with restarts, lazy startups and any cache
schedules appends the same records as the logical run; the physical state
after startup has INV-SLOT.

Done when: the Lean checks of 2.2.

### E6. Pins and index-freedom (S to M)

Statements: T-PIN (`TP_pins`): every clean object outside the pinned set of
8.6 may be evicted at any transaction boundary, and the theorems above still
hold; stated with Java's pinned set. T-INDEX: the physical writer reads only
slots, the pinned set, and maps bounded by the startup section (Rule R's,
and the window if E1 adopts it), never a map from every node id; a property
of the definitions, stated in `level4-alignment.md` with the Lean
definitions it rests on.

Done when: the Lean checks of 2.2.

### E7. The Java change list and the K1 review (S)

Output:

1. `level4-alignment.md`, "What Java must do": each change with its register
   row, its WP (R8 or J) and its check.
2. The K1 review guide, a new subitem of this item: what is proved (theorem
   names), what is checked (tools, counts), what is open, the decision
   (Option K confirmed, or Option F with its format change), and the
   estimated Java work.

Then K1.

### R1. α and the register for reclaim (M)

Goal: `level3-alignment.md`: what reclaim is in the model's terms, before the
model changes. R1 changes no model and no code, and may run before K1.

Inputs: `Reclaim.java` (the class comment, `transactionCompleted`, `step`,
`markSafePositions`, `pretruncateIfPossible`, `cutIfDurable`, `initFromDb`,
`storeTable`); `Db.putKvs` (the touch runs first), `touchRange`, `endOfOp`,
`endOfTrans`, `getOneInternal`, `getMany`, `expiredIfReadBelowCut`;
`DbStarter` after a cut; `NodeCollection.resolvePointers` (slots below the
cut); `StorageManager`, `BufferedStream`, `FileStream.pretruncate`,
`CutStream`; `docs/levels.md`, Level 3; Codex's review of 09, findings 2, 5
and 6; F1-008-07, sections 5 to 8; F1-008-08, section 2 (needed nodes).

Do:

1. α for reclaim (8.1): every executed transaction is a record (user
   transactions, reclaim steps, table stores); T(i) of a step is its value
   nodes (rewrites and the current row); touch(i) is the index nodes its
   touch marks; fa(i) comes from the table; a cut is decided at one record
   and made physically later; pStart, pCut, pEnd, pSafe, tStart and tEnd
   become records.
2. The arguments for M32 (Java's startup needs f only after reconstruction)
   and M38.
3. The register rows of A2, with Java's lines at the current commit.
4. The safety argument of levels.md ("Level 3: reclaim") rewritten in the
   model's terms (8.7), with every step marked: to prove (R4 to R6), checked,
   or assumed.

Output: `level3-alignment.md`, sections 1 to 6.

Done when: R2 and R3 have what they need.

### R2. Trace format 2 and the exporter for reclaim runs (M)

Do:

1. The format (8.2): TOUCH, FA, CUT and PHYSCUT lines; PROBE lines after
   cuts.
2. `TraceExport` with reclaim (as `RestartInvariance`'s `retain` option,
   with its scaled clock): a test-only hook in `Db.Internal`, called after
   every executed transaction, so that internal transactions get their own
   `TX` blocks; the nodes each touch marked (the got-dirty nodes that
   `touchRange` marked); cuts (decisions from the table, physical cuts from
   the stream's first position).
3. Run B: restarts at random points and right after each cut; lookups at
   random times from f on; the stream comparison from the cut.
4. The exporter's own checks: every stored position after the cut is the
   start of a version; every touched node is an index node of P.

Done when: traces of the small reclaim configurations (8.4) are written and
pass the exporter's own checks.

### R3. The Level 3 model: touch, first available time, cuts (M)

Goal: trusted definitions for Level 3 in `lean/SIS/Reclaim.lean`, on the
logical model and the physical layer. Depends on K1: it builds on E1's
physical layer.

Do:

1. The touch (M17): `Spec.touch` (none by default) gives the index nodes
   that transaction i's touch marks, as a function of T(i), i and P@(i-1);
   step 3 marks them with the access path of the change (Java marks the touch
   first, then the puts: `Db.putKvs`). TouchOK: the touched nodes are index
   nodes reachable at i before the change. T13 generalized: T13'.
2. fa(i) in `Record` (Q5): it never decreases and stays at most the time of
   the startup pos; reads before it are not required.
3. Cuts (8.7): `cutStream c S` (records before c keep the node ids and
   record numbers of their versions, and lose their histories and
   references); `CutOK c f`; runs with restarts from cut streams.
4. Examples: F1-008-07's example 4, adapted to a marking touch and the pSafe
   wait; a random test with cuts at the largest safe position (`CutOK` found
   by running), `lake exe reclaimtest`.

Done when: `lake build`; the examples; `reclaimtest` passes 20 seeds.

### R4. Recovery and reads after a cut: T8, T9 (M to L)

Statements: T8 (`T8_recoverCut`): after a safe cut, startup from the cut
stream gives P@t for every t from f to the last record, and D. T9
(`T9_readCut`): after a safe cut, physical reads at every time from f on read
no record before the cut, and give P@t.

Done when: the Lean checks of 2.2.

### R5. Restarts across cuts: T12 (L)

Statement (`T12_restartCut`): a run that restarts from safe cut streams, with
any cache schedules, appends the same records as the run without cuts and
restarts; only the records before the largest cut are gone.

Do: prove it. This is where M33 (slots below the cut whose target is in D)
and M34 (Java writes every taken node) are settled: by `CutOK` and a lemma,
or by a Java change for R8. A Java change needed here is stop rule 4: record
it, and K3 decides.

Done when: the Lean checks of 2.2.

### R6. Java's scheme gives safe cuts: T-SCHEME (M to L)

Statement (`TS_safe`): if an iteration's touches cover every index node that
is reachable at its end and has a version before pStart (TouchCover), its
rewrites cover every live value stored before pCut, f = tEnd, and the cut is
decided only after the startup pos has passed pEnd and then pSafe, then
`CutOK pCut tEnd` holds when the cut is decided.

Do: TouchCover is about key ranges, which the model does not have. Make it
an assumption, check it on Java's traces (C-A), and prove the rest.

Stop if: the proof stalls (stop rule 6). Then check `CutOK` at every cut of
every trace instead (C-CUT), state T-SCHEME as checked, not proved, and go
on.

### R7. The red list on Java's reclaim (S)

Do: the checker with R3's definitions on R2's reclaim traces (small and
medium), and the Java tier; classify every failure by register row, with the
smallest configuration for each. If every failure maps to a row, go on (as
F1-008-11's K1). Otherwise stop rule 3.

Output: `level3-alignment.md`, "Red list"; a summary in
`docs/evidence/level3-redlist-baseline.txt`.

### R8. Java: the corrections the model requires, before eviction (M)

Goal: the changes of E7's list and R7's red list in today's Java code, one
at a time, each with its own test and checks.

Expected, with Option K:

1. `NodeCollection.resolvePointers`: resolve by node id only against the
   pinned set (the nodes of D and of the record being written), Rule R and,
   if E1 adopts it, the window (8.5); no snapshot from the node table (M21,
   M26, M44).
2. Runtime loading: cut back to the startup time only during reconstruction
   (M22).
3. The loader: the canonical object, or the exact version the pointer names
   after Rule R; no newer snapshot (M27, Q7).
4. Slots: one capture of a slot's pair in `KeyNode.getPointer` and
   `TopNode.getPointer`; access data no longer kept in the position field,
   or updated only under the slot's lock with a recheck (M23, M24). The
   access clock becomes a field of its own, for J7.
5. Reclaim's maintenance reads: the scan and the per-KV reads neither
   register nor swizzle what they read (M28); where a slot's position gives
   the value's record, use it instead of loading the value (level4-plan.md,
   5.1, point 3).
6. Whatever R7 found.

Checks, for each change: the gates; **the byte comparison against
`l34-base` (8.9): the same stream in every configuration**, since Option K
changes no record; `conformance.sh small` and the reclaim set;
`performance.sh ab l34-base current` on a quiet machine, with no alerts, for
changes 1, 3 and 4.

Output: the changes; `docs/levels.md`, `docs/log.md`; the register rows
closed.

Then K2, per change or for the set, as Q2 says.

### R9. Level 3 conformance; the gate proposal (S)

Do: the small, medium and large reclaim sets (the Lean tier); the Java tier
with reclaim (`ReclaimStress`, `RestartInvariance` and `CrashTest` with
`retain`, with A4's checks); the gates. In `level3-alignment.md`: the outcome
of 1.2 for Level 3, point by point, and the proposal of a conformance step
for `level3.sh`, as level2-alignment.md's section 12 did for `level2.sh`.

Output: the K3 review guide (section 3).

Then K3.

### J1. Registry, pins and audits (M)

Goal: Java knows what is resident and what is pinned, and can check the
model's invariants on its own state. No eviction yet.

Inputs: E1's design and E7's list; `docs/level4-plan.md`, sections 4.1, 4.2
and 5; 8.8 here.

Do:

1. The resident registry: which objects are resident and their bytes:
   canonical objects, snapshots, objects of operations in progress.
2. Pins (8.6): the objects of D (`TransSeq`), of the record being written
   (`TransNodes`), the super root and the root chain as E1 decided, objects
   being loaded for publication.
3. Accounting (M40): byte estimates per object (arrays and values),
   advanced on load, growth and release; the access clock of R8.
4. A test-only audit, at transaction boundaries when a stress program asks
   for it (with `-ea`): the resident graph recomputed; one canonical object
   per node id; every pinned object resident and canonical; INV-SLOT for
   every resident canonical object, against a test-only oracle of latest
   positions read from the stream.
5. The audit as an option of `RestartInvariance`, `ReclaimStress`,
   `CrashTest` and `TraceExport` (off in the gates until J9).

Checks: the gates; the audit on every configuration of 8.4 without
eviction, with no failure; the byte comparison.

### J2. Eviction of values (M)

Do:

1. The eviction primitive (Q8, Q9): at a transaction boundary, under the
   write lock, each slot under its pointer lock: a memory slot to a clean,
   written value node becomes a stream slot naming the value's position;
   then the value object is released.
2. Admission: a new value becomes evictable once its record is written;
   large values are not kept (today's `CACHE_ALL_EXCEPT_LARGE_VALUE_NODES`).
3. Forced schedules for tests (8.4), as test options of `DbBuilder`.
4. `java/stress/EvictionInvariance.java`: the same workload with the
   schedules none, every and random gives the same stream (byte for byte),
   the same D and the same answers at random times; also with reclaim, and
   with restarts.
5. Unit tests: a value shared by two parents; a dirty parent that releases a
   clean value; a reload after release; a restart after release.

Checks: the gates; EvictionInvariance on the configurations of 8.4; the
audit.

### J3. Eviction of index nodes (L)

Do:

1. Clean, unpinned key nodes and top nodes become evictable: their parents'
   memory slots become stream slots naming their positions; release clears
   the node table's entry and the canonical flag (M31); the writer's follower
   makes a reloaded node canonical again.
2. Reload: the canonical object, or the exact version the slot names after
   Rule R (R8, change 3); top node skip slots keep their cached times (M29).
3. Tests, from `docs/level4-plan.md`, section 9: one child with several
   parents; an old snapshot and a newer canonical object; startup, updates,
   writeout, eviction; splits and root changes; a historical parent with a
   shared, updated child (example 5); reclaim with misses (`CutStream`);
   crashes after eviction (`CrashTest` with a schedule); restarts after
   eviction (`RestartInvariance` with a schedule).

Checks: the gates; EvictionInvariance with index eviction on every
configuration; the audit.

### J4. Eviction invariance and conformance with eviction (M)

Do:

1. `TraceExport`, run E: run A's workload with a forced schedule; its
   stream must equal run A's; SLOT lines (8.2) at transaction boundaries.
2. The checker: C-P, INV-SLOT on Java's physical states, with the model's
   own `lv` from the trace.
3. `conformance.sh`: an eviction set (small, medium, reclaim), checked with
   C-S, C-R and C-P.

Done when: `CONFORMANCE OK` on the eviction sets; EvictionInvariance passes
on every configuration.

### J5. Readers under eviction (M)

Goal: concurrent readers stay correct while slots change both ways
(`docs/level4-plan.md`, sections 4.5.1 and 6).

Do:

1. The protocol of Q8, in code and in a class comment.
2. Deterministic interleaving tests: a slot alternating between memory and
   stream while readers, the serializer, copying and array growth run; a
   reader's access-clock update racing an unswizzle, after which the
   position must have survived.
3. `ReclaimReaders` with a forced schedule (a new option); scans across
   chunks keep their actual snapshot; expiry stays the only allowed failure.

Checks: the gates; `ReclaimReaders` with eviction, `CutStream` and
`FileStream`, 0 failures in 100 rounds.

### J6. Reclaim under eviction (M)

Do: reclaim's maintenance reads (R8, change 5) under eviction; a reserve for
a step's pinned bytes, enforced as a hard cap (a step that would exceed it is
split; the `RerunException` path repeats it); reclaim's reads counted in
`Reclaim.Stats` (loads and bytes per iteration). Tests: `ReclaimStress` and
`LoadTest` with reclaim and a forced schedule. A measurement: the hit rate
of a hot set before and after an iteration.

Checks: the gates; the tests above.

### J7. The capacity controller (M to L)

Do (Q9, Q10; `docs/level4-plan.md`, section 5): a soft target from
`cacheSizeInMb`; high and low watermarks; an incremental, fair sweep at
transaction boundaries, and load-triggered batches that take the write lock
only when they hold no slot lock; age from the access clock; a complete sweep
under pressure; bytes of released but still referenced objects bounded;
pinned state never evicted, and reported when it is above the target;
metrics (resident, pinned and evictable bytes, loads, evictions).

Tests: reads with no writes (memory stays bounded); scans; large puts;
stalled readers; pinned state above the target (no partial change, no
deadlock).

Checks: the gates; EvictionInvariance with the controller instead of the
forced schedules.

### J8. Larger than memory (M)

Do: on disk (`FileStream`), in a capped JVM (for example `-Xmx2g` with a
budget of 500 MB), a database of at least five times the budget whose index
alone is at least twice the budget: uniform and hot updates, gets, scans,
reclaim on, cold restarts; every key checked at the end and after each
restart; memory sampled every second. A report in docs (a new
`docs/level4-evidence.md`, or a section of `levels.md`): memory, throughput,
cold and warm reads, startup.

Done when: memory stays below the JVM's cap with margin over the whole run,
every check passes, and the report is written.

### J9. `level4.sh` (S)

Do: `java/stress/level4.sh`, built like the other gates: the unit tests
(with the eviction tests); EvictionInvariance; `RestartInvariance`,
`CrashTest`, `ReclaimStress` and `ReclaimReaders` with forced schedules and
the audit; the eviction conformance set; a larger-than-memory run of a few
minutes. It prints `LEVEL 4 OK`. About 20 minutes full, 3 quick.

Done when: it passes, full and quick, and `docs/levels.md` describes it.

### J10. Performance (S to M)

Do: on a quiet machine, `SUITE=quick java/stress/performance.sh ab l34-base
current`, twice: with eviction off (`noEvict`), and with a budget larger than
the data (eviction on, no pressure). Compare with Q13's targets. Then one run
under pressure (a budget of a fifth of the data), reported without a target.
Results in docs (`level3-performance.md`'s table extended, or a new
`docs/level4-performance.md`).

Output: the K4 review guide (section 3).

Then K4.

### F1. The conformance campaign, all levels (S to M)

Do, on the final code and model: the Level 2 sets; the reclaim sets; the
eviction sets; the Java tiers; EvictionInvariance; the four gates in full,
one after the other, on a scratch copy of the final work tree. Evidence in
`docs/evidence/level34-conformance.txt`.

### F2. Documents (S)

Do: `level3-alignment.md` and `level4-alignment.md`: the outcome of 1.2,
point by point (as level2-alignment.md, section 11). `docs/levels.md` (Levels
3 and 4: status, how they work, evidence; Next); `README.md` (the status
table, after K4); `docs/sis-model.md` (the physical layer, reclaim);
`lean/README.md` (the trusted part, the theorems, how to run the new tests);
`docs/problem.md` (its requirements R5 and R6, and Q10);
`docs/level4-plan.md` and `docs/reference-theory.md` (a status note at the
top: what this item settled, and where); `docs/log.md`. The proposed change
to `AGENTS.md` (four gates), for Frans.

### F3. The final report (S)

Do: a new subitem of this item, as F1-008-12 was for F1-008-11: summary; the
outcome point by point; what changed in Java, in the model and in the tools;
findings; where the work differs from the plan; what Frans decides at K5.

Then K5.

### P1. The Level 3 quick performance reference (S, on a quiet machine)

Task 3 of `docs/level3-plan.md`. Do: `java/stress/performance.sh quick` on
A1's code (after task 1) on a quiet machine; `promote` as
`quick-YYYY-MM-DD-post-task1`; update `docs/level3-performance.md` and name
the reference in `docs/level4-plan.md`, step 0. If the quiet check fails
three times over a day, record it and try again later; never force. Must be
done before J1.

### P2. The Level 3 soak (M, plus at least 2 hours of machine time)

Task 2 of `docs/level3-plan.md`. Do: `java/stress/Soak.java` and `soak.sh`
(reuse `PerfUtil`'s histograms and GC log reader): `FileStream` in a
disposable directory; wall-clock retention; the pilot of level3-plan (one
million keys, 1,000-byte values, a retention of five minutes, one writer, two
to four readers; or a documented smaller scale); at least two measured
hours, ten physical cuts and three cold restarts; every operation checked at
its actual snapshot. Report in `docs/level3-soak.md`. During the measured
hours: no gates, no performance runs, no full Lean builds (2.7). Must be
done before J1.

### P3. Bounds, measured (S to M)

Do: with workloads like `LoadTest`'s (uniform, hot, 40-key transactions, one
million keys): the length of the startup section against the startup
distance (problem.md's requirement R3 and its Q4); the size of D in nodes
and bytes over time (the memory that Level 4 cannot evict); and how often
the conservative still-dirty test writes nodes that are not current
(sis-model.md, section 11). Report in `docs/levels.md`, "Bounds, measured";
input for J7's reserve.

### P4. The soak with eviction (M, plus machine time)

After J8: P2's soak with eviction on and a capped heap; compare memory and
pauses with P2. Report in `docs/level3-soak.md` or the Level 4 evidence.


7. The register, initial
========================

To be checked and completed in WP A2 (section 6). "Java" names classes and
methods in `java/src/bergdb/`; "model" names definitions in `lean/SIS/`.
M1 to M19 are in [docs/level2-alignment.md](../011-docs-archive/11-level2-alignment.md),
section 6; M8 and M17 are reopened here.

| | Mismatch or open question | Java | Model | Proposed resolution | Stage, WP |
|---|---|---|---|---|---|
| M8 | First touch after a restart is lazy; the model reads all of P at startup (lemma M). Argued and checked at Level 2 | `NodeCollection.followStreamPointer`; `DbStarter.canonicalNode` | `Startup.baseStruct` | Model: the physical layer, part 1; LM, T1-L, CC, T2-L; checked by C-L | 1: L1 to L5 |
| M17 | Reclaim's touch marks nodes without adding entries | `Db.touchRange`, `endOfOp(true)`; `endOfTrans` skips touch transactions | step 3 (`markOf`) | Model: `Spec.touch`, T13' | 3: R3 |
| M20 | With eviction, the writer cannot find lv(y) for a dead pointer without a table of all nodes (reference-theory.md, 5.1; `SISCase.lean`) | `NodeCollection.resolvePointers`; `Cache3` | `mkVersion` (`S.lv`) | Option K: A6 and INV-SLOT, references from slots (8.5); fallback Option F | 2: A4, E1 to E6; K1 |
| M21 | `resolvePointers` may take a newer snapshot from the node table, so the reference written depends on what readers left in memory (level4-plan.md, 2.1, second case) | `NodeCollection.resolvePointers` (`usable`) | — | Code: resolve by id against the pinned set and Rule R only; INV-SLOT says the result is lv(y) | 2, 3: E1, R8 |
| M22 | A runtime load of a version in the original startup section is cut back to the startup time (level4-plan.md, 2.1, first case). Not reachable today (every section node has a canonical object); reachable with eviction | `NodeCollection.followStreamPointer` (`toPreviousState`) | — | Code: cut back only during reconstruction | 3: R8 |
| M23 | A memory slot keeps access data in its position field, so the slot's position is lost while it is swizzled | `KeyNode.pos`; `TopNode.pointersPos`, `rootPointerPos`; `setPointerAccessData`; `AccessData` | — | Code: unswizzle writes the target's position; the access clock kept apart, or updated under the slot lock | 3, 4: R8, J1 |
| M24 | Readers of a slot's pair assume that a memory pointer stays one (lock-free fast paths; `TopNode.getPointer` reads the reference twice) | `KeyNode.getPointer`, `TopNode.getPointer`; asserts in `setPointerAccessData` | — | Code: one capture; defined behavior for an evicted slot (level4-plan.md, 4.5.1) | 3, 4: R8, J5 |
| M25 | `Cache3`'s reference counts are unbalanced: `pointerDestroyed` has no caller | `Cache3.pointerCreated`, `pointerDestroyed` | — | Not used for eviction; the registry and the sweep instead (Q9) | 4: J1 |
| M26 | `Cache3` holds every node ever read (canonical objects and snapshots), for readers and the writer | `Cache3`; `NodeCollection` | — (P is logical) | Physical layer: the table holds resident objects only; the writer needs only the pinned ones (T-INDEX) | 2, 4: E1, J1, J3 |
| M27 | Readers swizzle slots to objects that may be newer than the slot's reference (Rule R, a canonical object, a snapshot) | `NodeCollection.followStreamPointer` | — | Model: allowed by LM (stage 1). Level 4 loader: the canonical object or the exact version (Q7) | 1, 2, 3: L1, E1, R8 |
| M28 | Reclaim's scan reads through the ordinary path at tStart: it swizzles and registers what it reads | `Reclaim.step` (`GetMany`, `getOne`) | — | Code: maintenance reads (no admission, no swizzle) | 3, 4: R8, J6 |
| M29 | Top node skip slots cache the target's time (`pointersTime`); the trace does not export it (F1-008-13, 5) | `TopNode.pointersTime`; `TraceExport.topEntries` | entries `skip` | Trace: SKIPT lines; checker: equal to the target's time; kept on unswizzle | 1, 4: L5, J3 |
| M30 | Top node ordinals of 32,768 and more are written wrong (F1-008-13, 5.1) | `StoredTopNode.toLongs` | — | Code fix | A3 |
| M31 | One canonical object per node id must survive release and reload | `Cache3.makeCanonical`; `isCanonical` flags | Phys: the node table | Model and code: release clears the table's entry and the flag; the writer makes a reloaded node canonical | 2, 4: E1, J3 |
| M32 | Java keeps the first available time in the reclaim table, a value in the database, and reads it after startup (Codex's review of 09, finding 5) | `Reclaim.initFromDb`, `pretruncateIfPossible` | — | Model: fa(i) in records, by α (Q5); an argument that Java's startup needs f only later | 3: R1, R3 |
| M33 | After a cut, Java cannot read the id of a slot's target below the cut, and `resolvePointers` skips such slots (finding 2) | `NodeCollection.resolvePointers`; `StoredKeyNode` (positions only) | `javaTest` (by id) | Model: version stubs keep positions; CutOK must imply that no such slot of a node in D names a node in D; otherwise a code change | 3: R3 to R5 |
| M34 | Java writes every taken node, also nodes that no lookup from f on reaches (F1-008-08's "needed" nodes) | `Db.store`, `TransSeq.take` | step 6 | Model: show that it changes no record after a safe cut (T12), or a needed test in code | 3: R5 |
| M35 | A cut is decided (in the table) before it is made (when durable); `FileStream` deletes whole files; `CutStream` refuses reads below the cut | `Reclaim.pretruncateIfPossible`, `cutIfDurable`; `FileStream`; `CutStream` | `cutStream` | α: the model's cut is the decided position; the physical cut comes later, at the same or a lower position | 3: R1 |
| M36 | Reads before f are refused, and an admitted read may expire (D1 = A) | `Db.getOneInternal`, `getMany`, `expiredIfReadBelowCut` | `view` (every time) | Model: reads required from f on; expiry is concurrency, outside the model | 3: R3 |
| M37 | Reclaim stores its table and current row as values under internal keys, in internal transactions, with a value transformation | `Reclaim.storeTable`, `step` | T(i) | α: ordinary puts; T(i) is what the record stores | 3: R1 |
| M38 | A reclaim step can fail with a `RerunException` and then writes no record | `Reclaim.step` | — | α: no transaction; nothing to model | 3: R1 |
| M39 | Eviction beside concurrent readers | — | — (sequential) | Java protocol (Q8) and its tests | 4: J5 |
| M40 | Memory accounting is not implemented: `Cache3.totalSize` and `putSize` do not move; access data is `-putSize` | `Cache3`; `Db.getAccessData` | — | Code | 4: J1, J7 |
| M41 | After a restart from a cut stream, startup reads D's nodes at their stored positions and the root chain from topPos | `DbStarter.canonicalNode`, `topNodeOfLastTransaction`, `findSuperNodeAtStartupTime` | `startup` | CutOK must cover them | 3: R3 to R5 |
| M42 | Rule R applies for the whole process, also to nodes written after startup | `NodeCollection.section` | `follow` (startup only) | Model: Rule R in the physical loader (L1); an argument that it agrees with the latest-version rule | 1: L1, L5 |
| M43 | Option K relies on A6 (no adoption) and TREE (one current parent), which the model does not assume today | `Dag.handleFullNode` and the splits; `TopDs.newSuperRoot` | `StepOK` | Checked on Java (A4); assumption in the model (E1) | 2: A4, E1 |
| M44 | After a restart, a node of D can hold a stream slot to a node of D that is written before it; today the node table gives the newer version, with eviction nothing does (8.5, the gap) | `DbStarter.canonicalNode`; `NodeCollection.resolvePointers` | — | Model and code: the window (Rule R at runtime for the records after the previous startup pos), or startup resolving D's slots against D | 2, 3: E1, R8 |


8. Technical notes
==================

8.1 α for the cache and for reclaim (proposal)
----------------------------------------------

To be checked and completed in A2, L1, E1 and R1.

The cache, the physical layer (8.6):

* **Object**: a Java `Node` object, by identity. Its node: α of `getId()`
  (2.2 of level2-alignment.md). Its history: as 2.4 there, from the object's
  own klongs or fields, up to its own size.
* **Slot**: for each pointer of the object, memory (the object in
  `pointers[i]`, `rootPointer`) or stream (the record of the version at the
  slot's position, or none for a vpos). The serialized reference of a slot:
  the target's latest position for a memory slot to a canonical object, the
  target's own position for a memory slot to a snapshot, the slot's position
  for a stream slot; Rule R applies where the startup section (or, with
  Option K, probably the window of 8.5) has a newer version.
* **Canonical**: `Node.isCanonical()`. **The node table**: `Cache3`'s entries.
* **Pins**: the objects of D's nodes (`TransSeq`), those of the record being
  written (`TransNodes`), the super root (`TopDs.superRoot`) and whatever
  root chain E1 pins, objects of an operation in progress.

Reclaim:

* Every executed transaction is a record: user transactions, reclaim steps
  and table stores (`Reclaim.storeTable`). A step that fails with a
  `RerunException` writes nothing.
* T(i): the stored value nodes with their keys, as at Level 2: for a step,
  the rewritten values and the current row.
* touch(i): the index nodes that `Db.touchRange` marked in transaction i
  (`Trans.touch`, `touchFrom`, `touchTo`).
* fa(i): the first available time as of R(i): the tEnd of the newest row
  marked cut in the table as stored at or before R(i), as a model time (2.1
  of level2-alignment.md); 0 before the first cut.
* A cut decided at R(i): c is the record that starts at that row's pCut;
  f = fa(i). The physical cut: the stream's first position, later, at or
  below the start of R(c).
* pStart, pCut, pEnd and pSafe are stream positions at record boundaries:
  each maps to the record that starts there. tStart and tEnd map to model
  times.

8.2 The trace, version 2
------------------------

Version 1 (level2-alignment.md, section 9), plus:

    TRACE 2                      the format version; version 1 traces stay valid
    SKIPT j t                    after a top node's H lines: skip slot j caches time t
    TOUCH x1 x2 ...              in TX i, after the ADD lines: the nodes T(i)'s touch marked
    FA t                         in TX i: fa(i), as a model time
    CUT c t                      in TX i: Java decided a cut: records before c may go,
                                 first available time t
    PHYSCUT c                    in TX i: the stream's first position moved to R(c)
    FIRST x n r kind cut         run B, after a restart: a first touch of node x through a
                                 pointer naming record n after Rule R; Java took record r
                                 (or - for a canonical object); kind is canonical, version
                                 or snapshot; cut is 1 if it was cut back to the startup time
    SLOT x y r                   run E, at the end of TX i: the resident canonical object of
                                 node x serializes record r (or -) for its pointee y

The order within `TX i` stays as in version 1; new lines come after the
lines they refer to. Sorted wherever the order carries no meaning.

8.3 The checker, for Levels 3 and 4
-----------------------------------

**The Lean tier** (exact, for small and medium runs):

* **C-A**, the assumptions: as at Level 2, plus A6 and TREE (A4, then E1),
  TouchOK and, where the trace allows, TouchCover (R3, R6).
* **C-S**, the steps: the model's step for every record, internal
  transactions included; after a cut, on the cut stream.
* **C-CUT**: `CutOK` at every CUT line.
* **C-V**, as at Level 2.
* **C-R**, the restarts: as at Level 2, plus probes after cuts.
* **C-L**: every FIRST line follows the first-touch rule (L5).
* **C-P**: INV-SLOT on Java's physical states (SLOT lines, J4).
* Diagnostics: D closed upward; INV-2 (with `--inv`).

**The Java tier** (for sizes the Lean tier cannot reach): `A2A3Check2` with
A6 and TREE; `RestartInvariance` with `retain` and with eviction schedules;
`EvictionInvariance`; the audits of J1; `StreamDigest` against `l34-base`.

8.4 Configurations
------------------

* **Level 2**: the small and medium sets of level2-alignment.md, 10.5; a
  large set (C3): node sizes 8 to 62, 1,000 to 5,000 transactions, up to
  3,000 keys.
* **Reclaim, small**: node sizes 8 and 14; 30 to 200 keys; 300 to 800 user
  transactions at a startup distance of 200 to 1,000 bytes and a retention of
  1 to 2 s on `RestartInvariance`'s scaled clock, so that several cuts happen;
  deletes 0 and 25 percent; long keys; probes every 10 transactions and right
  after each cut; five configurations of five seeds.
* **Reclaim, medium**: node sizes 8 to 30, 500 to 3,000 keys, 2,000 to 5,000
  user transactions.
* **Reclaim, large** (the Java tier): `ReclaimStress`'s random
  configurations.
* **Eviction schedules**: none; every (every eligible object after every
  transaction); random (each eligible object with probability 0.3, seeded);
  values only (J2); the controller with a budget (J7).

Every set includes transactions that change nothing (empty ones and deletes
of missing keys), as at Level 2. Record the time and memory of each run.

8.5 The reference rule: Option K and Option F
---------------------------------------------

**The question.** The model's `mkVersion` names lv(y), the latest version,
for every pointee y, live or dead. Java does the same today because
everything stays in memory: `resolvePointers` finds y's canonical object by
id in the node table. With eviction, the canonical object of a clean node
may be gone, and a table of every node's latest position is excluded: it
grows with the database. reference-theory.md (5.1) proves that a dead
pointer's old reference and the recent tail do not determine lv(y) in
general, and `lean/References/SISCase.lean` is an abstract run where it
matters.

**Option K: keep the rule, and show that Java's slots already hold lv(y)
wherever it matters.**

* Hypothesis H1 (A6, no adoption): in BergDB's Dag, a pointer that stops
  being live in a node that stays current points to a node that stops being
  current (replaced by a split, or under a deleted key), or to a value node.
  Splits make new nodes (`Dag.timeSplit`, `spaceSplit`; the in-place splits
  of D1 change only nodes of the same transaction, which no lookup sees
  before it ends), and a node never hands a child to another current node.
  SISCase's move of Y from P to Q is such an adoption. TREE: every current
  node has one current parent (sis-model.md, section 11).
* The invariant INV-SLOT: for every resident canonical object x and every
  pointee y of x, the slot's serialized reference (8.1) is lv(y), unless y is
  pinned (then the writer finds it by id), or x is neither current nor in D
  (then x is never written again: step 3 marks only current nodes, and Rule
  A puts back only taken ones).
* Why it may hold (a sketch, to be proved in E3):
  * A live slot of a current node x: by TREE, x is y's only current parent.
    y is written only after being in D, and gets into D only through a change
    below it, marked through x (reclaim's touch too goes through x), which
    makes x's slot a memory slot to y's canonical object; D stays closed
    upward, so x is in D while y is. When y is written, its position moves
    with it; when y is evicted later, x's slot gets y's position, which is
    lv(y).
  * A dead slot of a current node x: by A6, y is not current, or is a value.
    A value has one version. A node that is not current is written again
    only while it stays in D, and while y is in D, Rule A (over every
    pointer, dead ones too) keeps x in D; so x is written after y's last
    write.
  * A historical node x still in D, with a child y that it shares with its
    replacement: when y gets dirty again through its new parent, x has the
    smaller got-dirty index, so x is taken no later than y: it sees y in D
    when taken (Rule A by id against the pinned set), or is written in the
    same record after y.
  * A historical node that is not in D is never written again. Its slots do
    not matter for records; for reads, its versions are good for the times
    its parents use them (LM, T1-L).
* **A gap in this sketch, found while writing the plan: restarts.** After a
  restart, the objects of D's nodes come from the stream, so their slots are
  stream slots. Let x and y both be in D, with d(y) < d(x) (Rule A put x
  back while y was in D), and x's slot naming y's version of that time. y is
  taken first and written; it is then clean, and may be evicted; when x is
  taken, its slot names an older version than lv(y), and y is not pinned.
  Today the node table still holds y's canonical object, so
  `resolvePointers` writes lv(y); with eviction it would not, and the record
  would depend on the cache. The candidate fix keeps the rule: a **window**,
  Rule R carried on at runtime: a map from node id to the newest position of
  every index node written in the records after the previous startup pos,
  s(i-1), bounded like the startup section, consulted by `resolvePointers`
  for stream slots. When x is taken in transaction i, y's write lies in that
  window: it came after the restart, so after d(x), and d(x) > s(i-1), since
  x was not taken before transaction i. F1-008-07 has the same
  window (its Rule F, with s0) and Codex's review of 09, finding 7, says
  which frontier to use. The alternative: startup resolves the slots of D's
  objects against D by id. E1 must settle this, and look for more such
  cases.
* What Java must do for it (R8, J): unswizzle writes the target's position;
  the writer's follower makes the object it reaches canonical and swizzles
  the slot to it (as today); `resolvePointers` resolves by id against the
  pinned set, Rule R and, if E1 confirms it, the window only; no cut-back
  after startup; release clears the canonical flag.
* What would refute it: an A6 or TREE failure on a Java run (A4, C-A); a
  counterexample in E2's random runs; a Java run whose stream changes with
  the eviction schedule (J2 to J4); a byte difference against `l34-base`
  after an R8 change.
* What it gives: the record format and the bytes stay as they are;
  databases written today stay readable; the Level 2 alignment stays valid;
  and the byte comparison of 8.9 checks every Java change before eviction.

**Option F: F1-008-07's Rule F.** A dead pointer keeps the reference of its
node's previous version, unless the child's newest version is in the window
(the records of the current startup section); live pointers name lv(y) as
found on the access path; a log of anchors in every record restores the
writer's state after a restart. Proved in F1-008-07 (with the exact
still-dirty test) and F1-008-08 (with BergDB's bookkeeping), in models that
drifted from Java. It changes the records (dead pointers keep old
positions), the format (the anchor log) and every stream's bytes: Q4, K1.
Port it only if Option K fails.

8.6 The physical layer (sketch, for L1 and E1)
----------------------------------------------

State, beside the logical ⟨P, D, S⟩:

* objects: identity, node id, history, canonical or not, and per pointee a
  slot: memory (an object) or stream (a record, or none);
* the node table: from node id to an object;
* the startup section's map (Rule R) and the startup time; with Option K,
  probably the window (8.5);
* pins: the objects of D's nodes, of the record being written, the super
  root at the current time and the root chain Java keeps (E1 decides which),
  and objects of an operation in progress.

Operations: startup (lazy, L1); follow (first touch: Java's rule in L1, the
Level 4 loader in E1); read at time t; the writer's follow (makes
canonical); a transaction's change applied to canonical objects; writing
(versions from canonical objects, references from slots); unswizzle;
release.

Invariants: INV-CAN (at most one canonical object per node, holding its
node's whole history; the node table names it; every pinned node has one),
INV-SNAP (every other object is a version from S, or such a version cut back
to the startup time during reconstruction), INV-SLOT (8.5).

Keep it sequential: every operation is atomic; concurrency is Java's (Q8).

Example 5, for E2 and J3: a historical parent that shares a child with its
replacement, the child then updated, written and evicted, the historical
parent still in D; a node replaced while in D; two root changes in one
transaction; a delete of a long key whose segment subtree then goes cold.

8.7 Level 3: what makes a cut safe (sketch, for R1 and R3 to R6)
----------------------------------------------------------------

Java's scheme (levels.md, "Level 3: reclaim"): an iteration has tStart,
pStart and its cut point pCut (the previous iteration's pStart); its steps,
at times up to tEnd, rewrite every live value stored before pCut (new value
nodes, so new entries in their leaves) and touch the key range of the step
at the step's time (every index node the range traversal follows gets
dirty); together the ranges cover every key. The cut at pCut waits until the
startup pos has passed pEnd (every touched node has been taken and written),
then pSafe (a parent written before its child and kept in D by Rule A has
been written again), until tEnd is older than R, and until the last valid
meta block names a transaction at pCut or later. Then f = tEnd.

`CutOK c f` (to define in R3), roughly:

1. c ≤ the record of f ≤ s;
2. every node reachable at some time from f on has its latest version at c
   or later, or none;
3. every node in D has its latest version at c or later, or none, and no slot
   of a node in D below c names a node in D (M33);
4. top(k) and the root children that reads from f on need are at c or later.

Version stubs: `cutStream c S` keeps, for the records before c, the node ids
and record numbers of their versions and drops their histories and
references. Java likewise keeps positions in its slots and loses the bytes.
The writer then computes the same references on the cut stream (it never
needs a stub's content), and the logical step on a stub-cut stream equals the
step on the whole stream when step 3 marks.

Why it may hold: nodes reachable at tEnd were touched at their step and
written after it, or were created later; values live at tEnd are at pCut or
later, or were rewritten; pSafe covers parents written before their
children. Nodes not reachable from f on that are still in D (historical
nodes that Rule A keeps in D) are the delicate case (M33, M34): R5 must show
that they are written again after c, or need no reading.

8.8 Level 4 in Java (sketch, for E7 and the J WPs)
--------------------------------------------------

* Where the changes go: `NodeCollection` (the loader, the followers),
  `Cache3` (resident objects only, with the registry), `Db` (the eviction
  points, accounting), `DbStarter` (a reconstruction phase), `KeyNode` and
  `TopNode` (slots), `Reclaim` (maintenance reads, the step reserve),
  `DbBuilder` and the Pub API (the budget, test schedules).
* Eviction points: at the end of `Db.executeInner`, after `store`, under the
  write lock; and load-triggered batches that take the write lock while
  holding no slot lock.
* Per slot, under its pointer lock (`PointerLocks`): recheck the target
  (clean, not pinned, written), then make the slot a stream slot at the
  target's position.
* Release: remove the node table's entry if it names the object; clear the
  canonical flag; the registry forgets the object; the garbage collector
  frees it once no reader holds it.
* Readers: the hot path stays as it is: `followPointer` reads the slot under
  its lock, follows a memory pointer, and loads on a stream pointer.
* Not in the first release (level4-plan.md, section 10): exact LRU,
  background threads, a directory of every node's position, early writeout,
  incoming-reference lists.

8.9 Commands, and the byte comparison
-------------------------------------

Run in bergdb, with the JDK of 2.7:

    java/build.sh
    java -ea -cp java/build/bergdb.jar bergdb.dev.Unit
    java/stress/level1.sh; java/stress/level2.sh; java/stress/level3.sh
    java/stress/level4.sh                                  # from J9 on
    cd lean && lake build && lake exe sistest 20 40 && sh test-traces/run.sh
    cd lean && lake exe phystest && lake exe reclaimtest   # from L3 and R3 on
    java/stress/conformance.sh small|medium|large [seeds]
    java/stress/performance.sh build LABEL
    SUITE=quick java/stress/performance.sh ab l34-base current

**The byte comparison.** `StreamDigest` (A1) runs, without restarts, the
workloads of the six `RestartInvariance` configurations of `level2.sh`, step
4, and of the four of `level3.sh`, step 3, and prints the SHA-256 of each
stream from its first position. A1 records the digests of the preserved
build `l34-base`. A change that must not change the records (A3, R8, J1, and
every J WP with eviction off) gives the same digests with the current build.
Under Option K that is every Java change of this plan; a difference is a
finding (stop rule 3). One compiled copy of `StreamDigest` runs against both
jars:

    java -cp java/build/perf/builds/l34-base/<jar>:<digest classes> bergdb.core.StreamDigest all
    java -cp java/build/bergdb.jar:<digest classes> bergdb.core.StreamDigest all

(`performance.sh build` prints where the preserved jar is; A1 records the
exact commands in the progress file.)

Gate logs are in `java/build/level1/` to `level4/`; traces in
`java/build/traces/`.


9. Risks
========

| | Risk | Response |
|---|---|---|
| 1 | Option K fails: A6 or TREE does not hold in Java, or INV-SLOT does not follow | A4 tests A6 at the start, before any model depends on it; E2 searches for counterexamples before proofs; Option F is the fallback, through K1 |
| 2 | Stage 2 takes much longer than planned | The time box (5.3) and K1 with options; the other tracks go on meanwhile |
| 3 | The physical layer drifts from Java, as F1-008-07 and 08 did | Model Java's own procedures (L1 models today's first-touch rule); C-L and C-P check them on Java's runs; the byte comparison and EvictionInvariance check the records |
| 4 | The checker is too slow for runs with cuts and eviction | Stage 0 first; the Java tier for sizes the Lean tier cannot reach |
| 5 | T-SCHEME needs key ranges, which the model does not have | TouchCover as an assumption, checked on traces; C-CUT at every cut if the proof stalls (R6) |
| 6 | Historical nodes in D after a cut (M33, M34) need a Java change | R5 decides; a change goes through K3 |
| 7 | R8's corrections break reclaim or change records | One change at a time; the byte comparison; the gates; the reclaim conformance set |
| 8 | Concurrency bugs once slots change both ways | Q8: eviction only under the write lock, slots under their pointer locks; deterministic interleaving tests (J5); `ReclaimReaders` with forced eviction |
| 9 | The pinned state (D, the record being written) is larger than practical budgets | P3 measures it first; J7 reports it, never evicts it; the limits are documented |
| 10 | Eviction's bookkeeping slows the resident path | No per-hop id lookup or reference count (8.8); J10 against Q13; the sweep works on mutation and at boundaries, not on reads |
| 11 | Uncommitted work piles up during a long unattended run | Q2 (b) or (c); review guides at K1, K3, K4 and K5; one WP per change |
| 12 | Long jobs collide: gates, soak, performance, Lean builds | 2.7; scratch copies for gates; the progress entry says what runs in the background |
| 13 | The agent loses context over many sessions | Section 0; progress entries written before long jobs; WPs small enough for one session |
| 14 | The AI budget runs out in the middle of a WP | Keep the work tree consistent at every step; a "partial" entry with the exact next step |
| 15 | New tests find latent bugs outside the register (as M18 at Level 2) | A small fix as its own WP with a failing test first, K2; stop rule 3 if it does not fit a row |
| 16 | Work drifts into out-of-scope topics | 1.5; ideas go into progress entries |


10. After this plan
===================

Not planned here: protected snapshots (D1 = B); a Lean model of the TopDs
skip list and its lookup (F1-008-13, 4 to 16 days by its estimate); proofs
of the bounds (T3, T4) after P3's measurements; reclaim option B for
short-retention, space-critical use; a second stream for cold data;
replication with cuts; publishing the self-indexed stream concept with its
Lean model.


11. Sources
===========

* In bergdb: [README.md](../../README.md), [AGENTS.md](../../AGENTS.md),
  [items/readme.md](../readme.md); [docs/levels.md](../011-docs-archive/04-levels.md),
  [docs/level2-alignment.md](../011-docs-archive/11-level2-alignment.md),
  [docs/level3-plan.md](../011-docs-archive/06-level3-plan.md),
  [docs/level3-durability.md](../011-docs-archive/07-level3-durability.md),
  [docs/level3-performance.md](../011-docs-archive/10-level3-performance.md),
  [docs/level4-plan.md](../011-docs-archive/05-level4-plan.md),
  [docs/reference-theory.md](../011-docs-archive/08-reference-theory.md),
  [docs/sis-model.md](../../docs/sis-model.md),
  [docs/problem.md](../011-docs-archive/01-problem.md),
  [docs/performance-harness.md](../011-docs-archive/09-performance-harness.md);
  [lean/README.md](../../lean/README.md),
  [lean/References/README.md](../011-docs-archive/08-reference-theory/README.md).
* In f1, F1-008:
  [07](../../../f1/b/008-bergdb-lean-model/07-solution-claude/07-solution-claude.md),
  [08](../../../f1/b/008-bergdb-lean-model/08-solution-claude/08-solution-claude.md),
  [09](../../../f1/b/008-bergdb-lean-model/09-implementation-plan-claude/09-implementation-plan-claude.md),
  [Codex's review of 09](../../../f1/b/008-bergdb-lean-model/review-09-codex.md),
  [10](../../../f1/b/008-bergdb-lean-model/10-java-transactions-claude/10-java-transactions-claude.md),
  [11](../../../f1/b/008-bergdb-lean-model/11-level2-alignment-plan-claude/11-level2-alignment-plan-claude.md)
  and its [progress](../../../f1/b/008-bergdb-lean-model/11-level2-alignment-plan-claude/progress.md),
  [12](../../../f1/b/008-bergdb-lean-model/12-level2-alignment-report-claude.md),
  [13](../../../f1/b/008-bergdb-lean-model/13-topnodes-feasibility-codex/13-topnodes-feasibility-codex.md).
