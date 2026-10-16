001-02. Progress of the plan 001-01
===================================

The state of the work on the plan [01-plan.md](01-plan.md).

Agents: update the status table and the current state, and append an entry
to the log at the end of every session, and before every long job (plan,
sections 0 and 2.6). Frans: record the go (G0), the results of the
checkpoints and your decisions under "Frans's go and decisions". They
override the plan's defaults.


Frans's go and decisions
------------------------

* 2026-10-16 13:55, on F1-008-12's proposal (its K4, point 3): one plan for
  Levels 3 and 4, in stages, each with its own theorems; caching (Level 4)
  before reclaim (Level 3); Level 4's model may change Java's Level 3 where
  it requires it.
* G0, go for work in bergdb: **not given yet.**
* Q1 to Q13 (plan, section 4): the plan's defaults until Frans decides. Q2,
  commits: default (a), Frans commits; the plan recommends (b) for long
  unattended runs.


Current state
-------------

* Checkpoints: G0 not given; K1 to K5 open.
* Uncommitted work of this plan in bergdb: `items/001-lean-model-levels-3-4/`
  (readme.md, 01-plan.md, this file). Nothing in `java/`, `lean/` or
  `docs/`.
* Long jobs running: none.
* Stage 2's time box (plan, 5.3): not started; 60 hours from the start of
  E1.
* Preserved builds: none yet (`l34-base` comes with A1).


Status
------

| WP | Title | Status | Updated |
|---|---|---|---|
| A1 | Baseline and environment | not started | — |
| A2 | The registers, checked against the code | not started | — |
| A3 | The TopNode ordinal defect | not started | — |
| A4 | Probe H1: no adoption | not started | — |
| C1 | Profile the checker | not started | — |
| C2 | Fast versions, proven equal | not started | — |
| C3 | Larger sets and parallel runs | not started | — |
| L1 | The physical layer, part 1: loading | not started | — |
| L2 | Lemma M | not started | — |
| L3 | Lazy startup and reads: T1-L | not started | — |
| L4 | The writer after a lazy startup: CC, T2-L | not started | — |
| L5 | Lazy reading checked against Java | not started | — |
| E1 | Design: eviction, references, pins | not started | — |
| E2 | The physical model with eviction, executable | not started | — |
| E3 | INV-SLOT and the physical writer: T-CACHE | not started | — |
| E4 | Reads under eviction: T-READ | not started | — |
| E5 | Restarts with eviction: T2-C | not started | — |
| E6 | Pins and index-freedom | not started | — |
| E7 | The Java change list; the K1 review | not started | — |
| R1 | α and the register for reclaim | not started | — |
| R2 | Trace format 2; the exporter for reclaim runs | not started | — |
| R3 | The Level 3 model: touch, first available time, cuts | not started | — |
| R4 | Recovery and reads after a cut: T8, T9 | not started | — |
| R5 | Restarts across cuts: T12 | not started | — |
| R6 | Java's scheme gives safe cuts: T-SCHEME | not started | — |
| R7 | The red list on Java's reclaim | not started | — |
| R8 | Java: the corrections the model requires, before eviction | not started | — |
| R9 | Level 3 conformance; the gate proposal | not started | — |
| J1 | Registry, pins and audits | not started | — |
| J2 | Eviction of values | not started | — |
| J3 | Eviction of index nodes | not started | — |
| J4 | Eviction invariance; conformance with eviction | not started | — |
| J5 | Readers under eviction | not started | — |
| J6 | Reclaim under eviction | not started | — |
| J7 | The capacity controller | not started | — |
| J8 | Larger than memory | not started | — |
| J9 | `level4.sh` | not started | — |
| J10 | Performance | not started | — |
| F1 | The conformance campaign, all levels | not started | — |
| F2 | Documents | not started | — |
| F3 | The final report | not started | — |
| P1 | The Level 3 quick performance reference | not started | — |
| P2 | The Level 3 soak | not started | — |
| P3 | Bounds, measured | not started | — |
| P4 | The soak with eviction | not started | — |

Status values: not started, in progress, partial, blocked, done, dropped.


Log
---

### 2026-10-16 14:05 to 14:48. The plan

Agent: Claude, Opus 5.5, Claude Code. bergdb at `fb52a14`, uncommitted:
`items/001-lean-model-levels-3-4/readme.md` (the morning's decisions) and
`01-plan.md` (the overview), both from earlier today.

Did: on Frans's request, extended 001-01 from the overview into the
detailed plan, and wrote this file (001-02). Read for it: bergdb's
`docs/levels.md`, `level2-alignment.md`, `level3-plan.md`,
`level3-durability.md`, `level3-performance.md`, `level4-plan.md`,
`reference-theory.md`, `sis-model.md`, `problem.md`,
`performance-harness.md`, the start of `log.md`; `lean/README.md`, the
trusted Lean files, the checker (`Check/`, `TraceCheck.lean`, `Test.lean`);
the Java code the plan names (`Reclaim`, `NodeCollection`, `Cache3`,
`Pointer`, `KeyNode`, `TopNode`, `TopDs`, `Dag`'s splits, `Db`, `DbStarter`,
`DbHelper`, `TransSeq`, `OpData`, `GetData`) and the stress scripts and
tools (`level1.sh` to `level3.sh`, `conformance.sh`, `TraceExport`,
`A2A3Check2`, `RestartInvariance`, `ReclaimStress`); in f1, F1-008's 07, 08,
09, Codex's review of 09, 11 with its progress, 12 and 13. No WP started;
nothing in bergdb's `java/`, `lean/` or `docs/` changed.

Found while planning, for the WPs that follow:

* The TopNode ordinal defect of F1-008-13 (section 5.1) is still in the code
  (`StoredTopNode.toLongs`, line 176 at `fb52a14`): WP A3, register M30.
* Option K, the plan's leading candidate for Level 4's reference rule (plan,
  8.5), has a gap after restarts that today's node table hides: a node of D
  can hold a stream slot to a node of D that is written before it (M44). The
  candidate fix is a window, Rule R carried on at runtime; E1 must settle it.
* `NodeCollection.followStreamPointer` overwrites a slot's position with
  access data when it swizzles, so a trace of first touches needs a
  test-only hook (L5).
* There is no soak harness yet; P2 must write one.

Open, next: G0, with Q2 in particular; then A1.
