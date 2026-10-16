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
* **G0, go for work in bergdb: given 2026-10-16 15:23 CEST**, in the prompt:
  "Carry out the next work packages of bergdb item 001
  (items/001-lean-model-levels-3-4/01-plan.md). Follow the plan's rules, and
  work unattended as far as possible. G0: as the plan recommends, do commit
  unattended. Q10: yes, eviction is on by default. Note this current time
  when this is started and that Opus 5.5 Max is used." The run started at
  15:23:51 CEST, with Claude Opus 5.5 at Max effort, in Claude Code.
* **Q2, commits: (b).** The agent commits each finished WP whose checks
  passed, as a local commit on `main`; never pushes, amends or rewrites
  history; lists the commits here. bergdb's AGENTS.md still applies: the
  three level scripts print `LEVEL n OK` before a Java change is committed.
* **Q10, the default: eviction is on by default** (Frans, the same prompt).
  K4 no longer decides it; the agent turns it on with the existing default
  budget once the capacity controller (J7) works and the gates pass with it.
  `level4.sh` as a required gate in AGENTS.md and README.md still waits for
  K4.
* Q1, Q3 to Q9, Q11 to Q13 (plan, section 4): the plan's defaults until
  Frans decides.
* **2026-10-16 15:43, Frans:** "Before or during WP A3 and WPs C1–C3, read
  section 7.1 of
  ../f1/b/008-bergdb-lean-model/13-topnodes-feasibility-codex/review-13-claude.md
  and take its points into the plan's WPs, recording what you adopt in
  02-progress.md." Read at 15:44 (with its sections 2, 3, 4.3, 5 and 6,
  which 7.1 cites). Adopted, as additions to the plan's WPs (the plan
  itself is unchanged):
  * **A3.** (1) The compatibility note says what really happened: a stream
    whose newest written top had an ordinal with bit 15 set could not be
    read; one with an ordinal of 65,536 or more and bit 15 clear could be
    read silently wrong (the ordinal modulo 65,536, with the wrong height),
    start, lose history and go on with wrong ordinals, and the fix alone
    cannot repair it. (2) Two checks in `StoredTopNode.parse`: the stored
    slot count equals the height of the ordinal, and the populated slots are
    exactly its set bits; either turns the silent case into an error. (3) A
    database-level restart test: one hot key at node size 8, about 131,000
    transactions, past ordinal 32,768, then a restart and checks. (4) The
    unit test builds the top of `MAX_TOP_NODE_ID_VALUE` directly, with the
    slots of the formula, not through `newSuperRoot`; the other ordinals
    (0, 1, 32,767, 32,768, 65,535, 65,536, 98,303) through `newSuperRoot`
    from a predecessor built directly. (5) Optional repair from the slot
    bitmap: not adopted; such streams are refused by the checks of (2), since
    Java has no external users (plan, Q4) and no such database is known.
    Also the two small Java points of 7.1, inside A3 since they are top
    node code: the startup `assert` at `DbStarter.java` 277 becomes a real
    check, and the comment of `TopNode.pointersTime` says that it caches the
    target's `rootTime`.
  * **C1 to C3.** C1 also times `topClosure` (R4, C-A) and `readTops`
    (startup with the virtual root, wherever the checker evaluates a model
    startup) on a trace with many tops (one hot key at node size 8).
    C2: `topClosure` and `readTops` are exponential in the number of tops,
    and `@[csimp]` cannot help, since a replacement must return the same
    list; use C2's other route, a checker step with its own theorem: R4
    through `PredChain` and `closure_of_chain` (review-13-claude's
    `R4Bridge.lean`), or a closure with a visited set proved to have the same
    members; the same for `readTops`. C3: the large set includes a
    configuration with many tops (one hot key at node size 8), and the
    checker must handle it.
  * **L5.** Besides the cached times (SKIPT lines, M29): query the root at
    every time t ≤ i on each record, so that C-V compares Java's predecessor
    branch (`leftMost`) with the model; and check the layout from the trace
    (the populated slots are the set bits of the ordinal, the level minus
    `topLevel`, and each target is the formula's).
  * **L2.** Tops never change after their transaction, so lemma M is
    immediate for top selection; only the root pointer's target, a key
    node, needs the key tree's lemma M.
  * **R3, R4, E1, M41.** The footprint lemma and the hop bound of
    review-13-claude 4.3 say what a cut must keep and what eviction may load:
    a search at a time q loads, besides the answer, only tops created at or
    after q, and at most h(H) tops; for queries at or after tEnd, the tops
    created after tEnd and the top live at tEnd.
  * **Open for Frans (not urgent):** the ordinal bound 2^30 − 1 limits a
    database's lifetime under reclaim (review-13-claude, 3; at the limit
    `TopNode.height` throws in the middle of a root split): a wider ordinal
    (48 bits fit the header) or a clean early refusal. Register row M46 in
    `docs/level4-alignment.md`.


Current state
-------------

* Checkpoints: G0 given (2026-10-16 15:23); K1 to K5 open.
* Commits of this run (Q2 (b)): see the log entries.
* Uncommitted work of this plan in bergdb: the files of the WPs in progress,
  named in the last log entry.
* Long jobs running: none.
* Stage 2's time box (plan, 5.3): not started; 60 hours from the start of
  E1.
* Preserved builds: `l34-base` (A1; `java/build/perf/builds/l34-base/`,
  with its digests in `digests-a1.txt`).


Status
------

| WP | Title | Status | Updated |
|---|---|---|---|
| A1 | Baseline and environment | done | 2026-10-16 |
| A2 | The registers, checked against the code | in progress | 2026-10-16 |
| A3 | The TopNode ordinal defect | in progress | 2026-10-16 |
| A4 | Probe H1: no adoption | in progress | 2026-10-16 |
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


### 2026-10-16 15:23 to 16:05. WP A1, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `50a2a7b`
(Frans's commit of the plan), clean work tree at the start.

Did:

1. HEAD `50a2a7b`; `git status --short` empty.
2. `java/stress/StreamDigest.java` (plan, 8.9): the workloads of
   `RestartInvariance`'s configurations in `level2.sh` step 4 (seven
   configurations, eight runs with the two idle seeds, the 100 MB one
   included) and `level3.sh` step 3 (four, reclaim on), draw for draw; each
   in three modes, plain (transactions only), reads (as `RestartInvariance`'s
   run A: a checksum and its lookups at every checkpoint) and restarts (as its
   run B). It prints the SHA-256 of each stream from its first position
   (`sha256all`) and from the cut that reclaim decided (`sha256`), and
   compares two outputs (`compare`). Only `DbBuilder.testSetup`, `Db`,
   `Trans`, `MemoryStream`, `CoreTestClock` and `DbUtil`. The stream lengths
   equal those `RestartInvariance` printed in the gates' logs (all 12). The
   three modes give the same stream after the decided cut in all 12; the
   physical cut differs once (l3-node14: front at 0 without restarts, at
   1,000,000 with them, since a restart syncs and the cut waits for
   durability; M35), so the mode comparison uses `sha256`.
3. `java/stress/performance.sh build l34-base`, 15:56: from `50a2a7b`,
   dirty (StreamDigest.java untracked; `java/stress/A2A3Check2.java` already
   changed by A4, test code only; `java/src` is that of `50a2a7b`, unchanged
   since `d5c56dd`). Jar SHA-256 `45037cbae774cb33...`. Digests of every
   configuration with it, in `java/build/perf/builds/l34-base/digests-a1.txt`
   (36 lines). The plain mode, stream length and the first 16 hex digits of
   `sha256`: l2-sd100 5,131,920 `fbaa851612f5bd8e`; l2-sd1000-node8
   4,257,960 `30f368687bb514bc`; l2-sd10000-node14 2,421,648
   `2f8ecac2f7645645`; l2-sd100000-node62 2,492,680 `d2174d5c8859bb94`;
   l2-every1 468,400 `08238b1b2ffdfd4b`; l2-idle-1 221,192
   `59941275e25016d6`; l2-idle-2 221,560 `c9c4212f89c3ac09`;
   l2-default-100MB 78,934,240 `e44e68be138b1066`; l3-every1 1,789,400
   `9f8cb1c67b175a8a`; l3-node8 7,006,600 `a6802defd874880d`; l3-node14
   1,327,208 `1dd165e9616b1487`; l3-node62 8,872,320 `743b6c1dc7957ccc`.
   The byte comparison, the commands (from `java/`, JDK of 2.7):

       B=build/perf/builds/l34-base/java/build
       java -Xmx9g -cp build/bergdb.jar:$B/stress bergdb.core.StreamDigest all > build/digest/X.txt
       java -cp build/bergdb.jar:$B/stress bergdb.core.StreamDigest compare build/digest/l34-base.txt build/digest/X.txt

   (`build/digest/l34-base.txt` is the same as `digests-a1.txt`.) The
   preserved jar against the work tree's jar: `DIGESTS IDENTICAL (36 of
   36)`. A run of all takes 45 s.
4. The gates, full, one after the other, 15:31 to 15:55: `LEVEL 1 OK` (86 s;
   908 unit tests), `LEVEL 2 OK` (995 s; 908 unit tests; step 7: a2a3-1 to 3
   OK, conformance small 50 of 50 traces `TRACECHECK OK`, 127,707 LIVE lines,
   0 failed probes, the checks 281 s), `LEVEL 3 OK` (317 s; 908 unit tests,
   37 f-tests). Logs in scratch and `java/build/level1/` to `level3/`.
5. Lean, 15:55 to 16:02: `lake build` OK, no warnings; `lake exe sistest 20
   40` "all checks pass" (407 s; the 16 algorithms and the 8 with a virtual
   root 20/20 seeds, T13 20/20, the witness as before); `#print axioms` of
   `T1_recovery`, `T1_crash`, `T1_nodes`, `T2_restart`, `T13_markExact`: each
   `[propext, Classical.choice, Quot.sound]`; no `sorry`, `admit`, `axiom` or
   `unsafe` in `lean/SIS/` and `lean/Check/`; `sh test-traces/run.sh`: `TRACE
   TESTS OK`.
6. What P1 and P2 must still do (level3-plan.md, tasks 2 and 3;
   level3-performance.md). **P1**: all of task 3. The tracked quick reference
   (`quick-2026-10-14-pre-task1`, `506510d9`) predates task 1 and the Level 2
   alignment (D0's 8 bytes per record, D1's in-place splits). So:
   `java/stress/performance.sh quick` on A1's code on a quiet machine (90
   percent idle, never `FORCE`), promote as `quick-2026-10-16-post-task1`,
   update level3-performance.md, name it in level4-plan.md, step 0. About 15
   minutes. **P2**: all of task 2;
   no soak harness exists. Write `Soak.java` and `soak.sh` (PerfUtil's
   histograms and GC log reader); `FileStream` in a disposable directory,
   wall-clock retention; the pilot (one million keys, 1,000-byte values, five
   minutes' retention, one writer, two to four readers, gets, scans, updates,
   deletes, reinserts, a hot subset, long keys), or a documented smaller
   scale; then at least two measured hours, ten physical cuts and three cold
   restarts, every operation checked at its actual snapshot with a bounded
   reference; the metrics of task 2's list; `docs/level3-soak.md`. During the
   measured hours nothing else heavy runs (plan, 2.7).

Files changed: `java/stress/StreamDigest.java` (new); this file.

Checks: as above. The java/stress check of 2.2: `java/build.sh` passes; the
tool ran on every configuration (small and medium sizes, and the 100 MB one).

Register: none.

Open, next: commit A1. Then A2 (in progress: `docs/level4-alignment.md`,
`docs/level3-alignment.md`, pointers in `docs/levels.md` and
`docs/level2-alignment.md`), A3 (in progress: the fix and its tests pass the
unit tests of the classes concerned; the gates next) and A4 (in progress:
the diagnostics in a scratch copy of `lean/`, and in `A2A3Check2`).
