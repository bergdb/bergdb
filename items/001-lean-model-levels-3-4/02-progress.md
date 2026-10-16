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
| A2 | The registers, checked against the code | done | 2026-10-16 |
| A3 | The TopNode ordinal defect | done | 2026-10-16 |
| A4 | Probe H1: no adoption | done | 2026-10-16 |
| C1 | Profile the checker | done | 2026-10-16 |
| C2 | Fast versions, proven equal | done | 2026-10-16 |
| C3 | Larger sets and parallel runs | done | 2026-10-16 |
| L1 | The physical layer, part 1: loading | done | 2026-10-16 |
| L2 | Lemma M | done | 2026-10-16 |
| L3 | Lazy startup and reads: T1-L | done | 2026-10-16 |
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
| P1 | The Level 3 quick performance reference | done | 2026-10-16 |
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


### 2026-10-16 15:23 to 16:04. WP A1, done

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


### 2026-10-16 15:57 to 16:33. WP A3, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `75d3c2d`,
uncommitted: A2's documents and A4's `java/stress/A2A3Check2.java` (named in
the A1 entry), and this WP's files.

Did, with the points of review-13-claude, 7.1, that Frans asked for (above,
"Frans's go and decisions"):

1. The tests first, each failing on the unchanged code:
   `StoredTopNode.testOrdinalsRoundTrip` (ordinals 1, 2, 3, 32,767, 32,768,
   32,769, 65,535, 65,536, 98,303 and 2^20 through `TopDs.newSuperRoot` from a
   predecessor built with the layout's slots, and 0 and
   `MAX_TOP_NODE_ID_VALUE` built directly; ordinal, slot count, every slot's
   position and cached time, `rootTime` and id compared): failed with
   "Bad TopNode ID of TopNode in stream, -32768".
   `StoredTopNode.testParserRefusesSlotsThatDoNotFit` (65,536 stored as 0,
   98,303 as 32,767, 5 as 4, 6 as 5): failed, "ordinal 65536 stored as 0
   refused". `DbTesterRestart.testRestartAfterManyTopNodes` (one hot key, node
   size 8, startup distance 10,000 bytes, until the newest written top node
   passes ordinal 32,800, then a restart: the super root, seven historical
   values, and the next top node's ordinal): failed with the same exception,
   in 1.5 s.
2. The fix: `StoredTopNode.toLongs` widens the ordinal before the shift.
   `StoredTopNode.parse` refuses a top node whose slot count is not the
   ordinal's height, or whose populated slots are not the ordinal's set bits.
   `DbStarter.findSuperNodeAtStartupTime`: the assert that the newest written
   top node is the super root at the startup time is a check
   (`StreamFormatException`). `TopNode.pointersTime`'s comment says what it
   caches. `TopNode.createDummy` (tests only) gets the layout's slots, and
   `StoredTopNode.testTopNodeToLongs2` gives TopTester's top nodes positions,
   since the parser now refuses top nodes without them; no other test needed
   a change.
3. Compatibility (`docs/levels.md`, "Bugs found by the alignment of Levels 3
   and 4"; `docs/log.md`): streams whose top node ordinals are all below
   32,768 are unchanged, byte for byte; the others could not be read, or were
   read wrong, and are now refused; no repair (adopted from review-13-claude,
   7.1, point 5: not done).

Files changed: `java/src/bergdb/core/StoredTopNode.java`, `DbStarter.java`,
`DbTesterRestart.java`, `java/src/bergdb/dag/TopNode.java`; `docs/levels.md`
(the bug, a new section), `docs/log.md`.

Checks, on the work tree (`75d3c2d` plus the files above, A2's documents and
A4's `A2A3Check2.java`), 16:08 to 16:32: `LEVEL 1 OK` (89 s; 911 unit tests),
`LEVEL 2 OK` (988 s; 911 unit tests; step 7: a2a3-1 to 3 OK, conformance
small 50 of 50 `TRACECHECK OK`), `LEVEL 3 OK` (317 s; 911 unit tests, 37
f-tests). A first run stopped at the unit tests (`StoredTrans.
testTopPosOfTopNodeInTransaction`: `TopNode.createDummy(7)` had no slots),
fixed as in point 2. The byte comparison against `l34-base`: `DIGESTS
IDENTICAL (36 of 36)`.

Register: M30 closed (code fix, A3).

Open, next: commit A3, then A2 (M30 closed there).


### 2026-10-16 15:31 to 16:34. WP A2, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `75d3c2d`, then
`280525a` (A3); uncommitted: A4's `java/stress/A2A3Check2.java`, and this
WP's files.

Did:

1. Read the inputs of the plan's A2: `docs/level2-alignment.md` (all),
   `docs/level4-plan.md` (2, 2.1, 4, 5, 5.1, 6), `docs/reference-theory.md`
   (1 to 7), Codex's review of 09 (findings 2 and 4 to 7), F1-008-13 (5,
   5.1), and the Java the plan names: `NodeCollection`, `Cache3`, `DbStarter`,
   `Db` (the constructor, `startInner`, the listeners, marking, `getOneInternal`,
   `getMany`, `expiredIfReadBelowCut`, `executeInner`, `store`, `warmup`,
   `putKvs`, `touchRange`, `getAccessData`), `DbHelper`, `TransSeq`, `Reclaim`
   (the class comment and the core methods), `Trans`, `StoredKeyNode`,
   `StoredTopNode`, `DbBuilder` and `pubimp/DatabaseBuilderImp`, `Pointer`,
   `KeyNode` and `TopNode` (fields and slot methods), `TopDs`, `Dag` (the put
   path and the splits), `AccessData`, `PointerLocks`, `Node`, `CutStream`,
   `ReadBelowFirstPosException`, and the cut paths of `FileStream`,
   `BufferedStream` and `StorageManager`.
2. `docs/level4-alignment.md` (new): scope; α for the cache (objects:
   canonical objects, snapshots, temporary objects; slots, memory and stream,
   and how they change today; the node table; the pins; Rule R for the whole
   process, `idByPos`, access data, the writer's warm-up reads); the
   register, M20 to M31, M39, M40, M43 to M46, each with file, method and
   line at `75d3c2d`. Sections for A4 (probes), E1 (the design) and E7.
3. `docs/level3-alignment.md` (new): scope; α for reclaim (records, T(i)
   of a step and a table store, touch(i), fa(i), cuts decided and made, the
   iteration's positions and times); the register, M17, M32 to M38, M41.
   Sections for R1 (arguments, the safety argument) and R7 (red list).
4. Pointers: `docs/levels.md` (the table's Level 4 row, Level 3, Next) and
   `docs/level2-alignment.md` (a paragraph after the register: M8 and M17
   reopened, the new documents), and M42 added to level2-alignment.md's
   register, where stage 1 closes it.

Findings, beyond the plan's register:

* M45 (new): the public API's cache size is computed in `int`
  (`pubimp/DatabaseBuilderImp.start`, line 173: `cacheSizeInMb * 1000000`):
  above 2,147 MB it overflows; the default is a fifth of the maximum heap, so
  with heaps above about 10.7 GB and `-ea` the `Db` constructor fails
  (`Cache3.setSizeIndicator` asserts a positive size), and without `-ea` the
  budget becomes 4 MB. No effect today (nothing reads the budget, M40); the
  fix belongs before J7 relies on it.
* M46 (from review-13-claude, 3): the ordinal bound 2^30 − 1 over the
  database's life; for Frans (above).
* Every transaction reads its keys through the readers' follower first
  (`Db.warmup`), so readers' first touches and snapshots occur in every run
  (matters for M21, M27). `TransNodes.clean` clears the dirty flags of the
  record being written before it is appended (for eviction's eligibility).
  M22's runtime cut-back is not reachable today, with the reason and lines.
* M30 is closed by A3 (`280525a`).

Files changed: `docs/level4-alignment.md`, `docs/level3-alignment.md` (new);
`docs/levels.md`, `docs/level2-alignment.md`; this file.

Checks: the documents' links resolve (checked with the script of the plan's
session); statements about code cite file, method and line at `75d3c2d`.

Register: M17, M20 to M44 checked and in the new documents (M30 closed); new
M45, M46.

Open, next: A4 (the medium set with the A6 and TREE diagnostics is running
on the fast checker of C2).


### 2026-10-16 15:48 to 16:46. WP A4, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `75d3c2d` to
`f6cf45c` (A1 to A2); uncommitted: this WP's files.

Did:

1. The checker (developed in a scratch copy of `lean/`, then copied in):
   `adoptionFailures` (A6) and `treeFailures` (TREE) in
   `lean/Check/Steps.lean`, with the model's `reachList`, `pointees` and the
   instance's `live`; reported in `TraceCheck.lean`'s diagnostics, which now
   count a transaction once even when several diagnostics fail (before, D's
   closedness and INV-2 counted separately). A test trace,
   `test-traces/adopt.trace`, where TREE and then A6 fail.
2. The Java tier: `java/stress/A2A3Check2.java` counts A6, A6' (the weaker
   form: the adopted node is at least below the node with the dead pointer)
   and TREE, prints them on a new summary line (the gate's grep patterns are
   unchanged), and with `-DdebugA6=1` prints each A6 failure.
3. Runs. The Lean tier on the small set (A1's traces, 50) and the medium set
   (F1-008-11's 9 traces on `d5c56dd`; production code and exporter
   unchanged since): A6 0, TREE 0, in 3,700 and 3,360 transactions. The
   medium set ran with C2's fast checker, which computes the model's
   definitions (proven); the slow and the fast checker gave identical outputs
   on all 50 small traces and on the two medium traces both finished. The
   Java tier on the 21 configurations of level2-alignment.md, 10.5 (68,901
   transactions, 80 s): TREE 0; A6 fails in 5 transactions, A6' in 0.
4. The failures, with `-DdebugA6=1`: a segment leaf with a dead pointer to a
   node that the same transaction created and then split in place
   (`Dag.spaceSplitInPlace` with a segment-leaf parent): the parent's new
   klong points to the new root above the split node, so the split node is
   still below the parent. Smallest configurations: `-Dmaxnode=8 -Dkeys=1000
   -Dn=50 -Dexact=1 -Dops=40 -Ddel=25 -Dlong=1` seed 4, T2; and
   `-Dmaxnode=8 -Dkeys=500 -Dn=2000 -Dops=10 -Ddel=20 -Dlong=1` seed 2,
   T26 to T29.
5. `docs/level4-alignment.md`, section 4 "Probes", and M43 updated.

Files changed: `lean/Check/Steps.lean`, `lean/TraceCheck.lean`,
`lean/test-traces/run.sh`, `lean/test-traces/adopt.trace` (new);
`java/stress/A2A3Check2.java`; `docs/level4-alignment.md`; this file.

Checks: `java/build.sh` and the gates passed with the new `A2A3Check2`
(A3's run; level2.sh step 7 runs it); the tool ran on the 21 configurations,
small to large. Lean, 16:35 to 16:42: `lake build` OK, no warnings; `lake exe
sistest 20 40` "all checks pass" (410 s); `#print axioms` of the five
theorems: the standard three; no `sorry`, `admit`, `axiom` or `unsafe` in
`lean/SIS/` and `lean/Check/`; `sh test-traces/run.sh`: `TRACE TESTS OK`,
with the two new expectations on `adopt.trace`.

Register: M43 (A4's part done: TREE holds, A6 fails, A6' holds). For E1:
whether the model assumes A6' instead of A6, and how the dead-slot argument
of 8.5 goes with A6'. This does not trigger the stop of 5.3 ("A6 refuted and
no weaker property found"): A6' is the weaker property, so far checked, not
proved to suffice.

Open, next: commit A4 when its Lean checks pass; then L2 (proved in a
scratch copy) and C2 (in progress: `markOf`, `writeAll`, `reachList` and
`step` fast, proven equal; the medium set 88 s instead of 6,770 s).


### 2026-10-16 16:10 to 16:30. WP C1, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `75d3c2d`; no
repository change (the profiler is in scratch).

Did: a scratch copy of `TraceCheck.lean`'s loop (`Profile.lean`, not for
bergdb), which evaluates the parts of the model's `step` one by one and the
checker's phases, each timed with `IO.monoNanosNow` (results kept, so that
nothing is optimized away). On `m-mixed-1` (500 transactions, node size 8,
1,717 nodes at the end, 12 top nodes, 5,009 versions), with other jobs on
the machine:

| Part | Time | Share of the step |
|---|---|---|
| step 3, `markOf` | 282.7 s | 99.5 % |
| step 6, `writeAll` (index) | 0.10 s | |
| step 5, take and `byLevel` | 0.06 s | |
| step 7, `stillDirtyOf` (`javaTest`) | 0.01 s | |
| step 2, `writeAll` (data); step 8, `topOf` | 0.01 s | |
| the whole `step` | 284.2 s | 100 % |
| C-A: `reachList` before and after | 0.96 s | (outside the step) |
| C-A: `stepFailures` (of it `topClosure`, R4: 0.04 s) | 0.10 s | |
| C-S: `diffRecord`, D | 0.01 s | |
| diagnostics: D closed upward, A6, TREE | 2.4, 0.7, 0.7 s | |
| parsing the trace | 0.04 s | |

`markOf` dominates because `marked` calls `reachable`, which computes the
whole `reachList` again for every index node: quadratic in the nodes, with a
list lookup (`Struct.get?`) for every step of every traversal. `Stream.lv`
does not matter at 500 records. The review's addition (02-progress, Frans's
decisions): on two traces with many top nodes, `hot400` (one hot key, node
size 8, 400 transactions, 101 top nodes) and `long2000` (2,000 transactions,
node size 8, 20 keys, 41 top nodes), the profiler did not finish in 5 minutes,
in R4's `topClosure`, as review-13-claude, 5.1, predicts. (`readTops` is not
evaluated by the checker; only sistest's startups evaluate it, on example 3,
whose top nodes form a chain.)

Checks: none needed (no repository change).

Open, next: C2.


### 2026-10-16 16:08 to 16:55. WP P1, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `eecb513`;
uncommitted: this WP's files.

Did:

1. The quiet check. 16:08: 86.7 percent idle; another process
   (`mediaanalysisd`, macOS) used a whole core; not forced (plan, 2.4). 16:46:
   95.7 percent idle, nothing of this run active.
2. `BUILD=l34-base java/stress/performance.sh quick post-task1`, 16:46 to
   16:54 (96.1 percent idle at the start): the preserved build of A1, the code
   after task 1 and the Level 2 alignment. Session
   `50a2a7be-d92fa83-20261016T164646-quick-g1-8g-post-task1`; no correctness
   failure. Promoted as `java/bench/reference/quick-2026-10-16-post-task1`
   (`promote` needs an absolute session path, since `performance.sh` changes
   to `java/` first).
3. `docs/level3-performance.md`: the new reference with its source, command
   and environment, and a table against the one before task 1: warm latest
   gets 1.28 M/s (+12 percent), historical 1.26 M/s, 4 threads 3.42 M/s,
   scans 3.70 / 3.88 M KVs/s, updates 90.1k commits/s (infinite retention) and
   58.4k (finite), bytes per user byte 1.22 and 1.68, startup 0.65 s, append
   p50 / p99.9 / max (finite) 9.3 us / 116 us / 271 ms. Nothing collapsed.
   `docs/level4-plan.md`, section 8, step 0, names it; `docs/level3-plan.md`'s
   status says task 3 is done.

Files changed: `docs/level3-performance.md`, `docs/level4-plan.md`,
`docs/level3-plan.md`, `java/bench/reference/quick-2026-10-16-post-task1/`
(new, 204 KB, the compact results); this file.

Checks: the session ran every scenario and its correctness checks; the
documents' links resolve.

Open, next: J1 needs P1 (done) and P2 (the soak, not started).


### 2026-10-16 16:30 to 17:04. WP C2, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `d8abf0a`;
uncommitted: this WP's files.

Did (developed in a scratch copy of `lean/`, then copied in):

1. `lean/Check/Fast.lean`: fast versions of the model's definitions, each
   proven equal and marked `@[csimp]`: `reachList` (`reachList_eq_fast`; P
   through a hash map, `nodeMap`, with `nodeMap_get?`), `markOf`
   (`markOf_eq_fast`: the reachable nodes once per transaction, P, D and the
   changed nodes through hash maps and sets), `writeAll` (`writeAll_eq_fast`:
   the stream's latest versions through a hash map built once per call,
   `lvMap_get?`), and `step` itself (`step_eq_fast`, by `rfl`): a `@[csimp]`
   equation changes only code compiled after it, and the model's `step` was
   compiled before, with calls to the slow definitions; `stepFast` is `step`
   word for word, compiled again. Helpers with proofs: `reachFromG` (lookups
   through a function), `eraseDupsFast` (= `List.eraseDups`), `allIdsFast`.
   Of the plan's two routes (C2, point 1), `@[csimp]` equations sufficed; no
   checker step with an index kept along the trace was needed.
2. `lean/Check/R4.lean`: R4 in linear time, as review-13-claude, 7.1, asked.
   `PredChain` and `mem_topClosure` are review-13-claude's `R4Bridge.lean`
   (F1-008-13, f1), with its proofs; new: `chainB` (the test of the chain
   through hash maps), `chainB_sound`, `r4Fast`, and `r4Fast_sound`: when the
   test passes, the list that the checker's R4 check filters is empty, so the
   checker evaluates `topClosure` only when the test fails. The R4 check in
   `virtFailures` now goes over the node ids of P with `Struct.get?` (as
   `VirtStep.closure` says) instead of P's entries; the same for traces, whose
   ids are distinct.
3. `lean/README.md`: the fast paths, and the checker's equalities in the
   axioms check.

Results (the targets of C2: the medium set under 15 minutes; 5,000
transactions at node size 30 with 1,000 keys under 10 minutes and 2 GB):

| Trace or set | Before | After |
|---|---|---|
| `m-mixed-1` (500 transactions) | 265 s | 4.5 s |
| the medium set, 9 traces (one at a time; CPU) | 6,770 s | 88 s; 31 s on 3 cores |
| the small set, 50 traces (CPU) | 281 s | 8 s |
| `hot400` (one hot key, 101 top nodes) | did not finish (R4) | 0.13 s |
| `long2000` (2,000 transactions, 41 top nodes) | did not finish (R4) | 8.2 s, 30 MB |
| `big5000` (5,000 transactions, node size 30, 1,000 keys, 10,113 nodes) | — | 428 s, 128 MB |

Regression: on the 50 small traces and the 9 medium traces, the output of the
final checker equals that of the checker with the model's definitions (the
50 small and the 2 medium traces it finished) or of C2's first version (the
other 7 medium ones), apart from the first line (the file name). All 59
`TRACECHECK OK`.

Files changed: `lean/Check/Fast.lean`, `lean/Check/R4.lean` (new);
`lean/Check/Steps.lean` (imports; R4's fast path), `lean/README.md`; this
file.

Checks, 16:56 to 17:03: `lake build` OK, no warnings; `lake exe sistest 20
40` "all checks pass" (404 s); `#print axioms` of the five model theorems and
of `markOf_eq_fast`, `writeAll_eq_fast`, `reachList_eq_fast`, `r4Fast_sound`
(the standard three) and `step_eq_fast` (`propext`, `Quot.sound`); no
`sorry`, `admit`, `axiom` or `unsafe` in `lean/SIS/` and `lean/Check/`; `sh
test-traces/run.sh`: `TRACE TESTS OK`.

Open, next: C3 (`conformance.sh` has the large set and `PAR`; running), then
L2 (proved in scratch) and L1.


### 2026-10-16 16:15 to 17:20. WP L2, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `411b3c4`;
uncommitted: C3's `java/stress/conformance.sh` (running), and this WP's
files. Developed in a scratch copy of `lean/`.

Did:

1. The statements (trusted, `lean/SIS/PhysTheorems.lean`, new), each with a
   comment in plain English: `LM_newer`, in every run with the assumptions,
   after every transaction, if version v of node x is good for time t, every
   version w of x written at or after v is good for t; `LM_ruleR`, so is the
   newest version of y in R(s), ..., R(k), which Rule R follows instead of
   the version a pointer names (for every s); `LM_cutTo`, a version cut back
   to s is good for t ≤ s exactly when the whole version is.
   `Version.cutTo` is in `lean/SIS/Phys.lean` (new, trusted), the start of the
   physical layer.
2. The proof (`lean/SIS/Proof/Newer.lean`, new): `Inv.newer`, by induction on
   the level, from the invariant's `vh` (a version holds its node's history up
   to its record) and `ref` (its references name the latest versions of the
   stream as it was when it was written): the newer version's references name
   versions at or after the older one's (`Inv.ref_mono`), whose node is lower,
   and the histories agree up to t (`upTo_between`). `newest_ge` for Rule R;
   `good_cutTo`. It needed no new assumption and no change to the trusted part
   that was there.
3. By running: sistest checks lemma M along random runs of examples 2 and 3,
   every fourth state, every node, every pair of versions and every time
   (`lemmaMCheck` in `SIS/Example.lean`); 2 seeds of 20 transactions: 13,954
   cases (an older version good, a newer one checked), 0 failures.
4. `lean/README.md` (the trusted part, the theorems, the axioms check, the
   status) and `docs/level2-alignment.md` (lemma M is proved; M8 stays open
   until L5).

Plan note: the plan (2.3) asks to check a theorem by running before proving
it; here the proof came first (it went through at once), and the running
check after.

Files changed: `lean/SIS/Phys.lean`, `lean/SIS/PhysTheorems.lean`,
`lean/SIS/Proof/Newer.lean` (new); `lean/SIS.lean`, `lean/SIS/Example.lean`,
`lean/Test.lean`, `lean/README.md`; `docs/level2-alignment.md`; this file.

Checks, 17:09 to 17:19: `lake build` OK, no warnings; `lake exe sistest 20
40` "all checks pass" (421 s), with lemma M by running: 1,277,099 cases, 0
failures; `#print axioms`: `LM_newer` and `LM_ruleR` the standard three,
`LM_cutTo` `propext` and `Quot.sound`, the earlier theorems and the checker's
equalities as before; no `sorry`, `admit`, `axiom` or `unsafe`; `sh
test-traces/run.sh`: `TRACE TESTS OK`.

Register: M8 (lemma M proved; the first touch itself is L1 to L5).

Open, next: L1 (the physical layer, part 1; developed in scratch: the
definitions build and the examples' checks pass), C3 (running).


### 2026-10-16 17:04 to 17:25. WP L1, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `130f380`;
uncommitted: C3's `java/stress/conformance.sh` (running), and this WP's
files. Developed in a scratch copy of `lean/`.

Did:

1. The design, `docs/level2-alignment.md`, new section 13 "Lazy reading":
   the state, Java's first touch, reads, the lazy startup, what is left out
   and why, the checks by running, and the statements of L2 to L4 in plain
   English.
2. `lean/SIS/Phys.lean` (trusted, executable): `Slot`, `Obj`, `Mem`; Java's
   first touch `Mem.follow` (Rule R for the whole process, M42; the table's
   object if canonical or at least as new; the version read, cut back in the
   section; `Mem.register`; the swizzle; the writer's `Mem.makeCanonical`);
   `Mem.read`; `lazyStartup` (the section's canonical objects, the root's
   object, memory slots between canonical objects, the rerun with the
   writer's paths, the change on canonical objects, copied slots for new
   pointers, `canonicalNode`). Each definition with a comment that names the
   Java method.
3. `lean/SIS/PhysExample.lean` (`#guard`, in `lake build`): in every state of
   runs of example 3 (a virtual root) and example 2 (a written root, four
   algorithms), reads at every time in increasing and in decreasing order
   give P, every canonical object holds its node's whole history, also with
   the writer's walks to every reachable node between reads; unit checks of
   the first touch (Rule R with Java's runtime cut-back, M22; a newer
   snapshot in the table; the writer's promotion; the version named read;
   `canonicalNode`). The plan's example "a node of D that the rerun does not
   reach" does not arise in the model (section 13.1 says why; in Java it came
   from deletes of missing keys before F1-008-11's D1); a unit check covers
   `canonicalNode` instead.
4. `lean/PhysTest.lean`, `lake exe phystest` (in `lakefile.toml`; L3's random
   test, written now): random runs, random reads and writer walks in random
   order after lazy startups, and startups from prefixes of the stream.
5. `lean/README.md`: the trusted part's change, the tests, how to run them.

One error found by running, in the model, fixed before anything was
committed: the root's object was not in the node table, so the rerun's
entries for new top nodes were lost (reads after the last startup pos missed
the newest top node); `lazyStartup` now enters it.

Files changed: `lean/SIS/Phys.lean`, `lean/SIS.lean`, `lean/lakefile.toml`,
`lean/README.md`; `lean/SIS/PhysExample.lean`, `lean/PhysTest.lean` (new);
`docs/level2-alignment.md`; this file.

Checks: `lake exe phystest 20 40`: all checks pass (29 s): example 3, four
policies, 820 states each, 6,578 reads each give P, no canonical object not
whole; 820 of 820 prefixes (crashes) read P; example 2, 16 algorithms, 4,363
reads each. The Lean checks of 2.2 on bergdb's `lean/` with these files
(17:21 to 17:28): `lake build` passes, 68 jobs, no warnings (the `#guard`s
of PhysExample.lean included); `lake exe sistest 20 40`: all checks pass
(421 s); `lake exe phystest 20 40`: all checks pass (28 s); the axioms of
T1, T2, T13, LM_newer and LM_ruleR are `propext`, `Classical.choice` and
`Quot.sound`, LM_cutTo's `propext` and `Quot.sound`; no `sorry`, `admit`,
`axiom` or `unsafe` in `SIS/` and `Check/`; `sh test-traces/run.sh`: TRACE
TESTS OK.

Register: none closed (M8 and M42 close in L5).

Open, next: L3, T1-L. The proof needs, beyond lemma M, that the stream
slots of canonical objects name (after Rule R) the latest versions of their
live children, or lead to canonical objects: for section nodes and for the
nodes of D this follows from the logical invariants and marking (every
reachable ancestor of a changed node is marked), and it is what Option K
needs too (INV-SLOT, plan 8.5). L3 will develop it as a lemma of the
logical model that E3 can reuse.


### 2026-10-16 16:55 to 18:32. WP C3, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `411b3c4` to
`3782bc8` (C2, L2 and L1 committed meanwhile; the checker is C2's
throughout); uncommitted: `java/stress/conformance.sh`, this WP's docs.

Did:

1. `java/stress/conformance.sh`: a `large` set (plan, 8.4): six
   configurations of two seeds, node sizes 8 to 62, 1,000 to 5,000
   transactions, up to 3,000 keys; two of them with many top nodes, as
   review-13-claude 7.1 asks (`l-hot`, one key at node size 8: 501 top
   nodes; `l-few`, 30 keys: 133). `all` runs the three sets. `PAR=N` checks
   N traces at once, default 4 (in batches of N: plain `sh` has no `wait -n`,
   so a batch waits for its slowest trace).
2. Timed the small, medium and large sets and the commands of `level2.sh`'s
   step 7; the times are in `docs/level2-alignment.md`, section 12 (and a
   note in 10.5), and in `docs/evidence/level2-conformance-c3.txt` (new).

Results (all CONFORMANCE OK, no failing check, no exporter error):

| Set | Traces | Time | Before C2 |
|---|---|---|---|
| small | 50 | 15.6 s (check 8 s in total) | 5 min 20 s |
| medium | 9 | 46 s (check 87 s in total, 18 s at most) | 1 h 53 min |
| large | 12 | 60 min 10 s (check 8,256 s in total) | — |
| `level2.sh` step 7, full / quick | | about 20 s / 8 s | about 5.5 min |

The large set's per-trace checks: l-mixed 226 and 222 s, l-long 526 and
545 s, l-5000 455 and 461 s (C2's target, a trace of 5,000 transactions at
node size 30 with 1,000 keys in under 10 minutes, met again), l-hot 5 s
each, l-few 89 and 92 s, and l-big62 (node size 62, 3,000 keys, 1,000
transactions) 2,690 and 2,940 s: the slow case, which sets the set's length.
Memory: the checker at most 155 MB; the exporter's JVM at most 1.6 GB.

Files changed: `java/stress/conformance.sh`; `docs/level2-alignment.md`
(sections 10.5 and 12); `docs/evidence/level2-conformance-c3.txt` (new);
this file.

Checks: the sets above; the gates on the work tree with the new
`conformance.sh` (`level2.sh` step 7 runs it), 18:10 to 18:30: `LEVEL 1 OK`
(89 s), `LEVEL 2 OK` (726 s), `LEVEL 3 OK` (343 s); StreamDigest against
`l34-base`: DIGESTS IDENTICAL (36 of 36).

Register: none.

Open, next: L3 (in progress since 17:35, in a scratch copy of `lean/`).


### 2026-10-16 17:35 to 20:24. WP L3, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `3782bc8` to
`e03c2d1` (C3 committed meanwhile); uncommitted: this WP's files only.
Developed in a scratch copy of `lean/`; brought into bergdb when every proof
was done there.

Did:

1. T1-L, `T1_lazy` in `lean/SIS/PhysTheorems.lean` (trusted statement):
   after a run with BergDB's still-dirty test (`javaTest`) that meets the
   assumptions (`RunOK`, and the new `PhysRunOK`), the lazy startup from the
   stream after T(k) (the whole stream, or a prefix: a crash), then any reads
   and writer follows (`Op`, admissible: `OpsOK`): (a) a read at any time
   t ≤ k gives P at t, each node reachable at t with its history at t;
   (b) every canonical object holds its node's whole history; (c) every other
   object holds a version of its node from the stream, all of it or cut back
   to s; (d) a memory slot that a canonical object's node uses at a time t
   leads to a canonical object, or to one that holds a version good for t if
   it holds all of it. The plan's statement ("a version that is good for the
   times at which its parents use it") is (d) for canonical parents; for
   snapshot parents it is part of the proof's invariant (`SnapSlots`,
   `MemInv.snap_slotGood`).
2. The proof, 15 new files in `lean/SIS/Proof/` (7,070 lines; `Fresh`,
   `PhysMem`, `PhysInv`, `PhysFollow`, `PhysLogic`, `PhysRead`, `PhysWriter`,
   `PhysRun`, `PhysPath`, `PhysRerun`, `PhysApply`, `PhysStep`, `PhysLazy`,
   `PhysBase`, `PhysT1`). An invariant of the memory at time K, relative to
   the run's final state (`MemInv`): canonical objects in the node table,
   with the node's history up to K, slots good at every time the node is
   reachable and fresh at K; other objects versions of their nodes; memory
   slots to the table's object or an older version; and canonical objects for
   the nodes of gd(d), s < d ≤ K, the section's index nodes with entries up
   to s, and the nodes with entries in (s, K]. It holds before the rerun at
   K = s (`PCtx.base_ok`), each rerun transaction takes it from K to K + 1
   (`rerunStep_ok`), reads and writer follows keep it (`MemInv.ops_ok`), and
   under it reads give P (`MemInv.read_ok`). Two new facts of every run of
   the logical model, in `Fresh.lean`: `CleanFresh` (a clean reachable
   node's latest version names the latest versions of its live children,
   which are not in D; with `javaTest`) and `DataOnce` (a data node has one
   version). `CleanFresh` is the "lemma of the logical model" that L1's entry
   said L3 would develop; E3 can reuse it for INV-SLOT.
3. Three refinements of the lazy startup in `lean/SIS/Phys.lean` (trusted;
   each found while proving, checked by running before it was proved; M8's
   resolution, "a Lean model of lazy reading"): step 1 leaves out the
   section's nodes with no entries up to s (Java's
   `wasCreatedInRerunSection`; before, a node created after s got two
   canonical objects); a new pointer copies the slot of a canonical object of
   a node reachable at j - 1 (`srcOK`), else the object's own, else any
   canonical object's, taken before the transaction's entries; and every
   pointee of a new entry gets the new pointer's slot (`Obj.putSlot`), also
   one the object had a slot for.
4. Two assumptions of the physical layer (`PhysStep`, for every transaction
   `PhysRunOK`; new register row M47 in `docs/level2-alignment.md`):
   `liveNew` (a node's new live children are pointees of its new entries)
   and `adopt` (a new live child that the transaction does not create was a
   live child of a reachable node that it changes or replaces). On Java:
   `liveNew` by α (level2-alignment 2.4), `adopt` from TREE and A5, which
   are checked (A4, C-A); the argument is in level2-alignment 13.3. Not stop
   rule 4: Java meets both by these arguments and checks.
5. `lean/SIS/PhysExample.lean`: `physStepB`, `physRunOKB` (with `#guard`s on
   examples 2 and 3) and `memInvB`, the proof's invariant by running;
   `lean/PhysTest.lean` checks `memInvB` after the startup and after every
   operation, and `PhysRunOK`.
6. `lean/README.md` (the theorem, the axioms list, the proof files, the
   tests, "Changes to the trusted part" for L3, "Not done");
   `docs/level2-alignment.md` (register M47; 13.1 updated for the
   refinements; 13.2, T1-L as proved; new 13.3, the proof).

Also checked by running, in scratch only (not in the repository): `MemInv`
at the base and after every rerun step, for every state of 20 seeds of 40
transactions of examples 2 (16 algorithms) and 3 (4 policies): 0 failures
in 53,625 checks (78 s); and that this check is not vacuous: the final
memory, checked at K = s, fails it in 48 of 51 states (3 seeds of 16).

Files changed: `lean/SIS/Phys.lean`, `lean/SIS/PhysTheorems.lean`,
`lean/SIS/PhysExample.lean`, `lean/PhysTest.lean`, `lean/README.md`; 15 new
files in `lean/SIS/Proof/`; `docs/level2-alignment.md`; this file.

Checks: the Lean checks of 2.2 on bergdb's `lean/` with these files (20:14
to 20:24): `lake build` passes, 83 jobs, no warnings; `lake exe sistest 20
40`: all checks pass (398 s); `lake exe phystest 20 40`: all checks pass
(257 s; was 28 s before `memInvB`): example 3, four policies, 820 states
each, 6,578 reads each give P, the invariant by running holds after every
startup and operation, `PhysRunOK` holds; 820 of 820 prefixes (crashes) read
P; example 2, 16 algorithms, 4,363 reads each; the axioms of T1, T2, T13,
LM_newer, LM_ruleR and T1_lazy are `propext`, `Classical.choice` and
`Quot.sound`, LM_cutTo's `propext` and `Quot.sound`, the checker's
equalities as before; no `sorry`, `admit`, `axiom` or `unsafe` in `SIS/` and
`Check/`; `sh test-traces/run.sh`: TRACE TESTS OK. No change to `java/`, so
no gates (2.2). Time: 2 h 49 min, within M (2 to 8 h).

Notes on the plan (not changed): T1-L's hypotheses go beyond the plan's
statement: BergDB's still-dirty test (`CleanFresh` needs it; T1 and T2 also
hold for the exact test without a virtual root, T1-L does not claim it) and
`PhysRunOK` (M47). The writer's follows that `OpsOK` admits are those of a
walk down from the root at the last time: live slots of canonical objects of
reachable nodes.

Register: M47 new (argued, a direct check open); M8 and M42 close in L5.

Open, next: L4 (CC, T2-L), on top of `MemInv`. CC is close to T1-L's second
part (every canonical object holds its node's whole history; for the object
the writer reaches, `MemInv.follow_writer`). T2-L needs the invariant after
live transactions too, where Rule R keeps the startup's section while P and
S grow; L3's invariant has one state for both (the state at the restart), so
L4 must split it: the startup stream for Rule R and the versions read, the
current state for P.
