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

* Checkpoints: G0 given (2026-10-16 15:23). **K1 waits for Frans** since
  2026-10-17 05:31: E7 is done, and K1 does not pass automatically, since
  A6 fails on Java (the proofs use A6' and A-COPY instead); the review guide
  is [03-k1-review.md](03-k1-review.md). Until K1: R3 to R8 and stage 4
  wait; R2 and P3 may go on. K2 to K5 open.
* Commits of this run (Q2 (b)): see the log entries.
* Uncommitted work of this plan in bergdb: the files of the WPs in progress,
  named in the last log entry.
* Long jobs running: the Lean tier of the A-COPY check on the large trace
  set (`copyFailures`, the entry of 2026-10-17 03:27; started 03:41, in the
  background, at low priority; 10 of its 12 traces done by 05:48, no
  failure; the two l-big62 traces still run).
* Stage 2's time box (plan, 5.3): started with E1 at 2026-10-16 23:14;
  60 hours, so it ends at 2026-10-19 11:14.
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
| L4 | The writer after a lazy startup: CC, T2-L | done | 2026-10-16 |
| L5 | Lazy reading checked against Java | done | 2026-10-16 |
| E1 | Design: eviction, references, pins | done | 2026-10-16 |
| E2 | The physical model with eviction, executable | done | 2026-10-17 |
| E3 | INV-SLOT and the physical writer: T-CACHE | done | 2026-10-17 |
| E4 | Reads under eviction: T-READ | done | 2026-10-17 |
| E5 | Restarts with eviction: T2-C | done | 2026-10-17 |
| E6 | Pins and index-freedom | done | 2026-10-17 |
| E7 | The Java change list; the K1 review | done | 2026-10-17 |
| R1 | α and the register for reclaim | done | 2026-10-16 |
| R2 | Trace format 2; the exporter for reclaim runs | done | 2026-10-17 |
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
| P2 | The Level 3 soak | done | 2026-10-17 |
| P3 | Bounds, measured | done | 2026-10-17 |
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


### 2026-10-16 20:27 to 21:17. WP L4, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `0f7db33` (L3);
uncommitted: this WP's files only. Developed in the scratch copy of `lean/`
that L3 used; brought into bergdb when every proof was done there.

Did:

1. The writer after a lazy startup, in `lean/SIS/Phys.lean` (trusted): a
   read returns, for each node it reaches, the node its object gives at the
   time, with level and kind (`Mem.readAt`, `Obj.nodeAt`; before, the
   history only), so the writer's view of P is a read (`Mem.view`);
   `stepWith`, steps 2 to 8 of `step` with the change given
   (`step_eq_stepWith`, by `rfl`); the writer's transaction (`lazyTrans`: the
   change from the view it reads at i - 1; it reaches the nodes of its paths,
   highest level first, and applies the change to the canonical objects, as
   the rerun does; Rule R and the versions read from the stream of the last
   startup, M42); a run with lazy restarts (`runLazy`: the logical startup
   for ⟨P, D, S⟩, as `runRestarts`, and the lazy startup for the memory).
2. CC (`CC_canonical`): in a run with lazy restarts, after any transaction,
   every canonical object holds its node's whole history (that of the run
   without restarts). T2-L (`T2_lazy`): such a run appends exactly the
   records of the run without restarts. Both in `lean/SIS/PhysTheorems.lean`,
   with BergDB's still-dirty test and `PhysRunOK`, as T1-L. T1-L's first
   part restated for reads that return nodes: a read reaches exactly the
   nodes reachable at t, each with its node in P@t.
3. The proof: `lean/SIS/Proof/PhysFrozen.lean` (429 lines) and `PhysT2.lean`
   (400 lines), and small changes to `PhysInv`, `PhysFollow`, `PhysRead`,
   `PhysRerun`, `PhysLazy` and `PhysT1`. After a lazy startup at k1 the
   memory is read against the frozen run: the same transactions with the
   startup pos frozen from k1 on (`frozenAlgo`), which has the run's P,
   takes no node after k1 and writes only new data nodes, so its states only
   grow (`frozen_grow`, `DbGrow`) and L3's invariant carries over to the next
   one (`MemInv.transfer`). With streams that agree on the nodes without
   canonical objects (`StreamAgree`, `follow_congr`, `read_ok` and
   `reachFold_congr` for a follow stream), each transaction keeps the run's
   invariant (`LazyInv`, `lazyInv_step`): the view read is P's, the paths are
   reached, and the change applied takes the invariant from j to j + 1; a
   restart is T1-L. No change to L3's invariant was needed.
4. Checked by running before the proofs: `checkLazy` in
   `lean/SIS/PhysExample.lean` (`#guard`s on examples 2 and 3) and in
   `phystest` (`frozenB`, the frozen algorithm, for `memInvB`): after every
   transaction of runs with lazy restarts, the writer's view is P's, the
   records are the run's, every canonical object is whole, and the memory
   meets the invariant for the frozen run.
5. `lean/README.md` (the theorems, the axioms list, the proof files, the
   tests, "Changes to the trusted part" for L4, and what T2-L does not cover
   yet: the versions and references the writer writes come from `mkVersion`,
   and steps 3 and 7 from P; from the objects and slots is stage 2, E3);
   `docs/level2-alignment.md` (13.2: CC and T2-L proved; new 13.4).

Files changed: `lean/SIS/Phys.lean`, `lean/SIS/PhysTheorems.lean`,
`lean/SIS/PhysExample.lean`, `lean/PhysTest.lean`, `lean/README.md`;
`lean/SIS/Proof/PhysInv.lean`, `PhysFollow.lean`, `PhysRead.lean`,
`PhysRerun.lean`, `PhysLazy.lean`, `PhysT1.lean`; new
`lean/SIS/Proof/PhysFrozen.lean` and `PhysT2.lean`; `docs/level2-alignment.md`;
this file.

Checks: the Lean checks of 2.2 on bergdb's `lean/` with these files (21:03 to
21:16): `lake build` passes, 85 jobs, no warnings; `lake exe sistest 20 40`:
all checks pass (398 s); `lake exe phystest 20 40`: all checks pass (371 s),
including the runs with lazy restarts: example 3, four policies, and example
2, the eight algorithms with BergDB's test, 800 transactions each, 0 failing
T2-L, CC or the invariant (9,600 transactions); the axioms of T1, T2, T13,
LM_newer, LM_ruleR, T1_lazy, CC_canonical and T2_lazy are `propext`,
`Classical.choice` and `Quot.sound`, LM_cutTo's `propext` and `Quot.sound`,
the checker's equalities as before; no `sorry`, `admit`, `axiom` or `unsafe`
in `SIS/` and `Check/`; `sh test-traces/run.sh`: TRACE TESTS OK. No change
to `java/`, so no gates. Time: under an hour, within M.

Notes on the plan (not changed): T2-L's "whose writer reaches nodes through
the physical layer" is formalized as: the writer's change comes from the view
it reads through the physical layer, and it reaches the nodes of its paths
through the writer's follows, which make them canonical; steps 2 to 8 of the
record still use ⟨P, D, S⟩, as the README now says. Stage 1's theorems are
done (LM, T1-L, CC, T2-L); stage 1 also needs C-L (L5) and M8 closed.

Register: none closed (M8 and M42 close in L5).

Open, next: L5 (Java's first touches checked against the rule: a test-only
hook in `NodeCollection.followStreamPointer`, FIRST and SKIPT lines, trace
format 2, C-L in the checker; and review-13-claude 7.1's root queries and
layout check, see the adoptions above).


### 2026-10-16 21:17 to 22:08. WP L5, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `e24e633` (L4);
uncommitted: this WP's files only.

Did:

1. A test-only hook in `java/src/bergdb/core/NodeCollection.java`:
   `FirstTouchListener` and the static field `firstTouchListener`, null
   unless a test sets it (then nothing is called; plan 2.1).
   `followStreamPointer` tells it of each first touch of a stream pointer:
   the node, the position after Rule R, the object taken, whether the version
   was read, whether it was cut back. No other change to production code.
2. `java/stress/TraceExport.java`, trace format 2 (plan 8.2): FIRST lines in
   run B (from each restart's own rerun up to the next restart, in the
   restart's `TX` block), SKIPT lines (the skip slots' cached times, M29),
   and, with `live=1`, the root's LIVE lines at every time t ≤ i on each
   record, at the record's time and at the last Java time before the next
   (review-13-claude 7.1 and 5.2, adopted above for L5).
3. The checker (`lean/Check/Trace.lean`, `Check/Steps.lean`,
   `TraceCheck.lean`; not trusted): reads format 1 and 2; C-L
   (`firstFailures`): every FIRST line follows `Phys.lean`'s rule (Rule R
   from the startup's section, the node table's canonical object or a
   snapshot at least as new, or the version named, cut back exactly when it
   is a key node version of R(s) on); in C-S, each top node version's skip
   slots: the set bits of its ordinal, the formula's targets, the targets'
   creation times (`topFailures`, failures named `skip`). Test traces
   `badfirst.trace` and `badskip.trace` (`test-traces/run.sh`).
4. `java/stress/conformance.sh`: a C-L line in the summary; the small set
   gets a sixth configuration, `hot` (one key at node size 8, the root
   queried at every time: about 75 top nodes per trace).
5. Docs: `docs/level2-alignment.md` (9.2: format 2; register M8 and M42
   closed; 12: the small set's times; new 13.5: C-L and its results);
   `docs/level4-alignment.md` (M29: L5's part done); `docs/levels.md`
   (Level 2: lemma M proved, lazy reading proved and checked; "Argued, not
   proved" updated); `lean/README.md` (the checker, stage 1 done, "Not
   done").

Results (bergdb `e24e633` with these changes; `docs/level2-alignment.md`,
13.5): small set, 60 traces, `CONFORMANCE OK`, C-L 0 of 252,539 FIRST lines
fail, C-V 1,870,868 LIVE lines with no difference, 19 s; medium set, 9
traces, `CONFORMANCE OK`, C-L 0 of 43,873, 45 s; the large set's `l-hot`
configuration (501 top nodes), seeds 1 and 2, `TRACECHECK OK`, 4,425 SKIPT
lines each, C-L 0 of 4,961 and 0 of 4,920. Of the small set's first touches, 137,473 found a
canonical object, 22,352 a snapshot and 92,714 read a version; none was cut
back (M22: not reachable today).

Files changed: `java/src/bergdb/core/NodeCollection.java`;
`java/stress/TraceExport.java`, `java/stress/conformance.sh`;
`lean/Check/Trace.lean`, `lean/Check/Steps.lean`, `lean/TraceCheck.lean`,
`lean/test-traces/run.sh`, new `lean/test-traces/badfirst.trace` and
`badskip.trace`; `lean/README.md`; `docs/level2-alignment.md`,
`docs/level4-alignment.md`, `docs/levels.md`; this file.

Checks: the gates on the work tree with these changes, full, one after the
other (21:34 to 21:54): `LEVEL 1 OK` (91 s), `LEVEL 2 OK` (726 s; its step
7: 60 traces, `TRACECHECK OK` 60), `LEVEL 3 OK` (342 s); unit tests 911
successful, F tests 37 successful; StreamDigest against `l34-base`: DIGESTS
IDENTICAL (36 of 36), so the hook changes no record. The Lean checks of 2.2
(21:55 to 22:07): `lake build` passes, 86 jobs, no warnings; `lake exe
sistest 20 40` and `lake exe phystest 20 40`: all checks pass (398 and
369 s); the axioms as in L4; no `sorry`, `admit`, `axiom` or `unsafe` in
`SIS/` and `Check/`; `sh test-traces/run.sh`: TRACE TESTS OK, with the two
new traces. Time: about 1 hour, within M.

Notes for Frans: the small set of `conformance.sh`, which `level2.sh` runs in
its step 7, now has six configurations (60 traces in full mode, 12 in quick
mode; K4's adoption said 50 and 10): the new one, `hot`, makes the gate check
the top nodes' layout and the root search's predecessor branch, and adds
about 3 seconds. It strengthens the step and changes no other; revert the
line in `small()` if the old set is wanted.

Register: M8 and M42 closed; M29 (L5's part done, J3's open).

Stage 1 (plan 5.3) is done: LM, T1-L, CC and T2-L proved; C-L passes on the
small and medium sets; M8 closed by proof.

Open, next: P2 (the Level 3 soak), then P3 and R1; E1 starts stage 2 and its
time box.


### 2026-10-16 22:10. WP P2, in progress (written before the pilot)

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `a66e4d9` (L5);
uncommitted: `java/stress/Soak.java` and `java/stress/soak.sh` (new).

Did so far:

1. `java/stress/Soak.java`: the soak of level3-plan task 2. A `FileStream`
   in a disposable directory (a marker file, as `Perf`), the system clock,
   retention in wall-clock seconds; one paced writer, two to four paced
   readers (latest and historical gets, also just around the first
   available lookup time; forward and backward scans at the latest or a
   historical time); updates, deletes and reinserts; a hot set (half of it
   long keys) and uniform keys; long keys of 120 bytes. A bounded model
   (per key, the versions a lookup at or after a "keep" time can see; keep
   never passes a lookup time a reader has announced), so every successful
   operation is checked at its actual snapshot, scans for completeness too;
   expiries counted at admission and during, never in place of a check.
   Phases: load, warm-up (until the first physical cut), the measured phase
   (steady seconds, restarts and their checks excluded), the end check.
   Cold restarts spread over the measured phase, each checked: every key at
   the latest time, the hot keys and 20,000 others at six times from the
   first available lookup time to the latest; every key at every time with
   at most 20,000 keys (the companion case). Streaming histograms
   (`PerfUtil.Hist`), the slowest commits with whether reclaim stepped or
   decided a cut in them, reclaim iterations, cut decisions and physical
   cuts with their uptimes, memory, storage and dirty-node samples.
2. `java/stress/soak.sh NAME [PROP=VALUE ...]`: runs it from a copy of the
   build in `java/build/soak/NAME/` (so `build.sh` cannot change it), with
   the flags of `performance.sh` (G1, fixed heap, assertions off, the same
   GC and safepoint log), records the source, JVM and machine, then
   `Soak finish` adds the GC log's pauses per phase and the pauses that
   overlap the slowest commits.
3. Tests at a tiny scale (2,100 keys, retention 5 s, a 5 MB startup
   distance): `SOAK OK`, 90 steady seconds, 19 physical cuts, 3 restarts,
   337k gets and 189k scans checked, 13,725 expired at admission. An
   earlier tiny run showed that a durable commit (`sync(ORDINARY)`) takes
   about 113 ms on this machine, so the default is one durable commit a
   second, and that the default startup distance (50 MB) spaces reclaim
   iterations by 100 MB of stream (Reclaim's ITERATION_SPACING).

Running: the pilot (`soak.sh pilot2`, started 22:43; `pilot1`, started
22:41, was stopped after a minute: its readers spun while pacing, three
busy cores; they park now): one million keys
plus 1,000 long keys, 1,000-byte values, retention 300 s, 300 transactions
a second of 10 keys (about 0.9 updates per key per retention window,
paced), three readers at 5,000 operations a second each, G1 with
`-Xms12g -Xmx12g`; warm-up until the first physical cut (at most 40
minutes), 15 measured minutes with one restart. It calibrates the rate and
the heap (memory growth, the cut cadence, commit latency) for the main run;
no gates, performance runs or Lean builds while it runs.


### 2026-10-16 22:44 to 22:59. WP R1, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `a66e4d9`;
uncommitted: P2's `java/stress/Soak.java` and `soak.sh` (in progress, not
part of this WP) and this WP's files. Written while P2's pilot ran (document
work only, plan 2.7).

Did: `docs/level3-alignment.md`, sections 2 to 5, from `Reclaim.java`,
`Db.java`, `DbStarter.java`, `NodeCollection.java`, `FileStream.java` and
`BufferedStream.java` at `a66e4d9`, levels.md ("Level 3: reclaim"), the
plan's 8.1 and 8.7, F1-008-07 (sections 5 to 8) and Codex's review of 09
(findings 2, 5, 6):

1. α for reclaim (section 2): the three kinds of record and their order
   within one `transactionCompleted` call (zero to five internal records
   after a user record); T(i) of a step (the rewrites and the current row)
   and of a table store; touch(i) (the nodes `touchRange` visits over
   (touchFrom, touchTo], marked before the puts, computed on P@(i-1) at
   time i); the iteration's positions and times as records and model times;
   fa(i) as a function of the records (it never decreases and stays before
   the startup pos); a cut decided at R(d) at c = the record at the row's
   pCut, f = tEnd, made later, at or below c; what R2's trace needs (2.7).
2. The register, checked again at `a66e4d9` (line numbers updated:
   `resolvePointers` 317, `canonicalNode` 455, `topNodeOfLastTransaction`
   293; `Reclaim.java` and `Db.java` are unchanged since `75d3c2d`).
3. The arguments (section 4): M32 (Java's startup uses f only after the
   reconstruction, and reads nothing before c if the cut is safe; the rest
   is T8, R4) and M38 (the conflict check runs before any change, so a
   failed step is no transaction; it cannot fail today, since no
   transaction runs between a step's reads and its check). M35 and M37 are
   settled by α.
4. The safety argument of levels.md in the model's terms (section 5), in
   ten steps against the plan's sketch of CutOK, each marked: checked
   (order, the take rule, the meta block and durability), assumed (the
   retention policy; the coverage of a step's range traversal, which R6
   takes as an assumption on the touch and R2's traces check), to prove
   (values from f on, index nodes and the root chain, references after
   pSafe: R6; historical nodes in D, M33 and M34: R5 or R8; T8, T9, T12:
   R4, R5).

Files changed: `docs/level3-alignment.md`; this file.

Checks: the links of `level3-alignment.md` resolve; every statement about
code names the file, the method and the line at `a66e4d9`; the test names
cited exist (`Reclaim.Tester`'s `testIterationRewritesAllOldValues`,
`testDeletedKeysAfterCut`, `testCutKeepsMetaBlockTransaction`,
`testLookupsFromFirstAvailableTime`; `ReclaimRetentionTester`). Time: about
a quarter of an hour of writing on top of the reading, within M.

Register: M32 and M38 argued (R1); M35 and M37 resolved by α (R1), to be
checked by R2's traces; no new rows. Noted: `pSafe` is the stream length
after the user record of its call, a little before that call's internal
records (section 5, step 6 allows it).

Open, next: P2 continues (the pilot runs). R2 can start after R1 and C2
(it needs no K1); R3 waits for K1.


### 2026-10-16 23:13. WP P2, in progress: the pilot's result, the main run (written before it)

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `309243b` (R1);
uncommitted: `java/stress/Soak.java`, `java/stress/soak.sh`.

The pilot (`java/build/soak/pilot2/`, 22:43 to 23:11; one million keys,
300 transactions a second, `-Xms12g -Xmx12g`): `SOAK OK`, 900 steady
seconds, 269,179 commits (299.1 a second, 0.90 updates per key per retention
window), 8,370,238 gets and 4,689,717 scans (234 million KVs) checked at
their snapshots, no failure, 335,470 reads expired at admission (the reads
just below the first available lookup time), none during, none unverifiable;
three physical cuts (one in the warm-up), one restart (started in 0.95 s,
5,678 transactions rerun; its check, 1,127,000 gets, 13.1 s). What it showed
for the calibration:

1. Memory grows with the updates and nothing gives it back: the heap after
   young collections rose by about 4 MB a second, about 1.3 KB per update,
   cuts or not (Level 3 keeps every node it has ever made or read: `Cache3`
   entries are never removed, level4-alignment.md M25, M26). A restart starts
   from a new, lazily loaded database (about 4.4 GB after the check had read
   every key); the old one is garbage then. In the 12 GB heap the restart's
   check (the old database not yet collected, the new one loading) ended in
   a full collection of 2.6 s, the run's longest pause.
2. The first iteration rewrote the loaded data in about 470 s; later ones
   took 240 to 270 s, one physical cut each, with the first available lookup
   time 300 to 750 s old (each cut is decided when tEnd is exactly the
   retention old; the iteration after the first cut cannot cut until the one
   after it ends).
3. The slowest commits (136 and 39 ms) are the physical cuts: the commit
   whose reclaim call deletes the files (`FileStream.pretruncate`, one
   directory force per file). Durable commits take 70 to 148 ms (the buffer's
   flush interval).

The main run, frozen from that (`soak.sh main1`, started 23:12:41): the pilot's
workload (one million keys plus 1,000 long keys, 1,000-byte values, retention
300 s, 10 keys a transaction, three readers at 5,000 operations a second,
one durable commit a second), at 200 transactions a second (about 0.6
updates per key per retention window, paced), with `-Xms24g -Xmx24g` (the
plan's limit, 2.4), so that the memory between restarts (about 2.7 MB a
second) and a restart's transient fit with room; warm-up until the first
physical cut (at most an hour); 7,200 steady seconds with three cold
restarts at 30, 60 and 90 minutes, extended up to an hour if it has fewer
than 10 physical cuts. Expected end: about 02:15. Meanwhile: no gates,
performance runs or Lean builds; document work (E1).


### 2026-10-16 23:14 to 23:25. WP E1, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `309243b`;
uncommitted: P2's `java/stress/Soak.java` and `soak.sh` (in progress) and
this WP's files. Written while P2's main soak runs (document work only, plan
2.7); its inputs were read from 22:59 on, during the pilot. Stage 2's time
box starts here (23:14).

Did: `docs/level4-alignment.md`, section 5, "The design", from the plan's
8.5 to 8.8, level4-plan.md (sections 1 to 7 and 10), reference-theory.md
and `lean/References/SISCase.lean`, F1-008-07 (sections 3, 4, 8), F1-008-08
(sections 2, 9, 10), Codex's review of 09 (findings 2, 4, 7), A4's probes
and L1's `Phys.lean`; Java's `TopDs.newSuperRoot`, `KeyNode`'s copies,
`DbStarter.createMemoryPointers` and `NodeCollection.resolvePointers` at
`a66e4d9`:

1. The physical layer, part 2 (5.2): the pinned set (D's canonical objects
   and the root's object); eligibility; unswizzle (the slot names the
   target's position, so its serialized reference does not change); release;
   the Level 4 loader of Q7 (the canonical object, or the exact version after
   Rule R; the node table names canonical objects only; no cut-back after
   startup); promotion; the physical writer (references from slots and the
   pinned set by id, Rule R; Rule A by id against the pinned set, which is
   `javaTest`); startup with rule 4; cache schedules.
2. Option K worked out (5.4): INV-SLOT made precise, with a second half (a
   slot to a pinned node that is not a memory slot to its canonical object
   belongs to an object written no later than that node), which makes
   unpinning safe. A table of every way a slot changes against the only way
   lv(y) moves, and the five kinds of slot (live; dead with the pointee
   current, by A6'; dead with the pointee not current, by Rule A's coupling;
   historical in D; after a restart). The restart gap of the plan's 8.5
   (M44) is closed by rule 4, startup linking D's objects by id, which needs
   no runtime window and gives today's records; the window stays the
   fallback. Checked by hand: SISCase (excluded by A6 and A6'), the two
   component cases of level4-plan.md 2.1 (excluded by the loader and
   resolution rules, and by INV-SLOT).
3. Found: Java copies slots as pairs (splits; `TopDs.newSuperRoot` inherits
   a stream skip slot as a stream slot, lines 77 to 90). A copied stream slot
   to a pinned node would go stale; argued that it cannot happen in Java
   (case 1 for key node copies; for skip slots, a super root pointing to an
   older top node in D is itself in D, so rule 4 links it after a restart),
   to be checked by E2 (example 5: a root split after a restart while an
   older top node is in D) and by the exporter (C-P).
4. The assumptions (5.5): TREE and A6' (not A6: A4 found A6 false in 5 of
   68,901 Java transactions, A6' true in all), per transaction, in a
   structure of their own (`EvictStep`), not in `StepOK`; D closed upward to
   be proved in E3 (F1-008-08's T15, for marking and `javaTest`).
5. The statements of stage 2 in plain English (5.6): T-CACHE, T-READ, T2-C,
   T-PIN, T-INDEX (the writer reads slots, the pinned set and Rule R's
   section map only).
6. What Java must change and keep (5.7), for R8 and the J WPs.
7. The register: M20, M21, M22, M27, M31, M43 (A6' chosen), M44 (rule 4
   chosen) updated.

Files changed: `docs/level4-alignment.md`; this file.

Checks: the links of `level4-alignment.md` resolve; statements about code
name file, method and line at `a66e4d9`. No model or code changed (E1 is a
design WP; E2 implements it).

Register: M43 resolved for the model (A6' and TREE as assumptions); M20,
M21, M22, M27, M31 and M44 designed (E1), open for E2 to E6 and R8.

Notes for Frans: K1's automatic pass (plan, section 3) asks that "A6 and
TREE hold on every Java run checked". A6 does not (A4); the design uses A6',
which does. Unless Frans accepts A6' in place of A6, K1 will need his
decision even if every theorem of stage 2 is proved.

Open, next: E2 (the executable physical model with eviction, and its random
tests): it needs Lean builds, so it waits for the end of P2's measured
hours (about 02:15); until then, document work (R2's format, or P2's
report skeleton).


### 2026-10-17 01:31. WP P2, in progress: the main run's result, the companion (written before it)

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `065c21f` (E1);
uncommitted: P2's `java/stress/Soak.java` and `soak.sh`, `docs/level3-soak.md`
(draft), this file.

The main run (`java/build/soak/main1/`, 23:12:41 to 01:30:02, exit 0):
`SOAK OK`, 7,200 steady seconds, 1,438,664 commits (199.8 a second),
67,378,447 gets and 37,733,061 scans checked at their snapshots, no failure,
19 physical cuts in the measured phase, three cold restarts with their checks
(1,127,000 gets each), 2,696,284 reads expired at admission and none during;
in the measured phase 143 GC pauses, 25.3 s in all, the longest 3.3 s (to be
analysed in the report). During the main run, other work ran at the lowest
priority (`nice -n 19`, one core at a time): single Lean files of E2 and E3
in a scratch copy, and E2's random tests (`phystest 20 40 evict`, 00:36 to
00:38). The plan's rule for the measured hours (no gates, performance runs or
full Lean builds) allows it; the 23:13 entry said "no Lean builds", which was
stricter than the plan and not kept. The report checks the slowest commits
against those times.

Next, the companion (`soak.sh comp1`, started now): 20,000 keys and 200 long
keys, retention 60 s, 100 transactions a second, `-Xms4g -Xmx4g`, 1,200
steady seconds, three restarts, at least ten physical cuts, every key checked
at 11 times at every restart and at the end (the exhaustive check of a small
key space). Expected end: about 02:10. Meanwhile: the report, Lean work in
scratch at `nice -n 19`.


### 2026-10-16 21:17 to 2026-10-17 02:02. WP P2, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `065c21f` (E1);
uncommitted before this WP's commit: its files, below.

Did: the soak of level3-plan task 2 (the entries at 22:10, 23:13 and 01:31
record the tool, the pilot and the runs as they went).

1. `java/stress/Soak.java` and `java/stress/soak.sh` (new; 22:10 entry).
2. The pilot (`pilot2`, 22:43 to 23:11, `SOAK OK`) calibrated the main run:
   memory grows by about 1.3 KB per update and only restarts give it back,
   so the main run kept the pilot's scale and workload at 200 transactions
   a second in a 24 GB heap (23:13 entry).
3. The main run (`main1`, 23:12:41 to 01:30:02): `SOAK OK`. Two steady hours
   at one million keys and a five-minute retention, 1,438,664 commits (199.8
   a second), 19 physical cuts, three cold restarts with their checks;
   67,378,447 gets and 37,733,061 scans checked at their snapshots, no wrong
   result, 2,696,284 reads expired at admission and none during.
4. The companion (`comp1`, 01:31:15 to 01:54:37): `SOAK OK`. 20,000 keys, a
   one-minute retention, 1,200 steady seconds, 12 physical cuts, three
   restarts; every key at 11 times after each restart and at the end
   (exhaustive), 11,246,785 gets and 6,301,138 scans checked, no wrong
   result.
5. `docs/level3-soak.md`: the report (result, what runs, the pilot and the
   scale, the main run, latency, the worst pauses, memory and storage,
   restarts, the companion, what it does not show, where the data is), with
   the runs' `source.txt`, `stdout.txt` and trimmed `result.json` in
   `docs/evidence/level3-soak/`. `docs/level3-plan.md`: task 2 done.

Findings (the report has the numbers):

* Reclaim bounds the stream: 3.6 to 6.7 GB on disk while 28.8 GB were
  appended; one iteration (320 to 480 s, rewriting 140,000 to 600,000 live
  values) and one cut, decided when the iteration's end was the retention
  old; the first available lookup time 303 to 1,069 s old.
* Commits: 0.26 ms at the median, 0.59 ms at p99. In the main run the tail
  (up to 208 ms) is G1's young collections; the commits that delete files
  (`FileStream.pretruncate`, a directory force per file) take 59 to 111 ms
  and are the slowest in the companion and the pilot.
* The longest pauses (3.3 s, and two Remark pauses of 1.6 s) come within
  three minutes after a restart and are mostly system time (8.4 s of system
  time in the 3.3 s pause): page faults of a heap that is not pretouched, I
  think. P4 should pretouch its heap (`-XX:+AlwaysPreTouch`), to separate
  this from collection work.
* Memory grows by 2.6 to 2.9 MB a second between restarts; at that rate the
  24 GB heap would have run out after about two hours without restarts.
  Level 4's eviction is what is to bound it; P4 measures that.

Checks: `build.sh` passes with `Soak.java` (02:00; java/stress only, so no
gate is required); the tool ran on tiny configurations (t1 to t4), the
companion (small), the pilot and the main run (the plan's scale).

Not as planned: the 23:13 entry said "no Lean builds" during the main run,
which was stricter than the plan's rule (no gates, performance runs or full
Lean builds) and was not kept: single Lean files of E2 and E3 and E2's random
tests (`phystest 20 40 evict`, 00:36 to 00:38) ran at `nice -n 19`, one core
at a time. None of the slowest commits or the long pauses falls in the
random tests' window; the report says the effect is not measured.

Time: P2 is M (2 to 8 hours) plus machine time: about 2.5 hours of agent
work over 4.7 hours, and 3.6 hours of runs.

Register: none changed (the measurements are for P3, P4 and J7).

Open, next: E2's Lean checks and commit (its model was revised during E3,
see the next entries), then E3.


### 2026-10-16 23:25 to 2026-10-17 02:23. WP E2, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `065c21f` (E1)
at the start and `e5b643b` (P2) at the end; uncommitted before this WP's
commit: its files, below. The model was written and run in a scratch copy of
`lean/`, at the lowest priority during P2's measured hours (single files and
the random tests, no full builds; the 01:31 entry); its full checks ran after
P2, on a clean copy.

Did:

1. `lean/SIS/Evict.lean` (new, trusted, executable): the physical layer,
   part 2, as E1 designed it (`docs/level4-alignment.md`, 5.2): the pinned
   objects, unswizzle and release; the Level 4 loader (`Mem.follow4`) and
   reads through it; the writer's path and the change; startup with rule 4
   (`evictStartup`); the physical writer (`Mem.refOf`, `writeNodes`,
   `evictTrans`); cache schedules (`CacheOp`) and runs with restarts
   (`runEvict`); the assumptions of stage 2 (`EvictStep`: TREE and A6';
   `CopyStep`: A-COPY; `EvictRunOK`).
2. `lean/SIS/EvictExample.lean` (new): the invariants by running (INV-CAN,
   INV-SNAP, INV-SLOT, no dangling slot), the cache schedules, and
   `checkEvict` after every transaction of a run: the records and D are
   `step`'s, reads at the last time, at half of it and at a random time give
   P at that time, and the invariants hold; TREE, A6' and A-COPY by running;
   example 5 (example 3 with drops, so that a subtree goes cold).
   `lean/PhysTest.lean`: the eviction part of `phystest` (also alone:
   `lake exe phystest 20 40 evict`). `lean/SIS.lean` imports both files;
   `lean/README.md` describes them.
3. Revised during E3 (`level4-alignment.md`, 5.10, new), each change run
   before a proof relied on it: the writer's walk follows every slot of its
   paths, as Java's `WriterFollower` does; a new pointer's slot comes only
   from a canonical object of a node reachable before the change (stage 1's
   last resort, any canonical object's slot, is gone), which needs a new
   assumption, A-COPY; and a fourth cache schedule, unswizzles and releases
   apart, since the plan's three never leave an object in memory with some of
   its slots unswizzled.

Result: examples 2 (8 algorithms), 3 and 5 (2 policies each), with restarts
and the four schedules, 20 seeds of 40 transactions each: 25,600
transactions, none fails, and TREE, A6' and A-COPY hold on every run. Before
the revision, with the plan's three schedules, 19,200 transactions passed
too (00:36 to 00:38). A mutation shows that the tests see rule 4: without it
(no linking by node id at startup), example 3 writes a wrong record after a
restart (seed 8), the gap of the plan's 8.5. No counterexample to Option K
was found.

Not as planned: example 5 has one root split a transaction, not two root
changes in one transaction (plan, 8.6): the model's assumptions exclude two
(every node a transaction creates or changes is reachable after it), and
Java splits a node of the same transaction in place (F1-008-11's D1).

Files changed: `lean/SIS/Evict.lean`, `lean/SIS/EvictExample.lean` (new);
`lean/PhysTest.lean`, `lean/SIS.lean`, `lean/README.md`;
`docs/level4-alignment.md` (5.9, 5.10, M43); this file.

Checks (plan, 2.2), on a clean copy (bergdb's `lean/` at `e5b643b` with
this WP's five files), 02:04 to 02:20: `lake build` exit 0, no warnings;
`lake exe sistest 20 40`: all checks pass; `lake exe phystest 20 40` (with
the eviction part): all checks pass; `#print axioms` of the theorem list:
standard axioms only; no `sorry`, `admit`, `axiom` or `unsafe` in `SIS/` and
`Check/`; `sh test-traces/run.sh`: TRACE TESTS OK. No Java change, so no
gate.

Register: M43 (A-COPY added; holds on the model's runs, not yet checked on
Java).

Notes for Frans: A-COPY is a new assumption of stage 2, of the same kind as
A6': the pointer of a new entry names a node the transaction creates, a node
of the writer's paths, or a pointee of a node of the paths. Java's writer
meets it by construction, I think (a split copies the split node's pointers,
`TopDs.newSuperRoot` the old super root's skip pointers), but it is not yet
checked on Java runs; the trace checker can do it (with R2's exporter, or in
F1). K1 then needs it accepted together with A6'.

Time: E2 is M (2 to 8 hours): about 2.9 hours, interleaved with P2's runs
and E3's proofs.

Open, next: E3, in progress in the scratch copy: T-CACHE for runs without
restarts is proved from the invariant of the startup's memory; next, that
the startup from R(0) gives it, then E3's checks and commit.


### 2026-10-16 23:48 to 2026-10-17 02:57. WP E3, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `065c21f` (E1)
at the start and `ca2616c` (E2) at the end; uncommitted before this WP's
commit: its files, below. The proofs were written in the scratch copy of
E2's model, at the lowest priority during P2's measured hours, and checked
in full on a clean copy after E2's commit.

Did:

1. T-CACHE, stated in the trusted `lean/SIS/PhysTheorems.lean` as
   `TC_records`: in a run of BergDB's algorithm (`javaTest`, with marking)
   that meets the assumptions (`RunOK`), those of the physical layer
   (`PhysRunOK`) and those of stage 2 (`EvictRunOK`: TREE, A6' and A-COPY),
   from the Level 4 startup from R(0), with any cache schedule and no
   restart, after every transaction and its cache operations: the state is
   the model's (the physical writer appended exactly the model's records and
   left the model's D), and INV-CAN, INV-SNAP, no dangling slot and INV-SLOT
   hold (INV-SLOT: writing a relevant object now would give every pointee its
   latest version, and the second half of `level4-alignment.md` 5.4). Since
   the schedule is any, this holds after every operation. Restarts are E5's
   (T2-C).
2. D closed upward (F1-008-08's T15), which the plan expected E3 to need: it
   does, and it is stated alone too (`T15_closed`): a written current node
   with a node of D below it is in D; a current written node not in D has no
   pointee in D, and its latest version names the latest version of each
   pointee. Marking and `javaTest` give the first; A6' the second, for dead
   pointees.
3. The proofs, `lean/SIS/Proof/Evict*.lean` (14 new files, about 6,600
   lines): the invariant `EInv` (5.3 made precise; 5.10), kept by the
   loader, reads, unswizzles and releases, and by each transaction (the
   writer's view is P; the walk; the change, with TREE and A-COPY; the two
   loops of writes give the model's versions; INV-SLOT across D's changes);
   the startup from R(0) gives it (`einv_init`). Outline in
   `level4-alignment.md`, 5.11 (new).
4. While proving, three changes to E2's model (the writer's walk follows
   every slot of its paths; a new pointer's slot comes only from a node
   reachable before the change, with A-COPY; a fourth cache schedule), each
   run before a proof relied on it; they are in E2's commit (the E2 entry).
5. `lean/README.md`: the files, the statements, the axioms list, the
   history. `docs/level4-alignment.md`: 5.6 (T-CACHE proved without
   restarts), 5.11 (new), M20, M21, M31, M43.

Files changed: `lean/SIS/PhysTheorems.lean`; `lean/SIS/Proof/EvictLogic.lean`,
`EvictWrite.lean`, `EvictInv.lean`, `EvictFollow.lean`, `EvictPromote.lean`,
`EvictPath.lean`, `EvictRead.lean`, `EvictApply.lean`, `EvictApplyInv.lean`,
`EvictWrites.lean`, `EvictStepInv.lean`, `EvictTrans.lean`, `EvictRun.lean`,
`EvictInit.lean` (new); `lean/README.md`; `docs/level4-alignment.md`; this
file.

Checks (plan, 2.2), on a clean copy (bergdb's `lean/` at `ca2616c` with this
WP's 16 files), 02:34 to 02:49: `lake build` exit 0, no warnings (and each
of E2's and E3's 17 files elaborated alone, 02:37: no message); `lake exe
sistest 20 40`: all checks pass (02:41); `lake exe phystest 20 40`: all
checks pass (02:49); `#print axioms` of the theorem list with
`T15_closed` and `TC_records`: standard axioms only; no `sorry`, `admit`,
`axiom` or `unsafe` in `SIS/` and `Check/`; `sh test-traces/run.sh`: TRACE
TESTS OK. No Java change, so no gate.

Register: M20, M21 and M31 (the model's side proved, for runs without
restarts); M43 (the proof uses TREE, A6' and A-COPY).

Notes for Frans:

* T-CACHE rests on A6' and A-COPY, not A6 (the E1 and E2 entries): K1 needs
  both accepted, and A-COPY checked on Java.
* `TC_records` covers runs without restarts. With restarts (E5) the
  invariant must hold after a startup from any stream, where D is not empty
  and rule 4 links D's objects: the largest open piece of stage 2, I think.
* The statement's INV-SLOT says what Java's writer needs (`Mem.refOf` gives
  the latest version of every pointee of an object it may write). The
  proof's invariant has one more part (the live slots of current canonical
  objects, a virtual root's too), which the statement leaves out.

Time: E3 is L (8 to 24 hours): about three hours, interleaved with P2's runs
and E2.

Open, next: E4 (T-READ: reads at any time up to the last record). It needs
one more invariant: for every canonical object and every time t at which its
node was reachable, its slot for each live child at t is a memory slot to an
object readable at t (canonical, or the snapshot of a version good for t),
or a stream slot that names a version good for t (or, for an object that is
relevant now, a node of D, which the loader finds by id). INV-SLOT says
nothing about the objects of nodes that are neither current nor in D, nor
about a virtual root's dead slots. Lemma M and INV-2 (a node not in D is
clean) give it at each change of a slot. A probe (scratch, 02:47 to 02:57:
examples 3 and 5 with 8 seeds, example 2 with 4, the four schedules, 40
transactions each, with restarts) found it true after every operation.


### 2026-10-17 02:43 to 03:36. WP E4, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `afaa74a` (E3);
uncommitted before this WP's commit: its files, below. The design and the
probe ran while E3's checks did (02:43 to 02:57).

Did:

1. T-READ, stated in the trusted `lean/SIS/PhysTheorems.lean` as `TR_view`:
   in the runs of `TC_records` (BergDB's algorithm with marking, the
   assumptions, those of the physical layer and of stage 2, the Level 4
   startup from R(0), any cache schedule, no restart), after every
   transaction and its cache operations, a read through the Level 4 loader at
   any time t up to the last record reaches exactly the nodes reachable at t,
   each with its node at t. Since the schedule is any, this holds for every
   read of a schedule too.
2. The proofs, `lean/SIS/Proof/EvictHist.lean`, `EvictHistTrans.lean` and
   `EvictReadT.lean` (new, about 1,450 lines). INV-SLOT does not reach the
   earlier times: it says nothing about the objects of nodes that are neither
   current nor in D, nor about a virtual root's dead slots. A second
   invariant, `HInv`, does: every slot of a canonical object for a live child
   at a time t at which its node is reachable leads, through the loader, to
   an object or version good for t (or, by INV-SLOT's second half, names a
   node of D). Lemma M and INV-2 give it at each change of a slot; the cache
   operations and every transaction keep it (`HInv.evictTrans_ok`), and the
   read at t then goes as stage 1's. Outline in `level4-alignment.md`, 5.12
   (new).
3. Checked by running before the proof: the probe of the E3 entry (`HInv`
   after every operation, with restarts, examples 2, 3 and 5, the four
   schedules).
4. `lean/README.md`: the files, the statement, the axioms list, the history.
   `docs/level4-alignment.md`: 5.6 (T-READ proved), 5.11, 5.12 (new).

Files changed: `lean/SIS/PhysTheorems.lean`; `lean/SIS/Proof/EvictHist.lean`,
`EvictHistTrans.lean`, `EvictReadT.lean` (new); `lean/README.md`;
`docs/level4-alignment.md`; this file.

Checks (plan, 2.2), on a clean copy (bergdb's `lean/` at `afaa74a` with this
WP's 5 files), 03:18 to 03:33: `lake build` exit 0, no warnings (and each
new file elaborated alone, 03:19: no message); `lake exe sistest 20 40`: all
checks pass (03:25); `lake exe phystest 20 40`: all checks pass (03:33);
`#print axioms` of the theorem list with `TR_view`: standard axioms only; no
`sorry`, `admit`, `axiom` or `unsafe` in `SIS/` and `Check/`; `sh
test-traces/run.sh`: TRACE TESTS OK. No Java change, so no gate.

Register: none changed (M39, reads beside the writer, stays for J5: the
model's reads are sequential).

Time: E4 is M (2 to 8 hours): about 50 minutes.

Open, next: A-COPY on Java's tier (the next entry), then E5 (restarts with
eviction, T2-C): the invariants after a startup from any stream of a run,
where D is not empty and rule 4 links D's objects; then the run theorem with
restarts.


### 2026-10-17 03:27 to 03:59. A-COPY checked on Java (an addition after E3)

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `ddebd06` (E4);
uncommitted before this commit: its files, below. Not a WP of the plan: E3
needed a new assumption, A-COPY (the E2 entry), and stop rule 4 asks whether
Java meets it; A4 settled the same question for TREE and A6', so this does
for A-COPY what A4 did for them, before E5 builds on it.

Did:

1. The Java tier: `java/stress/A2A3Check2.java` counts, after every
   transaction, the pointers of its new entries (key klongs at tt, all key
   klongs of a node it created, a new top node's root and skip pointers) to
   nodes it did not create, and those that name neither a node of the
   writer's paths (the nodes current before it with a changed or replaced
   node below them) nor a child, live or dead, of one: a new summary line;
   `-DdebugA6=1` prints each failure.
2. The Lean tier: `copyFailures` in `lean/Check/Steps.lean`, the model's
   `CopyStep` (with the model's `pointees` and `live`; the paths computed
   lowest level first, checker-local), among the checker's diagnostics; a test
   trace, `lean/test-traces/copy.trace`, in which A-COPY (and TREE) fail.
3. Runs: the Java tier on the 21 configurations of level2-alignment.md, 10.5
   (68,901 transactions): 487,786 new pointers, 453,197 of them to a pointee
   of the paths that is not on them, 0 failures (TREE and A6' 0 too). The Lean
   tier on the small (60 traces) and medium (9) sets in `java/build/traces/`
   (10,129 transactions): no failure. The large set (12 traces) runs in the
   background; its result goes into a later entry.
4. `docs/level4-alignment.md`: section 4 (A-COPY), 5.9, 5.10, M43;
   `docs/evidence/level4-acopy.txt` (the counts); `lean/README.md`.

Files changed: `java/stress/A2A3Check2.java`; `lean/Check/Steps.lean`,
`lean/TraceCheck.lean`, `lean/test-traces/copy.trace` (new),
`lean/test-traces/run.sh`, `lean/README.md`; `docs/level4-alignment.md`,
`docs/evidence/level4-acopy.txt` (new); this file.

Checks: `java/build.sh` passes (03:33); the tool ran on the 21
configurations, small to large (java/stress only, so no gate is required).
Lean, on a clean copy (bergdb's `lean/` at `ddebd06` with this commit's
five files), 03:42 to 03:58: `lake build` exit 0, no warnings (the two
changed files elaborated alone: no message); `lake exe sistest 20 40` and
`lake exe phystest 20 40`: all checks pass; `#print axioms` of the theorem
list: standard axioms only; no `sorry`, `admit`, `axiom` or `unsafe`; `sh
test-traces/run.sh`: TRACE TESTS OK, with the new expectation on
`copy.trace`.

Register: M43 (A-COPY holds on every Java run checked).

Notes for Frans: with this, every assumption of stage 2 (TREE, A6', A-COPY)
holds on every Java transaction checked, and only A6 fails (A4). K1 still
needs your decision on A6' in place of A6.

Open, next: E5.


### 2026-10-17 03:44 to 05:09. WP E5, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `73320ec`
(A-COPY on Java); uncommitted before this WP's commit: its files, below. The
design and the first probe ran while the A-COPY checks did (03:44 to 03:59).

Did:

1. T2-C, stated in the trusted `lean/SIS/PhysTheorems.lean` as `T2_cache`:
   in the runs of `TC_records` (BergDB's algorithm with marking, the
   assumptions, those of the physical layer and of stage 2, the Level 4
   startup from R(0), any cache schedule), now with restarts after any
   transactions (`runEvict`: the logical startup and the Level 4 startup,
   both from the stream), after every transaction and its cache operations
   or its restart: the stream and D are the run's without restarts, so
   restarts change no record; P has the run's nodes; and the memory meets
   the invariants of `TC_records` (INV-CAN, INV-SNAP, no dangling slot,
   INV-SLOT) for the stream of the last startup, after some earlier
   transaction k1. Right after a restart they are the startup memory's: the
   plan's "the physical state after startup has INV-SLOT".
2. T-READ with restarts, `TR_view_restarts` (same file): in the same runs, a
   read through the Level 4 loader at any time up to the last record gives
   P at that time. Not in E5's statement, but T-READ's (plan, 1.4) is "for
   any reachable cache state", and `TR_view` (E4) covers the runs without
   restarts only; with this, every state a run with eviction reaches.
3. The proofs, `lean/SIS/Proof/EvictRerun.lean` and `EvictRestart.lean`
   (new, about 1,800 lines), and the lemmas of rule 4 in `EvictInit.lean`
   (`EInv.linkD`, which `einv_init` now uses too). The startup's rerun keeps
   `RInv` (every object canonical; every stream slot names, after Rule R of
   the section, its pointee's latest version; a slot for each pointee); the
   positions and rule 4 then give E3's invariant and E4's invariant for
   reads at earlier times (`einv_hinv_startup`); the physical writer depends
   on P only through its nodes (`evictTrans_congr`), so the transactions
   after a restart, from the logical startup's state, append the run's
   records; the run, by induction with the last restart (`evictInvR_all`).
   Outline in `level4-alignment.md`, 5.13 (new).
4. A change to the trusted part, under M44 (rule 4, "model and code"): rule
   4 (`Mem.linkD`) links the root's object's slots too, so the whole pinned
   set. The invariant needs a current canonical object's live slot to a node
   of D to be a memory slot to its canonical object; rule 4 gives it for
   D's objects, and a virtual root's object is never in D. The rerun leaves
   that slot a memory slot in every startup of the examples (probe 12,
   below), but a proof of that would follow the virtual root's slots
   through the rerun. Java does the same already: its virtual root's one
   slot, `TopDs.superRoot`, is a memory reference to the super root's
   canonical object. No record changes. `lean/README.md` lists it under
   "Changes to the trusted part". `lake exe phystest 20 40 evict` passed
   with the change (04:00 to 04:03), before the proof relied on it.
5. Checked by running before the proof. Probe 11 (03:46 to 03:48, scratch):
   after every transaction of 24 random runs of 40 transactions (examples 3
   and 5, 8 seeds each; example 2 with two of its algorithms, 4 seeds each),
   the startup from the stream, at every step of its rerun: every object
   canonical, every stream slot names its pointee's latest version after
   Rule R, every memory slot a canonical object of its pointee, and after
   the positions every canonical object is at its node's latest record. No
   failure. Rule R is needed for it: in each run of examples 3 and 5, 7 to
   39 references of section versions name an older version than the
   pointee's latest, before Rule R. Probe 12 (04:41): after the rerun and the
   positions, before rule 4, the root's live slots to nodes of D: 623 in the
   656 startups of examples 3 and 5, none a stream slot. T-READ with
   restarts: E2's runs check reads at three times after every transaction,
   with restarts, and E3's probe checked `HInv` after every operation with
   restarts.
6. `lean/README.md`: the files, the statements, the axioms list, the
   trusted change, the history; its "Not done" list lost the A-COPY check
   (done in the previous entry). `docs/level4-alignment.md`: the status
   line, 5.1 and 5.2 (rule 4), 5.6 (T2-C and T-READ with restarts proved),
   5.7 (item 4), 5.11, 5.13 (new), M20 and M44.

Files changed: `lean/SIS/Evict.lean` (trusted: rule 4),
`lean/SIS/PhysTheorems.lean` (trusted: two statements);
`lean/SIS/Proof/EvictInit.lean`; `lean/SIS/Proof/EvictRerun.lean`,
`EvictRestart.lean` (new); `lean/README.md`; `docs/level4-alignment.md`;
this file.

Checks (plan, 2.2), on a clean copy (bergdb's `lean/` at `73320ec` with this
WP's 5 files), 04:50 to 05:06: `lake build` exit 0, no warnings (the two new
files elaborated alone too, in scratch: no message); `lake exe sistest 20
40`: all checks pass (04:57); `lake exe phystest 20 40`: all checks pass
(05:06); `#print axioms` of the theorem list with `T2_cache` and
`TR_view_restarts`: standard axioms only; no `sorry`, `admit`, `axiom` or
`unsafe` in `SIS/` and `Check/`; `sh test-traces/run.sh`: TRACE TESTS OK.
The documents' links resolve. No Java change, so no gate.

Register: M44 (rule 4 extended to the root's object; proved with restarts,
`T2_cache`); M20 (its status: E4, E5).

Time: E5 is M (2 to 8 hours): about 1 hour 25 minutes.

Notes for Frans: E5 changed the trusted model once: rule 4 now links the
root's object as well as D's (M44, 5.13). It asks nothing of Java and
changes no record; please look at it at K1. With E5, T-CACHE, T-READ and
T2-C are proved for runs with eviction, any cache schedules and restarts;
of stage 2's theorems T-PIN (E6) remains.

Open, next: E6 (T-PIN, T-INDEX), whose design and first probe ran during
these checks (the next entry); the A-COPY Lean tier on the large set still
runs (current state).


### 2026-10-17 04:52 to 05:30. WP E6, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `e2e5bd5` (E5);
uncommitted before this WP's commit: its files, below. The design, the probe
and most of the proofs ran in a scratch copy while E5's checks did (04:52 to
05:06).

Did:

1. T-PIN, stated in the trusted `lean/SIS/PhysTheorems.lean` as `TP_pins`:
   in the runs of `T2_cache` (any cache schedules, restarts after any
   transactions), after any transaction and its cache operations or its
   restart, every object in memory outside the pinned set (`Mem.pinned`: the
   canonical objects of the nodes of D, and the root's object; Java also pins
   the record being written and the objects of an operation in progress,
   which the model treats as atomic) may be evicted. It has been written, so
   it may be detached; and there are slots, each a memory slot to it, such
   that unswizzling them and then releasing it leaves it out of memory. The
   theorems of stage 2 hold for every cache schedule, so they hold whatever
   objects outside the pinned set are evicted, in any order, at any
   transaction boundary: the plan's "and the theorems above still hold".
2. The proofs, `lean/SIS/Proof/EvictKeys.lean` and `EvictPin.lean` (new,
   about 870 lines). No object has two slots for the same pointee, in every
   memory of every run, whatever its assumptions (`SlotsND`,
   `slotsND_runEvict`, through every operation of the model, the startups
   included); so unswizzling every memory slot to an object leaves none
   (`Mem.unswizzles_incoming`), and it may then be released
   (`Mem.evict_ok`). With the invariant, an object outside the pinned set
   has a position (`EInv.detachable_of_unpinned`): a snapshot by INV-SNAP; a
   canonical one is of a written node not in D, clean by INV-2, at its
   latest version by INV-CAN.
3. T-INDEX, by the definitions: `level4-alignment.md`, 5.14, names what the
   physical writer reads, with the Lean definitions: a version from its
   node's canonical object (`Mem.writeNode`); each reference (`Mem.refOf`)
   from a pinned pointee's canonical object by node id, or from the slot (a
   memory slot's object's position, or a stream slot's record after Rule R,
   which reads `newest S0 s y` only, bounded by the startup section).
   `Stream.lv`, a map from every node, appears in the physical layer only in
   the last resort of the startup's `Mem.canonicalNode`, which the runs of
   the theorems never reach; the node table holds resident canonical objects
   only; and by T-CACHE and T2-C the records do not depend on what is
   resident or on what readers left in memory.
4. Checked by running before the proof, probe 13 (04:54, scratch): in the
   runs of examples 3 and 5 with the four cache schedules and restarts (4
   seeds of 40 transactions each, 1,280 states, 21,374 objects outside the
   pinned set seen), no object outside the pinned set without a position,
   every object that may be detached removed by `evictObj` (every memory
   slot to it unswizzled, then released), no object with two slots for the
   same pointee.
5. `lean/README.md`: the files, the statement, the axioms list, the history;
   its "Not done" list now has no stage 2 item. `docs/level4-alignment.md`:
   5.6 (T-PIN proved, T-INDEX stated), 5.14 (new), M20, M26.

Files changed: `lean/SIS/PhysTheorems.lean` (trusted: one statement);
`lean/SIS/Proof/EvictKeys.lean`, `EvictPin.lean` (new); `lean/README.md`;
`docs/level4-alignment.md`; this file.

Checks (plan, 2.2), on a clean copy (bergdb's `lean/` at `e2e5bd5` with this
WP's 3 files), 05:11 to 05:28: `lake build` exit 0, no warnings (the two new
files elaborated alone too, in scratch: no message); `lake exe sistest 20
40`: all checks pass (05:19); `lake exe phystest 20 40`: all checks pass
(05:28); `#print axioms` of the theorem list with `TP_pins`: standard axioms
only; no `sorry`, `admit`, `axiom` or `unsafe` in `SIS/` and `Check/`; `sh
test-traces/run.sh`: TRACE TESTS OK. The documents' links resolve. No Java
change, so no gate.

Register: M26 (T-INDEX: the model's node table holds resident objects
only); M20 (its status: E6).

Time: E6 is S to M (up to 8 hours): about 40 minutes.

Notes for Frans: with E6 every theorem of stage 2 is proved: T-CACHE, T-READ
(also with restarts), T2-C and T-PIN, for Option K under TREE, A6' and
A-COPY. E7 writes the Java change list and the K1 review guide.

Open, next: E7.


### 2026-10-17 05:12 to 05:31. WP E7, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `03f4eab` (E6);
uncommitted before this WP's commit: its files, below. Drafted while E6's
checks ran (05:12 to 05:28).

Did:

1. `docs/level4-alignment.md`, section 6, "What Java must do" (new): twelve
   changes, each with the model's definition it must match, the register
   rows, the WP and its check. Six before eviction (R8: `resolvePointers`,
   no runtime cut-back, the loader, rule 4 at startup, a slot's pair read
   once, reclaim's maintenance reads), which keep every record, checked byte
   for byte against `l34-base`; six for eviction (J1 to J7: the registry and
   the pins, unswizzle, release, the copies of slots (no change, a check),
   readers, accounting). What Java keeps, and what is not settled here.
   Lines at `e2e5bd5`. Also the status line and a pointer in 5.7.
2. The K1 review guide, 001-03,
   [03-k1-review.md](03-k1-review.md) (new), linked from the item's readme:
   what to decide (Option K under TREE, A6' and A-COPY instead of A6; the
   Java changes of section 6; E5's change to the trusted model; no format or
   API change), what is proved (the theorems, in plain English), what is
   assumed and how it was checked (the counts of both tiers), the changes,
   the Java work estimated (about 24 to 114 hours at the plan's sizes), how
   to reproduce the decisive checks, and the open risks.

Files changed: `docs/level4-alignment.md`;
`items/001-lean-model-levels-3-4/03-k1-review.md` (new),
`items/001-lean-model-levels-3-4/readme.md`; this file.

Checks (plan, 2.2, documents): the links resolve (a script, scratch); the
statements about code cite file, method and line at `e2e5bd5`. No code
changed.

Register: none changed; section 6 lists every Level 4 row with its WP.

Time: E7 is S (up to 2 hours): about 20 minutes.

Notes for Frans: stage 2 is done, and K1 is yours: please read
[03-k1-review.md](03-k1-review.md), section 1, and record your decision
under "Frans's go and decisions". The recommendation is to confirm Option K
with A6' and A-COPY, accept the list of section 6 and E5's change to rule 4.
A finding for you there (its section 7, risk 1): TREE, A6' and A-COPY are
counted by the Java tier and the checker, but no gate fails when one of
them fails.

Open, next: while K1 waits, R2 (trace format 2, the exporter for reclaim
runs) and P3 (bounds, measured); the A-COPY Lean tier on the large set still
runs (current state).


### 2026-10-17 05:31 to 06:05. WP R2, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `9eb146c` (E7);
uncommitted before this WP's commit: its files, below. K1 waits for Frans;
R2 does not depend on it.

Did:

1. Test-only hooks in `java/src/bergdb/core/Db.java`: `Db.TestHooks`, set
   in `Db.testHooks` (null by default, and then nothing changes): after every
   executed transaction, the internal ones (reclaim's steps and table stores)
   included, right after its record is appended (`transExecuted`, after
   `store()`); for every value node a transaction creates; for every index
   node a touch visits (`touchRange`, the super root included). And a test
   accessor, `Reclaim.lastCutRow()`, the newest row of the table marked cut.
2. `java/stress/TraceExport.java` with `retain=S` (reclaim on, the clock
   scaled as in `RestartInvariance`, the stream a `CutStream`, which refuses
   every read below the cut): every executed transaction is a record, with
   `kind=user`, `step` or `table` in its comment line; the new lines of
   format 2 (plan, 8.2): TOUCH (a step's touched index nodes), FA (fa(i),
   when it changes), CUT (a cut decided: c and the first available time) and
   PHYSCUT (the stream's first position moved). Run B also restarts right
   after each call that decided a cut, looks up from the first available
   time on, and compares the streams from the cut. The exporter's own checks:
   every touched node is an index node of P; every stored position is the
   start of a version; the physical cut is at or below the decided one
   (M35); Java's first available time is the table's. Without `retain`, the
   traces are as before: byte for byte the same on four traces of the small
   and medium sets (mixed-1, long-1, hot-1, m-mixed-1).
3. `java/stress/reclaimtraces.sh` (new): the plan's reclaim sets (8.4),
   small (five configurations of five seeds: node sizes 8 and 14, 30 to 200
   keys, 300 to 800 user transactions, a startup distance of 200 to 1,000
   bytes, retention 1 and 2 s, deletes 0 and 25 percent, long keys,
   transactions that change nothing; probes every ten transactions and right
   after each cut) and medium (three configurations of two seeds, 2,000 to
   5,000 user transactions); it fails on an exporter error, a failing probe
   or a trace without a cut.
4. Results (05:41 to 05:43): small, 25 traces, 3 to 28 cuts decided each, 2
   to 28 physical cuts, no exporter error, no failing probe (14 s); medium,
   6 traces, 18 to 46 cuts each, no error, no failing probe (73 s). The
   number of physical cuts varies from run to run (`cutIfDurable` waits for
   durability, which a background sync decides); the records do not, and
   run B's streams equal run A's from the cut in every trace. References of
   later records to versions before a decided cut are common (10 to 107,000
   per trace): Option K names the latest version of dead pointees too, and a
   cut stream keeps stubs for them (plan, 8.7). Today's checker refuses the
   new lines (`unknown line`); R3 extends it.
5. Not done here, and moved: the check that a step's touch covers every
   node whose key range meets the step's range (level3-alignment.md, 5,
   step 3) needs each node's key range, which neither the trace nor the
   model has; it is left to R6, on the Java side.
6. `docs/level2-alignment.md`, 9.2 (the lines); `docs/level3-alignment.md`,
   2.7 (done), section 5 (step 3 and the summary), M35 and M37.

Files changed: `java/src/bergdb/core/Db.java`, `Reclaim.java`;
`java/stress/TraceExport.java`, `java/stress/reclaimtraces.sh` (new);
`docs/level2-alignment.md`, `docs/level3-alignment.md`; this file.

Checks: `java/build.sh` passes; the gates on the work tree with this WP's
files, full, one after the other (05:44 to 06:04): `LEVEL 1 OK` (95 s),
`LEVEL 2 OK` (718 s; its step 7: a2a3-1 to 3 OK, conformance small 60 of 60
traces `TRACECHECK OK`), `LEVEL 3 OK` (341 s); unit tests 911 successful, F
tests 37 successful; StreamDigest against `l34-base`: DIGESTS IDENTICAL (36
of 36), so the hooks change no record. The two reclaim sets, as in 4. No
Lean change.

Register: M35 (the exporter checks it on every trace), M37 (the traces have
the table and the row as ordinary entries).

Time: R2 is M (2 to 8 hours): about 35 minutes.

Open, next: P3 (bounds, measured), which needs one more test hook (the nodes
a transaction replaces, to count the writes of nodes that are not current).
R3 to R8 wait for K1.


### 2026-10-17 06:05 to 06:35. WP P3, done

Agent: Claude, Opus 5.5, Max effort, Claude Code. bergdb at `ad1789d` (R2);
uncommitted before this WP's commit: its files, below.

Did:

1. One more test-only hook: `Db.TestHooks.nodeReplaced`, for every index
   node a transaction replaces (a split, a new super root; from the Dag's
   `keyNodeReplaced` and `topNodeReplaced`). Null hooks, the default, change
   nothing.
2. `java/stress/LoadTest.java`: D's bytes in memory (`Node.getMemSize`) in
   each sample and at most; the index nodes written that are no longer
   current, and of those the ones written again after a write since they
   were replaced.
3. Runs (06:08 to 06:12; LoadTest, 1M keys, 100-byte values, a FileStream,
   the default node size): 2M single-put transactions, uniform and hot (90
   percent on 1 percent of the keys), and 100,000 transactions of 40 puts,
   at the default startup distance of 50 MB; and the single-put workloads
   at 5 MB. All passed the full check.

   | Workload | sd | Section, max | D, max | D in memory | Index nodes per transaction | No longer current | Again since replaced |
   |---|---|---|---|---|---|---|---|
   | uniform, 1 put | 50 MB | 1.00 x sd | 90,048 | 72.0 MB | 0.68 | 273,857 of 1,366,968 (20.0 %) | 150,915 (11.0 %) |
   | hot, 1 put | 50 MB | 1.00 x sd | 72,026 | 48.7 MB | 0.28 | 258,007 of 560,614 (46.0 %) | 59,444 (10.6 %) |
   | uniform, 40 puts | 50 MB | 1.22 x sd | 119,167 | 95.3 MB | 22.93 | 525,091 of 2,292,519 (22.9 %) | 232,763 (10.2 %) |
   | uniform, 1 put | 5 MB | 1.67 x sd | 20,036 | 15.8 MB | 1.97 | 207,227 of 3,933,752 (5.3 %) | 180,343 (4.6 %) |
   | hot, 1 put | 5 MB | 1.22 x sd | 7,560 | 5.6 MB | 0.40 | 264,859 of 805,718 (32.9 %) | 72,474 (9.0 %) |

4. `docs/levels.md`: "Bounds, measured" (new), with the table and the
   findings: the startup section stays at the startup distance with single
   puts at 50 MB and goes past it with larger transactions and a small
   distance (up to 1.67 x); D in memory is 1.0 to 3.2 times the startup
   distance, so a reserve of twice the startup distance covers the runs at
   50 MB, not the uniform run at 5 MB (input for J7); about 10 percent of all
   index node
   writes are of dead nodes written again since they died, the cost of the
   conservative still-dirty test (sis-model.md, 11). Also the levels
   table's Level 4 row: its model is proved, the design waits for K1.

Files changed: `java/src/bergdb/core/Db.java`; `java/stress/LoadTest.java`,
`java/stress/TraceExport.java` (the hook's new method); `docs/levels.md`;
this file.

Checks: `java/build.sh` passes; the gates on the work tree with this WP's
files, full, one after the other (06:13 to 06:33): `LEVEL 1 OK` (94 s),
`LEVEL 2 OK` (707 s; step 7: a2a3-1 to 3 OK, conformance small 60 of 60
traces `TRACECHECK OK`), `LEVEL 3 OK` (341 s); unit tests 911 successful, F
tests 37 successful; StreamDigest against `l34-base`: DIGESTS IDENTICAL (36
of 36). The documents' links resolve.

Register: none (the findings are input for J7's reserve and for M40).

Time: P3 is S to M (up to 8 hours): about 30 minutes.

Open, next: every WP that does not wait for K1 is done (R1, R2, P1 to P3,
stages 0 and 1). The rest waits for Frans's K1 (current state).
