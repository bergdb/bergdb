028-23. Change: the test scripts sorted by kind, functional and timing
=====================================================================

Status: done. Kind: Change. Frans: decided (10:39).
Created 2026-11-19 by Frans Lundberg.

What: sort the test scripts by kind. Functional testing in
`java/before-commit.sh` (fast, about 2 minutes), `java/night.sh` (about
once a day while there is development) and a new `java/week.sh` (on
demand, near every release); timing in a new `java/timing.sh`, the only
script that needs a quiet machine. Every step classified, the
load-sensitive ones made robust, the user apps of 024-26 and 026-13 moved
into `java/` as maintained tests, and the release rule written down.

Why: Frans, 2026-11-19:

* 10:25: "We have the fastest before-commit.sh. That should be really
  fast, 2 minutes or less. [...] Then night.sh designed to run once per
  24h or so. When there is ongoing development work. Do we need week.sh or
  something? Testing run less often and on demand. The name is only a
  name, it is not necessarily scheduled. It would always run before a
  release. Near a release, at least. Not necessarily on the exact version
  that ships in the release. Minor change after can be acceptable."
* 10:34: "Sometimes it is useful to separate timing-sensitive testing
  from other testing. It would be good to know whether testing can be run
  while working on the machine or if is must have a quite machine."
* 10:39: "Yes, I want this separation. [...] Functional testing in
  before-commit.sh, night.sh, week.sh. Timing in timing.sh, only this
  script requires a quite machine. Good structure."

Frans: decided (10:39); nothing more needed.

Done when: every step has its kind in its script's header and in the
table below, and each script prints its kind at its start; the
load-sensitive steps are robust; the functional scripts hold no timing;
week.sh and timing.sh exist and were tried in a short form; the apps run
from `java/stress/apps.sh`; AGENTS.md, java/readme.txt, 013-02 and 026's
"How the release is made" state the rule; before-commit.sh prints BEFORE
COMMIT OK.

First step: read the scripts and the tests for time limits.


1. The kinds
------------

* **Functional**: the result does not depend on the machine's speed or
  load. Time limits inside are hang guards, far above the normal time.
  May run while someone works on the machine; night.sh and week.sh also at
  a low priority (`nice -n 10`; `taskpolicy -b` on macOS, which throttles
  CPU and disk hard and makes a run several times longer).
* **Load-sensitive**: functional, with a time limit inside that load can
  pass (a timeout near the normal time, "within N ms", a sleep that
  expects a state). None is left after section 3's changes: each became
  functional.
* **Timing**: the number is the result. Only on a quiet machine; never
  decides a pass in a functional script (a figure may be printed there as
  information, as level1.sh's CORE).


2. Every step and its kind
--------------------------

The steps of the four scripts, in their order. "Hang guards" lists the
time limits that only a hang reaches; "was" marks a step that held a
load-sensitive or timing check before this entry (section 3).

**before-commit.sh** (about 2 minutes; may run while someone works):

* build.sh, deps.py, doubles.py: functional.
* The unit tests (`bergdb.dev.Unit`, TransCheck on): functional; was
  load-sensitive (section 3, items 1 to 8 and 14).
* The f-tests (`bergdb.dev.F`): functional; was load-sensitive (item 8).
* The demos: functional; 60 s each, a hang guard (about 3 s in all).

**night.sh** (about 2.5 hours; may run while someone works, at a low
priority too):

* before-commit: as above.
* core-build (`stress/core-build.sh unit f`): functional.
* transcheck: functional (the unit and f-tests, as above).
* level1: functional. DagFuzz, DeleteRepro, RestartStress,
  RestartInvariance; Props MEM, SEG, MEM10M and SS are counts of bytes
  (checked against limits); CORE is printed, not checked: information
  only, measured by timing.sh.
* level2: functional (RestartStress, RestartInvariance, CrashTest,
  BryanRepro, treeconf, the contract and the bridge, conformance,
  TakeCheck). BryanRepro's 10 s retention uses the real clock but checks
  only the latest state.
* level3: functional; was load-sensitive (InterruptStress, item 10).
  Reclaim's retention in every stress program is a test clock, so no
  check depends on real time passing.
* level4: functional. LargerThanMemory's live heap below three quarters
  of the cap depends on eviction keeping up with the writer: not known to
  be load-sensitive (section 4).
* count-gates: functional; was load-sensitive (item 11).
* lean-tests, tree-tests: functional (Lean programs).
* night-tests (`bergdb.dev.Night`): functional; was load-sensitive
  (StorageFaultTester, item 9; IndexJobsHarness, item 14).
* harness-soak -r 2: functional; `-t` (1,800 s a job) and the harnesses'
  join and cleanup bounds (10 to 30 s, scaled by `harness.slow`) are hang
  guards.
* fuzz 12: functional; was timing (item 12). The 12 minutes are a budget.
* unlinkfuzz: functional.
* kill-restart 1000: functional; the harness's waits (a phase 300 s, an
  exit 60 s, a job 120 s) are hang guards, LIMIT_S a budget; the late
  exit is 028-20's.
* conformance-medium, contract-medium: functional.
* (night.sh large) conformance-large: functional.

**week.sh** (about 11 hours; may run while someone works, at a low
priority too): night.sh's steps above, then:

* apps-quick, apps-soak N, apps-kill N (`stress/apps.sh`): functional;
  was load-sensitive (item 13).
* kill-restart-week (1,000 kills on each of three more seeds):
  functional, as kill-restart.
* fuzz-week (60 minutes, other seeds): functional, as fuzz.
* unlinkfuzz-week (a second block of the day's seeds): functional.
* harness-soak-week (-r 10, other seeds): functional.
* conformance-large: functional.

**timing.sh** (about 2 hours, an estimate; needs a quiet machine):

* core: timing (CORE of the candidate and the last release, ABBA).
* pauses: timing (the pause probe with ZGC, ABBA; the guide 50 ms on
  F53, 100 on s1).
* perf: timing (`performance.sh ab`, the release suite, 1M and 10M keys).

**Other scripts**: functional: unit.sh, f.sh, stress/apps.sh,
stress/android.sh, stress/conformance.sh, stress/contractconf.sh,
stress/flush-order.sh, stress/reclaimgrid.sh (WE and SE are counts of
bytes), stress/reclaimtraces.sh, stress/treeconf.sh and the night
steps' scripts above. Timing: perf.sh, props.sh (for CORE; MEM and SS do
not depend on speed), stress/performance.sh, stress/objectbench.sh,
stress/soak.sh.

Counts: before-commit.sh 6 steps, night.sh 17 (18 with large), week.sh 9
of its own besides night's 17, all functional: 32; timing.sh 3 steps,
all timing. Before this entry 13 checks inside the functional steps were
load-sensitive or timing (section 3) and 3 more in the apps; none known
now.


3. The load-sensitive checks made robust
----------------------------------------

Found by reading the tests (the unit, f and night groups, the stress
programs, the harnesses, the scripts' own limits). Each keeps its real
check:

1. `BufferedStream.test1` (unit): the buffer must be empty right after an
   append, before its 1 s timer. Now checked unless the test thread was
   stalled for 900 ms of the 1 s (the timer may have written by then).
2. `StorageManagerTester.testSyncWokenByAFailure` (unit): the sync must
   throw within 250 ms of the stream's failure (a wake, not the next
   check 500 ms later). Now three tries: a sync that is not woken is late
   every time, a stalled thread now and then.
3. `StorageManagerTester.testWait1` (unit): `sync(0)` within 0.4 s. Three
   tries, as 2.
4. `StoredTrans.testFindNode` (unit): 200,000 lookups within 2 s, a guard
   against a linear search (minutes). Now 20 s.
5. `DbTesterStream.testSyncAfterOneCommitWaitsForOneForce` (unit): the
   force count is the check; its upper bound of 5 s is now 60 s, a hang
   guard (the lower bound, at least the force's 50 ms, stays).
6. `PubTesterIndexJobs.testJoinFromAnotherThread` (unit): `join(5000)` on
   the other thread, then its result (a NullPointerException if it had not
   ended). Now `join(60000)` and an assertion that it ended.
7. `DbTesterFailure.within` (unit and f, nine calls, 5 to 10 s) and
   `waitForStorageError` (10 s): hang guards, now at least 30 s.
8. `DbTester.testStopWithRunningTransaction` (f): `stop()` "at once",
   within 1 s; now 10 s (a stop that waited for the writer would wait
   until the join of 30 s after it gives up).
9. `StorageFaultTester`'s runner (night tests, about 3,900 runs): a run
   not done in 10 s was a finding "hangs"; now 60 s.
10. `InterruptStress` (level3): each worker must end within 10 s of the
    stop; now 60 s.
11. `CountGates` (count-gates, G4 and G5): the heap was measured 3 s after
    the last write, expecting the write buffer's shrink (after 2 s idle);
    on a loaded machine the shrink can come later, and its up to 10 MB
    would fail the gate. Now it waits, up to 60 s more, until the buffer
    is back at its first capacity.
12. `FormatFuzzer.measure` (unit's testFuzz* and fuzz.sh, on one core):
    the full check within 20 ms + 200 ns a byte, the least of three, a
    timing check that a collector's pause could fail. Now the least of up
    to ten, and a failure only at five times the bound, where a check that
    is not linear in the length lands; between the two the check is
    counted (`slow`, printed with the turn's counts).
13. The apps (moved by this entry): Buffers' heap 3.5 s after its writes
    within 500 kB a database of a reopened one is now a NOTE, the check
    the heap 10 s after; Kill's and KillEmpty's child exit within 120 s
    now 600 s; Buffers' child start within 60 s now 300 s.

14. `IndexJobsHarness`'s creation (unit's testRetriedFaultThenDeletedDuringBuild,
    the night tests, harness-soak): found by this entry's gate, failed once
    in before-commit.sh at a load near 100 % ("creation 1 returned, and
    memory has no definition"). With a deletion during build 1, the build's
    thread can reach its third step, and the deletion, before start() has
    returned to the run's thread, which then found no definition. Now no
    finding when the deletion has begun (a flag set before its call); the
    deletion's own call checks the rest.

Left as they are, with headroom of about 1,000 times or only in the safe
direction: the 10 s hang guards of NodeStreamTester, FileStream,
NodeCollection, PubTester (testCloseReportsBackgroundWriteFailure),
PubTesterIndexJobs' cleanup and DeleteIndexTester; the 30 to 60 s guards
elsewhere; the sleeps that expect a thread still blocked (load only
makes them pass more easily); Eviction's CPU below half the wall time.


4. Not changed, for a look
--------------------------

* `KillRestartHarness.verify()` reads at the earlier runs' times (`ts`,
  `tsj`) with the real clock and a retention of 20 s in two of five
  databases, without catching LookupTimeNotAvailableException: a slow
  verify and a cut could fail it, in principle (rare with a startup
  distance of 5 MB or more). Not verified; the file is 028-20's today.
* `IndexJobsHarness` (night tests, harness-soak): after a RUNTIME fault in
  a cleanup, markers still there after 50 ms count as "stuck"; a slow
  cleanup that removes them later could give a false finding. A possible
  race, not verified.
* LargerThanMemory (level4): the live heap after a full GC below three
  quarters of the cap depends on eviction keeping up; not known to fail
  under load.
* No step of night.sh has a time limit of its own: a hang stalls the
  run (as before).


5. week.sh and timing.sh
------------------------

`java/week.sh` is night.sh's run with its own steps (`night.sh week`): a
clone of HEAD in `build/week/RUN/`, the report `report.txt` ending WEEK OK
or WEEK FAILED, a `tools/news.sh` entry. Its steps and estimated times on
F53: night's steps (about 2.5 hours), apps quick, soak and kill (about 6,
40 and 30 minutes), kill-restart 3,000 more kills (about 80 minutes), fuzz
60 minutes, unlinkfuzz another block (5 minutes), harness-soak 10 rounds
(about 20 minutes), conformance large (about 5 hours): about 11 hours in
all. `week.sh short` is a trial of the script (its own steps small,
night's left out).

`java/timing.sh` builds the candidate (this tree) and the reference (the
last release's tag, cloned and built once in
`build/timing/ref.noindex/TAG/`), checks the CPU (at least 90 % idle; it
refuses, or waits with WAIT=MINUTES, and checks again before each run),
and runs core (CORE, ABBA, an alert above 1.10 times the reference's),
pauses (the pause probe with ZGC, ABBA, an alert above the guide) and perf
(`performance.sh ab` with the new release suite,
`stress/performance-release.suite`: 1M keys as the principal suite, 10M
keys as 026-25, section 7). Its report ends TIMING OK, TIMING ALERTS,
TIMING FAILED or TIMING REFUSED. On s1: `timing.sh prepare` here, the
builds copied, `CAND=DIR REF=DIR PAUSE_GUIDE_MS=100 sh timing.sh core
pauses` there (its header). Times are estimates; the first run on a
quiet machine gives them.


6. The user apps
----------------

024-26's apps (a1 to a7) and 026-13's (b1 to c2) are in
`java/stress/apps/`, run by `java/stress/apps.sh` (quick, soak N, kill N)
against the clone's own `build/bergdb-release.jar`. Adapted for 2026.6:
the node sizes 8, 14 and 62 through `bergdb.core.TestNodeSize`, which the
release jar has; 024-26's `Limits` probe checks the decided behaviour of
024-27 (a refused call spoils the builder: later calls and execute()
throw, nothing written); 026-13's KeyLimits imports `bergdb.pub.Limits`
by name (024-26's class `Limits` shadowed it); Upgrade builds 2026.4's
jar from the tag `release-2026.4` once, or skips with a note;
OldNodeSize runs only if `build/apps/old-dbs/b2-node62` exists (not in
the repository). The items keep their reports and logs and point to the
new place; their copies of the sources were removed (Git has them).


Log
---

2026-11-19. Registered (Frans, 10:25, 10:34, 10:39) and taken by an agent
of coord-1118: in progress; branch `028-23-test-kinds` in a scratch clone.

2026-11-19. Done on the branch `028-23-test-kinds`, main merged in, by an
agent of coord-1118. Gates, all on F53 at a load of 30 to 96 (other
sessions' gates and night.sh): BEFORE COMMIT OK (166 s; the first run
failed once in IndexJobsHarness, the race of section 3, item 14, fixed;
the class then 6 times in parallel, all OK); COUNT GATES OK (554 s);
InterruptStress 10 s OK; the night tests' StorageFaultTester OK (279 s);
`stress/apps.sh quick` APPS OK (6 minutes; soak and kill lines tried with
smaller arguments); `week.sh short` (30 minutes): apps-quick, kill-restart-week (2 seeds
of 10 kills), fuzz-week, unlinkfuzz-week (1,122 s at that load) and
harness-soak-week ok, conformance-small failed for want of the Lean
checker (night's level steps build it; short mode skips them), so the
short step now builds it first, and that step alone then gave
CONFORMANCE OK (170 s); `timing.sh core`
refused at 8 % idle (TIMING REFUSED, exit 2); `FORCE=1 ROUNDS=1
PAUSE_SECONDS=5 timing.sh core pauses`, a trial and not a measurement (the
CPU 0 to 1 % idle): the reference release-2026.5 cloned and built, CORE
and the pause probe ran on both builds, TIMING ALERTS as expected under
that load; performance.sh's harness compiles against 2026.5's jar; `sh -n`
on every changed script. Not run: a full week.sh (the coordinator starts
the first tonight) and timing.sh on a quiet machine (its times in the
headers are estimates until then).


2026-11-19. Main merged again (028-20, kill-restart.sh's late-exit
self-test): BEFORE COMMIT OK (150 s) and `kill-restart.sh 10` KILL RESTART
OK on the merge, `c2376f74`, by an agent of coord-1118.

2026-11-19. Since 028-27 (Frans's decision of 2026-11-19), week.sh no
longer includes night.sh's steps: night.sh, week.sh and timing.sh are
disjoint sets of tests, each of the first two runs before-commit.sh first,
night.sh has no `large` and `week` modes (conformance-large is week.sh's),
and week.sh runs the Android tests (`stress/android.sh`, with the SDK in
its environment). Sections 2 and 5 above describe week.sh as it was made
here; 028-27, sections 2 and 3, have the steps since then.
