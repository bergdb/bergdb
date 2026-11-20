# 030-30. New trace seeds each day, and Java's commit-time check in week.sh

Created 2026-11-20 by Frans Lundberg. Status: done.

Two changes to the testing of Java against the model, decided by Frans
on 2026-11-20: `night.sh` checks traces on new seeds each day, with every
seed recorded so that a failure can be made again; and `week.sh` runs
Java's commit-time check of the writer's contract (CC; 030-09, section
3; 030-20) on a part of its steps, adding at most about 45 minutes to
the full run.


# 1. New trace seeds each day

## 1.1 Before

The sets of traces (`java/stress/conformance.sh`, `treeconf.sh`,
`contractconf.sh`, and the level scripts and `night.sh` steps that run
them) numbered their seeds 1 to N on every run, so each night checked
the same traces: a regression set, and nothing more. Kill-restart, fuzz,
unlinkfuzz and the harness soak already took new seeds each day, from
the day's number (days since 1970, `DAY` in `java/stress/runlib.sh`).

## 1.2 The change

- `conformance.sh`, `treeconf.sh` and `contractconf.sh` take a first
  seed after the seeds: `SET [seeds [first]]`. The seeds are first to
  first + seeds - 1; with a first other than 1 the traces go to
  `build/traces/SET-FIRST/` (`tree-SET-FIRST/`), so that the fixed seeds'
  traces, which later steps take, stay. `ONLY=NAME` runs one
  configuration of the set. The fixed seeds from 1 stay where the level
  scripts and `night.sh`'s steps 11 to 11c use them, as the regression
  set.
- A failing trace gets a line in the script's output:
  `FAILED NAME-SEED, set SET, seed SEED: why; trace ...; rerun from the
  repository's root: ONLY=NAME sh java/stress/conformance.sh SET 1 SEED`
  (`treeconf.sh` and `contractconf.sh` alike), and its path goes to the
  set's `failed.txt`.
- `night.sh` has two steps more, at its end, on the day's seeds (from
  the day's number times 1000): `conformance-day` and `contract-day`
  (section 1.3). Each prints every trace with its seed, and its last
  line, the report's line, gives the seeds. A failing trace is copied
  with its outputs to `build/night/RUN/traces/` (`keep_traces` in
  `runlib.sh`), which the run keeps when it deletes its clone; for
  `pecmp` the step writes the FAILED lines itself.
- `java/night.sh day` runs only these two steps, in a clone as the
  night run does; `DAY=N` in the environment runs day N's seeds again.

## 1.3 The sets and their seeds

Chosen so that `night.sh` grows by at most about 20 minutes (Frans's
limit), measured on F53 on 2026-11-20 at a load of 20 to 37 (other runs
beside it):

- `conformance-day`: `conformance.sh` on the small and drain sets, 10
  seeds a configuration; reclaim, 4; evict and medium, 3. 211 traces
  (70, 50, 28, 54 and 9); 548 s. Every set of the level scripts and
  `night.sh` is in it: the Lean trace checker's checks, the reclaim
  set's cuts and steps (C-CUT, C-STEP: 623 cuts, 810 steps) and the
  evict set's slots and handles (C-P, C-H).
- `contract-day`: `contractconf.sh` with `TREE=1` on the tree sets small
  and drain, 10 seeds a configuration, and reclaim, 3: the tree check,
  the contract checker and the bridge checker; then `pecmp` on the same
  traces. 195 traces (70, 110 and 15), 30,102 transactions; 253 s.
- Both steps: 13 minutes. The large set stays `week.sh`'s; the medium
  tree set's contract check (30 minutes for 27 traces in `night.sh`'s
  step 11b) runs on fixed seeds only.

The seeds are the day's number times 1000 plus 0 to 9; `fuzz.sh` and
`unlinkfuzz.sh` take seeds of the same form, but each tool feeds its
seed to its own generator, so the numbers do not need to differ.

## 1.4 The run, and a trace made again from its seed

`java/night.sh day` on the branch (its first commit, 2026-11-20 11:19):

    conformance-day    ok       548 s   CONFORMANCE DAY OK: 211 traces, seeds 20777000 to 20777009 (small:10 drain:10 reclaim:4 evict:3 medium:3)
    contract-day       ok       253 s   CONTRACT DAY OK: 195 traces, seeds 20777000 to 20777009 (small:10 drain:10 reclaim:3)
    NIGHT OK (13 minutes)

The step's log has a line a trace, such as `mixed-20777003: TRACECHECK
OK`, and a line a set with its seeds (`== conformance.sh reclaim 4
20777000: seeds 20777000 to 20777003`).

A failure, shown with a checker that fails the trace of seed 20777002
(a stand-in for `tracecheck`, through conformance.sh's `CHECK`):

    mixed-20777002: TRACECHECK FAILED (planted for the demonstration)
    FAILED mixed-20777002, set small, seed 20777002: TRACECHECK FAILED (planted for the demonstration);
      trace java/build/traces/small-20777000/mixed-20777002.trace; rerun from the repository's root:
      ONLY=mixed sh java/stress/conformance.sh small 1 20777002
    CONFORMANCE FAILED

`keep_traces small-20777000` copied the trace with its outputs
(`mixed-20777002.trace`, `.export.txt`, `.check.txt`, the times) and the
set's `configs.txt`. The rerun command, with the real checker, made the
trace again, byte for byte the same as the kept one (394,046 bytes), and
passed it. The contract step's FAILED lines, from the checkers' lines
that check.sh counts as failures, were shown the same way on a planted
line: `TREE=1 ONLY=a6 sh java/stress/contractconf.sh small 1 20777004`;
such a one-trace rerun takes 17 s.

Is every trace made again from its seed? Each set run twice on the
seeds 20777100 and 20777101 (the conformance sets small, drain, reclaim,
evict and medium, and the tree sets small, drain and reclaim, 126
traces): 88 traces byte for byte the same; in the 38 others only lines
that a thread of Java's own times write differ:

- the reclaim traces (r-small to r-drain, conformance and tree sets): the
  place of a PHYSCUT line, the move of the stream's first position,
  which a thread of its own makes when it can. Everything else is the
  same: the transactions, the records, the nodes, the steps, the cuts,
  the probes. r-maint, where maintain() makes the moves, repeats byte
  for byte.
- the evict set's configurations with reclaim (e-r-*) or with the
  capacity controller (e-budget, e-r-budget, e-b-restart): besides
  PHYSCUT, run E's lines of what is in memory (SLOT, HMEM and the
  handle lines): the controller's evictor is a thread of its own, whose
  batches are bounded in time, and the cut frees memory.

So a failure of the writer, the reads, the steps or the cuts repeats
from its seed; a failure that depends on the moment of a physical cut or
of an eviction (C-P and C-H in those configurations) may need a few
reruns, or the kept trace, which is why the step keeps it.


# 2. CC in week.sh

## 2.1 How CC is switched on

`TransCheck` (030-09, section 3) is on with the system property
`transcheck=1`: in the unit tests (`before-commit.sh`) and in the unit
tests and f-tests of `java/stress/transcheck.sh` (`night.sh`). A failure
throws an `AssertionError`, which fails the database (`Db.fail`). Each
JVM prints a summary line at its exit, `TRANSCHECK: N transactions, ...`.

`week.sh`'s steps start JVMs that start JVMs: the apps' Kill, KillEmpty
and Buffers, and `KillRestartHarness`, whose children do the writes,
with command lines of their own. A property does not reach them. Tried
first: `JDK_JAVA_OPTIONS=-Dtranscheck=1`, which reaches every JVM, but
the launcher prints `NOTE: Picked up JDK_JAVA_OPTIONS` on each JVM's
stderr, and Buffers' kill round failed on it ("the child printed: ...");
`JAVA_TOOL_OPTIONS` prints such a line too, and `build.sh`'s jdeps check
failed on it. The summary line on stdout would break such checks as
well.

So since 030-30 `TransCheck` is on also with the environment variable
`BERGDB_TRANSCHECK` set to a file, which every JVM a step starts sees,
its children too, with no change to their command lines or output: the
summary line is appended to the file instead of printed, and the first
failure is appended at once (`TRANSCHECK FAILURE: ...`), so that a JVM
killed after it still leaves it. A JVM killed with SIGKILL leaves no
summary. `week.sh`'s `with_cc NAME COMMAND` runs a step's command with
the variable set to `build/cc/NAME.txt`, in a subshell, so that no later
step sees it; then a failure line, or a summary with a failure, fails
the step with `CC FAILED:` and the check's message, whatever the
command returned, and a step whose JVMs wrote no summary fails too (the
check was not on). Else the step's line in the report ends with the
commits checked, such as `APPS OK; CC: 4042166 commits checked in 70
JVMs that ended normally, no failure`. Java's change: `TransCheck.java`
(the variable, the file) and a comment in `Db.java`; the property works
as before.

## 2.2 The cost, measured

On F53, 2026-11-20, each step run twice side by side in two clones, one
with CC and one without, at a load of 12 to 85 (this item's other runs
and other sessions beside them):

- `apps.sh quick`: 214 s with CC (to its last app, whose failure was
  the NOTE line above) and 230 s without; 340,348 commits checked in 14
  JVMs; in `week.sh short`, 341,005 commits in 27 JVMs.
- `apps.sh soak 20777`: 3,116 s with CC, 2,942 s without: 174 s more
  (6 percent); 4,042,166 commits checked in 70 JVMs.
- `apps.sh kill 20777`: 1,960 s with CC, 2,111 s without (Kill, KillEmpty
  and Buffers' kill: their kills follow a schedule too); 31,720 commits
  counted in the 174 JVMs that ended normally, and more in the killed
  children, which the count leaves out (Buffers' kill alone saw 62,054
  committed transactions).
- `kill-restart.sh 100 207771`: 135 s with CC, 151 s without. The kills
  follow the harness's schedule of phases and delays, so CC costs no
  time there; the children commit less in that time (31,222 transactions
  found after the restarts with CC, 52,396 without).
- `harness-soak.sh -r 2`: 143 s with CC, 138 s without; 31,038 commits
  checked.

030-20 measured 3.5 to 6 times an in-memory commit. These steps are
not bound by the writer: the Pub layer, the syncs, the apps' oracles and
the harnesses' own checks take most of the time, and the kills follow a
schedule.

## 2.3 What runs with CC

Frans's limit: at most about 45 minutes more for the full `week.sh`. The
measured cost allows CC on most of the steps; it runs on a part, so that
each harness runs both with and without it (the users' configuration,
with the timing that CC changes):

- `apps-soak-cc` and `apps-kill-cc`: the apps' soak and kill rounds of
  the day. `apps-quick` stays without CC.
- `kill-restart-cc`: the third of the three seeds of 1,000 kills
  (`kill-restart-week` runs the first two without).
- `harness-soak-cc`: rounds 7 to 9 of the harness soak's ten
  (`harness-soak.sh -f 7 -r 3`, the same rounds, seeds and sizes as
  before; `-f`, the first round, is new); `harness-soak-week` runs
  rounds 0 to 6.
- Not with CC: fuzz and unlinkfuzz (no database's commits, or the Dag
  alone), `conformance-large` (TraceExport, whose traces the Lean
  checkers check), Android.

The time it adds to the full run, estimated from section 2.2: the apps'
soak about 3 minutes (6 percent of its 34 to 52 minutes), the kill
rounds and the kill-restart seed none (their time is their schedule),
the three harness-soak rounds under a minute (of about 6): about 4
minutes, well inside the limit.

The commits it checks, estimated from section 2.2: about 4 million in
the apps' soak, more than 31,720 in the apps' kill round, about 300,000 in
the kill-restart seed (its children commit about 310 a kill with CC; the
killed children's are checked but not counted), and about 15,000 a round
in the harness soak: about 4.4 million commits a week run, each
checked against the writer's contract.

`week.sh short` runs `apps-quick-cc` (the apps in small, with CC),
`kill-restart-cc` (10 kills on the second seed) and `harness-soak-cc`
(round 1), so that the trial of the script takes the path of CC.

## 2.4 A CC failure fails the step

Shown with a fault planted in a scratch copy of `TransCheck` (a JVM's
N-th checked commit throws the check's `AssertionError`; not committed),
through `with_cc`:

- `harness-soak.sh -r 1`, the fault at commit 300: `HARNESS SOAK FAILED
  ...`, then `CC FAILED: Java's commit-time check of the writer's
  contract failed in 4 JVMs; the first: transcheck: a fault planted for
  the demonstration, transaction 300 (log: java/build/cc/hs.txt)`;
  status 1.
- `kill_seeds 20 207772` (`kill-restart.sh`), the fault at commit 200:
  `KILL RESTART FAILED: late exit ...`, then `CC FAILED: ... failed in 5
  JVMs; the first: transcheck: a fault planted for the demonstration,
  transaction 200`; status 1. The failures were in the children, which
  the harness starts.
- The same without the fault: `KILL RESTART OK: 20 kills and 1 exits in
  21 s, seed 207772; CC: 2909 commits checked in 5 JVMs that ended
  normally, no failure`; status 0, and the variable not set after it.


# 3. Found on the way, not changed here

- **KillEmpty does not handle an interrupted creation.** In the first
  `week.sh short` (2026-11-20 11:58, at a load near 85), `apps-quick-cc`
  failed: KillEmpty's final check of database 3 started a database whose
  creating start a kill had cut (`DatabaseNotCreatedException`, bergdb
  028-18). Kill (a4) removes the files and starts again in that case;
  KillEmpty (b5) does not. CC found nothing (341,005 commits, no
  failure). A fix for the apps' owner (030-31 works on the apps).
- **IndexJobsHarness's testRetriedFaultThenDeletedDuringBuild** failed
  once in `before-commit.sh` in the second `week.sh short` (12:23, at a
  load near 40): "creation 1 returned; memory has index "j" ..., building";
  the kind of load-dependent finding that 028-23, item 14, fixed for
  "memory has no definition". It passed in the other four runs of the
  unit tests that day.
- **contractconf.sh runs the bridge checker twice:**
  `lean/contract/check.sh` runs both checkers since 030-15, and
  `contractconf.sh` then runs `bridge-check.sh` again. In `night.sh`'s
  step 11b the bridge is most of its 30 minutes; one of the two runs
  could go.


# 4. Gates

On the branch `030-30-seeds-and-cc`: `before-commit.sh` BEFORE COMMIT OK;
`level2.sh` LEVEL 2 OK; `DRY=1 night.sh` and `DRY=1 week.sh` show the new
steps; `night.sh day` NIGHT OK (section 1.4); `week.sh short` WEEK OK (16 minutes, 2026-11-20 12:36; its CC steps:
`apps-quick-cc` 319,409 commits checked, `kill-restart-cc` 3,194,
`harness-soak-cc` 23,002, no failure), after two runs that failed on
the findings of section 3.


# Log

2026-11-20. Created and done, on the branch `030-30-seeds-and-cc`.
