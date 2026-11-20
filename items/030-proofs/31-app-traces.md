# 030-31. The apps' workloads and reclaim across restarts, against the model

Created 2026-11-20 by Frans Lundberg. Status: done.

Two changes to the testing of Java against the Lean model, decided by
Frans on 2026-11-20. Until this item every trace came from TraceExport's
synthetic generators, and reclaim's steps were checked (C-STEP, 030-27)
only in runs without restarts. (1) The user applications' workloads
(java/stress/apps/, 028-23) are traced and checked by the model's
checkers. (2) Reclaim's steps are checked across restarts and crashes of
the traced run: an iteration that spans a restart goes on from the row
its last step committed (030-25). Done by an agent, on the branch
`030-31-app-traces` from 6d379122.


# Result

- **The apps' workloads** (section 1): `java/stress/AppRecord.java`
  records the Core transactions that an app's run commits, and
  TraceExport replays them (`workload=F`); `java/stress/apptraces.sh`
  runs it, a step of `night.sh` (nine apps, small) and of `week.sh` (the
  same apps larger, at node sizes 8 to 62, and WorstCase, with seeds of
  the day). Each trace is checked by `tracecheck` (with reclaim, C-CUT
  and C-STEP; with the app's restarts, STEP-resume), and, replayed
  without the restarts, by `contractcheck` and `bridgecheck`.
  - night (the run of 2026-11-20, 12:45): 11 traces of 9 app runs,
    1,725 user transactions with 30,723 operations, 8 restarts
    replayed; `tracecheck` 11 of 11 OK on 1,768 transactions; the
    contract checker and the bridge checker 0 failures on 1,757
    transactions; 2.5 minutes on F53 under load, APPTRACES OK.
  - week (the run of 2026-11-20, 11:58 to 12:39): 19 traces of 14
    app runs, 4,299 user transactions with 107,902 operations, 35
    restarts replayed; `tracecheck` 19 of 19 OK on 4,411 transactions
    (C-STEP: 18 steps, 0 failures); the contract checker and the bridge
    checker 0 failures on 4,392 transactions; the app's time at every
    transaction, the app's record's bytes at 4,204 of 4,299; 41 minutes
    on F53 under a heavy load (two level scripts and another agent's runs
    beside it; 2,911 s of CPU), APPTRACES OK.
- **Reclaim across restarts and crashes** (section 2): run A restarts
  (`restart=K`) and crashes right after a step's record is durable
  (`crash=K`); the trace has RESTART and RESUME lines (027-02, section
  4); C-STEP's new check STEP-resume checks the row each restart resumed
  and the first step after it. `conformance.sh crash`, in `level3.sh`
  step 8 (3 seeds; 1 quick): 15 traces, 6,837 transactions, 943 restarts
  (167 crashes), 844 with an iteration in progress, 194 iterations with a
  step before a restart and the next after it, 503 STEP lines, 256 cuts;
  0 failures. The fault test
  (`step-faults.sh`) has four more faults, each found by STEP-resume.
- **No finding about Java.** Every trace passed every checker; every step
  across a restart went on from the row its last step committed.


# 1. The apps' workloads

## 1.1 Recorded and replayed, not traced in place

TraceExport's recorder reads run A's database in memory after every
record: the new nodes, their entries, the klongs, D, Java's reads. It
needs a memory stream, no eviction (every node an object reached through
memory pointers) and one thread. An app's run has file streams, a cache
budget, threads, restarts, several databases. So the app's run is
recorded at the Core and replayed through TraceExport, which traces the
replay as it traces a generated workload.

What makes the replay faithful: the writer gets a transaction's
operations (the keys and values after the key and value
transformations, deletes as deletes) at a time; PE is a function of them
and the node size (030-04, 3.5, the writer's repeatability). AppRecord
records exactly that, through Db's test hooks: for each committed user
transaction, `kvApplied` gives the operations in the order the Dag gets
them, `transExecuted` the time and the record. The replay executes the
same operations at the same times, at the app's node size, startup
distance and reclaim settings, and restarts where the app restarted.
What it leaves out does not change the records: eviction, restarts and
the file stream give the same stream byte for byte (TraceExport's runs B
and E, RestartInvariance, EvictionInvariance); the threads only decide
the order of the commits, which is recorded. Not replayed: the app's
reads (the replay makes its own GET and SCAN lines) and a call of
`Db.maintain()` that wrote nothing (one that wrote records is replayed,
see below).

The replay checks itself against the app: each user transaction's time
must be the app's, and its record's bytes are compared with the app's
record when it is at the same position. They differ where the replay's
internal records differ (reclaim's steps at another transaction, a
maintain() call of another size, the app's restart that wrote a take), so
this is a count, not a pass condition. In the night run the time was the
app's at all 1,725 transactions and the record's bytes at 1,689; in the
week run 4,299 and 4,204 of 4,299. So most replayed records are the
app's records byte for byte.

## 1.2 AppRecord

`java -cp bergdb.jar:stress:APP_CLASSES bergdb.core.AppRecord PREFIX
AppClass args...` runs the app's `main` in the same JVM with the hooks
set, and writes one file per database, PREFIX-K.rec. A database is known
by its file stream's directory (a start gives a new Db and a new
database ID; the directory stays), so its restarts are in its file where
they came. The file has, in commit order: `TX tt tpos hash k` and the k
operations of each user transaction; `SET sd retain fraction` before a
transaction when the startup distance or reclaim's settings changed;
`RESTART` when a new Db of the database committed; `MAINTAIN n tt` when
the app's `maintain()` calls wrote n records (known by `Reclaim.maintain`
on the stack); `NODESIZE`. Not recorded as transactions: reclaim's
internal transactions and the settings' records (KVs at the Core's own
keys, `Trans.coreKey`), which the replay makes itself.

TraceExport's `workload=F` (and `apptx=N`, the first N user
transactions; `apprestarts=0`, without the restarts) sets n, the node
size, the startup distance and reclaim from the file, executes each
transaction with `putLongKey` and `deleteLongKey` (the Pub layer's keys
may be longer than 111 bytes), calls the settings where SET lines change
them, calls `maintain()` before a transaction until the replay's calls
have written as many records as the app's (at most 100 calls), and
restarts run A where RESTART lines are (section 2). The GET and SCAN
lines read keys of the workload.

## 1.3 The sets and the checks

`java/stress/apptraces.sh [night|week]` compiles the apps against
`build/bergdb.jar`, records each, replays each recording (with STEP lines
if it ran reclaim) and checks the traces with `tracecheck`, four at a
time; a trace with reclaim or restarts is replayed a second time without
the restarts and the STEP lines, whose lines the contract's grammar does
not have (the records are the same), for `contractcheck` and
`bridgecheck` (`lean/contract/par.sh`). An app that fails its own checks
fails the script, as in `apps.sh`.

- **night** (a step of `night.sh`, after pecmp-medium): DeleteHeavy
  (node size 8, restarts), Churn twice (reclaim, the queue), Readers
  (reader threads, reclaim), IndexChurn (Pub objects with two indexes,
  long keys), BackToEmpty (a twin database, maintain()), Transform
  (transformations that throw or pass a limit, threads), KeyLimits,
  GivenBack; the first 60 to 400 user transactions of each database. The
  check's time grows with the transactions and with the keys' segments:
  IndexChurn's 126 transactions took `tracecheck` 190 s (34 segments
  deep), so night replays its first 60.
- **week** (a step of `week.sh`, after conformance-large): DeleteHeavy at
  node sizes 8, 14, 30 and 62, Churn three ways (node sizes 8 and 30),
  Readers and IndexChurn larger, BackToEmpty with `maintain()` after every
  transaction, Transform with more threads, KeyLimits, GivenBack, and
  WorstCase (transactions of 500 keys of 111 bytes at node sizes 8 to 62);
  seeds from the day's number (night's are fixed), the first 10 to 800
  user transactions.
- Not in it: the apps whose writes are in a child JVM that is killed
  (Kill, KillEmpty, Buffers kill: the recording would hold what the kill
  lost), Buffers many (60 to 150 databases), Huge (values of megabytes),
  Upgrade and OldNodeSize (other jars).

## 1.4 The runs

The night run of 2026-11-20, 12:45 (`build/apptraces/night/`), the
summary as printed:

    workloads: 11 traces of 9 apps; 1725 user transactions, 30723
      operations, 8 restarts replayed; maintain()'s records: the apps' 0,
      the replays' 0; the app's time 1725 times, the app's record's bytes
      at its position 1689 times
    tracecheck: 11 of 11 TRACECHECK OK; transactions checked: 1768
    C-STEP: 0 of 415 transactions fail; 2 STEP lines, 2 iterations, 6
      old KVs met and checked put again, 0 CUT lines; restarts: 0 with a
      RESUME line
    contract: 11 traces, 1757 transactions, 30761 operations, 7028 GET,
      1757 SCAN; failures: C1 0, C2 0, C3 0, R1 0, L1 0, C4 0, C5 0, L2 0,
      KIND 0
    bridge: 11 traces, 1757 transactions, 40375 nodes made, 70545
      entries, 28 touched; failures: all 0
    Time: 151 s
    APPTRACES OK

The apps at these sizes reach few steps of reclaim (2 at night, 18 in the
week run) and no cut in night's traces; the apps' restarts with reclaim
(BackToEmpty, Transform) fall where no STEP line is, so no RESUME line is
checked in night's set. Reclaim across restarts is the crash set's
(section 2).

The week run of 2026-11-20 (the sizes of the script as committed; its
exports and checks then ran in batches of four, since then as a pool of
four, the largest recordings first, which shortens a run), each line `tracecheck`'s verdict and
the replay's own line:

    a1-8-1, a1-14-1, a1-30-1, a1-62-1: TRACECHECK OK; 86 to 88 user
      transactions, 9,741 to 12,147 operations, 6 or 7 restarts; the
      app's record's bytes at 85 to 86 of them
    a2-8-1, a2-30-1, a2q-1: TRACECHECK OK; 250 each, 8,352 to 14,276
      operations, 1 restart; bytes 235 to 240 of 250
    a5-1: 400, 9,582 operations; a6-1: 100, 3,349; b1-1 and b1-2: 800
      each, maintain()'s records 6 in the app and 6 in the replay; b2-1:
      250, 5,470, 2 restarts, bytes 229; b4-1, b4-2: 596 and 214; gb-1:
      20; wc-1 to wc-4: 5 transactions of 500 operations each, at node
      sizes 8 to 62: all TRACECHECK OK
    contract: 19 traces, 4392 transactions, 108262 operations, 17568 GET,
      4392 SCAN; failures: C1 0, C2 0, C3 0, R1 0, L1 0, C4 0, C5 0, L2 0,
      KIND 0
    bridge: 19 traces, 4392 transactions, 219180 nodes made, 336219
      entries; failures: all 0
    APPTRACES OK


# 2. Reclaim across restarts and crashes

## 2.1 Run A restarts

Run B (`probe=K`) restarts a second run and compares its stream with run
A's; the trace is run A's, and run A had no restart. Now run A itself
may restart (TraceExport, `restartA`):

- `restart=K`: after every K-th user transaction's call, a sync,
  `stop()` and a start from a copy of the stream;
- `crash=K`: right after every K-th step's record, inside the step's call
  (the hook of its record), the record is synced and the hook throws: the
  database fails before `Reclaim.step` updates its row in memory and
  before the rest of the call (the table store of a step with eod, the
  row stored again, the cut); run A starts from a copy of the stream as
  it is. A crash that loses the step's record is a crash before the step
  and needs no trace of its own; the exporter checks that the stream
  holds the whole record;
- a recorded app's RESTART lines (section 1).

The recorder goes on through the restart: a node keeps its id; its object
is the restarted database's from when the walk (since a restart, also the
node table's canonical objects) or a transaction's dirty nodes meet it,
and its history must go on from the one before (else an ERROR line), so
recovery's rebuilt nodes are compared with what they were. A pointer that
is a stream pointer after the restart is named by the record that wrote
its version. The start must append no record (checked). The last record
before the restart gets `RESTART stop` or `RESTART crash`, and with
`steps=1` a RESUME line, the iteration in progress that the start read
from the stream: t0, c, lastKey and its endKey E, or `-` (027-02, section
4). After a crash, the crashed step's STEP line takes lastKey after the
step and eod from that row, the row the step committed (030-25's model of
a restart). Restarts do not change the records: on r-del's workload the
trace with `restart=10` has the same records as the one without
(compared by their times and positions), only the RESTART and RESUME
lines and the place of PHYSCUT lines differ.

## 2.2 STEP-resume

C-STEP (lean/Check/Steps.lean, `resumeFailures`, `stepCheck`) checks, at
each RESTART line of a trace with STEP lines:

- a RESUME line with every RESTART line, and none without;
- `RESUME -` only when the last STEP line had eod;
- for `RESUME t0 c L E` whose iteration has had steps: the same c, L the
  last step's L', and that step without eod; for an iteration without a
  step yet: L none, the last STEP line with eod and an earlier t0, c ≤ t0
  + 1 and t0 at or before the restart's record;
- E is the greatest key live after T(t0), from the trace's tree: Java's
  endKey itself, which C-STEP otherwise computes and does not compare;
- the first STEP line after the restart has the resumed t0, c and L.

The chain across the restart (STEP-chain), the range, the puts and the
cut at the iteration's last step are checked as before. `lean/Check/Tree.lean`
reads RESTART (one a transaction) and RESUME. `lean/Check/Trace.lean`, the
trace parser of the other checks, is pinned in `lean/contract/statements.pin`
(it is in the main theorems' trusted closure) and stays unchanged:
`tracecheck` gives it the trace without the RESTART and RESUME lines, which
change nothing its checks read (a first version that parsed them there
failed `pins.sh` in `level2.sh`, step 0). The report adds "R restarts (K crashes), I with
an iteration in progress, S iterations with a step before a restart and
the next after it". Three `#guard` tests of `resumeFailures`.

The fault test, `lean/test-traces/step-faults.sh` (level 3, step 8),
exports a second good trace (300 transactions, `restart=10`, `crash=2`)
that must pass with a crash and an iteration across a restart, and four
faults that must each fail by STEP-resume. Its new lines in level 3,
cut at 100 characters:

    good2: passes: 13 STEP lines, 7 iterations (7 ended by a step with eod), 9 old KVs met and checke
    rmiss: fails, STEP-resume: T(14) a restart without a RESUME line
    rc: fails, STEP-resume: T(14) c 6 after t0 + 1 = 5
    rlast: fails, STEP-resume: T(89) lastKey -, the iteration's last step left [25684929853521952]
    re: fails, STEP-resume: T(14) endKey [8], but the greatest key live after T(4) is [25684923411071

(good2 also: 34 restarts, 6 crashes, 6 iterations with a step before a
restart and the next after it.)

## 2.3 The crash set

`conformance.sh crash` (5 configurations, 3 seeds by default; 200 to 400
transactions, 30 to 200 keys, node sizes 8 and 14, values up to 200
bytes so that iterations take several steps, long keys, deletes up to 60
percent, maintain() every second transaction; a restart every 4 to 10
calls and a crash after every second to fourth step; no run B). A trace
without a cut, a STEP line or a crash fails the set. `level3.sh`, step 8,
runs it after the reclaim set (3 seeds; 1 with quick):

    across restarts and crashes: traces: 15, TRACECHECK OK: 15
    C-STEP: 0 of 6837 transactions fail; 503 STEP lines, 309 iterations
      (307 ended by a step with eod), 7745 old KVs met and checked put
      again, 256 CUT lines with their iteration's last step; traces
      without a STEP line: 0
    STEP-resume: 943 restarts (167 crashes), 844 with an iteration in
      progress, 194 iterations with a step before a restart and the next
      after it

About 2 minutes (15 traces, 215 s of checks four at a time).


# 3. What stays tested

030-26, sections 4 and 5, updated with this item (030's rule "030-26
stays true"):

- The traces now include the user apps' workloads, replayed: Java's
  writer meets the contract, its records are the model's (C-A, C-S) and
  its reads are the model's on them, besides the generated workloads.
  Their limits: the apps' transactions as replayed, not their threads,
  eviction or file streams (shown not to change the records, item 9 of
  030-26's list); the first 60 to 800 transactions of each database; no
  kill.
- Reclaim's steps across restarts and crashes are checked, and Java's
  endKey at each restart. Still tested only: that a STEP line is Java's
  row (the exporter reads it; after a crash the row read back from the
  stream), Java's endKey where no restart reads it, a crash at another
  point of a call (inside the step's transaction it is one before the
  step; after the table store, the same as a restart), and the
  configurations the traces do not reach.


# Files

- java/stress/AppRecord.java (new): the recorder and the recording's
  reader.
- java/stress/TraceExport.java: `restart`, `crash`, `workload`, `apptx`,
  `apprestarts`; run A across restarts (`restartA`,
  `stepEndedAfterCrash`, `resumeLine`, `ptrObj`; the objects of a node
  after a restart); RESTART and RESUME lines.
- java/stress/apptraces.sh (new); java/stress/conformance.sh (the set
  `crash`); java/stress/level3.sh (step 8); java/night.sh (the step
  apptraces); java/week.sh (the step apptraces-week).
- lean/Check/Tree.lean, lean/Check/Steps.lean, lean/TraceCheck.lean
  (STEP-resume), lean/test-traces/step-faults.sh, lean/README.md. No pinned
  file (lean/contract/statements.pin unchanged), nothing under lean/contract.
- 027-02 (section 4: RESTART and RESUME), 030-26 (sections 4 and 5),
  030's readme.


# Log

2026-11-20, 11:00. Started, on the branch `030-31-app-traces` from
6d379122.

2026-11-20, 11:40. Run A across restarts and crashes, RESTART and RESUME
lines, STEP-resume and its four faults; the crash set: 15 traces, 0
failures.

2026-11-20, 12:00. AppRecord and the replay (`workload=F`), with
maintain() calls; `apptraces.sh` night and week, each APPTRACES OK.

2026-11-20, 12:20. Gated: BEFORE COMMIT OK (117 s). The first LEVEL 2
run failed at step 0, `pins.sh`: lean/Check/Trace.lean is pinned; the
RESTART and RESUME lines moved to lean/Check/Tree.lean, and `tracecheck`
gives the pinned parser the trace without them (section 2.2). Then LEVEL
2 OK and LEVEL 3 OK (step 8: the fault test with 14 faults, the reclaim
set as before, the crash set as in section 2.3). Done.
