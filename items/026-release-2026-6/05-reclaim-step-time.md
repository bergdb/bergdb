# 026-05. Each reclaim step scans at its own time

Created 2026-11-13 by Frans Lundberg. Status: open.

For release 2026.6: P8 of 023-05 ("each reclaim step scans at its own
time", the prototype `p8-steptime`), decided for 2026.6 (024-05, OP9;
Frans, 2026-11-12, 12:10, "as recommended"; 026's readme), with the fix
of the fault the reviews of 023-07 found in it (023-08, fault 13), on
today's `main`. Made by the agent "p8" of coord-1113 in a clone; the
coordinator lands it.

Why now: 026-04, section 4. A step scans at its iteration's start time
tStart, so the iteration in progress at a mass delete walks every key
live at its start, the deleted ones too, at the step cap of 16 kB of
KVs a user transaction; back to empty's lag grows as about n/300 + 1,280
transactions (33,501 at 10M keys and f = 3/8). With each step scanning
at its own time the deleted keys are not met; expected a lag of about
1,280 at every n and f.


## 1. The plan

1. Read P8 (023-05, P8), the reviews (023-08; review A, section 2.6;
   check V8, `08-reviews/checks/p8-liveness.md`) and `main`'s reclaim
   since the prototype: the last touch (024-07: a step marks the paths of
   its own puts only), OP8 (024-34: a KV at pCut or later is not read
   again), the pace cap (024-31), `maintain()` (024-32), the limits
   (024-17, 024-24), SE (021-28: `GetMany.endKey`).
2. The change in `Reclaim` (section 2), on a branch from `main`:
   P8's scan at the step's time and its end key, V8's count (only the KVs
   stored before pStart count toward a step's size), and one rule of my
   own, the scan's result holds the KVs to rewrite only (section 2.4).
3. The cut's argument with today's reclaim (section 3), and what the
   Lean model and the conformance say (section 3.4).
4. Unit tests; the gates of section 5; the lag of 026-04's workload (d)
   at 1M, 4M and 10M at f = 1/4, 3/8, 1/2 (section 6).


## 2. The mechanism

All in `Reclaim` (java/src/bergdb/core/Reclaim.java).

### 2.1 The end key

* **What.** E, the last key live at an iteration's tStart, BergDB's own
  keys included (the value of any live key may need a rewrite), or
  `IterationInfo.NO_KEY` (an empty array) if no key was.
* **When, by whom.** When an iteration begins: in
  `transactionCompleted`, at the external transaction t that begins it
  (under the write lock, `lastKeyAt(t.tt)`), and in `maintain()`'s M1
  (`lastKeyAt(lastTransTime)`, the time of the state at pStart). One
  backward `GetMany` of one KV at that time with the maintenance follower;
  an assert checks that the read's actual lookup time is the one asked
  (review A's caution for `maintain()`, section 2.7: `lastTransTime` is a
  committed transaction's time, `Db.maintain` passes
  `dbClock.lookupTime(Long.MAX_VALUE)`).
* **Kept.** In the iteration's row, the line `endKey=` (`none` for
  NO_KEY, else the segments as lastKey has them), stored with the table
  in the same call and in every step's row after it. A row without the
  line (stored before 026-05) is read with endKey null: no bound; a bad
  value is refused (`InternalDataException`), as for lastKey. 027-03's
  section on the internal texts (024-02 until 2026-11-13) says so.

### 2.2 The scan at the step's time

* A step (`Reclaim.step`, at a later external transaction or in
  `maintain()`'s M2, under the write lock) scans with `lookupTime =
  Long.MAX_VALUE`, the state after the last committed transaction, its
  own time, from after lastKey, with `GetMany.endKey = E` (inclusive):
  the scan ends after E, as at the end of the data (`eod()`), and the
  iteration is done. If E is NO_KEY, or lastKey is at or after E, the step
  does not scan: the iteration is done.
* The scan's KVs are the values the step rewrites: no second read. The
  scan is at the step's time, so its value is the one a read at that
  time gives (before, each KV stored before pCut was read again at the
  latest state, 024-34); `keyRead` and `readTime` (the scan's actual
  lookup time) as before.
* The rest as on `main`: the rewrite of each live value stored before
  pCut, the paths of the puts made dirty (024-07), the row, tEnd, pEnd,
  pSafe, the cut.

### 2.3 What counts toward a step's size (V8, fault 13)

* A KV adds `key.length * 8 + value.length + 100` to the step's size only
  when its value is stored before pStart (`Spos.isValid`, not a vpos,
  `kvt.spos < it.pStart`). The step ends after the KV that takes the size
  past writeSize (min(allowed, 16 kB)), or at the reserve
  (`maxNodes`, index nodes followed), as before.
* Why: a counted KV was live at tStart with that value (its record is
  before pStart, so at or before tStart, and no write of its key since),
  and the scan moves forward, so each is counted once: an iteration takes
  at most (the KVs live at tStart) / 16 kB steps, as with the scan at
  tStart, whatever the user puts ahead of the scan. With every KV counted
  (P8 as built) the keys put ahead of the scan slowed it: a queue before
  a key that stays, or random puts faster than a step, kept an iteration
  from ending (023-08, section 3; V8, sections 2 and 3).

### 2.4 The scan's result: the KVs to rewrite only

* My addition. A KV whose value is at pCut or later (or not yet written)
  is walked and left out of the result (`StopCondition.CONTINUE`; at a
  stop, `STOP` with lastKey at it). The result holds the KVs to rewrite
  only.
* Why: with V8's count a step walks, uncounted, the KVs put since pStart
  in its range, bounded only by the reserve (about 2,759 index nodes). On
  V8's branch they stayed in the result with their values until the step
  ended: a queue of large values before a key that stays could hold
  thousands of values in one step. Now the result holds at most about
  16 kB of counted KVs and one more, as on `main`.
* The value limit of 015-50 moved from the loop into the scan: a KV to
  rewrite whose value node would take the step's value nodes past
  `StoredTrans.valueLimit()` stops the scan before it (`STOP`), unless it
  is the step's first; it is the first of the next step. The same lastKey
  and the same puts as the loop gave.
* `IterationInfo.kvCount` and the statistics' `kvs`: the KVs the step's
  range covered, walked or kept. `Stats.Iteration.gets` (the second
  reads) is gone.

### 2.5 A pending cut that is durable is made first

* `pretruncateIfPossible`, when it decides a newer cut, first makes the
  pending one if its table is durable (`cutIfDurable()` before
  `pendingCut` is replaced). Before, the newer decision replaced it, and
  if every transaction decided a newer cut, no cut was made.
* Found by `Reclaim.Tester.testPretruncate` with 026-05's steps: one key
  overwritten with 100 kB values; its iterations now end in one step
  (the overwritten key is not counted), so the test's last transaction
  decided a newer cut over the durable one. V8 changed the test (a few
  more transactions with a sync); check V8's Q2 recommended this fix of
  the cause instead, "in its own change". Own commit; the test is not
  changed.


## 3. The cut's guarantee

### 3.1 Values (REWRITES)

023-05 P8, section 2.3, holds on `main` as it is: a value v stored
before pCut and read by a lookup at a time t from tEnd on was written at
w <= tStart (every record before pStart is of a transaction at or before
tStart); no put or delete of its key k came in (w, t] (a put writes a new
value node, a delete leaves no entry, a time split copies the pointer);
so k was live with v at every time in [tStart, t]. k <= E (live at
tStart). The steps' ranges (lastKey, L] start at the first key, join
(lastKey is the last key the scan covered, also with CONTINUE and at the
value limit) and reach E (the last step's scan passed E, reached the end,
or found lastKey at or after E). Step i, whose range holds k, scanned at
s_i in [tStart, tEnd], when k was live with v, stored before pCut: so k
was in its result, and the step put v again at tt_i <= tEnd <= t. Then
k's entry at t is the rewrite or later, not v: no lookup from tEnd on
reads a value stored before pCut. The count (2.3), CONTINUE (2.4) and the
value limit change where steps end, not that the ranges join.

### 3.2 Index nodes (LIVEBELOW, COVER)

Unchanged from 024-07, section 4: the touch marks the paths of the
step's puts; T-COVER needs REWRITES (3.1) and LIVEBELOW (the delete
path's invariant I2, `Dag.deleteUpward`), neither of which refers to the
scan's time. The space root is on the path of every step's row.

### 3.3 Determinism and the rerun (INV-RESTART)

Nothing of the scan is stored: a step's record holds its puts, its row
(now with E) and the got-dirty ids, and a start reruns records, never a
scan. What decides the next step after a start: the row (lastKey, E,
pCut, rewritten), the stream's length, the state at the latest time and
the value nodes' positions (`Kvt.spos`; the rerun gives a value node its
stored position), all functions of the stream. E is computed once, from
the state at tStart, and stored in the same call as the table. The
reserve counts index nodes by id. RestartInvariance with reclaim (level3,
step 3) checks it (section 5).

### 3.4 The model, the trace and the conformance

* The Lean model has no scan and no keys (024-07, section 4.4):
  REWRITES and LIVEBELOW are Java's premises of T-COVER and T-LATEST;
  the model needs no change. 027-02 (the trace format) has no scan time:
  a step is a `TX` with its OP lines and a TOUCH line (the paths of its
  puts), and `CUT` lines for Java's cuts.
* What the checker checks on every trace with reclaim: C-A (TouchOK),
  C-S (the model's step on Java's records and D), C-CUT (`CutOK` at every
  cut Java decides, in the model's state: every version a read from the
  first available time on may follow is at the cut or later). So the
  scan's time is checked through its effect: a value that a step failed
  to rewrite fails C-CUT at its cut. The traces change (other steps), the
  checks not.
* T-SCHEME stays checked by running, not proved.


## 4. Tests

New unit tests in `Reclaim.Tester`:

* `testStepScansAtItsOwnTime` (P8's, adapted to the 500 operations of
  024-17): 2,000 keys, an iteration begins, all but the last ten are
  deleted in key order in four transactions; the iteration's scans cover
  117 KVs (at most 400 asserted); with the scan at tStart the test fails
  (probe: the build with `lookupTime = it.tStart`). The ten are at pCut
  or later when it is done.
* `testEndKeyBoundsTheScan` (P8's, stronger): 500 keys, then 200 new keys
  after them a transaction; the iteration ends and its scans covered 503
  KVs (at most 510 asserted): E keeps the steps from walking the new
  keys.
* `testMaintainBeginsWithEndKey`: an iteration that `maintain()` begins
  has E.
* `testSerializeEndKey`: the row's E stored and read back (a key,
  `none`, no line), and three bad values refused.

`main`'s liveness tests of 023-09 pass unchanged, their comments brought
up to date: `testQueueBeforeAKeyEnds` (review C's queue before "/z",
within 37 transactions) and `testRandomPutsAheadDoNotSlowTheScan` (review
B's random puts ahead, within 30). No expected value of an existing test
changed.


## 5. Gates

On d9822ebe (the change, before main moved) and on 57cbb21e, the
branch merged with `main` 20535a1d (026-06 landed at 08:47; the
coordinator's message): the gated tree is the one that lands. Logs in
/Users/f/fl/bench/2026-11-13/p8/runs/ (`before-commit.txt`,
`level1.txt`, `level3.txt`, `level4.txt` for d9822ebe; `final-*.txt` and
`final.log` for 57cbb21e).

| Gate | d9822ebe | 57cbb21e |
|---|---|---|
| `before-commit.sh` | OK (68 s; unit 1,704, f 89, demos 14) | OK (71 s) |
| `level3.sh`, full  | OK (8 min 15 s)                        | OK (7 min 23 s) |
| `level1.sh`        | OK (MEM 129, SS 1.53)                  | OK (MEM 129, SS 1.53) |
| `level4.sh quick`  | OK (conformance evict 18 of 18)        | OK (18 of 18) |
| `count-gates.sh`   | -                                      | COUNT GATES OK (137 s) |

`before-commit.sh` again on d2ff5fb8 (`main` 4f191556 merged; its Java
changes are two comments): BEFORE COMMIT OK (62 s; unit 1,708, f 89,
demos 14), runs/final2-before-commit.txt.

* **level3** on both heads: ReclaimStress 4 x 50 rounds, 0 failures,
  every round with a cut; RestartInvariance with reclaim, four
  configurations: the stream identical with and without restarts, the
  same cut; CrashTest, ReclaimReaders, LoadTest (6 restarts with a full
  check after a cut), PowerLossTest, InterruptStress OK; the conformance
  with reclaim: 35 of 35 traces TRACECHECK OK, C-CUT 0 of 794 cuts
  failing.
* **level4 quick** (d9822ebe): the conformance with eviction, 18 of 18
  traces, C-P and C-H 0 of 4,886 transactions failing; LargerThanMemory
  OK.
* **count-gates** (57cbb21e), against `main`'s counts (026-07's run at
  08:31, whose change is the write buffer; its G4 kept is 026-04's on
  `main`, 2,618,568): G1's largest record 112,048 bytes (108,912); G3
  4.401 (4.410); G4 kept 0.959 of the twin's (1.072), resident objects
  1.071 (1.081); G5 kept 0.015 (0.139), and `maintain()` quiet after call
  3,015 of 20,000 (6,130).
* **level2** not run: its conformance has no reclaim (no `retain`), so
  reclaim's traces do not enter it.
* **026-05's own traces** (`runs/traces.sh`, as P8's `p8traces.sh`; the
  build of d9822ebe copied to p8/after/), each checked by the Lean
  checker (C-A with TouchOK, C-S, C-CUT; C-P and C-H for run E), three
  seeds each: heavy deletes (`del=60`, 800 transactions, 200 keys), bulk
  puts in key order (`bulk=20`), long keys (`long=1`), run E with random
  eviction, and `maintain()` after every third transaction (`maint=3`).
  15 of 15 TRACECHECK OK, C-CUT 0 of 479 cuts failing (s-maint 115 to
  121 cuts each), C-P and C-H 0 failing. Summary:
  runs/traces/summary.txt.


## 6. The lag after a mass delete

026-04's workload (d) (024-30's G4: n keys put in key order, 100 a
transaction, all deleted in key order, 100 a transaction, then a drive of
40 R; R = 1,000 transactions; as 026-04, section 4.1): FracRuns with `g4its=1`, on the
branch `026-05-lag` (57cbb21e with 026-04-lag's three commits
cherry-picked, 412b97fc, 28df3457, 33e9ea54; not to land) in the worktree
/Users/f/fl/bench/2026-11-13/p8/lag; one slot, 09:18 to 09:25. Outputs:
p8/runs/d1m.txt, d4m.txt, d10m.txt (`runs/lag.sh`, `runs/lag-an.py`,
026-04's). "Before" is 026-04, section 4.2 (`main`).

| n   | f   | Lag before | Lag after | X's end after | X's KVs walked | X's steps |
|---|---|---|---|---|---|---|
| 1M  | 1/4 | 4,395      | 1,281     | 0             | 564,732        | 7,709     |
| 1M  | 3/8 | 1,857      | 1,272     | 0             | 162,479        | 2,168     |
| 1M  | 1/2 | 1,850      | 1,266     | 0             | 163,844        | 2,186     |
| 4M  | 1/4 | 4,066      | 1,286     | 0             | 1,038,835      | 13,853    |
| 4M  | 3/8 | 13,736     | 1,273     | 0             | 2,367,611      | 32,856    |
| 4M  | 1/2 | 13,737     | 1,265     | 0             | 2,750,622      | 37,267    |
| 10M | 1/4 | 8,064      | 1,279     | 0             | 2,554,819      | 34,066    |
| 10M | 3/8 | 33,501     | 1,273     | 0             | 40,306         | 539       |
| 10M | 1/2 | 33,181     | 1,268     | 0             | 56,610         | 756       |

* **The lag is 1,265 to 1,286 transactions at every n and f**, as 026-04,
  section 4.3 expected (about 1,280): the iteration X that runs when the
  deletes end ends with them (X's end 0, the last delete transaction, in
  every run), so the lag is the two iterations after it, R/4 + about
  25 + R. It no longer grows with n (before: up to n/300 + 1,280).
* **The stream after the drive**: kept 2.26 to 2.39 MB at the end, as
  before; kept 4 R into the drive 2.14 to 2.30 MB at every n and f
  (before: up to 2,596 MB at 10M, 1/4).
* **The cost: work ahead of the deletes** (section 7). X's steps run just
  ahead of the delete front and rewrite values that a later delete
  removes (4M, 1/2: 782,791 values; 3/8: 402,179). The stream written by
  the end of the drive, against `main`: 1M +0.4 % (1/4 and 3/8); 4M
  +0.04 %, +6.0 %, +12.3 % (1/4, 3/8, 1/2: 1,438 MB against 1,281 MB);
  10M +0.5 % and +6.9 % (1/4, 3/8; 1/2 not in 026-04's run). Within the
  internal fraction: every step is allowed by it.


## 7. Risks and limits

* **The walk of a step.** A step walks, uncounted, the KVs put since
  pStart in its range up to the reserve; with random puts it walks about
  r + g/2 KVs (V8, section 4.1: a user transaction's own puts). Each
  walked KV's value is loaded by the scan (GetMany reads it), also when
  it is left out of the result. A keys-only scan would remove those loads
  (023-05 P8, section 8).
* **A chase is still possible, at the reserve.** A user who puts, before
  E and ahead of the scan, more index nodes' worth of new keys in every
  transaction than a step's reserve (about 2,759 index nodes) keeps an
  iteration going while such transactions last; each step still moves
  the scan by a reserve's worth. Not seen; it needs transactions near
  the size limit, all in the range ahead of the scan.
* **Work ahead of an ascending mass delete** (023-05 P8, section 5.4;
  section 6): the steps run just ahead of the deletes and rewrite values
  that a later transaction deletes, within the internal fraction: up to
  12 % more stream written over workload (d) at 4M and f = 1/2, 0 to 7 %
  at 1/4 and 3/8 (P8's Q2, 023-07's D5, recommended accept; Q3 here).
* **A row of 2026.5 or before** has no E: its iteration's scan is not
  bounded by E, only by the count; it ends as on V8's branch.
* **Bytes.** Reclaim's records change (other steps, E in the row), so
  StreamDigest's digests and any stream pin change (024-05, "bytes"); no
  record format change, no rerun rule.


## 8. Questions for Frans

Each is decided here by the recommendation, so that the work goes on;
Frans may overturn it.

* **Q1. The pending cut (2.5)**, its own commit (94421dd0): a durable
  pending cut is made before a newer decision replaces it. Recommended:
  yes (check V8's Q2, 023-08); it keeps `testPretruncate` as it is,
  where V8 changed the test.
* **Q2. The scan's result and the second read (2.4)**: my addition to
  P8 and V8; the result holds the KVs to rewrite only, and their values
  come from the scan. Recommended: yes; it bounds what a step holds and
  halves the reads of a step that rewrites.
* **Q3. Work ahead of an ascending mass delete** (P8's Q2, 023-07's D5):
  accept. Recommended: yes, within the internal fraction.
* **Q4. G4's lag as a gate** (024-30, Q30-3; 026's readme): with 026-05
  the lag is 1,265 to 1,286 transactions at 1M, 4M and 10M and every f
  (section 6), R/4 + about 25 + R; a gate at 2 R (2,000 transactions at
  G4's R) is independent of n and has a margin of 1.55. Recommended: make
  it a gate once 026-05 is on `main` (a change of CountGates, not made
  here).


## 9. State

2026-11-13, 09:40. Done; ready to land. Clone
/Users/f/fl/bench/2026-11-13/p8/clone, branch `026-05-step-time`:
94421dd0 (2.5, the pending cut), d9822ebe (2.1 to 2.4, the tests, the
row's text in 024-02, now 027-03), 73cad7c7 (this item), 57cbb21e
(merge of `main` 20535a1d), 6bbe9594 (this item's results), d2ff5fb8
(merge of `main` 4f191556: 024-02 moved to 027-03, so the row's text
went with it; `main`'s Java changes there are two comments), then this
State. Every gate of section 5 OK on 57cbb21e; before-commit again on
d2ff5fb8 (section 5). The lag of section 6 measured: 1,265 to 1,286 at
every n and f. No expected value of an existing test changed. The lag
branch `026-05-lag` (worktree /Users/f/fl/bench/2026-11-13/p8/lag) is
not to land. Open: Frans's Q1 to Q4 (section 8), each decided here by
its recommendation.
