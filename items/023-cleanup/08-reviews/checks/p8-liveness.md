# V8. Review B's finding 2.6: P8 and keys put ahead of the scan

Written 2026-11-10 by Frans Lundberg. A check of one finding of review B
of 023-07 (section 2.6, "Liveness"): with P8 (023-05, P8) keys put before
the end key E, ahead of reclaim's scan, are scanned too, so that under a
growing random-key workload an iteration ends only after about
(L0 / g) (e^(g / r) - 1) transactions instead of L0 / r. Review C (its
section 2.6, fault 13) found the same fault in another form; its probes
and its quota sketch are judged here too (section 5).

Work in /Users/f/fl/bench/2026-11-10/v8/: the clone `clone/`; worktrees
`wt-main` (main, `0a0f0016`), `wt-p4` (`023-p4-empty-key`, `0e66d1c9`),
`wt-p8` (`023-p8-steptime`, `f56dca40`), `wt-fix` (branch `023-v8-fix`
from `f56dca40`, section 4) and `wt-quota` (branch `023-v8-quota` from
`f56dca40`, review C's quota, section 5). Probes in `probe/`, their
outputs in `out/`, the T1 and T4 logs in `t1/`. Committed in the clone
only (section 6).

Symbols: L0 the live keys when an iteration starts, g the net new keys a
transaction, r the KVs a step scans (72 for the probe's keys: 3 segments
and 100 bytes, 24 + 100 + 100 = 224 bytes by the scan's measure, against
16,000 bytes a step).


## 1. The mechanism, as read

* **main and P4** (their `Reclaim.java` is the same file). An iteration
  starts at an external transaction when the stream has grown by twice
  the startup distance and a quarter of the retain duration has passed.
  After each later external transaction `transactionCompleted` computes
  `allowed`, a quarter of the growth since pStart minus the bytes
  rewritten so far; above 10 kB it runs one step with
  `min(allowed, MAX_STEP_SIZE)`, MAX_STEP_SIZE = 16,000. The step's scan
  is a `GetMany` from lastKey at `lookupTime = tStart`; its stop condition
  adds `key.length * 8 + value.length + 100` for every KV met and stops
  past the limit (or at the reserve of index nodes). So a step covers
  about 16 kB of the KVs live at tStart, and an iteration takes about
  (bytes of KVs live at tStart) / 16 kB steps, L0 / r.
* **P8** scans at `Long.MAX_VALUE`, the state after the user's
  transaction, and stops at E (`IterationInfo.pastEnd`). The stop
  condition is unchanged: every KV met counts, also one put since tStart.
  Keys put in (lastKey, E] since tStart are therefore met and counted, so
  the scan's progress through the key space a step falls as the range
  ahead fills. With uniform random puts the position x (0 to 1) follows
  dx/dt = r / (L0 + g t), so x = (r / g) ln(1 + g t / L0), and x = 1 at
  t = (L0 / g) (e^(g / r) - 1).
* **B's description is right**, and its model fits every run below to a
  few percent (table 2.2). One addition: E bounds only keys after the
  last key live at tStart. Review C's form (section 3) shows that any key
  after the appends (a "/z") makes even ordered appends land before E.
* **Not changed by P8**: the allowance, one step at most an external
  transaction, the touch of (lastKey, lastKeyOfStep] at the step's time.


## 2. B's probe on the three builds

### 2.1 Settings

B's `P8Live.java` (copied to `probe/p8/`, and to `probe/noend/` without
the print of `endKey`, which main and P4 lack; both print also the kept
bytes, the stream from the first available position). A Core Db on a
file, budget 1 GB, test clock 10 ms a transaction, retain 1 s, startup
distance 100 kB, keys `/h/` and 16 hex digits of a random long, values of
100 bytes, each transaction 90 % puts of new keys and 10 % deletes of
live ones. Runs A (1,000 ops a transaction, g = 800), B (200 ops,
g = 160) and C (60 ops, g = 48), as B's. P8's runs A to C reproduce B's
outputs line for line. Run A was also run to 4,500 transactions on main
and the fix (`A45`).

### 2.2 Iterations

Lengths of the iterations done, in transactions; "rule" is L0 / r for
main and P4, (L0 / g) (e^(g / r) - 1) for P8.

| Run | Build | Iterations done, lengths                 | Rule, last one | Cuts |
|---|---|---|---|---|
| A   | main  | 25, 317 (3rd: 3,854 at A45)              | 324; 3,857     | 1    |
| A   | P4    | 25, 317                                  | 324            | 1    |
| A   | P8    | none; the first (L0 1,700) at 1,998 steps | about 140,000 | 0    |
| B   | main  | 12, 68, 222, 718, 2,316                  | 2,318          | 4    |
| B   | P4    | 10, 66, 215, 696, 2,245                  | 2,245          | 4    |
| B   | P8    | 39, 382, 3,512; the 4th from L0 630,420   | 3,522; 32,300 | 2    |
| C   | main  | 15, 27, 56, 83, 140, 233, 389, 650, 1,084 | 1,083         | 8    |
| C   | P4    | 17, 26, 49, 78, 132, 220, 369, 615, 1,026 | 1,026         | 8    |
| C   | P8    | 17, 37, 73, 146, 286, 556, 1,086          | 1,088         | 6    |

### 2.3 At the end of each run

| Run | Build | Transactions | now - f, ms | Stream, MB | Kept, MB |
|---|---|---|---|---|---|
| A   | main  | 2,000        | 19,729      | 2,252.3    | 2,251.8  |
| A   | P4    | 2,000        | 19,729      | 2,235.9    | 2,235.4  |
| A   | P8    | 2,000        | never set   | 2,185.6    | 2,185.6  |
| A45 | main  | 4,500        | 2,999       | 5,765.9    | 5,749.4  |
| B   | main  | 10,000       | 66,419      | 2,918.2    | 2,853.1  |
| B   | P4    | 10,000       | 67,459      | 2,897.9    | 2,836.9  |
| B   | P8    | 10,000       | 60,599      | 2,783.3    | 2,777.6  |
| C   | main  | 3,000        | 2,919       | 279.2      | 195.6    |
| C   | P4    | 3,000        | 4,369       | 271.0      | 195.6    |
| C   | P8    | 3,000        | 7,699       | 254.2      | 211.7    |

### 2.4 What the runs say

* **main and P4 follow today's rule exactly**: every iteration scanned
  the KVs live at its tStart, 72 a step, one step a transaction (the
  allowance held none back). The "rule" column uses the live keys at the
  first step, one transaction later, so it is up to 2 % high.
* **P8 follows B's model**: runs C, B and A take 1.43 times today's
  length (g / r = 0.67), 3.7 times (2.2) and about 6,000 times (11.1).
  In run A no iteration ends in any time that matters: about 140,000
  transactions for the first, which started with 1,700 live keys (main
  scanned 1,746 KVs in its first iteration, from the same transaction).
* **A correction of B's emphasis.** In this workload today's rule also
  lets now - f grow without a bound: an iteration takes L / r
  transactions, and L grows, so main's now - f at the end of run B
  (66 s) is above P8's (61 s), and main keeps nearly the whole stream in
  run A too (2,251.8 of 2,252.3 MB: a cut at pCut, two iteration starts
  back, frees little while the database grows twelvefold an iteration).
  "60 s, climbing" is therefore not P8's fault alone. What P8 changes is
  the factor a database grows by during one iteration: 1 + g / r today,
  e^(g / r) with P8 (run A: 12 against about 66,000). That is the
  fault: for g above r an iteration started on a small database
  practically never ends, and nothing is ever cut.
* Today's rule is itself a pace of 16 kB of KVs a transaction, whatever
  the transaction's size: at 1M live keys and 1,000 random puts a
  transaction, an iteration is 14,000 transactions. Whether that keeps
  up in Frans's sense is a question for 023-02 (R6), not for P8.


## 3. Review C's probes

C's unit-test probes (`rev23/c/scratch-p8/probes.diff`) rewritten as one
class without asserts and without `endKey` (`probe/cq/`, `CProbes`), so
that it runs on main and P4 too: a queue of 1,000 keys, 200 puts at the
tail and 200 deletes at the head a transaction, with and without a key
"/z" after the queue; and 500 keys with 200 ordered puts a transaction
after them and "/z" after those. Also B's form at unit scale
(`probe/ut/`, `RandAhead`): 500 keys, then N new random keys between them
a transaction. Transactions until the first iteration is done (limit
3,000; RandAhead 5,000):

| Probe                           | main | P4 | P8                 | Fix | Quota |
|---|---|---|---|---|---|
| queue with "/z"                 | 22   | 15 | not done, 137.5 MB | 5   | 15    |
| queue without "/z"              | 22   | 15 | 5                  | 5   | 5     |
| ordered puts with "/z"          | 9    | 9  | not done, 119.6 MB | 9   | 28    |
| random ahead, 100 a transaction | 10   | 10 | 22                 | 10  | 11    |
| random ahead, 200               | 8    | 8  | 57                 | 8   | 9     |
| random ahead, 400               | 7    | 7  | 449                | 7   | 8     |
| random ahead, 800               | 7    | 7  | not done           | 7   | 7     |

C's figures for P8 are reproduced (3,000 transactions, 137,547,904
bytes). main differs from P4 in the queue (22 against 15) because main has
no upward unlink. Quota and Fix: sections 4 and 5.


## 4. The fix: count only the KVs the iteration must cover

### 4.1 The mechanism

* **What.** In `Reclaim.step`, the scan's stop condition adds a KV's
  bytes to the step's size only when its value node is stored before the
  iteration's pStart (`kvt.spos != Spos.NULL && kvt.spos < it.pStart`;
  `Kvt.spos` is the value node's position, 020-24-09, U9-8). Every KV
  the scan meets is still in the step's result: read, rewritten when
  stored before pCut, and inside the touched range, as before. Only where
  a step ends changes. An `if` around the existing line, a unit test
  (`testRandomPutsAheadDoNotSlowTheScan`) and a fixture's change
  (section 6); 65 lines with the comments.
* **When, by whom.** At every step, in the scan, by `Reclaim.step`, which
  `transactionCompleted` calls after an external transaction under the
  write lock; unchanged.
* **Why it bounds the iteration.** A counted KV has a value from before
  pStart, so its key was live at tStart with that value; the scan moves
  forward, so each is counted once. Every step but the last counts about
  writeSize, so an iteration takes at most (bytes of the KVs live at
  tStart) / 16 kB steps, plus the steps that the reserve or the value
  limit cut short: today's bound, whatever is put ahead of the scan,
  random keys, a queue or ordered appends before E. Keys deleted or
  overwritten since tStart count nothing, so an iteration is at most as
  long as today's (measured 0.80 to 0.97 times, table 4.2).
* **The cost of a step.** A step walks the KVs put since pStart in its
  range without counting them. Measured, a step walked r + g / 2 KVs on
  average (runs A, B, C: 503, 160, 99), about the user transaction's own
  puts. The walk of one step stays bounded by the existing reserve,
  `maxNodes` = 4 MiB / 1,520 bytes = 2,759 index nodes. Today's touch
  already visits the same range at the current time, so the nodes made
  dirty are of the same order; the new cost is the read of each walked
  value (P8, section 8's keys-only scan would remove it).
* **Soundness.** P8's arguments (P8, 2.3 and 2.4) are about the scan's
  time, the joined ranges and the touch, not about where a step stops;
  the ranges still join (lastKey is the last key met, as before). A value
  not yet written has a vpos at or after the stream position at its
  transaction's start, so it is never counted before pStart. Nothing new
  is stored; `spos` is a function of the stream, and a restart's rerun
  gives a value node its stored position (`DbStarter.nodeCreated`).
* **How it is checked.** The unit test: 500 keys, then 400 new random
  keys between them a transaction; the iteration must end within 30
  transactions (fix: 7; P8: 449). B's and C's probes (sections 2, 3,
  4.2). T1 and T4 of 023-03 with CleanupRule (4.3). `before-commit.sh`.

### 4.2 B's probe on the fix

| Run | Iterations done, lengths                    | L0 / r, last one | Cuts | now - f, ms |
|---|---|---|---|---|
| A   | 21, 251 (3rd: 2,551 at A45)                 | 312; 3,112       | 1    | 19,769      |
| B   | 9, 61, 188, 574, 1,752, 5,341               | 5,800            | 5    | 20,499      |
| C   | 16, 25, 50, 76, 126, 207, 346, 568, 934     | 966              | 8    | 6,179       |

Stream and kept at the end: A 2,257.5 and 2,257.0 MB; B 2,896.9 and
2,708.8 MB; C 273.4 and 201.0 MB. The iterations are main's or shorter;
now - f follows main's rule, linear in the live set (2.4). Wall time as
main's (A45: 180 s against 185 s).

### 4.3 T1 and T4 (023-03) with CleanupRule

The commands of P8's report (P8, 5.1 to 5.3), rerun here for P8 and the
fix on the same machine (`t1/`); P8's figures match its report. Twin:
M1 2,108,432, M3 1,040 ms, M8 83, M9 2,504, M11 83; W 365,008; a_n 14,
16, 17 at 1,000, 100,000, 1M (023-03, section 2.6).

| N, order       | Build | M1, most  | M3, ms | M8 | M9    | M11 | Fails |
|---|---|---|---|---|---|---|---|
| 1,000          | P8    | 2,118,280 | 1,224  | 85 | 3,912 | 98  | C9 (+15) |
| 1,000          | fix   | 2,118,280 | 1,224  | 85 | 3,912 | 98  | C9 (+15) |
| 100,000        | P8    | 2,119,792 | 1,219  | 91 | 2,840 | 105 | C9 (+22) |
| 100,000        | fix   | 2,150,496 | 1,222  | 87 | 3,024 | 98  | none     |
| 1M             | P8    | 2,109,160 | 1,218  | 90 | 3,168 | 91  | none     |
| 1M             | fix   | 2,171,520 | 1,218  | 94 | 3,168 | 106 | C9 (+23) |
| 1M, descending | P8    | 2,138,472 | 1,168  | 78 | 3,104 | 86  | none     |
| 1M, descending | fix   | 2,143,320 | 1,166  | 85 | 3,152 | 85  | none     |
| 1M, random     | P8    | 2,127,032 | 1,137  | 84 | 3,352 | 91  | none     |
| 1M, random     | fix   | 2,159,144 | 1,138  | 84 | 3,800 | 88  | none     |

* C1 to C3, C5 to C8 and C10 hold for the fix in every row (M10, the
  last iteration's touch, is 7; M12 at most 6).
* **C9 at 1M ascending** is 106, 6 over twin + a_n. The same kind of
  excess as P8's at 100,000 (P8, 5.1, Q4): the drive's iterations are
  the same in both builds (one step, 4 KVs, touch 7); the fill and the
  deletes differ slightly (iteration 3: 932 steps against 919), so the
  stream's phase at the end of the drive differs. Shifting the drive by
  1, 2, 3 or 5 overwrites (pre=K) leaves it at 106 (P8: 91 each time).
  Not examined further: whether the start reruns a longer startup
  section, as P8 found at 100,000, is open (Q4 of P8 covers both).
* **T4** (L = 1,000, 100,000 transactions):

| Queue   | Build | Iterations | Steps | KVs scanned | Kept, most | D, most | Record, most |
|---|---|---|---|---|---|---|---|
| ordered | P8    | 167        | 3,276 | 146,356     | 1,606,232  | 139     | 34,136       |
| ordered | fix   | 167        | 3,264 | 146,637     | 1,621,936  | 166     | 32,152       |
| hashed  | P8    | 214        | 4,644 | 214,640     | 3,919,648  | 693     | 26,520       |
| hashed  | fix   | 216        | 3,480 | 216,708     | 3,628,112  | 624     | 30,032       |

  (Kept, D and record are the most of the ten samples.) The hashed queue
  needs 25 % fewer steps: its new keys before E are no longer counted.


### 4.4 The cost: overwrites of live keys

The fix also stops counting keys overwritten since pStart. A probe
(`probe/upd/`, `UpdProbe`, `out/upd.txt`): 200,000 random keys, then
3,000 transactions of u overwrites of random existing keys (no growth).
With the fix the iteration ends after (L / u) ln(1 + u / r) transactions
(the column "Iteration"), and its last steps walk r + u KVs; measured
exactly so:

| u     | Build | Iteration | KVs a step | Most scan nodes | Slowest, ms | Stream, MB |
|---|---|---|---|---|---|---|
| 200   | P8    | 2,778     | 71         | 112             | 17          | 933        |
| 200   | fix   | 1,330     | 150        | 469             | 13          | 984        |
| 1,000 | P8    | 2,778     | 71         | 112             | 38          | 3,480      |
| 1,000 | fix   | 540       | 370        | 1,745           | 96          | 3,769      |

* Iterations are shorter than today's, so reclaim writes 5 to 8 % more
  (more iterations, each a full touch); within the allowance.
* A step near an iteration's end walks about r + u KVs, as many as the
  user's transaction writes, and reads each value. "Slowest" is the
  slowest user transaction with its step, one run on a loaded machine
  (load 15 to 26), not a timing measurement: 96 ms against 38 ms at
  u = 1,000. The reserve bounds one step (here 1,745 of 2,759 nodes).
  P8's keys-only scan (P8, section 8) would remove most of it: a value
  is read only when its position is before pCut, which a KV put since
  pStart never is.
* A weight w between 0 and 1 for the new KVs instead of 0 would bound the
  walk at r / w, but brings back the exponential, at g above r / w:
  (L0 / (w g)) (e^(w g / r) - 1). Only w = 0 removes it.


## 5. Review C's quota, against the fix

### 5.1 The quota

C's sketch (review C, 2.6, fix (2); its worktree's uncommitted diff),
copied without its probe switches and switched on, in `wt-quota`: the
step's limit is min(allowed, max(16 kB, 2 x the transaction's bytes)),
the transaction's bytes being the stream's growth since the last external
transaction (its record, the writes of dirty nodes, reclaim's records).
Six lines in `transactionCompleted`. C names what it lacks: an argument
for the steps that the allowance holds back.

### 5.2 Results

B's probe (`out/quota-*.txt`) and C's probes (table 3):

| Run | Iterations done | Last length, L0     | Cuts | now - f, ms | Stream, MB | Kept, MB |
|---|---|---|---|---|---|---|
| A   | 10              | 439, L0 909,700     | 9    | 4,249       | 3,030.3    | 1,981.5  |
| B   | 15              | 2,089, L0 1,068,820 | 14   | 12,319      | 3,793.6    | 2,052.6  |
| C   | 10              | 702, L0 77,046      | 9    | 6,939       | 298.4      | 202.9    |

* The quota ends every probe. It does more than restore today's pace: a
  step scans up to twice the transaction's bytes, so in a growing
  database its iterations are shorter than today's (run A, last one: 439
  transactions against L0 / r = 12,600) and reclaim spends its whole
  allowance: the stream grows 30 to 35 % more than main's (A 3,030
  against 2,252 MB; B 3,794 against 2,918 MB) and keeps less (B 2,053
  against 2,853 MB). Its steps walked 685 to 2,455 KVs on average in
  run A's iterations, growing with the database.
* T1 (`t1/quota-*`): M8 101 at 1M ascending (C6: 1 over, a_n 17) and 100
  at 100,000 (C6: 1 over, a_n 16); M11 103 at 1M descending (C9: 3 over);
  1M random passes; 1,000 as P8. T4 as P8 exactly (its transactions are
  small, so the quota stays 16 kB).

### 5.3 Judgement

| Property                    | Fix                        | Quota                      |
|---|---|---|
| B's probe, runs A to C      | ends; today's pace or less | ends; faster than today    |
| C's queue, ordered, "/z"    | 5 and 9 transactions       | 15 and 28                  |
| Bound on an iteration       | KVs live at tStart / 16 kB | needs appends <= quota     |
| Depends on the allowance    | as today                   | yes, unargued (C)          |
| Bytes written, B's runs     | as main                    | 30 to 35 % more            |
| One step's walk, KVs        | at most r + the user's     | 2 x the transaction's bytes |
| T1, over twin + a_n         | C9 +6 at 1M ascending      | C6 +1 twice, C9 +3         |
| T4                          | hashed: 25 % fewer steps   | as P8                      |
| Production lines changed    | 3                          | 6                          |

* **Both end B's and C's probes; neither keeps P8's T1 result exactly.**
  Each moves the end state of some T1 rows by a few nodes, over a_n: the
  fix in one row (C9 at 1M ascending, 106 against 100), the quota in
  three (by 1, 1 and 3). P8 itself fails C9 at 1,000 and 100,000. These
  are phase effects of the history before the drive, not of the scan
  during it; P8's Q4 asks how C9 should be measured.
* **The fix is the smaller change of behaviour.** It keeps today's pace
  and write volume and adds a bound by counting: the KVs the iteration
  must cover. The quota changes the pace for every workload with large
  transactions; that may be wanted (it keeps up with growth better:
  now - f 12 s against main's 66 s in run B), but it is a change of
  reclaim's write cost, a performance question (performance.sh), and it
  needs C's missing argument. It could be added later on top of the fix.
* **Recommendation**: the fix in P8 for 2026.4 (with its unit test and
  the probes of B and C as tests), and the quota as a separate question
  for Frans: should reclaim's pace follow the growth of the live set
  (023-02, R6), and at what write cost.


## 6. Gates and state

* Branch `023-v8-fix` in /Users/f/fl/bench/2026-11-10/v8/clone, from
  `f56dca40`; worktree `wt-fix`. Changes: the stop condition in
  `Reclaim.step` (an `if` around one line, and comments), the unit test
  `testRandomPutsAheadDoNotSlowTheScan`, and the fixture
  `testPretruncate`.
* **The fixture.** The first `before-commit.sh` failed one unit test,
  `Reclaim.Tester.testPretruncate`: one key overwritten 40 times with
  100 kB values. With the fix its iterations end in one step (the
  overwritten key no longer counts), so the test's last transaction
  decided a newer cut, which replaced the pending, durable one
  (`pendingCut` is overwritten at line 921) before it was made, and the
  test ended before the next transaction. Up to four more transactions,
  each followed by a sync, make the cut (the first one does). Not a fault
  of the fix; but a pending cut that is durable is dropped when a newer
  one is decided first. That is today's code: if each new decision
  came before the pending cut is durable, no cut would be made. A
  question beside this one (Q2).
* `before-commit.sh` at the fixture's change: BEFORE COMMIT OK (258 s;
  unit 1,629, f 86, demos 14). The probes and T1 ran on the build before
  the fixture's change; the production code is the same.
* Committed in the clone only: `0f4571fc` on `023-v8-fix`, and C's quota
  as `2055236f` on `023-v8-quota` (for comparison, not gated).
* Not run: level scripts, performance.sh, conformance.


## 7. Questions for Frans

* **Q1.** The fix (only the KVs stored before pStart count toward a
  step's size) in P8 for 2026.4? Recommended: yes.
* **Q2.** `pretruncateIfPossible` replaces a pending cut that is already
  durable by a newer one before making it (section 6). Make the durable
  one first (one call of `cutIfDurable()` before the replacement)?
  Recommended: yes, in its own change with its own test.
* **Q3.** Should reclaim's pace follow the transaction's size or the live
  set's growth (C's quota), at 30 to 35 % more bytes written in B's
  runs? Today's pace, 16 kB of KVs a transaction, makes now - f grow
  with the live set in a growing database (2.4).
