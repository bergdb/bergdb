# 023-05 P8. Each reclaim step scans at its own time

Created 2026-11-10 by Frans Lundberg. Status: open.

Frans's Z14 (023-06, 13:42): each reclaim step scans at its own time, not
at its iteration's start time tStart, after a probe. This prototype makes
the probe first (section 2), then the change on P4's branch, the base
for 2026.4 (023-06, section 12.1 and Z12).


## 1. Summary

* **The probe holds** (section 2, written before the code): with each step
  scanning at its own time, every value and node that a lookup from tEnd
  on can reach is still at pCut or later, or dirty, after the iteration.
  The values' argument is short: a value stored before pCut that is live
  at a time t >= tEnd was live, with that value, at every time from tStart
  to t, so the step whose range holds its key finds it. The touch is
  unchanged. Nothing of the scan is stored or rerun, and the model has no
  scan: C-CUT checks the cut itself on every trace.
* **One addition**: an end key E, the last key live at tStart, kept in the
  row. Without it the iteration need never end: ordered puts after the
  scan faster than a step scans keep it busy forever (a unit test shows
  it, section 3.3).
* **T1 at N = 1M with the fixed drive of 4,000 passes** C1 to C3 and C5 to
  C10 against its twin, in ascending, descending and random order of the
  deletes (P4: M1 287 MB, 298 MB and 1,430 MB). At 1,000 and 100,000, C9
  (resident objects after the probe) is 15 and 22 over the twin, against
  P4's 17 and 14: a longer startup section when the drive ends, whose
  rerun leaves replaced leaves resident; not the scan's doing (5.1).
* **The iteration in progress at a mass delete** ends with the deletes:
  0 steps after them, against P4's 2,995 at 1M (ascending; 4,000 and not
  done for descending), and 0 loads after them, against P4's 175,860 with
  a 20 MB budget.
* **T4** (ordered queue, 100,000 and 1M transactions; hashed, 100,000):
  the same stream, kept bytes, records and D as P4; 11 to 12 % fewer steps
  in the ordered queue, the same in the hashed one.
* **A cost**: during an ascending mass delete the steps work just ahead of
  the deletes and write 24 % more bytes there (1M: 85.0 MB against 68.4 MB),
  while the drive after writes 61 % less (5.5 MB against 13.9 MB);
  within the internal fraction, as every step (5.4).
* **Gates**: before-commit, level1, level3 full and level4 quick OK; the
  conformance with reclaim 25 of 25 traces (C-CUT 0 of 303 cuts failing)
  and 14 traces of P8's own (0 of 163); ReclaimStress and RestartInvariance
  with reclaim OK. One fixture changed (3.2).


## 2. The probe: the cut's guarantee with the scan at the step's time

Written before the code was changed.

### 2.1 Reclaim today

From `Reclaim` (class comment, `transactionCompleted`, `step`) and
docs/levels.md, section 6:

* An iteration starts at an external transaction t: pStart is the stream
  length after t's record (`t.nextPos`), tStart is t's time, and pCut is
  the pStart of the iteration before. Every record before pStart is of a
  transaction at or before tStart, so a value stored before pCut was
  written at a time w <= tStart.
* A step, at a later external transaction, scans the KVs live at tStart
  after the row's lastKey, about 16 KB of them (`GetMany` at
  `it.tStart`). It then reads each scanned key at the latest time (the
  step's lookup time, `stepLookupTime`), and puts again each value that is
  still live and stored before pCut (a rewrite, with `keyRead` and the
  read time). In the same internal transaction it touches the key range
  (lastKey, L] at the transaction's time (`Trans.touch`, `Db.touchRange`:
  every index node reachable then for those keys gets dirty), where L is
  the last key of the scan; the last step, whose scan reached the end,
  touches (lastKey, end of the key space). The row, with lastKey = L, is
  the value of `/#i/dreclaim/-current.txt` in the same transaction.
* When the scan reaches the end, the iteration is done; tEnd and pEnd are
  the time and position of the last step. The class comment's guarantee:
  every node and value reachable at times from tEnd on is then stored at
  pCut or later (index nodes at pStart or later), or is dirty and will be
  written there. The cut at pCut waits for R, pEnd, pSafe and the meta
  block; then the first available lookup time becomes tEnd.

### 2.2 The change

A step scans the KVs live at its own time, the latest state, the same
snapshot its reads use (the step's lookup time s, the time of the last
transaction committed before the step; under the write lock nothing
commits between the scan and the step's transaction). The rest is as
today: the reads at s, the rewrite of each value stored before pCut, the
touch of (lastKey, L] at the step's transaction time, the row.

One addition, for liveness only (2.8): the iteration has an end key E, the
last key live at tStart, found when the iteration starts (a backward scan
of one KV at tStart) and kept in the row. A step's scan covers the keys
after lastKey up to E; the iteration is done when the scan passes E or
reaches the end, and the last step touches (lastKey, end of the key space)
as today.

### 2.3 Values

Claim: after the iteration, no lookup at a time t >= tEnd reads a value
stored before pCut.

* A lookup at t reads the value of a key k live at t: the data node named
  by k's last entry at or before t. With the unlink (P1 to P4) and without
  it alike, no other value is read at t (`ReadsAt`, `ReadsPhys` in
  SIS/Reclaim.lean: the latest versions of the nodes reachable at t and
  their live children at t).
* Suppose k's value at t is a node v stored before pCut. Then v was
  written at w <= tStart (2.1). No put or delete of k came in (w, t]: any
  such write would give k a later entry at or before t, and a put writes a
  new value node (reclaim's rewrite too); a time split of k's key node
  copies the entry with the same value pointer. So k was live, with value
  v, at every time in [w, t], which contains [tStart, tEnd].
* k <= E, since k was live at tStart and E is the last key live then.
* The steps' ranges (lastKey_i-1, L_i] are consecutive, start at the first
  key (lastKey = null) and end at E or beyond (the scan of the last step
  passed E or reached the end). So k is in the range of exactly one step
  i, with scan time s_i, tStart <= s_i < tt_i <= tEnd.
* The scan of step i returns every key live at s_i in its range, in key
  order, up to L_i (it stops only after adding a KV, or at a key past E,
  or at the end; the value limit of 015-50 moves L_i back to the key
  before, and the next step starts there). k is live at s_i, so the scan
  returns k, the read at s_i gives v, stored before pCut, and the step
  rewrites k at tt_i <= tEnd <= t.
* Then k's last entry at or before t is the rewrite or later, not v.
  Contradiction: no value stored before pCut is read at t >= tEnd.

With the scan at tStart, the same steps give the same conclusion; the
scan at s_i only drops the keys that are not live at s_i (deleted since
tStart: no rewrite needed, the read gave null) and adds the keys put since
tStart (their values are at pStart or later: no rewrite). What the step
rewrites is the same set of keys as today's scan at tStart would have
given it for the same range: the keys live at both tStart and s_i whose
value is stored before pCut.

### 2.4 Index nodes

The touch is unchanged: at its step's transaction time, every index node
reachable then for the keys of the step's range gets dirty, and a dirty
node is written again at pStart or later (pEnd, pSafe). Only the ranges'
boundaries L_i change: keys live at s_i instead of keys live at tStart.
The touch's part of the guarantee does not depend on where the boundaries
are, only on the ranges being consecutive and covering the whole key
space, each touched at a time in [tStart, tEnd]:

* A node x whose latest version is stored before pStart and that is
  reachable at t >= tEnd was made before tStart (a node made later is
  written at pStart or later, or dirty). A node is reachable over one
  interval of times, from its making until the transaction that replaces
  it or leaves it out (A5, 023-06, 13.1: I3; a left-out node is reachable
  only before the delete's time). So x is reachable at every time in
  [tStart, t].
* The keys routed through x at tStart form a non-empty range; while x is
  reachable that range only grows (a sibling left out gives its keys to a
  neighbour, LE-b gives the leftmost child's keys to the next live child,
  root collapse gives the child every key; a split replaces the node it
  splits). Take a key k routed through x at tStart; k is in the range of
  one step i, and at tt_i k is still routed through x, so step i's touch,
  which visits every node that a scan of its range at tt_i enters,
  reaches x and makes it dirty. Contradiction with x's latest version
  being before pStart.

That is today's argument (023-06, 13.2, "Reclaim's step and cut"), and it
holds for any boundaries. The last step still touches to the end of the
key space, so the keys put after E since tStart are covered as today.

### 2.5 Lookups at every available time

No lookup path changes. A rewrite puts k's value as read at s_i, so
lookups at every time give the same values with or without the step, as
today. The first available lookup time is still tEnd of the cut
iteration, and the cut still waits until tEnd is older than R: what
changes is how early an iteration ends after a mass delete, not the rule
that decides the cut.

### 2.6 Determinism and the rerun

* What a step's record stores: the rewrites as puts (key and value), the
  row as the value of `/#i/dreclaim/-current.txt` (now with E), and the
  got-dirty ids of the nodes the touch and the puts made dirty. Neither
  the scan, nor its time, nor the touch's range is stored
  (`Trans.touch`: "Not stored: startup rebuilds D from the stored
  got-dirty ids").
* What a start redoes: the records after the startup pos, by the same
  rules (the puts, P4's deletes), and D from the got-dirty ids. It never
  reruns a scan or a touch, so the scan's time does not enter the rerun.
* What decides the next step after a start: the row (lastKey, E, pCut,
  rewritten; `initFromDb` reads the table and the current row), the
  stream's length (the allowance) and the state at the latest time, all
  functions of the stream. Today's step also used the state at the latest
  time for its reads, and the state at tStart for its scan; now both are
  the latest state. E is computed once, at the iteration's start, from
  the state at tStart, and stored with the table in the same call. So a
  run with restarts writes the same records as one without
  (INV-RESTART), as before. The step's reserve counts index nodes by id
  (`MaintenanceFollower.indexNodes`), the same whatever is resident.

### 2.7 The Lean model and the conformance checks

The model has no scan. Java's steps reach the trace checker as
transactions: their puts, and the touch as TOUCH lines. C-A checks
TouchOK (`StepOK.touchIndex`, `touchReach`, `touchUp`,
SIS/Assumptions.lean: touched nodes are index nodes reachable at the
time before the transaction, closed upward); C-S runs the model's step on
Java's state and compares the record and D; C-CUT checks `CutOK`
(SIS/Reclaim.lean) at every cut Java decides, in the model's state:
every version that a read from the first available time on may follow,
values included, is at the cut or later, and the conditions on D. None
of these refers to tStart or to how Java chose the step's keys, so the
change needs no change of the model, and C-CUT checks the cut's safety
directly on every trace with a cut. That Java's scheme gives safe cuts
(T-SCHEME) stays checked, not proved (sis-model.md, 15.3).

### 2.8 Liveness: the end key E

Without E the scan at the step's time sees the keys put since tStart
after it. A step scans at most 16 KB of KVs (`MAX_STEP_SIZE`), at most
one step an external transaction; the allowance charges the bytes
rewritten and made dirty, not the bytes scanned. A user who puts more
than about 16 KB of new keys after the scan's position every transaction
(ordered appends: a log, a time series, T4's ordered queue in big
batches) keeps the scan from ever reaching the end: the iteration never
ends, and no cut is ever made. Today's scan at tStart has a fixed set of
keys and always ends. With E the steps cover at most the keys up to E,
and the keys put after E since tStart are reached by the last step's
touch only, as today. By 2.3, E loses nothing: every key whose value
needs a rewrite was live at tStart, so it is at most E.

What E does not bound: keys put since tStart before E (random inserts).
The scan at the step's time covers them, today's does not; an iteration
can take longer than today's while the user inserts faster than the scan
in the range still ahead of it (a limit, section 7).

### 2.9 Verdict

The guarantee holds: values by 2.3, index nodes by 2.4 (unchanged), the
lookups at every available time by 2.5, the rerun by 2.6. The change is a
change of what Java chooses to rewrite and where the ranges end, inside
what the model already checks (2.7). So the code follows; the fallback
(023-03's drive counted from the end of the iteration in progress) is not
needed.


## 3. The mechanism as built

Branch `023-p8-steptime`, from P4's `0e66d1c9`; the change is commit
`edb8e14d`, all in `Reclaim`.

### 3.1 What, when, by whom

* **The end key.** When an external transaction t starts an iteration
  (`Reclaim.transactionCompleted`, under the write lock, after t's
  `dbClock.transactionEnd()`), reclaim reads the last key live at t's time
  (`lastKeyAt`: a backward `GetMany` of one KV at `t.tt`, with the
  maintenance follower, which swizzles nothing; an assert checks that the
  read's actual lookup time is `t.tt`). It is the row's `endKey`, or
  `NO_KEY` (an empty array) if no key was live. The table that the same
  call stores holds it, and every step's row after it.
* **The scan.** A step (`Reclaim.step`, at a later external transaction,
  under the write lock) scans with `lookupTime = Long.MAX_VALUE`: the
  state after the last committed transaction, its own time. Its stop
  condition stops at the first key after `endKey` (`IterationInfo.pastEnd`)
  and marks the iteration's end there, as the end of the data did; the
  size and reserve limits are as before.
* **The reads.** Each scanned key is read at the scan's actual lookup time
  (`scanTime`), which is the time the first read used before (it read at
  `Long.MAX_VALUE`); `readTime` and `keyRead` as before.
* **The rest is unchanged**: the rewrite of each live value stored before
  pCut, the value limit of 015-50, the touch of (lastKey, L] at the step's
  transaction time (to the end of the key space in the last step), the
  row, tEnd, pEnd, pSafe and the cut.
* **The row's text** gets a line `endKey=` with the key's segments as
  lastKey has them, or `none`; a row without the line (none is written in
  format 6) reads as no bound (`endKey` null): the scan is still sound,
  only not bounded.

### 3.2 Other changes

* `Reclaim.Stats.Iteration.scanNodes`: the index nodes the steps' scans
  follow, summed (commit `0ec8498e`). CleanupRule prints every
  iteration's steps, scanned KVs, scan nodes and loads, and the iteration
  in progress at the end of T1's deletes (`0ec8498e`, `f56dca40`).
* docs/levels.md, section 6, in the clone: the step scans at its own time,
  up to the last key live at tStart.
* `testUserTransactionLeavesTimesForReclaim` arms its step with a margin
  of 100 bytes for the record of its put of "/last", not 150: with the new
  history the put came 8 bytes short of a step (allowed 9,992 against
  10,000). The record takes about 115 bytes. A fixture of the history,
  not a fault; Frans's approval asked (section 9, Q3).

### 3.3 Unit tests (commit `1d6494f0`)

* `testStepScansAtItsOwnTime`: 2,000 keys, an iteration starts, all but
  the last ten are deleted in one transaction; the iteration then scans at
  most 20 KVs (the ten, "/a" and reclaim's keys; a scan at tStart would
  pass the 2,000), and the ten are rewritten at pCut or later.
* `testEndKeyBoundsTheScan`: 500 keys, an iteration starts, then every
  transaction puts 200 new keys after them (43 kB by the scan's measure);
  the iteration must end within 300 transactions. Run without the end key
  (`pastEnd` always false, a probe build), it fails: the iteration does
  not end.
* `testSerializeEndKey`: the row's end key stored and read back, and
  `pastEnd` for a key, `NO_KEY` and null.


## 4. Gates

In the clone, at `f56dca40` (the change is `edb8e14d`; the commits after
it are tests and CleanupRule). Logs in /Users/f/fl/bench/2026-11-10/p8/runs/.

| Gate | Result |
|---|---|
| `before-commit.sh`, `edb8e14d`          | FAILED: one unit test, the fixture of 3.2         |
| `before-commit.sh`, `f56dca40`          | BEFORE COMMIT OK (267 s)                          |
| `level1.sh`                             | LEVEL 1 OK (169 s); MEM 130, SS 1.51              |
| `level3.sh`, full                       | LEVEL 3 OK (569 s)                                |
| ReclaimStress (level3, step 2)          | 4 x 50 rounds, 0 failures, every round with a cut |
| RestartInvariance with reclaim (step 3) | 4 configurations: stream identical, same cut      |
| LoadTest with reclaim (step 6)          | 6 restarts with a full check after a cut          |
| Conformance with reclaim (step 8)       | 25 of 25 TRACECHECK OK; C-CUT 0 of 303 cuts fail  |
| P8's own traces (below)                 | 14 of 14 TRACECHECK OK; C-CUT 0 of 163 cuts fail  |
| `level4.sh quick`                       | LEVEL 4 OK (226 s); conformance evict 15 of 15    |

The conformance's traces, C-S included, are the model's step on Java's
records: no difference from the change, as 2.7 expects (the model has no
scan). P8's own traces: TraceExport with reclaim, restarts every ten
transactions, and workloads for the change: heavy deletes (60 % of the
KVs, 200 keys, ops 8), sorted bulk puts of new keys (`bulk`, many after
the iteration's end key), long keys, and run E with random eviction;
each trace checked by the Lean checker (C-A with TouchOK, C-S, C-CUT,
C-P and C-H for run E): 5 traces of 800 transactions with heavy deletes
(21 to 26 cuts each), 3 with bulk puts, 3 with long keys, 3 with run E
(C-P and C-H: 0 failing transactions). Script: p8/runs/p8traces.sh.
StreamDigest was not run: its digests change with format 6 already (P4,
R27).


## 5. Measurements

CleanupRule (023-03's T1 and T4), counts, on F53 shared with other
agents' runs. "P4" is the build at `0ec8498e` (P4's head with the
statistics), "P8" the build at `edb8e14d` with CleanupRule of `f56dca40`.
Logs: /Users/f/fl/bench/2026-11-10/p8/runs/ (`b-*`, `sb-*` P4; `a-*`,
`sa-*` P8).

### 5.1 T1, the fixed drive of 4,000

Shape "after", R = 1 s, batches of 100, values of 100 bytes. Each build
has its own twin, since reclaim's records differ; P4's twin: M1 2,132,312,
M3 1,039 ms, M8 79, M9 2,840, M11 85; P8's twin: 2,108,432, 1,040 ms, 83,
2,504, 83. W (the twin's swing of M1 in the window) is 365,008 bytes for
P8's twin.

| N, order | Build | M1, most in window | M3, ms | M8 | M9 | M11 | M12 |
|---|---|---|---|---|---|---|---|
| 1,000          | P4 | 2,142,984     | 1,221  | 90  | 2,856  | 102 | 5 |
| 1,000          | P8 | 2,118,280     | 1,224  | 85  | 3,912  | 98  | 5 |
| 100,000        | P4 | 2,187,224     | 1,144  | 107 | 3,488  | 99  | 5 |
| 100,000        | P8 | 2,119,792     | 1,219  | 91  | 2,840  | 105 | 5 |
| 1,000,000      | P4 | 287,410,920   | 1,004  | 204 | 16,600 | 187 | 7 |
| 1,000,000      | P8 | 2,109,160     | 1,218  | 90  | 3,168  | 91  | 6 |
| 1M, descending | P4 | 297,875,416   | 12,956 | 270 | 56,296 | 184 | 4 |
| 1M, descending | P8 | 2,138,472     | 1,168  | 78  | 3,104  | 86  | 5 |
| 1M, random     | P4 | 1,430,330,752 | 1,010  | 174 | 7,768  | 161 | 7 |
| 1M, random     | P8 | 2,127,032     | 1,137  | 84  | 3,352  | 91  | 3 |

M4 (reachable key nodes) is 6 and M6 (get) 1 in every row, as the twin's;
M10 (the last iteration's touch) is 7 in P8's rows, as the twin's.

P8 against its twin, 023-03's criteria with the bounded allowance
(a_n = 10 + h_fill: 14, 16 and 17 at 1,000, 100,000 and 1M):

* At 1M, in all three orders: C1 (M1 the twin's + 30,040 bytes at most,
  against W = 365,008), C2 (+178 ms, R / 4 = 250 ms), C3, C5, C6 (+7 at most), C7 (+848
  bytes at most), C8, C9 (+8), C10 (+4): T1 passes at 1M with the fixed
  drive (C11 is not in the prototype). P4 fails C1, C6, C7 and C9 there,
  and C2 too when descending (no cut in the whole drive).
* At 1,000 and 100,000: C1 to C8 and C10 pass; C9 is +15 (a_n 14) and +22
  (a_n 16). P4's own runs of the same commands give +17 and +14. M11 is
  the objects resident after the start and the probe. At 100,000 P8's D
  after the start is the twin's (77), but 28 objects outside D are
  resident against the twin's 6 (P4: D 90, 9 outside it). It is stable:
  with the drive shifted by 1 to 8 transactions (pre=K) P8 gives 105 or
  106 and P4 99 every time. A probe of the node table after the start
  (a scratch copy of CleanupRule): the 22 extra are clean key nodes of 29
  klongs, the replaced versions of "/a.txt"'s leaf that the start's rerun
  of the startup section makes again; P8's section is 126,160 bytes at the
  end of the drive, the twin's 88,800 (sd = 100,000), so it reruns more
  records. Where the startup pos stands when the drive ends is a phase of
  the writer's writes of dirty nodes; D holds 58 top nodes against the
  twin's 51 (the window of Z13, 023-06). Not the scan's doing (Q4).

### 5.2 The iteration in progress at the mass delete

The iteration running when the deletes end, from CleanupRule's line at
the end of the deletes and its totals at the end of the drive. In P8's
runs the last iteration is already done then; the row is that one. Loads with
a budget of 20 MB (evict=20000000); without a budget P4 keeps every
object and loads none.

| Run | Build | Steps | After the deletes | KVs scanned | Scan nodes | Loads, 20 MB |
|---|---|---|---|---|---|---|
| 100,000        | P4 | 309    | 78              | 23,104  | 3,912   | 3       |
| 100,000        | P8 | 382    | 0               | 28,571  | 4,274   | 9,155   |
| 1M             | P4 | 11,943 | 2,995           | 895,604 | 174,995 | 704,774 |
| 1M             | P8 | 7,323  | 0               | 535,633 | 92,276  | 577,788 |
| 1M, descending | P4 | 8,924  | 4,000, not done | 640,613 | 142,156 | -       |
| 1M, descending | P8 | 109    | 0               | 7,904   | 1,262   | -       |
| 1M, random     | P4 | 11,942 | 2,989           | 895,604 | 183,096 | -       |
| 1M, random     | P8 | 109    | 0               | 7,925   | 13,209  | -       |

* After the deletes: P4's iteration runs on through the drive, one step a
  transaction, scanning the keys that were live at its tStart (at 1M,
  224,613 KVs, 59,333 scan nodes and 175,860 loads after the deletes);
  P8's ends with the last delete, and the next iteration, at the first
  drive transaction, scans the 4 KVs left.
* During the deletes both scan live keys. In ascending order P8's steps
  run just ahead of the deletes, one a transaction (the deletes give a
  large allowance), and read keys that the next transaction deletes; so
  the loads during the deletes stay (P4 528,914 by their end, P8 577,788,
  mostly values: the scan reads each KV's value). In descending and random
  order P8's iterations end and start again during the deletes, as the
  live set shrinks.
* P6's 190,272 loads at 100,000 (P6, 4.3) came from the scan at tStart
  reading leaves that the deletes unlinked and P6's queue evicted. P8 does
  not read unlinked leaves; not measured on P6's branch.

### 5.3 T4, the queue

L = 1,000, one put and one delete a transaction, values of 100 bytes.

| Queue, M | Build | Iterations | Steps | KVs scanned | Kept, most | D, most | Record, most |
|---|---|---|---|---|---|---|---|
| ordered, 100,000 | P4 | 168   | 3,732  | 168,540   | 1,660,336 | 162 | 32,392 |
| ordered, 100,000 | P8 | 167   | 3,276  | 146,356   | 1,606,232 | 139 | 34,136 |
| ordered, 1M      | P4 | 1,698 | 37,772 | 1,704,660 | 1,708,344 | 157 | 32,392 |
| ordered, 1M      | P8 | 1,695 | 33,593 | 1,499,381 | 1,597,608 | 176 | 34,136 |
| hashed, 100,000  | P4 | 214   | 4,637  | 214,391   | 3,834,096 | 796 | 25,048 |
| hashed, 100,000  | P8 | 214   | 4,644  | 214,640   | 3,919,648 | 693 | 26,520 |

The stream written is the same within 1 % (ordered 1M: 596.4 MB against
595.7 MB), reach 117 and 2,134 and the queue's head 4 and 5 in both,
the most lag 1,574 ms against 1,535 ms (ordered 1M). The scan at the step's
time skips the keys deleted since tStart (11 to 12 % fewer steps when
ordered); with hashed keys the puts land before E and the deletes behind
the scan about equally, so the steps are the same.

### 5.4 Bytes written by phase (T1, P4 against P8)

| N, order | Deletes, P4 | Deletes, P8 | Drive, P4 | Drive, P8 |
|---|---|---|---|---|
| 100,000        | 6,155,440     | 7,907,104     | 5,717,688  | 5,540,528 |
| 1M             | 68,417,392    | 85,010,544    | 13,912,464 | 5,474,632 |
| 1M, descending | 79,824,168    | 84,782,448    | 12,962,160 | 5,353,184 |
| 1M, random     | 1,213,934,080 | 1,282,350,896 | 11,324,320 | 5,467,336 |

In ascending order P8's steps touch the leaves just ahead of the deletes
and rewrite their old values (the iteration at 1M: 46,426 nodes made
dirty and 26,677 values rewritten, against P4's 2,784 and 0); the next
transaction deletes them. That is 24 % more in the deletes at 1M, 28 % at
100,000, 6 % descending and random; the drive after writes 61 % less at
1M. Every step is within the internal fraction (a quarter of the growth),
so this is the allowance spent earlier, not a new kind of cost.


## 6. Requirements and tests met

023-02's requirements as P4 meets them (P4, section 4), with these
changes:

* R5, R6 (the stream bounded by the live data): the iteration in progress
  at a mass delete now ends with it, so the cuts resume one retention after
  the deletes, whatever N; T1's fixed drive suffices at 1M.
* R1, R16 (lookups at every available time, readers): unchanged; no lookup
  path changes (2.5), and T6 (CleanupRule's model checks) passes in every
  run.
* 023-03, T1: passes at 1M in three orders; C9 at 1,000 and 100,000 is
  over by 1 and 6 (5.1). T4: as P4 (5.3). T8 (determinism):
  RestartInvariance with reclaim in level3 (section 4).


## 7. Faults and limits

* **Random puts before E** are scanned by the steps (2.8). An iteration
  takes longer than today's only while the user puts, before E and ahead
  of the scan, more than a step scans; in a growing database with uniform
  puts at r times the scan's rate, it can end only after the live set has
  grown by about e^r. Not seen in T4 hashed (steps equal to P4's). Bulk
  loads in key order after E are not scanned.
* **Work ahead of an ascending mass delete** (5.4): rewrites and touches of
  keys deleted a transaction later.
* **The loads during the deletes** with a small budget remain (5.2): the
  scan reads each live KV's value, also when its position is at pCut or
  later and no rewrite is needed.
* **C9 at 1,000 and 100,000** (5.1): 15 and 22 over the twin, stable
  under phase shifts of the drive: a longer startup section at the end of
  the drive (126 kB against 89 kB) whose rerun leaves replaced leaves
  resident.
* The fault found by the gates: only the fixture of 3.2.


## 8. Left for a production version

* Read a value only when its position is before pCut: `Kvt.spos` gives
  the value node's position, so the scan could skip the values at pCut or
  later and the second read per key (a keys-only scan); this would remove
  most of 5.2's loads and halve the step's reads.
* Keep E or drop it, as Frans chooses (Q1). With E, the class comment and
  docs/levels.md as in the clone.
* The Lean model needs nothing (2.7); T-SCHEME stays checked, not proved.
  If Frans wants the values' argument of 2.3 proved, it is a lemma about
  the model's histories: a key whose entry at t names a data node stored
  before c has no entry in (w, t].
* The row's text: `endKey` is a new line; format 6 refuses older databases
  anyway (F9 (a)).


## 9. Questions for Frans

* **Q1. The end key E.** Keep it (recommended: without it, ordered puts
  faster than the scan keep an iteration from ever ending, a liveness
  fault), or scan without a bound?
* **Q2. Work during a mass delete** (5.4): accept that the steps spend
  their allowance during the deletes (24 % more bytes there, 61 % less
  after), or make the step skip ranges that the user's last transaction
  deleted? Recommended: accept; it is within the internal fraction.
* **Q3. The fixture** `testUserTransactionLeavesTimesForReclaim`: the
  margin 100 for 150 (3.2). Recommended: yes.
* **Q4. C9 at 100,000** (5.1): the start reruns a longer startup section
  (126 kB against the twin's 89 kB, with sd = 100 kB) and keeps 22 replaced
  leaves resident. Should M11 be measured with the startup pos at a fixed
  phase (after a sync that writes D), or C9 get a tolerance of the
  section's nodes? Recommended: decide with Z13's fix, which changes D and
  the section.


## 10. State

* 14:26. Branch `023-p8-steptime` in
  /Users/f/fl/bench/2026-11-10/p8/clone, from P4's `0e66d1c9`; head
  `f56dca40`. Commits: `0ec8498e` (statistics), `edb8e14d` (the change),
  `1d6494f0` (unit tests, the fixture), `f56dca40` (CleanupRule).
* Runs: /Users/f/fl/bench/2026-11-10/p8/runs/ (`b-`, `sb-`, `phb-` P4;
  `a-`, `sa-`, `pha-` P8), builds copied to p8/before and p8/after; P8's
  own traces in p8/runs/traces/ (summary.txt).
* Gates done at `f56dca40` (p8/runs/gates.log): all OK (section 4).
* Nothing running. The report is complete; open: Frans's Q1 to Q4.
