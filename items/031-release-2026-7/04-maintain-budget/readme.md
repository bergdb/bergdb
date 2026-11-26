# 031-04. maintain(budget): a study

Created 2026-11-26 by Frans Lundberg. Status: open.

A study of a simpler `maintain()`: a call with a cost budget, and
reclaim passes that end by construction, so that BergDB no longer
decides by itself when its maintenance is done. Frans decided
(2026-11-26) to study this direction as a possible simple solution
before any decision on `maintain()`'s design: nothing of it is decided
for implementation. The study comes first; Frans decides the next steps
from it.

What was known: 031-03 (the witness, O-1, and Codex's review of it,
section 14), 031-01, 028-53, 028-54, 027-13 (reclaim, section 1.10 for
`maintain()`), 010-01 (P1, P2).


## 1. Why

`maintain()`'s difficulty is that BergDB decides, without being told,
when there is work and when it is done. That decision gave `main` its
two stretches and the 400 kB threshold (MIN_RELEASE), gave 031-03 its
drain for an emptied database, whose end is argued but not proved
(Codex's finding 1: with a step reserve of 1 the drain repeats), and is
the cause of RB-007. The direction below takes the decision away: the
application grants a budget, and a pass that a call begins ends by its
own construction.


## 2. The direction studied

As discussed with Frans on 2026-11-26; to be designed, built as a
prototype and measured, not decided.

* **The idle-time hook.** `maintain()` is the application's general
  call for the database's maintenance while it is idle: reclaim, the
  take (index nodes of the startup section), and later possibly the
  cache (dropping cold nodes) and other cleanup; not only reclaim.
* **A cost budget.** `void maintain(int budget)`. The budget is an
  indication of the work allowed in the call, in cost units; one unit
  is about the work of writing 1 kB to the stream. The value is clamped
  to a range, about 100 to 100,000 (100 kB to 100 MB). The database may
  use less than the budget, or none, depending on its state. The Pub
  API defines it loosely on purpose, so that the implementation may
  change without the API changing.
* **No return value.** A returned cost or boolean invites a loop that
  waits for it to drop, which a later release could break; users
  observe the effect on the database instead (the stream kept, below).
* **The old `maintain()` removed** (the Pub API is not yet kept
  constant between releases).
* **The cost model is internal** and may change: bytes read (perhaps
  charged less than written), bytes written to the stream, and other
  counts. What decides what is written is charged only by deterministic
  counts (bytes read as the logic reads them, cache hit or not; bytes
  written; KVs scanned; nodes visited), so that the stream's bytes do
  not depend on timing (P2). Charges of time or CPU only for work that
  writes nothing.
* **One iteration at a time.** A call continues an iteration in
  progress, also one that a commit began, by its steps within the
  budget; it begins none while an iteration runs or a done one waits
  for its cut.
* **A pass that a call begins cuts at its own start** (pCut := pStart,
  as the first iteration does today): one pass rewrites every live value
  stored before it, and its cut drops the stream before it. A commit's
  iterations keep today's pCut, the pStart of the iteration before.
* **When a call begins a pass:** no iteration runs or waits for its
  cut, and the stream kept still holds a record of the application's:
  w >= fp, with w read off the stream as 031-03's R1 to R3 do (no store
  of its own, no recovery case). After such a pass, with the
  application idle, w < fp and the calls go quiet; after a commit's
  iteration, at most one more pass. No drain, no MIN_RELEASE.
* **The user's model.** A full pass takes at most about the stream kept
  divided by the budget's bytes in calls, since a pass scans every live
  KV once and all live data lies in the stream kept; the space comes
  back once R has passed since the pass ended. Calls after that do
  little until the application writes again.
* **The stream kept** (L - fp) in the Pub API, as a getter: exact and
  free. With the live bytes, summed by an iteration's scan, kept / live
  is the space amplification; history (states the retain duration keeps
  readable) is not waste. In a database not written to for longer than
  R, kept - live is exactly the stream that reclaim can give back.


## 3. The study

By one agent of lead-1126 (Opus, xhigh), in a clone of `main`; Codex
reviews the result before Frans reads it. Its answers go in the
sections it adds here; a prototype on a branch, not on `main`.

1. **The design text**: each rule with what, when, by whom and how it is
   checked; the cost model and its determinism rule; what stays of
   `main`'s `maintain()` (the take, the filler, the sync, the cut).
2. **A prototype** on `main`, with the old `maintain()` removed and
   `maintain(int budget)` and the stream kept's getter added.
3. **Measurements**: RB-007's case (031-03's `HoleProbe`) and an
   emptied database; a database with live values not written to (quiet
   when done); Codex's case of 031-03 (step reserve 1, 150 keys of 111
   bytes at node size 8), which must end; the calls of a full pass
   against kept / budget, from small databases to 10 million keys; the
   longest call at 10 million keys and the budget's range; the same
   bytes over restarts between calls; stops and crashes at every record
   (031-03's probes, section 7).
4. **The Lean proofs**: whether the reclaim theorems, the contract and
   the checkers accept pCut = pStart for any iteration, not only the
   first; what would change.
5. **The counts and the format**: new state, stores, recovery cases and
   lines, next to `main` and 031-03's O-1; what changes in the stream's
   internal format.
6. **Open questions for Frans**, each with options and a
   recommendation: the getter's name; the live bytes in the rows; the
   cache's part; a commit's maintenance next to the calls'; the budget's
   range and default.


## 4. The design

Written 2026-11-26 by an agent of lead-1126, and built as a prototype
on the branch `031-04` of the clone c314 (section 5). Nothing of it is
on `main`.

### 4.1. In a paragraph

`maintain(int budget)` grants the database a budget of work, in cost
units of about 1 kB written. The call works in parts, each under the
write lock as a commit's maintenance is. A part does what `main`'s call
does, at most one of each: it continues the iteration that runs, a
commit's or a call's, by a step; it writes the index nodes that a done
iteration waits for (the take); it writes the filler; it makes the cut.
It also begins a **pass** when no iteration runs or waits for its cut and
the stream kept still holds a record of the application's. The parts go
on until their cost reaches the budget, or until a part writes nothing.
A pass that a call begins cuts at its own pStart: it rewrites every live
value stored before it, and its cut drops the whole stream before it.
Reclaim remembers one position, **a**, that of the application's last
record. a is read off the stream as 031-03's w is (R1 to R3), and the
pass waits until the take has passed a. Once a pass that began after a
is cut, a lies before the first available position, and no call begins
another pass. So the calls go quiet by construction: there is no drain,
no MIN_RELEASE and no R/4 clock for calls.

### 4.2. The rules

Each rule says what it is, when it applies and who applies it, and how
it is checked.

* **C1, the call.**
  * **What.** `void Db.maintain(int budget)` and
    `void Database.maintain(int budget)`. They replace
    `boolean maintain()`, which is removed.
  * **The budget.** It is clamped to 100 to 100,000 units
    (`Reclaim.MAINTAIN_MIN_BUDGET`, `MAINTAIN_MAX_BUDGET`). A unit is
    1,000 bytes of cost (`MAINTAIN_UNIT`).
  * **When, by whom.** The application calls it. `Db.maintain` repeats
    the following, each repetition a part:
    * the checks of a transaction (the database is active, top node
      ordinals and time are left);
    * under the write lock, `Reclaim.maintainPart(now, lastTransTime)`,
      which returns its cost;
    * if a cut's table is not yet durable, a sync outside the lock, and
      then the cut;
    * one batch of eviction's dead hand.
  * **The end.** The call stops when the parts' costs reach the budget,
    or when a part writes nothing. While the dead hand still has
    objects to release, it then runs alone within the rest of the
    budget, charged by its time: 5 µs a unit (`Db.MAINTAIN_NANOS`).
  * **Checked.** `ReclaimMaintainTester` (a call's growth is bounded by
    its budget and one part); `PassProbe`.
* **C2, the cost.**
  * **What.** A part's cost is the bytes it wrote to the stream (the
    stream length after it less before it, meta blocks included), plus a
    quarter of the bytes its step read (`stepReadBytes`). The bytes read
    are counted as follows:
    * for each KV the scan met, 8 bytes a segment and VALUE_NODE_BYTES;
    * the value, if it was loaded to be rewritten;
    * each index node the scan followed, at a full node's size
      (`stepNodeBytes()`).
  * **The determinism rule.** Only these counts decide whether another
    part runs. They are a function of the stream and of the call's
    inputs, its time and its budget. Timing does not count, nor what is
    resident: a node counts whether or not it was in memory (010-01,
    P2). The dead hand's time is charged only after reclaim's last part
    of the call, so it never decides what is written.
  * **Checked.** `WitnessProbe` (the same bytes with restarts between
    calls); `testSameStreamOverARestart`.
* **R1 to R3, the witness a.** These are 031-03's R1 to R3 (031-03,
  section 3), with w made a position.
  * **What.** a is the position of the last record that is not
    reclaim's own, or -1 if there is none.
  * **R1.** As in 031-03: a record is reclaim's own if it holds one of
    reclaim's maintenance keys.
  * **R2.** Every record of reclaim's holds the table or the current
    row. The table's last row and the current row hold a (`a=` in their
    text). A table without rows, written by the take before the first
    pass, is the text `a=N` alone.
  * **R3.** The running database sets a at each application record
    (`recordWritten`): at every user transaction, and at an internal one
    unless it holds a maintenance key of reclaim's. A start reads a off
    the stream:
    * the position of the stream's last record, if that record is not
      reclaim's;
    * otherwise the larger a of the table's last row (or of the table
      without rows) and of the current row;
    * the position of the last record, if the table holds no a (a stream
      of 2026.6).
  * **Why a position, not w.** The take before a pass (M1) needs to know
    where the application's last record is, not only which pStart it
    followed.
  * **Checked.** `WitnessProbe`, `Witness2Probe` and `StopAtProbe`: a
    database started after any record has the a of the run
    (section 6.6).
* **M1, when a call begins a pass.**
  * **What.** A pass is due (`passDue`) when all of these hold:
    * R is finite;
    * no iteration runs;
    * no done iteration waits for its cut (`cutPending`);
    * a ≥ fp: the stream kept holds a record of the application's.
  * **The begin.** If the startup pos sp has reached a, the pass begins
    with pStart = L, tStart = the last transaction's time, E the last
    key live then, and **pCut = pStart**. The table is stored.
  * **The take before a pass.** If sp has not reached a, M4 takes up to
    a first, and the pass begins in a later part.
  * **What is not asked.** No R/4 clock, no MIN_RELEASE, no condition on
    the stream's size.
  * **Why the take first.** Without it, the index nodes that the
    application's last records made dirty are written after the pass's
    pStart, by the takes that the pass waits for, and its cut keeps
    them. In HoleProbe's case these were 873 kB: 5,396 index nodes in 10
    table records (`HoleDiagProbe`, on the first prototype without it).
    With the take first, 117 kB are kept.
  * **Checked.** `HoleProbe`, `TwoStretchProbe`, `IdleLiveProbe`,
    `IdleShapeProbe`, `Reserve1Probe`.
* **M2 to M6, as `main`.**
  * M2: a step of MAX_STEP (16 kB) of the iteration that runs, without
    the allowance.
  * M3: the safe positions.
  * M4: a store of the table whose take goes on to the least wait
    position of a done iteration, or to a.
  * M5: the filler, which is 031-03's padded table.
  * M6: the cut's decision and the cut.
* **A commit's maintenance: unchanged.** A commit begins an iteration
  after 2 sd of growth and R/4. It steps by the allowance. Its pCut is
  lastPStart, or pStart for the first iteration.
* **G, the stream kept.**
  * **What.** `long Database.getStreamSize()`: `Db.getStreamLength()`
    less `Db.getFirstAvailablePos()`, each exact when read. A file
    storage may hold up to a file more.
  * **Checked.** It is the `kept` of every probe.

### 4.3. Why the calls go quiet

Let A be the position of the application's last record.

1. Reclaim's records leave a at A (R1, R3).
2. After A, the iterations are at most these: the one that runs or
   waits at A, which may be a commit's, then passes that calls begin,
   one at a time.
3. A pass begun after A has pStart > A. Once the first such pass is
   cut, fp = its pStart > A = a, and M1 begins no other pass.
4. Until that cut, the calls write a bounded amount:
   * the steps of an iteration, bounded by the keys live at its tStart
     and the step reserve;
   * takes, each up to a fixed target;
   * at most one filler for each waiting cut;
   * a few stores of the table.
5. The cut itself needs only R after tEnd.

So after the application's last record, the calls write at most the
iteration then in progress with its waits, and one pass with its waits;
then nothing. The argument uses neither the step reserve nor what an
iteration rewrote, and Codex's finding 1 of 031-03 has no counterpart
here (section 6.4). It is argued and tested, not proved (section 7).

### 4.4. What stays of `main`'s maintain()

* **The take (M4).** It stays, as a store of the table (031-03's R2, in
  place of an empty record). The take before a pass uses it too.
* **The filler (M5).** It is 031-03's padded table, one record, not
  `main`'s put and delete of `-fill.txt`.
  * R2 needs it: every record of reclaim's must hold the table or the
    current row.
  * A stop cannot leave a filler live (031-03, section 9.2; RB-010).
* **The sync and the cut (M6).** As in `main`, but a call may now make
  several cuts. Each sync is made outside the lock, before the next
  part.
* **The dead hand.** One batch a part, then alone, charged by its time.
* **What goes:**
  * M1's two stretches and `tablePos()`;
  * MIN_RELEASE;
  * the R/4 clock for calls;
  * `maintainDue()` and the boolean result;
  * the filler's key and its two transactions;
  * the take's empty record.

### 4.5. P1: what a commit waits for

A part holds the write lock for at most one of each: a step (16 kB of
KVs scanned), a take (256 kB beyond one transaction's share), a filler
(200 kB), a few stores of the table, and the cut's decision. That is
what `main`'s whole call holds it for. The sync is made outside the
lock, as on `main`.

A commit waits for one part only if the lock passes to it between two
parts. The write lock is a Java monitor, which is not fair: the call's
loop can take it again at once. In the prototype, a commit waited for
several parts at a budget of 100,000. An experiment with a yield between
parts brought the wait down to the length of a GC pause (section 6.5,
section 9, Q9).


## 5. The prototype

* **Where.** The branch `031-04` of the clone c314, on `main` at
  `9e72d0d5`; `prototype.diff` in this directory is its `java/`
  against `main`. It has no switches: the design only.
* **The code.**
  * `Reclaim.maintainPart` replaces `Reclaim.maintain`.
  * `passDue` replaces `maintainBeginDue` and `tablePos`.
  * `maintainTakeTarget` gains the take before a pass.
  * a: `appA`, `isOwnRecord`, `recordWritten`, `initFromDb(StoredTrans)`,
    and `a` in the row and in the table without rows.
  * `storeTable(takeTo, pad)` serves the take and the filler.
  * The read charge is in `step()`.
  * `Db.maintain(int)` holds the loop of parts, and `Db.initFromDb`'s
    caller passes the last record.
  * `Database.maintain(int)` and `Database.getStreamSize()`, with
    `DatabaseImp`.
* **Tests adapted.** `BEFORE COMMIT OK` needed these changes:
  * **`ReclaimMaintainTester`, all seven tests.** "Returns false"
    became "writes nothing". The bounds of 024-32 became the budget's
    and G5's 600 kB. `testNothingDue` now expects, for a finite R on a
    fresh database, one pass and its cut, then nothing.
  * **`Reclaim.Tester.testAllowanceCountsNodesMadeAfterTheRow`.** It
    compared the stored row's text with the row in memory. a moves on
    at every commit, so the test now compares with the a that the row
    holds, and checks that it is at most the a in memory.
  * **`Reclaim.Tester.testMaintainBeginsWithEndKey`.** It calls until a
    pass begins, since the take before the pass comes first.
* **Callers in `java/stress`.** `TraceExport`, `AppRecord`,
  `CountGates` (G5: the allowance 600 kB, "the last call that wrote" in
  place of "returned true"), and the apps b1, b5, c2, d2 and d3: each
  calls `maintain(budget)` once where it called `maintain()` until it
  returned false. Only `TraceExport` ran (section 6.7); `AppRecord`'s
  replay of an application's calls is approximate now (calls of 100
  units until as many records), and not run.
* **Probes**, in `probes/`, in package `bergdb.core`, compiled against
  the prototype's jar or `main`'s and put before it on the class path:
  * `M.java`, a shim: a call is `maintain(B)` on the prototype (B from
    `-Dbudget`, 100 by default) and `maintain()` on `main`, so one probe
    runs on both;
  * 031-03's `TwoStretchProbe`, `StopAtProbe`, `IdleShapeProbe`,
    `WitnessProbe` and `Witness2Probe`, and 028-53's `HoleProbe` and
    028-51's `IdleLiveProbe`, each adapted to the shim;
  * new: `PassProbe` (the calls of a pass, the longest call and
    commit), `Reserve1Probe` (Codex's case) and `HoleDiagProbe` (where
    HoleProbe's stream kept goes, by record kind).


## 6. Measurements

On the branch `031-04` at `92e8db79`; its head `cc02ccff` changes two
Javadoc comments only. The setup:

* MemoryStream or CutStream, test clocks, R = 1 s, a call a millisecond
  of the test clock.
* A call is `maintain(100)` (100 kB), unless a budget is named.
* `main` is `9e72d0d5`, built in a worktree of the clone, and runs the
  same probes through the shim (section 5), where a call is
  `maintain()`.

Sizes and counts do not depend on the machine. Times are indicative
only: F53 ran week.sh meanwhile, at a load of 12 to 27 (uptime),
recorded with each PassProbe run.

### 6.1. RB-007, and back to empty

* **`HoleProbe 4000 20000`**: kept 116,880 bytes, the twin 53,120.
  `main` keeps 4,804,384 and 315,008; 031-03's O-1 189,240.
* **`HoleProbe 20000 20000`**: kept 117,872, the twin 116,672. `main`
  keeps 5,361,912 and 872,424; O-1 124,392.
* **The last call that wrote** is 1,605 of 10,000 in both, where
  `main`'s is 623 and 632. A pass waits R for its cut, then nothing.
* **The first prototype, without the take before a pass**, kept 884,128
  and 841,864. `HoleDiagProbe` showed why: after the second writes, the
  stream kept was 10 table records holding 5,396 index nodes (873 kB),
  the takes of the nodes that the application's last writes had made
  dirty. They were written after the pass's pStart, so its cut kept
  them (section 4.2, M1).
* **An emptied database in `WitnessProbe`'s phases** ends at 16 to 183
  kB kept, in 24 runs.

### 6.2. 031-03's cases of its section 9

* **9.1, an emptied database kept at 790 kB** (`TwoStretchProbe
  390000 390000 390000 10000 20000`; RB-006's remaining part):
  * kept 17,680 bytes, 16,976 more than a fresh database;
  * `main` keeps 790,264, 789,560 more.
  * **Fixed**: the call's pass cuts at its own pStart, after both
    stretches.
* **9.2, the filler left live** (`StopAtProbe 10 100 20000`; RB-010):
  * on `main`, a stop at its record 6, the filler's delete, leaves
    `-fill.txt` live, with 199,672 bytes kept after 20,000 calls;
  * on the prototype, 8 records and 8 stops: no filler key is ever
    written, and none is live.
  * **Fixed**, by 031-03's padded table, which the prototype keeps
    rather than `main`'s two transactions. R2 needs a record of
    reclaim's to hold the table or the row, and one record leaves
    nothing to delete.
  * 1,460 stops in four more scenarios (`StopAtProbe` 10 100 5000 30;
    20000 1000 5000 50; 100000 5000 5000 200; 5000 300 5000 400): 0
    with another a, and 0 with the filler live. A stop after the
    workload's last record gives the uninterrupted run's stream kept
    within 50 kB. A stop before it truncates the workload, so the kept
    stream differs as the workload does.
* **9.3, a database not written to, kept at 7 times its values**
  (`IdleShapeProbe 3000 2 100 50000000 20`):
  * kept 1,065 kB, 2.31 times the values put once (462 kB);
  * `main` keeps 3,245 kB, 7.01 times.
  * **Fixed** in this case. After the overwrites, one pass rewrites the
    live values once (676 kB rewritten), and its cut drops everything
    before it; then a < fp, and nothing is written in the last 20 R.
  * A database written only below 2 sd keeps no more than the stream
    of its last pass and its waits.

### 6.3. Quiet when done

`IdleLiveProbe LIVE SD 20 10`, written by the calls in the last 10 R,
with `main` in brackets:

* 30,000 values at sd 1 MB: 0 (24,522 kB); kept 6,070 kB (9,989).
* 15,000 at sd 1 MB: 0 (14,554 kB); kept 3,056 kB (5,379).
* 100,000 at sd 1 MB: 0 (51,595 kB); kept 20,237 kB (21,240).
* 100,000 at sd 5 MB: 0 (55,421 kB); kept 20,101 kB (24,215).

The last call that wrote is 2,042 to 2,337 of 20,000: one pass, and its
cut R later. In `WitnessProbe`, every phase of calls alone (24 runs,
two phases each) writes nothing in its second half.

### 6.4. Codex's case of 031-03: a step reserve of 1

`Reserve1Probe 150 111 SD ROUNDS 1000000 1`: a step reserve of 1, 150
keys of 111 bytes, node size 8, a million calls (1,000 R).

* **Every run ends.** SD was 10 kB, 100 kB and 1 MB, with 0 or 10
  rounds of overwrites. Each run did 1 or 2 iterations, wrote nothing in
  the last 500,000 calls, and its last call that wrote was 1,003 to
  2,006.
  * Stream kept: 143 to 181 kB. `main` keeps 34 to 429 kB, and is quiet
    too.
  * 031-03's O-1, by Codex: 866 iterations and 236 MB written in a
    million calls.
* **Variants.** 500 keys: 2 iterations, 548 kB kept, 0 in the last
  half. The default reserve: 2 iterations, 200 kB, 0 in the last half.
* **Why.** No rule here depends on what an iteration rewrote. The
  reserve only splits a pass into more steps (section 4.3).
* **The stream kept with a reserve of 1** holds the pass's rows: about
  one row record a key, each step split after one index node.

### 6.5. The calls of a pass, and the longest call

`PassProbe N 100 BUDGETS SD`: N keys of 100 bytes put once (all live),
then passes with each budget in turn. "Calls" counts the calls until the
pass is done, as a multiple of kept / budget.

* **N = 10,000, sd 50 MB:** 1.61 at 100, 1.53 at 1,000; at 10,000 and
  100,000, 1 call.
* **N = 100,000, sd 50 MB:** 1.57 at 100, 1.27 at 1,000, 1.52 at
  10,000; 1 call at 100,000.
* **N = 1,000,000, sd 50 MB:** 1.63 at 100, 1.68 at 1,000, 1.70 at
  10,000, 2.00 at 100,000 (4 calls).
* **N = 1,000,000, sd 1 MB:** 1.97 at 100,000 (4 calls).
* **N = 10,000,000, sd 50 MB** (1.63 GB kept, put in 17 s): 1.59 at
  100 (25,949 calls), 1.77 at 1,000 (3,531), 1.77 at 10,000 (356), and
  1.79 at 100,000 (36). The first pass wrote 1.22 times the stream
  kept, which went from 1.63 to 1.99 GB; later passes wrote 1.00 to
  1.02 times, and kept about 2.01 GB.
* **What a pass costs.** In this case of all-live data, a pass writes
  1.0 to 1.4 times the stream kept: every value, the index nodes, and
  the take before it. The read charge adds 0.2 to 0.75 more. So
  "kept / budget" is low by a factor of 1.5 to 2 when nothing is dead.
  Without the read charge, the first prototype took 1.08 to 1.14 times
  at a budget of 100.
* **With dead data**, the case that maintain() is for (`-Drounds=4`,
  so three quarters of the stream are dead):
  * 100,000 keys: 0.40 of kept / budget at 100, and 0.48 at 1,000;
  * 1,000,000 keys: 0.43 at 1,000.
  * The stream kept goes from 60 MB to 19.8 MB, and from 649 MB to
    198 MB.
* **After every pass**, nothing is written after its cut (2,000 calls).
  The cut comes 1,001 to 1,002 calls after the pass is done: R at a
  call a millisecond.
* **The longest call** (indicative; load 12 to 27):
  * at a budget of 100: 40 to 185 ms;
  * at 1,000: 28 to 62 ms;
  * at 10,000: 37 to 177 ms;
  * at 100,000: 39 ms (10,000 keys) to 1,590 and 2,401 ms
    (1,000,000 keys);
  * at 10,000,000 keys: 268 ms at 100, 294 ms at 1,000, 593 ms at
    10,000, and 3,499 ms at 100,000.
  * A call of 100 units writes about 100 kB; its calls of 40 to 300 ms
    were not examined (F53 ran week.sh, and the JVMs collect garbage).
* **The longest commit during calls** (P1).
  * The setup: `PassProbe 10000000 100 B 50000000 1`, where a thread
    commits a put of 10 bytes every millisecond of wall time during the
    calls. Each figure is from one run, and is indicative.
  * At a budget of 100,000, the longest commit was 590, 908 and
    1,281 ms in three runs. Their longest GC pauses were 250, 250 and
    608 ms (`-Xlog:gc`).
  * At a budget of 100: 153 ms.
  * `main`, with `maintain()` as the call: 143 ms, with GC pauses of up
    to 428 ms. That run made 20,000 calls and reached no cut.
  * **Why.** The write lock is a Java monitor and is not fair. After a
    part, the call's loop takes the lock again at once, so a waiting
    commit can wait for several parts.
  * **An experiment**, not in the prototype: `Thread.yield()` after each
    part. The longest commit was 259 ms, with GC pauses of up to 254 ms;
    the control run without the yield gave the 1,281 ms above. See
    section 9, Q9.

### 6.6. a at every record, and P2

* **`WitnessProbe SD EVERY 1 SEED`** (031-03's): a random workload of
  puts, deletes, empty transactions, setter records and calls, with
  phases of calls alone and an emptied database. SD was 5,000, 20,000,
  100,000 and 1,000,000, with a restart every 7, 23 and 101
  operations, and two seeds: 24 runs.
  * The same stream in each, over 288, 1,268 and 4,166 restarts.
  * 52,857 starts after a record, 0 with another a. A few records lie
    before the stream's length at a cut of the same call; they are
    skipped, as in 031-03.
  * 0 records of another kind than their keys say.
* **`Witness2Probe SD EVERY SEED 3000`** (031-03's review's): 4 runs,
  20,660 starts, 0 with another a. The same stream over 725 to 1,912
  restarts.
* **In all, 73,517 starts after a record, 0 with another a; 51,268
  restarts between operations, the stream the same.**
* **`StopAtProbe`**: 1,468 stops inside a call, 0 with another a
  (section 6.2).
* **`ReclaimMaintainTester.testSameStreamOverARestart`**: the same
  bytes with two restarts among 6,000 calls.

### 6.7. Gates

* **`java/before-commit.sh`**: on `92e8db79`, `BEFORE COMMIT OK (105 s)`
  at a load of 17 to 19; on `cc02ccff`, `BEFORE COMMIT OK (87 s)` at 14 to
  16. The tests changed are those of section 5.
* **The conformance on the unchanged trace checker**, built in the
  clone (`lake build tracecheck`), on `92e8db79`:
  * the reclaim set: `CONFORMANCE OK`, 40 traces, r-maint and r-maint-sd
    among them; C-CUT 0 of 880 CUT lines fail, C-STEP 0 of 26,656
    transactions;
  * the crash set: OK, 15 traces, c-maint among them; 0 of 257 CUT lines
    and 0 of 6,805 transactions fail;
  * e-r-maint of the evict set: OK, 3 traces.
  * The same three on `1e4238ba`, before the read charge, were OK too.
    A first run of the reclaim set on `92e8db79` failed with
    `ClassNotFoundException` for every trace: `count-gates.sh`, started
    beside it, rebuilt `java/build` under it. The run again was OK.
* **`count-gates.sh all`**: `COUNT GATES OK`.
  * G5: kept 102,184 bytes, the twin 199,296. The last call that wrote
    is 2,002 of 20,000.
  * G4's M5 1.429, G1 105,200 bytes, G2 1.227, G3 4.721.


## 7. The Lean proofs

An agent of lead-1126 read lean/ in the clone at `9e72d0d5`
(2026-11-26), with the question of part 4: do the reclaim theorems, the
contract and the checkers accept pCut = pStart for any iteration, not
only the first?

* **Yes, and nothing changes.** In the model, an iteration's cut c is
  free up to t0 + 1 (`StepsOK` asks `it.c ≤ it.t0 + 1`,
  lean/contract/Contract/ReclaimSteps.lean, 179 to 181; the premise
  `hc : c ≤ t0 + 1` of `old_live_before`, 358). A cut at its own pStart
  is c = t0 + 1, the largest that the contract allows.
  * `iterationOK_of_stepsOK`, `rc2_of_iteration`, `cutOK_of_rc` and
    `PE.pe_reclaim_reads_steps` and `pe_reclaim_user_reads_steps` then
    give reads that are right from fa on.
  * The first iteration has that cut today, and `ReclaimStepsExample.itS`
    (c = 2, t0 = 1) proves the case.
* **No statement ties a cut to another iteration's pStart.**
  * Between cuts, the only rule is that cuts do not go down: c' ≤ c
    (RC1's order; `CutsMeetRC`, ReclaimScheme.lean, 107 to 110;
    `CutsMeetSteps`, ReclaimSteps.lean, 601 to 607).
  * Cuts still only rise: a later cut's iteration has a larger pStart
    than any earlier cut's row, so its pCut is above every earlier
    pCut.
  * An older done iteration left uncut is accepted. A cut needs only
    some iteration with that c. The trace checker finds it through the
    step at R(fa) (lean/Check/Steps.lean, 1196 to 1206), not through
    the table.
* **The checkers.** They read pCut and never compute it.
  * The trace checker's STEP-c rule is `c ≤ t0 + 1` (Steps.lean, 967;
    RESUME, 1084). STEP-chain asks a new iteration for a later t0,
    nothing about c (955 to 966).
  * The exporter maps Java's `row.pCut` to a record index, which
    exists, since every pCut is a pStart (TraceExport, 1341, 1364,
    1027).
  * The contract's checker skips CUT lines (lean/contract/Contract/
    Trace.lean, 136 to 138).
  * No Lean file mentions pStart, tStart, the table or `maintain()`.
* **Run on the prototype.** The unchanged trace checker, built in the
  clone (`lake build tracecheck`), on the conformance's reclaim and
  crash sets and e-r-maint (section 6.7). Their r-maint, r-maint-sd,
  c-maint and e-r-maint traces call `maintain(100)` after every first,
  second or third user transaction, so their iterations include passes
  that cut at their own pStart.
* **Proved, and only tested.**
  * **Proved, whatever M1 decides:** reads are right from fa on after
    every cut whose iteration's steps follow the model of the steps and
    meet RC1 and RC4. That includes a pass's cut at its pStart.
  * **Tested only, as for 031-03:** that Java's c is t0 + 1 for a
    pass, which holds because tStart is the last record's time and
    pStart the stream's length (`Db.maintain`,
    `dbClock.lookupTime(Long.MAX_VALUE)`), as for the first iteration
    today. Also tested only:
    * R3 (section 6.6);
    * the calls going quiet (section 4.3);
    * RB-007's fix, and back to empty.
* **What would change.** Nothing in Lean. In Java and the texts:
  * the begin's pCut (`Reclaim.maintainPart`);
  * 027-13, sections 1.3 and 1.10.
  * `Reclaim.Tester.testCutPointBeforeScan` asserts pCut = the previous
    row's pStart, for commits only. It passes unchanged.
* **What becomes simpler to state.** As 031-03, section 8, says for
  w, the calls' going quiet becomes a small statement about positions:
  a, the pStarts, fp and the last record's kind. Here it needs no
  drain: once a pass with pStart > a is cut, a < fp, and M1 is false
  until the application writes. That the cuts come (the waits end)
  stays tested. None is proposed for 2026.7.


## 8. The counts and the format

The counts are next to `main` and 031-03's O-1 (031-03, section 6).
Lines of code exclude comments and blank lines, from `git diff -w`
against `main`.

* **New state:** 1 number, a, in the rows that reclaim stores anyway.
  It is 031-03's w made a position. A table without rows holds it alone
  (`a=N`), as written by the take before the first pass.
* **New stores:** none of its own.
  * The take's records hold the table (031-03's R2).
  * The filler is the padded table: one record where `main` has two.
  * The take before a pass writes M4's records at a new target, a.
    `main` begins the iteration at once.
* **Recovery cases:** 0. A start evaluates the expression that the
  running database keeps, and writes nothing. There is one reading rule
  for a stream of 2026.6: a row or table without a reads as the
  position of the stream's last record. Then one pass follows, which is
  the conservative choice.
* **Invariants:** 1 (R3 for a), checked at every record by the probes
  (section 6.6). The calls' quiet (section 4.3) is argued, not an
  invariant of the code.
* **Rules:** C1 (the call), C2 (the cost), R1 to R3 (a), and M1 (a pass
  when passDue, after the take to a). M2 to M6 are `main`'s.
* **Lines, the production code:**
  * `Reclaim`: 84 added, 60 removed.
  * `Db`: 30 added, 12 removed: the loop of parts.
  * `Database`: 2 added, 1 removed.
  * `DatabaseImp`: 6 added, 2 removed.
  * In all, 122 added and 75 removed: **47 more than `main`**.
* **Lines, by part:**
  * a, its reading and the table without rows: about 40, as 031-03's
    w.
  * M1 and the take before a pass: about 15.
  * The cost and the loop: about 30.
  * Removed: `tablePos()`, M1's two stretches, MIN_RELEASE, the filler's
    key and transactions, `executeInternal`, `maintainDue()`.
* **Next to 031-03's O-1.** O-1 is about 25 more than `main` when
  landed without its switches (031-03, section 6). This design adds
  about 22 more: the budget's loop with its sync and dead hand, the
  read charge, and the take before a pass. It drops O-1's drain (X)
  and MIN_RELEASE.
* **Tests changed:** `ReclaimMaintainTester` (its seven tests, since
  the API changed) and two tests of `Reclaim.Tester` (section 5).

### 8.1. The stream's internal format (027-03)

No meta version and no record format change. What changes in the texts
and records of reclaim's keys:

1. **`a=<decimal>`** in the text of the table's last row and of the
   current row (027-03, section 15). 2026.6 ignores the name, and drops
   it at its next store of the row.
2. **A table without rows**, the text `a=<decimal>`, written by the
   take before the first pass. 2026.6's parser refuses it at a start
   (`InternalDataException`: a table must have a row). Such a table is
   in the stream only between the first take before a pass and that
   pass's begin, a few parts of one call, unless the call's budget or a
   stop ends the call in between.
3. **The take's records hold the table**, where `main`'s are empty
   records.
4. **The filler is the table with spaces after its text**, up to the
   next meta block. `main` puts and deletes `/#i/dreclaim/-fill.txt`.
   2026.6's parser skips the spaces (031-03).
5. **pCut = pStart** in the rows of passes that calls begin: a value,
   not a format. 2026.6 reads it as any pCut, and its own cuts follow
   from it.
6. **The order of a row's names**: thirteen in a Java `HashMap`, as in
   031-03 (027-03, section 15, G16).

A stream of 2026.6 opened by the prototype gets a from its last record
(the reading rule above). A stream of the prototype written by 2026.6
and opened again by the prototype can lose a, as 031-03's w can
(Codex's finding 3 of 031-03): a one-way upgrade is safe, and a round
trip needs a rule. A filler that 2026.6 left live stays live after an
upgrade (Codex's finding 4 of 031-03; RB-010), unless the landing
deletes it.


## 9. Open questions for Frans

Each question has its options and a recommendation. Q1 to Q5 are those
of section 3, part 6. Q6 to Q9 came up during the study.

* **Q1. The getter's name.**
  * Options:
    * `getStreamSize()`, the prototype's;
    * `getStreamKept()`;
    * `getStreamBytes()`;
    * `getStorageSize()`, which is misleading: a file storage holds up
      to a file more.
  * Recommended: **`getStreamSize()`**, with the prototype's Javadoc:
    "the size of the stream kept, in bytes: from the first position
    that reclaim has not cut to the stream's end".
* **Q2. The live bytes in the rows.**
  * Options:
    * **(a)** none in 2026.7, as in the prototype.
    * **(b)** a name `live` in the row: a pass's scan sums the bytes of
      the KVs it meets (8 bytes a segment, the value, VALUE_NODE_BYTES),
      and a getter reads them from the last pass's row. This is one
      more name in the row, and the figure is only as fresh as the last
      pass.
    * **(c)** a figure from the last done pass's `rewritten`, which is
      already stored: its rewrites and the index nodes it made dirty.
      For a pass (pCut = pStart) this is the live data and its index,
      as of the pass. For a commit's iteration it is only what lay
      before its pCut.
  * Recommended: **(a)**. If a figure is wanted, (c), documented as "as
    of the last pass".
* **Q3. The cache's part.**
  * Options:
    * **(a)** the prototype: one batch of the dead hand a part, then the
      dead hand alone, charged by its time (5 µs a unit), after
      reclaim's last part of the call;
    * **(b)** `main`'s one batch a call;
    * **(c)** also eviction of cold nodes down to the cache's budget
      within maintain()'s budget, in a later item.
  * Recommended: **(a)** now; (c) later, as its own design.
* **Q4. A commit's maintenance next to the calls'.**
  * Options:
    * **(a)** The prototype: commits unchanged (a begin after 2 sd and
      R/4, steps by the allowance, pCut = lastPStart). A call continues
      a commit's iteration by its steps.
    * **(b)** As (a), and an iteration whose pCut is at or before fp
      ends at its begin, with no scan.
      * After a pass's cut, fp is the pass's pStart. The next
        iteration that a commit begins gets pCut = that pStart = fp, so
        it rewrites nothing and is never cut. Its scan still walks
        every key, in steps that each store a row.
      * At 100,000 keys, such an iteration took one call of 1,000 units
        and wrote 1.0 MB, all of it rows and index nodes (`PassProbe`,
        before it was made to count only the pass). This grows with the
        number of keys.
      * `main` has the same iteration once, after the first
        iteration's cut. With calls it comes after every pass that a
        commit follows.
      * (b) changes `main`'s commit-only streams from that point on.
    * **(c)** Commits also cut at their own pStart. This rewrites at
      twice `main`'s rate under commits (031-03, section 5).
  * Recommended: **(b)**, as its own 028 entry, gated by StreamDigest
    and G1 to G4. Not (c).
* **Q5. The budget's range and default.**
  * Options:
    * the range 100 to 100,000 units of 1 kB, as in the prototype, or
      wider;
    * no default, as in the prototype, or an overload `maintain()` =
      `maintain(1000)`.
  * Measured, on a loaded F53 (section 6.5):
    * the longest call of 1,000 units: 62 ms at 1 million keys and
      294 ms at 10 million;
    * of 100,000 units: 1.6 to 2.4 s at 1 million keys and 3.5 s at
      10 million.
    * A commit waits for parts, not for the call, once the lock is
      handed over between parts (Q9).
  * Recommended: **keep the range; no overload**. The Javadoc suggests
    1,000 for an idle loop, and calls of 100,000 only where a call may
    take seconds.
* **Q6. The take before a pass**, beyond section 2's direction.
  * Without it, RB-007's case keeps 873 kB of index nodes (section
    6.1).
  * It makes the witness a position (a) in place of 031-03's w. It also
    adds a table without rows (`a=N`), which 2026.6 cannot read, for
    the few parts before the first pass begins (section 8.1).
  * Options:
    * **(a)** keep it as built;
    * **(b)** drop it, and accept the takes of the last writes' nodes in
      the stream kept, up to about the dirty index of one startup
      distance of writes;
    * **(c)** keep it, and avoid the table without rows: the first pass
      begins without the take, so only the first pass keeps such nodes.
  * Recommended: **(a)**, with the format decision of Q8.
* **Q7. The read charge's weight**, and with it the user's model.
  * With reads at a quarter, and index nodes at a full node's size, a
    pass over all-live data takes 1.5 to 2 times kept / budget calls.
    Without the read charge it takes about 1.1 times. With three
    quarters dead, it takes about 0.4 to 0.5 times.
  * Section 2's model, "at most about the stream kept divided by the
    budget", holds where there is dead data to give back, not where
    nothing is dead. There every pass writes at least the stream kept.
  * Options:
    * **(a)** keep the weight, and the Javadoc says "about one to two
      times";
    * **(b)** charge the index nodes at their stored size, or reads at
      an eighth;
    * **(c)** no read charge: only the bytes written decide.
  * Recommended: **(a)**. The cost model is internal, and reads are
    real work.
* **Q8. The format** (018-01's rule).
  * The changes, as listed in section 8.1:
    * `a` in the rows;
    * the table without rows;
    * the take's and the filler's records;
    * pCut = pStart in the passes' rows.
  * With them, Codex's findings 3 and 4 of 031-03 (a writable
    downgrade, an old filler) stand as they do for 031-03.
  * Options:
    * **(a)** a compatible change of the internal format, with a one-way
      upgrade and a refusal of 2026.6 in a stream written by this
      design;
    * **(b)** the same with a rule that reads mixed rows (a = the
      position of the last record whenever the last row lacks it), as
      the prototype does;
    * **(c)** an old filler deleted once at the landing.
  * Recommended: **(b) and (c)**.
* **Q9. The lock between parts** (P1; sections 4.5 and 6.5).
  * Java's monitor lets the call's loop take the write lock again ahead
    of a waiting commit. At 10 million keys and a budget of 100,000, a
    commit waited up to 1.3 s; with a yield between parts it waited
    259 ms, about the longest GC pause.
  * Options:
    * **(a)** `Thread.yield()` after each part: one line, and a hint to
      the scheduler, not a promise.
    * **(b)** a handoff: `Db.execute` counts the commits that wait for
      the write lock, and the call's loop, after a part, waits while the
      count is above 0. A few lines; a commit then waits for at most one
      part.
    * **(c)** a fair lock in place of the monitor: a change of every
      writer's locking.
  * Not in the prototype. The stream does not depend on it: what a part
    writes depends on the order of the transactions, not on their
    timing (P2).
  * Recommended: **(b)**, measured with `PassProbe`'s commit thread and
    `timing.sh`'s pause probe.
  * Frans chose (b), the handoff, on 2026-11-26: commits count
    themselves while they wait for the write lock, and a call's loop,
    after a part, waits while the count is above 0; for this direction,
    if Frans takes it. Being added to the prototype and measured
    (q9-handoff.md).

Not settled here, and the same as for 031-03:

* **028-54**: P2 inside a call. A stop or a crash between parts of a
  call changes what the next start does, as between a user record and
  reclaim's records today. Parts of a call are now more numerous, but
  each part ends at a record boundary.
* **A database written slowly** under calls: a pass after each cut,
  about once an R, while the application writes.
* **Not run**:
  * `night.sh`, `level3.sh` and `level4.sh` in full, and `timing.sh`.
    On the commit path, a commit gains one comparison and a store of
    its position.
  * StreamDigest and RestartInvariance;
  * the apps of `apps.sh`.
* **Not reviewed** by an independent agent or by Codex.


## 10. State

2026-11-26, by an agent of lead-1126.

* **Done:**
  * the design (section 4);
  * its prototype, on the branch `031-04` of the clone c314
    (`cc02ccff` for `java/`, with `BEFORE COMMIT OK`);
  * the measurements (section 6);
  * the Lean answer (section 7);
  * the counts and the format (section 8);
  * the open questions, with recommendations (section 9).
* **Next:** Codex's review (section 3), then Frans's decisions.
* **Not done:** no independent review. Nothing is on `main`.


## Log

2026-11-26. Created by lead-1126 at Frans's request, from the
discussion of 031-03 with him: a study of the direction, not a decision.

2026-11-26. The study, by an agent of lead-1126 in the clone c314
(branch `031-04`): `maintain(int budget)` in parts with a deterministic
cost; a pass that a call begins cuts at its own pStart, and begins only
while the stream kept holds a record of the application's (031-03's
witness, made a position, a) and after the take has passed it; the
calls go quiet by construction, with no drain and no MIN_RELEASE. RB-007's
case keeps 117 kB (`main` 4.8 MB); 031-03's 9.1, 9.2 and 9.3 fixed;
Codex's case of a step reserve of 1 ends; 73,517 starts with the run's a.
Sections 4 to 10, `prototype.diff` and `probes/`.

2026-11-26. Q9: Frans chose (b), the handoff between a call's parts, for
this direction if he takes it; being added to the prototype and measured
(q9-handoff.md).
