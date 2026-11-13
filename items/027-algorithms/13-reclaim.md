# 027-13. Reclaim

Created 2026-11-13 by Frans Lundberg. Status: draft (the pilot part of
027-04, section 5.1, step 3; not yet reviewed).

Part 9 of 027 (027-04, section 2.3; Level 3): how the front of the stream
is cut. The rule as `main` has it at 0870e7ea (2026-11-13), read from the
code. It replaces 027-01's `levels.md`, section 6, and `sis-model.md`,
section 15.3, both stale since 026-05. The bytes are 027-03's; the take,
D, Rule A and the startup pos are part 6's (until it is written, 027-01's
`sis-model.md`, sections 5 and 6). Each claim carries one status word of
027-04, section 2.2.


## 1. What it does

With a finite retain duration R, reclaim keeps every state from now - R
on readable and lets the storage drop the stream before a cut position.
It works in iterations. An iteration fixes a cut position pCut and then,
in steps, puts again every live value stored before pCut, with the same
key and value; the puts make the index nodes on their paths dirty, so the
take writes them again after pCut. When the iteration has ended, its
nodes are written and its end is older than R, the stream before pCut is
cut, and lookups before the iteration's end time are refused.

### 1.1. Settings, terms and constants

* **R**, the retain duration, in time units (100 ns): at least 10^7 (one
  second); 2^63 - 1 is forever, the default.
* **f**, the internal fraction, an integer in units of 2^-16, from 66 to
  58,982 (0.001 to 0.90); the default 16,384 (1/4). A decimal x becomes
  round(x * 65,536), halves up.
* **Kept in the stream**, in the internal KV `/#i/dreclaim/-settings.txt`,
  the exact text `retain=R\nfraction=f\n` (027-03, section 15). A call
  that sets R or f refuses a value out of range before it writes
  anything; with the values in force it writes nothing; otherwise it
  commits one internal transaction with the KV, and the new values hold
  from the next transaction. Without the KV the defaults hold.
* **sd**, the startup distance in force; **sp**, the startup pos of the
  last record written; **mp**, the position of the transaction that the
  last valid meta block names (027-03, section 6), where recovery starts.
* **fa** and **fp**, the first available lookup time and position: 0
  until the first cut.
* **The table**: one row an iteration, in `/#i/dreclaim/-table.txt`; the
  row of the iteration in progress also in `/#i/dreclaim/-current.txt`. A
  row: pStart, tStart, pCut, E (the end key), lastKey, kvCount,
  rewritten, done, tEnd, pEnd, pSafe, cut. The current iteration is the
  table's last row if it is not done.
* **Internal transactions.** Reclaim writes only in transactions of its
  own, each with its own time; user transactions are refused in the last
  1,024 times, which are kept for them. Reclaim reacts to user
  transactions only.
* **Constants**: MIN_STEP 10,000 bytes; MAX_STEP 16,000; VN 32 (a value
  node's bytes besides its key and value); META 200,000 (the meta block
  distance); MIN_RELEASE 400,000; TAKE_MORE 262,144; RESERVE 4 MiB (a
  test setting, not in the stream); NB = 80 + 48 N, N the largest node
  size.

### 1.2. After each user transaction

Under the write lock, after the user transaction T's record is appended,
within T's go point: a failure here fails the database; a stop that comes
meanwhile ends it, T stays committed, and the work goes on after the next
start (015-53).

    L := the stream length after T's record;  t := T's time
    it := the current iteration
    if it is none and R is finite and L > lastPStart + 2 sd
            and t - lastTStart >= R div 4:
        it := begin(pStart = L, tStart = t)                   (1.3)
    if it is not none:
        allowed := floor((L - it.pStart) * f / 2^16) - it.rewritten
        if allowed > MIN_STEP: step(it, min(allowed, MAX_STEP))   (1.4)
    markSafe()                                                (1.5)
    decideCut(now = t)                                        (1.6)
    makeCutIfDurable()                                        (1.7)

lastPStart and lastTStart are those of the table's last row: 0 and minus
infinity if it has none. On the call that begins an iteration, L - pStart
is 0, so there is no step.

### 1.3. The start of an iteration

begin(pStart, tStart) appends a row and stores the table, in one internal
transaction:

* pCut := pStart for the first iteration (an empty table), else
  lastPStart, the pStart of the iteration before;
* E := the greatest key live at tStart, of every key, BergDB's own too
  (any live value may need a rewrite); "none" if no key was live;
* lastKey none; kvCount, rewritten and tEnd 0; pEnd and pSafe unknown;
  done and cut false.

### 1.4. A step

step(it, W) is one internal transaction:

1. **The scan** (since 026-05): the live KVs at the latest state, the
   step's own time, forward from the first key after lastKey (from the
   first key if none), up to E inclusive. If E is none, or lastKey is at
   or after E, there is no scan, and this step is the last.
2. **Each KV met**, in key order, with p its value node's position (none
   if not yet written):
   * rewrite := p < pCut;
   * if rewrite, and the step holds a KV to rewrite already, and the
     value nodes' bytes with this one would pass the value limit (7/8 of
     the record limit, 027-03, section 8.3): stop before this KV, which
     is the next step's first;
   * lastKey := its key; kvCount += 1;
   * if p < pStart: size += 8 s + v + 100 (s the key's segments, v the
     value's bytes); only these KVs count (023-08, fault 13);
   * stop after this KV if the scan has followed more than max(1,
     RESERVE div NB) index nodes (the step is split), or else if
     size > W;
   * keep it if rewrite; walk past it otherwise.

   If the scan passes E or reaches the last key without a stop, this
   step is the last.
3. **The puts**: for each KV kept, a put of the same key and value, and
   a read of the key at the scan's time; rewritten += 8 s + v + VN each.
   Then a put of the row at `-current.txt`: it with the new lastKey,
   kvCount and rewritten, plus the bytes of the index nodes that the
   transaction made dirty before this put, each at its size when it got
   dirty. The row is the last call on its key, so it replaces a rewrite
   of that key.
4. **The touch** (024-07): before the puts, every index node on the path
   of each key of the transaction at its time, from the top node down to
   the segment leaf that holds the key's entry or would, becomes dirty;
   these marks stay even when a put then replaces the node. No other
   node is touched.
5. **Commit.** A conflict, which the write lock rules out (argued),
   would drop the step; the same step would come at a later call.
6. **The end.** After the last step: done := true; tEnd := its time;
   pEnd := its record's position; the table is stored.

Why the cut loses no value (REWRITES; argued, 026-05, section 3.1): a
value stored before pCut that a lookup at a time t >= tEnd reads was
written at or before tStart (every record before pStart was), and its
key had no write until t, so it was live with that value from tStart to
t. Its key is then at most E; the steps' ranges join and cover every key
up to E; and the step whose range holds the key met it live at its own
time and put it again before tEnd. The index nodes need no touch of a
key range (024-07, section 4): each one a lookup reaches has a live key
below it, but an empty space root (LIVEBELOW, part 4's delete path), and
that key's put after pCut, the user's or a step's, made it dirty; the
space root is on the path of every step's row.

### 1.5. The safe positions

markSafe(): for every done row with pSafe unknown and sp >= pEnd, pSafe
:= the stream length now, after the records this call has appended
(015-54); if a row changed, the table is stored. sp >= pEnd means every
node the steps made dirty is written; the wait for sp >= pSafe then
writes once more the nodes written before their children and kept in D
by Rule A, so that they name the children's new positions.

### 1.6. The cut's decision

decideCut(now), with now the user transaction's time, or the call's time
in `maintain()` (1.10). A row is a candidate if it is done, now - R >
tEnd, pSafe is known and sp >= pSafe, mp >= pCut, and pCut > fp. Of the
candidates, C is the one with the largest pStart. If there is none, or C
is cut already, nothing happens. Otherwise:

1. the rows with pStart below C's are removed, C is marked cut, and the
   table is stored;
2. fa := C.tEnd and fp := C.pCut: from here, lookups before fa are
   refused (1.8);
3. caches of what the cut makes unreadable may be dropped; Java drops
   the node ids it read below pCut and its key hashes of writes at or
   before tEnd (026-10), so a transaction that read at a time before fa
   may be rerun as a conflict;
4. a cut still pending whose table is durable is made first (1.7;
   026-05, section 2.5);
5. C.pCut becomes the pending cut, to be made when the stream is durable
   up to its length now, the end of the table just stored.

### 1.7. The physical cut

makeCutIfDurable(): if a cut is pending and the stream is durable up to
its mark, the storage drops the stream before pCut, and nothing is
pending. The storage may keep more: a file storage drops whole files
(027-03, section 4). A read below the storage's first position fails with
an error of its own. Durable first, so that a crash cannot lose the table
that marks the cut once the front is gone.

### 1.8. Reads and the retention

* A get or a scan with a lookup time below fa is refused: the lookup
  time is not available. So is a transaction asked for by a position
  whose bytes the storage has dropped.
* A read admitted before a cut that meets bytes below the storage's
  first position, and whose actual lookup time is now below fa, expires
  with the same exception; the database goes on (011-04, W1, D1 = A).
  Any other read below the first position fails the database.
* Each cut keeps the duration in force when it is decided: fa = tEnd <
  now - R then. fa never moves back, and a larger R does not bring back
  what was cut. R may change at any time (011-04, W2). Set to forever
  while an iteration runs, it runs to its end; no cut and no iteration
  follow until R is finite again.

### 1.9. A start

A start reads the settings, the table, and the current row, which
replaces the table's row with the same pStart if neither is done. The
newest row marked cut gives fa := its tEnd and fp := its pCut (0 and 0
without one). If the storage's first position is below fp, the cut is
made now: a crash came between the table and the cut. Nothing else is
kept, so a restart does not change what reclaim writes (INV-RESTART).
Startup on a cut stream is part 7's (rule 4 by position skips the
pointers below the first position).

### 1.10. maintain()

An optional call (024-32; Frans, 023-04, Y10), under the write lock,
refused as a user transaction is (an inactive database, the top node
ordinals used, no user time left), and then nothing is written. With now
the call's time, in internal transactions, at most once each, in order:

* **M1**: if R is finite, no iteration runs, now - lastTStart >= R div 4,
  no done row waits for its cut (not cut, pCut > fp), and the new
  iteration's pCut (lastPStart; the stream length for the first) is at
  least MIN_RELEASE after fp: begin(pStart = the stream length, tStart =
  the time of the last transaction), with E at that time. No condition
  on the stream's growth.
* **M2**: step(it, MAX_STEP) if an iteration runs, without the
  allowance.
* **M3**: markSafe().
* **M4**: of the rows waiting for their cut whose wait position (pEnd
  while pSafe is unknown, then pSafe) is after sp, the least such
  position, if any: an empty internal transaction whose take writes,
  beyond its share, more of D oldest first, up to it, at most TAKE_MORE
  bytes of index nodes (part 6). Then markSafe() again.
* **M5**: if a row meets every condition of 1.6 but mp >= pCut: a
  filler, a put of `/#i/dreclaim/-fill.txt` with max(1, META - L mod
  META) zero bytes (L the stream length), then its delete, two
  transactions, so that a meta block names a transaction at or after
  pCut.
* **M6**: decideCut(now), makeCutIfDurable().

Then, if a cut is pending and not durable, a sync outside the lock, and
the cut; and one batch of eviction's dead hand (part 8). The call returns
whether more is due now: an iteration runs, an M4 or M5 is due, a cut is
pending, M1's condition holds, or the dead hand has more.


## 2. State

* **In memory**: R and f; the table's rows; fa and fp, which readers read
  without the write lock; the pending cut and its mark; RESERVE.
* **In the stream**: the three KVs of 1.1, and the filler of 1.10, never
  live after a call (027-03, section 15: the texts; the row is read
  leniently, the settings strictly). Reclaim's transactions are ordinary
  records (027-03, section 8): a step's holds its puts, its row and the
  got-dirty ids of its touch and puts. Nothing of a scan is stored; E is
  stored with the row.


## 3. Invariants

* **INV-RECLAIM** (011-01): from fa on, lookups give what they gave
  before the cut. Proved in the model for a safe cut (`CutOK`: T8, T9);
  that Java's cuts are safe is checked (T-SCHEME, below).
* **REWRITES** (1.4): argued; checked (C-CUT's part 2); gated
  (`testIterationRewritesAllOldValues`, `testStepScansAtItsOwnTime`,
  `testEndKeyBoundsTheScan`).
* **LIVEBELOW** (part 4): checked at every cut (C-CUT, `CUT-live`);
  gated (UnlinkFuzz in the night).
* **COVER** and **LATEST**: from REWRITES and LIVEBELOW, every node
  reachable from tEnd on has its latest version at pCut or later once sp
  >= pEnd. Proved (`T_cover`, `T_latest`).
* **T-SCHEME**: Java's waits (1.5, 1.6) give `CutOK`. Checked: C-CUT at
  every cut of every reclaim trace (026-05: 0 of 794 cuts failing in
  level3's set, 0 of 479 in its own traces), and in the model by running
  (`checkSchemeC`). Not proved: open.
* **The touch on the paths** (`TouchOnPaths`): checked (C-A,
  `touchPath`); gated (`testStepDirtiesItsPathsOnly`).
* **INV-RESTART**: a run with restarts writes the stream of the run
  without them, the same cuts too. Proved in the model (`T12_restartCut`,
  `T12_handles`); gated (RestartInvariance with reclaim, `level3.sh`).
* **Retention** (1.8): argued; gated (ReclaimRetentionTester,
  ReclaimStress).
* **Crash**: the table is durable before the physical cut. Gated
  (`testCutIsMadeAfterDecisionIsDurable`, CrashTest, PowerLossTest).
* **Readers**: a read that a cut overtakes expires and never fails the
  database. Gated (ReclaimReaderTester, ReclaimReaders).


## 4. Costs and bounds

* **A step**: at most one a user transaction, and one a `maintain()`
  call. It counts at most MAX_STEP bytes of KVs stored before pStart and
  one KV more; it walks the KVs put since pStart up to the reserve (about
  2,759 index nodes at the default node size, 026-05). Argued.
* **A step's values**: within the value limit, unless it is one KV.
  Argued; gated (`testStepWithinValueLimit`,
  `testLastStepWithinRecordLimit`).
* **A step's dirty nodes** (024-07, B1; 024-05, BD7): at most 3 h s + 3
  a put, h a segment tree's height, s the key's segments. Argued; gated
  (`testStepDirtiesItsPathsOnly`); checked (`touchPath`).
* **Internal transactions after a user transaction**: at most five (the
  table at a start, a step, the table at an end, the safe positions, the
  cut). Argued (`Db`'s margin of 1,024 top node ordinals).
* **An iteration's rewrites**: at most f of the stream's growth since
  pStart, through the allowance, unless paced by MAX_STEP, R div 4 or 2
  sd (024-29, section 4.2). Argued. Reclaim wrote 26 to 38 percent of all
  stream bytes at f = 1/4: measured (011-04, W4).
* **An iteration's length**: at most (the KV bytes live at tStart) /
  MAX_STEP steps, whatever the user puts ahead of the scan. Argued
  (026-05, section 2.3); a chase at the reserve: open (section 9).
* **The stream kept** (BD10, G3): less the user's records within R, at
  most 6 times a fresh twin's stream. Gated (`count-gates.sh`, night;
  4.401 measured, 026-05). Its form, G(R) + j W: argued (024-29); not
  derived: open (017-04).
* **Back to empty** (G4): kept, key nodes, heap and the rest at most 2
  times the twin's; the lag at most 2 R transactions (026-11). Gated;
  1,265 to 1,286 measured at 1M to 10M keys and every f (026-05). G5,
  the same by `maintain()` calls: gated.
* **The largest record** with reclaim on (G1, BD1): at most the larger of
  1 MB and 5 times the mean. Gated.
* **A `maintain()` call**: one step, TAKE_MORE beyond one transaction's
  take, a filler below META. Argued; gated (ReclaimMaintainTester).
* **Pauses** (P1): the physical cut waits for the storage's append in
  progress, 19.85 ms at the longest on s1 (015-80, 019-36): measured.
  The forget of 1.6, step 3: 0.3 to 6 ms (026-10): measured.
* **The disk**: whole files, 6 to 9 percent more than the stream kept.
  Measured (011-04, W5d).


## 5. In the model

* **Definitions** (lean/SIS/Reclaim.lean, trusted): `Version.stub`,
  `Record.cut` and `cutStream c S` (the records before c keep stubs:
  node, record number, no history); `ReadsAt` and `ReadsPhys` (the
  versions a lookup, or a read in the running process, may follow);
  `CutOK` (c <= f; every version a read from f on may follow is at c or
  later; every node of D has its latest version at c or later, with
  references below c to latest versions only; the top at c or later);
  `SameFrom`, `ExecRootOK`, `VirtLiveOK`, `PolicyCutOK`,
  `runRestartsCut`. The touch is `Changes.touch`; f is `Record.fa`.
  `TouchOnPaths` in ReclaimTheorems.lean; `runHandlesCut` and
  `runHandlesCutPos` in HandleReclaimTheorems.lean.
* **Proved** (lean/SIS/Proof/, the Cut and HandleCut files):
  * T13' (`T13_markTouch`): with touches, step 3 marks exactly the index
    nodes not in D that are dirty or touched;
  * T-COVER (`T_cover`): at an iteration's end e, if every reachable
    data node is at c or later and every reachable index node has a data
    node below it, every reachable index node is in D or at c or later;
  * T-LATEST (`T_latest`): with the same premises, in every later state
    whose startup pos is at e or later, every node reachable from e on
    has its latest version at c or later;
  * T8 (`T8_recoverCut`): after a safe cut, a startup from the cut
    stream gives the same lookups from f on, and the same D;
  * T9 (`T9_handles`): reads through the handles from f on give the same
    on the cut stream as on the whole one;
  * T12 (`T12_restartCut`; with eviction `T12_handles`): a run that
    restarts from safe cut streams appends the records of the run
    without restarts;
  * `Rule4PosCut_handles`, `RunPosCut_handles` (005-62): Java's rule 4
    by position after a cut is rule 4 by node id.
* **Assumptions**: `RunOK` (A2 to A5, TREE), Java's still-dirty test and
  marking, `LiveAppend`, `EvictRunOK`; for T8 and T12 `ExecRootOK`,
  `VirtLiveOK`, `PolicyCutOK`.
* **Stated, not proved**: nothing. T-SCHEME has no statement; it is
  checked by running (`checkSchemeC` in SIS/ReclaimExample.lean, `lake
  exe reclaimtest`, with and without a touch; 024-07, section 4.3).
* **Left out**: keys, the scan and E, R and the times, the table, the
  allowance and the step sizes, the durable wait, the storage's files,
  reads in flight, `maintain()` (its transactions are records like any),
  the settings. REWRITES and LIVEBELOW are Java's premises.
* **Conformance** (027-02: `TOUCH`, `FA`, `CUT`, `PHYSCUT`;
  lean/Check/Steps.lean): C-A (TouchOK, `touchPath`), C-S (the model's
  step against Java's records and D on the cut stream), C-CUT (`CutOK`
  at every cut Java decides, with `CUT-live`), C-L (the first touches
  after restarts from the cut stream); C-P and C-H with eviction.


## 6. In Java

* `core/Reclaim`: `transactionCompleted` (1.2), `lastKeyAt` (E), `step`
  (1.4), `markSafePositions` (1.5), `pretruncateIfPossible` (1.6),
  `cutIfDurable` (1.7), `initFromDb` (1.9), `maintain` (1.10),
  `setSettings`, `fractionOf`, `IterationInfo` and `IterationTable` (the
  rows); the class comment.
* `core/Db`: `executeInner` (calls `transactionCompleted` in the go
  point); `putKvs` and `touchPaths` (the touch, by `Dag.followPath`);
  `makeDirtyIfNeeded` (a step's dirty bytes); `cutDecided`
  (`NodeCollection.forgetIdsBelow`, `KeyModSet.forgetUpTo`); `maintain`;
  `setRetainDuration`, `setReclaimInternalFraction`;
  `expiredIfReadBelowCut`; the take's `maintainTakeTo`
  (`TransSeq.takeTo`).
* `dag/GetMany` (`endKey`, the stop conditions); the step reads through
  `NodeCollection.MaintenanceFollower`, which keeps nothing in memory.
* `stream`: `AppendOnlyStream.pretruncate`, `FileStream` (whole files),
  `CutStream` (exact, for tests), `ReadBelowFirstPosException`.
* The Pub API: `Database.setRetainDuration`, `Database.maintain`; no
  setter of f (024-29).
* The C clone (012) has release 2026.2's reclaim (`reclaim.c`), before
  024-07, 024-32, 024-34 and 026-05; it does not follow this part.


## 7. Tests

* **Unit tests**, gated by `before-commit.sh`: `Reclaim`'s (38; among
  them the steps' `testStepScansAtItsOwnTime`,
  `testEndKeyBoundsTheScan`, `testQueueBeforeAKeyEnds`,
  `testRandomPutsAheadDoNotSlowTheScan`, `testAllowanceCountsIndexNodes`,
  `testStepReserveSplitsSteps`; the cut's `testPretruncate`,
  `testSafePosAfterTheCallsRecords`, `testCutKeepsMetaBlockTransaction`,
  `testEmptiedSubtreesAfterCut`; the restarts' `testRestartAfterCut`,
  `testCrashBeforeIterationEnd`, `testRestartResumesIteration`);
  ReclaimRetentionTester (7, R changed); ReclaimReaderTester (8);
  ReclaimMaintainTester (4); DbTesterRestart's
  `testReclaimSettingsKeptOverRestarts` and
  `testMalformedSettingsRefusedAtStart`.
* **`level3.sh`** (night, full): ReclaimStress, RestartInvariance with
  reclaim, CrashTest, ReclaimReaders, LoadTest with a check after every
  cut, PowerLossTest, the conformance's reclaim set, InterruptStress.
* **The night** also: `count-gates.sh` (G1, G3, G4 with its lag, G5),
  the conformance's `drain` set, `lean-tests.sh` (reclaimtest),
  UnlinkFuzz.
* By hand: ReclaimCost (`Reclaim.Stats`), FracRuns (026-04).


## 8. Principles and rules

* **P1**, no stop-the-world: a step is bounded by its paths (024-07). A
  deviation: the physical cut waits for the storage's append (015-80).
* **P2**, a deterministic stream: R and f are in the stream (015-87);
  `maintain()` writes as its calls and their times decide. RESERVE is
  not in the stream: a test setting, below its default only.
* **P3**, calm when not used: reclaim works at the user's commits and
  `maintain()` calls only, so a quiet database keeps its stream until
  either comes.
* **P4**, maintenance proportional to the user's work: one step a
  commit, within f of the growth and MAX_STEP of scan; a step's uncounted
  walk (1.4) is bounded by the reserve only.
* **P10**, few settings: R and f; the Pub API sets R only.
* **P12**: reclaim treats every key and value as bytes, BergDB's own
  too; its own keys are reserved, and a caller's put there is refused
  (024-37, CA3; 010-04, R5).
* **R1**: a refused setter call or `maintain()` call changes nothing.


## 9. Limits and open work

* T-SCHEME is checked, not proved; 001-07's register rows M32, M33, M36,
  M41 and M48 are argued or checked. REWRITES and LIVEBELOW are argued
  for Java; the tree model (024-12) could make them theorems.
* 026-09, a keys-only scan (024-34, Q34-1, option b): registered for
  2026.6, not on `main`. Today a step loads the value of every KV it
  walks, also those it does not rewrite (43 percent of its loads at 1M
  keys with a 20 MB cache, 024-34).
* A chase at the reserve: a user who puts, ahead of the scan and before
  E, more than a reserve's worth of index nodes in every transaction
  keeps an iteration going (026-05, section 7). Not seen.
* Work ahead of an ascending mass delete: up to 12 percent more stream
  written (026-05, section 6; accepted, its Q3).
* f's three recommended values and one default: 026-04, open.
* The bounds on the stream kept and the lag (BD8, BD10) are measured and
  gated, not derived (017-04).
* Protected long-lived reads, which a cut would wait for (D1 = B): not
  built.
* The row's text: Java's `HashMap` line order, a lenient parser, no
  version (027-03, G16 and Q9; 026-12). A row of 2026.5 or before has no
  E: its scan is bounded by the count only.


## 10. Evidence

* 001-07: Level 3 in Lean, the alignment, T-SCHEME's argument (section
  5) and the register. 001-09: the two-hour soak on disk.
* 011-04: the rework of 2026-10-13, "Level 3 cost", W1 to W5.
* 015-50: a step within the value limit. 015-54: pSafe after the call's
  records. 015-80, 019-36: the cut's wait. 015-87: the settings kept.
* 023-05, P8, and 023-08 (fault 13, check V8): the scan at a step's time.
* 024-07: the last touch, T-COVER, T-LATEST, the bounds B1 to B4.
* 024-29, 026-04: the fraction and the lag's mechanism.
* 024-30, 026-11: the count gates and G4's lag.
* 024-32: `maintain()`. 024-34: reads only what it rewrites (OP8).
* 026-05: each step at its own time, E, the count, the pending cut.
* 026-10: the forget at a decided cut.


Note for the reviewer
=====================

Where the code on `main` (0870e7ea) and a text disagree; the code was
taken as right:

1. 027-01's `levels.md`, section 6: a step scans at tStart and reads a KV
   again; since 026-05 it scans at its own time and the scan gives the
   values.
2. `Reclaim`'s class comment: an iteration starts when the stream has
   grown "by twice" sd; the code asks for more than twice. A step comes
   when the bytes are "below" f of the growth; the code asks for an
   allowance above MIN_STEP, and a step of min(allowance, MAX_STEP).
3. `Reclaim.pretruncateIfPossible`'s Javadoc cuts "at the pStart" of an
   iteration that "starts at or before" mp's transaction; the code cuts
   at pCut and asks mp >= pCut (the Javadoc is older than pCut).
4. `IterationInfo.kvCount`'s comment, "total number of KVs in the
   database for the iteration lookup time": since 026-05, the KVs that
   the steps' ranges covered.
5. `Db.maintain`'s Javadoc begins an iteration when "the last one is
   cut"; the code asks that no done row waits for its cut (pCut > fp),
   so a done row with pCut <= fp does not block.
6. 027-03, section 15: its table of keys lacks `/#i/dreclaim/-fill.txt`
   (024-32), and says a step's touch writes `-current.txt` (it is the
   row every step puts). Its Q8 (section 20) says E needs Q9 first; E
   landed with 026-05 without it.
7. 026-11's status and its line in 026's readme say "on the branch, to
   land"; it is on `main` (fe947c7c). 026-10's line in 026's readme says
   "Code on branch"; merged (e4ac051f).
8. The brief put 026-09 on a branch; its item says registered, and no
   branch of that name is in the main repository.

First to check: 1.4's accounting (what counts toward size, rewritten and
the row's dirty bytes), which a second implementation must match byte
for byte; and 1.6's conditions against `pretruncateIfPossible` and
`cutWaitsForMetaBlock`.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-13. The draft, the pilot part (Frans, 11:34, "Yes" to the
reclaim pilot), from the code at 0870e7ea, the Lean files and the items
of section 10. By an agent of coord-1113.
