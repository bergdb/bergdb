# 027-13. Reclaim

Created 2026-11-13 by Frans Lundberg. Status: read by Frans (2026-11-13,
12:34: "027-13 is good! I looks really good."); the pilot part of 027-04,
section 5.1, step 3, and the template for the other parts.

Part 9 of 027 (027-04, section 2.3; Level 3): how the front of the stream
is cut. The rule as `main` has it at 03f38f24 (2026-11-13; `java/` and
`lean/` as at 1a53e45c), read from the code. It replaces 027-01's
`levels.md`, section 6, and `sis-model.md`, section 15.3, both stale
since 026-05 (there a step scans at tStart and reads each KV again). The
bytes are 027-03's; the take, D, Rule A and the startup pos are part 6's
(until it is written, 027-01's `sis-model.md`, sections 5 and 6). Each
claim carries one status word of 027-04, section 2.2.


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
* **Kept in the stream**, in the KV `/#i/dreclaim/-settings.txt`, the
  exact text `retain=R\nfraction=f\n` (027-03, section 15); without it
  the defaults hold. A call that sets R or f refuses a value out of range
  before it writes anything; with the values in force it writes nothing;
  otherwise it commits one internal transaction with the KV, and the new
  values hold from the next transaction.
* **sd**, the startup distance in force; **sp**, the startup pos that the
  take set for the last record written, which that record stores (after a
  start, the one read from the last record); **mp**, the position of the
  transaction that the last valid meta block names (027-03, section 6),
  where recovery starts; **fa** and **fp**, the first available lookup
  time and position, 0 until the first cut.
* **The table**: one row an iteration, in `/#i/dreclaim/-table.txt`; the
  row of the iteration in progress also in `/#i/dreclaim/-current.txt`,
  as its last step left it. A row: pStart, tStart, pCut, E (the end key),
  lastKey, kvCount, rewritten, done, tEnd, pEnd, pSafe, cut. The current
  iteration is the table's last row if it is not done.
* **Internal transactions.** Reclaim writes only in transactions of its
  own, each with its own time; user transactions are refused in the last
  1,024 times and top node ordinals, kept for them. Reclaim reacts to
  user transactions only.
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

step(it, W) is one internal transaction, at its own time ts:

1. **The scan** (since 026-05): the live KVs at the latest state (the
   last commit's time, just before ts), forward from the first key after
   lastKey (from the first key if none), up to E inclusive. Every row
   has E: a row without it is refused as damaged (`IterationInfo.deserialize`,
   since 028-15). Such a row, stored before 026-05 by 2026.5 or earlier,
   was scanned to the last key until 028-15, and is in a stream of meta
   version 154, which a start refuses first (027-03, section 6). If E is
   none, or lastKey is at or after E, there is no scan, and this step is
   the last.
2. **Each KV met**, in key order, with p its value node's position (none
   if not yet written), s its key's segments and v its value's bytes:
   * rewrite := p < pCut;
   * if rewrite, and the step holds a KV to rewrite already, and their
     value nodes with this one's would pass the value limit (7/8 of the
     record limit, 027-03, section 8.3; a value node is 32 + 8 s + v
     bytes, rounded up to a multiple of 4): stop before this KV, which is
     the next step's first;
   * lastKey := its key; kvCount += 1;
   * if p < pStart: size += 8 s + v + 100; only these KVs count (023-08,
     fault 13);
   * stop after this KV if the scan has followed more than max(1,
     RESERVE div NB) distinct index nodes (the step is split), or else if
     size > W;
   * keep it if rewrite; walk past it otherwise.

   If the scan passes E or the last key without a stop, this step is the
   last.
3. **The transaction**: the KVs kept and the row, one KV a key, applied
   in key order.
   * **The touch** (024-07), first: every index node on the path at ts of
     each of its keys that is not dirty becomes dirty. A path is the super
     root, the space root and, in each segment's tree, the nodes down to
     the segment leaf of the key's segment, or to where no key has the
     segment. These marks stay even when a put then replaces the node. No
     other node is touched.
   * **The rewrites**: for each KV kept, a put of the same key and value,
     with a read of the key at the scan's time; rewritten += 8 s + v + VN
     each.
   * **The row**, at `-current.txt`, in its place in key order: it with
     the new lastKey, kvCount and rewritten, plus the dirty bytes: the
     stored size of each index node that the step's touch made dirty, each
     at its size when it got dirty, also if a put then replaces it
     (`Trans.dirtiedBytes`, read by the row's value transformation). The
     transformation runs before the writer applies any of the
     transaction's operations, which it gets as one batch (record format
     8, 026-25), so nodes dirty before the step are not counted, and
     those that the puts make dirty are counted after the commit (4b).
     Until format 8 the operations were applied one by one in key order,
     the row counted the nodes that the rewrites of keys before the row's
     key made dirty, and those after it were never counted.
     The row is the last call on its key: it replaces a rewrite of that
     key, whose bytes stay counted.
4. **Commit.** A step cannot conflict: the scan and the commit hold the
   write lock, so no key is written after the scan's time (argued; no
   test). A step that conflicted would be dropped, to come again at a
   later call.

   4b. **The row again** (028-26). rewritten += the bytes of the index
   nodes that the transaction made dirty after the row was made: its
   `Trans.dirtiedBytes` at the end less those the row counted, which are
   PE's new nodes (replacements, cuts, joins, a new top node), each at
   its size when it got dirty. If they are more than 0 and this step is
   not the last, the row is stored again at `-current.txt`, in an
   internal transaction of its own; after the last step, the table of 5
   holds them. So, after every call, the row in the stream is the row in
   memory, and a restart resumes with the same charge (INV-RESTART).
   Why a second transaction: the row is a value of the transaction whose
   dirty bytes it counts, and PE makes a value node, with its id, when
   the plan applies its operation at its segment leaf, before nodes that
   the row would count are made (026-25, section 2, "The ids"); a count
   carried in memory to the next step's row is lost at a restart, which
   then paces the steps otherwise (028-26 tried it:
   `testReclaimSettingsKeptOverRestarts` failed). The bytes that the
   second transaction makes dirty are not counted, as those of the
   table's transactions are not; a crash between the two transactions
   loses the step's new nodes from the charge. Until 028-26 they were
   counted nowhere (Codex's review of PE, 2026-11-19, finding 1).
5. **The end.** After the last step: done := true; tEnd := ts; pEnd :=
   the step's record's position; the table is stored, in a transaction of
   its own.

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
is cut already, nothing happens. Otherwise, in this order:

1. the rows with pStart below C's are removed, C is marked cut, and the
   table is stored;
2. fa := C.tEnd and fp := C.pCut: from here, lookups before fa are
   refused (1.8);
3. caches of what the cut makes unreadable may be dropped (Java: the
   node ids read below pCut, the key hashes of writes at or before tEnd;
   026-10), so a transaction that read before fa may be rerun;
4. a cut still pending whose table is durable is made first (1.7;
   026-05, section 2.5);
5. C.pCut becomes the pending cut, to be made when the stream is durable
   up to its length now, the end of the table just stored.

### 1.7. The physical cut

makeCutIfDurable(): if a cut is pending and the stream is durable up to
its mark, the storage drops the stream before pCut, and nothing is
pending. The storage may keep more: a file storage drops whole files
(027-03, section 4). Durable first, so that a crash cannot lose the table
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
  while an iteration runs, the iteration runs to its end and a pending
  cut is still made; no cut is decided and no iteration begins until R
  is finite again.

### 1.9. A start

A start reads the settings, the table, and the current row, which
replaces the table's row with the same pStart if neither is done. The
newest row marked cut gives fa := its tEnd and fp := its pCut (0 and 0
without one). If the storage's first position is below fp, the cut is
made now: a crash came between the table and the cut. Nothing else is
kept, so a restart does not change what reclaim writes (INV-RESTART).
Startup on a cut stream is part 7's.

### 1.10. maintain()

An optional call (024-32; Frans, 023-04, Y10), under the write lock,
refused as a user transaction is (an inactive database, the top node
ordinals used, no user time left), and then nothing is written. With now
the call's time, in internal transactions, at most once each, in order:

* **M1**: if R is finite, no iteration runs, now - lastTStart >= R div 4,
  no done row waits for its cut (not cut, pCut > fp), and a cut that the
  new iteration leads to releases at least MIN_RELEASE: its own, the
  stream from fp to its pCut (lastPStart; the stream length L for the
  first), or the next one's, at least L - tp, tp the position of the
  table's value at the latest state (where the table was last stored,
  read from the index, so that a start gives the same):
  begin(pStart = L, tStart = the time of the last transaction), with E
  at that time. No condition on the stream's growth. With no iteration
  running and no cut pending, reclaim's last record is a store of the
  table (the last iteration's end, markSafe or cut), so L - tp is what
  others wrote since: nothing in a database not written to, where this
  rule begins none. Counted from lastPStart instead, it would hold
  the last iteration's own rewrites, every live value after a first
  iteration, and the calls would rewrite them again and again in a
  database not written to (028-51 measured it). Until 028-51 only the
  first counted: once the cut iteration had its pStart within
  MIN_RELEASE of its pCut (the first, whose pCut is its pStart, or one
  begun R/4 after an iteration with nothing to cut, in a database
  written by less than MIN_RELEASE in R/4), no iteration began until
  1.2's rule of growth began one, and a database emptied after such a
  cut and not written to kept the stream of what it had deleted, below
  2 sd, for good (028-47, F1; 028-51). The first rule still begins
  iterations in a database with live values that is not written to:
  after a cut, the stretch from fp to lastPStart holds the rewrites of
  the iteration before the last, which the new one rewrites again, so
  the live values fall into two sets that the iterations rewrite in
  turn, each cut releasing the old copies of one, while both sets'
  iterations write MIN_RELEASE or more (028-53: 24.5 MB in 10 R at
  30,000 values of 100 bytes and sd 1 MB, where the overwrites had
  left the values in two such sets; a cost, no promise broken). And
  the others' writes between lastPStart and tp, made while the last
  iteration ran or waited for its cut, are counted by neither rule
  until another iteration begins: after an iteration that began within
  MIN_RELEASE of its pCut, none begins, and a database emptied then
  keeps that stream, below 2 sd (RB-007; 028-53).
* **M2**: step(it, MAX_STEP) if an iteration runs, without the allowance.
* **M3**: markSafe().
* **M4**: of the rows waiting for their cut whose wait position (pEnd
  while pSafe is unknown, then pSafe) is after sp, the least such
  position, if any: an empty internal transaction whose take, after its
  share, goes on with whole transactions of the startup section, oldest
  first, while sp is below that position: the first whatever its size,
  then each while the bytes taken (counted as the take counts them, part
  6) stay within TAKE_MORE and the record. Then markSafe() again.
* **M5**: if a row, not cut, meets every condition of 1.6 but has mp <
  pCut: a filler, a put of `/#i/dreclaim/-fill.txt` with max(1, META - L
  mod META) zero bytes (L the stream length), then its delete, two
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
* **In the stream**: the three KVs of 1.1, and the filler of 1.10,
  deleted by the call that put it; a stop or a crash between its put and
  its delete, two records, leaves it live, rewritten by the iterations as
  any live value, until the next filler's put and delete (028-59,
  2026-11-25). 027-03, section 15: the texts; the row is read
  leniently, the settings strictly. Reclaim's transactions are ordinary
  records (027-03, section 8): a step's holds its puts, its row and the
  got-dirty ids of its touch and puts; the row stored again (1.4, 4b) is
  a record of its own. Nothing of a scan is stored.


## 3. Invariants

* **INV-RECLAIM** (011-01): from fa on, lookups give what they gave
  before the cut. Proved in the model for a safe cut (`CutOK`; T8, T9);
  that Java's cuts are safe is T-SCHEME.
* **REWRITES**: every value stored before pCut that a lookup from tEnd on
  reads is rewritten. In the contract's words `IterationOK` (030-24), from
  which, with VAL-NEW, RC2 is proved (`rc2_of_iteration`). Proved since
  030-25 for steps that follow a model of 1.4 (`StepsOK`, with any stops
  before or after a KV), given VAL-NEW (`iterationOK_of_stepsOK`), by the
  argument of 026-05, section 3.1: it was written by tStart and its key had
  no write since, so the key was live from tStart on and is at most E; the
  steps' ranges cover every key up to E, and the step whose range holds it
  rewrote it. That Java's steps are the model's: checked step by step on
  the reclaim traces since 030-27 (C-STEP, on 027-02's STEP lines: each
  step against the model's step at its state, each cut against its
  iteration's last step; since 030-34 also that each rewrite writes the
  value the scan read and that the step writes nothing else than the
  rewrites and its row), and through RC2 (C-CUT's part 2); gated
  (`testIterationRewritesAllOldValues`, `testStepScansAtItsOwnTime`,
  `testEndKeyBoundsTheScan`).
* **LIVEBELOW** (part 4): each index node a lookup reaches, but an empty
  space root, has a live key below it, and that key's last put (the
  user's at pCut or later, or a step's rewrite) made the node dirty; so
  no key range needs a touch, and the space root is on every step's
  row's path (024-07, section 4). It rests on the writer: since record
  format 8 PE drops every child left empty and every empty segment tree,
  and collapses a root of one entry (`PeWriter.rebalance`, `settleRoot`;
  026-25), as the upward unlink and root collapse did in formats 6 and 7.
  Checked at every cut (C-CUT, `CUT-live`); gated (UnlinkFuzz,
  `testEmptiedSubtreesAfterCut`, `testDeletedKeysAfterCut`).
  Proved from the writer's contract, given a live key at tEnd
  (`rc3_tree`, 030-24).
* **COVER**, **LATEST**: with REWRITES and LIVEBELOW, every node
  reachable from tEnd on has its latest version at pCut or later once sp
  >= pEnd. Proved in the model (`T_cover`, `T_latest`).
* **T-SCHEME**: Java's waits (1.5, 1.6) give `CutOK`. Checked: C-CUT at
  every cut of every reclaim trace (026-05: 0 of 794 failing in level3's
  set, 0 of 479 in its own), and `checkSchemeC`; C-CUT checks reclaim's
  contract RC (030-22) at every cut too (`RC1-order`, `RC2-rewrites`,
  `RC4-waits`; RC3 is `CUT-live`; 030-23). Proved since 030-24 for runs
  with A6' (BergDB's tree): RC gives `CutOK` (`cutOK_of_rc`; part 2 needs
  only the first wait, part 3 the second). `TScheme` as 030-23 stated it,
  for every run with RunOK, is false (`AdoptionExample.tscheme_false`).
  RC3 for the key tree from the writer's contract (`rc3_tree`); RC2 from
  the iteration (`IterationOK`: every key whose value node predates pCut is
  written again from the iteration's first step to tEnd) and VAL-NEW, which
  PE meets (`rc2_of_iteration`, `PE.pe_valNew`). So for every history PE
  writes, Java's reads after cuts are right given `IterationOK` and RC1
  and RC4 at each cut (`PE.pe_reclaim_reads`), and given steps that follow
  the model of 1.4 in place of `IterationOK` (`PE.pe_reclaim_reads_steps`,
  030-25).
* **The touch on the paths** (`TouchOnPaths`): checked (C-A,
  `touchPath`); gated (`testStepDirtiesItsPathsOnly`). **No conflict in
  a step** (1.4): argued; no test.
* **INV-RESTART**: a run with restarts writes the stream and the cuts of
  the run without them. Proved in the model for safe cuts
  (`T12_restartCut`, `T12_handles`); gated (RestartInvariance, level3).
* **Retention** (1.8): argued; gated (ReclaimRetentionTester,
  ReclaimStress). **Crash**, the table durable before the cut: gated
  (`testCutIsMadeAfterDecisionIsDurable`, CrashTest, PowerLossTest).
  **Readers**, a read that a cut overtakes expires: gated
  (ReclaimReaderTester, ReclaimReaders).


## 4. Costs and bounds

* **A step** (one a commit, one a `maintain()` call) counts at most W
  bytes of KVs stored before pStart and one KV more, and walks those put
  since up to the reserve (about 2,759 index nodes at the default node
  size, 026-05): argued. Its values: within the value limit unless it is
  one KV; argued; gated (`testStepWithinValueLimit`,
  `testLastStepWithinRecordLimit`). Its dirty nodes: at most 3 h s + 3 a
  put, h a segment tree's height (024-07, B1; 024-05, BD7); argued;
  gated (`testStepDirtiesItsPathsOnly`).
* **After a user transaction**: at most six internal transactions
  (begin, a step, the row again, the end, the safe positions, the cut);
  argued (the margin of 1,024 times and top node ordinals).
* **An iteration's rewrites**: about f of the stream's growth since
  pStart, by the allowance at commits (a step may pass it by its dirty
  bytes and one KV; `maintain()`'s steps have none), unless paced by
  MAX_STEP, R div 4 or 2 sd (024-29, section 4.2): argued; 26 to 38
  percent of all stream bytes at f = 1/4: measured (011-04, W4). The
  charge (the values put again and the index nodes made dirty) is 0.250
  of an iteration's stream at f = 1/4, with PE since 028-26 as with the
  old writer; before 028-26 PE's new nodes were left out of it, and its
  iterations ended after 24 % less stream than their work: measured at
  10M keys (028-19).
* **An iteration's length**: at most about (the counted bytes of the KVs
  live at tStart) / W steps, W from MIN_STEP to MAX_STEP, whatever the
  user puts ahead of the scan, plus steps that the value limit or the
  reserve ends early: argued (026-05, section 2.3, says / MAX_STEP).
* **The stream kept** (BD10, G3), less the user's records within R: at
  most 6 times a fresh twin's; gated (`count-gates.sh`); 4.401 measured
  (026-05). Its form, G(R) + j W: argued (024-29), not derived (017-04).
* **Back to empty** (G4): kept, key nodes, heap and the rest at most 2
  times the twin's, the lag at most 2 R (2,000 transactions in G4's
  workload, 026-11): gated; the lag 1,265 to 1,286 transactions at 1M to
  10M keys and every f: measured (026-05). G5, by `maintain()`: gated.
* **The largest record** with reclaim on (G1, BD1): at most the larger
  of 1 MB and 5 times the mean; gated. **A `maintain()` call**: one
  step, TAKE_MORE beyond its first taken transaction, a filler of at
  most META bytes; argued; gated (ReclaimMaintainTester).
* **Pauses** (P1): the physical cut waits for the storage's append in
  progress, 19.85 ms at the longest on s1 (015-80, 019-36); 1.6's forget
  0.3 to 6 ms (026-10): measured. **The disk**: whole files, 6 to 9
  percent more than the stream kept: measured (011-04, W5d).


## 5. In the model

* **Definitions** (lean/SIS/Reclaim.lean, trusted): `cutStream` (the
  records before c keep stubs), `ReadsAt` and `ReadsPhys` (what a lookup,
  or a read in the running process, may follow), `CutOK` (c <= fa; all
  that a read from fa on may follow at c or later; each node of D with
  its latest version at c or later, its references below c naming latest
  versions; the top at c or later), `SameFrom`, `ExecRootOK`,
  `VirtLiveOK`, `PolicyCutOK`, `runRestartsCut`, `Changes.touch`,
  `Record.fa` (fa); `TouchOnPaths`, `runHandlesCut`, `runHandlesCutPos`.
* **Proved** (stated in ReclaimTheorems.lean and
  HandleReclaimTheorems.lean, proofs in lean/SIS/Proof/): T13'
  (`T13_markTouch`): step 3 marks exactly the index nodes not in D that
  are dirty or touched. T-COVER (`T_cover`): at an iteration's end e,
  with every reachable data node at c or later and a data node below
  every reachable index node, every reachable index node is in D or at c
  or later. T-LATEST (`T_latest`): with the same premises, in every
  later state with its startup pos at e or later, every node reachable
  from e on has its latest version at c or later. T8 (`T8_recoverCut`)
  and T9 (`T9_handles`): a startup from, and reads through the handles
  on, a safely cut stream give the same lookups from fa on (and T8 the
  same D). T12 (`T12_restartCut`, with eviction `T12_handles`): a run
  that restarts from safe cut streams appends the records of the run
  without restarts. `Rule4PosCut_handles`, `RunPosCut_handles` (005-62):
  rule 4 by position after a cut is rule 4 by node id; the statements
  and their proof are at the tag `proofs-2026-11-17` since 2026-11-18
  (030-18).
* **Assumptions**: `RunOK` (A2 to A5, TREE), Java's still-dirty test and
  marking, `LiveAppend`, `EvictRunOK`; for T8 and T12 `ExecRootOK`,
  `VirtLiveOK`, `PolicyCutOK`. REWRITES and LIVEBELOW are premises.
  **Proved** in lean/contract since 030-24: T-SCHEME for runs with A6'
  and its use, as above (Contract/ReclaimScheme.lean, ReclaimReads.lean,
  ReclaimTree.lean); since 030-25 REWRITES from a model of the steps,
  with the scan and E (ReclaimSteps.lean). Also checked by running
  (`checkSchemeC` in SIS/ReclaimExample.lean, `lake exe reclaimtest`;
  024-07, section 4.3).
* **Left out**: keys, the scan and E, R and the times, the table, the
  allowance and the step sizes, the durable wait, the storage's files,
  reads in flight, `maintain()` (its records are like any), the settings.
* **Conformance** (027-02's `TOUCH`, `FA`, `CUT`, `PHYSCUT`, `STEP`;
  Check/Steps and TraceCheck.lean): C-A (TouchOK, `touchPath`), C-S (the
  model's step against Java's records, D on the cut stream), C-CUT
  (`CutOK` at every cut Java decides; `CUT-live`; RC, 030-23), C-STEP
  (each step of reclaim against the model of the steps, `StepsOK`, and
  each cut against its iteration's last step; 030-27; the values written
  back and the step's other operations, 030-34), C-L (the first
  touches after restarts); C-P and C-H with eviction.


## 6. In Java

* `core/Reclaim`: `transactionCompleted` (1.2), `lastKeyAt` (E), `step`
  and `storeCurrent` (1.4), `markSafePositions` (1.5), `pretruncateIfPossible` (1.6),
  `cutIfDurable` (1.7), `initFromDb` (1.9), `maintain` and its
  conditions (1.10; `maintainBeginDue`, `tablePos`), `setSettings`,
  `fractionOf`, `IterationInfo`, `IterationTable`; the class comment.
* `core/Db`: `executeInner`, `putKvs`, `touchPaths`, `makeDirtyIfNeeded`
  (`Trans.dirtiedBytes`), `cutDecided`, `maintain`, `store` (M4,
  `TransSeq.takeTo`), `expiredIfReadBelowCut`, the setters; `KeyModSet`
  (a step's read time, the latest, is never before its first bin, so no
  conflict); `DbClock` (the 1,024 times kept); `dag/GetMany` (`endKey`);
  `NodeCollection.MaintenanceFollower` (a step's reads, kept nowhere);
  `stream`: `AppendOnlyStream.pretruncate`, `FileStream`, `CutStream`,
  `ReadBelowFirstPosException`.
* The Pub API: `Database.setRetainDuration`, `Database.maintain`; no
  setter of f (024-29). The C clone (012) has release 2026.2's reclaim
  (`reclaim.c`), before 024-07, 024-32, 024-34 and 026-05.


## 7. Tests

* **Gated by `before-commit.sh`**: `Reclaim`'s 39 tests, among them
  section 3's and `testAllowanceCountsIndexNodes`,
  `testAllowanceCountsNodesMadeAfterTheRow` (028-26: 4b's charge, in
  memory and as stored, at node sizes 8 and 30),
  `testStepReserveSplitsSteps`, `testQueueBeforeAKeyEnds`,
  `testCutKeepsMetaBlockTransaction`, `testRestartResumesIteration`;
  ReclaimRetentionTester (7),
  ReclaimReaderTester (8), ReclaimMaintainTester (7; 028-51's
  `testSlowlyWritten`, `testEmptiedAgainAfterACut` and
  `testLiveDatabaseQuiet`); two of
  DbTesterRestart's (`testReclaimSettingsKeptOverRestarts`,
  `testMalformedSettingsRefusedAtStart`).
* **In the night**: `level3.sh` (ReclaimStress, RestartInvariance,
  CrashTest, ReclaimReaders, LoadTest with a restart and a check after
  every cut, PowerLossTest, the conformance's reclaim set,
  InterruptStress); `count-gates.sh` (G1, G3, G4 with its lag, G5); the
  conformance's `drain` set; `lean-tests.sh` (reclaimtest); UnlinkFuzz.
  By hand: ReclaimCost (`Reclaim.Stats`); FracRuns (026-04), not on
  `main`.


## 8. Principles and rules

* **P1**, no stop-the-world: a step is bounded by its paths (024-07); a
  deviation: the physical cut waits for the storage's append (015-80).
  **P2**, a deterministic stream: R and f are in the stream (015-87);
  `maintain()` writes as its calls and their times decide; RESERVE, a
  test setting below its default only, is not in the stream.
* **P3**, calm when not used: reclaim works at commits and `maintain()`
  calls only. **P4**, maintenance proportional to the user's work: one
  step a commit, within f of the growth and MAX_STEP of scan; a step's
  uncounted walk (1.4) is bounded by the reserve only.
* **P10**, few settings: R and f; the Pub API sets R only. **P12**:
  reclaim treats every key and value as bytes, BergDB's own too; its own
  keys are reserved, and a caller's put or delete there is refused
  (024-37, CA3; 010-04, R5). **R1**: a refused setter call or
  `maintain()` call changes nothing.


## 9. Limits and open work

* T-SCHEME is proved for BergDB's tree, given RC at each cut (030-24);
  RC1 and RC4 (Java's arithmetic of the cut) are checked at every cut,
  not proved; `IterationOK` (REWRITES) is proved from a model of the
  steps (030-25); that Java's steps are the model's is checked step by
  step on the reclaim traces (C-STEP, 030-27) and gated, and its
  consequence RC2 is checked at every cut.
  001-07's register rows M32, M33, M36, M41 and M48 are argued or checked.
  A step's commit without conflict is argued for Java.
* 026-09, a keys-only scan (024-34, Q34-1, option b): registered for
  2026.6, not on `main`; today a step loads the value of every KV it
  walks (43 percent of its loads not rewritten, 1M keys, 20 MB cache).
* A chase at the reserve (026-05, section 7): puts ahead of the scan,
  before E, of more than a reserve's worth of index nodes in every
  transaction keep an iteration going; not seen. Ahead of an ascending
  mass delete, up to 12 percent more stream written (026-05, section 6;
  accepted, its Q3).
* `maintain()`'s M1 (1.10) knows from the stream's positions only, not
  where the application wrote: it rewrites the live values of a
  database not written to in two sets in turn, while both sets'
  iterations write MIN_RELEASE or more, and misses the others' writes
  between lastPStart and tp after an iteration that began within
  MIN_RELEASE of its pCut (RB-007). 028-53 holds the options (A: a mark
  of the application's writes kept with the table).
* Open: f's recommended values and default (026-04); the stream kept and
  the lag (BD8, BD10) are gated, not derived (017-04); protected
  long-lived reads that a cut would wait for (D1 = B) are not built.
* The row's text: Java's `HashMap` line order, a lenient parser, no
  version (027-03, G16, Q9; 026-12). E came with 026-05 before Q9, which
  027-03's Q8 asked for first: a reader without E (2026.5 and before)
  would ignore a row's E and drop it at its next store; since 028-15
  such a reader refuses the stream by its meta version (155) before it
  reads a row.


## 10. Evidence

001-07 (Level 3 in Lean, T-SCHEME's argument, the register); 001-09 (the
soak on disk); 011-04 (the rework of 2026-10-13, W1 to W5); 015-50 (a
step within the value limit); 015-54 (pSafe after the call's records);
015-80, 019-36 (the cut's wait); 015-87 (the settings kept); 023-05, P8,
and 023-08, fault 13 (the scan at a step's time); 024-07 (the last touch,
T-COVER, T-LATEST, B1 to B4); 024-29, 026-04 (the fraction, the lag's
mechanism); 024-30, 026-11 (the count gates, G4's lag); 024-32
(`maintain()`); 024-34 (OP8); 026-05 (each step at its own time, E, the
count, the pending cut); 026-10 (the forget at a decided cut); 028-26
(the row again, 1.4's 4b); 028-47, 028-51 (M1's second cut).


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-13. The draft, the pilot part (Frans, 11:34, "Yes" to the
reclaim pilot), from the code at 1a53e45c, the Lean files and the items
of section 10. By an agent of coord-1113.

2026-11-13. Reviewed against the code at 03f38f24 and the Lean files by
a second agent of coord-1113 (027-04, section 5.2): 1.4 (the step's
accounting made exact; its commit argued, untested), 1.8, 1.10 (M4),
sections 3, 4, 7 and 9 fixed; 1.6 matches the code. The note for the
reviewer became "For the code's comments" and a fix of 027-03, section
15; its items 7 and 8 (026's readme, 026-11's status) went to the
coordinator.

2026-11-13. Read by Frans (12:34: "027-13 is good! I looks really good."):
the pilot is accepted as the template for the other parts (027-04,
section 5.1).

2026-11-13. The comments fixed in Java (028-02).

2026-11-19. Brought up to date with PE (026-25), from the code at
`b03dcea7`: 1.4's row counts the bytes of the touch's nodes only, as
the writer gets the step's operations as one batch after the row's
value transformation; LIVEBELOW's premise now PE's drops and collapses.
By an agent of coord-1118, on the branch `027-pe`.

2026-11-19. 1.4's 4b, the row stored again with the bytes of the nodes
that PE made after it (028-26); sections 2, 4, 6, 7 and 10 with it. By
an agent of coord-1118, on the branch `028-26-reclaim-charge`.

2026-11-19. REWRITES proved from a model of 1.4's steps (030-25): section
3's REWRITES and T-SCHEME, sections 5 and 9. By an agent of coord-1118, on
the branch `030-25-iteration-ok`.

2026-11-19. Java's steps checked on the traces (030-27): section 3's
REWRITES, sections 5 and 9.

2026-11-20. 028-31: 1.4's step 1 as the code is since 028-15, every row
with E, a row without it refused; the row without E of before 026-05 as
history; section 9's reader without E refuses the stream first. By tx of coord-1120, on the branch `028-30-31-texts`.

2026-11-20. C-STEP checks the values a step writes back and that it
writes nothing else than its rewrites and its row (030-34): section 3's
REWRITES, section 9.

2026-11-24. 1.10's M1 as the code is since 028-51: a cut that the new
iteration leads to, its own or the next one's (the stream since the
table was last stored), releases MIN_RELEASE; sections 6, 7 and 10. By
an agent of lead-1124, on the branch `028-51`.

2026-11-24. 4: the charge over an iteration's stream measured, 0.250,
and what leaving out PE's new nodes did before 028-26 (028-19). By an
agent of lead-1124, on the branch `028-19`.

2026-11-25. 2: the filler stays live after a stop or a crash between its
put and its delete (028-59); until then the section said that it is
never live after a call. By an agent of lead-1125, on the branch
`028-58`.
