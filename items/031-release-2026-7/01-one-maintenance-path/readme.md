# 031-01. One maintenance path: back to empty, quiet when done

Created 2026-11-25 by Frans Lundberg. Status: open.

The design of BergDB's maintenance as one step for a commit and for
`maintain()` (026-03), together with the fix of RB-007 and of the
rewriting of live values in a database that is not written to (028-53).
A design only: nothing of it lands without Frans.


## 1. The request

Frans, 2026-11-25, 13:03: design 026-03 and 028-53's fix together,
rather than choosing between 028-53's options A, B and C on their own.
`maintain()` in the public API is not an absolute requirement; the
database's return to empty is wanted; one way into the maintenance work
would be the simpler design.

What the design is to give:

* one maintenance step that both a commit and `maintain()` call, or the
  reasons that keep two paths;
* back to empty: a database that has been emptied returns to about the
  stream of a fresh one under the calls (024-30's G5);
* quiet when done: a database not written to, with live values, stops
  writing under the calls once nothing is left to give back (028-53,
  sections 1 and 2);
* RB-007 fixed (028-53, section 3; 033);
* the stream deterministic (010-01, P2), and bounded startup (027-11).
* the effect on the Lean proofs (Frans, 13:04): which theorems, the
  model's scope (027-13, section 5; 030-25) and the contract and trace
  checkers change or stay, what new proofs the design needs or makes
  possible, and what a single step makes simpler to prove.

Sources: 026-03 (the question, the simple form with filler, the sync
inside `maintain()`, the tests to keep); 028-53 (the faults, the
options, A's design in section 8, its prototype on the branch
`028-53-a`); 024-32 (`maintain()` as built); 027-13, section 1.10 (M1);
010-01 (P2, P3, P4, P11, P13).


## 2. The design in short

Written 2026-11-25 by an agent of lead-1125, from the sources above,
028-47 and the code of `main` at `4ce8f942`, and measured on a
prototype (section 10; `prototype.diff`, the branch `031-01-proto` of
the clone c311). Nothing of it is on `main`.

* **One maintenance step.** `Reclaim.transactionCompleted` and
  `Reclaim.maintain` become one method, run after each user transaction
  and by each `maintain()` call: the same parts, in one order (section
  3). What paces a part is the call's kind: a commit's growth, as today
  byte for byte, or the application's request. The step alone writes
  the same streams as `main` (StreamDigest quick: 44 of 44 identical).
* **w, where the application wrote.** One number in reclaim's table:
  the pStart of the last iteration after whose start the application
  wrote, or -1 (section 4). The table is stored once more when w
  changes, at most once an iteration, by the step of the commit that
  changed it; a start reads w from the table, and from the stream's last
  record after a crash. No read beyond the startup section.
* **M1 with w.** `maintain()` begins an iteration when a cut that it
  leads to releases at least MIN_RELEASE of stream in which the
  application wrote; where the application wrote nothing in the stream
  kept, only after an iteration that rewrote at most X = MIN_RELEASE / 4
  (an emptied database). This fixes RB-007, ends the rewriting of a
  database not written to, keeps G5, and replaces 028-51's second rule
  and its read of the index (`tablePos`).

Measured on the prototype: `HoleProbe` (RB-007) keeps 188,256 and
143,624 bytes where `main` keeps 4,804,384 and 5,361,912; `IdleLiveProbe`
writes nothing in the last 10 R in every run where `main` writes 14.5 to
55 MB; G5 keeps 50,288 bytes (`main` 80,600); the same stream and w over
up to 2,919 restarts; the streams of StreamDigest's reclaim
configurations 0.3 to 2.9 % longer; `BEFORE COMMIT OK (63 s)` with two
tests changed (section 8).


## 3. One maintenance step

### 3.1. The parts, in order

`Reclaim.maintenanceStep(kind, now, tStart, L)` runs under the write
lock, as both paths do today:

* kind **commit**: after a user transaction T, within T's go point
  (027-13, section 1.2); now and tStart are T's time, L the stream after
  T's record;
* kind **call**: in `Db.maintain()`, after its checks (024-32, section
  2.6); now is the call's time, tStart the last transaction's time, L
  the stream now.

Each part at most once, in this order; each says what it does, when,
what paces it for each kind, and how it is checked:

1. **The begin, or w's store.** If no iteration runs and the begin is
   due (part 2), an iteration begins, and its store of the table carries
   w. Otherwise, if w differs from the stored w, the table is stored. So
   the record after an application record that changed w is a store of
   the table (section 4.3). Checked: `ProtoW`, `CrashW` (section 10).
2. **When the begin is due.** For both: R finite, no iteration runs,
   and R div 4 has passed since the last iteration began.
   * commit: L > lastPStart + 2 sd (027-13, section 1.2), as today;
     checked by StreamDigest (identical streams without w), G1 to G4;
   * call: M1 with w (section 5); checked by `HoleProbe`,
     `IdleLiveProbe`, G5, r-maint and e-r-maint.

   The begin itself as today for both (027-13, section 1.3): pStart = L,
   tStart, pCut, E at tStart, the table stored.
3. **A step** of the iteration that runs (027-13, section 1.4):
   * commit: if allowed = floor((L - pStart) f / 2^16) - rewritten is
     more than MIN_STEP, a step of min(allowed, MAX_STEP), as today;
   * call: a step of MAX_STEP, without the allowance, as today (M2).

   Both charge the row's `rewritten`, so a call's step lowers the
   allowance of the commits after it, as today. Checked: C-STEP on every
   step of the reclaim traces (030-27).
4. **The safe positions** (markSafe, 027-13, section 1.5), for both.
5. **The take beyond the share** (M4), call only. A commit's take is its
   share in `Db.store`, as today.
6. **The filler** (M5), call only.
7. **The cut**: decideCut(now) and makeCutIfDurable (027-13, sections
   1.6 and 1.7), for both. Checked: C-CUT with RC at every cut.

After the step, outside reclaim and as today: a call syncs outside the
lock if the pending cut's table is not durable, makes the cut, and does
one step of eviction's dead hand (M7, 024-32, Q32-4); a commit has
eviction's work after every record (`Eviction.afterTransaction`), the
records of reclaim's step too. Eviction writes nothing and stays where it
is: after every record, a call's records included.

`maintain()` returns `maintainDue()` as today. The bound of 027-13,
section 4 holds: at most six internal transactions after a user
transaction (the store of w is the alternative of the begin's store).

### 3.2. What the one step changes, and what it does not

* One method, one order of the parts, and the kind's pacing written at
  three places (parts 2, 3, and 5 with 6), where `main` has two methods
  that repeat the begin, the step's call, markSafe and the cut. In the
  prototype the two methods' 68 lines of code become 65 (the step's 49
  and three short methods): the gain is in reading, not in lines.
* No change of what a part does. With w switched off
  (`-Dproto311.now=true`), the prototype's streams are `main`'s:
  StreamDigest quick, 44 of 44 identical (section 10).
* The commits keep their paces. 028-47 measured the alternatives (Frans
  decided A, no change, 2026-11-24, 12:30): a commit that also begins
  by M1's rule (its B) gave no clear gain; a commit that also takes as
  M4 does (B2) wrote 4.3 times the stream of a twin at sd 50 MB, and
  broke a promise of `Database.setRetainDuration()`. A filler at a
  commit would write up to 200 kB at a small commit (P4). So the parts
  that pace by the request stay the call's.

### 3.3. Why not the simple form

026-03's simple form: `maintain()` commits an ordinary internal
transaction with filler bytes, and the commit's maintenance does the
rest. Every wait of a commit is paced by the stream's growth (024-32,
section 2.1), so the filler would have to supply it:

* the begin waits for 2 sd of growth: 2 sd of filler an iteration
  (100 MB at the Pub's default sd of 50 MB);
* a step's allowance is f of the growth: the live values' bytes / f of
  filler to rewrite them (4 times the live data at f = 1/4);
* the cut waits for the startup pos to reach pEnd, then pSafe, which the
  take moves in proportion to a record's own bytes: about 1 sd of growth
  a wait (028-47, section 3: about 1 MB a wait at sd 1 MB);
* the meta block after pCut: met by the above.

So an iteration under calls would write at least about 4 sd plus 4
times the live data, and the stream kept would never be below the 2 sd
of filler between the last two pStarts: 100 MB at sd 50 MB, where G5
asks for twice a fresh database's stream plus 600 kB. It would still
need a rule to stop (the commit's rule begins an iteration whenever the
filler has grown the stream by 2 sd), and so w or an equivalent. Not
proposed. What it gets right is kept: every write of a call is an
ordinary internal transaction (the table, a step, an empty record, a
filler), and a call's step is the commit's step.


## 4. w: where the application wrote

### 4.1. Why M1 needs it

M1 decides from stream positions only, and both of 028-53's faults
need what positions do not tell: whether the application wrote in a
stretch (028-53, section 5). Counted from the last pStart, a rule counts
the last iteration's own rewrites and rewrites them again and again;
counted from the table's last store, it misses the application's writes
made before that store (RB-007). In a database written to, the commits
begin iterations by growth and M1 hardly matters; in one not written
to, M1 is all there is.

### 4.2. What w is

* **Definition.** w is the pStart of the last iteration after whose
  start the application wrote a record, or -1 if it wrote after none of
  the table's rows. An application record is one with a value or delete
  node and none under `/#i/dreclaim/` (005-42's test, as 028-53, section
  8.1): a user transaction's, a setter's such as `setStartupDistance`,
  the Pub layer's; not reclaim's steps, tables, settings, fillers or M4's
  empty record.
* **Why the pStart and not the record's position.** M1 compares w only
  with fp and lastPStart (section 5), and both are pStarts: fp is the
  cut row's pCut, the pStart of the row before it (its own pStart for
  the table's first row). So the pStart before the newest application
  record answers every question M1 asks, and it changes at most once an
  iteration, where the record's position changes at every application
  record. Records before the first row's pStart are not counted: M1 reads
  w only after a cut, and the first cut sets fp to that pStart or later.
* **When it changes, and by whom.** `Reclaim.recordWritten`, after every
  record: if the table has a row, w < lastPStart and the record is the
  application's, w := lastPStart. Nothing else changes it in a run: a
  begin adds a pStart after w; a cut moves fp only.
* **Where it is kept.** As `w=<decimal>` in the table's last row, at
  every store of the table (027-03, section 15). One name more in the
  row's text, no new key, no version (section 6.4).

### 4.3. The store, and why the stream stays deterministic

* **The store.** The step stores the table when w differs from the
  stored w (section 3.1, part 1). Since only an application record
  changes w, and the step that follows it stores it, the stored w is w
  between calls. In a database written to that is one store an
  iteration, at its first commit of the application's after its start;
  in one not written to, none.
* **A start.** w := the last row's `w`. A row without it (written by
  2026.6 or `main`) gives w := lastPStart, as if the application wrote
  after the last iteration began: at most one or two iterations more
  under calls, then quiet. Then, if the stream's last record is the
  application's and at or after lastPStart, w := lastPStart: a crash came
  between that record and the store after it. The stored w stays as
  read, so the next step stores w if the start changed it.
* **P2.** Between calls the stored w is w, so a restart between any two
  calls gives the same w and the same bytes after it. Checked by
  `ProtoW` (the same stream, w and stored w after every operation, a
  restart every 7 to 101 operations, sd 5 kB to 1 MB) and StreamDigest's
  modes, which agree in every configuration (section 10).
* **A crash.** Only the last record can be an application record that
  changed w without its store, as the store is the first record after
  it; a start always reads the last record (its startup pos is before
  its own position, 027-11, section 1.4). Checked by `CrashW`: 109
  starts from streams that end with such a record, each with the running
  database's w.
* **What a fault of w could do.** Decide when `maintain()` begins an
  iteration, and so the stream's size and the bytes written; never what
  a read returns: no step, wait or cut reads w, and the proofs take the
  iterations as given (section 7).

### 4.4. Compared with 028-53's A

A keeps W, the newest application record's position, which changes at
every application record; so it must store the table whenever a start
could no longer see the records after the table's last store: each time
the startup pos passes that store (about once per sd of growth), with a
start that reads the section, and an invariant (the startup pos at or
before the last store between calls). With K, fewer stores and a start
that reads up to K before its section. w keeps the same answers to M1's
questions with one store an iteration, a start that reads one more
field and the last record, and no invariant on the startup pos.


## 5. M1 with w

The conditions of today stay: R finite, no iteration runs, R div 4 since
lastTStart, no cut pending (027-13, section 1.10); with no row, the
stream from fp is at least MIN_RELEASE. Then, with own = lastPStart - fp
(what the new iteration's cut releases) and next = L - lastPStart (at
least what the next one's releases):

* own counts if w >= fp: the application wrote in the stream kept;
* next counts if w >= lastPStart: it wrote after the last iteration
  began;
* where w < fp (it wrote nothing in the stream kept), both count if the
  last iteration rewrote at most X = MIN_RELEASE / 4 = 100,000 bytes;
* an iteration begins if a stretch that counts is at least MIN_RELEASE.

028-51's second rule, the stream after the table's last store at tp,
needs no line of its own: with no iteration running and no cut pending,
reclaim's last record is that store, tp >= lastPStart, and a stream
after it is the application's (or a change of reclaim's settings, a
record of a few dozen bytes), which makes w >= lastPStart and next >=
L - tp. So `tablePos()` and its read of the index at every evaluation of
M1 go.

What it does in each case:

* **RB-007.** Writes made while the last iteration ran or waited for its
  cut are after its pStart: w = lastPStart, next counts, and an
  iteration begins once the stream from that pStart is MIN_RELEASE; the
  one after it releases them. `HoleProbe 4000 20000`: 188,256 bytes
  kept (`main` 4,804,384).
* **The rewriting** (028-53, section 2). After the application's last
  write, in the stretch from some pStart P, the iterations go on while
  the stretches they release count; once two iterations have begun after
  P and the second's cut has moved fp past P, w < fp, and only an
  iteration that rewrote at most X leads to another. A database with
  more than X of live values is quiet from there. `IdleLiveProbe`: 0 kB
  in the last 10 R at 15,000 to 100,000 values (`main` 14.5 to 55 MB).
* **Back to empty.** An emptied database's deletes are in the stream
  kept (w >= fp), so the calls begin and cut iterations as now; when the
  deletes are cut away, w < fp, the last iteration rewrote reclaim's own
  few keys (under X), and the calls drain reclaim's own records while a
  stretch is MIN_RELEASE or more. G5: 50,288 bytes kept (`main` 80,600).
* **Why X.** Without the drain, a database emptied while iterations ran
  keeps the iterations' own records: 028-53 measured W and RB-007's rule
  alone at 921,504 bytes in `HoleProbe 4000 20000`, over 400 kB more
  than a fresh database (028-53, section 8.4). X tells an emptied
  database (its iterations rewrite reclaim's few keys) from one with
  live values; MIN_RELEASE / 4 makes an iteration begun so release at
  least four times what the last one rewrote. A database with at most X
  of live values that is not written to is drained too, until its
  stretches are below MIN_RELEASE: `IdleLiveProbe` with 300 to 1,200
  values of 100 bytes, sd 100 kB and 1 MB, writes nothing in the last
  10 R, as `main`.
* **What it leaves as on `main`: a database written slowly.** One
  application record in the stream kept makes every stretch count, so
  under calls a database with live values and a trickle of writes
  rewrites its live values about once an R/4, as `main` does: with
  30,000 values of 100 bytes, sd 1 MB and one value overwritten each R
  (2 kB of values in 20 R), `main` and the prototype both write 30.6 MB
  in the last 10 R, and with ten an R 88 MB (`TrickleProbe`, section
  10). Without calls, the commits' rule of 2 sd of growth begins none
  there. A rule in proportion to the application's writes (for instance
  an iteration under calls only after the application has written f of
  what the last one rewrote) would end it, but it counts the bytes the
  application wrote, not what they free: a database whose application
  deletes few large values that an iteration has just rewritten would
  keep their copies, against back to empty, which w's position rule
  keeps. Not part of this design; a cost, no promise broken (028-53,
  section 4's reading of the Javadoc); F7 in section 12.


## 6. The cost

Compared with `main`, 028-53's A (with and without K) and B (M1's second
rule counted from lastPStart, one line).

### 6.1. Code

* The prototype: 113 lines of code added and 55 removed in `Reclaim`
  and `Db`, besides comments, with a switch that keeps `main`'s M1 and
  `tablePos()` for the measurements. Landed without the switch, about 35
  lines more than `main`: w about 55 (the fields, the two record tests,
  the row's text, the start), M1 about 15 fewer (`tablePos()`'s 18 lines
  go, the rule grows by a few), the one step 3 fewer than the two
  methods. Tests: about 150 lines (section 8), as A.
* A: about 80 lines in `Reclaim` and `Db`, 15 more with K; `tablePos()`
  kept. B: one line.

### 6.2. State

* In memory: w and the stored w, two numbers. In the stream: `w` in the
  table's last row, at most 20 bytes a store.
* A: W and q in memory, `w` in the row, and the invariant that the
  startup pos is at or before q between calls. B: nothing.

### 6.3. Stream bytes

* A database written to: one store of the table more an iteration
  (`CrashW` counts one w change an iteration: 40 at 41 iterations, 6 at
  6). The table is about 240 bytes a row (measured with keys of three
  segments; 7 rows at R = 100 and 300 s), up to about 30 rows with a
  long R (`Reclaim`'s comment on the current row). StreamDigest quick:
  the two-level configurations (no reclaim) identical; the reclaim
  configurations, sd 500 to 10,000 bytes, longer by 2.9 % (l3-every1),
  0.34 % (l3-node8), 0.80 % (l3-node14) and 1.41 % (l3-node62). From
  sd 1 MB on, one table of a few kB per 2 sd or more of growth: under
  0.5 %, argued; under 0.01 % at the Pub's default 50 MB.
* A database not written to: nothing in the last 10 R of
  `IdleLiveProbe`'s runs, where `main` writes 2.5 MB an R at 30,000
  values. G5's drive writes 78,120 bytes (`main` 102,072).
* A: a store each time the startup pos passes the table's last store,
  about once per sd; StreamDigest's reclaim configurations 20 to 63 %
  longer without K, -0.6 to +0.3 % with K. B: every database with live
  values that is not written to rewrites them under the calls (3,066 kB
  in 10 R at 3,000 values, where `main`, A and w write nothing; 028-53,
  section 8.5).

### 6.4. The format

A name `w` in the last row of the table's text (027-03, section 15); the
row is read leniently and has no version (027-13, section 9). 2026.6
ignores `w` and drops it at its next store; the design reads a row
without it as w = lastPStart (section 4.3). No meta version, no record
format, no new key. A change of the stream's format is Frans's to
decide (018-01's rule): F2 in section 12.

### 6.5. Startup

The start reads one more field of the row and tests the last record's
keys, a record it has read already: no read beyond the startup section,
so bounded startup (027-11; T3) is as on `main`. A reads the section's
records for W, and with K up to K before the section, which the bound of
027-11 would have to cover.

### 6.6. Commit latency

After every record, a comparison (w < lastPStart); while it holds, a test
of the record's keys against reclaim's prefix, until the first
application record after an iteration's start. Once an iteration, one
store of the table in that commit's step, in place of none: a record as
large as the begin's own store. Within 027-13, section 4's six internal
transactions after a user transaction. Not timed: timing.sh needs a
quiet machine; a gate of the build (section 8.3). `maintain()` reads the
index no more for M1.


## 7. The Lean proofs

From lean/ and the 030 items at `4ce8f942`, read for this design.

### 7.1. What stays, and why

* **lean/SIS** (027-13, section 5): its reclaim theorems are about the
  cut and what follows it: T13' (`T13_markTouch`), T-COVER (`T_cover`),
  T-LATEST (`T_latest`), T8 (`T8_recoverCut`), T9 (`T9_handles`), T12
  (`T12_restartCut`, `T12_handles`), `Rule4PosCut_handles`. None
  mentions an iteration's begin, the table, maintain() or whose a record
  is; the table appears only in a comment of `Algo.faPolicy`. Unchanged.
* **T3** (bounded startup; `T3_take` in SIS/BoundTheorems.lean, "T3
  holds for every pace"): the take is not changed; M4's take beyond the
  share is a pace, as since 024-32. The start reads no more than its
  section. Unchanged.
* **lean/contract** (030-24, 030-25): `cutOK_of_rc`, `rc2_of_iteration`,
  `iterationOK_of_stepsOK`, `PE.pe_reclaim_reads_steps` and
  `PE.pe_reclaim_user_reads_steps`. Their premises take the iterations
  as given: `CutsMeetSteps` asks for some iteration with `StepsOK` and
  RC4 at each cut, and `StepsOK` holds for any t0, so no rule for the
  begin is assumed; between steps "run any transactions: the user's,
  reclaim's table stores, the row stored again" (ReclaimSteps.lean).
  `MaintenanceOK` lets a maintenance transaction write only under
  reclaim's keys, or be a step: a store of the table in a transaction of
  its own meets its first case. Unchanged, given that w's store stays a
  transaction of its own and is never put into a step's transaction
  (a step may write only its row and its rewrites, `StepOpOK`).
* **The trace checker** (`tracecheck`; C-A, C-S, C-CUT with RC, C-STEP,
  C-L, C-P, C-H): no checker parses the row's text (the STEP and RESUME
  lines' fields come from Java's memory, through `TraceExport`); a
  record's kind is only in a comment line, which every reader skips; a
  record without a TOUCH line needs no STEP line. More table stores and
  `w` in the row need nothing. The exporter's hooks inside the step
  (`crash=K`, the STEP line in the step's commit, `maint=K`) keep their
  places in the one step.
* **The contract's checkers** (`lean/contractcheck`: C1 to C5, R1 and S
  on every transaction, whatever its kind): nothing to learn.

So no statement, premise or checker rule changes, and nothing has to be
proved again.

### 7.2. Proved, and only tested

* **Proved, whatever w decides**: that reads from fa on are right after
  every cut whose iteration's steps follow the model of the steps and
  meet RC1 and RC4 (`pe_reclaim_reads_steps`): the design changes when
  iterations begin under calls, which the theorems do not fix.
* **Tested, not proved**: that w is the same over restarts (`ProtoW`,
  StreamDigest's modes, RestartInvariance) and after a crash (`CrashW`);
  RB-007's fix (`HoleProbe`); quiet when done (`IdleLiveProbe`); back to
  empty (G4, G5); that Java's internal transactions are the kinds
  `MaintenanceOK` allows ("tested links", 030-35). No theorem says that
  reclaim makes progress or bounds the stream (030-38, G6); INV-RESTART
  for reclaim's state is tested, not in Lean, as before.

### 7.3. What a single step makes possible or simpler

* **One transition to model.** A model of reclaim's maintenance would
  have one step with a kind, not a commit's path and a call's path that
  repeat four parts. 026-14, section 2, item 1 ("reclaim as a whole")
  asks for such statements; none is proposed for 2026.7.
* **Quiet when done**, a small model of positions only (fp, the
  pStarts, w, the stream's length, the last row's rewritten), not of the
  steps: with no application record after a pStart P, once two
  iterations have begun after P and the second is cut, w < fp, and if
  the last iteration rewrote more than X no call begins an iteration.
  The rule makes the last part immediate; the content is in w's
  definition and the order of the pStarts. That the cuts come at all
  (the waits end) stays tested.
* **The record kinds and RC1, RC4 as theorems** about the step, where
  today they are checked at every cut: they need the table, R and the
  times in the model, which 030-22, section 4.3 judged worth little.
* **Back to empty as a theorem** would need bounds on what a call
  writes (the take's TAKE_MORE, the filler's META, the tables), a larger
  model; G5 gates it.


## 8. Tests and gates

### 8.1. Failing on `main`, passing with the design

Measured on the prototype (section 10); each becomes a unit test of
about a second or less in the build, sized so that `main` fails it:

* RB-007: `HoleProbe 4000 20000` and `20000 20000` (028-53's probe).
* The rewriting: `IdleLiveProbe 15000 1000000 20 10` (028-51's probe):
  `main` writes 14,554 kB in the last 10 R, the design none.
* w over restarts: `ProtoW` (this item's probe), and a row without `w`
  (a stream of 2026.6).
* w after a crash between an application record and its step's store:
  `CrashW` (this item's probe).

### 8.2. Passing on both, kept

* G4 and G5 (`count-gates.sh`): on the prototype G1 to G3 and G5 pass
  (G5 kept 50,288 bytes, the last call with work 3,007 of 20,000); G4
  fails on its M5 alone, the dead KEY klongs, 27 against the twin's 13,
  2.077 times where 2 is the limit. That gate is a snapshot of small
  counts at the drive's end, and its phase decides it: at drives of 38 to
  42 R its value goes from 0.37 to 1.46 on `main` and from 0.48 to 2.08
  on the prototype, the emptied database's count 10 to 35 and 13 to 27.
  The build gives it G5's allowance (the larger of twice the twin's and
  the twin's plus a constant, 023-03's C4) or takes its most over the
  last R; F6 in section 12.
* `ReclaimMaintainTester` (7 tests), `Reclaim`'s 39, the restart tests:
  pass on the prototype, with two changed:
  * `Reclaim.Tester.testRestartResumesIteration`, which asserts that no
    step stores the table: it allows the one store of w, at the first
    commit after the iteration's start;
  * `StorageFaultTester.testStopWhileReading` (section 9).
* The conformance's r-maint, r-maint-sd, c-maint and e-r-maint: not run
  on the prototype (its clone has no built Lean checker); A's prototype,
  whose records are of the same kinds, passed the reclaim and crash sets
  (028-53, section 8.3).
* StreamDigest quick: the two-level configurations identical to `main`;
  the reclaim ones changed, the four modes the same in each.

### 8.3. Gates of the build

* `java/before-commit.sh` (on the prototype `BEFORE COMMIT OK (63 s)`).
* `count-gates.sh all`, with G4's M5 as F6 decides.
* The conformance's reclaim, crash, drain and evict sets (`level3.sh`,
  `level4.sh`), r-maint and e-r-maint among them; and one configuration
  more that reaches M1's rules: `TraceExport` with N calls of
  `maintain()` after the workload's last write (a new option such as
  `idle=N`), so that traces hold iterations begun by w's rules; the
  checker needs nothing new for them.
* StreamDigest quick: two-level identical to `main`, the four modes the
  same in each reclaim configuration; RestartInvariance (`level3.sh`).
* `java/timing.sh` before the release (the commit path's test and store),
  as 034 asks for every release.


## 9. testStopWhileReading without K: the cause

On A's prototype without K, and on this design's before its change,
`StorageFaultTester.testStopWhileReading` fails: "call 3: the read did
not meet the closed stream: get 10 threw DbStoppingException", after
30 s. Traced 2026-11-25 (a stack at the injected stop):

* The test stops the database at the stream's calls number 1 and 3 of
  the workload's thread after a reopen, and waits up to 30 s for the
  stop's close, so that the read goes on on the closed stream. On `main`
  and A with K, call 3 is a get's read, outside the write lock.
* A's stores without K, and w's store, change the records of the
  prefill, so after the reopen call 3 falls in a reclaim step's scan
  (`Reclaim.step`, within a commit's `transactionCompleted`), under the
  write lock. The stop's close waits for the running transaction (since
  005-35), the test waits for the close; after its 30 s the read goes
  on, on the open stream, the commit returns, and the next get is
  refused as the database stops.

So the cause is the test's fixed call numbers, not A's store rule or w:
no value is lost or wrong, and nothing in the database waits wrongly.
With the stop made only at reads of the workload's thread outside the
write lock, when the test waits for the close (seven lines in
`StorageFaultTester.Injector.call`, in the prototype), the test passes
with A without K, with A with K, and with w; `testSample` too. The
build takes that change.


## 10. Measurements

On the branch `031-01-proto` (head `54c768c8`, on `main` at `4ce8f942`;
`prototype.diff`), MemoryStream or CutStream, test clocks, counts and
sizes only. `main` is the same commit's build. The probe `HoleProbe` is
028-53's, `IdleLiveProbe` 028-51's, `ProtoW`, `CrashW` and
`TrickleProbe` this item's (`probes/`).

* **The one step alone** (`-Dproto311.now=true`): StreamDigest quick,
  DIGESTS IDENTICAL, 44 of 44.
* **RB-007**, `HoleProbe N1 20000`: N1 4,000: kept 188,256 bytes, the
  twin 315,024 (`main` 4,804,384 and 315,008; A 176,736); N1 20,000:
  143,624, the twin 199,376 (`main` 5,361,912; A 177,344). The last call
  with work: 3,858 of 10,000 (`main` 621).
* **The rewriting**, `IdleLiveProbe LIVE SD 20 [10]`, written in the
  last 10 R, `main` in brackets: 30,000 values at sd 1 MB after 10
  rounds, 0 (24,522 kB), and 6,111 kB kept (9,989); 15,000, 0 (14,554
  kB); 100,000 at sd 1 MB, 0 (51,595 kB); 100,000 at sd 5 MB, 0
  (55,421 kB); where `main` is quiet too, 0: 30,000 at sd 5 MB, 3,000
  after 10 rounds, 2,000 and 0 values.
* **G5**: kept 50,288 bytes (`main` 80,600), the twin 800; the drive
  wrote 78,120 bytes in 10 calls (`main` 102,072), the most in a call
  40,328 bytes (`main` 70,976); the last call returning true 3,007
  (`main` 3,006).
* **count-gates.sh all**: G1 100,720 bytes, G2 1.229, G3 4.715, G4 as
  in section 8.2, G5 PASS.
* **P2**: `ProtoW SD EVERY`, sd 5,000, 50,000, 200,000 and 1,000,000,
  a restart every 7, 23 and 101 operations (2,919, 888 and 202
  restarts): SAME STREAM in all twelve, w and the stored w equal after
  every operation; the workload's idle phases write nothing after the
  writes stop (its third phase: 0 bytes), and the emptied database keeps
  133 to 280 kB.
* **A crash**: `CrashW SD`, sd 5,000, 20,000, 100,000 and 1,000,000: 40,
  34, 29 and 6 starts from a stream ending with a record that changed w,
  each with the running database's w; 2 copies skipped at sd 5,000,
  where the sync left the copy short of the record's end.
* **StreamDigest quick**: section 6.3; the four modes agree in each
  configuration.
* **A database written slowly**, `TrickleProbe LIVE SD 20 10 EVERY`
  (this item's probe, `IdleLiveProbe` with one value overwritten every
  EVERY calls during the calls): 30,000 values at sd 1 MB, written in
  the last 10 R by `main` and the prototype: EVERY 0 (no writes), 24,522
  kB and 0; EVERY 1,000 (one an R), 30,650 and 30,665 kB; EVERY 100,
  88,311 and 88,378 kB.
* **Small live databases**, `IdleLiveProbe LIVE SD 20 10` with 300,
  600, 900 and 1,200 values at sd 100 kB and 1 MB: nothing in the last
  10 R on both.
* **Gates**: `BEFORE COMMIT OK (63 s)` on `54c768c8`.


## 11. Options

### 11.1. The path

* **P-a. One step, kind-paced** (sections 3.1, 3.2). One method and one
  order for both; the commits' paces unchanged. Byte-neutral by itself.
  Cost: a change at the heart of the commit path, checked by identical
  streams.
* **P-b. The simple form** (section 3.3): rejected, its filler grows
  with sd and the live data, and the stream kept stays above 2 sd.
* **P-c. Two paths, as today**, with w and M1's rule in
  `Reclaim.maintain` only: the same streams as P-a, without the merge.
* **P-d. One pace for both** (028-47's B and B2): decided against on
  2026-11-24.

Recommended: **P-a**. It is what 026-03 asked for, it costs no byte,
and w's store has one place to live in it (part 1).

### 11.2. Where the application wrote

* **W-a. 028-53's A**: W exact, the table stored when the startup pos
  passes its last store; with K, fewer stores and a read before the
  section (section 4.4).
* **W-b. w, the pStart** (section 4): one store an iteration, no read
  beyond the section, no invariant on the startup pos.
* **W-c. B**: no w; M1's second rule from lastPStart. Fixes RB-007 in a
  line; every database with live values that is not written to rewrites
  them under the calls for as long as they go on.
* **W-d. w in every record's header**: no store of the table, a record
  format change (027-03, section 8) for one of reclaim's rules; not
  measured, not proposed.

Recommended: **W-b**: A's answers at about A-with-K's bytes, without K's
read beyond the section. W-c if Frans judges any stored mark too much
for 2026.7: it fixes the bug, and the rewriting stays a known cost.

### 11.3. Where w is stored

* **In the table's last row** (the design): the store is a table's, a
  few kB, once an iteration.
* **A KV of its own**, such as `/#i/dreclaim/-w.txt`: a store of about
  20 bytes, so the reclaim configurations of StreamDigest would grow
  less; a new internal key in the format, and one more read at a start.

Recommended: the row: reclaim's state stays in one KV, and the extra
store is under 0.5 % of the stream from sd 1 MB on.

### 11.4. maintain() in the API

Kept. By P3 (010-01) an idle database does no work of its own, so a
database that the application emptied and no longer writes to gives its
space back only under a call that asks for it; without `maintain()`
back to empty is gone for such a database. The API does not change; the
Javadoc gains what the design adds (F3).


## 12. What Frans decides

* **F1.** The one step (P-a), or two paths with the same rules (P-c).
* **F2.** The stream's format: `w` in the table's last row and one more
  store of the table an iteration (W-b, in the row), or A (W-a), or B
  (W-c), or a KV of its own (11.3).
* **F3.** The promises of `Db.maintain()` and `Database.maintain()`:
  whether their Javadoc says that, in a database the application no
  longer writes to, the calls stop writing once a cut would release no
  stream that it wrote, but for an emptied database's own records.
* **F4.** RB-007 fixed by this design in 2026.7 (033), or B first as a
  stopgap if the design waits.
* **F5.** X = MIN_RELEASE / 4 (100,000 bytes), as 028-53 measured it.
* **F6.** G4's M5 gate: G5's additive allowance, or its most over the
  last R (section 8.2).
* **F7.** The slowly written database under calls (section 5, the last
  case): as on `main` and kept, or registered as a 028 entry to study a
  rule in proportion to the application's writes that keeps back to
  empty.


## 13. State

2026-11-25, by an agent of lead-1125: the design written (sections 2
to 12), with a prototype on the branch `031-01-proto` of the clone c311
(`54c768c8`, `prototype.diff`) and its measurements; for Frans's
decisions F1 to F7. Recommended: P-a, W-b in the table's row, X as
028-53, G4's M5 with an allowance. Nothing on `main`. Not settled: a
database written slowly under calls rewrites its live values as on
`main` (section 5, F7); the conformance sets were not run on the
prototype (no Lean checker built in its clone).


Log
===

2026-11-25. Created (Frans's decision of 13:03, 006-35).

2026-11-25. The design, by an agent of lead-1125 in the clone c311
(branch `031-01`): one step for a commit and a call, w (the pStart after
which the application last wrote, kept in the table's row), M1 with it;
the cost, the Lean proofs, the tests and the options, F1 to F7 for
Frans. A prototype on the branch `031-01-proto`, `BEFORE COMMIT OK`;
testStopWhileReading's failure without K traced to its fixed call
numbers. The subitem a directory with the prototype's diff and two
probes.
