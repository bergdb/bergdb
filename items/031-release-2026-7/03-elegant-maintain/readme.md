# 031-03. An elegant maintain()

Created 2026-11-25 by Frans Lundberg. Status: open.

A search for an elegant, simple design of `maintain()` and of how it
decides its work: one that gives an emptied database back its space
(RB-007 fixed), stops writing in a database the application no longer
writes to, and holds through crashes, stops and restarts without
recovery machinery of its own, with the stream deterministic (010-01,
P2). Frans, 2026-11-25: neither 028-53's A nor its B; `maintain()` is
the one part of the database's core that is not yet elegant, and an
elegant way is expected to exist.

A design with a prototype: nothing of it lands without Frans.

What was known: 028-53 (the faults, A, B, C), 031-01 (one maintenance
step, w, Codex's review and the repair: the exact repair adds a state,
a store and a start that writes), 026-03, 024-32, 028-47, 028-51,
028-54.


## 1. The goals

1. **Back to empty.** A database the application has emptied returns,
   under `maintain()` calls with time passing, to within about 400 kB of
   a fresh database's stream (the Javadoc of `Db.maintain()` and
   `Database.maintain()`; 024-30's G5). RB-007 (033) breaks it.
2. **Quiet when done.** A database with live values that is no longer
   written to stops writing under the calls once nothing is left to give
   back (028-53, sections 1 and 2).
3. **Through crashes, stops and restarts, easily.** No state that must
   survive a restart beyond what the stream holds anyway, no recovery
   case of its own; the stream a function of the accepted transactions
   (010-01, P2); startup bounded (027-11, T3).
4. **Simple** (010-01, P11 and P13): few rules, explained in a
   paragraph; counted by new state, new stores, recovery cases, lines.
5. P3, P4 and P1 as today.


## 2. The design in a paragraph

Written 2026-11-25 by an agent of lead-1125, measured on a prototype
(the branch `031-03-proto` of the clone c313, `prototype.diff`, on
`main` at `e04663b5`).

Reclaim remembers one thing about the application: **w, the last pStart
after which it wrote**. It costs nothing to keep. Every record that
reclaim writes holds its table or its current row, and the row holds w;
and while the stream's last record is not reclaim's, that record itself
says that the application wrote after the last pStart. So w is read off
the stream, by the running database and by a start in the same way, at
every record: there is no store of its own, no moment when it is in
memory only, and nothing for a start to repair. With it, `maintain()`
has one rule for beginning an iteration: **the stream kept is 400 kB or
more, and it still holds a record that the application wrote** (w is at
or after the first available position). Once the cut has passed the
application's last write, all that the stream keeps was written by
reclaim itself after that write, so it is live values and reclaim's own
records, and the calls go quiet. One exception drains an emptied
database: the rule also holds while the last iteration rewrote next to
nothing (at most X = 100 kB).

What it gives, measured (section 7): RB-007's case keeps 189 and 124 kB
where `main` keeps 4.8 and 5.4 MB; a database not written to writes
nothing in the last 10 R in every run, where `main` writes 14.5 to 55
MB; an emptied database ends below 400 kB by the rule itself, also in
the case where `main` keeps 790 kB (section 9.1); a start from the
stream cut after any record has the running database's w (60,000
such starts and stops, none different); the same bytes over restarts;
Codex's four cases of 031-01 pass; `BEFORE COMMIT OK` with one test
line changed.


## 3. The rules

Each rule: what, when, by whom, and how it is checked. The probes are
in `probes/` (section 7).

### 3.1. R1: whose a record is

* **What.** A record is reclaim's own if it holds one of reclaim's
  maintenance keys: a key under `/#i/dreclaim/` other than the settings'
  (the table, the current row; the filler's in a stream of 2026.6).
  Every other record is the application's: a user transaction's, an
  empty one's, a setter's (the startup distance, reclaim's settings).
* **When, by whom.** Told from the record's keys alone, so the running
  database (`Reclaim.recordWritten`, after each record) and a start
  (`Reclaim.initFromDb`, for the stream's last record, which it has
  read: a record's startup pos is before its own position, 027-11,
  section 1.4) tell the same.
* **Checked.** `WitnessProbe` and `Witness2Probe`: every record of the
  runs is reclaim's own by its keys exactly when reclaim's maintenance
  wrote it (0 of another kind).

### 3.2. R2: every record of reclaim's holds a row, and a row holds w

* **What.** `w=<decimal>` is one more name in the text of the table's
  last row and of the current row (027-03, section 15). Reclaim writes
  no record without one of the two:
  * the begin, the end, the safe positions, the cut: the table, as
    today;
  * a step and its row stored again: the current row, as today;
  * `maintain()`'s take (M4), an empty record on `main`: the table,
    stored again, with the take going on to the position its row waits
    for;
  * `maintain()`'s filler (M5), a put and a delete of `-fill.txt` on
    `main`: the table, stored with spaces after its text up to the next
    meta block (the table's parser skips them, also 2026.6's). One
    record, nothing to delete; the next store of the table, the cut's
    in the same call, replaces it.
* **When, by whom.** By reclaim, at the stores it makes anyway. No
  store is made for w.
* **Checked.** R1's check (a record without a row would not be reclaim's
  own by its keys); the conformance's reclaim, crash and e-r-maint sets
  on the unchanged trace checker (section 8).

### 3.3. R3: w is read off the stream

* **What.** w is the pStart of the last iteration after whose start a
  record of the application's was written, or -1 if none was after a
  row's pStart. At every record boundary:

      w = the last pStart, if the table has a row and the stream's
              last record is the application's;
          the larger of the w of the table's last row and of the
              current row, otherwise.

* **When, by whom.** The running database keeps it by one line after
  each record: an application record raises w to the last pStart. A
  start computes the same expression from the table, the current row
  and the last record. A table's last row without w (a stream of
  2026.6) reads as the last pStart.
* **Why it is the same.** By induction over the records. After an
  application record, both give the last pStart. After a record of
  reclaim's, the record holds a row (R2) with the w of that moment, and
  w only grows, so the larger of the stored ones is the newest. A
  begin adds a row and leaves w, which its table holds.
* **Checked.** For every record of the probes' runs, of every kind (the
  application's, a step, a table, a take, a filler), a database started
  from the stream cut after it has the w that the run had there:
  `WitnessProbe`, `Witness2Probe`, `UpgradeProbe`, `StopAtProbe`
  (section 7.3).

### 3.4. R4: when maintain() begins an iteration (M1)

* **What.** The conditions of today (027-13, section 1.10): R finite,
  no iteration runs, R div 4 since the last one began, no done row
  waits for its cut. Then, with L the stream length and fp the first
  available position:

      begin  iff  L - fp >= MIN_RELEASE
                  and (no row yet, or w >= fp,
                       or the last row's rewritten <= X)

  MIN_RELEASE = 400,000 as today; X = MIN_RELEASE / 4 (031-01's X).
* **Why.** w >= fp says that the stream kept holds a record of the
  application's: something in it may be dead. The iterations go on
  until the cut passes w: the cut of the second iteration that begins
  after the application's last record. Between them the two rewrite
  every live value once. Then every byte kept was written by reclaim
  after the application's last record: the values that those two
  iterations rewrote, which nothing has replaced since, and reclaim's
  own records. Rewriting them again frees nothing but those records,
  so the calls stop, unless that is nearly all there is: an emptied
  database, whose iterations rewrite reclaim's few keys, goes on until
  the stream kept is below MIN_RELEASE.
* **Why the drain ends.** An iteration that rewrote at most X writes
  little more than its rewrites, its rows and a few tables to the
  stream (028-53's rows: stretches of 1.08 to 1.12 times their
  rewrites at 2 to 3.5 MB). A filler is written only when no meta
  block follows the iteration's pCut, and then the stream from that
  pCut ends within one meta block distance, half of MIN_RELEASE. So
  after such a cut the stream kept is at most about 200 kB and one
  iteration's records: below MIN_RELEASE while those are under 200
  kB. Argued, and checked by the sweeps of section 7.2, where no
  drain went on; X = MIN_RELEASE / 8 would widen the margin (F4).
* **What it replaces.** `main`'s two stretches (from fp to the last
  pStart; after the table's last store) and `tablePos()`, the read of
  the index at each evaluation. 028-53's B is the same test without
  the second line, stretch by stretch.
* **Checked.** `HoleProbe` (RB-007), `IdleLiveProbe` and the sweep of
  small databases (quiet when done, no loop of the drain),
  `TwoStretchProbe`, G5 and G4 (back to empty).

### 3.5. What does not change

A commit's maintenance (the begin by 2 sd of growth, a step by the
allowance, the safe positions, the cut): as today, byte for byte but
for `w=` in the rows. `maintain()`'s M2, M3, M6, the sync and the dead
hand; what a step, a wait and a cut do; what `maintain()` returns.
031-01's one maintenance step for a commit and a call (its F1) is
independent of this design and fits it.


## 4. Crashes, stops, restarts, and P2

* **No state outside the stream.** R3's expression is a function of
  the stream's bytes at every record boundary. The field in memory is
  a cache of it. The other inputs of M1 (the rows, fp, L, the clock)
  are as today.
* **A crash or a stop anywhere.** A crash leaves the stream cut at a
  record boundary; a stop inside a call leaves it after the call's last
  completed record (015-53). In both, the next start reads the w that
  the running database had after that record (R3). Nothing is written
  by the start, and no later record can hide the fact before it is
  stored: only a record of reclaim's replaces the application's as the
  stream's last, and it holds the row with w (R2). A setter's record
  or an empty transaction, which hid 031-01's recovered w (Codex's
  finding 1), is itself a record of the application's here.
* **A restart between calls** (P2, INV-RESTART): the same w, so the
  same decisions and the same bytes. `WitnessProbe`: the same stream
  after up to 4,166 restarts in a run.
* **Inside a call's maintenance** (028-54): on `main`, a crash or a
  stop between a user record and reclaim's records after it changes
  the stream from there on. This design makes it neither better nor
  worse: `MidCallProbe` gives other bytes from the user record on, on
  `main` and on the prototype alike. w adds no such point, as it has no
  record of its own whose place an interruption could move (Codex's
  finding 2 of 031-01: its `bytes` case gives the same bytes here).
* **Bounded startup.** A start reads one more field of two rows it
  reads anyway, and the keys of the last record, which it has read.
  Nothing beyond the startup section; T3 as on `main`.
* **What a fault of w could do.** Decide when `maintain()` begins an
  iteration, so the stream's size and what is written; never what a
  read returns. No step, wait or cut reads w.


## 5. The search

The candidates weighed, in the order they fell.

* **Sizes alone.** `main`'s two stretches, B, a stretch's size less
  what its iteration rewrote, the live bytes that an iteration's scan
  counts. One record of 136 bytes can make megabytes dead (Codex's
  case of 031-01: two values of 1.5 MB, one delete). Two streams that
  differ by that record only must be decided differently, so the rule
  has to react to any record of the application's, whatever its size:
  the fact needed is whether the application wrote, not how much. A
  size tells that only where the application's bytes can be told from
  reclaim's by position: after reclaim's last record.
* **Done by what an iteration released.** The cut's release less the
  iteration's rewrites, known after the fact and free to keep in the
  row: it shows that the two-set loop of 028-53 gains nothing, but
  says nothing of a delete made after the iteration's scan passed its
  key. With the clock slowed after each iteration without gain
  instead of a stop, the calls write for ever, more and more seldom,
  and an emptied database returns late. Not built.
* **An exact count of dead bytes.** The writer knows the value that a
  put or a delete replaces. A counter that every application record
  changes cannot be shown by one record; it needs a store whenever the
  startup pos passes its records (A's rule and invariant). The one
  candidate that would also end the slowly written case (section
  10.3). Not built.
* **Iterations under calls that cut at their own pStart.** One stretch
  instead of two, but the same fact is needed through the iteration's
  own records, and every live value is rewritten in each iteration,
  twice `main`'s rate. Not built.
* **The application says when.** A call that asks for one pass, and
  `maintain()` only continues it: BergDB decides nothing. An
  application that asks at every idle moment rewrites as with B, and
  the promise of the API changes. Option O-5 (section 10).
* **w in the application's own record.** Reclaim adds its table to the
  first user transaction after a begin: atomic, no window. But a user
  transaction then holds a key of reclaim's, against "reclaim writes
  only in transactions of its own" (027-13, section 1.1). Not built.
* **A mark in every record's header** saying whose it is: a change of
  every record's format (027-03, section 8) for what the keys already
  tell.
* **The witness** (the design). What made it work: w is a fact that
  one record shows (any record of the application's after the last
  pStart gives the same w), so the stream's last record is enough, and
  the only records that can follow it without being the application's
  are reclaim's, which carry w at no cost. 031-01, section 13.4,
  looked for a form "on stores that already happen" and found none,
  because a setter's record, an empty transaction, the take and the
  filler stored nothing of reclaim's; here the first two count as the
  application's, and the last two are stores of the table.
* **M1's form.** First built stretch by stretch (B's two stretches,
  each 400 kB or more, with the second line of R4). An independent
  review (section 7.6) found an emptied database kept at 790 kB by
  it, two stretches just below 400 kB each, as on `main` (section
  9.1). One threshold on the stream kept is simpler and ends it; the
  drain does not loop with it (the sweep, section 7.2).


## 6. The counts

Next to 028-53's A and B and 031-01's repaired w (031-01, section
13.4).

* **B**: 1 line; 0 states, 0 stores, 0 recovery cases. Fixes RB-007.
  Rewrites the live values of every database not written to, for as
  long as the calls go on. Keeps `main`'s 790 kB case (section 9.1).
* **This design**:
  * new state: 1 number, w, in a row that is stored anyway;
  * new stores: 0. Two records change what they hold: the take's (the
    table, where it was empty), the filler's (the table with padding,
    one record where there were two);
  * recovery cases: 0. A start evaluates the expression the running
    database evaluates; it writes nothing. One reading rule for a
    stream of 2026.6 (a row without w);
  * invariants: 1 (R3), checked at every record by the probes;
  * lines: the prototype adds 100 lines of code and removes 17 in
    `Reclaim` and `Db`, with switches for `main`'s M1, B, the
    stretch-by-stretch form, 031-01's rule, O-7 and `main`'s filler.
    Landed without them, about 55 added and 30 removed (`tablePos()`,
    the take's empty transaction, the filler's two transactions and
    its key go): about 25 more than `main`;
  * tests changed: 1 line (a test that compares a stored row's text).
* **w, repaired** (031-01): about 55 lines more than `main`; 1 state,
  1 store of its own (once an iteration), 2 recovery cases, in one of
  which a start writes a record, 1 invariant; 2 tests changed.
* **A** (028-53, section 8): about 80 lines; 2 states, a store about
  once per sd, 4 cases at a start, 1 invariant on the startup pos.


## 7. Measurements

On the branch `031-03-proto` at `47103353` (its head `eae8d1da` adds
the switch of O-7 only), built in the clone;
`main` is `e04663b5`, whose `java/` is that of `4ce8f942`. MemoryStream
or CutStream, test clocks, R = 1 s, a call a millisecond; counts and
sizes only. The prototype with `-Dproto313.m1=main` writes `main`'s
bytes (StreamDigest quick, 44 of 44 identical), so the build's own
`main` mode is `main`.

### 7.1. RB-007 and back to empty

* `HoleProbe 4000 20000` (028-53's): kept 189,240 bytes, the twin
  316,368 (`main` 4,804,384 and 315,008; 031-01's w 188,256).
  `HoleProbe 20000 20000`: 124,392, the twin 198,784 (`main` 5,361,912
  and 872,424). The last call with work 3,859 and 3,858 of 10,000
  (`main` 621 and 632).
* `TwoStretchProbe` (section 9.1): kept 19,480 bytes (`main` 790,264);
  `TwoStretchM1Probe`: 113,832 (the stretch-by-stretch form 781,208).
* `count-gates.sh all`: COUNT GATES OK. G5: kept 105,536 bytes
  (`main` 80,600; the twin 800), the last call returning true 3,007 of
  20,000 (`main` 3,006). G4 within its gates, its M5 (dead klongs)
  1.571 where 2 is the limit (031-01's prototype: 2.077). G1 110,992
  bytes, G2 1.232, G3 4.723.

### 7.2. Quiet when done

* `IdleLiveProbe LIVE SD 20 [10]` (028-51's), written in the last 10
  R, `main` in brackets: 30,000 values at sd 1 MB after 10 rounds, 0
  (24,522 kB), and 6,139 kB kept (9,989); 15,000, 0 (14,554 kB);
  100,000 at sd 1 MB, 0 (51,595 kB); 100,000 at sd 5 MB, 0 (55,421
  kB); and where `main` is quiet too, 0: 30,000 at sd 5 MB, 3,000 at
  sd 5 MB with and without rounds, 2,000 at sd 1 MB, 100,000 and
  30,000 at sd 50 MB.
* What the calls write until they are quiet, against `main` where it
  is quiet too: 7,013 kB (6,973) at 30,000 values and sd 5 MB; 1,056
  (1,055) and 601 (600) at 3,000; 20,444 (20,464) and 10,642 (10,636)
  at sd 50 MB. So w in the rows and the table in the take's records
  cost 0.6 % or less of a call-driven iteration.
* **The drain does not loop**: a sweep of 160 small databases not
  written to (50 to 6,000 values of 100 bytes, sd 10 kB to 5 MB, with
  and without 10 rounds of overwrites): nothing written in the last
  10 R in any.
* `IdleShapeProbe` (keys of 2 to 30 segments, values of 0 and 1
  bytes, where the index nodes are most of what an iteration writes):
  6 runs of the review's and a sweep of 36 (600 to 2,400 keys of 12
  and 30 segments, sd 10 kB and 1 MB, 5 rounds): nothing in the last
  20 R in any.
* **A database written slowly** is as on `main`: `TrickleProbe 30000
  1000000 20 10 EVERY`, written in the last 10 R: one value an R,
  30,798 kB (`main` 30,650); ten an R, 88,639 kB (88,311). Section
  10.3.
* **An empty transaction, or a setter's record**, counts as the
  application's: after either, in a database of 0.85 MB that was
  quiet, the calls write 0.87 to 0.89 MB (two iterations) and are
  quiet again (`WitnessProbe`'s phases).

### 7.3. w at every record, and P2

* `WitnessProbe SD EVERY 1 SEED`: a random workload of puts, deletes,
  empty transactions, setter records and calls, with phases of calls
  alone and an emptied database; sd 5,000, 20,000, 100,000 and
  1,000,000, a restart every 7, 23 and 101 operations, two seeds: 24
  runs, the same stream in each over 288, 1,268 and 4,166 restarts;
  54,384 starts after a record, 0 with another w (30 records skipped
  that lie before the stream's length at a cut of the same call: not a
  state that a crash leaves, as a cut waits for the stream to be
  durable to there); 0 records of another kind than their keys say;
  nothing written in the second half of each phase of calls alone;
  the emptied database ends at 59 to 399 kB kept.
* `Witness2Probe` (the review's: values of 0 bytes to 1.2 MB, the
  retain duration at 1 s, 1 s + 1 and forever, the startup distance
  changed between 10 bytes and 5 MB, time jumps): 4 runs, 3,128
  starts after a record, 0 with another w; the same stream over 2,662
  to 6,212 restarts.
* `UpgradeProbe`: a stream written in `main`'s mode (rows without w,
  empty take records, the filler key), then opened by the design: 4
  streams, 2,402 starts, 0 with another w; emptied, they end at 125
  to 189 kB kept.
* `StopAtProbe`: a stop from inside the call at each record of three
  scenarios, the records of a call that cuts among them: 165 stops, 0
  starts with another w.
* Codex's cases of 031-01 (`probes/codex/ReviewProbe.java`, logs in
  `probes/codex/logs/`): `recovery` (a setter after a recovery),
  `recovery empty`, `recovery stop`: w kept by the second start, and
  the calls bring the stream kept to 124,592 and 124,704 bytes, the
  same as the control without the extra restart; `bytes`: the same
  bytes.
* `MidCallProbe` (028-54): other bytes from the user record on, on
  `main` and on the prototype alike.

### 7.4. The stream's bytes

* StreamDigest quick against `main`: the 28 digests without reclaim
  identical; the 16 with reclaim differ, the four modes (plain, reads,
  restarts, restarts-once) the same in each configuration. Lengths:
  l3-every1 -0.92 %, l3-node8 -0.02 %, l3-node14 -4.6 %, l3-node62
  +0.14 %: `w=` in a row's text moves the steps' pace a little, in
  both directions; no record is added (031-01's store of w: +0.3 to
  +2.9 %).
* A row has thirteen names with w: its lines come in the order of a
  Java `HashMap` of thirteen entries, another order than with twelve
  (027-03, section 15, G16).
* A snapshot of a stream can differ by the take's phase: after
  `HoleProbe`'s second writes the prototype's stream is 1.9 % longer
  than `main`'s, the startup pos 160 kB further on; the index nodes
  written earlier there are written later on `main`.

### 7.5. Gates

* `java/before-commit.sh` on `47103353`: `BEFORE COMMIT OK (281 s)`
  on a loaded machine (132 s on the first prototype), with one test
  line changed: `Reclaim.Tester.testAllowanceCountsNodesMadeAfterTheRow`
  compares the stored row's text, which holds w.
  `testRestartResumesIteration` and
  `StorageFaultTester.testStopWhileReading`, which A and 031-01
  changed, pass as they are.
* The conformance on the unchanged trace checker (built in the
  clone, `lake build tracecheck`): the reclaim set, CONFORMANCE OK (40
  traces; r-maint and r-maint-sd among them); the crash set, OK (15
  traces; c-maint among them); e-r-maint of the evict set, OK (3
  traces). The same on the first prototype.

### 7.6. The independent review

An agent with the prototype's jar, its diff and the probes, and no
part in the design, was asked for counterexamples (2026-11-25, about
16 minutes). Its findings on the first prototype:

* An emptied database kept at 790 kB by the stretch-by-stretch M1
  (section 9.1): M1 changed to one threshold (R4).
* The filler left live by a stop between its put and its delete, on
  `main` too (section 9.2): the filler made one record (R2).
* No start with another w in 8,600 starts and stops of its own probes
  on the first prototype, `dc5b3059` (`Witness2Probe`, `StopAtProbe`,
  `UpgradeProbe`; run again on `47103353`, section 7.3); quiet when
  done in 24 configurations; no defect read in the diff.

A second round on `47103353`, with the one threshold and the filler
as a table (about 14 minutes):

* **No drain that goes on**: 1,608 databases not written to (300 to
  3,000 keys of 1 to 8 segments, values of 0 to 40 bytes, sd 10 bytes
  to 5 MB, 2 and 3 rounds, node sizes 8 and 14 among them), nothing
  written in the last 20 R in any. The margin is thin: 59 of them
  ended with w before fp, the last iteration's rewrites at or below X
  and 397 to 399 kB kept.
* **The padded table**: 899 configurations with the stream's length
  in every phase of the meta block distance; 286 had a filler, the
  smallest of 8 spaces; in each the cut came in the same call, one
  filler an iteration. 446 stops at and right after a filler: the
  same w, and the same stream kept as the run without the stop. After
  a stop right after it, the next commit, empty transaction or call
  cuts and stores the table without the padding (`PadStopProbe`);
  with the retain duration set to forever the padded table stays the
  table's value until it is finite again.
* **A stream of `main`'s mode with a filler left live**, opened by the
  design: 859 starts, 0 with another w; nothing broken but the 196 kB
  staying live (section 9.2).
* **w**: 4,411 more starts after a record, 0 with another w.
* One finding, on `main` too: section 9.3.

Not reviewed by Codex.


## 8. The Lean proofs

031-01, section 7, is the reference; it holds for this design as
written there, with these differences.

* **No statement, premise or checker rule changes.** lean/SIS's
  reclaim theorems (T13', T-COVER, T-LATEST, T8, T9, T12) and T3 do
  not mention an iteration's begin, the table, `maintain()` or whose a
  record is. The contract's theorems take the iterations as given.
* **The take's and the filler's records.** `MaintenanceOK`
  (lean/contract, ReclaimValues.lean) lets a maintenance transaction
  write only under reclaim's keys, or be a step. `main`'s empty take
  meets its first case with no operation; a store of the table meets
  it too, and so does the filler as a store of the table. A step still
  writes only its rewrites and its row (`StepOpOK`): the row's text
  gains a name, which no checker parses.
* **No transaction of w's own.** 031-01's condition, that w's store
  stays a transaction of its own and never joins a step's, falls
  away.
* **The checkers.** The trace checker and the contract's checkers need
  nothing new: the trace checker, unchanged, passes the reclaim and
  crash sets and e-r-maint on the prototype (section 7.5). The
  contract's checkers (lean/contractcheck) were not run; they check
  every transaction whatever its kind (031-01, section 7.1).
* **Proved, whatever w decides**: reads from fa on after every cut
  whose iteration's steps follow the model and meet RC1 and RC4.
  **Tested, not proved**: R3 (the probes of section 7.3), RB-007's fix,
  quiet when done, back to empty.
* **What becomes simpler to state.** R3 is a small inductive
  invariant over a sequence of records of two kinds, with the rows'
  w: a model of positions only (the pStarts, w, the last record's
  kind), not of the steps. Quiet when done follows from it and R4 in
  a few lines: with no application record after a pStart P, once fp
  has passed P, w < fp, and no call begins an iteration unless the
  last one rewrote at most X. That the cuts come (the waits end)
  stays tested. None is proposed for 2026.7.


## 9. Found on the way, on main

Both for the lead to register; neither is this item's to fix on
`main`.

### 9.1. An emptied database kept at 790 kB

M1's two stretches are tested one by one, so each can stay just below
MIN_RELEASE. `TwoStretchProbe 390000 390000 390000 10000 20000` (the
review's probe; a value put and deleted on each side of the second
iteration's pStart): `main` keeps 790,264 bytes after 20 R of calls,
789,560 more than a fresh database, where the Javadoc says about 400
kB and G5 allows 600 kB. B keeps the same. In 2026.6 and 2026.5 by
the same rule. R4's one threshold ends it (19,480 bytes kept).

### 9.2. The filler left live

A stop or a crash between the filler's put and its delete leaves
`/#i/dreclaim/-fill.txt` live, up to 200 kB of zeros, until another
filler is needed: 027-13, section 2, says it is never live after a
call. `StopAtProbe 10 100 20000` in `main`'s mode: after the stop and
20,000 calls, the filler is live, 199,672 bytes kept. With the filler
as one store of the table (R2) there is nothing to delete, and a
padded table left by a stop is replaced by the next store of the
table. A stream of 2026.6 with a filler left live keeps it under this
design, unless the landing deletes a live filler once (a read at a
start).


### 9.3. A database not written to, kept at several times its live values

A database written only while its stream is below 2 sd, then left to
the calls, keeps the stretch of its one iteration for good: the
values rewritten, and the index nodes that the calls' takes wrote
there, most of them replaced since. `IdleShapeProbe 3000 2 100
50000000 20` (the review's: 3,000 values of 100 bytes overwritten 20
times, sd 50 MB, 40 R of calls): 3,256 kB kept, 7.0 times the stream
of the same values put once, on `main` 3,245 kB. With w before fp and
505 kB rewritten, more than X, no iteration begins. B brings it to
885 kB and never stops (7 MB written in the last 20 R). A space cost,
no promise broken; O-7 measures a rule for it.


## 10. Options, and what Frans decides

### 10.1. The options

* **O-1. This design**: w read off the stream (R1 to R3), M1 with one
  threshold (R4), the take and the filler as stores of the table.
* **O-2. This design with `main`'s filler** (`-Dproto313.fill=key`:
  the put stores the table too, then the delete): no change of what
  the filler is; 9.2 stays to fix.
* **O-3. B** (028-53): one line, no state. Never quiet in a database
  not written to; 9.1 stays.
* **O-4. 031-01's repaired w, or A**: as counted in section 6.
* **O-5. A change of the promise**: the application asks for a pass
  (a call of its own, or `maintain()`'s first call after it returned
  false), and BergDB does one pass of two iterations each time,
  whether or not anything was written. No w. An application that
  calls at every idle moment rewrites its live values each time.
* **O-6. The drain dropped**, with the Javadoc's bound raised: R4
  without its last line. An emptied database then keeps reclaim's own
  records of its last two iterations, 921,504 bytes in 028-53's
  measurement of `HoleProbe 4000 20000`.

* **O-7. The drain by proportion** (`-Dproto313.m1=wr`): R4's last
  line as "the last row's rewritten is at most a quarter of the
  stream kept", in place of X. 9.3's case ends at 791 kB kept (1.7
  times the values put once), a second one at 1,871 kB where the
  design keeps 4,219. The other probes as with X: `HoleProbe` 189,240
  and 124,392, `TwoStretchProbe` 19,480, `IdleLiveProbe`'s runs
  quiet; 1,720 small databases not written to (the review's 840 and
  720, section 7.2's 160), none writing in the last half of the
  calls. But the row's `rewritten` does not count what the takes
  write, so the rule also begins passes that give little: with 3,000
  keys of 4 segments and empty values at sd 5 MB, 1,564 kB written
  where the design writes 853, for 711 kB kept in place of 853. Not
  reviewed.

Recommended: **O-1**.

### 10.2. What Frans decides

* **F1.** The design for 2026.7: O-1 (recommended), or another
  option.
* **F2.** The stream's format (018-01's rule): the name `w` in a
  row's text, which 2026.6 ignores and drops at its next store; the
  take's record holds the table; new streams hold no filler key. No
  meta version, no record format.
* **F3.** What counts as the application's writing: every record
  that is not reclaim's own, so also an empty transaction and a
  setter's record. Each can cost up to two iterations under calls.
  The Pub's `rw()` commits a record also when its action wrote
  nothing; whether such a commit should write a record at all is a
  question of its own (`RwTransaction.executeRwInner` executes its
  Core transaction whatever it holds).
* **F4.** X for the drain: MIN_RELEASE / 4 as measured (031-01's
  F4), or MIN_RELEASE / 8, with a wider margin against a drain that
  does not end (sections 3.4 and 7.6) and the same result for an
  emptied database, whose iterations rewrite under 1 kB; or O-7's
  proportion, if 9.3's space is to come back.
* **F5.** The Javadoc of `Db.maintain()` and `Database.maintain()`:
  whether it promises that the calls stop writing in a database the
  application no longer writes to; and its "within about 400 kB",
  which R4 keeps by the rule itself.
* **F6.** 9.1 and 9.2 on `main`: whether they are released bugs
  (033's rules), and their entries; 9.3 as a cost, or a 028 entry.
* **F7.** With this design or without: 031-01's F1 (one maintenance
  step), F5 (G4's M5 gate), F6 (the slowly written database) and F7
  (P2 inside a call, 028-54) stand as they are.

### 10.3. Not settled

* **A database written slowly** under calls rewrites its live values
  about once an R/4, as on `main` (section 7.2): any record of the
  application's makes the whole stream kept suspect. Only a count of
  the dead bytes would end it (section 5).
* **028-54**: not changed. The witness could serve there too: a start
  that finds a user record as the stream's last knows that its
  maintenance may not have run. Not designed.
* **A stream of 2026.6 with a filler left live** (9.2).
* **Not run**: `night.sh`, `level3.sh` and `level4.sh` in full,
  `timing.sh` (the commit path gains one comparison and, until the
  first application record after a begin, a test of the record's
  keys). No unit test of the design is written; section 11 lists
  them.
* **9.3**: a database not written to can keep several times its live
  values, as on `main`.
* **Not reviewed by Codex.**


## 11. Tests and gates for a landing

Failing on `main`, passing with the design; each a unit test of about
a second, sized from the probes:

* RB-007: `HoleProbe`'s two cases.
* Quiet when done: `IdleLiveProbe 15000 1000000 20 10`.
* Back to empty below 400 kB: `TwoStretchProbe`'s case.
* R3: a start after every record of a short mixed run
  (`WitnessProbe`, small), a stream with rows without w
  (`UpgradeProbe`), a stop inside a call that cuts (`StopAtProbe`).
* R1 and R2: every record of a run with calls is reclaim's own
  exactly when reclaim wrote it.
* The filler: no key `-fill.txt` after any call or stop; a padded
  table replaced by the next store.

Gates: `java/before-commit.sh`; `count-gates.sh all`; the
conformance's reclaim, crash, drain and evict sets; StreamDigest
quick (without reclaim identical to `main`, the four modes the same
with reclaim); RestartInvariance; `timing.sh` before the release.
Texts: 027-13, sections 1.1, 1.9, 1.10, 2 and 9; 027-03, section 15;
the Javadoc of `Db.maintain()`, `Database.maintain()` and
`MAINTAIN_MIN_RELEASE`; RB-007 in 033.


## 12. Files

* `prototype.diff`: the branch `031-03-proto` (`eae8d1da`: `47103353`,
  on which section 7 was measured, and the switch `wr`) against `main`
  at `e04663b5`. Switches, for the measurements only:
  `-Dproto313.m1=` `w` (the design, default), `wr` (O-7), `w2` (M1
  stretch by stretch), `w311` (031-01's M1), `main` (`main`'s bytes),
  `b` (028-53's B); `-Dproto313.fill=key` (`main`'s filler).
* `probes/`: `WitnessProbe` (this item's); `Witness2Probe`,
  `StopAtProbe`, `UpgradeProbe`, `TwoStretchProbe`,
  `TwoStretchM1Probe`, `IdleShapeProbe`, `PadProbe`, `PadStopProbe`
  (the review's);
  `codex/ReviewProbe.java` (Codex's of 031-01, printing w only) and
  its logs. `HoleProbe` is 028-53's, `IdleLiveProbe` 028-51's,
  `TrickleProbe` and `MidCallProbe` 031-01's. All in package
  `bergdb.core`, compiled against the prototype's jar and put before
  it on the class path, as their headers say.


## 13. State

2026-11-25, by an agent of lead-1125: the design (sections 2 to 4),
its prototype on the branch `031-03-proto` of the clone c313
(`eae8d1da`; `BEFORE COMMIT OK` on `47103353`, to which it adds a
switch) and its measurements (section 7), after an independent review
in two rounds (section 7.6). For Frans's decisions F1
to F7 (section 10.2); recommended O-1. Nothing on `main`.


## 14. Codex's review

Codex (GPT-6.1 Sol, reasoning effort max) reviewed the design and its
prototype (`eae8d1da`) on 2026-11-25, 17:03 to 17:17, at lead-1125's
request, with probes of its own; its report is outside the repository.

* **Held.** R1 to R3, the witness: every record of reclaim's carries w
  before it can hide a user record, and setters and empty transactions
  witness the application's writing themselves; no window like 031-01's
  unstored w. 031-01's four cases (Codex's own probe) keep w; 5,878
  restarts between calls give the same stream; 3,401 record boundaries
  and 27 stops inside calls give no wrong w; eight streams of `main` and
  2026.6, upgraded, 1,919 boundaries, no wrong w. HoleProbe 189,240 and
  124,392 bytes; TwoStretchProbe 19,480; IdleLiveProbe quiet. Section
  8's Lean claims check out; the unchanged trace and contract checkers
  pass (reclaim, crash, drain, e-r-maint; 3,838 transactions in a
  maintain-driven contract trace).
* **Finding 1, the drain.** With a reduced reclaim step reserve
  (`DbBuilder.reclaimStepReserve` = 1, a test setting) and 150 keys of
  111 bytes at node size 8, R4 lets a live database's drain repeat: a
  million calls, 866 iterations, 236 MB written, 118 MB in the last
  500 R; X = 50,000 gives the same. With the default reserve (4 MiB) the
  same case goes quiet, keeping 291,280 bytes. R4's threshold is a
  stopping condition, not a proof that the drain ends; the quiet promise
  holds at production settings in every run, not in general.
* **Finding 2, P2 inside a call.** A crash after a user record and
  before its iteration's begin changes the stream, as on `main` and
  2026.6 (028-54); the design does not make it better or worse.
* **Finding 3, a writable downgrade.** A stream of the design opened
  and written by 2026.6, then by the design again, can lose w: 2026.6
  stores a row without `w`, and the start reads the old default. A
  one-way upgrade is safe; a round trip needs a rule (refuse it, or
  read mixed rows).
* **Finding 4, an old filler.** A filler left live by 2026.6 or `main`
  (RB-010) stays live after an upgrade unless the landing deletes it.
* **Costs.** The stream's internal format changes: `w`, the take's
  contents, the padded table, and the order of the row's thirteen names
  (a HashMap); the framing and versions do not. The prototype adds 166
  lines and removes 17, with comments and switches.
* **Its view on F1 to F6.** F1: the witness (O-1) over A, B or a
  stored w, with its scope stated (production settings, or a bounded
  drain) and the P2 and downgrade limits written. F2: a compatible
  change of the internal format, with a rule for writable downgrades
  and a cleanup of old fillers, and a pinned order of the row's names
  if portability is promised. F3: as recommended. F4: a smaller X is a
  margin, not a bound; O-7 needs a review of its own. F5: keep "about
  400 kB" for an emptied database; promise quiet only at production
  settings until the drain is bounded. F6: 9.1 and 9.2 S4 (as 028-58
  and RB-010 now record), 9.3 a cost.


Log
===

2026-11-25. Created by lead-1125 at Frans's request (14:54); taken by
an agent of lead-1125 (Fable, high).

2026-11-25. The design, by that agent in the clone c313 (branch
`031-03`): w, the last pStart after which the application wrote, read
off the stream at every record (every record of reclaim's holds a row
with it, and a last record that is not reclaim's shows it), with no
store and no recovery case of its own; M1 with one threshold on the
stream kept; the take and the filler as stores of the table. A
prototype on the branch `031-03-proto`, `BEFORE COMMIT OK`. An
independent review found an emptied database kept at 790 kB by M1's
two stretches, on `main` too, and the filler left live by a stop
between its two records, on `main` too (section 9); its second round,
on the one threshold and the filler as a table, found no drain that
goes on and a database not written to kept at 7 times its live
values, on `main` too (9.3). The subitem a directory with the
prototype's diff and the probes.

2026-11-25. Codex's review (section 14): the witness holds; the drain
can repeat with a reduced step reserve (a test setting); a writable
downgrade can lose w; an old filler stays after an upgrade.
