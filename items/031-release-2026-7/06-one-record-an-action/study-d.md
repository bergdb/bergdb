# A1 (d): an action's records as one compound unit, a feasibility study

2026-11-27, by an agent of lead-1127, 09:44 to 10:20, for
006-37's question A1, option (d) (Frans, 2026-11-27, 09:28): the user's
record and its maintenance records form one unit, marked in the user's
record; a start treats an incomplete unit at the stream's end as a torn
record, so the whole unit is kept or void. Read: 031-05 (sections 2, 4 to
10, 12 and its review), 031-04, 006-37, 028-54, 028-60 (also its part 2 on
the branch `028-60b`), 010-01 (P1, P2, P3, P7), 027-03 (sections 6 to 8),
the history of reclaim's records (lead-1127, 09:30), and the code of
031-05's prototype (branch `031-05`, `4135ba2a`, `java/` at `8a6bb105`) in
a clone, `a1-d`. Three probes were written and run there (section 13); no
prototype of (d) was made, and no gate was run.

Each statement is marked: **ran** (a probe run here), **read** (the code or
an item, with the place), or **inferred** (reasoning, not checked).


## Verdict

**Feasible and clean, with three warts**, provided two choices that the
idea as stated leaves open:

* **The mark is the record's last byte, appended last.** Whether more
  records follow a user record is not known when the record is
  serialized (section 1), so a mark in its header needs a prediction (the
  review's F7) or an extra closing record (+1.6 % to +10.9 % of the stream,
  ran). The record's last byte, its commit byte, can carry it exactly: 10
  when the record closes its unit, 11 when another record of the unit
  follows; the writer appends a record without its last byte and appends
  that byte when it knows. Same bytes otherwise (ran, 4,563 layouts), no
  byte added, and the mark lives in the framing layer that recovery
  already walks.
* **The start cuts the void tail.** The stream is append-only, and today a
  torn record is completed and kept as an aborted record, not overwritten
  (read). Left in place, a void unit's bytes move every later record, as a
  torn record's do today (review, F2), and every reader would have to skip
  void units, with a second mark (section 2). Only with a cut of the tail
  at the end of the last closed unit is the stream after any crash, stop
  or restart exactly the stream of the accepted actions, at every byte, a
  torn record included. The cut can be made as 028-60's part 2 makes its
  zero-tail cut: left out at the start, truncated and forced by the first
  append, so a start writes nothing.

With these, every rule of (d) as stated holds (inferred, from sections 1
to 10): every action atomic, no roll-forward, no catch-up before a call's
own record, no held clock between calls, a refused call writes nothing, a
start never appends, and the Lean theorems apply as they are.

**The warts:**

1. A new storage operation, a cut of the tail at a given position (in
   `AppendOnlyStream` and its classes, `FileStream` truncating and, for a
   unit that spans files, deleting files): it sets aside Frans's
   decision of 2026-11-26 for 028-60's part 2, which keeps
   `AppendOnlyStream` and `RecoverableStream` unchanged (028-60, section
   7).
2. Positions are written twice: the internal encryption's keystream
   depends only on the key, the nonce and the position (`SalsaStream`'s
   Javadoc, 020-24-07, U7-1), so a void unit's positions get a second
   plaintext under the same keystream.
3. A file copy that overlaps the first append after a start that cut is
   not a backup, as 028-60's part 2 already says of its cut; with (d) it
   applies after every crash inside an action, not only after zeros.

**Against (c)** (the start writes what is due): (d) is exact at every
byte (also F2's torn record), keeps the Lean statements unchanged, makes a
start write nothing, and lets reclaim's multi-record work back in (the
after-row record of 028-26, the open B1 and F8); it costs the storage cut
and about 1.2 to 2 times (c)'s production lines (section 7). Nothing found
breaks it outright (section 10).


## 1. The mark

* **Where a mark can live** (read: 027-03, sections 7 and 8.1).
  * The record header: bytes 5 to 7 are written zero and skipped by the
    parser (`StoredTrans.Parser`, `offset += 3`), a place for a flag. It is
    written with the record's first bytes.
  * The transaction's bytes (a node or a KV): inside the node layer, which
    recovery does not read.
  * The record's last byte: 10 for a committed record, 0 for one that
    recovery's fill aborted; any other value is refused (`NodeStream`'s
    `readRecordHeader` and `TransIterator.next`: "Bad lastByte"). It is
    the last byte appended, and the framing layer
    (`RecoverableStream`) reads it.
* **Is "maintenance follows this record" known before the record is
  appended? Not exactly** (read: `Reclaim.catchUpRecord`, `commitWork`,
  `markSafePositions`, `cutRow`; `Db.store`; `NodeStream.appendNodes`;
  `RecoverableStream.append`, `writeMetaBlock`).
  * B or S is decided from the record's end (`lastEnd`) and time
    (`lastTime`), which `recordWritten` sets after the append; both are
    computable from the serializer's output.
  * P depends on the startup pos after the record's take (set in
    `store()` before the append).
  * C reads the last valid meta block's `lastTrans`
    (`getLastTransPosOfLastValidMetaBlock`), which the record's own append
    changes when it crosses a block's position.
  * The writer itself learns that it wrote a record by the stream's
    length changing (`catchUpRecord`); a `step()` can return without one
    (review, F7).
  * So a mark in the header needs a predicate that copies these
    decisions, the trap of F7.
* **How often maintenance follows** (ran: `UnitProbe`, section 13; the
  prototype in D2, 20,000 commits each, retain duration 1 s): 8.2 %, 4.4 %
  and 1.1 % of the user records (sd 2 kB, 100 kB, 1 MB; values up to 3,000,
  1,000 and 100 bytes); a unit had at most 3 records.
* **The designs compared** (inferred, with the probe's figures):
  * *A "more follows" bit on every record but the unit's last*: the
    information needed is whether a record is the last; in the header it
    needs the predicate.
  * *A count on the first record*: needs the whole unit predicted; the
    worst.
  * *A closing mark on the last record*: the same information as the bit,
    the same problem.
  * *An always-present end* (an empty closing record after every user
    record): exact, no predicate; +1.6 %, +3.3 % and +10.9 % of the stream
    in the three runs (48 bytes against mean user records of 2,293, 878
    and 321 bytes). After only the records that have maintenance it would
    be +0.12 % to +0.15 %, but then the user record must be marked open in
    advance: the predicate again. An empty record also meets every place
    that reads the stream's last record (`Reclaim.initFromDb` reads `a`,
    031-04 R3, off the last record when it is not reclaim's own, and
    `isOwnRecord` goes by keys, which an empty record has none of).
  * *The last byte, appended last*: exact and free. The writer appends a
    record without its last byte; the byte follows when the writer knows:
    11 just before the next record of the same unit, 10 when the action
    ends. The decision is the writer's own (it ran the next record, or
    found none), not a copy of it. A record's nodes end before its
    end-of-nodes marker, got-dirty list and padding (027-03, 8.1), so no
    node read needs the last byte. Appended in two parts, a record gives
    the same bytes and meta block positions as in one: 4,563 of 4,563
    layouts before, at and across a meta block's position (ran:
    `LastByteProbe`).
* **Recommended: the last byte** (10 closes the unit, 11 more follows). A
  maintain() part, a setter and the end of an action write 10; a record of
  a stream of an older release, with 10, reads as a unit of one.


## 2. The start

* **Today** (read: `Db.startInner`; `RecoverableStream.recover`,
  `readLastValidMetaBlock`, `checkLastTransSpos`, `fixMetaBlockIfNeeded`,
  `fixLastTransactionIfNeeded`, `transHeaderFixBytes`, `appendZeros`;
  `Db.readStartupPos`, `getStartupPosFromLastTransaction`):
  * the start refuses an incomplete creation and another node size, then
    recovers: the last valid meta block (a block of zeros is not valid,
    028-60 part 1), its `lastTrans` checked;
  * it completes a meta block that the end cut (the template, or zeros),
    and walks the records by their sizes from the block's `lastTrans`; a
    record that the end cut is completed with zeros and aborted (last byte
    0), a cut size field first completed by `transHeaderFixBytes`; a size
    below 5 is refused ("Bad transaction size");
  * then the walk of `getStartupPosFromLastTransaction` skips aborted
    records, takes the last record's startup pos and sets the meta block's
    `lastTrans` to the last record; `readTransactions` and `DbStarter`
    follow.
  * On the branch `028-60b`, `FileStream` leaves a run of at most 8 MB of
    zeros at the end of its last file out of the stream at open, and the
    first append truncates the file there and forces it (028-60, section
    8).
  * So a start writes today (the fills; 027-03's G18: also a start refused
    later), and a torn tail is not overwritten: it stays as an aborted
    record, and every later record moves (review, F2: 0 of 1,038 continued
    streams equal).
* **What changes** (inferred): `recover()` walks as today, by size, and
  also reads each record's last byte; the stream's end E is the end of the
  last record whose last byte is 10 and whose records before it are whole.
  Records after E (an open unit, a torn record, a cut meta block, zeros)
  are outside the stream: reads stop at E, and the first append cuts the
  files at E and forces the cut before it writes. The fills go, and so do
  aborted records: the last byte is 10 or 11.
* **A start never writes** (inferred): nothing is due after a closed unit
  (the unit's loop ran until nothing was due; ran: in D2, `catchUpDue()`
  was false after each of 60,000 commits, `UnitProbe`), and the cut is
  the first append's. A start refused after the walk (another record format)
  leaves the files as they were, which fixes 027-03's G18.
* **The void bytes cannot be left in place** (inferred). The stream is
  append-only (`AppendOnlyStream`: bytes appended are never modified, the
  length only grows; read), so the next append would follow them:
  * every later position moves, and the stream is no longer that of the
    accepted actions (F2's case, for every crash inside an action);
  * a restart's next unit would follow an open unit, and its closing
    record would close both: the walk would take the voided transaction
    as accepted. A second mark (the first record of a unit) would be
    needed, and every reader (the start's rerun, `getTrans`,
    `TraceExport`, `StreamDigest`, the C clone) would have to skip void
    units anywhere in the stream.
* **An incomplete creation** (inferred): the creation's two records (the
  primordial record, 11; the startup distance's, 10) are one unit, so 028-18's
  cases (`isIncompleteCreation`, `holdsFirstTransactionAlone`) become "no
  closed unit": refused as today, by one rule.
* **The meta block at E** (inferred): when E is a block's position and
  the eager block is missing or cut, the first append writes it
  (`RecoverableStream.append`'s case `blockPos == 0`; read) with the same
  bytes as the uninterrupted run's, given the rule of section 3 on
  `lastTrans`. Today recovery writes the template there (an invalid
  block), other bytes than the eager block (the review's last open point).


## 3. Meta blocks, the startup pos, the safe positions, sync and durability

* **Meta blocks inside a unit name records of the unit** (ran:
  `UnitProbe`): in the three runs, 74, 57 and 14 meta blocks were written
  during a later record of a unit than its first, and each of them names a
  record of its own unit (74, 57 and 14), as `appendNodes` sets the block's
  `lastTrans` after every record (read); 226, 87 and 30 were written during
  a unit's first record, naming the record before the unit. A block of the
  first kind names a record of a unit that may be void.
* **Rule M** (inferred): `lastTrans` changes only when a unit closes, to
  its closing record, before the closing byte is appended, so that a block
  written right after that byte names it; a start sets the same value (the
  record ending at E). Then a valid block names only a record of a closed
  unit, the walk of section 2 starts at one, and a block inside a void
  tail names a record at or before E. Enforced in `NodeStream` (the unit's
  close) and checked by a unit test with a block inside a unit and by the
  crash-at-every-byte probe of section 8.
* **After the cut** (inferred): `posOfLastValidMetaBlock` and its
  `lastTrans` must be those of the last valid block before E, not one
  inside the void tail; `recover()` reads again below E when the block it
  found is past E.
* **The startup pos** (read: `Db.checkStartupPos`): a record's startup
  pos is before the record, so the last kept record's names a kept record.
* **The safe positions** (read: `markSafePositions`): pSafe is the stream
  length when P is written, inside P's unit, and void with it.
* **sync()** (read: `Db.sync`, `ExecuteData.end`): `sync(0)` takes
  `x.endOfLastTrans` under the write lock, and a unit holds the lock from
  its first record to its close (D2's maintenance runs in
  `transactionCompleted`, under the lock), so it sees only closed units.
  `sync(pos)` with a caller's position takes `pos + 1`; a position inside
  an open unit (a get's tpos during the unit) would return when those
  bytes are durable. Rule: a position at or past the end of the closed
  units waits for the write lock and syncs to the unit's end (inferred).
* **Durability and the cut** (read: `pretruncateAt`, `cutIfDurable`): the
  physical cut waits until the stream is durable up to the length after
  C's record. If records followed C in its unit, a crash could keep the
  cut and void its decision. Rule: the cut waits for its unit's end
  (inferred; set at the close).
* **Forced appends** (read: `AppendOnlyStream.append`'s Javadoc):
  `FileStream` forces each of its appends; a unit can span several, so
  part of an open unit can be forced and then cut at a start. Nobody was
  told: `execute()` had not returned, and `sync()` waits for the close.


## 4. Reclaim's positions and the cut

* **The cut is inside a unit by construction** (read: `commitWork`): an
  iteration's pStart is `lastEnd`, the end of the user record whose
  maintenance begins it, and pCut is an earlier pStart: the start of a B
  record, after its unit's user record. So the stream's front after a cut
  can begin in the middle of a unit.
* **That is harmless** (inferred): a unit's atomicity matters only at the
  stream's end. The start walks from a closing record named by the last
  valid meta block (which the cut keeps: `cutRow`'s `metaTransPos >=
  row.pCut`; read), the startup section and `getTrans`'s walks from the
  cut go by record sizes (read: `getStartupPosFromLastTransaction`,
  `createTransIteratorAtCallersPos`), and none needs a unit's first
  record. No rule makes a unit uncuttable; none is needed.
* **pEnd, pSafe, tStart, tEnd** are positions and times of records inside
  units; each is in the unit that writes it and is void with it
  (inferred).
* **Multi-record work comes back** (inferred): inside a unit, a crash
  cannot come between two of its records. So:
  * 028-26's second record after a step (`storeCurrent`, the after-row
    charge; 031-05's N6) can stay: B1 and the review's F8 are answered;
  * the done table record after the last step (N7) could stay too; the
    prototype's done row in the step is fine either way;
  * a maintain() part of several records (031-04's M1 to M6) would be
    atomic, so 031-05's one record a part (Q7) is no longer needed for
    crashes; it can stay for the budget's granularity.


## 5. stop(), a failure, and memory ahead of the stream

* **stop()** (read: `Db.stop`, `closeStorage`; `executeLocked`): stop()
  sets STOPPING at once, and its close takes the write lock first ("a
  transaction that runs has ended"). On the prototype, reclaim's internal
  transactions are refused at their entry when STOPPING, and a
  `DbStoppingException` from the maintenance is caught: the commit
  returns, "committed", its maintenance left to the next start (015-53).
  Under (d) that would be an `execute()` that returned with its unit open,
  void at the next start: a call reported as accepted that is not. Ran
  (`StopProbe`, D2): stop() right after the user record of 30 commits
  whose calls write maintenance: `execute()` returned normally in all 30,
  and none of the 30 wrote its maintenance.
* **Rule S** (inferred): the records and reads of an open unit are not
  refused by STOPPING; the unit completes, then the close runs. So a stop
  never comes inside a unit, and stop()'s Javadoc ("a transaction that
  runs completes, and is written") holds for its maintenance too.
* **A failure (P7)** (read: `executeLocked`'s try around
  `transactionCompleted`, `fail()`): in D2 the maintenance runs inside the
  commit's go point, where any exception fails the database, as on
  `main`. Under (d) the go point extends to the unit's close; the
  catch-ups before a call's own record, which F7 found outside it, are
  gone (section 7). `execute()` throws `DbFailedException`, whose Javadoc
  says that whether the transaction is in the stream is known after the
  restart: it is not, unless the failure came after the close (inferred).
* **Memory ahead of the stream** (read: P7, `assertDbStateIsActive`):
  after a failure every read and write is refused until a restart, so the
  memory that holds the void unit is never read again. `close()` called
  from a listener inside a transaction closes the storage under the unit;
  its next append fails, `execute()` throws, and the unit is void at the
  start (inferred).
* **A refused call** writes nothing (inferred): nothing precedes an
  action's own checks, as nothing is due between units; Q8 and B6 are
  gone.


## 6. Readers and the clock

* **Values are visible before the unit closes, as today** (read:
  `executeLocked`): `dbClock.transactionEnd()` comes before `store()`, so
  a lookup at the transaction's time sees it before its record is
  appended, and a crash then loses it. Under (d) the window lasts to the
  close, a step of reclaim at most (P1's bound, as D2's call).
* **The record is not**: `getTrans` waits for the write lock when the
  position is at or after `appendedEnd` (021-13; read), and with
  `appendedEnd` moved at closes only it waits for the unit
  (`transactionInfo` too).
* **The clock**: maintenance records take the last record's time plus one
  (`DbClock.maintenanceBegin`; read), so `currentTime()` must not run
  ahead of them during the unit: the hold is needed inside a unit only,
  from the action's go point to its close. Between calls nothing is held:
  maintenance comes only right after an action's own time (inferred).
* **The difference from today's committed but unsynced transaction**
  (inferred): the same kind, visible and lost by a crash. One difference:
  with `FileStream`'s forced appends, today a user record survives a
  crash once its own append returned, before `execute()` returns; under
  (d) only once its unit closed. Neither is promised before `execute()`
  returns.


## 7. What goes and what comes; the size against (c)

All inferred, from 031-05's section 6.7 (its breakdown of the
prototype's 231 production lines), the review's F6, the code, and
028-60's part 2 (about 100 to 220 production lines in `FileStream`, by a
rough count of its diff).

* **Goes from the prototype** (about 120 of 231 lines):
  * the catch-up before a call's own record (four sites) and the D1/D2
    switch;
  * the trigger read off the stream at a start (`isTrigger`,
    `lastIsTrigger` in `initFromDb` and `recordWritten`): maintenance runs
    only right after the action's record, inside its unit;
  * the "would write" predicates (`catchUpDue`, `safeDue`, `cutDue`, the
    split of `pretruncateIfPossible`) and the hold between calls
    (`holdIfDue`, the count of maintain() calls);
  * with them Q8, F5 and F7 (a predicate that must match its writer).
* **Stays** (about 110): the times (`Trans.maintenance`,
  `maintenanceBegin`, `actionTime`, the floor), the loop of `catchUp`
  after a user record, the done row in the step, one record a part (now
  optional), `maintain(int, int)` for probes.
* **Comes:**
  * the mark and the close: `NodeStream` (a pending last byte, the
    logical end, `appendedEnd` and `lastTrans` at a close, a read of the
    pending record on the writer's thread), `RecoverableStream` (an append
    without the last byte, the closing byte), `Db` (the close of every
    action, rule S, sync's rounding, the cut's durable position): about
    70;
  * the start: the walk to E and the logical end, about 40;
  * the tail cut through the stream classes: about 60 to 100 on top of
    028-60's part 2, 150 to 200 without it;
  * 028-26's after-row record back, about 15.
* **Goes from recovery**: the fills (`fixLastTransactionIfNeeded`,
  `transHeaderFixBytes`, `appendZeros`, `fixMetaBlockIfNeeded`: 78 code
  lines, counted) and most of the incomplete-creation cases (68 lines,
  counted, to about 15): about 130.
* **Net**: (d) about 170 to 300 production lines over 031-04's
  prototype; (c) about 135 to 155 (231 less F6's 80 to 100, plus 4), with
  the after-row charge still open. Tests: (d) about 300 to 500 added (the
  cut, kills, a unit at every byte, meta blocks in a unit, a stop and a
  failure inside a unit), 150 to 250 removed (the fills' tests); (c) about
  30 to 50.
* **Per commit**: no byte added; one more append into the storage for
  each record (its last byte). Not measured.


## 8. The tools and the tests

All inferred, from the code read (`TraceExport`'s header and
`record()`/`parseRecord()`, `P2CrashProbe`).

* **TraceExport**: every call's first record is its own (no catch-up
  before it), as it assumes. Its hook parses each record right after its
  append (`parseRecord` reads `readTransBytes(tpos)`), on the writer's
  thread, before the record's last byte is appended: `NodeStream` must
  serve a read of the pending record (above). Its `crash=K` mode crashes
  after a step's record, inside a unit: the unit is then void, so its
  lines must be held until the close and dropped at a crash, and the
  voided user transaction run again. "The start itself appends no record"
  still holds.
* **The trace format 027-02 and the checkers**: unchanged if the trace
  holds closed units only; optionally the closing byte on a record line.
* **StreamDigest**: other digests (the last bytes, the after-row record,
  no catch-up); its modes must agree as before. **RestartInvariance**:
  restarts are between calls, so between units: unchanged.
* **Kill tests** (`kill-restart.sh`, 031-02's KillWriter): their oracle
  takes any state from the last synced to the last executed transaction,
  which (d) keeps; new is a kill during the first append after a start
  (the cut), which repeated kills reach.
* **P2CrashProbe**: the rule changes to "an action is accepted if and
  only if its unit closed", and crashes at every byte (031-05 review's
  `TornProbe`), not only at record boundaries: every continued stream is
  to equal the reference.
* **Recovery's tests** of the fills (`RecoverableStream.Tester`'s
  `crashIn*`, `testTransHeaderFixBytes*`, `testZeroedTail*`;
  `DbTester.testCrash8InCreation`) become tests of the walk and the cut.


## 9. The Lean model

Read: lean/README.md, `T1_crash` and `T2_restart` (lean/SIS/Theorems.lean),
`T12_restartCut` (lean/SIS/ReclaimTheorems.lean), 031-05's section 9 and
the review's F3.

* **A unit need not be one record of the model.** The model's records are
  Java's (the internal transactions are in its list, given, not chosen).
  `T1_crash` keeps a prefix of whole records for any k, `T2_restart`
  takes a restart after any transaction, `T12_restartCut` a restart from a
  cut after any; a crash or a restart at a unit's boundary is one of
  these. So all three apply unchanged (inferred).
* **What is proved then**: a crash, a restart or a cut at a unit
  boundary changes no record of the given list.
* **What is assumed and tested**:
  * A-UNIT, the bytes: a start keeps exactly the records up to the end of
    the last closed unit (section 2); tested by crashes at every byte;
  * A-ACCEPT: an action is accepted if and only if its unit closed
    (`execute()` returns after the close, rule S); tested by stops and
    failures at every record of a unit;
  * A-DUE, as for every option: a unit's records after the action's own
    are a function of the stream before the unit and of the action; tested
    by P2CrashProbe, StreamDigest, RestartInvariance, later a C-DUE check.
* **What changes in lean/**: nothing is required. Optional: a corollary
  over a list of units (a run of units, a crash cut back to a unit
  boundary), about 50 to 150 lines without Mathlib, and its line in
  lean/README.md's list of axioms printed. 031-05's `T16_crash` (600 to
  1,100 lines by the review), a crash inside a call continued by a later
  writer, is not needed: in (d) no writer continues another's call.


## 10. Attempts to break it

Each inferred unless marked.

* **A unit larger than a file**: the void tail can span files; the cut
  deletes the later files, last first, and truncates the one that holds
  E, each forced, so that a crash during the cut leaves a prefix and the
  next start finds the same E. More than 028-60's part 2, which cuts in
  the last file only.
* **A unit larger than the write buffer** (`BufferedStream`, 10 MB by
  default; its writes at most 5 MB, 028-60): the buffer writes parts of a
  unit, which is fine: atomicity comes from the mark, not from the
  writes.
* **The limits**: a value of 8 MiB, a transaction of 32 MiB (L5; read:
  `Db`'s Javadoc), a record of up to 2^31 − 9 bytes (027-03, 8.3): one
  record each, unchanged; a unit is the user record and at most a few
  records of maintenance (3 in the probe; ran), so a crash's void tail is
  about one user record and its maintenance.
* **A bound on the cut**: 028-60's part 2 bounds its zero cut to 8 MB, so
  that a power loss that destroyed forced bytes is not silently repaired.
  (d)'s cut needs a bound too, at least one unit at the limits plus one
  write of the buffer; a longer tail would be refused as damage (Q-D3).
* **Hard sync inside a unit**: forced bytes of an open unit can be cut
  (section 3); no promise covers them.
* **The Pub layer's index jobs**: their commits are actions of their own
  threads, each its own unit; they stay outside P2 (031-05's N9, B2).
* **Setters**: a unit of one record; what a setting makes due waits for
  the next unit, so the cut moves at the next commit, as on `main`, and
  `testRestartWithOtherRetention` (the review's F1) is unchanged.
* **A commit handed the write lock between maintain() parts** (031-04's
  Q9): each part holds the lock and is a unit; the commit's unit comes
  between two, closed. No unit is ever interleaved.
* **What a maintain() call or a setter leaves due** (P, C) waits for the
  next unit; no hold is needed, as it is then timed after a fresh action's
  time.
* **The creating start**: a unit of two records (section 2).
* **Encryption** (read: `SalsaStream`; 028-60's C1 in 006-37): the cut
  rewrites positions under the same keystream (wart 2). The walk and the
  cut work on plaintext (`RecoverableStream` sits above `StorageManager`,
  `BufferedStream` and `SalsaStream`; read: `Db`'s constructor,
  `StorageManager`, `DatabaseBuilderImp`), so they also do for encrypted
  streams what 028-60's C1 asks of its option (b), a repair at the record
  level.
* **Backup by copying files**: a copy of a stopped database, or one taken
  between appends, holds whole units and a void tail at most, which its
  own start cuts; a copy that overlaps the first append after a start
  that cut is not a backup (wart 3).
* **Reads of the open unit's record on the writer's thread**:
  `TraceExport`'s hook does it (read); in `src`, the record readers are
  `getTrans` and the Pub's `transactionInfo` (read), which a listener could
  call inside the call. `NodeStream` serves the pending last byte from
  memory for such a read.
* **Damage that is not a tail** (stale bytes, 028-67): as today, outside
  the contract; the walk stops at the first record that is not whole and
  the bound limits what it cuts.
* **Not broken by**: P1 (the unit holds the lock as D2's call does), P3,
  eviction (a pending record's nodes are appended; only its last byte
  waits), the take (unchanged per record).


## 11. The smallest clean design

Each rule says what, when, by whom, and how it is checked (inferred, not
built).

1. **The unit.** Every action's records form one unit, written under the
   write lock within the action's call: a transaction's record and the
   maintenance that the stream makes due after it; a maintain() part; a
   setter's record; the creation's two records. Db ends every action with
   the unit's close; nothing else ends one. Checked by P2CrashProbe at
   every record and every byte.
2. **The mark.** A record's last byte is 11 when another record of its
   unit follows and 10 when it closes the unit. `NodeStream` appends a
   record without its last byte, and appends that byte as 11 before the
   unit's next record, or as 10 at the close. Checked by a unit test (every
   action's last record ends in 10, the others in 11) and by the start's
   walk.
3. **Publication at the close.** Only a close makes a position public:
   `appendedEnd` (for `getTrans`), the meta block's `lastTrans` (the
   closing record, set before its last byte is appended), the end that
   `sync()` waits for, and the position the cut of reclaim waits for. A
   `sync(pos)` inside an open unit waits for its close. Checked by unit
   tests with a meta block inside a unit and a sync from another thread
   during a unit.
4. **The start.** `RecoverableStream.recover()` walks the records from
   the last valid meta block's record by size and last byte; the stream
   ends at E, the end of the last record with last byte 10 whose records
   before it are whole. Reads stop at E; the first append cuts the files
   at E and forces the cut before it writes; a start writes nothing. A
   stream with no closed unit is a creation that did not complete. Checked
   by crashes at every byte with the continued stream compared byte for
   byte, `kill-restart.sh`, and tests that a refused start leaves the files
   as they were.
5. **The atomic call.** From an action's go point to its close nothing
   refuses it: an exception fails the database (P7), and stop() waits, as
   the unit's records and reads are not refused while STOPPING.
   `execute()` returns only after the close, so an action is accepted if
   and only if its unit closed. Checked by a stop from another thread and
   an injected failure at every record of a unit.
6. **Maintenance inside units only.** Maintenance is written only right
   after an action's own record, in its unit, decided from the stream and
   the action, timed from the last record; nothing comes before an action's
   own record, and the clock is held only inside a unit. What a call
   leaves due waits for the next unit. Checked by StreamDigest,
   RestartInvariance, HoldProbe (0 hold failures) and P2CrashProbe.


## 12. Open questions for Frans

* **Q-D1. The cut of the tail** (wart 1). (d) as stated needs a storage
  operation that removes bytes after the last closed unit, made by the
  first append, against the decision of 2026-11-26 for 028-60's part 2
  (no change in `AppendOnlyStream` and `RecoverableStream`).
  * Options: (a) the cut, and the stream after any crash is that of the
    accepted actions; (b) no cut: void units stay, every reader skips
    them, a crash inside an action is an input as F2's torn record.
  * Recommended: **(a)**. It also does 028-60's part 2 at the record level,
    for encrypted streams too (its C1).
* **Q-D2. The mark.** Options: (a) the record's last byte, appended last
  (10 closes, 11 more follows); (b) a header flag with an empty closing
  record after every user record (+1.6 % to +10.9 % of the stream, ran);
  (c) a header flag set by a predicate (F7's trap). Recommended: **(a)**.
* **Q-D3. The bound on the cut.** Options: (a) one unit at the limits plus
  one write of the buffer, a longer tail refused as damage; (b) no bound.
  Recommended: **(a)**, as 028-60's 8 MB for zeros.
* **Q-D4. The internal encryption** (wart 2). Options: (a) record in
  017-10 that the stream's positions can be written twice, so its design
  needs a keystream that changes then; the internal `SalsaStream` (tests
  only since 2026.4) accepts the reuse until then; (b) no cut for encrypted
  streams. Recommended: **(a)**: (b) is two designs.
* **Q-D5. Backups** (wart 3): the barrier of 028-60's part 2 for a copy,
  after every start that cuts. Recommended: **accept**, in `Database`'s
  and `FileStream`'s Javadoc.
* **Q-D6. stop() inside an action** (rule 5): a stop waits for the unit,
  where 015-53 let it end reclaim's work after a commit. Recommended:
  **yes**: otherwise a returned `execute()` can be void.
* **Q-D7. Multi-record maintenance** (section 4): restore 028-26's
  after-row record (answers B1 and F8) and keep one record a part only
  for the budget. Recommended: **yes**.
* **Q-D8. What a call leaves due waits for the next unit** (P and C after
  a maintain() call or a setter; F1 then stays as on `main`).
  Recommended: **yes**: no hold, no catch-up, the same bytes after a
  restart.


## 13. Probes run

In the clone `a1-d` (branch `a1-d`, from c315's `031-05` at `4135ba2a`),
`probes-a1d/`, on the prototype's jar (`java/build.sh`), macOS, JDK 27,
2026-11-27 (ran):

* **UnitProbe** (`-Dproto315.eager=true`, D2): a seeded workload of
  20,000 commits (puts of one key, 15 % deletes), retain duration 1 s;
  the records of each call grouped into its unit.
  * sd 2,000, 200 keys, values up to 3,000 bytes: 1,643 of 20,000 user
    records with maintenance (8.2 %); units of 1, 2 and 3 records: 18,357,
    1,462, 181; mean user record 2,293 bytes, maintenance record 7,839;
    meta blocks in a unit's first record 226, after it 74.
  * sd 100,000, 10,000 keys, up to 1,000 bytes: 885 (4.4 %); 19,115, 876,
    9; 878 and 12,699 bytes; blocks 87 and 57.
  * sd 1,000,000, 100,000 keys, up to 100 bytes: 215 (1.1 %); 19,785, 214,
    1; 321 and 11,053 bytes; blocks 30 and 14.
  * A 48-byte closing record after every user record: +1.6 %, +3.3 %,
    +10.9 % of the stream; after those with maintenance only: +0.13 %,
    +0.15 %, +0.12 %.
  * Also: every meta block written during a later record of a unit than
    its first names a record of its own unit (74, 57 and 14 of 74, 57 and
    14); `catchUpDue()` under the write lock after each call: false after
    all 60,000 calls.
* **StopProbe** (D2, seed 1, sd 2,000, values up to 3,000 bytes at 200
  keys): a first run finds the commits whose calls write maintenance; for
  the first 30, a run of the same actions stops the database in the test
  hook of that commit's user record. `execute()` returned normally 30
  times, threw 0 times; the maintenance was written 0 times.
* **LastByteProbe**: `RecoverableStream` on a `MemoryStream`, a record
  appended whole or as its bytes but the last and then its last byte,
  records of 48 to 4,096 bytes ending 8 to 56 bytes before a meta block's
  position, at it, or 8 bytes past it (over the block): 4,563 of 4,563
  cases give the same bytes and length.


## State

2026-11-27, 10:20. Done: the ten points, the design, the questions,
three probes. Not done: a prototype of (d) and any gate; the cost of the extra
append per record (not measured); `FileStream`'s cut across files (read
from 028-60's part 2 only, not built); whether a production listener
reads its own record inside the call (only `TraceExport`'s hook found);
the bound's number; the C clone; option (e), studied separately.
