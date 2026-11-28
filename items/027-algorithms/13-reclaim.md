# 027-13. Reclaim

Created 2026-11-13 by Frans Lundberg. Status: read by Frans (2026-11-13,
12:34: "027-13 is good! I looks really good."); the pilot part of 027-04,
section 5.1, step 3, and the template for the other parts. Brought up to
date with one record an action (031-06) on 2026-11-28.

Part 9 of 027 (027-04, section 2.3; Level 3): how the front of the stream
is cut. The rule as `main` has it at 8a0897cf (2026-11-28), read from the
code; first written from 03f38f24 (2026-11-13; `java/` and `lean/` as at
1a53e45c). Since 031-06 (landed from 2026-11-27 to 2026-11-28) reclaim
writes no record of its own after a commit: its work rides in the records
of the actions, decided from the stream before each record. It replaces
027-01's `levels.md`, section 6, and `sis-model.md`, section 15.3, both
stale since 026-05 (there a step scans at tStart and reads each KV
again). The bytes are 027-03's (section 8.5 for what a record holds); the
take, D, Rule A and the startup pos are part 6's (until it is written,
027-01's `sis-model.md`, sections 5 and 6). Each claim carries one status
word of 027-04, section 2.2.


## 1. What it does

With a finite retain duration R, reclaim keeps every state from now - R
on readable and lets the storage drop the stream before a cut position.
It works in iterations. An iteration fixes a cut position pCut and then,
in steps, puts again every live value stored before pCut, with the same
key and value, a copy; the copies make the index nodes on their paths
dirty, so the take writes them again after pCut. When the iteration has
ended, its nodes are written and its end is older than R, the stream
before pCut is cut, and lookups before the iteration's end time are
refused.

Every accepted action appends exactly one record (031-06, section 2,
rule 1), and reclaim's work rides in the records of two kinds of action:
a commit (1.2) and a part of `maintain(budget)` (1.10). Under the write
lock, before the record's go point, reclaim plans what the record carries
from the stream before it, the record's time and the action's KVs
(`Maintenance.plan`); after the record is appended, it brings its memory
to the state after the record (`Maintenance.apply`), as a start reads it
off the stream (1.9). Nothing is written between two records. Until
031-06 reclaim wrote its work after a commit's record, in internal
transactions of its own (1.2).

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
  otherwise it commits one internal transaction with the KV, whose record
  carries no maintenance (031-06, rule 11), and the new values hold from
  the next record.
* **sd**, the startup distance in force; **sp**, the startup pos that the
  take set for the last record written, which that record stores (after a
  start, the one read from the last record); **mp**, the position of the
  transaction that the last valid meta block names (027-03, section 6),
  where recovery starts; **fa** and **fp**, the first available lookup
  time and position, 0 until the first cut. A plan reads sp and mp as the
  last record left them.
* **L0**, the stream's length before the record that is planned, its
  position; **tl**, the time of the stream's last record, the state at L0;
  **tt**, the record's own time.
* **a**, the position of the application's last record (031-04, R3;
  031-03's witness made a position): of the last record that is not
  reclaim's own, -1 if none. A record is reclaim's own if it holds a value
  or delete node at one of reclaim's keys (under `/#i/dreclaim/`, but the
  settings) without the copy mark (`Reclaim.isOwnRecord`; 031-06, rule
  6): since 031-06 only a part's record that stores the row or the table.
  After every record but a part's, a is that record's position.
* **The table**: one row an iteration, in `/#i/dreclaim/-table.txt`; the
  row of the iteration in progress also in `/#i/dreclaim/-current.txt`,
  as its last step left it. A row: pStart, tStart, pCut, E (the end key),
  lastKey, kvCount, rewritten, done, tEnd, pEnd, pSafe, cut; the table's
  last row and the current row also hold a, as it is after the record
  that stores them, and a table without rows holds a alone (031-04, R2).
  rewritten is written at a fixed width of 19 digits (027-03, section
  15). The current iteration is the table's last row if it is not done.
* **The actions that carry maintenance**: a commit, a user transaction
  that is not a setter's (`Db.execute`; the Pub layer's index jobs commit
  so too), and a part of `maintain(budget)`, an empty internal
  transaction with its own time from the clock (`Trans.part`). The
  setters' records (`Trans.noMaintenance` for `setStartupDistance`;
  reclaim's settings, an internal transaction) and the creation's carry
  none. User transactions and parts are refused in the last 1,024 times
  and top node ordinals (015-55, 005-02), which reclaim's own transactions
  used until 031-06 (031-06, rule 9 and Q4).
* **Constants**: MIN_STEP 10,000 bytes; MAX_STEP 16,000 (a part's step,
  and the least cap of a commit's); MAX_COMMIT_STEP 131,072 (128 KiB, half
  of `StoredTrans.STEP_FIXED_ROOM`); GROWTH 2 (`STEP_GROWTH_FACTOR`); VN
  32 (a value node's bytes besides its key and value); META 200,000 (the
  meta block distance); TAKE_MORE 262,144; RESERVE 4 MiB
  (`DEFAULT_STEP_RESERVE`, a constant for every database since 028-68,
  2026-11-27; a smaller one by a hook for tests only, not in the stream);
  NB = 80 + 48 N, N the largest node size; `maintain()`'s budget from 100
  to 100,000 units of UNIT 1,000 bytes.

### 1.2. The maintenance of a commit's record

Under the write lock, before the go point and after the commit's last
check that may refuse it (its value transformations), `Reclaim.planCommit`
plans on copies of the rows, from the state before the record, in this
order (031-06, section 2, rule 3):

    it := the current iteration
    B: if it is none and R is finite and L0 > lastPStart + 2 sd
            and tl - lastTStart >= R div 4:
        it := begin(pStart = L0, tStart = tl)                     (1.3)
    S: else if it is not none:
        allowed := floor((L0 - it.pStart) * f / 2^16) - it.rewritten
        if allowed > MIN_STEP: step(it, min(allowed, cap))        (1.4)
    P: markSafe()                                                 (1.5)
    C: decideCut(now = tt)                                        (1.6)

    cap := max(MAX_STEP, min(MAX_COMMIT_STEP,
                             GROWTH * floor((L0 - a) * f / 2^16)))

with L0 - a taken as 0 while a is -1. lastPStart and lastTStart are those
of the table's last row: 0 and minus infinity if it has none. B and S
exclude each other, and no decision depends on another in the same
record: a row that S ends has pEnd = L0, after sp, so P cannot mark it; a
row that P marks has pSafe = L0, so C cannot cut it (031-06's study,
section 1). A decision that needs the record's own length or take is made
in the next record. The cap lets a commit's step spend twice the
allowance that the application's last record and the records after it
added, so that reclaim keeps up with large commits; after records under
32 kB it is MAX_STEP at f = 1/4 (031-06's landing, step 3, 2026-11-27;
028-71; until then MAX_STEP for every commit).

**The record's room** (031-06's landing, step 2): `Reclaim.plan` gives
the plan to `Db.recordDirtyFits`, which counts the index nodes that the
record's KVs, the action's and the plan's together, can make dirty or
create, as a transaction's are counted (027-08, section 4.2), within
`StoredTrans.dirtyLimit()`, 15/16 of the record limit. If they do not
fit, the plan is made again with a step of one copy at most (015-50's
rule: the next old KV); if that does not fit either, the commit's record
carries no step, and a later record whose action leaves more room carries
it. An action alone is admitted within 7/8 (`actionDirtyLimit()`), so
every action leaves a step a sixteenth.

If nothing is due, as for most commits, the record is the action's
alone. Otherwise Db merges the plan's KVs with the action's (1.4, step 4).
After the record, `Maintenance.apply` sets a to the record's position,
takes the plan's rows as the table and, for C, moves fa and fp and makes
the cut pending (1.6); then makeCutIfDurable() (1.7). A stop during the
plan, or before it returns, refuses the commit with nothing written, its
keys, values and time given back (`Db.giveBack`); any other exception
from the plan on fails the database (010-01, P7); after the go point a
stop does not refuse, and the close waits for the record (031-06, rule
8; 027-15).

Until 031-06 reclaim's listener ran after the commit's record, within its
go point, from the stream's length after that record and the commit's
time, and wrote its work in internal transactions of its own, at most six
(a begin, a step, the row again, the end, the safe positions, the cut); a
stop that came meanwhile left the rest to later commits, which changed
the stream's bytes (RB-013, 033).

### 1.3. The start of an iteration

begin(pStart, tStart) appends a row to the plan's table, which the
record stores:

* pCut := pStart for the first iteration (an empty table), else
  lastPStart, the pStart of the iteration before (a pass of `maintain()`
  has pCut := pStart, 1.10);
* E := the greatest key live at tStart, of every key, BergDB's own too
  (any live value may need a rewrite); "none" if no key was live;
* lastKey none; kvCount, rewritten and tEnd 0; pEnd and pSafe unknown;
  done and cut false.

pStart is the record's own position, L0, and tStart the time of the
state before it, tl (031-06; until then the stream's length after the
commit's record, and the commit's time).

### 1.4. A step

step(it, W) is planned for a record (`Reclaim.planStep`), at the state
before it:

1. **The scan** (since 026-05): the live KVs at the latest state, the
   state before the record, read under the write lock, forward from the
   first key after lastKey (from the first key if none), up to E
   inclusive. Every row has E: a row without it is refused as damaged
   (`IterationInfo.deserialize`, since 028-15). Such a row, stored before
   026-05 by 2026.5 or earlier, was scanned to the last key until 028-15,
   and is in a stream of meta version 154, which a start refuses first
   (027-03, section 6). If E is none, or lastKey is at or after E, there
   is no scan, and this step is the last.
2. **Each KV met**, in key order, with p its value node's position (none
   if not yet written), s its key's segments and v its value's bytes:
   * rewrite := p < pCut; the scan loads the value only then
     (`GetMany.valuesBefore`; 026-09);
   * if rewrite, and the step holds a KV to rewrite already, and their
     value nodes with this one's would pass the value limit (7/8 of the
     record limit, 027-03, section 8.3; a value node is 32 + 8 s + v
     bytes, rounded up to a multiple of 4): stop before this KV, which is
     the next step's first;
   * lastKey := its key; kvCount += 1;
   * if p < pStart: size += 8 s + 100, and v if rewrite; only these KVs
     count (023-08, fault 13);
   * stop after this KV if the scan has followed more than max(1,
     RESERVE div NB) distinct index nodes (the step is split), or else if
     size > W, or if it is a KV to rewrite and the step holds as many as
     the record's room allows (1.2: one, or no limit);
   * keep it if rewrite; walk past it otherwise.

   If the scan passes E or the last key without a stop, this step is the
   last.
3. **The copies and the row.** A copy of each KV kept, at its key with
   the value the scan read, but at a key that the record's action writes,
   by its key as transformed: that copy is dropped, as the action's put
   makes a value node of its own at the record, after pStart, and its
   delete leaves no value (031-06, rule 7; Codex's E4); lastKey and
   kvCount stay as the scan left them. The copies are no reads or writes
   of the STM: the scan reads the state before the record, under the
   write lock, after the action's conflict check, and no copy enters the
   record's write set (031-06, rule 4). The row after the step holds the
   new lastKey, kvCount and rewritten (step 4); if this step is the last,
   done := true, tEnd := tt and pEnd := L0, in the step's own record
   (031-05). The record stores the row; it stores the table only if B, P
   or C changes it (1.2) or a part stores it (1.10), so a start takes a
   done current row over the table's row (1.9).
4. **The record** (`Db.putKvs`, after the go point):
   * **The touch** (024-07), first: every index node on the path, at the
     state before the record, of each copy's key and the row's
     (`Plan.touchKeys`) that is not dirty becomes dirty. A path is the
     super root, the space root and, in each segment's tree, the nodes
     down to the segment leaf of the key's segment, or to where no key
     has the segment. These marks stay even when a put then replaces the
     node. The action's keys are not touched; no other node is.
   * **The row and the table**, by value transformations after the touch
     (`Kv.planned`), which read no previous value; the step's row has
     nineteen nines for rewritten (`REWRITTEN_DUE`), its charge due.
   * **The batch**: the action's KVs and the plan's, merged in key order,
     one KV a key (`Db.merge`; a key in both would be a `Bug`, which
     fails the database), given to the writer as one batch (record format
     8, 026-25; 027-08). A copy at the row's or the table's key is
     replaced by it.
   * **The charge** (031-06's landing, step 3, 2026-11-27;
     `Db.chargeStep`, `RecordPlan.charge`), after the batch and before
     the append: rewritten += 8 s + v + VN for each copy, and the bytes of
     the index nodes that the record made dirty on the step's paths, the
     copies' keys and the row's: the touch's, each at its size then, also
     if the batch replaced it, and the key nodes that the batch made
     dirty that are on those paths after it (PE's replacements, cuts and
     joins), found by walking the paths again in key order. The number is
     written over `REWRITTEN_DUE` in the row's bytes and the table's, at
     the same width, so no node of the record changes its size. Not
     charged: the record's top node, which every record makes, and the
     nodes off the step's paths: a commit's action's, and the table's
     path. A row whose rewritten is not a long is refused at a start
     (`IterationInfo.deserialize`), so a charge never made is not read as
     0.
   * **The copy mark**: each copy's value node has its byte 6 set (027-03,
     section 12; `TransNodes.copyKeys`, from the plan), by which
     `transactionInfo()` follows a copy back to the transaction that
     wrote its value and leaves the copies out of the record's KVs
     (021-17; 031-06, rule 7).

   Until 031-06's landing, step 3, the row counted the touch's bytes
   before the batch; the nodes that the batch made after the row were
   charged by a second internal transaction that stored the row again
   (028-26, from 2026-11-19), lost at a crash between the two, and in
   031-06's prototype by none, 25.7 % and 39.5 % of the charge at node
   sizes 30 and 8 in a pass of parts (031-06, section 4.6). Until record
   format 8 the operations were applied one by one in key order, and the
   row counted the nodes that the rewrites of keys before the row's key
   made dirty.
5. **The end.** The last step's record holds the done row (step 3); no
   record of its own ends an iteration (031-05; until then the table was
   stored after the last step, in an internal transaction).

### 1.5. The safe positions

markSafe(), in the plan (`Reclaim.planSafe`): for every done row with
pSafe unknown and sp >= pEnd, pSafe := L0, the marking record's own
position; if a row changed, the record stores the table. sp >= pEnd
means every node the steps made dirty is written; the wait for sp >=
pSafe then writes once more the nodes written before their children and
kept in D by Rule A, so that they name the children's new positions.
015-54's reason for a pSafe after the records whose takes moved sp past
pEnd holds: those records are before L0, and a node that the marking
record's own take keeps dirty has its record at L0 or later. Until 031-06
pSafe was the stream's length after the records of the call that marked
it (015-54).

### 1.6. The cut's decision

decideCut(now), in the plan (`Reclaim.planCut`), with now the record's
time, a commit's or a part's (1.10), and sp, mp and fp as the stream
before the record has them: a meta block that the record itself makes
counts from the next record on. A row is a candidate if it is done, now -
R > tEnd, pSafe is known and sp >= pSafe, mp >= pCut, and pCut > fp. Of
the candidates, C is the one with the largest pStart. If there is none,
or C is cut already, nothing happens. Otherwise, in this order:

1. in the plan's table, the rows with pStart below C's are removed and C
   is marked cut; the record stores the table;
2. after the record (`Reclaim.applyCut`): fa := C.tEnd and fp := C.pCut:
   from here, lookups before fa are refused (1.8);
3. caches of what the cut makes unreadable may be dropped (Java: the
   node ids read below pCut, the key hashes of writes at or before tEnd;
   026-10), so a transaction that read before fa may be rerun;
4. a cut still pending whose table is durable is made first (1.7;
   026-05, section 2.5);
5. C.pCut becomes the pending cut, to be made when the stream is durable
   up to its length after the record that stores the table.

### 1.7. The physical cut

makeCutIfDurable(), after every record (`Reclaim.apply`) and in
`maintain()` after its sync (1.10): if a cut is pending and the stream is
durable up to its mark, the storage drops the stream before pCut, and
nothing is pending. The storage may keep more: a file storage drops whole
files (027-03, section 4). Durable first, so that a crash cannot lose the
table that marks the cut once the front is gone. A file storage deletes
the files of its cuts a batch at a time, with one force of the directory
after each batch (028-66, 2026-11-27; until then after each file): a
power loss can keep the delete of a newer file and lose that of an older
one, a gap, and the stream after the crash begins at the first file
after it, at or before the cut whose table is durable (027-14).

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

A start (`Reclaim.initFromDb`, its last step before any transaction)
reads the settings, the table, and the current row, which replaces the
table's row with the same pStart if that row is not done (the current
row may be done: the last step's record holds it, 1.4). The newest row
marked cut gives fa := its tEnd and fp := its pCut (0 and 0 without
one). If the storage's first position is below fp, the cut is made now:
a crash came between the table and the cut, or a power loss left a gap
in a file storage's files, and the cut deletes the files before it
(028-66), which the start's recovery has checked to be the database's
before anything was written: a file whose first meta block is not this
database's is refused (Frans, 2026-11-27; 027-14). If it is above fp,
the stream lacks the database's bytes from fp to it, and the start
refuses (a `StreamIoException`, the cause a `ReadBelowFirstPosException`,
with what the storage says; 028-66, 2026-11-27; before, the start went
on, and reads of those bytes failed the database); so does a start that
reads below the first position, which it does only then (027-11, section
1.10). Nothing is deleted before the refusal.

a: if the stream's last record is reclaim's own (1.1: a key of reclaim's
that is not a copy, the witness; 031-06, rule 6), the larger a of the
table's last row and the current row; else, or if they hold none, or
there is no table, the last record's position. So an empty commit, which
holds no key of reclaim's, gives its own position, as the running
database set it. A start appends no record of reclaim's: nothing of
reclaim's is due between two records (031-06; until then a stop between
a commit's record and reclaim's records after it left their work to the
next commits, RB-013). Nothing else is kept, so a restart or a stop does
not change what reclaim writes (INV-RESTART). Startup on a cut stream is
part 7's.

### 1.10. maintain(budget)

An optional call (024-32; Frans, 023-04, Y10): `maintain(int budget)`,
031-04's design, since 031-06's merge (2026-11-27), in place of
`maintain()` in the Core and the Pub API for 2026.7 (031-06, section 8,
A2). It works in parts, each an action of its
own (031-06, rule 10): an empty internal transaction (`Trans.part`) with
its own time from the clock, through a commit's path (`Db.maintainPart`,
`Db.executeLocked`), refused as a user transaction is (an inactive
database, the top node ordinals used, no user time left), and one record,
which carries the first of these that is due, planned from the state
before it (`Reclaim.planPart`):

* **M1**, a pass (031-04): if R is finite, no iteration runs, no done row
  waits for its cut (not cut, pCut > fp), the stream kept holds a record
  of the application's (a >= fp), and sp >= a: begin(pStart = L0, tStart
  = tl) with pCut := pStart, so that the pass rewrites every live value
  stored before it and its cut drops the stream before it. No condition
  on the stream's growth or on R div 4. A pass that a call begins ends by
  its own construction: once it is cut, a is before fp unless the
  application has written since its pStart, and no call begins another.
  Until 031-06's merge (2026-11-27) M1 began an iteration of 1.3 when R
  div 4 had passed and its cut would release 400 kB (028-51), which
  rewrote the live values of a database not written to in two sets in
  turn and missed the writes between lastPStart and the table's last
  store (028-53, RB-007).
* **M2**: step(it, MAX_STEP) if an iteration runs, a commit's or a pass,
  without the allowance; the record's room (1.2) may cut it to one copy,
  never to none, so that every part moves the iteration.
* **M3**: markSafe(), if it marks a row.
* **M4**: of the rows waiting for their cut, the least wait position
  (pEnd while pSafe is unknown, then pSafe) after sp, or else a if M1
  waits for sp to reach it: a record that stores the table and whose
  take, after its share, goes on with whole transactions of the startup
  section, oldest first, while sp is below that position: the first
  whatever its size, then each while the bytes taken (counted as the take
  counts them, part 6) stay within TAKE_MORE and the record
  (`Trans.maintainTakeTo`, `TransSeq.takeTo`).
* **M5**: if a row, not cut, meets every condition of 1.6 but has mp <
  pCut: the table, with max(1, META - L0 mod META) spaces after its text
  (031-03, R2), so that its record passes the next meta block's position
  and that meta block names a transaction at or after pCut. Until 031-06's
  merge a filler: a put of `/#i/dreclaim/-fill.txt` with that many zero
  bytes and its delete, two transactions, whose put a stop or a crash
  between them left live (028-59).
* **M6**: decideCut(now = the part's time).

A part with nothing due writes nothing and gives its time back.

**The call** (`Db.maintain(int)`): its budget, clamped to 100 to 100,000
units, times UNIT bytes, is spent by the parts' costs: the bytes of the
part's record and a quarter of the bytes that its step read, by
deterministic counts (each KV met 8 s + VN, and v if loaded to be
rewritten; each index node followed NB), whether resident or not, so that
the same calls write the same stream (010-01, P2). Before each part, and
again under the lock, the call gives way while a commit waits for the
write lock (031-04, Q9), and before each part's lock it warms the part's
scan (1.11). After a part, a pending cut whose table is durable is made
and one batch of eviction's dead hand runs (part 8); if the table is not
yet durable, the call syncs outside the lock, then makes the cut. Once a
part has nothing due, the dead hand alone runs, charged by its time (5 us
a unit), until it has nothing more or the budget is spent. The call
returns nothing (until 031-06's merge `maintain()` returned whether more
was due).

### 1.11. The warm-up before the lock

Since 031-06's landing, step 3 (2026-11-27): before the write lock, a
commit (beside its transaction's own warm-up; not a setter's) and each
part of `maintain()` read, as a reader reads, the KVs that the next
step's scan would meet (`Reclaim.warmup`, `Db.warmupStep`): if an
iteration runs and, for a commit, its allowance as the last record left
it is above MIN_STEP, a scan from the row's lastKey to E at the latest
time, through the node table's follower, with the values stored before
pCut, ending as the step's scan ends (its cap for a commit, MAX_STEP for a
part; the reserve). A commit counts the commits ahead of it at the lock,
at most 4 (`Db.commitsAhead`), and reads the steps that the records from
the next one to its own may take, each record adding the allowance of the
application's last record; a part reads nothing while the published row
is the one it read last (031-06, review 3, W1 and W2). Reclaim publishes
what the warm-up reads (the running row, the stream's length and a after
the last record) in `apply()` and `initFromDb()`; the warm-up reads it
without the lock. It decides nothing: the plan's scan, copies and charge
are counts of the KVs and index nodes met, resident or not; it changes
only what is in memory, so that the plan's scan under the lock meets its
nodes there. A read that a cut overtakes ends it; on a database that is
not active it reads nothing.


## 2. State

* **In memory**: R and f; the table's rows; a; fa and fp, which readers
  read without the write lock; the pending cut and its mark; the state
  published for the warm-up (1.11); RESERVE. A plan (`RecordPlan`) lives
  for one record.
* **In the stream**: the three KVs of 1.1 (027-03, section 15: the texts;
  the row is read leniently, but a rewritten that is there must be a
  long; the settings strictly). They ride in the actions' records (027-03,
  section 8.5): a commit's record holds its action's KVs and the plan's,
  the copies (each with the copy mark), the row and the table, one KV a
  key; a part's record holds the plan's alone; a record that carries a
  step holds the got-dirty ids of its touch and its batch. Records of
  reclaim's own (1.1) are parts' records only. Nothing of a scan is
  stored. 2026.6's filler key, `/#i/dreclaim/-fill.txt`, is among
  reclaim's keys of the witness (`isOwnKey`); nothing writes it since
  031-06's merge (2026-11-27).


## 3. Invariants

* **ONE RECORD AN ACTION** (031-06, rule 1): every accepted action
  appends exactly one record, and nothing is appended between two records
  but recovery's completion of a cut record; so a crash, a stop or a
  restart at a record boundary comes between two actions. By construction
  (`Db.executeLocked`); checked by 031-06's probes (as many records as
  accepted actions in every reference run, 16,661 records in 23 runs;
  031-06's landing, step 3); gated (`testUserTransactionLeavesTimesForReclaim`,
  `testMaintenanceNone`).
* **THE PLAN FROM THE STREAM** (010-01, P2): what a record carries is a
  function of the stream before it, the record's time and the action's
  KVs, and reclaim's memory after a record is what a start reads off the
  stream there. Argued (`Maintenance`'s contract: the plan reads copies of
  the rows, the stream's positions, sp and mp as the last record left
  them; the warm-up decides nothing). Checked by 031-06's probes: a crash,
  a failure before `apply()` and a stop after each record of 23
  configurations, each continued to the uninterrupted stream, with the
  start's memory (a, fa and fp, the settings, every row) the running
  database's: 27,741 interruptions and 570 torn records, 0 different
  (2026-11-28, 031-06's landing, step 3); threads replayed by one thread
  to the same stream; faults at four points (031-06, section 4.2).
  Gated: RestartInvariance (level3),
  `ReclaimMaintainTester.testSameStreamOverARestart`.
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
  rewrote it. A copy dropped at a key that the action writes leaves the
  key the action's value node, after pStart, or no value (1.4, step 3):
  the contract's `StepTx` asks of every old KV met only that the record
  writes its key, by a copy or by the action (031-06's landing, step 1).
  That Java's steps are the model's: checked step by step on the reclaim
  traces since 030-27 (C-STEP, on 027-02's STEP lines: each step against
  the model's step at its state, each cut against its iteration's last
  step; since 030-34 also that each copy writes the value the scan read;
  since 031-06 that the record's operations that are not copies are its
  action's as submitted or puts at reclaim's keys, STEP-action), and
  through RC2 (C-CUT's part 2); gated (`testIterationRewritesAllOldValues`,
  `testStepScansAtItsOwnTime`, `testEndKeyBoundsTheScan`).
* **COPIES CHANGE NO USER READ**: proved in the contract since 031-06's
  landing, step 1 (`record_preserves_users`, `applyOps_drop_copies`): the
  marked operations that put back the values before the record, at keys
  of no other operation, leave every user read as the reference of the
  unmarked operations. That Java's marks are the plan's copies, and the
  unmarked operations the action as submitted: checked (the trace
  exporter's check against the plan; C-STEP's STEP-values, STEP-ops and
  STEP-action), not proved.
* **LIVEBELOW** (part 4): each index node a lookup reaches, but an empty
  space root, has a live key below it, and that key's last put (the
  user's at pCut or later, or a step's copy) made the node dirty; so no
  key range needs a touch, and the space root is on every step's row's
  path (024-07, section 4). It rests on the writer: since record format 8
  PE drops every child left empty and every empty segment tree, and
  collapses a root of one entry (`PeWriter.rebalance`, `settleRoot`;
  026-25), as the upward unlink and root collapse did in formats 6 and 7.
  Checked at every cut (C-CUT, `CUT-live`); gated (UnlinkFuzz,
  `testEmptiedSubtreesAfterCut`, `testDeletedKeysAfterCut`). Proved from
  the writer's contract, given a live key at tEnd (`rc3_tree`, 030-24).
* **COVER**, **LATEST**: with REWRITES and LIVEBELOW, every node
  reachable from tEnd on has its latest version at pCut or later once sp
  >= pEnd. Proved in the model (`T_cover`, `T_latest`).
* **T-SCHEME**: Java's waits (1.5, 1.6) give `CutOK`. Checked: C-CUT at
  every cut of every reclaim trace (026-05: 0 of 794 failing in level3's
  set, 0 of 479 in its own; 031-06's landing, step 3: 0 of 857), and
  `checkSchemeC`; C-CUT checks reclaim's contract RC (030-22) at every cut
  too (`RC1-order`, `RC2-rewrites`, `RC4-waits`; RC3 is `CUT-live`;
  030-23). Proved since 030-24 for runs with A6' (BergDB's tree): RC gives
  `CutOK` (`cutOK_of_rc`; part 2 needs only the first wait, part 3 the
  second). `TScheme` as 030-23 stated it, for every run with RunOK, is
  false (`AdoptionExample.tscheme_false`). RC3 for the key tree from the
  writer's contract (`rc3_tree`); RC2 from the iteration (`IterationOK`:
  every key whose value node predates pCut is written again from the
  iteration's first step to tEnd) and VAL-NEW, which PE meets
  (`rc2_of_iteration`, `PE.pe_valNew`). So for every history PE writes,
  Java's reads after cuts are right given `IterationOK` and RC1 and RC4 at
  each cut (`PE.pe_reclaim_reads`), and given steps that follow the model
  of 1.4 in place of `IterationOK` (`PE.pe_reclaim_reads_steps`, 030-25).
* **The touch on the paths** (`TouchOnPaths`): checked (C-A,
  `touchPath`); gated (`testStepDirtiesItsPathsOnly`). **No conflict from
  a step**: the copies are no STM reads or writes, and the scan runs under
  the write lock after the action's conflict check (1.4): by
  construction; measured, no read-modify-write refused for them (031-06,
  section 4.5a).
* **INV-RESTART**: a run with restarts writes the stream and the cuts of
  the run without them; since 031-06 a run with stops too (THE PLAN FROM
  THE STREAM). Proved in the model for safe cuts (`T12_restartCut`,
  `T12_handles`); gated (RestartInvariance, level3).
* **Retention** (1.8): argued; gated (ReclaimRetentionTester,
  ReclaimStress). **Crash**, the table durable before the cut: gated
  (`testCutIsMadeAfterDecisionIsDurable`, CrashTest, PowerLossTest).
  **Readers**, a read that a cut overtakes expires: gated
  (ReclaimReaderTester, ReclaimReaders).


## 4. Costs and bounds

* **A step** (a commit's, or a part's) counts at most W bytes of KVs
  stored before pStart and one KV more, and walks those put since up to
  the reserve (about 2,759 index nodes at the default node size, 026-05):
  argued. W is at most the cap, 16 kB to 128 KiB, for a commit, and
  MAX_STEP for a part. Its values: within the value limit unless it is
  one KV; argued; gated (`testStepWithinValueLimit`,
  `testLastStepWithinRecordLimit`). Its dirty nodes: at most 3 h s + 3 a
  copy, h a segment tree's height (024-07, B1; 024-05, BD7); argued;
  gated (`testStepDirtiesItsPathsOnly`). With the action's, within
  `dirtyLimit()` by `Db.recordDirtyFits` before the go point, and the
  record's got-dirty set within `StoredTrans.takeRoom()` by
  `Db.checkTakeable` before the append, a `Bug` that fails the database
  with nothing of the record written if not (031-06's landing, step 2):
  gated (ReclaimRoomTester, among it `testUntakeableRecordFails` and
  `testLongKeyCopiedByAStep`). For a commit's step of up to 128 KiB these
  checks are the bound; 031-06's arithmetic of a record that carries a
  step holds for a step of 16 kB (031-06, section 3; review 3, D1).
* **A record**: one an action, and nothing else (ONE RECORD AN ACTION).
  A commit's record carries at most B or S, then P and C; a part's one of
  M1 to M6. A record that carries maintenance may take up to
  `StoredTrans.recordCap()`, the record limit and the step's room, at most
  `MAX_RECORD_SIZE` (027-03, section 8.3). Until 031-06 a commit was
  followed by up to six internal transactions of reclaim's (1.2).
* **An iteration's rewrites**: about f of the stream's growth since
  pStart, by the allowance at commits (a step may pass it by one KV and
  its charge's index bytes; `maintain()`'s steps have no allowance),
  unless paced by the cap, R div 4 or 2 sd (024-29, section 4.2): argued.
  Since 031-06's landing, step 3, the charge of a step's index nodes on
  its paths is exact in its record: a pass of parts over 30,000 values of
  10 bytes left 208 and 192 bytes uncharged at node sizes 8 and 30, 0.0 %
  (25.7 % and 39.5 % before); reclaim's share of the growth under
  commits of one small put 0.264 to 0.283 at f = 1/4 (0.291 to 0.397
  before), the rest above 0.25 the rows' and the tables' own bytes and the
  table's path, which no charge counts; under commits of 20, 100 and 300
  kB the stream kept 8.1, 7.2 and 7.8 times the live data (7.7, 13.8 and
  36.4 with MAX_STEP a commit), at 1 MB 18.2 times, steady (115.7 and
  growing): measured (031-06's landing, step 3; 028-71). Earlier: 26 to
  38 percent of all stream bytes at f = 1/4 (011-04, W4); the charge 0.250
  of an iteration's stream with PE and 028-26's second row, at 10M keys
  (028-19).
* **An iteration's length**: at most about (the counted bytes of the KVs
  live at tStart) / W steps, W from MIN_STEP to the step's cap, whatever
  the user puts ahead of the scan, plus steps that the value limit, the
  reserve or the record's room ends early: argued (026-05, section 2.3,
  says / MAX_STEP).
* **The stream kept** (BD10, G3), less the user's records within R: at
  most 6 times a fresh twin's; gated (`count-gates.sh`); 4.401 measured
  (026-05), 4.303 on 031-06's prototype (031-06, section 4.5). Its form,
  G(R) + j W: argued (024-29), not derived (017-04).
* **Back to empty** (G4): kept, key nodes, heap and the rest at most 2
  times the twin's, the lag at most 2 R (2,000 transactions in G4's
  workload, 026-11): gated; the lag 1,265 to 1,286 transactions at 1M to
  10M keys and every f: measured (026-05). G5, by `maintain()`: gated.
* **The largest record** with reclaim on (G1, BD1): at most the larger
  of 1 MB and 5 times the mean; gated. **A part of `maintain()`**: one
  record, with one of: a begin, a step of MAX_STEP, the table, the table
  and a take of TAKE_MORE beyond its first taken transaction, the table
  padded by at most META bytes, the cut; a call goes past its budget by at
  most one part's cost: argued; gated (ReclaimMaintainTester).
* **Pauses** (P1): the physical cut waits for the storage's append in
  progress, 19.85 ms at the longest on s1 (015-80, 019-36); 1.6's forget
  0.3 to 6 ms (026-10): measured. With the step in the commit's record
  and the warm-up (031-06's landing, step 3's timing run, F53,
  2026-11-28): at 20M keys and a cache budget of 200 MB, a commit with a
  step held the write lock for a median of 0.192 ms, p99 0.840 ms, at
  most 3.146 ms, and the longest commit took 11.58 ms (20.89 ms on `main`
  before step 3); a commit that carries a step of 128 KiB of small values,
  about 930 copies, held the lock for up to 12.5 ms: measured. Readers
  see a commit that carries a step after its scan (031-06, section 4.7).
* **The disk** (028-62): a file storage deletes whole files and keeps
  the part before fp of the file that fp lies in, up to about a tenth of
  the stream when that file was made (a quarter until 2026-11-26), also
  after the stream has shrunk (RB-011): argued (`FileStream`'s Javadoc).
  With `ReclaimCost` on disk (K = 1, uniform, 20 MB live, no cache
  budget; stream kept 99.6 MB on average) that part is 2.1 percent of
  the stream kept on average, 5.5 at most (6.3 and 23.5 with the
  quarter): measured. 011-04, W5d, measured 6 to 9 percent of the whole
  disk on 2026-10-13, when a cut deleted its files on the committing
  thread; since 005-46 a thread of the storage's own deletes them, from
  005-46 to 028-66 one at a time with the directory forced after each,
  since 028-66 (2026-11-27) a batch at a time with one force. With one
  force a file, a fast writer was ahead of the deletes: in `ReclaimCost`
  (about 120 MB of stream a second, F53 loaded) the files that end
  before fp and are not yet deleted, most of them taken off by the
  storage's cut and waiting for its thread, the rest for the cut, which
  waits for durability, are 24 to 44 percent of the stream kept with the
  quarter, 50 to 55 with the tenth, which makes about three times as
  many files (16 to 23 against 56 to 60 on average); the disk 1.28 to
  1.48 times the stream kept with the quarter, 1.49 to 1.56 with the
  tenth: measured. With a batch and one force (028-66, section 6.8: an
  A/B against `main` on a quiet F53, 2026-11-28, medians of 4 runs
  each): 113,580 transactions a second against 67,052, the disk 1.10
  times the stream kept against 1.62, the files not yet deleted 0.12 of
  it against 0.65, those that wait for the storage's thread 0.011
  against 0.549, 27 files against 63: measured. An emptied database (031-02's
  RetainChurn): 400 kB on disk for 61 kB of stream in seed 5 (10,400 kB
  with the quarter); 200, 600 and 800 kB in seed 1's rounds 1 to 3 (200,
  2,600 and 3,800): measured.


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
  with the scan and E (ReclaimSteps.lean), since 031-06's landing, step 1
  (2026-11-27), for a step in a record that also holds its action's
  operations, with the maintenance marked per operation, the copy mark
  (ReclaimValues.lean: `MaintenanceOK`, `record_preserves_users`). Also
  checked by running (`checkSchemeC` in SIS/ReclaimExample.lean, `lake
  exe reclaimtest`; 024-07, section 4.3).
* **Left out**: keys, the scan and E, R and the times, the table, the
  allowance and the step sizes, the plan's place in the record and its
  room, the durable wait, the storage's files, reads in flight,
  `maintain()` (its records are like any), the settings, the warm-up.
* **Conformance** (027-02's `TOUCH`, `FA`, `CUT`, `PHYSCUT`, `STEP`, the
  copies' `OP C` and the action's `ACT` lines; Check/Steps and
  TraceCheck.lean): C-A (TouchOK, `touchPath`), C-S (the model's step
  against Java's records, D on the cut stream), C-CUT (`CutOK` at every
  cut Java decides; `CUT-live`; RC, 030-23), C-STEP (each step of reclaim
  against the model of the steps, `StepsOK`, and each cut against its
  iteration's last step; 030-27; the values written back and the step's
  other operations, 030-34; every record against its action as
  submitted, STEP-action, and the copy mark, 031-06's landing, step 1),
  C-L (the first touches after restarts); C-P and C-H with eviction. The
  tree checker's C-T5 and C-T9 take a step's touch keys as the copies'
  and the row's (027-02).


## 6. In Java

* `core/Maintenance` (031-06): the boundary between Db and reclaim,
  `plan`, `apply`, `warmup`, `Plan` (the KVs, `copyKeys`, `touchKeys`,
  `takeTo`, `readBytes`, `charge`), and `NONE`, the empty implementation
  (`DbBuilder.maintenanceNone()`, for tests).
* `core/Reclaim`: `plan` (1.2, the room), `planCommit` (1.2),
  `commitStepSize` (the cap), `planStep` (1.4), `finishPlan` (the KVs, the
  touch), `RecordPlan` (`charge`), `planSafe` (1.5), `planCut`, `cutRow`,
  `applyCut` (1.6), `cutIfDurable` (1.7), `initFromDb` (1.9), `planPart`
  and its conditions (1.10; `passDue`, `maintainTakeTarget`,
  `cutWaitsForMetaBlock`), `warmup` and `publishWarm` (1.11), `apply`,
  `appA` and `isOwnRecord` (a), `lastKeyAt` (E), `setSettings`,
  `fractionOf`, `IterationInfo`, `IterationTable`, `serializeTable`; the
  class comment.
* `core/Db`: `executeInner`, `executeLocked` (one record an action),
  `planMaintenance` (the plan and its refusal), `merge`, `recordDirtyFits`,
  `checkTakeable`, `putKvs`, `touchPaths`, `chargeStep`,
  `makeDirtyIfNeeded` (`Trans.dirtiedBytes`), `cutDecided`, `maintain`,
  `maintainPart`, `giveWayToWriters`, `warmupStep`, `commitsAhead`,
  `store` (M4, `TransSeq.takeTo`), `giveBack`, `expiredIfReadBelowCut`,
  the setters; `StoredTrans` (`recordCap`, `stepRoom`, `dirtyLimit`,
  `actionDirtyLimit`, `takeRoom`); `StoredValueNode` (the copy mark) and
  `TransNodes.copyKeys`; `Kv.planned`; `Trans.part`, `Trans.noMaintenance`;
  `DbClock` (the 1,024 times kept); `dag/GetMany` (`endKey`,
  `valuesBefore`); `NodeCollection.MaintenanceFollower` (a step's reads,
  kept nowhere); `stream`: `AppendOnlyStream.pretruncate`, `FileStream`,
  `CutStream`, `ReadBelowFirstPosException`.
* The Pub API: `Database.setRetainDuration`, `Database.maintain(int)`,
  `Database.getStreamSize()`; no setter of f (024-29);
  `ConnectionImp.transactionInfo()` through the copies (021-17, 028-34).
  The C clone (012) has release 2026.2's reclaim (`reclaim.c`), before
  024-07, 024-32, 024-34, 026-05 and 031-06.


## 7. Tests

* **Gated by `before-commit.sh`**: `Reclaim`'s 40 tests, among them
  section 3's, `testMaintenanceNone` (a database with no maintenance:
  no copy and no key of reclaim's in any record),
  `testCopyAtAKeyTheActionWrites`,
  `testUserTransactionLeavesTimesForReclaim` (the step in the commit's
  own record), `testAllowanceCountsIndexNodes` and
  `testAllowanceCountsNodesMadeAfterTheRow` (the row against the charge,
  the nodes that the batch made charged, at node sizes 8 and 30),
  `testSafePosAfterTheCallsRecords` (pSafe = L0), `testWarmupBeforeTheLock`
  (the same stream with and without the warm-up),
  `testStepReserveSplitsSteps`, `testStepReserveIsAConstant`,
  `testQueueBeforeAKeyEnds`, `testCutKeepsMetaBlockTransaction`,
  `testRestartResumesIteration`; ReclaimRetentionTester (7),
  ReclaimReaderTester (8), ReclaimMaintainTester (8; among them
  `testCommitGoesBeforeTheNextPart`, the handover, and
  `testSameStreamOverARestart`), ReclaimRoomTester (6: the record's room
  at lowered limits, the long key copied by a step, the largest action
  beside the largest old value); `StoredValueNode.testCopyMark`; two of
  DbTesterRestart's (`testReclaimSettingsKeptOverRestarts`,
  `testMalformedSettingsRefusedAtStart`).
* **In the night**: `level3.sh` (ReclaimStress, RestartInvariance,
  CrashTest, ReclaimReaders, LoadTest with a restart and a check after
  every cut, PowerLossTest, the conformance's reclaim set with C-STEP's
  fault test, InterruptStress); `count-gates.sh` (G1, G3, G4 with its
  lag, G5); the conformance's `drain` set; `lean-tests.sh`
  (reclaimtest); UnlinkFuzz. By hand: ReclaimCost (`Reclaim.Stats`);
  FracRuns (026-04), not on `main`; 031-06's probes, in the item
  (`P2CrashProbe`'s sweep, `FaultProbe`, `ConcProbe`, `SafetyProbe`,
  `PaceProbe`, `WarmProbe`, and for timing `P1Probe`, `BigStepProbe`).


## 8. Principles and rules

* **P1**, no stop-the-world: a step is bounded by its paths (024-07) and
  its scan by its cap; the warm-up reads the step's range before the lock
  (1.11); a deviation: the physical cut waits for the storage's append
  (015-80). **P2**, a deterministic stream: every record of reclaim's is
  an action's record, decided from the stream before it, its time and its
  action's KVs (031-06); R and f are in the stream (015-87); `maintain()`
  writes as its calls and their times decide, its cost from counts;
  RESERVE is a constant (028-68), a smaller one a test hook only.
* **P3**, calm when not used: reclaim works in commits' records and
  `maintain()`'s parts only. **P4**, maintenance proportional to the
  user's work: at most one step a commit, within f of the growth and the
  cap of scan; a step's uncounted walk (1.4) is bounded by the reserve
  only. **P7**: a failure of the plan, or a record over its room, fails
  the database with nothing written (1.2, 4).
* **P10**, few settings: R and f; the Pub API sets R only. **P12**:
  reclaim treats every key and value as bytes, BergDB's own too; its own
  keys are reserved, and a caller's put or delete there is refused
  (024-37, CA3; 010-04, R5). **R1**: a refused setter call or
  `maintain()` call changes nothing; a commit refused by a stop during
  its plan writes nothing.


## 9. Limits and open work

* T-SCHEME is proved for BergDB's tree, given RC at each cut (030-24);
  RC1 and RC4 (Java's arithmetic of the cut) are checked at every cut,
  not proved; `IterationOK` (REWRITES) is proved from a model of the
  steps (030-25, with a step in a mixed record since 031-06); that Java's
  steps are the model's is checked step by step on the reclaim traces
  (C-STEP, 030-27) and gated, and its consequence RC2 is checked at every
  cut. 001-07's register rows M32, M33, M36, M41 and M48 are argued or
  checked. That a record's maintenance is a function of the stream before
  it (P2) is argued and checked by probes, not proved; its proof belongs
  with P2's extension, after 2026.7 (031-06, section 8, 026-14).
* The step's index nodes beside a large action: bounded by the checks of
  1.2 and 4, not derived for a commit's step of 128 KiB (031-06, section
  3); at lowered record limits the room cuts some steps to one copy, and
  a commit's record can carry none (ReclaimRoomTester).
* What no charge counts: the rows' and the tables' own value nodes and
  the table's path, about 0.01 to 0.03 of the growth above f at f = 1/4
  under small commits (4).
* 026-09, a keys-only scan (024-34, Q34-1, option b), landed on
  2026-11-14: a step does not load the value of a KV stored at pCut or
  later (`GetMany.valuesBefore`), which it counts as its key's bytes plus
  100 (1.4, step 2).
* A chase at the reserve (026-05, section 7): puts ahead of the scan,
  before E, of more than a reserve's worth of index nodes in every
  transaction keep an iteration going; not seen. Ahead of an ascending
  mass delete, up to 12 percent more stream written (026-05, section 6;
  accepted, its Q3).
* `maintain()`'s pass (1.10) rewrites the whole live data after one small
  put of the application's (031-06's review of the landed diff, R4;
  028-75, open): the cost of 031-04's rule.
* The 1,024 kept times and top node ordinals (1.1): no record of reclaim's
  needs them since 031-06; their removal is 031-06's Q4.
* Open: f's recommended values and default (026-04, chosen after 031-06's
  pace); the stream kept and the lag (BD8, BD10) are gated, not derived
  (017-04); protected long-lived reads that a cut would wait for (D1 = B)
  are not built.
* The row's text: Java's `HashMap` line order, a lenient parser, no
  version (027-03, G16, Q9; 026-12). E came with 026-05 before Q9, which
  027-03's Q8 asked for first, and a with 031-04: a reader without them
  (2026.5 and before for E, 2026.6 for a) would ignore them and drop them
  at its next store; 2026.6 and earlier refuse the stream by its meta
  version (156) before they read a row (027-03, section 21).


## 10. Evidence

001-07 (Level 3 in Lean, T-SCHEME's argument, the register); 001-09 (the
soak on disk); 011-04 (the rework of 2026-10-13, W1 to W5); 015-50 (a
step within the value limit); 015-54 (pSafe after the call's records);
015-80, 019-36 (the cut's wait); 015-87 (the settings kept); 023-05, P8,
and 023-08, fault 13 (the scan at a step's time); 024-07 (the last touch,
T-COVER, T-LATEST, B1 to B4); 024-29, 026-04 (the fraction, the lag's
mechanism); 024-30, 026-11 (the count gates, G4's lag); 024-32
(`maintain()`); 024-34 (OP8); 026-05 (each step at its own time, E, the
count, the pending cut); 026-09 (the values not loaded); 026-10 (the
forget at a decided cut); 028-26 (the row again, until 031-06); 028-47,
028-51, 028-53 (M1 until 031-06); 031-03 (the witness, the padded table);
031-04 (`maintain(int budget)`, the pass, a); 031-05 (the maintenance
decided from the stream before the record); 031-06 (one record an action,
its probes, its landing: the record's room in step 2, the charge, the cap
and the warm-up in step 3, its reviews); 028-68 (the reserve a constant);
028-71 (a commit's step by its allowance); 028-66 (the cut's deletes as a
batch, the gap).


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

2026-11-26. 4: the disk (028-62): `FileStream` gives a new file a
tenth of the stream, not a quarter; the part before fp of the file that
fp lies in, and the files that the storage's thread has not yet deleted,
measured apart; 6 to 9 percent was of 2026-10-13, before 005-46.

2026-11-28. Brought up to date with one record an action (031-06, landed
2026-11-27 and 2026-11-28, with 031-04's `maintain(int budget)` and
031-05's plan from the stream), from the code at 8a0897cf: section 1's
plan and apply; 1.1 (L0, tl, tt, a, the actions that carry maintenance,
the constants); 1.2 (a commit's B, S, P and C before the go point, the
cap, the record's room, the refusal by a stop); 1.3 and 1.5 (pStart and
pSafe the record's own position); 1.4 (the copies, the drop at the
action's keys, the merge, the charge in the record, the copy mark; 4b
gone); 1.6 and 1.7 (the decision in the plan, the cut after the record);
1.9 (a and the witness, no work at a start); 1.10 (the parts, M1 a pass,
M5 the padded table, the budget, the handover); 1.11 new (the warm-up);
sections 2 to 10 with them (ONE RECORD AN ACTION, THE PLAN FROM THE
STREAM, COPIES CHANGE NO USER READ; the step's room, the pace, the
pauses; 026-09 landed). By an agent of lead-1127, on the branch
`031-06-docs`.
