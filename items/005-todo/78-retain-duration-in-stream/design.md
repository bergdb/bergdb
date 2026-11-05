005-78, the design: the retain duration in the stream
=======================================================

For Frans to choose. Written 2026-11-05 from `main` at `0c6c4be` (after
release 2026.2), with the probe of the entry's U2 (`RetainProbe.java`, beside
this file; its output `probe.txt`). The entry is 005-78; its "Plan for
2026.2" asked for this file (section 4 there). Nothing in `java/` is changed.


# 1. Summary

* **The fault.** A start takes the builder's retain duration, forever by
  default, not the one the database ran with. In the probe, `l3-node8` with
  a retain duration of 1 s set once and a restart every 50 commits makes
  1 iteration and no cut, against 24 iterations and 22 cuts without
  restarts; it keeps 4,355,752 bytes of stream where the run without
  restarts keeps 2,094,096 (2.1 times), and the gap grows with every
  commit, as nothing is cut again. With the value set after each start, as
  every test does today, the streams are the same.
* **What Frans decides:** F1 to F7 below; F1, the form, is the approval of
  a format change that 016-01, section 3, asks for.
* **The recommendation:** B, an internal KV of reclaim's
  (`/#i/dreclaim/-settings.txt`) written by the setter as a small internal
  transaction and read at the start with the table; the stream's value wins
  over the builder's once there is one; a stream without one takes the
  builder's and writes it if it is finite; forever writes nothing.


# 2. For Frans to decide

## F1. The form: A, B or C?

* **A, the meta blocks.** 8 of the reserved bytes (offsets 46 to 53) hold
  the retain duration in time units. `Db.setRetainDuration` does what
  `Db.setStartupDistance` does: under the write lock, the state checked
  first, nothing if the value is in force, else the in-memory meta block
  set and a 200 kB value committed under `DbConstants.DUMMY_KEY`, so that a
  meta block holds the value before the call returns; the old value put
  back on failure. A start reads it in `Db.handleStartParams`, from the
  last valid meta block, and gives it to `Reclaim`. Cost: about 205 kB of
  stream a call (P5: 204,152 to 226,848 bytes). Checked by the restart test
  (section 5) and by StreamDigest with a mask of the field.
* **B, an internal KV.** The setter commits, under the write lock, an
  internal transaction (`Trans.isInternal`, as `Reclaim.storeTable`'s) that
  puts `/#i/dreclaim/-settings.txt` with the text `retain=<time units>`
  (a `StringMap`, as the table's rows). `Reclaim.initFromDb` reads it with
  `db.getOne(Long.MAX_VALUE, ...)`, as it reads the table, before `start()`
  returns. Cost: one small record a call (P5: 160 to 176 bytes when the
  record carries no index nodes of earlier commits). Reclaim's steps
  rewrite it like any live value (Q6, P3), so cuts never remove it.
  Checked by the restart test and by StreamDigest.
* **C, reclaim's table.** A field `retain=` in `-table.txt`, stored by the
  setter with `storeTable`. Read at the start by `initFromDb`'s parse.
  Cost: the table's size a call (estimated: hundreds of bytes to a few
  kB, with about 30 rows for a long retention; not measured). But the table
  has no place for a field of its own (each part is a row, and a part
  without `pStart` throws), so the field must go in every row; the table is
  not stored before the first iteration; and a table without rows makes
  today's and older parsers throw (`IterationTable.parse`, "Error in bergdb
  data"); so C changes the table's grammar, and 2026.1 and 2026.2 refuse a
  stream whose table has only the setting.
* **Recommended: B.** Tens of bytes, not 200 kB; the value lives with
  reclaim's other state and is read where that state is read; older
  versions ignore the key and keep it (their steps rewrite it); nothing in
  the meta blocks or the table's grammar changes. A is the precedent (one
  way for both kept settings) and a close second: its value needs no
  rewrite to survive cuts, and a new database can write it in its first
  transaction's meta block at no cost, as the startup distance; but every
  later call, and a first start on a stream without the value (F4), costs
  a 200 kB transaction, which is an external one that reclaim counts. C is
  out on its grammar change.
* **What follows:** the format gains one reserved internal key (016-01,
  section 3's list: "the reserved internal keys"); the C clone reads and
  writes the KV later (U7).

## F2. The builder against the stream, for a database with a value

* **Option 1, the stream's value wins** (as the startup distance,
  `DatabaseBuilder.startupDistanceInMb`'s Javadoc: "Existing databases keep
  the startup distance stored in their stream"). The builder's value is
  used only where the stream has none (F4). A change is a call of
  `Database.setRetainDuration`.
* **Option 2, the builder's value written when it differs.** A builder
  value given explicitly, and other than the stream's, is written at the
  start, as a call right after it would be. Needs F3's "unset".
* **Recommended: option 1.** One rule for both settings that are kept;
  P2 holds by construction (a start writes nothing when the stream has a
  value); no "unset" state in `DbBuilder`. The cost: an application that
  changes the builder's value between runs sees it ignored, so the Javadoc
  must say it, as `startupDistanceInMb`'s does.
* **What follows:** `DatabaseBuilder.retainDuration`'s Javadoc says that
  the value is for a new database, or one without a value (F4).

## F3. Unset against forever

* **Option 1, not needed.** With F2's option 1 and F4's rule, a builder's
  forever and an unset builder do the same: nothing written, forever in
  force where the stream has no value. `DbBuilder` stays as it is
  (`retainDurationInTimeUnits = Long.MAX_VALUE` in the constructor;
  `retainForever()` is `retainDuration(Long.MAX_VALUE)`).
* **Option 2, a distinct unset.** `DbBuilder` keeps `-1` for unset, and
  `retainForever()` sets `Long.MAX_VALUE`; needed only for F2's option 2.
* **Recommended: option 1**, with F2's option 1.

## F4. A stream without a value

Streams written before the change have none: 2026.2's (shipped 2026-11-04,
so there may be users' databases), and HEAD's until the change. 2026.1's are
refused since 005-50 anyway.

* **Option 1, the builder's value, written at that start if it is
  finite.** The start reads no value, takes the builder's, and if it is not
  forever commits the setting's record before `start()` returns. From then
  on the stream has it, and F2 applies. A new database is the same case:
  it gets the builder's value written at its first start if finite.
* **Option 2, the builder's value, written only at the first call.**
  Until a call, every start takes its builder's value, as today.
* **Recommended: option 1.** An application that passes the value to the
  builder at every start, as 2026.2's notes advise, keeps working and
  writes the record once; with option 2 it would keep today's fault.
* **What follows:** a start can write one record (B: about 170 bytes),
  once in a database's life unless the value is never finite.

## F5. Forever

* **Option 1, forever writes nothing.** No record (B), 0 in the meta
  block (A) means "no value", and with F4's option 1 forever is then in
  force unless the builder says otherwise. A database that had a finite
  value and goes back to forever writes `retain=forever` (B) or
  `Long.MAX_VALUE` (A) by the setter: then the stream has a value.
  StreamDigest: the 8 configurations without a retain duration keep their
  streams; the 4 `l3-*` change by the record after their first start.
* **Option 2, every new database writes its value, forever too.** A's
  meta blocks then all change (`Long.MAX_VALUE` in every block), so all 36
  StreamDigest streams; B's adds a record to every new database.
* **Recommended: option 1.**

## F6. The setter

* **The rule:** `Db.setRetainDuration` becomes a commit under the write
  lock: `assertDbStateIsActive` first (a refused call changes nothing),
  nothing written when the value is in force, else the record committed
  and `Reclaim`'s field set under the same lock; on failure the old value
  stays. Its place among the transactions is then defined; today the
  volatile field (`Reclaim.setRetainDuration`) is read by whichever commit
  comes next. JMX's three setters go through it.
* **The Javadoc:** `Database.setRetainDuration` says "This method can be
  called before start() or while the database is running", but a
  `Database` exists only after `DatabaseBuilder.start()`: the sentence
  goes, and the Javadoc says that the value is kept in the stream, as
  `setStartupDistanceInMb`'s does, and the exceptions of a refused call.
* **Recommended:** as above; no option is close.

## F7. The other settings of reclaim's (question 9)

* **The internal fraction** (`Db.setReclaimInternalFraction`, JMX only;
  an `int` in units of 2^-16 since 005-79, 16,384 by default) changes the
  step allowance (`Reclaim.transactionCompleted`, `fractionOf`), so the
  bytes, whenever it is set, and a start forgets it.
  * Option 1: kept in the same record (B: a second line,
    `fraction=16384`; A: 2 more reserved bytes), written only when it is
    not the default.
  * Option 2: documented as lasting for the run, for tests and
    measurements.
  * Option 3: its setters removed from `Db` and JMX.
  * Recommended: option 1 with B (no extra record, the same rule);
    option 2 with A.
* **The step reserve** (`DbBuilder.reclaimStepReserve`, the system
  property `stepreserve`) splits steps only below its default of 4 MiB:
  P4 finds no split step at the default in the four `l3-*` workloads (see
  section 4 for the 2,000-byte run). Recommended: documented as a setting
  for tests (it changes the records below the default, and a start takes
  the builder's), not kept.


# 3. The three forms side by side

**What a call writes, and its bytes.**
* A: a 200 kB value under `/#i/-dummy`, its record about 205 kB (P5), and
  8 bytes in every meta block after it.
* B: an internal record with one KV of about 30 bytes; 160 to 176 bytes
  (P5), more when the take puts earlier commits' index nodes in it.
* C: the whole table, a record of hundreds of bytes to a few kB.

**What a start reads, and where.**
* A: `Db.handleStartParams`, the last valid meta block, as
  `params.startupDistance`; before the transactions are replayed.
* B: `Reclaim.initFromDb`, `db.getOne` of the key, after `startDb` and
  `state = ACTIVE`, before `start()` returns (`Db.startInner`).
* C: `Reclaim.initFromDb`, the table's parse.

**A new database, and StreamDigest.** With F5's option 1: A, B and C
leave the 8 configurations without a retain duration unchanged; the 4
`l3-*` change after their first start's call. With option 2: A changes all
36; B and C the 8 by a record.

**Survives cuts.** A: every meta block carries it. B: yes; the step's scan
(`Reclaim.step`: `db.getMany` from `lastKey` at `tStart`, no prefix
filter) reaches `/#i/` keys and rewrites a live value stored before
`pCut`; P3 found the probe's KVs after 21 to 26 cuts and after a restart
on the cut stream. C: the table is stored again at each cut.

**A copy of the stream.** Replication is removed (005-11, `16fb228`); a
byte copy of the stream (a file copy, `MemoryStream.copy`) carries the
value in all three forms, and a database started on it uses it.

**What 2026.1 and 2026.2 do with such a stream.**
* A: `MetaBlock.checkFormat` checks the magic, the last transaction's
  position and the time only (at `release-2026.1` too); the reserved bytes
  are not read, and a block read whole is written on, so the field is
  passed on. The older version runs with its builder's value.
* B: the key is a KV it never reads; its steps rewrite it (the same scan
  at `release-2026.1`), so it is kept. It runs with its builder's value.
* C: a row's unknown field is ignored (`IterationInfo.deserialize` reads
  named keys only), but a table without rows throws
  `InternalDataException` at the start, and its next table store drops
  the field.

**Which part of the format changes** (016-01, section 3: "the meta
blocks, record headers and records, the node encodings, reclaim's table,
the version numbers and the reserved internal keys"). A: the meta blocks
(a field in the reserved bytes, the version kept, as 005-50's node size).
B: the reserved internal keys (one more). C: reclaim's table (a field, and
a table that may have no rows).

**The code to change.**
* A: `MetaBlock` (the field, its accessors, the format comment; ~20
  lines), `Db.handleStartParams` and the first transaction (~5),
  `Db.setRetainDuration` (~35, as `setStartupDistance`), the start's
  write for F4 (~10).
* B: `Reclaim` (the key, `initFromDb`'s read, a `storeSettings` beside
  `storeTable`; ~40), `Db.setRetainDuration` (~25), the start's write for
  F4 (~10).
* C: `Reclaim.IterationTable` (a header part or a per-row field, a parse
  that allows no rows; ~40), `storeTable` at the setter, `Db` (~25).
* All: the Pub Javadoc (`Database`, `DatabaseBuilder`), JMX's Javadoc,
  the tests of section 5 (~150 lines), StreamDigest's mode.

**The C clone later (U7).** A: the meta block's field, read and written.
B: the key read at the start, the record written by the setter, as the
clone's reclaim reads and stores its table under the same prefix (012's
`c/src/reclaim.h`: `RC_TABLE_KEY_NAME`, `RC_CURRENT_KEY_NAME`). C: the
table's parser and writer. B and A are about the same; C the most.

**Lean and the traces.** Nothing in the model changes in any form (Q10):
A's meta blocks are not modelled and its 200 kB transaction is an ordinary
one; B's and C's records are transactions like reclaim's table stores. The
exporter marks B's record `kind=table` (`TraceExport`: `!isInternal ?
"user" : touch ? "step" : "table"`), A's `kind=user`; the kind is in a `#`
comment line, which `lean/Check/Trace.lean` skips, so the checker treats
every `TX` alike.

**The risks.**
* A: 200 kB a call; `setStartupDistance`'s dummy is an external
  transaction, so reclaim may start an iteration or a step at it; the
  value of an older version's run is not updated (it passes the field on).
* B: one more reserved key; the record is internal, so
  `Reclaim.transactionCompleted` makes no decision at it (as for a table
  store), and `Connection.transactionInfo` never reaches it (no user value
  points to it); the start's read is one more `getOne`. Its survival rests
  on the step's scan reaching internal keys, as the table's and the current
  row's do; a change that made the scan skip them would lose it, so a unit
  test checks it (section 5).
* C: older versions fail on a table without rows; the table's grammar
  and every table store carry the setting; the C clone's parser.


# 4. The evidence

## 4.1 The probe

`RetainProbe.java`, run on the clone of `0c6c4be` (`/Users/f/fl/bench/016/005-78`),
StreamDigest's four `l3-*` workloads, retain duration 1 s, `CoreTestClock`;
the full output is `probe.txt`. Modes: `plain` (set at the start),
`restarts-each` (set after each start, StreamDigest's restarts),
`restarts-once` (set after the first start only, restarts every `every`),
`restarts-50` (the same, every 50 commits), `call-100` (set after commit
100), `after-call` (as `call-100`, a restart right after the call and every
50 commits after it), `p3` (form B's KV, question 6).

PROBE-TABLE

## 4.2 The study: questions 1 to 10, from `0c6c4be`

1. **The form.** `MetaBlock`: offset 40 the startup distance (4 bytes), 44
   the node size (2), 46 to 126 reserved (81, zero). Its comment on
   `CURRENT_VERSION`: a field in the reserved bytes keeps the version, as an
   older version "neither checks nor reads those bytes, and it copies a
   block it read whole". `Db.setStartupDistance` (the pattern for A):
   `assertDbStateIsActive`, return if in force, set the field and the
   meta block, commit 200 kB under `DUMMY_KEY`, restore on failure.
   `Reclaim.storeTable` commits the table as an internal transaction;
   `IterationTable.parse` splits rows by `----next----` and throws when
   there is none; `IterationInfo.deserialize` reads named keys and ignores
   others. At `release-2026.1`, `MetaBlock.checkFormat` and
   `IterationTable.parse` are as today. So: A and B are invisible to an
   older version; C is too only while the table has rows.
2. **The builder.** `DbBuilder`'s constructor sets
   `retainDurationInTimeUnits = Long.MAX_VALUE`; `retainForever()` is
   `retainDuration(Long.MAX_VALUE)`; `testSetupExceptStream` calls
   `retainForever()`. So unset and forever are one value.
   `DatabaseBuilderImp.retainDuration` passes `Duration.units()`
   (`Duration.MAX` is `Long.MAX_VALUE`). `Db`'s constructor:
   `reclaim.setRetainDuration(b.retainDurationInTimeUnits)` at every start.
   The precedent: `DatabaseBuilder.startupDistanceInMb`'s Javadoc,
   "Existing databases keep the startup distance stored in their stream".
3. **Old databases.** Since 005-50 (`bf19075`) a start refuses a stream
   without the node size, so 2026.1's databases are refused; 2026.2's
   (`release-2026.2`, 2026-11-04) open, and have no retain duration in any
   form. The rule for a stream without a value is F4; 2026.2's notes list
   the fault as a known issue (`releases/2026.2/readme.md`, "The retain
   duration is not kept in the stream").
4. **Forever.** A: 0 (none) or `Long.MAX_VALUE`; B and C: no record or
   `retain=forever`. StreamDigest's 12 configurations: 4 set a retain
   duration (`l3-*`, `retain=1`, after each start in `StreamDigest.start`),
   8 do not; F5.
5. **The setter.** `Db.setRetainDuration` calls `Reclaim.setRetainDuration`,
   which checks at least one second and sets a volatile field: no lock, no
   record, no state check. `DatabaseImp.setRetainDuration` checks at least
   one second, then `Db.setRetainDuration`. JMX's `setRetainDuration`,
   `setRetainDurationInSeconds`, `setRetainDurationInDays` (`Jmx.java`) go
   through `Db`. `Database.setRetainDuration`'s Javadoc: "can be called
   before start()", wrong, as a `Database` comes from `start()`.
6. **Survives the cuts.** `Reclaim.step`: `g.startKey = it.lastKey` (null
   at the iteration's first step), `g.lookupTime = it.tStart`, no key
   filter; every live value with `gd.tpos < it.pCut` is rewritten. So
   internal KVs are rewritten as the user's, the table's own keys too.
   `pretruncateIfPossible` and `cutIfDurable` cut at `pCut` after the
   iteration is done and safe, so a live value is never cut away. Shown by
   P3 (section 4.1).
7. **The restart test.** Section 5; the probe's `restarts-50` and
   `after-call` are its two halves and fail today.
8. **Replicas.** Replication is removed (005-11, `16fb228`). A byte copy
   carries the value in each form; nothing else to check.
9. **The other settings.** The internal fraction:
   `Db.setReclaimInternalFraction` (0.001 to 0.90, converted to units of
   2^-16) and JMX's `setReclaimInternalFraction`; used by
   `transactionCompleted`'s allowance at every step, not kept. The step
   reserve: `DbBuilder.reclaimStepReserve`, default
   `Long.getLong("stepreserve", Reclaim.DEFAULT_STEP_RESERVE)`, given to
   `Reclaim.setStepReserve` in `Db`'s constructor; it stops a step's scan
   when the index nodes followed would pass it. P4 in section 4.1.
10. **Lean and the traces.** `faPolicy` (`lean/SIS/Algorithm.lean`) and
    reclaim's records as given `TX` blocks; the exporter's `kind=` from
    `Trans.isInternal` and `touch` (`TraceExport`, the record's comment
    line), skipped by the parser (`lean/Check/Trace.lean`: a line that
    starts with `#`). Confirmed by reading; no Lean was run.

**How a start orders its work** (`Db`'s constructor, `Db.startInner`):
the constructor makes `Reclaim` and gives it the builder's step reserve and
retain duration; `startInner` runs `nodeStream.recover`,
`handleStartParams` (the meta block's startup distance), reads the
transactions from the startup position, `startDb`, then `state = ACTIVE`
and `Reclaim.initFromDb` (the table, the current row, the first available
position), all before `start()` returns. A value in the meta block (A) is
in force from `handleStartParams`; a KV (B) or a table field (C) from
`initFromDb`; in each case before the first transaction after the start.


# 5. The change after the choice

* **The files.** B: `Reclaim` (key, read, store), `Db.setRetainDuration`
  and the start's write (F4), `Jmx` (Javadoc), `pub/Database.java`,
  `pub/DatabaseBuilder.java` (Javadoc), `pubimp/DatabaseImp.java` (the
  exceptions). A: `MetaBlock` and `Db` instead of `Reclaim`'s key.
* **The tests** (in `DbTesterRestart`, beside
  `dbShouldRememberStartupDistance1` and `2`):
  * the restart test: `l3-node8`'s kind of workload, the value set once
    by `setRetainDuration` after commit 100 (builder default), a restart
    right after the call and every 50 commits after, without setting it
    again; the stream from the decided cut equals the run without
    restarts. It fails on `0c6c4be` (the probe's `after-call`) and passes
    after;
  * a refused call (a stopped database) changes nothing;
  * a call with the value in force writes nothing (the length unchanged);
  * a stream without the value starts with the builder's, and writes it
    once if finite (F4);
  * with F7 option 1, the fraction kept across a restart;
  * B: the setting's KV found after three cuts or more, and after a restart
    on the cut stream (the probe's P3).

  The restart test, as a sketch (`RetainProbe.run` has the working code,
  with `StreamDigest`'s workload):

  ```java
  /** The retain duration set once is kept over restarts (bergdb 005-78). */
  @Nano private static void retainDurationKeptOverRestarts() {
      String plain = run(false), restarts = run(true);
      Assert.assertEquals(plain, restarts);   // fails on 0c6c4be
  }

  /** The digest from the decided cut; restarts: after the call, then every 50. */
  private static String run(boolean restarts) {
      MemoryStream stream = new MemoryStream();
      CoreTestClock clock = new CoreTestClock();
      Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
              .maxNodeSize8().start();       // the builder's default: forever
      Random rnd = new Random(1);
      for (int i = 1; i <= 2000; i++) {
          clock.setTime(i * Clock.UNITS_PER_SEC / 10);
          db.execute(db.trans().put("/k/" + rnd.nextInt(500), new byte[1 + rnd.nextInt(40)]));
          if (i == 100) db.setRetainDuration(Clock.UNITS_PER_SEC);
          if (restarts && i >= 100 && i % 50 == 0 && i < 2000) {
              db.sync(SyncLevel.ORDINARY);
              db.stop();
              stream = stream.copy();
              db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                      .maxNodeSize8().start();   // the value not set again
          }
      }
      db.sync(SyncLevel.ORDINARY);
      long cut = Math.max(stream.getFirstPos(), db.getFirstAvailablePos());
      String digest = sha256(stream, cut) + " " + stream.getLength();
      Assert.assertTrue("cuts", stream.getFirstPos() > 0);
      db.stop();
      return digest;
  }
  ```
* **StreamDigest:** a fourth mode, `restarts-once`, that sets the value
  after the first start only, and must give plain's stream; the 8
  configurations without a retain duration unchanged (F5 option 1); the 4
  `l3-*` changed once, recorded as a new reference.
* **level3.sh:** a RestartInvariance configuration with the value set once.
* **Gates:** `java/before-commit.sh`, `java/stress/level3.sh` and
  `level2.sh`. Size: about 1.5 days with the tests.


# 6. The release

* 2026.2 shipped with the known issue (`releases/2026.2/readme.md`); its
  Javadoc was not changed (`Database.setRetainDuration` still says "before
  start()").
* The change goes into the next release: an API change in what a restart
  does (the value is kept), so a line in `releases/next.md`; the bytes of
  databases that reclaim change once (the record after the first start);
  the C clone follows later (U7), and until then Java and C differ on
  restarts that do not set the value.


# 7. Not decided here

Replication (005-11, removed), the C clone (U7), and 014-01.
