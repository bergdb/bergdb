005-78. Investigate: the retain duration is not kept in the stream
=================================================================

Status: open; the study (U1), the probe (U2) and the design (U3) done
2026-11-05, on `0c6c4be`, after release 2026.2: [design.md](78-retain-duration-in-stream/design.md),
the probe `78-retain-duration-in-stream/RetainProbe.java` and its output
`probe.txt`; waiting for Frans's choice, F1 to F7 ("For Frans", at the
end). Nothing in `java/` changed. Kind: investigate. Created 2026-10-29.

Registered as Frans decided (2026-10-29, 10:09), on 006-10's decision 6
(006-10, section 8: "The retain duration changes the stream's bytes but is
not kept in the stream, against the rule of 005-53 and 005-52"): "Yes, as
recommended for 5 to 9. One change for 6. It really should be in the
stream. It must be really, to follow our principle of a deterministic
stream. Still an Investigate entry. Important to study first." So the
direction is decided, the retain duration goes into the stream (010-01,
P2); how is to be studied first, and the design is for Frans. Registered
only; nothing run or changed. Code cited at `bcc7d3b`.


The issue
---------

The retain duration decides what reclaim does, and so the stream's bytes,
but a start does not find it in the stream: it takes the builder's value.

**Where it is set.**

* Pub API: `DatabaseBuilder.retainDuration(Duration)` ("Sets the wanted
  retain duration.", nothing more), implemented by
  `DatabaseBuilderImp.retainDuration`, which passes it to
  `DbBuilder.retainDuration`; `Database.setRetainDuration(Duration)` and
  `getRetainDuration()`, implemented by `DatabaseImp.setRetainDuration`
  (at least one second, then `Db.setRetainDuration`).
* Core: `DbBuilder.retainDuration(long)` (at least one second; the default
  `Long.MAX_VALUE`, forever, set in the constructor; `retainForever()`).
  `Db`'s constructor gives the builder's value to
  `Reclaim.setRetainDuration` (`Db.java`, `reclaim.setRetainDuration(
  b.retainDurationInTimeUnits)`), at every start, new database or not.
  `Db.setRetainDuration(long)` calls `Reclaim.setRetainDuration`, which
  sets a volatile field (`Reclaim.retainDuration`): no lock, no record, no
  check of the database's state. JMX's `setRetainDuration`,
  `setRetainDurationInSeconds` and `setRetainDurationInDays` (`Jmx.java`)
  go through `Db.setRetainDuration`.

**Where reclaim uses it** (both in the writer, under the write lock, at
each external transaction, from `Reclaim.transactionCompleted`):

* An iteration starts when the stream has grown by 2 sd since the last
  one started and a quarter of the retain duration has passed
  (`transactionCompleted`: `retainDuration != Long.MAX_VALUE` and
  `t.tt - lastTStart() >= ITERATION_SPACING * retainDuration`,
  `ITERATION_SPACING = 0.25`). The start stores reclaim's table (a record),
  and the iteration's steps follow at later commits (records that rewrite
  live values and touch index nodes). With the default, forever, no
  iteration ever starts.
* The cut: `pretruncateIfPossible(t.tt)` reads `db.getRetainDuration()` as
  `tRetain` and cuts at the newest done, safe iteration whose `tEnd` is
  older than `timeNow - tRetain`; marking the cut stores the table again (a
  record), and the cut moves the stream's first position.

So with the same transactions, two retain durations give different
streams: when iterations start, which steps are written, when the table is
stored and where the stream is cut. The times are the transactions' times
(`t.tt`), so with the same value the decisions are deterministic; only the
value is not in the stream.

**What a restart does today.** A start takes the builder's value, the
Pub API's and the core's default being forever. An application that calls
`setRetainDuration` after `start()`, or opens the database again with
another builder, or without `retainDuration`, gets after the restart a
reclaim with another value, or none: the transactions that follow give
other internal records than without the restart. That is what P2 rules
out: "a restart can be inserted between any two transactions without
affecting the bytes in the stream" (010-01, P2, Frans's goal of
2015-12-28). Neither `Database.setRetainDuration`'s Javadoc nor
`DatabaseBuilder.retainDuration`'s says that the value is not kept.

**Why the checks do not see it.** Every program that checks restarts
sets the retain duration again after each start: StreamDigest
(`start()`: `if (retain > 0) db.setRetainDuration(...)`, after
`b.start()`), RestartInvariance, TraceExport, CrashTest. Their restart
streams agree with the plain ones because each start passes the same
value; no test restarts without setting it again.

**How the startup distance is kept** (005-53's report, 1.2; its
Outcome; `Db` and `MetaBlock` at `bcc7d3b`): in the meta blocks, not in a
record of its own.

* `MetaBlock`, offset 40, 4 bytes: the startup distance; every meta block,
  one every 200 kB of stream (`RecoverableStream.META_BLOCK_DISTANCE`), has
  it. Offset 44, 2 bytes: the node size (005-50); offsets 46 to 126, 81
  bytes, reserved, zero. A new field there keeps the format's version
  (`MetaBlock`'s comment on `CURRENT_VERSION`, as 005-50 did).
* A new database writes the builder's value (`Db`, the first transaction:
  `meta.setStartupDistance(startupDistance)`); an existing database keeps
  the stream's: `Db.handleStartParams` reads the last valid meta block's
  value at every start (`params.startupDistance =
  meta.getStartupDistance()`), and the builder's value is not used
  (`DatabaseBuilder.startupDistanceInMb`: "Existing databases keep the
  startup distance stored in their stream").
* `Db.setStartupDistance` (005-53): under the write lock, checks the state
  first (a refused call changes nothing), returns at once if the value is
  in force (writes nothing), sets the field and the in-memory meta block,
  and commits a transaction with a 200 kB value under
  `DbConstants.DUMMY_KEY`, so that a meta block in the stream holds the new
  value before the call returns; a restart right after the call reads it
  there. On failure the old value is put back.
* Tested by `DbTesterRestart.dbShouldRememberStartupDistance1` and `2`,
  and `testSameStreamAfterDecreaseWithRestartsF` (007-07, 10.2: a
  decrease with a restart right after the call and every 10 commits gives
  the same stream, byte for byte). The Pub setter is
  `Database.setStartupDistanceInMb` (005-53, `fd8f513`).


The rule, and how the retain duration breaks it
-----------------------------------------------

005-53 and 005-52 decided one pattern for a setting changed while the
database runs (005-53's report, section 4; `Db.setCacheSizeIndicator`'s
and `Database.setCacheSizeInMb`'s Javadoc): **a setting that changes the
stream's bytes is kept in the stream (P2); one that does not lasts for the
run.** The startup distance changes the bytes (the take) and is kept; the
cache size does not (level4.sh's EvictionInvariance) and lasts for the
run. The retain duration changes the bytes and lasts for the run: it
breaks the rule today. 005-53's report put it in its table as "retain
duration (today) | yes, reclaim | no", and its Outcome left it: "The
retain duration shapes the stream's bytes and yet a restart takes the
builder's value ... not this entry's; its Javadoc does not say so." 010-01's
P2, "To check", names the memory budget, not the retain duration.

Two other settings of reclaim's are of the same kind and not kept either:
the internal fraction (`Db.setReclaimInternalFraction`, JMX only, default
0.25), which sets how much a step rewrites, and the step reserve
(`DbBuilder.reclaimStepReserve`, the system property `stepreserve`, for the
stress programs). Neither is in the Pub API.


What "in the stream" could mean
-------------------------------

Three forms, to be studied; none is chosen.

* **A. The meta blocks, as the startup distance.** 8 bytes of the
  reserved ones (offset 46) hold the retain duration; every meta block
  carries the value in force; `Db.setRetainDuration` does what
  `setStartupDistance` does: the state checked, nothing if the value is in
  force, the 200 kB dummy transaction so that a meta block holds it before
  the call returns. The start reads it in `handleStartParams` and gives it
  to `Reclaim`. Cost: 200 kB of stream per call (rare calls). The format's
  version stays (reserved bytes; an older BergDB ignores and copies them).
  Encoding to decide: 0 is what streams written before the change have;
  forever is `Long.MAX_VALUE` (writing it changes every meta block of every
  new database, so all 36 StreamDigest streams) or a code of its own.
* **B. A setting record: an internal KV.** The setter commits a small
  transaction of the database's own, for example a KV under reclaim's
  prefix (`Reclaim.KEY_PREFIX_SKEY`, `INTERNAL_PREFIX + "dreclaim/"`), with
  the value; the start reads it with `db.getOne` in
  `Reclaim.initFromDb`, as it reads the table. Tens of bytes, not 200 kB;
  the value is part of the database's state, so a restart finds it at any
  point after the record. It must survive reclaim's cuts: does a step
  rewrite internal KVs that are live and stored before pCut (as for
  `DUMMY_KEY`)? `Connection.transactionInfo()` leaves internal KVs out
  (005-42). `Reclaim`'s statistics and the trace exporter classify a
  record by `Trans.isInternal` and `touch` (user, step, table): a setting
  record committed as reclaim's table is (`isInternal`) shows as a table
  store, and is skipped by `transactionCompleted`; one committed as
  `setStartupDistance`'s 200 kB transaction is shows as a user's, and
  reclaim treats it as one.
* **C. Reclaim's table** (`dreclaim/-table.txt`): a field `retain=` in the
  table, stored by the setter. The table is reclaim's own state, read at
  every start; but its format changes (and the C clone parses it, 012),
  and a table is otherwise stored only when an iteration starts, ends,
  gets safe or is cut.

In all three, the setter becomes a commit: under the write lock, refused on
a database that is not active (as `setStartupDistance`, 005-53), so its
place among the transactions is defined. Today the volatile field is read
by whichever commit comes next, so a call concurrent with commits takes
effect at a transaction that depends on timing.

**What a start does with it.** The stream's value, if there is one, is
the one in force, as for the startup distance. Then:

* **The builder's value against the stream's.** As the startup distance:
  the builder's value for a new database only, and an existing database
  keeps the stream's (the change is `setRetainDuration`)? Or a value given
  to the builder explicitly, when it differs from the stream's, is written
  at the start, as a call right after it would? `DbBuilder` cannot tell an
  unset value from forever today (both `Long.MAX_VALUE`); the Pub
  builder's Javadoc must say which.
* **Old databases without it.** Release 2026.1 is out, so streams written
  by 2026.1 and since (until the change) have no value (0 in the meta
  block's reserved bytes, or no KV). Take the builder's value, as today,
  for them; and write it at the first start, so that from then on it is
  in the stream, or only at the first `setRetainDuration`?
* **Replicas.** A replica is a byte copy of the main stream (005-11), so
  it carries the value in any of the three forms; a replica started as a
  database then gets the main's retain duration, where today it gets its
  opener's. `addReplica`'s copy and 005-11's open decision are not
  affected; to be confirmed.
* **The C clone** (012) has the retain duration (`bergdb.h`:
  `retain_duration`, `bergdb_set_retain_duration`) and is compared with
  Java byte for byte (`cross.sh`); it must follow the chosen form.


StreamDigest and the Lean model
-------------------------------

**StreamDigest** (12 configurations, plain, reads and restarts, 36
streams; P2's check). Four configurations set a retain duration (`l3-*`,
`retain=1`), after each start. With the change:

* Their streams change, as intended: the setting's record (B, C), or the
  200 kB transaction and the meta blocks' bytes (A), after the first
  start. In each configuration the plain, reads and restarts streams must
  still agree; with "a call with the value in force writes nothing", the
  calls after the restarts write nothing.
* The other 8 configurations stay identical with B and C, and with A if
  forever is encoded as nothing written; otherwise every stream changes.
* A new check, the one that fails today: a restart mode, or a test in
  `DbTesterRestart`, that sets the retain duration once and restarts
  without setting it again (every k commits, and right after the call),
  and gives the same stream as without restarts. Today reclaim stops after
  the first restart (the builder's default, forever).

**The Lean model has no retain duration.** Reclaim enters it in two
ways: the first available time policy (`faPolicy`, `SIS/Algorithm.lean`;
Java's is the end of the newest iteration marked cut in reclaim's table),
and reclaim's transactions, its steps and table stores, which the traces
carry as ordinary `TX` blocks (`kind=step` or `table`; docs/trace-format.md,
"With reclaim") and which the model takes as given, like the user's
(sis-model.md, 15.3; T12_restartCut: a run with restarts from safe cut
streams appends the records of the run without restarts, for the same
transactions). Which internal transactions exist is decided outside the
model, by the retain duration: today a restart with another value gives
other transactions, so the model's premise, the same transactions, is what
Java fails, and the model cannot see it (A1, the determinism of the
transactions, is where it sits). Kept in the stream, nothing in the model
changes: B's or C's setting record is a transaction like reclaim's table
store, A's meta blocks are not modelled (their 200 kB transaction is an
ordinary one). The trace exporter (TraceExport sets the retain duration
after each start) would show the record as a table store or a user's
transaction, by how it is committed (`kind=`, from `Trans.isInternal`);
the trace checker treats every `TX` alike. To confirm on a
trace with restarts.


Questions
---------

1. **The form:** A (meta blocks, as the startup distance), B (an internal
   KV) or C (reclaim's table)? Cost per call, what a start reads, what an
   older BergDB does with the stream, the C clone.
2. **The builder against the stream:** for an existing database, is the
   builder's retain duration ignored (as the startup distance's) or
   written at start when it differs? And how does `DbBuilder` tell unset
   from forever?
3. **Old databases** (2026.1 and since, before the change): the builder's
   value, and written at the first start or at the first call?
4. **Forever:** how it is encoded, and whether a new database writes it
   (36 streams changed) or nothing (8 unchanged).
5. **The setter's semantics:** a commit under the write lock, refused when
   the database is not active, nothing written when the value is in force
   (as `setStartupDistance`); `Database.setRetainDuration`'s Javadoc says
   "This method can be called before start() or while the database is
   running", while a `Database` exists only after start.
6. **Survives cuts (B):** does a step rewrite live internal KVs stored
   before pCut, so that the setting's KV is never cut away?
7. **Restarts, the test:** a restart right after the call and every k
   commits after it, without setting the value again, gives the stream of
   the run without restarts; it fails today. And with a cut between.
8. **Replicas:** a replica carries the value; a replica started alone
   uses it; anything in 005-11's faults that changes?
9. **The other reclaim settings:** the internal fraction (JMX) and the
   step reserve (the builder, a system property) change the stream too;
   kept in the stream as well, documented as for tests only, or left?
10. **The Lean model and the traces:** confirm that nothing in the model
    changes, and how the exporter marks the setting's record.


Done when
---------

* A design for Frans, from questions 1 to 10: the form, what a start
  does, the builder's value, old databases, forever, replicas, the C
  clone; and his decision.
* Then the change: `Db.setRetainDuration` and the start, the Pub API's
  `Database.setRetainDuration` and `DatabaseBuilder.retainDuration` with
  Javadoc that says the value is kept in the stream (as
  `setStartupDistanceInMb`'s does), JMX following; tests: the restart test
  of question 7 (fails before, passes after), a refused call changes
  nothing, a call with the value in force writes nothing, an old stream
  without the value starts with the builder's; StreamDigest: the 8
  configurations without a retain duration identical (or the change of all
  36 explained, question 4), the 4 with one changed and plain, reads and
  restarts agreeing in each; `java/before-commit.sh` (BEFORE COMMIT OK),
  `java/stress/level3.sh` (reclaim) and `level2.sh`, the C clone's
  `cross.sh` if the form touches what it compares; 010-01's P2 (the retain
  duration checked), `releases/next.md` (an API change: the retain
  duration is kept), docs/levels.md.


First step
----------

Read `Reclaim`'s step scan for internal keys (question 6) and how a start
orders `handleStartParams`, `Reclaim`'s construction and `initFromDb`
(where a stored value would be read, and before which first transaction it
must be in force); then a probe in a scratch clone, without changing the
code: a database with a retain duration of 1 s and a `CoreTestClock`, a
restart every 50 commits without setting it again, against the run
without restarts, to show the streams differ today (and where: the first
iteration after a restart that does not start). Then the design, A, B and C
side by side, for Frans.


Size and order
--------------

S to M: the study and the probe about half a day; the change, with the
tests and StreamDigest, about a day, more if the C clone must follow.
Independent of the other entries; before the next release, since it
changes what a restart does with a database that reclaims. Builds on
005-53 and 005-52 (the rule), 005-61 (reclaim reads the live startup
distance), 005-42 (internal KVs), 010-01's P2.


Note: 005-79
------------

2026-10-29, at Frans's request (15:48): 005-79 replaces the doubles in
reclaim's decisions with integers, done on its own, not with this entry:
the iteration spacing `(long) (ITERATION_SPACING * retainDuration)`
becomes `retainDuration / 4` (the same for every duration below 2^53
time units, about 28 years), and `setReclaimInternalFraction` takes an
integer. If the retain duration goes into the stream here, the value kept
is the long in time units, and the spacing derived from it in integers.


Decisions of 2026-11-03
-----------------------

* **In 2026.2's scope** (016-01, section 4.1, item 3, under D2): first the
  study and the probe, then a design for Frans that sets the three forms
  side by side. It comes after 005-79, and the design is a stop for
  Frans.
* **Each form is a format question.** Frans: "Keep the stream format the
  same, unless I (Frans) explicitely approve changes." (016-01, section
  3.)
  * Each form adds something that a start reads: A the meta blocks'
    reserved bytes, B a reserved internal key, C reclaim's table.
  * Frans's choice of a form is the explicit approval that the rule asks
    for.
* **Java only** (Frans, 15:31): "The C code does not need to be updated
  for 2026.2 in this work. Only Java code will be included in the release.
  It is not a requirement to update the Lean code either. If this is
  needed to develop Java or to ensure it works well, then do it. See it as
  a tool, not an output artifact for the release." So the C clone follows
  after the release (the plan, U7). Lean is used only to confirm question
  10 (U1).
* **Tonight** (Frans, 15:40): "try your best to finish this work by 07:00
  tomorrow in the morning ... instead of in three days or so. Note, you
  only need before-commit.sh to be successful to commit your work."
  * The release commit is made at about 01:45 tonight, and Frans decides
    on the design in the morning.
  * So tonight makes only the study, the probe and the design. The
    change comes after 2026.2. In 2026.2 this is a known issue (U5), as
    the coordinator intends.
* **Question 9 goes with 005-79's fraction.** 005-79's plan settles the
  internal fraction as an `int` in units of 2^-16 (0.25 is 16,384). Kept
  in the stream, it is 2 bytes or a short field.


Plan for 2026.2
---------------

History: this plan was made for the night of 2026-11-03 and was not run
then. 2026.2 shipped (2026-11-04, `release-2026.2`) with the fault as a
known issue in its notes (`releases/2026.2/readme.md`, "The retain duration
is not kept in the stream"); the Javadoc of U5 was not changed. U1 to U3
were done on 2026-11-05 (section 8, State); U5 and U6 now belong to the
next release.

### 1. Tonight, and later

| Step | What | Who | Size | Gate or check |
|---|---|---|---|---|
| U0 | The clone, the status | coordinator | 5 min | the base commit recorded |
| U1 | The study: questions 1 to 10 from the code | agent | 2 h | each answer cites the code |
| U2 | The probe | agent | 1.5 h | restarts-once differs, restarts-each does not |
| U3 | The design for Frans | agent | 2 h | section 4's contents, checked by the coordinator |
| U4 | The stop for Frans | coordinator | 5 min | `news.sh` "needs a look"; 016-02's line |
| U5 | 2026.2's known issue: notes, Javadoc | agent | 30 min | `before-commit.sh` for the Javadoc |
| U6 | The change, after Frans's choice | agent | 1.5 days | section 6 |
| U7 | The C clone follows (after 2026.2) | later | hours | C's gate, `cross.sh full` |

* U1 to U3 and U5 are done tonight by one agent in
  `/Users/f/fl/bench/016/005-78/`, beside 005-79's agent.
* U1 and U2 overlap: the probe is written while the code is read.
* Nothing in `java/` changes before U5. U5 changes only the Javadoc.
* The night:

  | Time | What |
  |---|---|
  | 16:50 | U0; U1 begins |
  | 18:00 | U2 begins (a build of the clone, then the probe's runs) |
  | 20:30 | U3, the design |
  | 22:30 | U4, the stop; U5's text and Javadoc to the coordinator |
  | 00:30 | U5 committed with the other fixes, or left to the notes alone |

**U0. The coordinator.**

* `git clone /Users/f/fl/repos/bergdb /Users/f/fl/bench/016/005-78`, and
  the base commit into this entry's State.
* 005-78's row in 005's table: "in progress (study)".

### 2. The study (U1)

What the agent reads, at the base commit, and what it writes down. Each
answer is two to five lines with the code it rests on (class and method).
The answers go into the design's section 4.

1. **The form** (question 1), the facts for section 4's table:
   * `MetaBlock` (`java/src/bergdb/storage/`): offsets 40 (the startup
     distance, 4 bytes), 44 (the node size, 2 bytes) and 46 to 126 (81
     reserved bytes). Its comment on `CURRENT_VERSION` says that an older
     version neither checks nor reads those bytes, and copies a block it
     read whole.
   * `Db.setStartupDistance`, the pattern for A: the state checked first,
     nothing when the value is in force, a 200 kB value under
     `DbConstants.DUMMY_KEY`, the old value put back on failure.
   * `Reclaim.storeTable`, and `IterationInfo`'s serialize and parse
     (around `Reclaim.java` lines 1000 to 1070): the table's text, and
     whether a field the parser does not know makes it throw
     `InternalDataException`. That decides C for an older reader and for
     the C clone.
   * What 2026.1 does with each form's stream, read at the tag
     (`git show release-2026.1:java/src/...`): A's bytes, B's unknown
     internal key, and C's table with a new field. (2026.2 refuses
     2026.1's streams, 005-50; the question is the other way.)
2. **The builder against the stream** (question 2):
   * `DbBuilder.retainDuration` and `retainForever` (both
     `Long.MAX_VALUE`, so an unset value cannot be told from forever);
   * `DatabaseBuilderImp.retainDuration`;
   * the startup distance's precedent, `DatabaseBuilder.startupDistanceInMb`'s
     Javadoc ("Existing databases keep the startup distance stored in their
     stream").
3. **Old databases** (question 3): since 005-50, every stream older than
   the change is a test database. Frans: "No need to consider "today's
   databases". There are none." (016-01, section 2.) So the answer is the
   rule for a stream without a value, not a migration.
4. **Forever** (question 4): each form's encodings, and how many of
   StreamDigest's 36 streams each changes: 4 configurations set a retain
   duration (`l3-*`), and 8 do not.
5. **The setter** (question 5):
   * `Db.setRetainDuration`, and `Reclaim.setRetainDuration` (a volatile
     field, no lock, no record);
   * `DatabaseImp.setRetainDuration`, and JMX's three setters;
   * the claim in `Database.setRetainDuration`'s Javadoc, "This method can
     be called before start() or while the database is running", while a
     `Database` exists only after its start.
6. **Survives the cuts** (question 6, for B):
   * `Reclaim.step`'s scan: `db.getMany` from `lastKey` at `tStart`.
     Does it reach the keys under `DbConstants.INTERNAL_PREFIX` (`/#i/`),
     and so rewrite a live internal value stored before pCut?
   * `pretruncate`: what a cut does to a value that no step rewrote.
   * How `-table.txt` and `-current.txt` survive today: they are stored
     again at each iteration's start and step.
   * The probe's P3 checks it.
7. **The restart test** (question 7): the test that fails today, written
   out for U6. It goes in `DbTesterRestart`, beside
   `dbShouldRememberStartupDistance1` and `2`: the value set once, and a
   restart right after the call and every k commits, without setting it
   again, giving the stream of the run without restarts.
8. **Replicas** (question 8): `Database.addReplica`'s byte copy, and what
   a replica started as a database reads in each form. Read only; no
   fault of 005-11 is looked for (016-01, section 3).
9. **The other settings** (question 9):
   * The internal fraction is set by `Db` and JMX, and by ReclaimCost's
     property; it changes the bytes whenever it is set.
   * The step reserve is set by `DbBuilder.reclaimStepReserve` and the
     system property `stepreserve`, for the stress programs. Does it
     change the bytes at its default of 4 MiB? Probe P4 shows it.
10. **Lean and the traces** (question 10):
    * `TraceExport`'s `kind=`, from `Trans.isInternal` and `touch`;
    * the trace checker, which treats every `TX` alike;
    * A's meta blocks, which are not modelled.

    Confirmed by reading. A trace with the setting's record is made only
    by U6.

### 3. The probe (U2)

* **The file**: `78-retain-duration-in-stream/RetainProbe.java`, in the
  package `bergdb.core`. It is StreamDigest's code, copied with its four
  `l3-*` workloads draw for draw, and the modes below. It runs against the
  clone's jar, built from the base: `java/build.sh`, then the probe before
  `build/bergdb.jar` on `-cp`. Its header gives the commands, as 007-07's
  probes do.
* **The modes**, each on the four configurations:

  | Mode | The retain duration | Restarts |
  |---|---|---|
  | plain | set at the start | none |
  | restarts-each | set after each start (StreamDigest's restarts) | every `every` |
  | restarts-once | set at the first start only | every `every` |
  | restarts-50 | set at the first start only | every 50 commits |
  | after-call | set at commit 100, not at a start | right after the call, then every 50 |

* **What each run prints** (into `probe.txt`):
  * the length, `sha256` from the decided cut, and the first available
    position and time;
  * the records by kind (user, table store, step), counted by walking
    the final stream's records from its first position, and the
    iterations summed over the starts;
  * the first byte where the stream differs from plain's, with the
    record there: its index, time and kind.
* **What it must show** (the check of U2):
  * restarts-each gives plain's stream;
  * restarts-once, restarts-50 and after-call do not;
  * the first difference is the first iteration that does not start
    after a restart, and from there no iteration starts and no cut is
    made.

  If restarts-each differs from plain, that is another fault: the agent
  stops the probe, and reports it.
* **P3, question 6.** In `l3-node8`'s workload, a KV under B's key
  (`/#i/dreclaim/-probe`, if a transaction may write there; otherwise the
  path that `storeTable` uses) is set once, before the first iteration.
  * After three cuts or more, `getOne` at `Long.MAX_VALUE` must still
    find it, also after a restart from the cut stream.
  * It prints the value's position against the cut: rewritten by a step,
    or not.
* **P4, question 9.** `Reclaim`'s `splitSteps` (with `enableStats`) on
  the four workloads, with the default step reserve and with the stress
  programs' smallest: 0 at the default means that the reserve changes the
  bytes only below it.
* **P5, the costs for the design's table.**
  * A: the bytes of one call made as `setStartupDistance` makes its own,
    at least 200 kB, measured as a length.
  * B: one internal transaction with a value of about 30 bytes.
  * C: the table's text with the new field, at each store.
* No file in `java/` changes, and nothing is handed to the coordinator
  but this entry's files.

### 4. The design for Frans (U3)

* **The file**: `78-retain-duration-in-stream/design.md`, linked from
  this entry. At most about four pages.
* **The test of the design**: Frans can choose in one reading, or answer
  "as recommended".
* **Its contents, in this order**:
  1. **Summary**, five to eight lines:
     * the fault in one sentence, with the probe's numbers (for example,
       how much longer `l3-node8`'s stream is after a restart that does
       not set the value again, and that no cut is made after it);
     * what Frans decides;
     * the recommendation in one line.
  2. **For Frans to decide**, F1 to F7. Each has the question in one line;
     each option in full (what is written, when, by whom, what a start
     does, the cost, how it is checked); the recommendation and why; and
     what follows from it.
     * F1, the form: A, B or C. This is the approval of a format change
       (016-01, section 3).
     * F2, the builder against the stream, for an existing database: the
       builder's value ignored, as the startup distance's; or written at
       the start when it is given and differs.
     * F3, unset against forever, in `DbBuilder` and in the Pub
       builder's Javadoc.
     * F4, a stream without a value: the builder's value, and written at
       the first start, or at the first call.
     * F5, forever's encoding: whether a new database writes it (all 36
       StreamDigest streams change) or nothing (the 8 without a retain
       duration stay).
     * F6, the setter: a commit under the write lock, refused when the
       database is not active, and nothing written when the value is in
       force; and `Database.setRetainDuration`'s Javadoc corrected.
     * F7, question 9:
       * the internal fraction (units of 2^-16, 005-79): kept in the
         stream with the retain duration, documented as lasting for the
         run, or its setters removed from `Db` and JMX;
       * the step reserve: documented as a setting for tests, or kept.
  3. **The three forms side by side**, one row per point and the same
     points for each:
     * what a call writes, and its bytes;
     * what a start reads, and where in the code;
     * a new database's stream, and StreamDigest's configurations that
       change;
     * whether the value survives cuts;
     * a replica;
     * what 2026.1 does with such a stream;
     * which part of the format changes (016-01, section 3's list);
     * the code to change: the files, and about how many lines;
     * the C clone's work later;
     * Lean and the traces;
     * the risks.

     As a table if it fits AGENTS.md's widths, else as three lists in the
     same order.
  4. **The evidence**: the probe's table, by mode and configuration, and
     the study's answers to questions 1 to 10, with their code.
  5. **The change after the choice**, by form:
     * the files;
     * the tests:
       * question 7's restart test, shown to fail on the base and to pass
         after;
       * a refused call changes nothing;
       * a call with the value in force writes nothing;
       * a stream without the value starts with the builder's;
     * StreamDigest's fourth mode, `restarts-once`, which must give
       plain's stream;
     * a configuration of level3.sh's RestartInvariance with the value set
       once;
     * the gates and the size.
  6. **The release.**
     * 2026.2 ships with the known issue of U5, unless Frans decides
       otherwise.
     * What the choice costs afterwards: the change, about 1.5 days of an
       agent's time with the tests, in the next release; the bytes of
       databases that reclaim change once; and C follows later.
  7. **Not decided here**: replication (005-11), the C clone (U7), and
     014-01.
* **Done** when the coordinator has checked two things:
  * every F has its options and a recommendation;
  * each option says what is written, when, by whom, and how it is
    checked.

### 5. The stop, and the release without a choice (U4, U5)

**U4.** The coordinator posts `tools/news.sh "needs a look" 005-78 "the
design is ready for Frans's choice, F1 to F7"`, and adds a line to
016-02's "For Frans to decide". The other work goes on.

**U5, the known issue of 2026.2**, if Frans has not chosen before the
release.

* The notes, under "Known issues and limits". The agent drafts this text
  in the design's section 6, and the coordinator or W1's agent puts it in
  `releases/next.md`:

  > **The retain duration is not kept in the stream** (bergdb 005-78). A
  > start takes the builder's retain duration, which is forever by
  > default. An application that sets the duration after the start, or
  > opens the database without it, gets after a restart a reclaim with
  > another value, or none, and other bytes in the stream than without the
  > restart (010-01, P2). Set the retain duration at every start, with
  > `DatabaseBuilder.retainDuration`, or with
  > `Database.setRetainDuration` right after `start()`.

* The Javadoc, recommended, as users read it rather than the notes:
  * `DatabaseBuilder.retainDuration` and `Database.setRetainDuration`
    each get a sentence: the value is not kept in the stream, so set it
    at every start (bergdb 005-78);
  * `Database.setRetainDuration`'s "can be called before start()" is
    corrected, as a `Database` exists only after its start.
* Files: `java/src/bergdb/pub/DatabaseBuilder.java` and `Database.java`,
  Javadoc only.
* Gate: `java/before-commit.sh`. It is handed to the coordinator by 00:30,
  and reviewed with the others (H5).
* If it is late, the notes alone carry the known issue.

### 6. The change, after Frans's choice (U6)

After the release, by "Done when" and the design's section 5. An outline
for the plan of that day:

* **The code**, by form:
  * A: `MetaBlock` (a field at offset 46), `Db.handleStartParams`,
    `Db.setRetainDuration` as `setStartupDistance`;
  * B: `Reclaim.initFromDb` reads the KV, `Db.setRetainDuration` commits
    it;
  * C: `Reclaim`'s table, its parse, and `storeTable` at the setter.

  In all three, the setter is a commit under the write lock (F6), and the
  start puts the value in force before the first transaction after it.
  `Reclaim.initFromDb` runs after `startDb` and before `start()` returns,
  as the study confirms.
* **The API**: `DatabaseBuilder.retainDuration` and
  `Database.setRetainDuration`, with Javadoc that says that the value is
  kept in the stream, as `setStartupDistanceInMb`'s does; and JMX.
* **The tests** of the design's section 5.
* **StreamDigest**: the 8 configurations without a retain duration
  identical (or the change of all 36 explained, F5). The 4 with one
  changed, with plain, reads, restarts and restarts-once agreeing in
  each.
* **The gates**: `java/before-commit.sh`, `java/stress/level3.sh`
  (reclaim) and `level2.sh` (restart invariance).
* **The words**: `releases/next.md` (an API change: the retain duration
  is kept); 010-01's P2, where the retain duration is now checked; and
  docs/levels.md, section 5.
* Size: about 1.5 days.

### 7. The C clone follows (U7, after 2026.2)

* `bergdb.h` has `retain_duration` and `bergdb_set_retain_duration`.
* The chosen form goes into C as well:
  * A, the meta block's field;
  * B, the KV, read at the start;
  * C, the table's parser.
* `cross.sh full C=build/release` passes on workloads that set the
  value once.
* Until then, Java and C differ on the streams of restarts without the
  setting.
* A 015 entry, registered by the coordinator with 005-79's step 9.

### 8. State

* **2026-11-03:** this plan; nothing run (the night went to the release).
* **2026-11-05, U0 (07:20):** the clone `/Users/f/fl/bench/016/005-78`, at
  `0c6c4be` (`main`); `java/build.sh` there at 07:20 (5 s). The base of
  all answers and runs is `0c6c4be`.
* **U2, first run (07:22):** `RetainProbe.java` (in this entry's directory)
  compiled against the clone's jar and run on the four `l3-*` workloads,
  5 s. restarts-each gives plain's stream (the same length and sha256
  from the cut in all four); restarts-once, restarts-50 and after-call do
  not: after the first restart no iteration starts and no cut is made
  (`l3-node8`: 1 iteration and 0 cuts against 24 and 22; 4,355,752 bytes
  kept against 2,094,096). P3: both internal KVs found after 21 to 26
  cuts and after a restart on the cut stream. P4: no split step at the
  default reserve. P5: A 204 to 227 kB a call, B 160 to 176 bytes. That
  run's first-difference column was wrong (it compared bytes from the
  larger first position, past the divergence); fixed at 07:24 to compare
  the stream lengths after each commit. QUIET-BLOCK from 07:23: no run
  until it is gone.
* **U1 and U3 (07:24 to 07:30):** the study's answers (questions 1 to 10,
  with the code) and the design, in `design.md`: F1 to F7, the forms side
  by side, the evidence, the change, the release.
* **Next:** the probe again after the quiet block (the fixed comparison,
  and P4 with `-Dstepreserve=2000`); its table into `design.md`, section
  4.1 (the line `PROBE-TABLE`), and `probe.txt`; then U4, the stop
  (the coordinator's).
* **For the agent:**
  * A probe in `bergdb.core` goes before `build/bergdb.jar` on `-cp`;
    the probe's header gives the commands.
  * Every database the probe starts is stopped. Restart on
    `MemoryStream.copy()`, as StreamDigest does: a closed `MemoryStream`
    refuses appends.
  * Record the outcome of each step here, with the times, so that a fresh
    agent can resume.

Log
---

2026-10-29. Registered, as Frans decided at 10:09 (above).

2026-11-03.
* In 2026.2's scope (016-01, section 4.1, item 3).
* The plan for 2026.2 added: the study, the probe and the design tonight,
  a stop for Frans; 2026.2 ships it as a known issue unless he chooses
  first.
* Frans's changes of 15:31 (Java only) and 15:40 (tonight) are in
  "Decisions of 2026-11-03".

2026-11-05.
* U1 to U3 done on `0c6c4be` (section 8, State): the study, the probe,
  the design (`design.md`). The probe confirms the fault: a restart that
  does not set the retain duration again stops reclaim for good.


For Frans
---------

The design, `design.md`, sets out each choice in full; "as recommended"
answers all seven.

* **F1, the form** (the approval of a format change, 016-01, section 3):
  A, the meta blocks; B, an internal KV `/#i/dreclaim/-settings.txt`; or
  C, reclaim's table. Recommended: B.
* **F2, the builder against a stream with a value:** the stream's value
  wins, as the startup distance's (recommended), or the builder's written
  at the start when it differs.
* **F3, unset against forever in `DbBuilder`:** not needed with F2's
  recommendation (recommended), or a distinct unset value.
* **F4, a stream without a value** (2026.2's, and new databases): the
  builder's value, written at that start if finite (recommended), or
  written only at the first call.
* **F5, forever:** writes nothing, so StreamDigest's 8 configurations
  without a retain duration keep their streams (recommended), or every
  new database writes its value.
* **F6, the setter:** a commit under the write lock, refused when the
  database is not active, nothing written when the value is in force; the
  Javadoc's "before start()" removed. Recommended as stated.
* **F7, the internal fraction and the step reserve:** the fraction kept in
  the same record (recommended with B), documented as lasting for the run,
  or its setters removed; the step reserve documented as a setting for
  tests (recommended).
