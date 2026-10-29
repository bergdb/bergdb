005-78. Investigate: the retain duration is not kept in the stream
=================================================================

Status: open. Kind: investigate. Created 2026-10-29.

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
