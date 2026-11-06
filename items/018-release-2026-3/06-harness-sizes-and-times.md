018-06. Harness 6.4: sizes and times at their limits
====================================================

Created 2026-11-06 by Frans Lundberg, as harness 6.4 of 018-01 (W2), in
the night 006-12 (Frans, 2026-11-05, 21:33: "Will you fix all bugs?
[...]"). Built by Claude (Opus 5.5, Claude Code), a harness agent of that
night.

**Status: built; runs in `before-commit.sh`'s unit tests (2 s) and
in `night.sh`'s night tests (97 s).** It fails on each of the three
known faults of its class (018-01, section 6.4) on the code before its fix,
and passes on `main`. It found no new fault in 584 runs.


## 1. What it checks, and why

The Core Layer has limits that a transaction meets: the value limit
(`StoredTrans.valueLimit()`, 7/8 of the record limit), the bound of the
index nodes one transaction may make dirty (`Db.checkDirtyNodes`), the
range of database times (`Klong.MAX_TIME`) with the times kept for
reclaim's internal transactions (`DbClock.LAST_USER_TIME`, 015-55), the
top node ordinals with their margin (`Db.LAST_TOP_ORDINAL`, 005-02), and
the settings' ranges (`setStartupDistance`, `setRetainDuration`,
`setReclaimInternalFraction`, `setCacheSizeIndicator`, the builder's
startup distance). The three known faults of the class each passed one
of them in a way that failed the database or broke a promise:

* 015-50: a reclaim step rewrote old values that were each within the
  value limit, but not together; the step's internal transaction was
  refused inside a user transaction's go point, and the database failed,
  and again at every restart.
* 015-55: a user transaction at the last database time was taken, and
  the reclaim step after it found no time left.
* 015-76: `setStartupDistance` clamps its value, which its Javadoc did not
  say; it promised that a call with the setting in force writes nothing,
  which did not hold below the clamp.

The promise the harness holds the Core Layer to (018-01, section 6.4):

* Each transaction is either refused before its go point, with a
  `DbException` (not a `DbFailedException`) for a reason the Javadoc
  gives, and the database goes on with nothing of the transaction
  written; or it is committed, and every value it wrote reads back. The
  reasons, each checked against the transaction and the clock: its
  values and keys above the value limit (`Db.checkSize`); its index nodes
  (`Db.checkDirtyNodes`); the clock out of range; no time left, only when
  the clock, a read or the last user transaction is within 4,096 units of
  `LAST_USER_TIME`; the top node ordinals used, only in a run that starts
  near their end. Where several hold, any of them may be the one given:
  `Db` checks the size first, then the ordinals, the index nodes and the
  time.
* A transaction within the value limit is not refused for its size, and
  one above it is never taken; no user transaction is taken after
  `LAST_USER_TIME`, and transaction times increase.
* The database never fails. After a restart it holds every committed
  value and the settings in force (startup distance, retain duration,
  internal fraction), and it takes commits.
* Each setter at and beyond its bounds does what its Javadoc says: the
  value set, a refusal with `IllegalArgumentException` that changes
  nothing, and for `setStartupDistance` the clamp to 400,000 to 10^9
  bytes, with a write exactly when the clamped value is not in force.

The exception (018-01, section 6.4; 015-51, Frans, 2026-11-05, 21:03): a
value transformation's result above the value limit is the caller's
fault. The harness makes one in a quarter of its runs, at a random step
of the second half: either its record fits the record limit and it is
committed (then any later failure of the database is the caller's fault
too), or the database fails (P7). Then the transaction must not be in the
stream: a restart on a copy of the stream has the value before it and
takes a commit. The run ends there, and is counted as ended by the
caller's fault, not as a failure.


## 2. How it works

One test class, `bergdb.core.LimitsTester`, registered in the package's
`Pack`; test code only, nothing in the production code. It works on the
Core Layer (`Db`), as the limits are there; the Pub API's own clamps
(cache 4 MB, startup distance 5 to 1000 MB) are 6.7's.

* `run(seed, steps)` starts a database on a `CutStream` with a clock the
  test sets (it can go back, as `CoreTestClock` cannot), and makes
  `steps` random steps from a `Random` seeded by the seed, mixed
  (`SplittableRandom(seed).nextLong()`: `Random`'s first values for
  adjacent seeds are alike, and the night's seeds are adjacent; unmixed,
  160 adjacent seeds made no run near the end of the ordinals). The clock
  moves 1/40 to 3/40 of a second a step.
* The record limit is lowered, as `StoredTrans`'s and `Reclaim`'s own
  tests do, to 240 kB, 300 kB or 1 MB per run, so that a value at the
  value limit is 210 kB to 875 kB. 240 kB is the least that leaves room
  for `setStartupDistance`'s 200 kB value.
* Each run chooses, from its seed: the record limit; the node size (8 in
  a third of the runs, the default else); the builder's startup distance
  (10, its least, 2,000, 400,000 or 2,000,000); the cache size indicator
  (none evicted, 1, 300 kB or 3 MB; the capacity controller), or, in a
  fifth of the runs, the random eviction schedule; a retain duration of
  one second (reclaim on) in three runs of four; in a third of the runs,
  a step from which the clock is at the last user times (the end phase);
  in an eighth, the second top node's ordinal near the end of the
  ordinals (`DbBuilder.secondTopOrdinal`, 1 to 3 before
  `Db.LAST_TOP_ORDINAL`; a new super root comes only when the tree grows
  a level, about ten times in 1,500 steps, so the end comes within the
  run);
  in a quarter, the step of the caller's fault.
* The steps, by weight: small puts of 1 to 3 keys (35 %, and 12 % more
  with a read of a random key); one value whose node takes the value
  limit, 0, 1, 3, 4, 5, 100 or up to 100,000 bytes less, or in a quarter
  of them more, sometimes under a long key (12 %); 2 to 6 values that take
  the limit together, or a little more (7 %); deletes (7 %); a value
  transformation that grows its input to a value of 100 to 5,100 bytes or
  up to the value limit, made of its input and the previous value (9 %);
  keys of 20 to 3,000 bytes (to 429 segments), alone or up to six, or,
  one time in three, 50 to 1,549 small KVs in one transaction, at the
  bound of its index nodes (5 %); the clock back by up to a second, or
  out of range (-1, `Long.MIN_VALUE`, above `Klong.MAX_TIME`) for one
  transaction (4 %); a
  setter at and beyond its bounds (7 %); a restart (2 %): `close()`, and
  a start on a copy of the stream. In the end phase the clock goes to
  `LAST_USER_TIME` - 2,000 to `Klong.MAX_TIME` and moves 0 to 2 units a
  step.
* The reference is each key's last value. After each transaction its
  keys are read back; after each restart, and at the end of the run, all.
  At the end of a run that the caller's fault did not end: a restart, and
  a put.
* Each step is logged; a failure throws an `AssertionError` with the seed,
  the step, what differed, the cause, and the last 30 steps
  (`-Dbergdb.limits.lines=N` for more). `main(seed, steps, runs)` repeats
  runs and prints a summary: the commits, the refusals by reason, the
  settings calls, restarts, reclaim's cuts and iterations, and the runs
  that the caller's fault ended (`-Dbergdb.limits.verbose=true` prints
  each run's).
* `SKIP`, as 6.3's and 6.7's: a known fault that is not fixed is listed
  and stepped around. It is empty: the harness found no fault that is not
  fixed. `-Dbergdb.limits.skip=none` skips nothing.

Adapted from 018-01's proposal, and why:

* Lookups at old times and `LookupTimeNotAvailableException` are not
  checked, only the last values: the lookup promises are 6.7's.
* The record limit is lowered, which the proposal did not say: values at
  the real limit, about 1.88 GB, cannot be made in a test. The limits are
  all derived from `StoredTrans.recordLimit`, as the code derives them.
* The settings: the proposal's "settings at their bounds" are the four
  setters above, the builder's startup distance (9 refused, 10 taken),
  the cache size indicator of 1, and the node size 8; the startup
  distance's range is 015-76's.


## 3. Where it runs, and its cost

* **Unit tests** (Nano group "unit"): `testSeeds`, seeds 1 to 3, 100
  steps each; 2 s (6.5 s with 150 steps, which were cut).
  `before-commit.sh` runs the unit tests beside the f-tests, which take
  the longest, so it adds nothing measurable to its time.
* **Night tests** (`testSeedsLong`, Nano group "night", run by
  `night.sh`'s step night-tests): 20 seeds of 500 steps, 97 s on
  F53. Its seeds are new each day, the day's number times 1000 and the 19
  after it, printed first, so that a failure can be repeated. A step at
  the limit writes up to 875 kB, and a restart copies the stream and
  starts on it, so a step takes about 5 ms.

From `java/`:

```sh
./unit.sh -c LimitsTester                           # the unit tests
./night.sh tests -c LimitsTester                    # the night's seeds
java -ea -cp build/bergdb.jar bergdb.core.LimitsTester SEED STEPS RUNS
```


## 4. The skip list

```java
static final String[] SKIP = {
};
```

Empty: no fault that the harness finds is open.


## 5. The evidence

The known faults were fixed on 2026-11-05: 015-50 in bb3be64, 015-55 in
f679430, 015-76 in f5e73ea (the Javadoc only). On this branch, built on
`main` (8e2453e) with the harness, each fix's main hunk was reverted alone,
in classes compiled before the jar on the class path, and
`LimitsTester 1 500 40` run (seeds 1 to 40, 500 steps each):

* 015-50, `Reclaim.step`'s bound of the value nodes it rewrites and
  `Db.executeInner`'s exemption of internal transactions from
  `checkSize` reverted: seed 1, step 73, `put many at the limit: the
  database failed`, caused by `The transaction is too large: its values
  and keys take 262552 bytes in the stream, more than 262500.` (the
  step's internal transaction, refused inside the user transaction's go
  point, as the entry says).
* 015-55, `DbClock.transactionBegin`'s refusal of a user transaction after
  `LAST_USER_TIME` reverted: seed 1, step 455, `put at the limit: taken
  at 72057594037926914, after the last user time`. With that check of the
  harness taken out too, so that it runs to the fault itself: seed 40,
  step 451, `transform: the database failed`, caused by `No
  database time is left after 72057594037927935; the largest is
  72057594037927935.` (reclaim's step after a user transaction at the
  last time, R7-F6).
* 015-76: its fix changed only the Javadoc, so no code is reverted. With
  the old Javadoc's promise as the oracle (the value given is set, and a
  call with the setting in force writes nothing; no clamp): seed 1, step
  21, `setStartupDistance(10): expected the setting 10, got 400000`,
  R6-F5's observation (on a database built with 10). With the Javadoc of
  today it passes.

On `main`, with nothing skipped (the skip list is empty), all pass: 160
seeds of 500 steps (3000 to 3159; 4 JVMs, 217 s), 62,000 commits, 3,100
refusals for the size, 890 for the index nodes, 1,640 for the time, 400
for the top node ordinals and 2,300 for the clock, 5,400 settings calls,
1,620 restarts, 290 cuts and 540 reclaim iterations; 24 runs ended by the
caller's fault, each with a transformation's record that did not fit the
record limit, and a restart that had the value before it and took a
commit. Before the seeds were mixed (section 2), 160 more of 1,000 steps
(1000 to 1159) and 160 of 500 (3000 to 3159) passed too; after, 80 of
1,500 steps (5000 to 5079, 4 JVMs, 710 s). With the ordinals at their
final distance, 1 to 3 before the end (section 2): 24 seeds of 500 steps
(6000 to 6023), with 409 refusals for the ordinals, pass. 584 runs in
all.

The harness found no new fault. While it was built, three of its own
oracles were wrong and were fixed, not the code: a read at the clock's
time takes that time too, so "no time left" may come before a user
transaction reaches the end (the harness now counts the largest clock
time the database has seen); `Db` checks the top node ordinals before
the clock, so either refusal may come for a transaction where both hold;
and a new super root comes only when the tree grows a level (first set
3 to 3,100, then 3 to 82 ordinals before the end, the runs reached the
end too rarely: in 80 runs of 1,500 steps with 9 such runs, never).


## 6. What it does not cover

* Lookups at earlier times, and their availability with a finite retain
  duration: 6.7 checks lookups with the duration forever.
* A crash: each restart closes the database first. Truncated and damaged
  streams are 6.1's; failures of the stream, 6.2's.
* `FileStream` and the file-size limit (`setMax2G`): the stream contract,
  6.3's.
* The real record limit, about 2 GB: only lowered limits; the arithmetic
  is the same, as every bound derives from `StoredTrans.recordLimit`.
  `Reclaim.setStepReserve` is not lowered with it.
* Key transformations (`KeyTransformation`): only the Pub API's key
  replace uses one, and 6.7 checks it.
* Several threads: one thread makes every call (eviction's and the
  storage's own threads run as always). Concurrency is 6.6's.
* The Pub API's limits: 6.7 runs it at its smallest startup distance and
  cache.


## 7. State (night 006-12)

Clone `/Users/f/fl/bench/006-12/h64`, branch `h64`. Done: the harness,
this item, its lines in 018's readme and 018-01 (section 6.4 and the log),
one commit (BEFORE COMMIT OK). No new fault, so no 019 entry; 019-25 to
019-29 are not used. Next, if the harness is extended: crash restarts
(a copy of the stream without `close()`), lookups at old times with the
retain duration of one second, and a run at the real record limit on a
machine with the memory for it.


## 8. Log

2026-11-06, night 006-12. Built (W2 of 018-01, harness 6.4):
`LimitsTester`. It fails on 015-50 and 015-55, each with its fix
reverted, and on 015-76 with the old Javadoc's promise as its oracle; no
new fault in 584 runs. In the unit tests (2 s) and the night tests
(97 s).
