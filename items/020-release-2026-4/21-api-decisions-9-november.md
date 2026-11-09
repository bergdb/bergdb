# 020-21 Frans's API decisions of 9 November, implemented

Created 2026-11-09 by Frans Lundberg. Status: open.

The decisions that Frans took at 10:30 on 2026-11-09 on findings of the test study (020-13,
section 4) and the Javadoc hunt (020-19, Q1, Q2 and section 6), implemented in the code, the
Javadoc and the release notes, each with a test that failed first.


## 1. The request

Frans, 2026-11-09, 10:30: "1 to 5, all as recommended". The coordinator (coord-1109) gave
this item four parts, at 10:31:

1. `Time` parses strictly: `Time.utc()`, `resolve()` and their kin refuse fields out of
   range with the BadFormatException that the Javadoc promises, instead of rolling over
   (020-13, section 4.2, option (a); 020-19, Q1).
2. `WBuilder.execute()` spends the builder (020-19, Q2).
3. The small API faults: `setRetainDuration(null)`, `useIndex(name, String.class)`,
   `Job.join(millis)` with a negative time, `CryptoKey.NULL`'s round trip, and the rest of
   020-19's section 6 and 020-13's six Javadoc gaps (section 4.2).
4. The gate's StoppedCheck also checks the IndexBuild-* and IndexCleanup-* threads (020-13,
   section 6, recommendation 3).

Each a commit of its own, a failing test first, gated; each change of behaviour a line in
`releases/next.md`; the Javadoc through `java/javadoc-pub.sh`. A finding that needs a
decision beyond "as recommended": the safe part done, the question here.


## 2. The method

* Clone `/Users/f/fl/bench/2026-11-09/clone-a21`, on the integration clone's tip
  (`clone-int`, `80fa169`: `main` at `86dade8` and 020-19's 16 commits), as 020-19's J7 and
  J8 changed the Javadoc of `Time` and `WBuilder` that this item changes again.
* Gates in clones of their own (`/Users/f/fl/bench/2026-11-09/a21-gate`, `a21-gate2`,
  `a21-gate3`), so that the work went on meanwhile, under the shared lock (`lockf
  /Users/f/fl/bench/006-15/gate.lock`); outputs in `/Users/f/fl/bench/2026-11-09/a21-gate*.txt`.
  The messages' "BEFORE COMMIT OK" were written after the gates, by rebuilding the four
  commits on `80fa169` (the same trees, and a Javadoc line of 106 chars in `Time` broken in
  the first).


## 3. The changes

Commits in the clone, in order, on `80fa169`; each with its test, which failed before the
change, and a line in `releases/next.md`. Gates: section 5.

### 3.1. A time string is parsed strictly (1)

* Before: `TimeResolver` set a lenient `GregorianCalendar` from fields read with
  `Integer.parseInt` and `Double.parseDouble`, so it rolled a field over ("2013-13-01" was
  2014-01-01, "2013-02-30" 2013-03-02, "2013-00-10" 2012-12-10, "25:00" the next day,
  "00:00:75" 00:01:15; `parseDate`: "Let's allowed "overflow" for now", 2013) and took
  numbers that are not the format's ("00:00:1e1", "00:00:0x1p3", a trailing space after the
  seconds, "2013-+1-01", non-ASCII digits, a minus time "-1d s", "-NaN s", "-0x1p3 s").
* Now: each field is ASCII digits of its length, in its range (month 01 to 12, the day
  within its month by `YearMonth`, hour 00 to 23, minute and second 00 to 59); a fraction is
  one digit or more, rounded half up on its digits to 100 ns; a minus time's number is digits
  with an optional fraction, then exactly one space, a unit, and optionally one space and a
  time of day. Anything else is a `BadFormatException`.
* A time outside `Time`'s range is a `BadFormatException` too, as 020-13's option (a) says
  and as a minus time before 1970 already was: an absolute time or a time of day outside the
  range gave `IllegalArgumentException` from `Time.units()` (020-19, J7 had documented that,
  section 6 noted the mismatch). `Time.units()`, `millis()` and `add()` keep
  `IllegalArgumentException`: they take no string.
* Javadoc: `Time.resolve`'s ABNF gives every field with its range, and a paragraph says that
  the parse is strict; `utc()` and both `resolve()` list `BadFormatException` for a field out
  of range and a time out of range, `IllegalArgumentException` for nulls only.
  `TimeResolver`'s copy of the grammar is gone; it points to `Time`.
* Callers checked: only `Time` uses `TimeResolver`; the other uses of `Time.utc()` and
  `resolve()` in BergDB are tests with valid strings (`PubTester`); no demo, tool or
  document uses a time string.
* Tests: `Time.testStrictTimeStrings`, new: 64 strings refused by each of `resolve(zone,
  now, s)`, `utc(s)` and `resolve(zone, s)`, a time zone that puts 1970-01-01 00:59 before
  1970, and the edges taken (1970-01-01, `Time.MAX`'s string, 29 February 2000 and 2012,
  rounding half up into the next day); before: "'2013-00' not refused".
  `TimeResolver.testBadSeconds`, which kept the roll-over ("00:00:75" equal to "00:01:15"),
  now refuses it. `PubTesterJavadoc.testTimeStrings` expects `BadFormatException` for a
  time out of range. 020-13's `TimeProbe`: 200,000 random times equal to `java.time`'s and
  100,000 round trips of `toUtcString()`, no difference.
* Commit `c4c96ce`.

### 3.2. WBuilder.execute() spends the builder (2)

* Before: a second `execute()` ran the same writes again as a new transaction (writing back
  a value that another transaction had changed since), and a `put()` after `execute()` added
  to the writes, which the next `execute()` wrote with the old ones.
* Now: `execute()` sets a flag first, so the builder is spent also when it throws, as
  `IndexBuilder` is after `start()`; `put()`, `delete()` and `execute()` then throw
  `IllegalStateException`. Javadoc: `WBuilder`'s class comment (get one with
  `Connection.w()`, execute it once), each method's `@throws`, and `Connection.w()`.
* Every `WBuilder` in BergDB (testers, `IndexHarness`, `PrimaryHarness`,
  `IndexJobsHarness`, `PubPromiseTester`, `PayDemo`) executes each builder once.
* Test: `PubTesterJavadoc.testWBuilderSpentByExecute` (before: "execute() again:
  IllegalStateException expected, none").
* Commit `f15b5e8`.

### 3.3. The small API faults (3)

Code:

* `Database.setRetainDuration(null)`: `IllegalArgumentException`, also after `stop()`, the
  value unchanged; it was a `NullPointerException`. Test:
  `PubTesterJavadoc.testSetRetainDurationNull`.
* `Connection.useIndex(name, String.class)`: refused at the call with
  `IllegalArgumentException`, whatever the data and whether the index exists; it was taken,
  and every `next()` threw `DataFormatException`. `IllegalArgumentException` rather than
  `ObjectCreationException`, which the Javadoc keeps for a type that no get takes: a get
  takes `String`, but an index's values are objects. Test:
  `PubTesterJavadoc.testUseIndexOfStringRefused`, which also scans with `Account`,
  `DbObject`, `Object` and `byte[]`.
* `Job.join(millis)` with a negative time: `IllegalArgumentException`, as
  `Thread.join(millis)`, while the build runs and after it ended; it returned at once. Test:
  `PubTesterJavadoc.testJoinNegativeRefused`.
* `CryptoKey.NULL`: `parse(NULL.serialize())`, of "null-null-", gives `NULL`; it threw
  `FormatException` ("too few parts (2)"). `parse(null)`: `IllegalArgumentException`, not
  `NullPointerException`. Test: `CryptoKey.testNullRoundTrip`. (020-19's other CryptoKey
  note, `getKeyData()` giving the key's own array, was fixed before, 020-20's N1.)
* `DbObject.toDbObject(byte[])` is refused as before, but its message now says why ("a put
  stores it as it is, its bytes"); it gave the class check's "a primitive or an array is
  not a class of fields", though other arrays are taken (`DataObjects.toDbObject`).

Javadoc, each a corner that 020-13 (section 4.2) or 020-19 (section 6) found unsaid:

* `Connection.useIndex`: `LookupTimeNotAvailableException` for a lookup time behind the cut,
  and `IllegalArgumentException` for `String.class`.
* `Job.join()` and `join(millis)`: BUILDING after a failure of the database, as after a stop
  (a `DbFailedException` is an `IllegalDbStateException`, which ends the build's thread
  BUILDING); `join(millis)`'s `IllegalArgumentException`.
* `Duration.seconds()`: rounds to clock units; MAX above it, positive infinity included; 0
  for NaN; `IllegalArgumentException` for a negative result. Since Q1's decision (section
  4), NaN is refused instead.
* `Connection.delete()` of a key without an entry: nothing is deleted, but the delete
  commits a transaction of its own, with a time of its own.
* `DbObject.toDbObject()`: a `String` is wrapped in "p", as a wrapper is; a `byte[]` is
  refused. `toJavaObject()`: `String` reads "p"; `byte[].class` reads "array", as an array of
  integers, not a byte string in "p".
* `DatabaseBuilder.start()` of a `memory()` builder whose database has closed: it starts on
  the closed stream, reads the data, and its first write to the stream fails it
  (`DbFailedException`); probed, as 020-13 found it.
* `Database.setRetainDuration()`'s null, `CryptoKey.parse()` and `NULL`, and
  `freezeLookupTime()`'s line of 154 chars, broken.
* Test of the corners: `PubTesterJavadoc.testJavadocCorners` (its `byte[]` message failed
  before).
* Commit `f370bef`.

### 3.4. The gate finds the index threads (4)

* `NanotestForBergDB.StoppedCheck` (005-55) counted the storage threads and the eviction
  thread only; it now counts `IndexBuild-*` and `IndexCleanup-*` too (`databaseThreads()`),
  and its message names them. The unit and f groups leave none.
* Test: `NanotestForBergDB.testIndexThreadsChecked`, two threads of those names waiting on a
  latch must be found (before: "IndexBuild-t-1 not found"); `bergdb.dev.Pack` lists the
  class for it.
* Commit `cce0ff4`.


## 4. For Frans

* **Q1. `Duration.seconds(NaN)`.** It gives a duration of 0, which the Javadoc now says, as
  020-13 recommended ("a line"). A NaN that means nothing then means "no time", as a time
  string that meant nothing meant a time before decision 1. Recommendation: refuse NaN with
  `IllegalArgumentException`, as a negative duration is refused; one line in
  `Duration.seconds()`, and the Javadoc's "0 for NaN" changed.

  **Decided** by Frans, 2026-11-09, 11:23: "Yes, as recommended." Done in `e5b6de8`, on
  `cce0ff4`: `Duration.seconds(NaN)` throws `IllegalArgumentException` (`Double.isNaN`
  before the rounding), with its `@throws` and a line in `releases/next.md`; the
  Documentation line of 3 no longer says "0 for NaN". Siblings, the API's other methods
  that take a double: `DbDouble` is a value, which keeps Binson's one NaN (020-07), and
  `UseIndexBuilder`'s `eq()`, `from()` and `to()` refuse NaN already; no caller in BergDB
  passes a computed double to `Duration.seconds()`. Test: `PubTesterJavadoc.testJavadocCorners`
  refuses NaN, -NaN and negative infinity; before: "seconds(NaN): IllegalArgumentException
  expected, none".
* **Decided under "as recommended"**, to check: a time outside `Time`'s range from a time
  string is a `BadFormatException`, not an `IllegalArgumentException` (020-13's option (a);
  020-19's J7 had documented the other); `WBuilder` is spent also when `execute()` threw (as
  `IndexBuilder` after `start()`); `useIndex(name, String.class)` throws
  `IllegalArgumentException`, not `ObjectCreationException`.


## 5. State

Done: 1 to 4 committed in the clone `/Users/f/fl/bench/2026-11-09/clone-a21`, branch
`main`, on `80fa169` (the integration clone's tip with 020-19): `c4c96ce` (1), `f15b5e8`
(2), `f370bef` (3), `cce0ff4` (4). Not pushed; the coordinator takes them to the main tree.

Gates (`java/before-commit.sh`, under the shared lock, on a loaded F53):

* 1, alone (10:42): failed in `bergdb.core.Eviction.testInterruptedWhileAWriterWaits` only,
  "the thread parks for the writer" (a Core test that waits 2 s for the eviction thread to
  park, at load 19), not in this change; the rest passed (unit 1469 of 1470, f 86, DEMOS
  OK). Its second run was dropped from the lock's queue once 2's gate had passed.
* 1 and 2, at 2 (11:08): BEFORE COMMIT OK (172 s; unit 1471, f 86, DEMOS OK).
* 1 to 4, at 4 (11:11): BEFORE COMMIT OK (155 s; unit 1477, f 86, DEMOS OK), the extended
  StoppedCheck included; JAVADOC PUB OK.

3 was gated with 4 on top; 4 adds a check and a test, so 3 alone passes what 4 passes.

Q1, decided at 11:23, is `e5b6de8` on `cce0ff4` (section 4): BEFORE COMMIT OK (143 s;
unit 1477, f 86, DEMOS OK), JAVADOC PUB OK, 11:45.

Left: for 020-11: the Eviction test's failure under load, if it comes again.


Log
===

2026-11-09. Created by coord-1109's fixer a21, 10:31. 1 to 4 implemented, each with a test
that failed first, committed in the clone and gated by 11:14; Q1 for Frans.

2026-11-09. Q1 decided by Frans (11:23: "Yes, as recommended."): `Duration.seconds(NaN)`
refused, `e5b6de8`, a failing test first.

2026-11-09. Two faults in 1's strict parse (`648527f` on `main`), from Codex's review of the
day's fixes, round 2 (020-23), fixed in the clone on `main` at `6bb14a1`, each with a test
that failed first: Y1 (medium), a minus time's duration went through a double and was
truncated ("-0.0000021 s" was 20 units, `Time.MAX` minus its own seconds refused), now
exact and rounded half up, `1fa675f`, BEFORE COMMIT OK (140 s); Y2 (low), a year and a
month refused a time of day that the grammar allows ("2020-06 12:34"), `01ed9a2`, BEFORE
COMMIT OK (148 s).
