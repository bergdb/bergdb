019-08. Fix: DbUtil.dbTimeToUtc() from several threads gives wrong strings
==========================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Frans: none.
Created 2026-11-05 by Frans Lundberg.

What: `DbUtil.dbTimeToUtc(long)` (`java/src/bergdb/core/DbUtil.java`)
formats with one static `SimpleDateFormat`, `DATE_FORMAT`, which is not
thread-safe: 015-63's fault, in the Core Layer. Its callers:
`Db.getOneInternal`, `Db.getMany` and `Db.expiredIfReadBelowCut`, which
build the message of `LookupTimeNotAvailableException` in the reader's
own thread, and `Jmx`'s time strings.

Why: two threads that format at once share the formatter's `Calendar`,
so a message gets another thread's time, and the same pattern threw an
`ArrayIndexOutOfBoundsException` in `Time` (016-06's R8-F8), which would
come out of a read in place of `LookupTimeNotAvailableException`. Readers
that are refused at once (a cut that overtakes several) are the likely
case. Found by review R2 of night 006-12 (finding B1), with a probe: 8
threads, 20,000 calls each, 105,608 wrong strings, none thrown. 015-63
fixed `Time` only, which R8-F8 named; `bergdb.core` is in 2026.3's goal
(018-01, section 1).

Frans: none.

Done when: a test from several threads fails before the fix and passes
after it, a probe shows the strings unchanged over the valid times, and
`before-commit.sh` prints BEFORE COMMIT OK.

First step: fix it as 015-63 was fixed: a static `DateTimeFormatter`
with the same pattern, `Locale.US` and `ZoneOffset.UTC`, formatting
`Instant.ofEpochMilli(ms)`.


Log
---

2026-11-05. Registered in night 006-12, from review R2's finding B1, and
taken by a W1 agent (clone `f2`).

2026-11-05. Done in night 006-12, as 015-63.

* Test: `DbUtil.testDbTimeToUtcFromThreads` (unit test, 0.1 s): 8
  threads, 20,000 calls each, each thread its own time; an exception
  counts as a wrong string. Before the fix: "wrong strings, e.g. expected
  2001-09-09 01:46:40.000 UTC, got 2001-09-24 02:10:22.222 UTC, expected
  0, got 154986."; passes after it. `DbUtil.testDbTimeToUtc` pins three
  strings (time 0, a time in 2014, and 2^56 - 1, `Time.MAX`), before and
  after.
* Fix: a static `java.time.format.DateTimeFormatter` with the same
  pattern, `Locale.US` and `ZoneOffset.UTC`, immutable and thread-safe,
  formats `Instant.ofEpochMilli(ms)`; the Javadoc says the method may be
  called from any thread.
* The strings: a probe compared the old formatter with the new on the
  valid range's edges (0, 1, 9,999, 10,000, 10,001, `Time.MAX` and near
  it, -1 and -10,001 units) and 5,000,000 random times in 0 to
  `Time.MAX`: no difference; and none in 2,000,000 random times from
  1583 to 9999. They differ only outside the times a database has:
  before 1582-10-15 (`SimpleDateFormat` changes to the Julian calendar,
  `java.time` does not) and after year 9999 (`java.time` writes a "+").
* The stream's bytes (P2): unchanged; formatting writes nothing. 010-01:
  no departure.
* A line in `releases/next.md` (Reliability).
