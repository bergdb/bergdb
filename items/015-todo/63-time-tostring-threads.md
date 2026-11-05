015-63. Fix: time.toString() from several threads gives wrong strings and throws
================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F8 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F8: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (`Time.java` line 212 there, the same static formatter).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in the night 006-12 (W1, clone `g3c`), by R8's first proposal.
Verified with R8's probe as a test: `Time.toUtcString()` (and `toString()`,
which calls it) formatted with one static `SimpleDateFormat`, which is not
thread-safe, so threads that formatted at once got another thread's string or
an exception.

* Test: `Time.testToUtcStringFromThreads` (unit test, 0.1 s), R8's probe: 8
  threads, 20,000 calls each, each thread its own time; an exception counts as
  a wrong string. Before the fix: "wrong strings, e.g. expected 2014-08-14
  14:24:34.1234567, got 2014-08-12 12:22:32.1234567, expected 0, got 90047";
  after it, five runs in a row pass.
* Fix: a static `java.time.format.DateTimeFormatter` with the same pattern,
  `Locale.US` and `ZoneOffset.UTC`, which is immutable and thread-safe, formats
  `Instant.ofEpochMilli(millis)`. A probe compared the two formatters on the
  valid range's edges and 5,000,000 random milliseconds in 0 to `Time.MAX`: no
  difference. The sentence "This class is not thread-safe" in
  `resolve(TimeZone, Time, String)`'s Javadoc, copied from `TimeResolver`'s
  about the resolver, is gone (`TimeResolver`'s static methods make a new
  resolver per call); the class Javadoc says that a Time is immutable and its
  methods may be called from any thread.
* The stream's bytes (P2): unchanged; formatting writes nothing. 010-01: no
  departure.
* A line in `releases/next.md` (Pub API).
