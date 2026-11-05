019-09. Fix: close() returns normally after a background write failure that no call met
=======================================================================================

Status: waiting. Kind: Fix. Frans: decision.
Created 2026-11-05 by Frans Lundberg.

What: the buffer's consumer fails to write (a disk error) while the
database is active, and the application's next call is `close()`.
`Db.close()` sets the state to STOPPING first, so 015-35's check in
`Db.assertDbStateIsActive` never runs and never fails the database.
`StorageManager.closeInner` then returns no failure, as the main stream
has failed (`mainFailing`). `close()` returns normally. The transactions
that were buffered are lost, and no call reports it.

A failure during close's own flush is reported: `closeInner` reads
`failed` before its close, so that failure is returned and `close()`
throws `StreamIoException`.

Why: 018-01, section 6.2, checks after each run that "`close()` returns
and reports the failure". `Database.close()`'s Javadoc says that close
waits until "every transaction that has returned is written"; a normal
return here says so wrongly. Against 010-01, P7.

Source: review R1 of night 006-12 (`/Users/f/fl/bench/006-12/review-r1.md`,
section "Re-review of 3cb19f7", B2), confirmed by a run. Its probe
`R1UnreportedProbe`, case 1 (a failed flush, then `close()` with no call
between): "close() returned normally". Case 2 (the failure during close's
own flush): "close() threw StreamIoException: probe: append error 2".

Older than night 006-12. Before 3cb19f7 the close of a failed main stream
was skipped and `first` stayed null; before 015-35 too. Releases 2026.2
and 2026.1 have it, by reading: their consumer's failure goes through the
`appendFailed` listener to `handleStreamException`, which sets the
stream's place to null, so `closeInner` closes nothing there and returns
null, and `Db.close()` returns normally
(`git show release-2026.2:java/src/bergdb/storage/StorageManager.java`,
`closeInner` and `handleStreamException`; 2026.1's the same).

Also: `closeInner`'s Javadoc since 3cb19f7 says that the storage's
failure is "reported by the call that met it". In this case no call met
it. The words are corrected with the fix, as is the B1 part of 015-35's
entry, which says the same.

Frans: decision. `Database.close()`'s Javadoc promises that a failed
final flush or storage close throws `StreamIoException` (005-73, F5), and
that close waits until every returned transaction is written. It does not
say what close does when an earlier background write failed, nor when the
database has already failed. `DbFailedException`'s Javadoc says to stop or
close a failed database and start it again; today that close returns
normally. The options:

* (a) **close() throws when no call has reported the failure.**
  `closeInner` returns `getFailure()` when the main stream has failed.
  `Db.close()` throws `StreamIoException` with it as the cause, unless the
  database has already failed with it: the state was FAILED before the
  close (read before close sets STOPPING), or `Db.failure` is a
  `StreamIoException` whose cause is that failure. A close of a database
  that a call has failed returns normally, as today. `close()` after
  `stop()` throws it too, as for a failed final flush. The Javadoc of
  `Database.close()` says so. This is R1's suggested fix. P7 is met: every
  failure is reported once at least.
* (b) **close() throws whenever the storage has failed**, also after a call
  has reported it. Simpler: no check of the state. But the close that
  `DbFailedException` asks for then throws too. In a `finally` block, its
  exception replaces the `DbFailedException` that the application was
  handling; in try-with-resources it is added as suppressed. P7 allows a
  repeat; the noise is the cost.
* (c) **close() does not throw**; only the words change. `closeInner`'s
  and `Database.close()`'s Javadoc say that a background write failure
  that no call met is not reported by close(), and that a `sync()` before
  close is the way to know. 018-01, section 6.2, is then not met for this
  case, and close's Javadoc no longer promises that a normal return means
  every returned transaction is written.

Recommendation: (a). It reports the lost transactions to the one call
that is left, keeps the close of a failed database quiet, and uses the
exception that close already throws for a failed final flush.

Done when: a test, R1's probe case 1 made a test in `DbTesterFailure`
(a failed background flush, then `close()` with no call between), fails
on the code before the fix and passes after it, with the chosen option;
the Javadoc of `closeInner` and `Database.close()` and 015-35's entry say
what the code does; the fix is in `main` after `before-commit.sh`.

First step: Frans chooses. Then the test first, as above, and a second
case for the already-failed database (a get that fails first, then
`close()`), which pins (a)'s exception or (b)'s.


Log
---

2026-11-05. Registered in night 006-12, from review R1's re-review of
3cb19f7 (B2). Status waiting: the contract of `Database.close()` needs
Frans's decision.
