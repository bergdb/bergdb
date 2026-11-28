028-74. Decide: a commit's time after a restart can be at or before a time a reader was given
==========================================================================================

Status: decided (2026-11-28): (a); the Javadoc written, P2's draft
not changed (it is not in the repository). Kind: Decide. Frans: decided.
Created 2026-11-27 by Frans Lundberg.

What: `DbClock.transactionBegin` gives a transaction the clock's time,
raised above the last transaction's time and above `lastReadTime`, the
last time that `currentTime()` gave a reader. A start sets the last
transaction's time from the stream (`setLastTransTime`); `lastReadTime`
begins at 0, since the times given to readers are not in the stream. So
when a reader is given a time R, the database is started again, and the
clock at the next commit stands at R or before it (it stands still, or
it was set back), the commit takes the clock's time, at or before R;
without the restart it takes R + 1.

* A read at R after that commit gives the commit's value, where the
  reader was given the state without it. `Db.currentTime()`'s Javadoc
  says that a read at the time given reads the same state whenever it
  runs; 020-23's Z1 keeps that when the clock goes back within one
  session, not across a start.
* The bytes differ for the same calls at the same clock values. P2's
  draft (031-06, `p2-draft.md`, "Its time") counts the time as an input
  of the action, so this is outside the principle as worded; it is still
  memory that a start does not rebuild and that decides a byte.

Found by the independent review of 031-06's landed diff (2026-11-27,
`review-main.md`, R3), with the probe
`review-main-probes/RmClockProbe.java` (`runs/clock.txt`): a put,
`currentTime()` at a later clock, then a put with the clock standing
still and with it set back, each with and without a restart before the
second put. Without the restart the commit's time is 200000001 and a
read at R gives no value; with it, the commit's time is the clock's
(200000000, or 150000000 set back), the read at R gives the commit's
value, and the streams differ. Not of 031-06's diff: `DbClock` is as it
was. The reach is a clock that does not pass R across a restart: a
test's clock, or a system clock set back. `P2CrashProbe`'s
`-Dreader=1` calls `currentTime()` before every action, so its restarts
never fall between a reader's time and the next record.

Why: a read time's promise (the same state whenever it runs) does not
hold across a start; and P2's "nothing but the stream decides a byte"
has an exception that its draft covers only by calling the time an
input.

Frans: decided, (a) (2026-11-28). A change of `currentTime()`'s promise,
or of its behaviour, is the public API's. The options:

* **(a) State the limit.** No code. `currentTime()`'s Javadoc and P2's
  "Its time" say that a time `currentTime()` gave holds for the session
  that gave it: after a start, a read at a time given before it may see
  commits made after the start, if the clock did not pass that time.
  Cost: a sentence in the Javadoc and in 031-06's P2 draft.
* **(b) Read times within the stream.** `currentTime()` gives at most
  the last transaction's time while no commit has a later time to give:
  the state at the clock's time and at the last transaction's time is
  the same, so every read gives the same values; a start rebuilds the
  bound from the stream, and the next commit's time is above every time
  given. Changes what `currentTime()` returns while the database is not
  written to (it stands at the last commit's time), and with it what
  applications that use it as "now" see, and reclaim's checks of a read
  time against the retain duration; to be studied before it is chosen.
* **(c) The times given kept in the stream.** A record of the read time
  before it is given. Appends without an action, which P2 rules out, and
  costs a record per read; not recommended.
* **(d) A start waits for its clock.** A start, or the first commit after
  it, waits until the clock is past the last record's time by a margin.
  Covers a clock that stands still, not one set back past the margin,
  and still cannot know R; not recommended.

Recommendation: (a) for 2026.7: the reach is a test's clock or a clock
set back, and the statement makes the promise exact; (b) as a study for a
later release if a promise across starts is wanted.

Decision: Frans, 2026-11-28, 07:27: (a) for 2026.7.

Done when: Frans has chosen; for (a), the Javadoc of `currentTime()` and
P2's draft say it; for (b), a study with its effects on reads, reclaim
and the Pub API.

First step: the sentence in `currentTime()`'s Javadoc and in P2's draft.


Result
------

Written 2026-11-28 by an agent of lead-1127, from the code (`DbClock`,
`Db.setLastTransTimeOfDbClock`); no change of behaviour.

* `Connection.currentTime()` and `Database.currentTime()` (the Pub
  API): the paragraph of 018-04's Q5 says that a time that
  `currentTime()` returned holds for the session that returned it;
  after a restart, with a clock that stands still or was set back, a
  transaction can get a time at or before it, and a read at that time
  then sees that transaction. A time that holds across restarts is the
  time of a transaction that was committed and is durable
  (`Transaction.getTime()`, after `Transaction.sync()`).
* `Db.currentTime()` (the Core): the same, with `Trans.tt` after
  `execute()` and `sync(t.lastPos, level)`, and that a start takes the
  last transaction's time from the stream. The class Javadoc's
  "Threads": a read at a time given reads the same state within the
  started Db.
* Why a transaction's time holds: a start sets the last transaction's
  time from the last record it reads (`setLastTransTime`), and
  `transactionBegin` gives every transaction a time above it; a
  transaction that is durable is in the stream that the start reads.
* Not done: P2's draft (031-06, `p2-draft.md`), which is not in the
  repository.


Log
---

2026-11-27. Registered by lead-1127, from the review of 031-06's landed
diff (R3).

2026-11-28. Frans decided (a) (07:27). The Javadoc and P2's draft not
changed yet.

2026-11-28. The Javadoc of `currentTime()` in `Connection`, `Database`
and `Db`, and `Db`'s "Threads", by an agent of lead-1127 (branch
`floor-74-r6`); BEFORE COMMIT OK on the branch's final tree. P2's
draft left as it is.
