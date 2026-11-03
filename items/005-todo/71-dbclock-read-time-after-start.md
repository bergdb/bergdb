005-71. Fix: `DbClock` forgets the last read time at a start
============================================================

Status: open; option A taken under D2 (016-01, section 10) and planned
for release 2026.2: two notes, no code (see Plan for 2026.2). Kind: fix.
Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
012-02's determinism audit (012-02, section 10.3, finding C3; question Q2
in its section 13), as 012-01's decision D5 says.


The issue
---------

`DbClock.transactionBegin` gives a time later than the last transaction's
and than `lastReadTime`, the last time `currentTime()` returned. A start
rebuilds the last transaction's time from the stream, but `lastReadTime`
is in memory only and starts at 0. So with a clock that has not moved,
`currentTime()` followed by a restart changes the next transaction's
time, and with it the stream's bytes (against P2, 010-01: "a restart can
be inserted between any two transactions without affecting the bytes in
the stream").

Probe (012-02, `RestartStateProbe clock`): put `/a`; the test clock set to
T2; `currentTime()` (returns T2); [restart]; put `/b` with the clock still
at T2. Without the restart `/b` gets T2 + 1, with it T2; both streams 472
bytes, different SHA-256.

With the system clock a restart takes longer than a time unit (100 ns), so
it does not happen in practice; with a test clock or a clock set back, it
does. The order of times is kept either way: `/b`'s time is still later
than every transaction before it.


Options
-------

* **A.** Nothing in the code: a read time is not a write and need not be
  durable; the times stay increasing; write the exception into P2's text
  and the cross tests avoid the case.
* **B.** Keep the read time across a start: a start sets `lastReadTime` to
  at least the last transaction's time plus one, which removes most but
  not all of the dependence (the read time itself is not in the stream).
* **C.** Make `currentTime()` not move later transactions' times when the
  clock has not moved (a design change of `DbClock`).

Recommended: A, with a note in 010-01's P2, as the read time is not part
of the stream and the case needs a clock that does not move; Frans
decides. For 012: C ports `DbClock` as it is (012-01, 4.4).


Done when
---------

The decision is taken and done (for A, the note in P2 and in 012-05's
workload rules; for B or C, the change with its test and the gates).


Plan for 2026.2
---------------

Written 2026-11-03 for 016-05 (W4). Option A, the entry's recommendation,
taken with Frans's D2 (016-01, section 10: "D2. As you recommend unless I
say otherwise here."): nothing changes in the code; the exception is
written down where the rule and the workloads are.

The steps, by agent F1 (016-05), after 005-80, in
`/Users/f/fl/bench/016/005-71/repo` (a new clone of `main`):

1. **The note in P2** (0.1 hours), `items/010-principles/01-principles.md`,
   P2's "Where BergDB stands", a bullet after "Checked for the buffer
   time": "Not kept across a start (005-71, option A, 2026-11-03):
   `DbClock`'s last read time, the last time `currentTime()` returned. A
   restart after a `currentTime()`, with a clock that has not moved since,
   gives the next transaction an earlier time, by one unit, than without
   the restart, and so other bytes. Accepted: a read is not a write and
   need not be durable; the times stay increasing; it needs a clock that
   does not move (a test clock, or a system clock set back), as a restart
   takes longer than a time unit (100 ns). The checks of P2 move the test
   clock before each transaction." The agent checks that last sentence
   against `RestartInvariance` and `StreamDigest` (where they set the
   clock, whether either calls `currentTime()` before a restart) and
   writes what it finds.
2. **The note in 012-05** (0.05 hours),
   `items/012-bergdb-c/05-cross-harness.md`, section 6.1, the `now` rule:
   a dated sentence after "it can move the next transaction's time
   (012-01, 4.4)": "(2026-11-03, 005-71, option A:) a `now` before a
   `restart`, with the clock not moved, makes the next transaction's time
   differ from a run without the restart; Java and C do the same, so the
   cross tests agree, but a workload that compares streams with and
   without restarts sets the clock (`t T`) after such a `now`." 012 is a
   done item; this is a dated addition that the entry's "Done when" asks
   for, not an update of its history.
3. **No gate**: no file of `java/` or `lean/` changes.
4. **The review**, with 005-69 (016-05, section 5): the notes against the
   code (`DbClock.transactionBegin`, `currentTime`, the start's
   `setLastTransTimeOfDbClock`); the answers here, in the Log.
5. **The hand-off** (016-05, section 4): the two notes and this entry's
   Outcome, Status "done (2026-11-0x)".

Size: about 0.4 agent-hours, the review's share included. No stop for
Frans. Done when both notes are in `main`.

**State** (2026-11-03): planned, not started.


Log
---

2026-11-03. Option A planned for release 2026.2 (016-05): the notes in
010-01's P2 and in 012-05; no code. Nothing changed yet.
