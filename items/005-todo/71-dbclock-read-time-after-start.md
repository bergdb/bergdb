005-71. Fix: `DbClock` forgets the last read time at a start
============================================================

Status: open. Kind: fix. Created 2026-10-28.

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
