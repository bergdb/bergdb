019-42. Fix: an index build that meets an object it cannot index fails the database at every start
==================================================================================================

Status: open. Kind: Fix. Frans: none (the coordinator's default, below;
Frans may choose otherwise).
Created 2026-11-06 by Frans Lundberg.

What: since 019-10 (01b0493) and 019-38 (cecaf4c), the index build's
thread fails the database on any exception but a refusal, an expiry or
an interrupt. An index function that throws on the user's data does so:
an object whose indexed `String` field is null gives a
`NullPointerException` (an `AssertionError` with `-ea`; S2-F26), and a
nested field that does not parse another (S2's D1, S2-F15). The build is
resumed at every start, before `start()` returns, and fails the database
again within half a second: through the Pub API the database cannot run
again, and it cannot delete the index after the failure. Before 019-10
the build stopped silently and the database went on.

Why: 020-01, section 12, N1, shown by a probe (`V1Probe`, in
`/Users/f/fl/bench/006-13/v1-probe/`), with and without `-ea`. Class A by
018-01's severities ("a database that cannot run again"), in
experimental code (user indexes, 018-01, D2), and caused by today's
change.

Options (020-01, section 14, point 1): (a) fix S2-F26's cause: a null
indexed `String` gives no entry, as a missing field (a few lines and a
test); other objects a build cannot index still fail the database; (b)
the build's thread ends the build as failed (its status says so, the
exception kept), and does not fail the database, on any exception of the
index work that is not an `Error`; the database goes on, as before
019-10, and the index can be deleted; (c) a known issue of the
experimental part.

The coordinator's default, 2026-11-06, 12:31, while Frans is away (he
may choose otherwise): (b) now. It closes the whole class (any object a
build cannot index), not only the null field, and restores the behaviour
before today for this thread, with a visible status instead of a silent
stop; it does not decide what a null field means, which is 2026.4's
contract (020). An `Error` still fails the database (the error model,
docs/levels.md, section 3). (a) waits for 2026.4.

Done when: (b): in `IndexBuilderImp`'s build thread, an exception of the
build that is not an `Error` (and not a refusal, an expiry or an
interrupt, which 019-38 retries) ends the build: its status is failed
with the exception, the job is not resumed at the next start (or is, and
ends again without failing the database: say which, the simplest), and
`deleteIndex` works; a test with V1Probe's shape (a null indexed field)
fails before the fix (the database fails) and passes after (the database
goes on, the build's status is failed, a restart runs, the index can be
deleted); one sentence in docs/levels.md, section 3, and in
`releases/next.md`'s experimental part; `BEFORE COMMIT OK`.

First step: 020-01, N1, and its probe.


Log
---

2026-11-06. Registered by coord-1106 from 020-01's N1, with the
coordinator's default (b).
