015-65. Fix: a second start() of a memory() builder whose database runs is not refused
======================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: a second `start()` of a `DatabaseBuilder` with `memory()` (or the
Core's `mainStream()`) whose first database still runs is not refused:
both databases append to the same MemoryStream, and each misses the
other's puts. With a crypto key the second start wraps the SalsaStream
again. A `dir()` builder is refused (005-63, 015-56). Found by the agent
that fixed 015-56, with a probe in its clone
(`/Users/f/fl/bench/016/015-56/repo`).

Done when: a second start of such a builder is refused while its database
runs, with a test that fails before.

First step: the probe made a test in PubTester.



The fix
-------

**The cause**: `DatabaseBuilderImp.start()` takes the stream that its
`DbBuilder` holds. For `create()` and `open()` the start opens a new
`FileStream`, and a second one on the directory is refused by its lock
(005-63, 015-56); for `memory()` and `mainStream()` the `DbBuilder` keeps
the one stream, and with a crypto key the `SalsaStream` that the first
start wrapped around it. Nothing checked that a database still used it.
The probe (on `main` at `85d8fa4`): the second start returns, does not see
the first's unsynced `/a`, each database misses the other's puts, and the
second's `close()` closes the stream, so the first's `close()` throws
"Cannot append to closed stream"; the same with a key.

**The fix**: the builder keeps the `Db` of its last start on a stream
(`dir` null) and that stream as the `Db` got it (the `SalsaStream` with a
key). `start()` refuses, before anything else is checked or opened
(`refuseStreamInUse()`), when the `DbBuilder` still holds that stream and
that `Db`'s close has not ended: `IllegalStateException`, "The database
that this builder started on its stream of memory() has not closed ...".
So a start is refused also while the database closes after `stop()`, as a
directory is (`start()`'s Javadoc, 005-63). Once that close has ended, a
start goes on as before (a restart on a closed `MemoryStream`, as in
2026.1; not this entry's). `memory()` and `mainStream()` give the builder
another stream, which is not refused. `Db.Internal.isClosed()` is new: the
close's `closeDone`, under `closeLock`. `DatabaseBuilder.start()`'s
Javadoc says it, with `@throws IllegalStateException` (also for the
existing "no streams" refusal).

**Test**: `PubTester.testSecondStartOfMemoryBuilder`, without and with a
crypto key: the second start is refused, the first database puts, syncs
and reads `/a` and `/b`, `memory()` again starts a new, empty database,
and both close. Before the fix: "the second start returned, without a
crypto key"; after, it passes, as do `PubTester` and `DatabaseBuilderImp`
(112 tests). `javadoc-pub.sh` OK.

**Principles** (010-01): no setting (P10), no global state (the builder's
own fields, P9), no thread or timer (P3); the stream's bytes are unchanged
(P2): a start that is not refused runs as before. P12: one method on
`Db.Internal`, not on the Core API.



Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, night 006-12 (W1): fixed in the clone
`/Users/f/fl/bench/006-12/g4b`, branch `w1-g4b`; the test first, then the
fix; `before-commit.sh` through the night's gate.
