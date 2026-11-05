015-60. Fix: database.connection() keeps a connection for every thread that ever called it
==========================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F5 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F5: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (`DatabaseImp.java` lines 51 to 57 and 153 there).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, night 006-12. Done. Verified: `DatabaseImp.connection()` put each
calling thread and its connection in a `HashMap<Thread, Connection>`, which
only `stop()` and `close()` cleared.

* Test (`PubTester`, unit): `testConnectionOfEndedThreadNotKept`: 20 threads
  each call `connection()` and end; the test keeps weak references to their
  connections, and calls `System.gc()` and `connection()` up to 50 times.
  Before the fix: "connections of ended threads kept, expected 0, got 20.";
  passes after it (under G1 and ZGC), in a few milliseconds. R8's probe read
  the map by reflection; the test needs no reflection.
* Fix, one of R8-F5's two: the map is a `WeakHashMap<Thread, Connection>`,
  so an ended thread's entry goes at the map's next use after the collector
  has taken the thread (a connection holds no reference to its thread).
  `stop()` and `close()` clear it as before. Not R8's other option, a
  `ThreadLocal` per database: its value in a long-lived thread (a pool's)
  would keep a stopped database, as the connection refers to it, until the
  thread ends. A comment at the field says so.
* Javadoc of `Database.connection()`: the database does not keep the
  connection of a thread that has ended.
* 010-01: no setting, no global state, no thread (P3, P9, P10); the stream is
  not touched (P2).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (111 s)`, unit 1188, f 87.

2026-11-05, night 006-12. The Javadoc of `Database.connection()`, the
field's comment and the line in `releases/next.md` made exact (review R2,
C2): they said that the database does not keep an ended thread's
connection, but the entry goes only once the thread is no longer
referenced (an application's list of its workers keeps it) and the
collector has taken it, at a later call of `connection()`. Now they say
so. The code is unchanged.
