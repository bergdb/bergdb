028-32. Fix: IndexHarness bounds a frozen lookup time by a time taken before the read
====================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: `java/week.sh` (run 2026-11-19-1514, on main c0e2afaf), step
harness-soak-week, job 11 h2, failed. From `java/`:

    java -ea -Xmx1g -Devict=random -Devictseed=20776102 -cp build/bergdb.jar \
        bergdb.dev.Run bergdb.pubimp.IndexHarness 20776102 5000 2 1 0 1 0 0

    AssertionError: IndexHarness, seed 20776102, fault NONE, step 102: the frozen
    lookup time 98813245, not from the last transaction's time, 98813244, to the
    current time, 98813244
      at bergdb.pubimp.IndexHarness.check(IndexHarness.java:944), checkAt (1600),
      step (1357)

Step 102 was a deletion of the index i0 with a read-write transaction in
another thread. The coordinator reproduced it in 6 of 6 runs with the
week's jar and in 2 of 2 on main dab74f92, each time with a frozen lookup
time one unit after both bounds; with 1 thread and no eviction it passed 2
of 2.

Why: either the Pub layer reads at a time after the current time (a
database bug), or the harness's bound is wrong.

Frans: none.

Done when: the cause found; a database bug fixed with a unit test that
fails before and passes after, or a harness bug fixed with every real
check kept; `java/before-commit.sh` BEFORE COMMIT OK; the command 10 times
without a failure; `java/stress/harness-soak.sh -r 10 -b 20776100` ALL OK.

First step: read `IndexHarness.checkAt`.


Findings
--------

**The check.** After each operation, `IndexHarness.step` takes the
database's current time, t = `db.currentTime()`, and calls `checkAt(t,
true)`. In a wide run, one such check in four freezes a new connection's
lookup time (020-17, B10), reads once with `exists()`, and checks that the
frozen time, from `getLookupTime()`, is from the last user transaction's
time (the model's) to t.

**The cause: the harness.** The bound t was taken before the read. The
frozen time is the latest state at the read: the last transaction's time
then (`DbClock.lookupTime`). The index jobs commit the database's own
transactions in their threads at any moment: a build's steps
(`IndexBuild-NAME-GEN`) and a deletion's cleanup steps
(`IndexCleanup-NAME-GEN`, `IndexManager.startCleanup`). One that commits
between `now()` and the read takes the time t + 1 (the harness's clock is
fixed, so the next transaction's time is the last one's plus one), and the
read freezes at it: the latest state, as 020-10, section 3.6 promises, but
after t. A probe (a record of the last committing thread in `DbClock`,
not kept) named the committer in two failing runs: `IndexCleanup-i0-...`
at step 992 and `IndexBuild-i1-...` at step 4048; the current time after
the read was the frozen time in both. So the database read no future
state: no read was at a time after the current time when it ran.

Why it showed now: the check runs only in a wide run. `night.sh` runs
`harness-soak.sh -r 2`, rounds 0 and 1, whose h2 jobs are never wide
(`wide=$(pick $((r / 2)) 0 1)`); `week.sh` (028-23, 028-27) runs `-r 10`,
whose round 2 is this job: 5,000 operations, 2 threads, wide.

**The fix** (`IndexHarness.checkAt`). The upper bound is the current time
taken after the read, which bounds every time read: the frozen time is at
most the last transaction's time at the read, and `currentTime()` is never
earlier than that. The lower bound, the last user transaction's time, is
kept, as are the scans and the raw entries checked at the frozen time. A
read at a future time still fails the check.

**The start.** The bound is as old as the check, f4947035 (2026-11-09,
020-17, B10); no landing of 2026-11-18 or 2026-11-19 made it. The command
failed at f4947035 (in the third of three runs) and in the first run at
9a02d756 (2026-11-18), at c458bfea (2026-11-19, morning) and at dab74f92,
so a bisect had no good commit to start from.


Gates
-----

On the branch `028-32-frozen-lookup-time` (from main dab74f92), on F53:

- The command: before the fix, it failed in 2 of 2 runs (steps 2648, 906);
  after it, IndexHarness OK in 10 of 10 runs.
- `java/before-commit.sh`: BEFORE COMMIT OK (68 s).
- `java/stress/harness-soak.sh -r 10 -b 20776100`: HARNESS SOAK OK, 50
  jobs of 50 OK in 10 rounds (1,532 s).


Log
---

2026-11-19. Registered and taken: week.sh's harness-soak failure (run
2026-11-19-1514), by an agent of coord-1118.

2026-11-19. Done: a harness bug; the bound is the current time after the
read; gated on its branch, by an agent of coord-1118.
