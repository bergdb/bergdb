028-20. Fix: the kill-and-restart harness fails a late exit run
===============================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: `java/stress/kill-restart.sh 1000`, seed 20261119, while the
machine's load stood near 90, failed at database 11, run 13 (026-25,
section 6):

    KILL RESTART FAILED: the child ended before its kill, with status 0

The run was aimed at "exit": the child stops the database and returns from
`main`, and its JVM must end by itself with status 0. The child did not
print "P exit" within 8 s of "P running", so the parent counted the run
late and aimed a kill after a delay; by then the child had stopped and
ended by itself with status 0, as an exit run should. The check of the
data never ran. The rerun with the same seed, at a load near 7, passed.

Why: a false failure of the harness (020-15), not of the database, on a
loaded machine; the night runs and the gates run on such machines. Frans,
2026-11-19, 10:14: "Go ahead and fix the test tool."

Frans: none.

Done when: an exit run whose child ends by itself with status 0 is an
exit, also when it was late, and the next start checks its data as for
any exit; every real check kept; a test that fails before the fix and
passes after it; `java/before-commit.sh` BEFORE COMMIT OK;
`kill-restart.sh 1000` with seeds 20261119 and 20261121 KILL RESTART OK.

First step: read `KillRestartHarness.runChild`.


Findings
--------

**The cause.** `KillRestartHarness.runChild` waits for the line of the
phase that a run aims at. A run aimed at build, cleanup, close or exit
that sees no such line in 8 s after "P running" is late: the parent aims a
kill then, after the run's delay (up to 200 ms), and if the child is no
longer alive at the kill, it reports "the child ended before its kill".
For build, cleanup and close the child cannot end by itself (the schedule
runs, or `close()` waits for its kill), so such an end is a fault. A run
aimed at exit can: its index thread calls `stop()` after 50 to 1,550 ms,
at the end of an operation; on a loaded machine an operation (a join, a
check, a sync) can take seconds, so "P exit" came after the 8 s and the
JVM ended within the delay. Only the path of an exit seen in time wrote
the journal's PX (the JVM ended by itself with status 0), which makes the
next start check that every transaction that returned is there.

The other late paths (build, cleanup, close) have no such end; an end of
their child before the kill stays a failure. One more weakness of the
same loop: the late time and the 300 s hang deadline were checked only
when no line had come for 100 ms, so a child whose "P build" and "P
cleanup" lines came more often was never late.

**The fix** (`runChild`). Whether the child ended by itself is decided
after the kill, for every run aimed at a kill: it was not alive at the
kill, or its status is 0 (a JVM killed with SIGKILL never ends with 0).
A run aimed at exit that ended by itself with status 0 after "P exit" is
an exit, late or not: PX in the journal, counted as an exit, and the next
start checks its data as for any exit. Any other end before the kill
stays a failure ("the child ended before its kill, with status N"), as
does a non-zero status or a hang of an exit seen in time; a late exit run
whose child is still alive at the kill is a kill, as before (its journal
has XB and no PX, so the next start checks it as a kill). The late time
and the hang deadline are checked after every line. The late time is
`lateMs` (8,000 ms; the parent's system property `killrestart.late`).

**The test.** `KillRestartHarness lateexit BASE SEED`: a run aimed at
exit with a late time of 200 ms, its `stop()` after 1.5 s and a delay of
60 s, so that the parent goes late and the child ends by itself in the
delay, every time; it must be counted an exit, late, with no failure; then
the last run starts on the directory and must check one exited run
(`exitedRuns` 1). About 3 s. `kill-restart.sh` runs it after the
self-check (not a commit gate; before-commit.sh unchanged).

- Before the fix (the test hook and the check on the old `runChild`): LATE
  EXIT FAILED, "the child ended before its kill, with status 0", in 4 of 4
  runs.
- After the fix: LATE EXIT OK in 4 of 4 runs, and in each gate's run.


Gates
-----

On the branch `028-20-harness-late-exit` with main merged (00ca0348; the
later merge of main, e472f95f, changed only items), on F53 while
`java/night.sh` and other gates ran (load 40 to 70):

- `java/before-commit.sh`: BEFORE COMMIT OK (167 s).
- `java/stress/kill-restart.sh 1000 20261119`: SELF-CHECK OK, LATE EXIT OK,
  KILL RESTART OK, 1,000 kills and 50 exits in 2,242 s (late 0).
- `java/stress/kill-restart.sh 1000 20261121`: SELF-CHECK OK, LATE EXIT OK,
  KILL RESTART OK, 1,000 kills and 44 exits in 2,237 s (late 1).

The same three passed on the first merge of main (e95bcc66), before
028-18 landed.


Log
---

2026-11-19. Registered and taken by an agent of coord-1118 (Frans, 10:14),
on the branch `028-20-harness-late-exit`.

2026-11-19. Done: the fix, the check `lateexit` and the gates, by an agent
of coord-1118.
