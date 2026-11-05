015-38. Fix: JMX's monitor thread ends on an interrupt, and stop loses the caller's flag
========================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `Jmx`'s `DBMonitor.MThread` ends on an interrupt (stale speeds), and its stop swallows the caller's interrupt flag. Internal only: nothing in BergDB starts `Jmx.Speed`.

Source: review R3, R3-F4 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F4), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F4, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, night 006-12. Done. R3-F4's probe, made two tests in
`InterruptTester` (f-tests, about a second each, as `stop()` waits for the
monitor's sleep of 1 s):

* `testJmxMonitorInterrupted`: the monitor thread interrupted in its sleep.
  Before the fix: "the monitor ended on an interrupt, expected true, but was
  false."; passes after it.
* `testJmxStopInterrupted`: `stop()` with the caller's flag set. Before the
  fix: "the interrupt flag was lost, expected true, but was false." (and it
  returned before the monitor ended); passes after it, and checks that the
  monitor has ended when `stop()` returns.

* Fix, as R3-F4 proposed: `Jmx.Speed.run` goes on after an interrupt of its
  sleep (only `stop()` ends it, 005-46's rule for BergDB's own threads), so
  `registerAndStart()` never keeps a dead thread; `stop()` joins through
  interrupts, unregisters and clears the thread only after it ended, under
  the object's monitor as before, and sets the caller's flag again if it was
  set. A Javadoc for `stop()` says so.
* 010-01: no setting, no state, no new thread or timer (P3, P9, P10); the
  stream is not touched (P2).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (111 s)`, unit 1185, f 87.
