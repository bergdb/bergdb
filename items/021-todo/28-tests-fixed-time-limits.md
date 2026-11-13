021-28. Fix: unit tests with fixed time limits fail under load
==============================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: some unit tests of `java/before-commit.sh` wait for a condition, or
measure, against a fixed wall-clock limit, and fail when the machine is
loaded. The known one is `bergdb.core.Eviction.testInterruptedWhileAWriterWaits`
(`java/src/bergdb/core/Eviction.java`, the last test): it gives the writer
and the eviction thread 2 s together to reach their waits, then asserts
that the interrupted thread takes less than 25 ms of CPU time in 50 ms.
It failed once at load 19 on 2026-11-09 (020-21; 020-11, "Test gaps")
and once under load on 2026-11-13 at 05:16, during the release morning of
2026.5 (coord-1112, 006-23, section 6, point 3); which assertion failed
at 05:16 was not recorded. It passed when run again both times.

Why: a gate that fails on a loaded machine sends a session after a fault
that is not there, or teaches it to rerun until green. The coordinators
run gates while other work loads F53 (013-02), so the load is normal.

Frans: none.

Done when: every unit test of before-commit.sh with a fixed time limit
is listed in this entry, each changed so that load alone does not fail it
(wait for the condition with a generous limit, such as 30 s, and fail
only then; or measure in a way that load does not change), or kept with
a reason; `java/before-commit.sh` prints `BEFORE COMMIT OK`; and three
runs of before-commit.sh, each beside a CPU load of twice the cores
(such as `yes > /dev/null` in 2 x cores processes), pass, or each failure
is a fault of its own that gets an entry.

First step: reproduce the Eviction test's failure under load (the test
alone, in a loop, beside the CPU load) and note which assertion fails;
then grep the tests for `System.nanoTime()` and `currentTimeMillis()`
deadlines, `Thread.sleep` before an assertion, and timed `join(ms)` or
`await(ms)` whose limit is under about 10 s.


Log
---

2026-11-13. Registered by coord-1113 (Frans, 06:38: "Yes, register them"),
from coord-1112's handover (006-23, section 6, point 3).
