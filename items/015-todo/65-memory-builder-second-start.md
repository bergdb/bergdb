015-65. Fix: a second start() of a memory() builder whose database runs is not refused
======================================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

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


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
