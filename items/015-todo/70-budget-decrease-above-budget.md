015-70. Fix: a budget decrease can settle above budget although the pins fit
============================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2.

What: review R4's finding R4-F5 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F5: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12 (W1). Verified: R4's regression test
(`R4EvictionTester.testBudgetDecreaseAfterPinsFall`) fails on f5a5f66
(3,703 bytes resident, budget 3,447, pinned 3,016) but passes on the
night's `main`: since 015-87 (60f29c7, found by `git bisect`) the
decrease's batches happen to complete the hand's round, whose fresh pins
lower the trigger. The fault is still there; whether a batch reaches it
depends on where the hand stops (timing). The mechanism, in `sweep` and
`EvictorRun`: after a decrease the thread runs batches while the
resident bytes are over the trigger; a batch counts down to the pinned
bytes of the hand's last complete round (`pinnedOfLastRound`), which may
be of a round before the writer wrote nodes that were dirty, and the
trigger after the batch is those pins plus the gap between the
watermarks: with resident bytes at or below the old pins, nothing is
freed and the thread stops above the budget, although the pins fit it.

* Fix: a decrease of the budget (`setBudget` with a lower budget) sets
  `decrease` and counts itself in `budgetSets`. While it lasts, the
  thread's batches go on until the resident bytes are at most the budget
  (`goal()`), not the trigger. A batch counts down to the pins of the
  hand's last round only if that round began after the last decrease
  (`pins()`: `pinnedSets`, `roundSets`), else to the low watermark, and
  the trigger is computed from those pins likewise. The decrease ends
  when the thread's batches end (the budget reached, or two rounds of the
  hand without freeing anything: the 015-10 rule) unless another
  decrease came meanwhile, or when a round that began after it found
  pinned bytes above the budget: then the budget cannot be reached, and
  the trigger, raised by those pins, applies again, so that readers'
  loads do not keep the thread running. Javadoc of `decrease`, `pins()`,
  `setBudget(Db, long)`, `EvictorRun` and the comments in `sweep`;
  `releases/next.md`.
* Test: `Eviction.testLoweredBudgetAfterPinsFell` (unit group), R4's
  probe made a test: 500 puts with nodes of 8 entries and a startup
  distance of 2,000; the budget lowered to 1 (pins P0 = 3,878), raised, a
  transaction that writes the dirty nodes (pins P1 = 3,016); the test
  then evicts detachable objects, as a batch does, until the resident
  bytes are at most P0, the state R4's probe reached through the thread
  (made directly, as the hand's position decides whether the thread's
  batches reach it); the budget lowered to (P0 + P1) / 2 = 3,447. Before
  the fix 3,703 bytes stayed (trigger 4,740), after it at most the budget,
  the thread idle and the decrease ended; then a budget of P1 / 2, below
  the pins: the decrease ends and the thread waits. About 0.1 s.
* P1 to P12 (010-01): no new thread, timer, wait or setting (the
  decrease's batches are the ones 005-52 promised; their end is the
  015-10 rule or a round's pins); P3: a decrease that cannot be reached
  costs at most two rounds of the hand (the one in progress and one that
  began after it). The stream's bytes are
  unchanged (eviction does not write).

2026-11-06. Review R7 of 006-13 (019-41): OK, but the test pinned only
`pins()`. Since 019-41 it also asserts that, with the budget lowered to
1 byte, below the pins, the thread goes idle after few batches (2 to 4):
without `sweep`'s end of a decrease it ran about 17.5 million empty
batches in a second, each taking the write lock, and the test passed.
`goal()` (the budget, not the trigger, during a decrease) has no failing
test: in this fixture a batch that counts with stale pins goes to the
low watermark anyway; it matters only when the decrease's batches are
cut short (BATCH, BATCH_NANOS, a waiting writer) while a round that began
after the decrease ends with pins between budget - (high - low) and the
budget.
