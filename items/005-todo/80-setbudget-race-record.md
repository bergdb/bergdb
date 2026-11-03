005-80. Decide: the record and a test of setBudget's race, fixed inside 005-65's commit
======================================================================================

Status: open; option B taken under D2 (016-01, section 10) and planned
for release 2026.2 (see Plan for 2026.2). Kind: decide. Created
2026-10-29.

Registered at Frans's request (2026-10-29, 15:51: "Add an entry for "The
setBudget split" since I want to finish and I don't remember this one.").
Registered only.


The issue
---------

005-65's fix (`988fe1a`, in `main` and pushed, 2026-10-29) also fixed a
race of 005-52's `setBudget`, found while writing out the eviction
thread's protocol. One line of that commit, in `Eviction.sweep`:

* Before: a batch computed the new trigger,
  `trigger = Math.max(high, pinnedOfLastRound + (high - low))`, outside
  the monitor that `setBudget` holds while it writes `high`, `low` and
  `trigger`. A batch that ended while `setBudget` lowered the budget could
  write a trigger from the old budget after `setBudget` had written the
  new one.
* The effect: the trigger stays at the old, higher budget. Loads wake
  the eviction thread only when the resident bytes pass the trigger, so
  after a decrease the bytes could stay above the new budget until they
  passed the old one, or until another batch computed the trigger again;
  an idle database would not give the memory back. That is what 005-52's
  `setBudget(Db, long)` wakes the thread for.
* Now: the trigger is computed inside the `synchronized (this)` block that
  ends the batch, so `setBudget` and the batch write it one after the
  other; the comment at the line says why.

Three things are not done: the fix is not recorded in 005-52 (only in
988fe1a's message and the comment); no test forces the interleaving (005-65's
tests are of the lost request, not of this race; the race was found by
reading); and it is not a commit of its own. In the 006-10 session Claude
offered to split it out of 988fe1a; Frans did not answer then.


Options
-------

A. Nothing more than this entry: the fix is in `main`, with its comment,
   and this entry records it.

B. A record and a test: a line in 005-52's Outcome; a test in
   `Eviction`'s tests that forces the interleaving (a batch that ends
   while `setBudget` lowers the budget, with a hook or a latch as
   005-67 forced its interleavings), and fails on the code before
   988fe1a. Test code only; StreamDigest unchanged (the cache size changes
   no byte).

C. A commit of its own: not possible without rewriting `main`, which is
   pushed. Not proposed.

Recommended: B, small (S), when 005-52's pause probe is done or with it,
as both are about a lowered budget.


Done when
---------

Frans has chosen; for B, the line in 005-52, the test failing on the code
before 988fe1a and passing after, and `java/before-commit.sh` printing
`BEFORE COMMIT OK`.


Plan for 2026.2
---------------

Written 2026-11-03 for 016-05 (W4). Option B, the entry's recommendation,
taken with Frans's D2 (016-01, section 10: "D2. As you recommend unless I
say otherwise here."): the record in 005-52 and a test that forces the
interleaving.

The race, written out (the code before `988fe1a`): the batch's last
statement, outside the monitor, was `trigger = Math.max(high,
pinnedOfLastRound + (high - low));`. The batch reads `high` and `low` (the
old budget's); `setBudget` writes `high`, `low` and `trigger` (the new
budget's) under the monitor; the batch then writes its `trigger`, the old
budget's. The window is that one statement, so no hook before or after it
can force it: the test needs a point between the computation and the
write.

The steps, by agent F1 (016-05), after 005-69, in
`/Users/f/fl/bench/016/005-80/repo` (a new clone of `main`):

1. **The hook** (0.2 hours), `java/src/bergdb/core/Eviction.java`:
   * A package-private instance field `Runnable testBeforeTrigger`, null
     except in the test. An instance field, not a static one (010-P9).
   * In `sweep`'s `synchronized (this)` block, the trigger's line becomes
     three: `final long t = Math.max(high, pinnedOfLastRound + (high -
     low));`, then the hook if it is set, then `trigger = t;`. One field
     read a batch (a batch is up to 2 ms); no change in what is computed.
2. **The test** (0.4 hours), `Eviction.testSetBudgetAtBatchEnd` (unit),
   beside `testNoLostRequest`:
   * A database on a `MemoryStream` with the capacity controller
     (`Schedule.BUDGET`) and a budget B0 (1 MB), a few hundred values.
   * The hook starts a thread that calls `setBudget(B0 / 4)` and waits
     for it at most 200 ms (`join(200)`), recording whether it finished.
   * The test runs one batch itself: `synchronized
     (db.internal().getWriteLock()) { e.sweep(db, false); }` (a batch's
     caller holds the write lock; the eviction thread's batches take it
     too, so none runs beside it). Then it joins the thread.
   * Asserts: the trigger is `B0 / 4` (what `setBudget` wrote last), and
     the thread did not finish inside the hook (`setBudget` waited for the
     batch's monitor). The hook set back to null; the database closed.
3. **The check against the code before `988fe1a`** (0.2 hours): a
   mutation in the clone, the three lines of step 1 moved out of the
   `synchronized (this)` block, before it, as the line was before
   `988fe1a`. The test must fail: `setBudget` finishes inside the hook,
   and the batch then writes the old budget's trigger (B0 or more). The
   agent runs the unit test on both, records the two outcomes in the Log,
   and reverts the mutation (`git diff` shows only steps 1 and 2).
4. **The record** (0.05 hours): a bullet in 005-52's Outcome: "Fixed in
   `988fe1a` (005-65's commit, 2026-10-29): `Eviction.sweep` computes the
   trigger under the monitor that `setBudget` holds. Before, a batch that
   ended while `setBudget` lowered the budget could put back the old
   budget's trigger, and the decrease then waited until the resident bytes
   passed the old budget or another batch ended (005-80). Test:
   `Eviction.testSetBudgetAtBatchEnd`." Agent F2 edits 005-52 too (its
   Plan and runs): the coordinator applies the two hand-offs in turn
   (`git apply --3way`), as they touch different lines.
5. **The gate**: `java/before-commit.sh` (`BEFORE COMMIT OK`). If it fits:
   `java/stress/level4.sh quick` (about 4 minutes; the eviction tests, and
   EvictionInvariance, which shows that the cache size changes no byte).
6. **The review** (016-05, section 5): 0.5 hours of another agent, given
   the interleaving above, the diff and the mutation; the answers here, in
   the Log.
7. **The hand-off** (016-05, section 4), Status "done (2026-11-0x)".

Size: about 1.5 agent-hours, the review's included. Depends on nothing in
the code; its line in 005-52 meets F2's edits of that file (step 4). No
stop for Frans. Done when the line in 005-52, the test failing on the
mutation and passing on `main`, and `BEFORE COMMIT OK` are in place.

**State** (2026-11-03): planned, not started. Read at `df6ad50`:
`Eviction.setBudget(long)` and `setBudget(Db, long)`, `sweep` (the
trigger's line under `synchronized (this)`, with 005-65's comment), the
fields `high`, `low` and `trigger` (volatile), the callers of `sweep`
(the eviction thread's run under the write lock), and `988fe1a`'s diff.


Log
---

2026-11-03. Option B planned for release 2026.2 (016-05), with a test hook
between the trigger's computation and its write. Nothing changed yet.
