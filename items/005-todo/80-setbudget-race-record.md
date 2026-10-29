005-80. Decide: the record and a test of setBudget's race, fixed inside 005-65's commit
======================================================================================

Status: open. Kind: decide. Created 2026-10-29.

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
