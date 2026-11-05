015-27. Decide: a failed append's transaction was already visible to readers
============================================================================

Status: done (decided 2026-11-05: intended, not a fault). Kind: Decide.
Created 2026-11-03 by Frans Lundberg.

For Frans: which side to change (recommendation in 016-02).

What: A get that runs while a put's append fails can see the put's values before the failure; `docs/levels.md`, section 3, says that a transaction is visible only after it is stored. One of the two is wrong: the code or the text.

Source: review R3, R3-F8 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F8), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F8, made a test.


The options
-----------

For release 2026.2 the text was corrected (Frans, 2026-11-04, 07:39, on
016-02's item 6): `docs/levels.md`, section 3, says what a read may see of
a transaction that fails after its go point. The question left was the
code, as presented on 2026-11-05:

* **(a) Intended; keep the code.** A transaction's time becomes a lookup
  time when its changes are in memory (`dbClock.transactionEnd()`), before
  `store()` appends its record. A read in the window before a failure can
  return values that a restart then does not have. That is the same class
  as a read of any transaction that is not synced: BergDB makes a
  transaction visible before it is forced (015-85), and only `sync()`
  promises durability. Nothing changes in `java/`; `docs/levels.md` says
  that it is intended.
* **(b) Visible only after `store()`.** Move `transactionEnd()` after the
  append. A change of the writer's protocol, with little gained: `store()`
  appends to the in-memory buffer, so a later flush can still fail after
  the read, and the guarantee is still only `sync()`'s.

Recommended: (a).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, 10:47. Frans, to session bergdb-e8: "27 as recommended, this
is intended, durability is handled separately." Option (a): the behaviour
is intended and not a fault; `docs/levels.md`, section 3, says so. Done;
nothing in `java/` changed. Out of 018-01's list of the Core's faults.
