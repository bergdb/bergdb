019-40. Fix: review R6's C findings: tests, words, small faults of the error model's change
==========================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: review R6 of 006-13 (`/Users/f/fl/bench/006-13/review-r6.md`,
C1 to C9) found, beside its B findings (019-38, 019-39):

* C1: an `Error` under the write lock before the go point is recorded
  after the lock is released, unlike 015-66's order.
* C2: five new paths of 01b0493 have no test; with all five taken out,
  `before-commit.sh` still printed OK.
* C3: `DbTesterFailure.assertRefused`'s message does not name the case.
* C4: words: where an `Error` does not fail the database (the Pub API's
  conversion, setters), "any call" in `releases/next.md` and 010-P7,
  "began" undefined, and the cut's thread fails the stream, not the
  database at once.
* C5: the index deletion job says "Done!" after a failure.
* C6: `Db.getOneInternal` is public.
* C7: harness 6.2 counts only the fault's own `Error` as a failure.
* C8: 019-34's check could be the invariant it relies on (`firstPos <=
  spos < block.getPos()`), and its `< META_BLOCK_SIZE` branch is
  untested.
* C9: a comment line of 137 characters (`Residents.java`, about line
  191).

Why: the error model is part of the interface (Frans, 2026-11-06:
"Important that the database user understands the error model."), and a
path without a test can break unseen.

Frans: none. Each as R6 suggests, the simplest way (KISS, 010-P13); C6
only if making it non-public is a small change (else words); C5 may
overlap 015-61 (experimental), then a line there.

Done when: each C finding fixed or answered in this entry with a reason;
the five paths of C2 tested (each test fails with its hunk taken out);
`BEFORE COMMIT OK`.

First step: R6's C1 to C9. After 019-38 and 019-39 have landed (the same
files).


Log
---

2026-11-06. Registered by coord-1106 from review R6.
