015-73. Fix: a corrupt startupPos in the last record is accepted, and the transactions before it are lost
=========================================================================================================

Status: done (decided 2026-11-05: outside the fault model for 2026.3,
option (a)). Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too. A fix needs a design choice (a header checksum, a format change, or structural checks as 005-75).

What: review R6's finding R6-F2 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F2: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

Night 006-12, 2026-11-05
------------------------

Skipped tonight: the fix needs a design choice of Frans's (the entry says
so; 006-12, section 3), and the checks that would catch R6's probe need an
argument about the take's invariants beyond the obvious (006-12's brief).

What changed around it tonight:

* 015-75 refuses a startupPos that the take cannot have written:
  negative, not a multiple of 8, in the first meta block (only 0 is), or
  after its record's own position (`Db.checkStartupPos`; test
  `DbTesterRestart.testCorruptStartupPosRefused`). So a flip of a high bit
  is refused, and so is a position that is not a record start in most
  cases: since 015-72 a record's content must fill its size exactly.
* What is left is R6's probe itself: a startupPos that names the start of
  an earlier record that the take never reached. Records A, B and C at
  264, 384 and 472 (startup distance 1 MB, so the startup pos stays 0);
  C's startupPos set to 384. Checked tonight: B's got-dirty list is empty
  (A's holds nodes 1 and 0; B and C dirty no new index node), so R6's
  proposed check, "every got-dirty id of the section's first transaction
  has a version in the section after it", holds vacuously and does not
  catch R6's own probe. A check that does catch it must know which nodes
  were dirty at the section's first transaction: the got-dirty lists of
  the transactions between the previous startup pos and the new one, which
  lie before the section, so the start would read records it does not read
  now (the bounded startup, 007, reads only the section), and a take may
  move the startup pos over transactions whose lists are empty without
  writing an index node, so "the record that moved it wrote index nodes"
  is not an invariant either.

For Frans: how should a start treat a startupPos that names an earlier
record start the take never reached?

* (a) Outside the fault model, as damage other than truncation is best
  effort (018-01, section 6.1); the record header has had no checksum
  since 2015. 015-75's checks stay. 015-73 is closed as decided, and
  2026.3's notes say that a corrupt record header can lose data at a
  start that succeeds.
* (b) A check that reads back from the previous startup pos: the record
  that moved the startup pos to F holds a version of every got-dirty node
  of the transactions from the previous startup pos to F. No format
  change, but more reads at a start (records before the section, which
  the bounded startup, 007, does not read now) and a careful argument over eviction, reclaim's touches
  and cuts, and the decrease of the startup distance; at xhigh in a day
  session.
* (c) A checksum of the record header: a format change (RECORD_FORMAT 6;
  the header has three unused bytes, after the format byte), with Frans's
  approval, and the C clone (012) follows. It catches any corrupt header
  field, the time (005-75) and the size (015-72) too.

Recommendation: (a) for 2026.3, and (c) noted for the next change of the
record format, when its cost is shared with other changes. (b) costs the
most and protects against one field only.

2026-11-05, 15:35. Frans, to session bergdb-a2, which asked "do you take
(a), plus a 019 entry for (c)?": "Yes. Go ahead." Option (a): a
startupPos that names the start of an earlier record that the take never
reached is outside the fault model for 2026.3, as all damage other than
truncation is (018-01, section 6.1). 015-75's checks stay. Done; nothing
in `java/` changed. Out of 018-01's list of the Core's faults; harness 6.1
counts such a copy as known to pass undetected. 2026.3's notes
(`releases/next.md`) name it as a known limit. Option (c), a checksum of
the record header, is 019-07, for the next change of `RECORD_FORMAT`.
