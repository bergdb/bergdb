028-11. Fix: texts that disagree with the code, found by 027-11
================================================================

Status: open. Kind: Fix. Frans: P5 only.
Created 2026-11-13 by Frans Lundberg.

What: five texts that the review of 027-11 (Startup) found to disagree
with the code at 7e190010; the code is right in each (027-11, section 9,
"Found while writing"):

* 027-03, lines 415, 1116 and 1234: the creation as 264 bytes; it is 272
  (`Db.CREATION_LENGTH`, since 024-25).
* `java/stress/level1.sh`, lines 2 to 3 and 29 to 30: "startup always
  replays the whole stream"; since 005-49 the startup pos moves also
  below sd (027-11, section 1.11).
* 019-45, line 56: "the maps are garbage when the start returns"; Rule
  R's copy of newById stays (027-11, section 2). An item is history: a
  dated note, not an edit.
* `NodeCollection.java`, line 784, `linkToCanonical`'s Javadoc names
  only an `AssertionError` with 'check'; it also throws a
  `StreamFormatException` (027-11's comments list, item 10).
* 010-01, `01-principles.md`, line 357, P5's "Where BergDB stands": T3
  "not yet" for BergDB's own take; `T3_take` proves it since 007-08.

Why: 027 with Lean is the authority for the exact rule; texts that
disagree mislead the next reader (Frans, 2026-11-13, 11:09 and 13:01).

Frans: the P5 line only. Principles are edited only when Frans says so
(010-01); the entry proposes the sentence and Frans decides. The rest:
none.

Done when: the four texts say what the code does (027-03 corrected,
`level1.sh`'s header corrected, a dated note in 019-45, the Javadoc
fixed), `java/before-commit.sh` prints `BEFORE COMMIT OK` for the Java
comment, and P5's sentence is proposed to Frans in this entry.

First step: read each line on main.


Log
---

2026-11-13. Registered by coord-1113, from 027-11's review.
