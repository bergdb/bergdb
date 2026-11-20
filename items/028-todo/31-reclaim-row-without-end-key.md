028-31. Fix: text about a reclaim row without an end key
========================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: 027-13, section 1.4, step 1, says "(to the last key for a row stored
without E, before 026-05)", and `Reclaim.step`'s Javadoc
(java/src/bergdb/core/Reclaim.java, around line 794) says a row stored
before 026-05 has no end key and its scan is not bounded. Since 028-15 a
reclaim row without an end key is refused as damaged
(`IterationInfo.deserialize`), so no such row reaches a step. Found by
030-25 while checking Java against 027-13.

Why: 027 documents the code (027-04's decision); a sentence about a case that
cannot happen misleads.

Frans: none.

Done when: 027-13 and the Javadoc say what the code does since 028-15, the old case
as history; `java/before-commit.sh` BEFORE COMMIT OK (comments only).

First step: The two places above; grep for other mentions of a row without an end
key.


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.

2026-11-20. Taken by tx of coord-1120, on the branch `028-30-31-texts`.

2026-11-20. Done by tx of coord-1120: 027-13, section 1.4, step 1, and
`Reclaim.step`'s Javadoc say that every row has its end key and that
`IterationInfo.deserialize` refuses a row without it since 028-15, the
row without it of before 026-05 as history; 027-13, section 9, adds that
a reader of 2026.5 or earlier refuses a stream of meta version 155
before it reads a row. A grep of `java/`, `lean/` and 027 found no other
text of such a row as today's: 027-03, section 15, and
`IterationInfo.endKey`'s comment already said it. Comments only.
