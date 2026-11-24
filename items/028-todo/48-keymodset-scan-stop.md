028-48. Change: KeyModSet's modifiedAfter stops at the bin of the read time
===========================================================================

Status: open. Kind: Change. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: `KeyModSet.modifiedAfter(time, hash)` (java/src/bergdb/core/KeyModSet.java),
which a commit's conflict check calls for each key it read, sets `endBin`
to the last bin whose first time is at or before `time` and reads the
key's sub-array in every bin from the newest to that one. The bins are
ordered newest first, so every bin after the first one that begins at or
before `time` holds only times before its start, none after `time`; the
scan could stop at that first bin.

Why: found by 028-01 on the way (its Result). A cost of commits whose
read time is old enough to be covered by more than one bin: today they
read every bin down to the oldest. Not a fault: the answer is the same.

Frans: none.

Done when: `modifiedAfter` reads the bins from the newest to the first
that begins at or before `time`, and no further; a test that compares
its answers with the full scan's on the cases of 028-01's
`testSpreadSameAnswers` (adds, `forgetUpTo` cuts, sizes 8, 400 and
128,000, read times in every bin, before the first and after the last);
the bins read counted before and after (a count, not a time);
`java/before-commit.sh` prints `BEFORE COMMIT OK`.

First step: read `modifiedAfter`, `Bin.getTime` and `forgetUpTo`, and
028-01's tests and probe.


Log
---

2026-11-24. Registered by lead-1124, from 028-01's Result.
