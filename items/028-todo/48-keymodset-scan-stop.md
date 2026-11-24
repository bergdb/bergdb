028-48. Change: KeyModSet's modifiedAfter stops at the bin of the read time
===========================================================================

Status: done. Kind: Change. Frans: none.
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


Result
------

2026-11-24, by an agent of lead-1124, on the branch `028-48`.

* `KeyModSet.modifiedAfter` reads the bins from the newest to the first
  that begins at or before the read time, and no further (`endBin` with
  `stop`). A bin older than that one holds only times at or before that
  one's first time: the adds come in time order, and a bin begins at or
  after the last add before it (`add`, `forgetUpTo`). The full scan of
  before this entry stays as `modifiedAfter(time, hash, false)`, for the
  tests and the probe only. `pairsScanned` (028-01) counts as the new
  scan; the probe's table of 028-01 is unchanged, as it reads at the
  set's first time, where every bin is read.
* `testScanStopSameAnswers`: the cases of 028-01's `testSpreadSameAnswers`
  (adds, `forgetUpTo` cuts, sizes 8, 400 and 128,000), read before the
  first time, at each bin's first time, one before and one after it,
  inside each bin, and at and after the last add; the new scan gives the
  full scan's answers and never reads more bins. In all it read 185,992
  bins, the full scan 308,631. A scan stopped one bin too early fails it,
  `testScanStopBinsRead` and `testForgetUpTo`.
* The bins read a lookup, `binsRead` (a count, not a time), in a full
  set of 128,000 sequential keys, a read time in the middle of a bin,
  mean of the keys (`testScanStopBinsRead` asserts the column for keys
  not added; the probe, `KeyModSet.main`, prints the table):

      read time in bin   key added: before  after   not added: before  after
      0 (newest)                       3.6    1.0                 4.0    1.0
      1                                3.0    1.7                 4.0    2.0
      2                                2.6    2.2                 4.0    3.0
      3 (oldest)                       2.5    2.5                 4.0    4.0

  A commit's read of a key not recently written, the usual case, read
  all 4 bins whatever its read time; now the bins down to that of its
  read time, 2.5 on average over the four bins.
* The conflict check's answers do not change; the stream's bytes are not
  affected (`KeyModSet` is in memory only).

Gate: `java/before-commit.sh` in the clone printed `BEFORE COMMIT OK (66 s)`.


Log
---

2026-11-24. Registered by lead-1124, from 028-01's Result.

2026-11-24. Taken by an agent of lead-1124 (in progress), on the branch
`028-48`.

2026-11-24. Done by an agent of lead-1124 on the branch `028-48`: the scan
stops at the first bin that begins at or before the read time; the test
of the same answers as the full scan, the bins read counted (185,992 of
308,631 in the test); BEFORE COMMIT OK.
