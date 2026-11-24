028-01. Measure: KeyModSet's bins and sequential keys
=====================================================

Status: done. Kind: Measure. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: `KeyModSet` (java/src/bergdb/core/KeyModSet.java), the set of recent
writes that a commit's conflict check reads (`Db.stmCheckConflicts`,
`modifiedAfter`), puts a key's hash in a sub-array by the hash modulo
8,000. `Keys.hash` mixes a key's 8-byte segments by `* 37 +`, so
sequential keys such as CountGates' `/k/%010d` fall in few sub-arrays: 507
of 32,000 in G5, about 250 pairs each (026-10, section 2). `modifiedAfter`
scans the sub-array of each key a commit read, so such a commit scans
about 250 pairs a bin for each key instead of a few.

Why: found by 026-10 on the way (its Q2; Frans, 2026-11-13, 11:32:
"Yes" to a 028 entry). A cost of commits that read many sequential keys;
not a fault.

Frans: none.

Done when: the pairs scanned a key are measured before and after (a
count in a test or a probe, for sequential and random keys), and a hash
that mixes the bits before the modulo (for example a 64-bit finalizer of
the hash) makes the sub-arrays even for sequential keys, with no change
of the conflict check's answers; `java/before-commit.sh` prints `BEFORE
COMMIT OK`. Or the measurement shows the cost does not matter, and the
entry says so and closes.

First step: a probe that fills a `KeyModSet` with the hashes of 128,000
sequential keys and of 128,000 random ones and prints the largest and
mean sub-array sizes.


Result
------

2026-11-24, by an agent of lead-1124, on the branch `028-01`.

The probe, `KeyModSet.main` (`java -cp java/build/bergdb.jar
bergdb.core.KeyModSet`), fills a `KeyModSet` of 128,000 pairs (4 bins of
8,000 sub-arrays) with the hashes of 128,000 keys of three kinds, with the
sub-array index before this entry (modulo) and after it (mixed), and
counts the pairs that a lookup scans (`pairsScanned`, as `getTime`
scans: each slot of the key's sub-array in each bin read, up to the
match) at the set's first time, when every bin is read. Counts, not
times; a mean of pairs scanned is in tenths, as the Core's code has no
floating point (005-79):

    keys          index   sub-arrays  largest  mean   scanned, added: mean  most   not added: mean  most
    sequential    modulo         500      266   256                  698.2  1792            1523.5  1792
    sequential    mixed        31441       15     4                   10.7    47              20.5    48
    random /k/    modulo         500      301   256                  694.1  1825            1509.3  2048
    random /k/    mixed        31460       13     4                   10.7    43              20.5    48
    random bytes  modulo       31362       15     4                   10.6    44              20.5    48
    random bytes  mixed        31416       14     4                   10.7    45              20.5    48

* "sequential" is `/k/%010d` from 0, "random /k/" the same format with
  random numbers, "random bytes" two random 8-byte segments.
* Before: keys of the form `/k/%010d`, sequential or random, fell in 500
  of the 32,000 sub-arrays, 256 pairs each; a lookup of a key not
  recently written, the usual case of a commit's read, scanned about
  1,500 pairs. So the cost was not only that of sequential keys: any keys
  that differ only in a few bytes of a segment's digits. Keys of random
  bytes were spread already.
* After: `KeyModSet.subIndex` mixes the hash with MurmurHash3's 64-bit
  finalizer (fmix64) before the modulo; every kind uses about 31,400
  sub-arrays, at most 15 pairs, and a lookup scans about 21 pairs, 48 at
  most: 74 times fewer than before for `/k/%010d` keys.
* Only the sub-array index changed. `Keys.hash` is as before, and a bin
  finds a pair by its whole hash, so the conflict check's answers do not
  depend on the index. `KeyModSet.testSpreadSameAnswers` checks it: two sets,
  one with each index, given the same adds and cuts (`forgetUpTo`), at total
  sizes 8, 400 and 128,000, give the same `modifiedAfter` and
  `getFirstTime` for sequential and random hashes.
  `testSpreadSequentialKeys` asserts the counts of the table's first two
  rows (bounds, not times).
* The stream's bytes do not change (P2): StreamDigest `quick`, with the
  stress classes of the build of `e1f42edb` against that build's jar and
  against the branch's, printed `DIGESTS IDENTICAL (44 of 44; of the
  identical, the physical cut differs in 0)`.
* Found on the way, not changed: when the read time is covered,
  `modifiedAfter` reads every bin down to the oldest, while the bins
  older than the first that begins at or before the read time hold no
  time after it; it could stop there.

Gate: `java/before-commit.sh` in the clone printed `BEFORE COMMIT OK (99 s)`.


Log
---

2026-11-13. Registered by coord-1113, from 026-10's Q2.

2026-11-24. Taken by an agent of lead-1124 (in progress).

2026-11-24. Done by an agent of lead-1124 on the branch `028-01`: the
probe, the sub-array index of a mixed hash, the tests of the counts and
of the same answers; StreamDigest identical; BEFORE COMMIT OK.
