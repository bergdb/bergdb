028-01. Measure: KeyModSet's bins and sequential keys
=====================================================

Status: open. Kind: Measure. Frans: none.
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


Log
---

2026-11-13. Registered by coord-1113, from 026-10's Q2.
