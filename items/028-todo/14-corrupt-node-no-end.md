028-14. Investigate: a damaged node with its checksum right, and a start that does not end
=========================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-15 by Frans Lundberg.

What: `java/night.sh` on `main` 584c73af (2026-11-15, 11:17 to 14:04)
failed one step, the night tests: `CorruptStreamTester.testFull` (harness
6.1 of 2026.3, 018-01) found one damaged copy whose start or reads did not
end within 60 s:

    1 copies failed, the first: long, seed 3971544, node, xor 1 at its
    byte 49, checksum right, of the node at offset 96 (size 96, type 10)
    of the record at 43440: the start or the reads did not end in 60 s

`NanotestForBergDB.databasesStopped` failed after it, as that copy's
database was left going. Every other step of the night run passed: levels
1 to 4, count gates, Lean tests, tree tests, harness soak, fuzz, unlink
fuzz, 1,000 kills, conformance. Report:
java/build/night/2026-11-15-1117/report.txt.

The failure repeats: a rerun of the test alone in a fresh clone of `main`
(14:12, load average about 8) failed on the same copy. The test's seed is
the day's number (20772 for 2026-11-15), so tomorrow's night run tries
other copies; to repeat this one:

    java -ea -cp java/build/bergdb.jar bergdb.core.CorruptStreamTester 20772 full 4

Why: the harness counts a start or a read that does not end as a fault,
also for damage beyond a torn tail, where detection itself is best effort
(Frans, 2026-11-12: detecting damaged bytes is best effort, low priority).
A damaged node whose checksum was made right may point the start's or a
read's walk in a loop. To find: where the walk does not end (a cycle of
node pointers, or a loop that waits), and whether a bound on the walk (the
fuel, as the Lean model's) or a check makes it end with a DbException.
Then a Fix entry, or KNOWN in the harness if Frans decides so.

Found by coord-1115 (006-27); no work started.
