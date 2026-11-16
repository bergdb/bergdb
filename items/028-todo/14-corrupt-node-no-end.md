028-14. Investigate: a damaged node with its checksum right, and a start that does not end
=========================================================================================

Status: done. Kind: Investigate. Frans: none.
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


Result
------

Found: a read, not the start, did not end. The start of the damaged copy
succeeded; a get at a time before the damaged top node's looped in the
walk of `TopDs.findSuperRootAtTime` (`java/src/bergdb/dag/TopDs.java`,
the `while (true)` loop, lines 173 to 180 at 13beb100), which follows the
top nodes' skip pointers. A thread dump of the hung check (a probe that
made the copy and dumped the stack after 20 s) showed the get in that
loop, at `TopDs.java:179`, the follow of a skip pointer.

The damaged node: the top node at offset 96 of the record at 43440
(position 43536), ordinal 5, its skip pointers 0 and 2 at 43792 (time
330) and 43712 (time 250). The xor of 1 at its byte 49 changed skip
pointer 0's position by 256, to 43536: the node's own position. The walk
takes the right-most skip pointer whose cached time is at least the
lookup time; for a lookup time at most 330 it was pointer 0, which led
back to the same node, without end. Nothing checked where a skip pointer
leads but the type of its node (`NodeCollection.checkPointeeType`).

The fix (the smallest, one comparison a step of the walk, none on a get
at the newest time): `TopDs.skipTo`, used by both follows of the walk,
requires the top node a skip pointer names to have a smaller ordinal
than the node it is followed from, as every valid skip pointer has (it
names the newest top node before it whose ordinal has the pointer's bit
clear: TopDs.newSuperRoot). Otherwise it throws the follower's `cycle()`,
in a Db a `StreamFormatException`, so the get fails the database
(`Db.readFailed`, a `DbFailedException`), as for the key nodes' cycle of
`OpData.descentTo` (2026-11-10). The ordinal strictly falls each step, so
the walk ends on any stream. The start is not changed; no other code
walks the skip pointers.

The test: `CorruptStreamTester.testFoundTopCycle` makes the copy of the
night (seed 20772, LONG) and asserts it is checked without a failure, as
"node: read failed". Without the fix it failed (the check did not end in
60 s, and `databasesStopped` after it); with the fix it passes.

The harness after the fix, `CorruptStreamTester <seed> full 4`: seeds
20772, 20773 and 20774, 0 failures each (20772's copy now "node: read
failed (DbFailedException)").

Gates: `java/before-commit.sh`: BEFORE COMMIT OK (107 s);
`java/stress/level2.sh quick`: LEVEL 2 OK (the change does not touch
the start; run for its gets). Code commit: 95ba757b.


Log
---

2026-11-15. Registered by coord-1115 (006-27).

2026-11-16, 11:02 to 11:31. Done by an agent of coord-1116, in a clone
on branch 028-14-corrupt-no-end: repeated (the get looped in
TopDs.findSuperRootAtTime), fixed (TopDs.skipTo), tested and gated.
