005-61. Fix: reclaim uses the database's startup distance
=========================================================

Status: done (2026-10-27; see Outcome). Kind: fix. Created 2026-10-27.

Found in [005-53](53-startup-distance-on-the-fly.md), question 3
("Reclaim's startup distance"), by Claude (Opus 5.5, Claude Code);
registered and fixed at Frans's request (2026-10-27, 006-09: "Fix 005-53's
Reclaim fault").


The issue
---------

`Reclaim` spaces its iterations by the startup distance: an iteration
starts only when the stream has grown by twice the distance since the last
one started, and a quarter of the retain duration has passed
(`Reclaim.transactionCompleted`). But the distance it uses is a copy, the
final field `initialStartupDistance`, made in `Reclaim`'s constructor when
`Db`'s constructor makes the `Reclaim`. That is the builder's value. Later:

* `Db.start` reads the stream's last valid meta block and sets `Db`'s
  distance to the stream's (`handleStartParams`), as `DatabaseBuilder`'s
  Javadoc says; `Reclaim` keeps the builder's: the Pub API's default 50 MB,
  or what the opener passed.
* `Db.setStartupDistance` changes `Db`'s field and the meta block, not
  `Reclaim`'s copy.

No wrong cut follows: every cut is guarded by live values (`pSafe`, the
last valid meta block). But iterations start too seldom or too often.
005-53's probe made a database at 2000 bytes and restarted it with the
builder's default: 1 iteration instead of 65, and 20 times the stream
kept. Made at 1000 MB (as 005-38 suggests for a large database) and opened
with the default, an iteration may start every 100 MB of growth instead of
every 2000 MB. The pattern is in the 2017 code (`0257e0b`).


The fix
-------

`transactionCompleted` reads `Db`'s live distance,
`db.getStartupDistance()`, instead of the copy, and the field goes. It runs
under the write lock, which guards `Db`'s field (`getStartupDistance`
takes it again, reentrant). The spacing then follows the stream's distance
and every later change.


Done when
---------

* `Reclaim` has no copy of the startup distance; a unit test from 005-53's
  probe: a database made at a small distance, restarted with the default
  builder, reclaims as at its own distance; and one for
  `setStartupDistance`. Both fail on the code before.
* StreamDigest (P2): the standard tests' streams, before and after;
  identical or explained.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `java/stress/level3.sh`
  (reclaim's level) passes.


First step
----------

The one-line change in `transactionCompleted`, and the probe's third run
as a test.


Size and order
--------------

S. Before 007-03's step 3 and 006-06, which change the distance while the
database runs.


Outcome
-------

2026-10-27, by Claude (Opus 5.5, Claude Code), at Frans's request (006-09),
in a clone on `e6dbc82`; the commit there is `59c6771` (java/ only).

* The change, as "The fix" says: `Reclaim.transactionCompleted` starts an
  iteration when `streamSize > lastPStart() + 2L * db.getStartupDistance()`;
  the field `initialStartupDistance` and its copy in the constructor are
  gone. The class comment's first point says that the distance is `Db`'s
  live value.
* The tests, in `Reclaim.Tester` (unit, 0.1 to 0.15 s each):
  * `testIterationsFollowTheStreamsStartupDistance`, 005-53's probe: a
    database made at 2000 bytes (2000 puts, retention 1 s) is restarted
    from copies of its stream, once with 2000 in the builder and once with
    the default; then 2000 more puts each. Both runs must complete the same
    iterations (21) and keep the same bytes of stream.
  * `testIterationsFollowSetStartupDistance`: made at 2000, then
    `setStartupDistance(400 000)` (the smallest allowed); in 2000 more puts
    (about 220 KB) no iteration starts.
  * The helper of both asserts, at every put, that an iteration starts
    only after more than twice `Db`'s distance of growth.
  * On the code before both fail: "Expected 21, got 1", and an iteration
    that started 224 KB after the last at a distance of 400 000.
* StreamDigest (P2): `StreamDigest all` (12 configurations, modes plain,
  reads, restarts), HEAD `e6dbc82` against the fix: "DIGESTS IDENTICAL (36
  of 36)". As expected: its restarts give the builder the configuration's
  distance, which is the stream's, and nothing in it calls
  `setStartupDistance`, so the copy and the live value were equal. A stream
  changes only where they differed: a database opened with a builder
  distance other than its own, or after a `setStartupDistance`, with a
  finite retention; there reclaim's internal transactions now come when
  the database's distance says.
* Gates, on `59c6771`: `before-commit.sh` "BEFORE COMMIT OK (89 s)" (1,048
  unit tests, 73 f-tests); `level3.sh` (full) "LEVEL 3 OK".

Files: [61-reclaim-startup-distance/](61-reclaim-startup-distance/):
`gates.txt` (both gates' output), `digest-head.txt`, `digest-fix.txt` and
`digest-compare.txt`.
