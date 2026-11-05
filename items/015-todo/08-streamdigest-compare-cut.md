015-08. Fix: StreamDigest's compare reports the physical cut, which depends on timing
=====================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

A tool's fault, not the database's.

What: `StreamDigest compare` also compares `firstPos` and `sha256all`,
the result of the physical cut. The cut waits for durability, so it
differs between runs of the same jar (005-72): the base jar gives
`firstPos` 8000000 or 9000000 in `l3-node62`. So a second run of the same
jar can print `DIGESTS DIFFER` (3 of 36 in 005-79's run, all in
`l3-node62`), although no decided byte differs.

Why: StreamDigest is the check that a change keeps the stream's bytes,
and 2026.2's digests become the release's reference (016-10, N8). A
compare that fails without a byte change makes the check useless, or
hides a real difference among false ones.

Done when: the compare checks only the decided digests (length,
`firstAvailablePos`, `firstAvailableTime` and `sha256`, as 005-79's
`digest-compare.py` does), and reports the physical cut's fields apart,
as information; two runs of one jar compare `DIGESTS IDENTICAL`.

First step: 005-79's `items/005-todo/79-integers-not-doubles/digest-compare.py`.

Found 2026-11-03 by the work on 005-79.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. `StreamDigest compare` checks only the
decided fields of each DIGEST line: `length`, `firstAvailablePos`,
`firstAvailableTime` and `sha256`, as 005-79's `digest-compare.py` does.
Where they are the same and the physical cut's fields (`firstPos`,
`sha256all`) differ, a line `PHYSICAL CUT ... (timing, not compared)` shows
them, and the summary counts them: `DIGESTS IDENTICAL (36 of 36; of the
identical, the physical cut differs in 3)`. A configuration whose decided
fields differ prints `DIFFERENT`, the fields that differ and both lines, as
before; a line missing from one file prints `MISSING` and counts as a
difference. The summary's first words and the exit status are as before.

* Test: 005-79's two outputs of jars that write the same bytes,
  `digest-base.txt` and `digest-a.txt` (its log: the physical cut differed
  in `l3-node62` only). Before: `DIGESTS DIFFER (3 of 36)`, exit 1; after:
  `DIGESTS IDENTICAL (36 of 36; of the identical, the physical cut differs
  in 3)`, exit 0. `digest-base.txt` against `digest-b.txt` (005-79's Part B,
  which changed `l3-node14`'s bytes) still prints `DIGESTS DIFFER (3 of
  36)`, exit 1. StreamDigest has no unit tests (`java/stress/`), so the
  check is these runs.
* Two runs of one jar (this tree, `l3-node62` and `l3-node14`, 4 modes
  each): `DIGESTS IDENTICAL (8 of 8; of the identical, the physical cut
  differs in 0)`; the cut did not move in these two runs, 005-79's pair
  shows the case where it does.
* 010-01: a tool only; no setting; the stream's bytes unchanged.
