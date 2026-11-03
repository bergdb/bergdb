015-08. Fix: StreamDigest's compare reports the physical cut, which depends on timing
=====================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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
