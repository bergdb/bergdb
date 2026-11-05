015-74. Fix: metaBlock's format comment: the last byte is 10, not 1, and the version is read as 2 bytes, not an int
===================================================================================================================

Status: done. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R6's finding R6-F3 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F3: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies it and fixes the comment.

2026-11-05. Done, by session bergdb-e8's agent. Verified in the code
(016-06, R6-F3): `META_BLOCK_LAST_BYTE` is 10; `initBlock` writes the
version with `intToBytesLE` at offset 4, and `MetaBlock.getVersion` and
`RecoverableStream.readMetaBlock` read it with `bytesToUShortLE`, so bytes
6 and 7 are written as 0 and never checked. MetaBlock's format comment now
says so: offset 4, 2 bytes, the version as an unsigned short; offset 6, 2
bytes, zero, not checked; the last byte 10. A comment only, so no test
fails before it. Left: R6-F3's optional code change (`readMetaBlock` reads
the 4 bytes and refuses nonzero bytes 6 and 7), a decision for Frans.

2026-11-05, 10:47. Frans, to session bergdb-e8, on the optional code
change: "74, as recommended": registered as 019-01, for harness 6.1's
class (018-01, section 6.1).
