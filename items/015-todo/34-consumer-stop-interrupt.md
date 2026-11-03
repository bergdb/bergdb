015-34. Fix: a storage thread interrupted at its stop skips closing its stream
==============================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `BufferedStream`'s consumer, interrupted while it stops, returns before it closes the stream below: its files and the directory lock stay open. Reached through the Pub API only by the experimental `removeReplica` with an outside interrupt; `Db.stop`/`close` repair it.

Source: review R3, R3-F6 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F6), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F6, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
