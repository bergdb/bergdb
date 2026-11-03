015-35. Fix: a failed background write does not fail the database until a caller touches storage
================================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: When the buffer's consumer fails to write (a disk error), the database does not fail until a caller's call meets storage; a workload of reads served from memory goes on, and returns a transaction that a restart will not have. Against 010-01, P7; docs/levels.md, section 3 lists only failures met by a call. Normal use.

Source: review R3, R3-F10 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F10), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F10, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
