015-33. Fix: setMax2G(true) still allows files over two billion bytes
=====================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `FileStream.setMax2G(true)` can still make a file larger than 2^31 bytes. Internal only: nothing in `java/src` calls it.

Source: review R2, R2-F4 (items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R2-F4), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R2-F4, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StreamContractTester.testFileStreamSizeLimit` makes
R2-F4's directory directly, with sparse files, in 0.07 s, and fails and
names 015-33 (a file of 2,100,000,000 bytes). Its fix removes the skip
line "015-33" from `StreamContract.SKIP`.
