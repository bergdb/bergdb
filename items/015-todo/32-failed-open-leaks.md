015-32. Fix: an unchecked failure during an open leaks handles; an Error keeps the lock
=======================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: An unchecked exception or Error (such as `OutOfMemoryError`) while a `FileStream` opens leaks file descriptors; after an Error the directory stays in `LOCKED_DIRS`, so a reopen is refused until the JVM ends. Rare; no data lost. The leak is in 2026.1 too, the lock is new (005-63).

Source: review R2, R2-F3 (items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R2-F3), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R2-F3, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. R2's probe (R2/FailedOpenProbe.java,
the same injection: a `FileStreamIo` whose force of a file being opened,
`Force.OPEN`, throws) made `FileStream.testFailedOpenClosesFileAndUnlocks`,
which checks the three kinds in turn: the opened file is closed, and a new
`FileStream` on the directory starts. Before the fix: "the file is closed
after an unchecked exception, expected false, but was true"; with only
`openForRw`'s part of the fix: "the directory is locked after an Error".

* Fix: `FileStream.openForRw` closes the file it opened whatever its force,
  directory force or read channel throws (it closed it after an
  `IOException` only), and fails the stream (`ioException`) after an
  `IOException` only, as before. The constructor runs
  `closeAfterFailedOpen` for an `Error` too, so the directory leaves
  `LOCKED_DIRS` and its lock file is released.
* 010-01: no setting, thread or format change; the stream's bytes are
  unchanged.
