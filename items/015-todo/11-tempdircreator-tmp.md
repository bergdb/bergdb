015-11. Fix: the tests' TempDirCreator writes to /tmp, whatever java.io.tmpdir says
===================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

Not for 2026.2 unless cheap; a test tool.

What: `bergdb.nanotest.TempDirCreator` uses `/tmp` when it exists, and
ignores `java.io.tmpdir`. On s1, `/tmp` is a 1.9 GB tmpfs, and
`BryanIssueNight` fills it ("No space left on device"), so the night
tests cannot run there unless `/tmp` is bound elsewhere (016-08,
`08-tests/results.md`).

Done when: TempDirCreator takes `java.io.tmpdir` (whose default on Unix is
`/tmp`), and the night tests pass on s1 with it set to the disk.

Found 2026-11-03 by 016-08's runs on s1.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. `TempDirCreator` makes its directories
in the directory that `java.io.tmpdir` names (its default is `/tmp` on
Linux; on macOS a directory of the user's under `/var/folders`), and in
the current directory, as before, if that is not a writable directory.
`-Djava.io.tmpdir=DIR` on the test JVM now moves the tests' databases, such
as `BryanIssueNight`'s, off s1's 1.9 GB tmpfs.

* Test: `TempDirCreator.testUsesJavaIoTmpdir` (unit), the parent of a
  temporary directory is `java.io.tmpdir`. Before the fix on F53: "the
  parent of a temporary directory, expected
  '/private/var/folders/.../T', got '/private/tmp'"; it passes after, also
  with `-Djava.io.tmpdir` set to another directory.
* On F53 the unit tests and the f-tests now write under `/var/folders`
  instead of `/tmp`: the same volume. No script cleans `/tmp/temp-bergdb-*`.
* Not done tonight: the night tests on s1 with `java.io.tmpdir` on the disk
  (the "Done when"'s second half); nothing runs on s1 tonight (006-12, W3).
  The next run of the night tests on s1 sets it, as 016-08's runs would.
* 010-01: no setting (a JVM property that exists), no global state. Not
  the database's code; the stream's bytes are unchanged.
