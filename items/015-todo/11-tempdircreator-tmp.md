015-11. Fix: the tests' TempDirCreator writes to /tmp, whatever java.io.tmpdir says
===================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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
