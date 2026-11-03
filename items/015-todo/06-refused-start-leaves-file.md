015-06. Fix: a refused start leaves an empty first stream file
==============================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2, with 015-01.

What: `FileStream`'s constructor creates an empty `00000000000000.bergdb`
when the directory holds no `*.bergdb` file (`createDbFileObjects`,
`newFile()`), before the start has decided to create a database. A start
that is refused afterwards (an unknown crypto algorithm, for example, and
after 015-01 a directory with `created.txt` and no stream byte, if the
check were made later than the open) leaves that file behind.

Why it matters: a refused start must write nothing and create nothing, so
that the person can restore the files in place and start again (005-32).
An empty `00000000000000.bergdb` breaks the restore of a database whose
first file has another name: `FileStream`'s check of the files' positions
refuses the gap.

To verify first: a test that a refused start (the crypto case) leaves the
directory as it was.

Done when: a refused start leaves no new file; the test fails before the
fix and passes after; `BEFORE COMMIT OK`.

First step: write the test (016-01, section 6, the rule for findings:
verified by a failing test).

Found 2026-11-03 in 015-01's study.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
