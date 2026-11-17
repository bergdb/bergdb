015-06. Fix: a refused start leaves an empty first stream file
==============================================================

Status: done 2026-11-06 (2026.2: refusals before the open; the rest on
2026-11-06, for 2026.3). Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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

**State** (2026-11-03, 17:13, F1): the part for 2026.2 is done, with
015-01 (`/Users/f/fl/bench/016/015-01/handoff/`, one patch, for the
coordinator's combined gate and commit): the Pub API's refusals before the
open create nothing. Left, after the release: a start refused after the
open on a directory without a stream file (a refusal in `Db.start` before
the creation's first write, as a clock out of range, 005-18; a bad replica)
still leaves the empty first file and `bergdb.lock`, and the directory if
it was missing. Its fix would make `FileStream` create its first file at
the first append (the Log of 2026-11-03, "Not covered"); with a test that
fails before, as this entry's "Done when" asks.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 16:45 to 16:56, by F1 (016-05), with 015-01, in
`/Users/f/fl/bench/016/015-01/repo`:

* **The test first**: `PubTester.testRefusedStartCreatesNothing` (unit): a
  crypto key of an unknown algorithm ("other"), on an empty directory and
  on a missing one; `start()` throws the `IllegalStateException`; the
  empty directory stays empty and the missing one is not created. On the
  code as it was (`DatabaseBuilderImp.java` of `17270d1`) it fails: "the
  empty directory: 00000000000000.bergdb:0 bergdb.lock:225 , expected 0,
  got 2". So the finding is verified: the open (`openDirs()`, `new
  FileStream(D)`) creates the directory, `bergdb.lock` and the empty first
  file before the key is checked.
* **The fix**, in `DatabaseBuilderImp.start()`: the crypto key's checks
  (`checkCryptoKey()`: the algorithm salsa; key data of 40 bytes, which
  `CryptoKey.parse` already refuses otherwise) run before `openDirs()`,
  with 015-01's check of a missing stream; they are gone from
  `handleCryptoKeyAndCreatedTxt()`. So the Pub API's refusals before the
  `Db` (the key, and 015-01's) open, create and write nothing. With the
  fix the test passes, and `testUnknownCryptoAlgorithmClosesFile` (005-32)
  still does.
* **Not covered**, for the coordinator: a start refused after the open on
  a directory with no stream file still leaves the empty first file and
  `bergdb.lock` (and the directory, if it was missing): a refusal in
  `Db.start` before the creation's first write, such as a clock out of
  range at the creation (`DbClock.transactionBegin`, 005-18), or a bad
  replica (`syncStreams`, replication experimental). A fix of those would
  make `FileStream` create its first file at the first append, a change of
  `FileStream`'s opening that this entry does not make.

2026-11-03. Reviewed 2026-11-03 by the coordinator (H5, 016-05, section
5), with 015-01: no faults; the crypto check moved before the open with
the same messages. The coordinator made the case not covered (a start
refused after the open) this entry's remaining part: it stays open,
Status "in progress (2026.2: refusals before the open; the rest after)".

2026-11-06. The rest done, by agent f06 of coord-1106 (006-13), for
release 2026.3 (018-01, section 3.1), in the clone
`/Users/f/fl/bench/006-13/f06`:

* **The test first**:
  `PubTester.testRefusedStartAfterOpenCreatesNoStreamFile` (unit): a
  start by `create(p)` with a clock whose time is -1, out of range at the
  creation (`DbClock.transactionBegin`, 005-18), on an empty directory and
  on a missing one; `start()` throws ("outside the range"); the directory
  then holds `bergdb.lock` only; a start then creates the database. On
  the code as it was it fails: "00000000000000.bergdb:0 bergdb.lock:225".
* **The fix**, in `FileStream`: the constructor no longer makes the first
  file of a directory without a `*.bergdb` file (`createDbFileObjects`);
  `append` makes it at the first append of a byte (`newFile()`, as for
  every later file, forced with its directory before the write). An empty
  append makes no file. A `read` of a stream without a file reads 0 bytes
  at 0 and throws `EOFException` otherwise, as a read of the empty first
  file did, without failing the stream; a file once made stays (a cut
  keeps the last one). `close()` already handled no file. With the fix
  the test passes; the empty first file of a crash before the first
  write (005-33, row 0) is still possible, as the first append makes the
  file and forces it before it writes.
* **What stays**: `bergdb.lock`, and so the directory if the start made
  it. The lock file is never deleted (005-63, rule 3: a delete races with
  a third instance's lock), so a start refused after the open leaves it,
  as any start that opened the directory does. It does not break a
  restore in place, the harm of "Why it matters"; this entry's "Done
  when" ("no new file") is met for the stream files, which the entry is
  about. A refusal before the open still creates nothing (2026.2's part).
* **Tests changed**: `FileStream.testNoFileUntilFirstAppend` (new: no
  file until the first append, the reads of an empty stream, an empty
  append makes none); `testFailedOpenClosesFileAndUnlocks` opens a
  directory with a stream file, as the open of an empty one opens no
  file now; `PubTester.testCrashedCreationBeforeFirstWrite` and
  `testOpenRefusesDirectoryWithoutStream` make the crashed creation's
  empty first file themselves (`crashedBeforeFirstWrite`), as
  `new FileStream(dir).close()` no longer does.
* Reach: 010-01: no setting, thread or format change; the stream's bytes
  are unchanged. The Javadoc of `FileStream` (class and constructor) and
  the comment in `DatabaseBuilderImp.start()` say so; release note under
  Reliability (`releases/next.md`).
* Gates: `before-commit.sh` BEFORE COMMIT OK, on the tree rebased onto
  `main`; `java/stress/level2.sh` (full, with its Lean conformance) LEVEL
  2 OK, as the change is in `FileStream`'s start.
