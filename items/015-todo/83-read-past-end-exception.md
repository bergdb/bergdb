015-83. Fix: a read past the end throws IOException instead of the documented EOFException
==========================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F8 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F8: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StorageContractTester.testBufferedStream` and
`testStorageManager`, checks "a read past the end" and "an empty stream",
fail and name 015-83. Its fix removes the skip line "015-83" from
`StreamContract.SKIP`.

2026-11-05. Done in night 006-12. Verified by harness 6.3, which is the
test: with the line "015-83" removed from `StreamContract.SKIP`,
`StorageContractTester.testBufferedStream` and `testStorageManager` failed
before the fix ("an empty stream" and the three reads past the end:
`IOException`, expected `EOFException`) and pass after it.

* Fix: `BufferedStream.read` throws `EOFException`, with the same
  message, for a read past the end, as `AppendOnlyStream.read`'s Javadoc
  says, R5's proposal. It is an `IOException`, so no signature changes.
* `StorageManager` passes it on and fails the storage, as Frans decided
  for 018-02 (2026-11-05, 12:35, option (a)); its Javadoc said so already.
* The harness: its check "an empty stream" appended and read after the
  read past the end, which a `StorageManager` refuses after that failure
  (hidden until now by the wrong exception). 018-02, section 2.2, item 1
  has no such append; the check now ends with the read past the end, as
  that item says. The first append of a new stream is checked by "length
  0".
* Reach: Db reads only at positions it got from the stream; a read past
  the end fails the database as before. 010-01: no setting, thread or
  format change; the stream's bytes are unchanged.
