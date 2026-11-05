015-41. Fix: a String or bytes and an object, or a delete, of one key: the call order is lost
=============================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F2 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F2: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`e427a4c`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F2, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05, night 006-12. Done. S1-F2's two tests, in `PubTester` (unit):

* `testRwStringPutThenDeleteOfObjectKey`: a String put and then a delete of
  `/d` in an rw-transaction, the same through `w()`, also with a `byte[]`;
  a delete and then a put, and a put, a delete and a put, leave the last
  put. Before the fix: "rw: String put, then delete: expected no entry, got
  'new'."; passes after it. This half is in release 2026.3's goal (018-01,
  D4: `String` and `byte[]` puts and deletes).
* `testRwObjectPutThenStringPut`: an object put and then a String put of
  `/e`. Before the fix: "object put, then String put, expected 'text', got
  'bergo ... name Ann'" (the object's bytes); passes after it. An object
  put is experimental (018-01, D6); the fix of this half is in the String
  put, a line, so it is made too.

* Fix, as S1-F2 proposed, in `RwEnvironmentImp`: a delete of an object key
  removes the key's entry in `kvOps` (a String or `byte[]` put of it); a
  String or `byte[]` put of an object key turns an object put of it in
  `objectOps` into a delete. One choice of the review's "remove the key from
  the other map": the object put becomes a delete, not nothing, so that
  `indexEntries` still removes the index entries of the key's previous
  object, as it does for a delete and then a String put; a removal would
  leave them, 015-46's fault (S1-F7, experimental). An object put after a
  String put needed no change: `createTrans` adds `objectOps` after `kvOps`,
  and the later put wins. The comment on the maps says so.
* 010-01: no setting, no state, no thread (P3, P9, P10). The bytes written
  change only for a transaction that wrote a key twice in these ways, which
  wrote the wrong value before (as 015-40's fix); StreamDigest uses the Core
  API and is not affected (P2).
* All `PubTester*` classes pass (229 tests).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (110 s)`, unit 1187, f 87.
