015-72. Fix: a record whose size field is larger than its content is accepted, and the records it covers are lost
=================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R6's finding R6-F1 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F1: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. Verified with R6's test, made
`DbTesterRestart.testEnlargedRecordSizeRefused` (R6/R6-F1.diff, without
`retainForever()`, which 015-87 removed): before the fix, "started with A's
size over B; /b = lost".

* Fix: `StoredTrans.Parser.parse` refuses a record whose content (header,
  nodes, end marker, got-dirty list, last byte and padding) does not end
  where its size field says, with a `StreamFormatException` ("The record at
  ... ends at offset ... by its content, and its size says ..."). The
  serializer writes the size of the content exactly (`prepareToSerialize`,
  the same in 2026.1), and recovery's fixed records have the last byte 0 and
  are not parsed, so no valid stream is refused.
* R6's second case, a size past the end of the stream (`R6SizeProbe2`), is
  recovery's zero fill of a corrupt size; such a record is not parsed, and
  the check does not reach it (014-01's question, outside the crash
  contract).
* 010-01: no setting, method or thread; a start's read only. The stream's
  bytes are unchanged (P2): nothing that writes changed.
* Tests: the new test, and `DbTesterRestart` (29), `StoredTrans` (22),
  `NodeStreamTester` (16), `TransSeq` (18) pass.
