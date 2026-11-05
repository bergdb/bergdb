019-01. Fix: a meta block's version is read as 2 bytes; bytes 6 and 7 are not checked
====================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Frans: none.
Created 2026-11-05 by Frans Lundberg.

What: `MetaBlock.initBlock` writes the stream format's version as an int
at offset 4, but `MetaBlock.getVersion` and
`RecoverableStream.readMetaBlock` read it as an unsigned short
(`bytesToUShortLE(..., 4)`). A meta block whose int at offset 4 is not
154, but whose low two bytes are, is taken as version 154: bytes 6 and 7
are never checked.

Why: review R6, R6-F3 (016-06): its probe `R6MetaBlockProbe.java` (016-06,
R6) starts a copy whose version int is 65,690 ("START ACCEPTED"). No data
is lost, and no valid stream has nonzero bytes there: every version since
2026.1 writes the version as an int. The format comment was corrected in
015-74 (2026-11-05), which left this optional code change; Frans,
2026-11-05, 10:47, to session bergdb-e8: "74, as recommended", that is,
register it here and let harness 6.1 (018-01, section 6.1) cover its
class.

Frans: none. The change refuses only blocks that no version of BergDB
writes; it changes no valid stream and no written byte (018-01,
section 2). The C clone (012) is a port of 2026.2 and does not follow.

Done when: a test with a meta block whose bytes 6 or 7 are not zero (its
checksum, if any, made right again) is refused at the start, as a block
with a wrong version is; the test fails on the code before the fix; the
fix is in `main` after `before-commit.sh`. If harness 6.1 exists by
then, the case is one of its damaged copies.

First step: read R6-F3 and its probe; read the version as an int in
`readMetaBlock` and `getVersion`, and refuse a value other than the
versions accepted today.


Log
---

2026-11-05. Registered by session bergdb-e8, at Frans's word (10:47), from
015-74's log.

2026-11-05. Done in night 006-12. The test first:
`DbTesterRestart.testVersionHighBytesRefused` starts copies of a database
whose first meta block has byte 6 or byte 7 set to 1 (versions 65,690 and
16,777,370 as an int; the meta block has no checksum); before the fix the
start was accepted ("started a database whose meta block has version
65690"), after it the start throws `VersioningStreamException` naming the
int and writes nothing, and the copy as it was starts. A new case of
`RecoverableStream.Tester.testIsIncompleteCreation` (a creation cut at 10
bytes with byte 6 or 7 set) failed before ("expected false, but was
true") and passes after.

* Fix: `RecoverableStream.readMetaBlock` reads 8 bytes and the version as
  an int, `MetaBlock.getVersion` reads an int, and
  `MetaBlock.beginsAsBlock` (005-33's incomplete creation) compares the 8
  bytes; `FILL_OUT_TEMPLATE` writes the version as an int (the same bytes:
  the template's bytes 6 and 7 were 0). The format comment says 4 bytes.
* P2, every database that was valid is accepted: 2026.1 and 2026.2
  (`git show release-2026.1:java/src/bergdb/storage/MetaBlock.java`, and
  2026.2's) write the version with `intToBytesLE(154, block, 4)` and fill
  out a torn block from a template with 0 in bytes 6 and 7, as `main` does;
  no code writes other bytes there, and a block is copied only from one it
  read. The stream's bytes are unchanged.
* A stream that ends within a meta block's first 8 bytes:
  `readMetaBlock` reads the whole block after the header, so such a read
  failed with `StreamIoException` before too, unless the version was
  wrong; then it is now that exception instead of a
  `VersioningStreamException`. Recovery reads only blocks that it knows
  are complete.
* 010-01: no setting, thread, global state or format change. Harness 6.1
  does not exist yet; the case is for its damaged copies when it does.
