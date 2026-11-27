028-69. Implement: remove the internal crypto code
==================================================

Status: in progress: the removal is made and gated in the branch
`028-69` (2026-11-27); it lands with the lead, and 028-60's part 2 is
then rebased on it. Kind: Implement. Frans: none (decided).
Created 2026-11-27 by Frans Lundberg.

What: encryption left the API in release 2026.4 (020-28), and its code
was kept internal for a later design (017-10): `bergdb.stream.SalsaStream`,
`bergdb.pubimp.CryptoKey`, the package-private
`DatabaseBuilderImp.cryptoKey()`, and what only they use in the stream
contract, the storage, the Core's builder and the tests. This entry
removes that code, its tests and its mentions in the Javadoc. The
refusal of a database that a release before 2026.4 encrypted stays, if
it needs none of the removed code; if it does, the entry's log says what
was done about it.

Why: Frans decided on 2026-11-27 to remove it.

* The key is a setting outside the stream that changes the stream's
  bytes, against the rule of the day for P2's wording (no setting
  outside the stream is to affect the bytes; 028-68 is the other such
  setting).
* 028-60's part 2 (the repair of a tail of zeros, branch `028-60b`,
  gated and reviewed twice by Codex) waits only on a choice about
  encrypted streams, which exist only through this code.
* The study of A1's option (d) and Codex's review of it (2026-11-27,
  006-37) both met it: the keystream at a byte written again, and the
  cipher's cursor after a cut of the tail.

For the later design: the record of the removal goes into 017-10's log,
so that the design finds the code: the last commit that has it, the
commit that removes it, and the files. When encryption comes back, the
key is the one exception to "no setting outside the stream affects the
bytes": the stored bytes depend on it, and it cannot be in the stream
(Frans, 2026-11-27).

Frans: none; decided 2026-11-27.

Done when: the code is gone; `java/before-commit.sh` prints
`BEFORE COMMIT OK`; 017-10's log has the record of the removal; 028-60's
part 2 is rebased on it without its opt-out for encrypted streams.

First step: list every use of `SalsaStream`, `CryptoKey` and
`cryptoKey` in `java/` (on 2026-11-27: `DatabaseBuilderImp`,
`CryptoKey`, `PubTester`, `PubTesterJavadocRest` and `Pack` in
`bergdb.pubimp`; `DbBuilder` and `Db` in `bergdb.core`; `SalsaStream`,
`StreamContract`, `StreamContractTester` and `Pack` in `bergdb.stream`;
`RecoverableStream` in `bergdb.storage`; `bergdb.pub`'s package.html),
and the scripts and items that name them.


Log
---

2026-11-27. Registered by lead-1127 after Frans's decision; in progress,
by an agent of lead-1127 in a clone.

2026-11-27. The removal, in the branch `028-69`, made in a clone of main
at `0edd2a2f`:

* Removed: `bergdb.common.Salsa` (Salsa20), `bergdb.stream.SalsaStream`
  and `bergdb.pubimp.CryptoKey`, each with its Nano tests;
  `DatabaseBuilderImp.cryptoKey()`, its field, `salsaMade`,
  `checkCryptoKey()` and the encryption half of
  `handleCryptoKeyAndCreatedTxt()`, now `handleCreatedTxt()`; `Db`'s
  `encrypted` and the message of a start with a key;
  `StreamContractTester.testSalsaStream` and `SalsaStream`'s row in
  `StreamContract.FAULTS`. No script, harness or stress option gave a
  key: the scripts of `java/`, `java/stress/`, `tools/` and `lean/` name
  none of the removed classes or methods, so `java/stress/level1.sh`
  was not run.
* `created.txt` has no line "crypto key:" from now on; in every database
  since 2026.4 it said "none (not encrypted)". The rest of the file is
  as before.
* The refusal of a database that 2026.3 or before encrypted stays, and
  needs no cipher: `DatabaseBuilderImp.refuseEncrypted()` reads
  `created.txt`'s line "crypto key:" before the directory is opened, and
  refuses a value other than "none ..." with a
  `VersioningStreamException`; without `created.txt`, the start reads
  the stream and refuses its magic bytes with a `StreamFormatException`
  whose message names this case (`Db.startInner`). A database of 2026.4
  to 2026.6, whose line says "none (not encrypted)", and one created
  now, with no line, start.
* Tests rewritten where the key only made a stream that does not read:
  its bytes are flipped instead (every bit; flipped again, the stream is
  as before), as an earlier release's encryption or a wrong key left
  them. `RecoverableStream.testRecoverWithWrongKeyWritesNothing` is
  `testRecoverUnreadableWritesNothing` (005-40);
  `PubTester.testWrongKeyAfterCrashAtMetaBlock` is
  `testUnreadableStreamAfterCrashAtMetaBlock` (005-40);
  `testFailedStartsLeaveNothing` (005-32); and
  `testEncryptedByAnEarlierReleaseRefused` (020-28) makes the database
  as 2026.3 left it, a key's line in `created.txt` and the stream's
  bytes flipped, and also starts one whose line says "none (not
  encrypted)".
* Tests that ran with and without a key run without it, as before:
  `testSecondStartOfMemoryBuilder` (015-65), `testCrashInCreation`
  (005-33, 028-18); `testDamagedStreamWithTheRightKey` is
  `testDamagedStreamRefused` (U7-7); `testRestartsOfMemoryBuilderWithCryptoKey`
  is `testRestartsOfMemoryBuilder` (U7-5's restarts, without a key);
  `PubTester.testCreatedTxt1` and `DbTesterStream.testCreatedTxt` check
  the database ID and no key line. `PubTesterJavadocRest.testNoEncryptionInTheApi`
  also checks that the three removed classes do not exist.
* Tests dropped, 33 in all, each for a reason:
  * the encryption itself: `PubTester.testEncrypted1` to `3` and
    `testOpenEncrypted`, `DatabaseBuilderImp.testCryptoKeyNullAfterKey`
    and `testCryptoKeyNullRefused` (015-44), `testSalsaStream`, and the
    24 Nano tests of the three removed classes (among them
    `SalsaStream.testOneForcePerAppend`, U7-2);
  * `PubTester.testRefusedStartCreatesNothing` (015-06): its refusal,
    a key of an unknown algorithm, was the only check before the open
    that an empty or a missing directory met with create(); a refusal
    before the open that creates and writes nothing stays tested by
    open()'s refusals (015-05, `assertOpenRefused`) and by
    `testEncryptedByAnEarlierReleaseRefused`;
  * `PubTester.testUnknownCryptoAlgorithmClosesFile` (005-32): since
    015-06 its refusal came before the open, so it opened no file; a
    start that throws after the open closes its file, tested by
    `testFailedStartsLeaveNothing` and `testFailedStartsDirectoryRemoved`.
* Texts: the Javadoc and comments of `DatabaseBuilderImp`,
  `DbBuilder.createdTxt()`, `Db`, `RecoverableStream`,
  `StreamContractTester` and `PubTesterJavadocRest`; 027-03, section 16
  and the rows that named `SalsaStream`; a test's name in 027-11. The
  Pub API's Javadoc (`DatabaseBuilder.start()`, `bergdb.pub`'s
  "Encryption", `VersioningStreamException`) describes no kept code and
  is unchanged.
* Not removed: `bergdb.test.java.Ciphers`, `MacPerf` and `SecureHash` in
  `java/src-dev`, timings of the JDK's own ciphers, MACs and hashes; they
  use none of the removed code.
* For 028-60's part 2: `FileStream` is not changed. In
  `DatabaseBuilderImp`, the lines of main's `0edd2a2f` that the removal
  changes: the imports (8, 22), the fields (33, 44 to 45, 50 to 56),
  `cryptoKey()` (94 to 109), `start()` (207, 210 to 212, 222), the Javadoc
  of `refuseStreamInUse()` (248), `checkCryptoKey()` (294 to 314), the
  Javadoc of `refuseEncrypted()` (344, 349 to 350),
  `handleCryptoKeyAndCreatedTxt()` (447, 456 to 494) and the tests (530
  to 565).
* Gate: `java/before-commit.sh` in the clone on the removal's commit,
  2026-11-27: `Unit: SUCCESS, 1720 successful tests in 43.6 s.`,
  `F:    SUCCESS, 90 successful tests in 51.3 s.`,
  `Demos: DEMOS OK, 14 runs in 4 s.`, `BEFORE COMMIT OK (63 s)`.

2026-11-27. 017-10's log has the record of the removal: the last commit
with the code, `0edd2a2f` on main; the removal's commit: `1809e04c` in
the branch 028-69 (main's hash replaces it at landing); the files
removed; and the rule for the key's return.
