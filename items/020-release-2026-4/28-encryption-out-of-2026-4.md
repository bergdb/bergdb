# 020-28 Encryption out of 2026.4

Created 2026-11-09 by Frans Lundberg. Status: done.

Release 2026.4 has no encryption: the crypto key left the public API, and
the code stays inside BergDB, tested, for a later design (017-10).


## 1. The request

Frans, 2026-11-09, 16:08, on 020-24-07's findings U7-1 (keystream reuse)
and U7-3 (no integrity): "The theme of this release is bug-free database.
What you found is serious. [...] What do you think about removing
encryption all together for this release. Move the possibility to add it
to a 017 item." The coordinator (coord-1109, 16:09): take encryption out of
2026.4's public API, keep the code internal and tested, open a 017 item
for "encryption done right". Frans, 16:12: "Do it! Follow your plan
above." Done by rx for coord-1109 in the clone
`/Users/f/fl/bench/2026-11-09/clone-rx`, from main at `9ed1e6c` with e07's
three commits (U7-5, U7-2, the Javadoc) picked on it, then rebased on main
at `104d676`, where they are `ebf705c`, `1011a94` and `8742547` (batch 28;
the same tree).


## 2. What was done

* **The API.** `DatabaseBuilder.cryptoKey()`, `bergdb.pub.CryptoKey` and
  `bergdb.pub.util.BadCryptoKey` are gone. The Core's
  `DbBuilder.createdTxt(File, String)` is `createdTxt(File)`: the key's
  line of `created.txt` comes from the `SalsaStream`
  (`SalsaStream.getKeyInfo()`), so the Core API has no key setting.
* **The code kept, internal.** `CryptoKey` is `bergdb.pubimp.CryptoKey`,
  package-private; `DatabaseBuilderImp.cryptoKey()` is package-private, for
  the tests (`PubTester.withKey()`); `SalsaStream` and `Salsa` stay in
  their packages, marked internal. e07's U7-2 (one force per flush) and
  U7-5 (restarts of `memory()` with a key) are kept, with their tests. No
  change of the stream's format; `created.txt` keeps "crypto key: none
  (not encrypted)".
* **A database that an earlier release encrypted.** Its `created.txt`
  names the key ("crypto key:    00e9ede5-salsa-****"): `start()`, by
  `create()` or `open()`, throws a `VersioningStreamException` before it
  opens the directory, "The database in DIR is encrypted: its created.txt
  names the crypto key K. An earlier release of BergDB, 2026.3 or before,
  encrypted it, and this release cannot start it: release 2026.4 has no
  encryption. The start has opened, created and written nothing. To use
  the data with 2026.4, start the database with the earlier release and
  its key, and copy the data to a new database [...]". The stream's bytes
  give no certain test without the key (an encrypted meta block looks
  like a foreign or damaged one), so `created.txt` is the test. Without
  it, the stream's magic bytes refuse the start, now with a
  `StreamFormatException` (it was `BadCryptoKey`), whose cause is the
  `BadMagicBytes`: "Invalid magic bytes in stream: the stream is not a
  BergDB stream, or it is damaged; or an earlier release of BergDB, 2026.3
  or before, encrypted it, and this release cannot read it: it has no
  encryption (bergdb 020-28). The start has written nothing."
* **Tests.** `PubTester.testEncryptedByAnEarlierReleaseRefused` (new): a
  database encrypted with the internal key, which writes the stream and
  `created.txt` as 2026.3 did, refused by `create()` and `open()` with its
  `created.txt` and by the magic bytes without it, the files' names and
  bytes unchanged; the internal key still starts it.
  `PubTesterJavadocRest.testNoEncryptionInTheApi` (new): no `cryptoKey()`
  on `DatabaseBuilder`, no `bergdb.pub.CryptoKey`, no `BadCryptoKey`.
  `testForeignStreamRefused` replaces `testBadCryptoKeyForAForeignStream`;
  `CryptoKey`'s tests from `PubTesterJavadocRest` are in `CryptoKey`; the
  encryption tests of `PubTester` give the key by `withKey()` and expect
  a `StreamFormatException` with its message for a wrong key. The tools
  `CcDbTest`, `CcDbNightTest` and `Interactive` (src-dev) lost their
  encryption option (the night tests ran without it); the demos and
  `ReleaseDemo` never used it.
* **Docs.** The package page's "Encryption" (e07's section) is a short
  paragraph: 2026.4 has no encryption, why, full-disk encryption or values
  encrypted by the application, a database of an earlier release refused.
  `DatabaseBuilder.start()` says how such a database is refused.
  `releases/next.md`: an entry first in "Pub API" (removed, why, what to
  use, the refusal, export with 2026.3 first) and one in "Core API"
  (`createdTxt`, `StreamFormatException`); the entries of 2026.4 on
  `CryptoKey` and e07's on the encryption are folded into it.
  `docs/levels.md` lost a clause on an encrypted database's reads.
  README and the overview did not mention encryption.
* **017-10**, "Encryption done right": the topic for a later release, with
  e07's options written out.


## 3. Evidence

* The release jar of 2026.3 (`releases/2026.3/bergdb-2026.3.jar`) made an
  encrypted database of 3,000 values and a plain one; the release jar of
  the clone then started them (`create()` and `open()`): the encrypted one
  refused with the `VersioningStreamException` above, its copy without
  `created.txt` with the `StreamFormatException` above, the plain one
  started; the files' SHA-1s were the same after as before. The probe:
  `MakeOld.java` and `OpenNew.java` in the session's scratchpad (not
  kept).
* Under the gate lock, on the tree of the 020-28 and 017-10 commits on main
  at `104d676`: BEFORE COMMIT OK (149 s, unit 1584, f 86, demos); JAVADOC
  PUB OK; `java/stress/level1.sh`: LEVEL 1 OK (2 min 22 s).


## 4. State

Done in `/Users/f/fl/bench/2026-11-09/clone-rx`, branch `main`: two
commits on main at `104d676`, "020-28: ..." (the code, the docs, the
release notes, this item) and "017-10: ..." (the new topic, 017's index,
and the line in 020-24-07's section 4), for the coordinator to land.
Open until they are on main. Not changed: 020-11 (known issues) and 020's
readme, which may name the removal.


## 5. Log

2026-11-09. Created for coord-1109 at Frans's decision (16:12); the
removal in clone-rx, gated; 017-10 written.

2026-11-09. Done: on main, in release candidate 03ce6ec; encryption done right is 017-10 (coord-1109).
