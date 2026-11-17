017-10. Encryption done right
=============================

Created 2026-11-09 by Frans Lundberg. Status: open.

Open (notes only). For a release after 2026.4: 2026.4 has no encryption.

What this topic holds: the encryption of a database's files, which BergDB
had until 2026.3 and which release 2026.4 took out of its API (020-28),
after a new user's password vault (020-24-07) found that it reused
keystream and had no integrity. What 2026.3 had, why it went, the options
for a design that ends both faults, what such a design must be tested
against, and the code that stays inside BergDB for it. Nothing decided.


## 1. The request

Frans, 2026-11-09, 16:08, to the coordinator (coord-1109), on 020-24-07's
findings: "The theme of this release is bug-free database. What you found
is serious. [...] What do you think about removing encryption all
together for this release. Move the possibility to add it to a 017 item."

The coordinator's answer (16:09): take encryption out of 2026.4's public
API; keep the code internal and tested; open a 017 item for "encryption
done right". Frans, 16:12: "Do it! Follow your plan above." The removal is
020-28.


## 2. What 2026.3 had

* **The API**: `DatabaseBuilder.cryptoKey(CryptoKey)`; `bergdb.pub.CryptoKey`
  with `generate()`, `serialize()`, `parse()`, `NULL`, `getAlgo()` and
  `getKeyData()`; `bergdb.pub.util.BadCryptoKey`, thrown by a start with a
  wrong key, with none on an encrypted database, or with one on a database
  that is not encrypted.
* **The key**: a name (8 hex digits, for people), the algorithm "salsa",
  and 40 bytes of key data: an 8-byte nonce and a 32-byte key, both random
  from `generate()`. Serialized as `NAME-salsa-HEX`.
* **The cipher**: `bergdb.stream.SalsaStream`, a decorator of the
  database's `AppendOnlyStream`, encrypts every byte of the stream with
  Salsa20 (`bergdb.common.Salsa`): the nonce the key data's first 8 bytes,
  the block counter the stream position / 64. A new `SalsaStream` encrypts
  from the stream's length on. So the keystream is a function of the key
  and the position alone.
* **What was encrypted**: every byte of the stream's files (`*.bergdb`),
  from the first. Not encrypted: `created.txt`, whose line "crypto key:"
  names the key with its data masked (`3fa2c901-salsa-****`);
  `bergdb.lock`; what the files show by their names, sizes and times (the
  size of a transaction written alone, so a value's length); the data in
  memory.
* **No integrity**: a node's checksum is Fletcher-16 over the plaintext,
  without a key (017-08).
* **The cost**, after U7-2's fix: about 400 MB/s, 2.5 ns per byte written
  to or read from the files, on F53; puts as fast as without a key.


## 3. Why it was removed from 2026.4

The findings of 020-24-07 (u7's password vault), each with its
reproduction in `/Users/f/fl/bench/2026-11-09/app-u7/`: the application
`app/VaultApp.java` (run by `app/run.sh`, output `app/run.txt`) and the
minimal reproductions in `probe/`. They use the API of 2026.3 and of 2026.4
before 020-28: run them against `releases/2026.3/bergdb-2026.3.jar` or
`app-u7/bergdb-release.jar` (built from `4338cda`).

**U7-1, keystream reuse (high).** Two writes at one stream position with
one key are encrypted with the same keystream, so the XOR of the two
encrypted files is the XOR of their plaintexts (a "two-time pad").
`probe/KeystreamReuse.java` shows the three cases, 100 to 130 values of
3,000 'A's against as many 'B's ('A' ^ 'B' = 0x03; with independent
keystreams each byte value would be 0.4% of the XOR):

```
1. two databases, one key: 311936 bytes compared from offset 8; XOR 0x03: 96.2%, 0x00: 3.6%
2. a database and its copy: 312672 bytes compared from offset 311952; XOR 0x03: 95.9%, 0x00: 3.9%
3. a tail cut and written again: 93592 bytes compared from offset 311952; XOR 0x03: 96.2%, 0x00: 3.7%
```

1. Two databases with one key. In `VaultApp`'s phase `twin`, the keystream
   of a key, taken from a database and its plaintext twin, decrypted
   another database encrypted with that key: 300 of its 300 passwords.
2. A copy of a stopped database and the original, both written on (phase
   `copy`, 85.4% 0x03): a backup restored and written on while the old
   disk or a later backup holds the other branch.
3. The tail written after the last sync, cut as a power loss may cut it,
   and the database written on after the recovery (phase `crash-check`,
   after a SIGKILL and a cut: 82.9% 0x03 over 1.1 MB): whoever saw the
   files before the cut (a backup, a synced folder that keeps versions, a
   snapshot) and after reads the XOR of the lost transactions and the new
   ones.

BergDB's own bytes make the XOR worth more: the first meta block of a
plain stream holds runs of zero bytes, whose encryption is the keystream
itself, and the records have known headers.

**U7-3, no integrity (medium).** A stream cipher without authentication,
and a checksum without a key: a change of an encrypted byte changes the
same plaintext bit, and one who knows the plaintext of a node can
recompute its Fletcher-16. `probe/Forge.java` changed the site
"https://bank.example.com/login" of an entry to
"https://bank.examp1e.com/login" in the encrypted file of a database of
16 MB, with the sum recomputed; a start with the key and a `get()` gave
the forged site with no error. Changed blindly, the checksum catches it
(phase `twin`: `StreamChecksumException` at the start). The cases where an
attacker knows the plaintext are those of U7-1. Nor does anything notice
a cut tail or an older copy of the files put back (rollback).

The other findings, bugs of the implementation, are fixed in the code
that stays (section 6): U7-2 (a key made writes 6 to 8 times slower: up to
50 forces per flush; `probe/Cost.java`), U7-5 (`memory()` with a key: every
other start on its closed stream refused; `probe/MemKey.java`), U7-7 (the
right key on a damaged stream said "the wrong crypto key";
`probe/Damage.java`), U7-6 (`parse()` refuses a trailing newline).

e07 made the Javadoc true for 2026.4 (the package's "Encryption" section,
on main as `9ebffa5`); Frans then chose to remove the encryption instead,
as a release whose theme is a bug-free database should not offer a
feature with a known fault of its design. A fix of U7-1 or U7-3 changes
the stream's format, which 2026.4 does not.


## 4. The options

From 020-24-07, section 4 (e07), each written out. U7-1's options and
U7-3's can be combined; each is a change of the format.

### 4.1. U7-1, keystream reuse

**A. A random nonce per database.** At the creation, 16 or 24 random
bytes are written in clear at the stream's start (a header before the
first meta block, or in the first meta block's reserved bytes), and mixed
into Salsa's nonce with the key's: the keystream becomes a function of the
key, the database's nonce and the position. Ends case 1 (two databases
with one key) only: a copy of a database has the same nonce, and so does
the database after a recovery that cut its tail, so cases 2 and 3 remain.
Cost: a header in clear (it shows that the stream is encrypted, and lets a
start without a key say so with certainty); a start reads it before
anything else. Cheap to build and test.

**B. A random nonce per start that writes (an epoch).** Each start that
will append, and each recovery that cuts a tail, draws a random epoch
nonce and writes it, in clear, in a small record where its appends begin;
each meta block names the epoch in force at its position. A read of a
position finds its epoch from the meta block at or before it and the
epoch records after that block. A position is then written twice only
under two different epochs, so the keystreams differ: ends all three cases
(a copy written on gets new epochs at its next start; a recovery that
cuts starts a new epoch). Cost: about 16 bytes per start that writes; a
new record type, a meta block field, and the epoch lookup on every read
from the files (cached, as the epochs are few). Today's streams read as
epoch 0, so a 2026.3 database could be read and continue under new epochs.
Needs care: the epoch record must be written and durable before the first
encrypted byte of its epoch; reclaim's cut of the stream's front must keep
the epochs that the remaining positions need.

**C. B with XChaCha20 and a 192-bit nonce per epoch.** As B, but the
cipher is XChaCha20 (or XSalsa20), whose 192-bit nonce makes a collision of
two random epoch nonces negligible (with Salsa20's 64-bit nonce, B's random
epochs collide with probability about n^2 / 2^65 after n epochs, small
but not negligible for a database restarted often over years). Cost: a
new cipher implementation (ChaCha20 is in the JDK, `javax.crypto`, since
Java 11; XChaCha20 is not, and needs HChaCha20 on top), and the C port
would need it too (012/022).

### 4.2. U7-3, integrity

**A. Authenticated pages.** The encryption writes the stream in fixed
pages (such as 64 kB), each encrypted and given a Poly1305 tag
(XSalsa20-Poly1305 or XChaCha20-Poly1305, an AEAD), the page's position
and epoch in its associated data. A read checks the tag of each page it
reads, so a forged or damaged byte is refused, and a page cannot be moved
to another position. Cost: the files' positions differ from the stream's
(a tag per page, and the last page rewritten as it grows, or a partial
last page with its own tag); a random read reads and checks a whole page;
an append-only stream whose last page is rewritten is no longer
append-only on disk, which changes the crash contract (014-01, section 7)
unless the partial page is written as a new page each flush. The largest
change.

**B. A keyed check per node and record.** In an encrypted database, each
node and each record header carries a MAC (64 or 128 bits, such as a
truncated Poly1305 or a keyed BLAKE2/SipHash over the plaintext with its
position) in place of, or beside, Fletcher-16. A forged node or value is
refused at its read, as a damaged one is. Cost: headers grow by 8 or 16
bytes per node and per record; the MAC's key is derived from the
database's key. Fits BergDB's structure (017-08 asks for a stronger node
checksum anyway); does not by itself detect a cut tail or rollback.

**C. A MAC chain for rollback and a cut tail.** Each meta block (or each
record) holds a MAC over the stream up to it, chained from the one
before; the application keeps the last value (or the database keeps it
somewhere the files' attacker cannot reach) and a start checks that the
stream reaches it. Without state kept outside the files, no design can
tell an older copy of the files from the current one: the application
must keep a counter or the last MAC, as a password vault might in the
operating system's keychain. Cost: an API for that state, and a defined
behaviour when it does not match (refuse, or start and report).


## 5. What an implementation must be tested against

* **The three keystream-reuse cases**, as `probe/KeystreamReuse.java`
  makes them: two databases with one key; a stopped database copied and
  both written on; a tail cut after the last sync and written again. The
  XOR of the two versions' bytes must look random (each byte value about
  0.4%), not 0x03.
* **A forged node**, as `probe/Forge.java` makes it: known plaintext, a
  value changed in the encrypted file, the node's checksum recomputed; the
  start or the read must refuse it, not return the forged value.
* **Rollback**: an older copy of the files put back, and a cut tail; a
  design states which it detects and with what state outside the files,
  and the tests show it.
* **The cases that 2026.3 handled and its fixes**: a wrong key, no key on
  an encrypted database, a key on one that is not; the right key on a
  damaged stream (U7-7); starts again on the closed stream of `memory()`
  (U7-5); one force per flush (U7-2, `SalsaStream.testOneForcePerAppend`);
  reclaim's cut of the stream's front, crash recovery (SIGKILL and a cut
  tail), an index build retaken, concurrent readers of past versions from
  the files (`VaultApp`'s phases `reclaim`, `crash-*`, `index-crash-*`,
  `concurrent`); confidentiality of the files (phase `grep`: none of the
  needles).
* **Databases of 2026.3**: a database that 2026.3 encrypted, refused by
  2026.4 (section 6); the later release states whether it reads them
  (option B's epoch 0) or refuses them.
* **The cost**: puts and scans with and without a key, as
  `probe/Cost.java` measures them.


## 6. The code that remains

Internal since 2026.4, not API, with its tests in the unit tests (020-28):

* `bergdb.common.Salsa`: Salsa20.
* `bergdb.stream.SalsaStream`: the encrypting stream, with U7-2's fix (one
  append, one force, per flush) and the key's line of `created.txt`
  (`getKeyInfo()`). Its tests: its own Nano tests, among them
  `testOneForcePerAppend`; `StreamContractTester.testSalsaStream`;
  `RecoverableStream`'s test of a wrong key after a crash at a meta block.
* `bergdb.pubimp.CryptoKey`, package-private (was `bergdb.pub.CryptoKey`):
  `generate()`, `serialize()`, `parse()`, with 020-20's N1, 020-21's and
  020-25's C1 fixes; its tests, among them those moved from
  `PubTesterJavadocRest`.
* `DatabaseBuilderImp.cryptoKey(CryptoKey)`, package-private, and
  `handleCryptoKeyAndCreatedTxt()`, with U7-5's fix; `PubTester.withKey()`
  gives the key in the tests: `testEncrypted1` to `3`,
  `testWrongKeyAfterCrashAtMetaBlock`, `testCrashInCreation`,
  `testDamagedStreamWithTheRightKey` (U7-7),
  `testRestartsOfMemoryBuilderWithCryptoKey` (U7-5),
  `testSecondStartOfMemoryBuilder`, `testOpenEncrypted`,
  `testFailedStartsLeaveNothing`, `testCreatedTxt1`, and the tests of an
  unknown algorithm.
* `Db`'s `encrypted` (its main stream is a `SalsaStream`), for the message
  of a start refused for the magic bytes with a key.
* The refusal of a database that an earlier release encrypted:
  `DatabaseBuilderImp.refuseEncrypted()` by `created.txt`'s line "crypto
  key:", a `VersioningStreamException`; without `created.txt`, `Db`'s
  `StreamFormatException` for the magic bytes. Test
  `PubTester.testEncryptedByAnEarlierReleaseRefused`.

e07's Javadoc of the encryption for 2026.4 (the package's "Encryption"
section, `DatabaseBuilder.cryptoKey()`, `CryptoKey`, `BadCryptoKey`), true
for 2026.3's design, is in its commit, `9ebffa5` on main (020-24-07,
section 4), before 020-28 removed it: a start for the user documentation
of a later design.


## 7. Open questions for Frans

1. Bring encryption back at all, or leave it to the layers below and
   above: full-disk encryption (FileVault, LUKS, BitLocker), and values
   encrypted by the application?
2. If so: the whole stream (U7-1's B or C, with U7-3's A, B or C), or
   per value, with the keys in clear?
3. What integrity is wanted: forged bytes refused (U7-3's A or B), and
   rollback detected with state outside the files (C)?
4. Databases that 2026.3 encrypted: read and continue them, or refuse
   them as 2026.4 does?


## 8. Log

2026-11-09. Created at Frans's request (16:08, 16:12), with 020-28's
removal of the encryption from 2026.4's API: what 2026.3 had, why it was
removed (020-24-07's U7-1 and U7-3), e07's options written out, what a
design must be tested against, and the code that stays.
