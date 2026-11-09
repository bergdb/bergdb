# 020-24-07 A password vault on an encrypted database

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u7, for coord-1109, by the
common brief of 020-24, round 3): only the release jar on the class path, and only what a
user reads (README.md, `java/src/overview-pub.html`, the Javadoc of `bergdb.pub` and
`bergdb.pub.util`, `releases/next.md`). The jar was built from a clone of main at
`5d45478`. The implementation was read only afterwards, to explain U7-1, U7-2, U7-3 and
U7-5; `probe/Forge.java` was written after that reading.


## 1. The application

A password vault: entries of sites, users, passwords, notes, tags, a strength and a TOTP
seed, with their history, in an encrypted database whose key is kept apart.
`VaultApp.java` holds the application and its checks, in phases that `run.sh` runs as JVMs
of their own, one at a time; it prints `APP OK` when every phase passes. Both are in
`/Users/f/fl/bench/2026-11-09/app-u7/app/`, with the output of the last run, `run.txt`.
The minimal reproductions are in `/Users/f/fl/bench/2026-11-09/app-u7/probe/`.

How it uses BergDB:

* The key: `CryptoKey.generate()`, `serialize()` to a file of its own (`keys/`, mode 600),
  apart from the database's directory; every start reads the file and `parse()`s it, and
  gives the key to `DatabaseBuilder.cryptoKey()`.
* Entries as a Data Object, `Entry` (Strings, a `String[]`, two longs, a `byte[]`), at
  `/vault/eNNNN`; attachments as `byte[]` at `/attach/aNNN.bin`.
* Changes: a password rotated in an `rw()` (read, change, put; a skipped key told by an
  output); notes of two or three entries in one `w()`; deletes; entries made again.
* Two user indexes: `vault-by-site` (a "string" level, sites with non-ASCII and
  supplementary characters, so that code point order differs from `String.compareTo`) and
  `vault-by-strength` ("long", then "string"), the second built over existing data.
* History: the state at past lookup times, by `usePrimary()` and by the indexes;
  `transactionInfo()` after each get.

The phases, each checked against an oracle that records every version at its
transaction time:

* `create`: 1,429 transactions on 436 entry keys and 58 attachment keys.
* `verify`: a restart with the key read back: 289 past states (each a transaction's time
  and the unit before it) by primary scan, the indexes forward, backward and by prefix,
  `eq().eq()` and bounds; 1,739 versions by `get()` at their times; 341
  `transactionInfo()`.
* `grep`: the files of the directory searched for 4,002 needles (passwords, notes, users,
  sites, TOTP seeds and attachments as raw bytes, field names, and the key: its string,
  its hex in both cases, its raw bytes, nonce and key apart); a control database with the
  same data and no key, which shows 3,993 of the data's 3,996 needles.
* `keys`: starts with no key, `CryptoKey.NULL`, a new key, another database's key, the
  vault's key on another database and on one without a key, the key data changed at five
  hex digits, the algorithm "aes" and "SALSA", another name, the data in upper case, 12
  damaged strings; the files hashed before and after; a creation refused for the
  algorithm; an encrypted database in memory, started again on its closed stream.
* `copy`: the stopped directory copied, the copy opened with the key and checked, no key
  refused; the original and the copy run at once and both write.
* `reclaim`: startup distance 5 MB, retain duration 1 s, an index, 8,000 puts of about
  8 kB (66 MB) until the front is cut; every version within the available time, a read
  before it refused; a restart; starts with no key, a wrong key and `NULL` after the cut.
* `concurrent`: 26 MB in 6,000 versions, a restart with a 4 MB cache, so reads decrypt
  from the files; 4 readers of random past versions and a writer for 5 s.
* `crash-writer` and `crash-check`: a writer killed with SIGKILL after about 3 s; the tail
  written since the last sync cut, as a power loss may cut it; recovery with the key, the
  state that of an op at or after the last sync; 400 writes more and a restart.
  `crash-check-nocut` takes the files as the kill left them.
* `index-crash-writer` and `index-crash-check`: 30,000 entries, an index build started,
  the JVM halted; the start builds it again, and the scans are right.
* `twin`: databases written alike with a `TestClock`, with no key, a key `k`, `k` again
  for other data, another key; the keystream and two changes of the encrypted bytes.

Size: `VaultApp.java` 1,689 lines, `run.sh` 44 lines; about 20,200 checks in a run, which
takes about 32 seconds on F53 under a load of 11 to 16, and writes about 90 MB in `data/`.

The last run: every check passed but six: three of U7-1 (`copy`, `crash-check`, `twin`)
and three of U7-5 (`keys`), which fail in every run.


## 2. The findings

Most severe first. A reproduction names a file in `probe/` or a phase of `VaultApp`.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U7-1 | bug | high   | one keystream per key and stream position, ever         | KeystreamReuse |
| U7-2 | bug | medium | a key makes writes 6 to 8 times slower                  | Cost           |
| U7-3 | doc | medium | no integrity: known plaintext lets a value be changed   | Forge          |
| U7-4 | doc | medium | the Javadoc says almost nothing about the encryption    | the app        |
| U7-5 | bug | low    | memory() with a key: every other start on it refused    | MemKey         |
| U7-6 | API | low    | parse() refuses a trailing newline; the name is free    | `keys`         |
| U7-7 | doc | low    | the right key, a damaged stream: "the wrong crypto key" | Damage         |
| U7-8 | doc | low    | `getKeyData()` keeps a dated history note               | the Javadoc    |

### U7-1. One keystream per key and stream position, ever (bug, high)

Two writes at one position of the stream with one key are encrypted with the same bytes
of keystream, so the XOR of the two encrypted files is the XOR of their plaintexts: the
"two-time pad". Three cases meet it, each shown by `probe/KeystreamReuse.java` (100 to 130
values of 3,000 'A's against as many 'B's; 'A' ^ 'B' is 0x03; with independent
keystreams, each byte value is 0.4% of the XOR):

```
1. two databases, one key: 311936 bytes compared from offset 8; XOR 0x03: 96.2%, 0x00: 3.6%
2. a database and its copy: 312672 bytes compared from offset 311952; XOR 0x03: 95.9%, 0x00: 3.9%
3. a tail cut and written again: 93592 bytes compared from offset 311952; XOR 0x03: 96.2%, 0x00: 3.7%
```

1. Two databases with one key: the first 8 bytes of the two files are equal, and the
   rest XORs to the plaintexts' XOR. In the app's `twin` phase, the keystream of `k`,
   taken from a database and its plaintext twin, decrypts another database encrypted with
   `k`: 300 of its 300 passwords read ("BBBB...password..TPW-B-0042-42b557489a50.site..
   shop.examp"). `DatabaseBuilder.cryptoKey()` invites the reuse: "start a new one using
   the provided encryption key".
2. A copy of a stopped database, and the original, both written on (the app's `copy`
   phase: 85.4% 0x03): a backup restored and written on, while the old disk or a later
   backup holds the other branch.
3. The tail written after the last sync, cut as a power loss may cut it, and the database
   written on after the recovery (the app's `crash-check`, after a SIGKILL: 82.9% 0x03 over
   1.1 MB): whoever saw the files before the cut (a backup, a synced folder that keeps
   versions, a file system snapshot) and after reads the XOR of the lost transactions and
   the new ones. A SIGKILL alone left whole records in 6 runs, and nothing was rewritten.

BergDB's own bytes make the XOR worth more than it seems: the first meta block of a
stream without a key holds runs of zero bytes, whose encryption is the keystream itself,
and records have known headers.

Why, read afterwards: `bergdb.stream.SalsaStream` encrypts with Salsa20, the nonce the
first 8 bytes of the key data, the block counter the stream position / 64; a new
`SalsaStream` encrypts from the stream's length. So the keystream is a function of the key
and the position alone, the same in every database, every copy and every rewrite of a cut
tail. A random nonce per database and per recovery that cuts (kept in the stream's meta
data) would end it; that changes the stream format, so for 2026.4 the Javadoc at least
should say it (U7-4). For a password vault, whose point is that the files can be lost
without the data, this is the main finding.

### U7-2. A key makes writes 6 to 8 times slower (bug, medium)

`probe/Cost.java`: 100,000 puts of 1 kB `byte[]` values and a sync, then a restart with a
4 MB cache and a primary scan; two rounds each, on F53 under a load of about 16:

| Database | Puts | Restart and scan |
|----------|------|------------------|
| no key    | 1.5, 1.6 s  | 1.9, 1.7 s |
| encrypted | 12.2, 9.3 s | 2.2, 2.1 s |

Stack samples of the encrypted run (`probe/Cost2.java` and `jstack`): the putting thread
waits for room in the write buffer, and the storage thread is in `FileChannel.force()`,
called from `FileStream$DbFile.append()` under `SalsaStream.append()`, at each of 4
samples. Why, read afterwards: `SalsaStream.append()` encrypts and appends in chunks of its
100 kB buffer, and the database's `FileStream` forces each append (`FileStream(dir)`,
forcing on); without a key, a flush of the write buffer, up to half of its 10 MB, is one
append to the `FileStream`, with a force per file it reaches. So a key multiplies the
forces, which dominate on F53. Nothing documents the cost (U7-4).

### U7-3. No integrity: who knows a plaintext can change a value (doc, medium)

The encryption is a stream cipher without authentication, and the node checksum is
Fletcher-16 over the plaintext, with no key. A change of encrypted bytes changes the same
plaintext bits. Changed blindly, the checksum catches it: in the app's `twin` phase, a
password changed by the keystream made the start throw `StreamChecksumException`; in
`probe/Forge.java`, a site changed in a value outside the startup section made the `get()`
throw `DbFailedException` (as its Javadoc says), and the database failed. But who knows
the plaintext of the node can recompute the checksum: `probe/Forge.java` (written after
reading `NodeChecksum`) changed the site "https://bank.example.com/login" of an entry to
"https://bank.examp1e.com/login" in the encrypted file of a database of 16 MB, with the
sum recomputed, and a start with the key and a `get()` gave the forged site, with no
error; another key read right. For a vault, a site changed so is a phishing address that
the vault fills in. The cases where an attacker knows the plaintext are those of U7-1.
`Database`'s "Errors" says the checksums are a best effort against damage; the Javadoc
should say that the encryption keeps the data secret, not unchanged, and that a database
must be kept where it cannot be changed.

### U7-4. The Javadoc says almost nothing about the encryption (doc, medium)

The package page has no word on it; `CryptoKey`'s class Javadoc is one sentence, and
`DatabaseBuilder.cryptoKey()` two. A user who keeps secrets in BergDB needs to know, and
found only by trying:

* What is encrypted: the stream files, every byte from the first (the app's `grep`: none
  of 4,002 needles; the stream starts with "berg" without a key). `created.txt` and
  `bergdb.lock` are not; `created.txt` names the key, masked ("crypto key:
  143acd58-salsa-****"), which is useful when keys are many: say so.
* What the key's name is for: any name with the right key data opens the database (another
  name, the name in upper case, another database's name, a name with a leading space);
  `parse()` takes any name; `equals()` compares names, so two keys that open one database
  are not equal.
* One key per database (U7-1), and no copy of a database written on beside the original.
* No integrity (U7-3); and what the files show: the size of each write and when the files
  grew, so a password's length.
* A lost key loses the database: no recovery. The key cannot be changed, and a database
  cannot be encrypted later or decrypted: only its data can be copied to a new database,
  without its history.
* `memory()` with a key: allowed, and of what use.
* The cost (U7-2).

### U7-5. memory() with a key: every other start on its closed stream is refused (bug, low)

`DatabaseBuilder.start()` says that once the database on the stream of `memory()` has
closed, start() starts a database on that stream, which "reads the data". With a key, the
second start throws `BadCryptoKey` ("Likely, the wrong crypto key was used."), the third
reads the data, the fourth throws again. And on a stream of `memory()` without a key,
after a start with a key (refused, rightly), a start without a key is refused too, with
that message, though no key was given. `probe/MemKey.java`:

```
encrypted, its closed stream, the same key: BadCryptoKey: Likely, the wrong crypto key was used. ...
encrypted, its closed stream, the same key again: started; /m/a.txt reads memory secret
encrypted, its closed stream, another key: BadCryptoKey: ...
encrypted, its closed stream, its key after another: BadCryptoKey: ...
plain, its closed stream: started; /m/a.txt reads plain
plain, its closed stream, a key: BadCryptoKey: ...
plain, its closed stream, no key again: BadCryptoKey: Likely, the wrong crypto key was used. ...
```

Why, read afterwards: `DatabaseBuilderImp.handleCryptoKeyAndCreatedTxt()` wraps the
builder's main stream in a `SalsaStream` and sets the wrapper as the main stream; for
`memory()` the next start wraps the wrapper again, and two layers of one keystream cancel.
A refused start leaves its wrapper too. For a directory, each start opens the files anew,
and a builder started again works (`probe/FileBuilderReuse.java`). In memory only, so no
data is exposed; a test that restarts an encrypted database in memory meets it.

### U7-6. parse() refuses a trailing newline; the name is free (API, low)

A key kept in a text file often ends with a newline (an editor, `echo`): `parse()` refuses
it with `FormatException` "Bad keyData format.", which does not point at the newline; a
trailing space gives the same. A leading space is taken into the name, and the key works
(U7-4). A user trims, after finding why; `parse()` could trim, or say "whitespace" in its
message. The other damaged strings were refused with clear messages (three parts, the
length of the key data, its hex), and none of the messages or `toString()` held key data.

### U7-7. The right key on a damaged stream: "the wrong crypto key" (doc, low)

With the right key, a stream whose last meta block is damaged (in a small database, the
first bytes; `probe/Damage.java`, bytes 0 to 3) gives `BadCryptoKey` "Likely, the wrong
crypto key was used. Invalid magic bytes in stream.": a user then thinks the key is wrong
or lost. `BadCryptoKey`'s Javadoc and `DatabaseBuilder.start()` name damage only for a
start without a key. And "damaged at its beginning" holds only for a small stream: in a
1.1 MB vault, with the key, and in a 1.2 MB database without one, a byte changed at
offsets 0 to 200 was not noticed by the start, nor by a scan; the start reads the stream's
last meta block, not its beginning. The message could say "the wrong crypto key, or the
stream is damaged", as the one without a key does.

### U7-8. getKeyData() keeps a dated history note (doc, low)

`CryptoKey.getKeyData()`'s Javadoc says "(2026-11-09, bergdb 020-20, N1: the key's own
array, so a caller could change the key)". `releases/next.md` says that the sentences on
how a method behaved before a change, and their dates, are gone from `CryptoKey`, the
release notes keeping the history.


## 3. What went well

* Confidentiality of the files at rest, for one database written once: none of 4,002
  needles in the vault's files, against 3,993 of 3,996 in the control without a key; the
  key in no file, `toString()` masked, no key data in any message.
* Every wrong start refused with `BadCryptoKey` and a clear message (no key: "likely, the
  database is encrypted and needs its key"), with nothing written (the files' hashes
  equal), also after reclaim had cut the stream's front; the right key then started. The
  algorithm "aes" refused with `IllegalStateException`, also at a creation, which then
  created nothing, as the Javadoc says.
* Every value right against the oracle: 289 past states and 1,739 versions after a
  restart, indexes at past times (code point order with supplementary characters), the
  copy, the reclaim with 1 s retain (2,233 versions within the available time, after a
  restart too), 88,328 reads of past versions from the encrypted files by 4 threads beside
  a writer, the recovery after SIGKILL (at or after the last sync, a prefix of the ops), an
  index build retaken after a halt.
* Reclaim on an encrypted stream: the first available lookup time moved after 16 to 33 MB
  of puts, as `setRetainDuration()`'s Javadoc foresees (20 to 30 MB for a 5 MB startup
  distance), and the front was cut by 66 MB.
* The API for the key is small and right: `generate()`, `serialize()`, `parse()`, and
  `cryptoKey()` whose last call counts.


## 4. Fixes

Made 2026-11-09 for coord-1109 by the fixer e07, in the clone
`/Users/f/fl/bench/2026-11-09/clone-e07`, by the rule for 2026.4: a stable baseline, no
change of the stream's format, the Javadoc made true, a plain bug fixed with a failing
test first. Three commits, each with a line in `releases/next.md`: on its branch `main`
from `bd92096` (`9598088`, `16b2063`, `14de355`), each gated under the gate lock; and on
the branch `try-rebase`, the same rebased on `main` at `62345d3` (`7c6ad11`, `f15d1a7`,
`bc3cd44`; a conflict of `releases/next.md` alone, both entries kept), gated on its tip
under the lock: BEFORE COMMIT OK (151 s, unit 1580, f 86), JAVADOC PUB OK.

* **U7-5** (`9598088`, a plain bug, the test failing first): the builder keeps the
  `SalsaStream` that its last start made around the stream of `memory()`, and the next
  start, with a key or without, takes the stream under it again before it wraps it. Every
  start on the closed stream with the key reads it, and a start refused for its key leaves
  nothing behind. Test `PubTester.testRestartsOfMemoryBuilderWithCryptoKey`;
  `probe/MemKey.java` on the fixed jar gives every line as expected. BEFORE COMMIT OK
  (151 s).
* **U7-2** (`16b2063`, a plain bug, the test failing first): the cause was the forces.
  `SalsaStream.append()` passed each flush of the write buffer (up to 5 MB) to the
  `FileStream` in parts of 100 kB, and the `FileStream` forces each append: up to 50
  forces in place of one, which no sync level asks for (`FileStream`'s design is one force
  per flush). Now one append: its buffer grows to the longest append, up to 16 MB (the
  database's flushes are at most 5 MB by default). The bytes written are unchanged. Test
  `SalsaStream.testOneForcePerAppend`: 8 forces where a plain `FileStream` makes 4,
  before the fix. BEFORE COMMIT OK (143 s), LEVEL 1 OK. `probe/Cost.java`, two rounds
  each, on F53 under a load of 10 to 23:

  | Database         | Puts        | Restart and scan |
  |------------------|-------------|------------------|
  | no key, before   | 2.5, 1.6 s  | 2.2, 2.2 s       |
  | with key, before | 11.0, 9.8 s | 2.3, 2.5 s       |
  | no key, after    | 1.5, 1.2 s  | 2.1, 1.7 s       |
  | with key, after  | 1.3, 1.3 s  | 2.3, 2.1 s       |

  Salsa20 alone, in memory: about 400 MB/s on F53, 2.5 ns per byte; that is the cost of a
  key now, and the Javadoc gives it.
* **U7-1, U7-3, U7-4, U7-6, U7-7, U7-8** (`14de355`, the Javadoc and one message): the
  package `bergdb.pub` has a section "Encryption": what is encrypted and what is not, one
  key for one database with the three cases of keystream reuse as a limit of 2026.4,
  secret but not unchanged, the key (one database, no change, a lost key loses the
  database, the name is for people), and the cost. `DatabaseBuilder.cryptoKey()` and
  `CryptoKey` say it in short and link to it; `CryptoKey.parse()` says what it takes,
  whitespace too (U7-6, the behaviour left); `getKeyData()` without its dated note (U7-8).
  U7-7: the message with a key names a damaged stream too ("Invalid magic bytes in
  stream, read with the crypto key given: likely, the wrong crypto key was used, or the
  database is not encrypted; else the stream is damaged, or it is not a BergDB stream.");
  `BadCryptoKey` and `DatabaseBuilder.start()` say where the start reads first, the magic
  bytes of the last meta block, one at every 200,000 bytes, so "its beginning" only for a
  database of less than 200 kB. Test `PubTester.testDamagedStreamWithTheRightKey`,
  failing before. JAVADOC PUB OK, BEFORE COMMIT OK (145 s).
* **Removed from 2026.4's API** (020-28, `b78865d` on `main`; Frans, 2026-11-09, 16:12):
  the crypto key, `CryptoKey` and `BadCryptoKey` left the public API; the code stays inside
  BergDB, internal and tested, with the fixes of U7-2 and U7-5; a database that 2026.3
  encrypted is refused. The options below are 017-10, for a later release.

For Frans, options to fix U7-1 and U7-3 in a later release, each a change of the format:

* U7-1, A: a random nonce per database, in clear at the stream's start, mixed into
  Salsa's nonce. Ends case 1 only (two databases, one key); a header in clear.
* U7-1, B: a random nonce per start that writes (an epoch), in clear in a small record
  where its appends begin and named by each meta block; a read takes a position's epoch
  from them. Ends all three cases at about 16 bytes a start; today's streams read as
  epoch 0. A new record type and a meta block field.
* U7-1, C: B with XChaCha20 and a 192-bit random nonce per epoch, so that no two epochs
  can collide.
* U7-3, A: authenticated pages: the encryption writes fixed pages (such as 64 kB) with a
  Poly1305 tag each (XSalsa20-Poly1305), and a read checks its page. The files' positions
  then differ from the stream's, and a random read reads a whole page.
* U7-3, B: a keyed check (a 64- or 128-bit MAC) in place of Fletcher-16 in each node and
  record of an encrypted database: a forged node or value is refused; headers grow.
* U7-3, C, for rollback and a cut tail: a MAC chain over the stream in the meta blocks,
  its last value kept by the application; without state kept outside the files, no design
  finds an older copy.
