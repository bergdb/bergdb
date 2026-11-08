021-06. Investigate: a string that is not well-formed UTF-8 in a stream from another writer
=========================================================================================

Status: done. Kind: Investigate. Frans: answers (delegated, 2026-11-08).
Created 2026-11-07 by Frans Lundberg.

What: the read side of 021-04's rule. Every stream Java writes holds only
well-formed UTF-8 in its strings, but another writer may put other bytes
where a string should be, and Java's reader repairs them silently:

* Keys. The C clone's `bergdb_ikey_to_bkey` (012, at release 2026.2)
  takes any bytes but 0xFE and 0xFF; "The bytes are not checked to be
  UTF-8" (`include/bergdb.h`). It takes `ED A0 80` (WTF-8 of U+D800),
  `EF BF BD` (U+FFFD), '?' and `C0 80` in an ikey (021-04, section 5,
  CK1 to CK4). Java's `Keys.bkey2ikey` decodes with `StringUtil.toString`,
  which puts one U+FFFD in place of `ED A0 80`: Java reads the first two
  keys as the same String (JR1, JR2, JR4), and `Keys.toBytes` of it gives
  the second bkey, so the first key's value cannot be got by its key from
  Java (JR5). The Core API takes any bkey; 2013-key-encoding says "An
  arbitrary bkey cannot, in general, be converted to an ikey".
* Values and objects. A String value read with `get(key, String.class)`
  and an object's `s` fields and field names (`DbString.parseToString`,
  `DbObject.readFieldInfo`, `DbField.parse`) decode the same way: Java
  gives one U+FFFD for `ED A0 80`, where JavaScript, Python, Go and Swift
  give three (021-04, section 4.4), so two readers of one stream disagree.
* In Java too: `new DbObject(byte[])`, public in `pubimp`, takes an
  object's bytes as given, and a put of such a `DbObject`
  (`RwEnvironmentImp.ObjectInfo`) stores them, ill-formed strings and
  all; the String paths refuse since 021-04, this bytes path does not.

Why: 021-04's decision (Frans, 2026-11-07, 09:33, option 1) says that a
reader may rely on the rule; a reader that meets ill-formed UTF-8 must do
something defined, the same in every language, not repair it in a way
that differs by language and makes two keys one. 021-04, "Two questions
remain", the second, and section 4.4.

Frans: answers. Frans, 2026-11-07, 09:34: ""Two problems found". Yes, add
entries." The default (021-04): settle it with 020-01's object spec (F1,
question 5: is the object format part of the stream's format, and who
writes its spec). The questions, prepared by the investigation:

1. What does a reader do with a string that is not well-formed UTF-8: a
   String value, an object's string or field name? 021-04's default:
   report it, in Java with `DataFormatException` ("data in the database
   has an illegal format"), rather than repair it.
2. A key that is not well-formed UTF-8: is it a bkey without an ikey, as
   2013-key-encoding says, which the Pub layer skips or reports in a scan
   and cannot get by a String key? Or is it refused by every writer,
   the C clone's `bergdb_ikey_to_bkey` included, at a later port?
3. Does a put of a `DbObject` made from bytes check its strings, or does
   it go with 020-01's F1 decisions (a closed list of types, `DbObject`
   public or not)?

Done when: Frans has answered; the rule for readers is written in the
object format's spec (020-01, F1) and in the Core's `key-encoding.md`;
the Java reader does what it says, with a test of the CK1 and CK2 bkeys
(the two keys stay two, or are reported); `BEFORE COMMIT OK`; a line in
`releases/next.md`.

Answers, decided 2026-11-08 under Frans's delegation (22:17, "make the
decisions needed to get the 2026.4 release ready"; 006-15), as the night's
coordinator set them:

1. **A reader never repairs ill-formed UTF-8.** A String value or a key
   that is not well-formed is reported, never turned into U+FFFD. Java:
   `DataFormatException` for a value read as a String (`get(key,
   String.class)`, and as `Object.class` at a `.txt` key, where it is a
   String); a value read as a `byte[]` is its bytes, as always. For
   objects this is format 2's rule already (020-02, section 4.9; 020-07,
   R6 and R11), done by the objects' steps (020-08) in `DbObject` and the
   value classes.
2. **A bkey that is not well-formed UTF-8 is a bkey without an ikey**, as
   2013-key-encoding says. The Core API reaches it by its bkey; the Pub
   layer's scans leave it out; a get by a String key cannot name it (a
   String key's bkey is well-formed). Java's `Keys.bkey2ikey` no longer
   decodes with U+FFFD: it throws for such a bkey, and
   `Keys.bkey2ikeyOrNull` returns null. CK1 and CK2 stay two keys: CK1
   has no ikey, CK2 is the key with U+FFFD. Also without an ikey: a bkey
   with the byte 0x31 ('/' + 2), which no ikey gives (its ikey's bkey would
   have 1 there), so that two bkeys never give one ikey. The C clone's
   writer (`bergdb_ikey_to_bkey`) refuses such keys at a later port, not
   in 2026.4.
3. **A put of a `DbObject` made from bytes** gets format 2's full check:
   the objects' steps (020-08, 020-07, section 7.4), not this entry.

Done (2026-11-08, commit "021-06: ..."): the rule in the Core's
`doc-files/key-encoding.md` ("Conversion bkey --> ikey"); `Keys.bkey2ikey`,
`Keys.toString(long[])` and the new `Keys.bkey2ikeyOrNull` strict, with
`StringUtil.isWellFormedUtf8` (RFC 3629, tested against the JDK's decoder
set to report); `Klong.getKeyString`, a debug printer of 7-byte pieces of a
key, shows the bytes with `Keys.toDisplayString`; the primary scan
(`UsePrimaryBuilderImp`) leaves out a bkey without an ikey and a key whose
name in the directory has a '/' (an ikey that no ukey of the directory
gives, such as "/dd/-x/y" written through the Core). Tests:
`Keys.testBkeyWithoutIkey`, `Keys.testBkeyIkeyRoundTrip` (100,000 random
bkeys: none, or the ikey's bkey is the bkey), `StringUtil.testIsWellFormedUtf8`,
`Utf8ReadTester.testCk1AndCk2StayTwoKeys` and
`testScanPastKeysWithoutIkey`.

Left, for the coordinator: the String value's read is in
`KvToObjectImp.entryToString`, a file of the objects' steps tonight (020-08),
so its fix and its failing test are a patch,
`/Users/f/fl/bench/006-15/clone-021-06/021-06-string-values.patch`, to apply
after 020-08's step 2 (it also adds a `@throws DataFormatException` to
`Connection.get` and a sentence to `UsePrimaryBuilder`). Then this entry is
done, with a line in `releases/next.md` by the coordinator. Also for others:
the index build (`IndexBuilderImp`, step I2 of 020-10) converts every key it
visits with `Keys.toString`, so a key without an ikey after a directory
fails a build of it (as a `RuntimeException` does, 019-42) until I2's build
reads only the directory's keys and leaves such keys out
(`Keys.bkey2ikeyOrNull`); `Connection.transactionInfo()`'s `Kv.key()` throws
`IllegalArgumentException` for such a key, as for any key without a ukey.

First step: a list of Java's read paths that decode UTF-8
(`StringUtil.toString` and its callers: `Keys.bkey2ikey`,
`toDisplayString`, `DbString.parseToString`, the field names, the index
sort keys, scans), what each does with `ED A0 80`, `C0 80` and a cut
sequence, and what a report there would cost; then the questions above,
with 020-01's F1.


Log
---

2026-11-07. Registered by agent u04 of coord-1107 (006-14) from 021-04's
"Two questions remain" paragraph and sections 3.2 and 4.4, at Frans's
word (09:34, quoted above).

2026-11-08. The answers decided under Frans's delegation (22:17), as the
night's coordinator set them (006-15); the key side done, with its tests,
and the String value's read as a patch for after 020-08's step 2 (above).
Status: in progress.

2026-11-09. The patch applied by the objects' agent of the night, in its
own commit after 020-08's step 3: `KvToObjectImp.entryToString` throws
`DataFormatException` for a value read as a `String` (or as `Object` at a
".txt" key) that is not well-formed UTF-8, with `Connection.get`'s
`@throws`, `UsePrimaryBuilder`'s sentence and `DataFormatException`'s
Javadoc; `Utf8ReadTester.testStringValueNotWellFormed` and the testers that
expected U+FFFD. One change for format 2: `PubTesterPrimary.
testTypesListByKind` listed an object's first 3 bytes as a `String`, which
were "ber" in format 1 and start with the header 0x82 since 020-08's step
2, no UTF-8: the test now expects the `DataFormatException` for it, and
the listing to go on. `BEFORE COMMIT OK`. Status: done; `releases/next.md`
is the coordinator's.
