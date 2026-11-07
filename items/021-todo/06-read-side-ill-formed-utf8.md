021-06. Investigate: a string that is not well-formed UTF-8 in a stream from another writer
=========================================================================================

Status: open. Kind: Investigate. Frans: answers.
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
