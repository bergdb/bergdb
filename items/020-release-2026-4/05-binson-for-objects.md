# 020-05 Binson for objects: feasibility, pros and cons

Created 2026-11-07 by Frans Lundberg. Status: open. A study of Binson
(binson.org) as the byte format of BergDB's objects (`DbObject`) in
release 2026.4, in place of today's format: the types, the bytes, the
reads, the kind of a value, other languages, the spec's governance and
the cost, with measurements, the options and a recommendation, for
Frans to decide (020-02, question 4).

Frans, 2026-11-07, 20:42: "I want you to study something for me. [...]
Read binson.org, the website. I want you to study the possibility of
using Binson for storing objects in BergDB. The serialization format of
DbObject would be Binson instead of the current one. Currently I have no
strong preference between those. Just want an investigation of the
feasibility of using Binson here. Pros and cons compared to the current
format. Consider this in detail, please."

How each fact is known: **run** with a label (S, B, W, BJ, DB, JS, PY, C,
SW) means a program's output line, from the programs in
`/Users/f/fl/bench/006-14/020-binson/` (its `readme.txt` says how each
was run; section 14); **code** means read in the source named (BergDB at
`a7fe143`, the Binson implementations as cloned on 2026-11-07); **docs**
means a document of section 15, read on 2026-11-07.


## 1. In short

* **Feasible.** Binson's types are DbObject's eight with one integer and
  no null: shape 1's closed list, question 1b's no-null lean, question
  1's exactness by value. Fields sort in DbObject's order (UTF-8 bytes).
* **Half the bytes**: 1.3 to 2.8 times smaller on eight typical objects;
  an index definition 95 bytes against 146 (S).
* **Reading is the trade.** DbObject's stored field table finds a field
  in 10 to 30 ns; Binson reads in order, 26 to 370 ns here, 50 µs behind
  a 10,000-element array (B, W). Today's code ignores the table and
  parses the whole object: 340 to 720 ns per field read (B).
* **A spec exists**, three pages, canonical, with strict readers in Java,
  C and Python; BergDB adds a profile: UTF-8 as a must, depth, limits.
* **Other languages get less than the list suggests**: binson-js and
  binson-java refuse each other's bytes for some names (JS9, BJ25); Rust
  has no parser. Java and C (binson-c-light, no malloc) are solid.
* **Options**: (a) keep the format; (b) Binson with a profile; (c) Binson
  behind a BergDB header, with or without a field table; (d) DbObject's
  format moved towards Binson's types.
* **Recommended: (c1)**, Binson under a profile behind a short header of
  kind and version, no stored field table for now (section 13).


## 2. The question and the method

The question: should the bytes of a stored object be a Binson object
(BINSON-SPEC-1.1) instead of DbObject's own format (`bergo`, a version,
a field table, the fields), with no backward compatibility needed in
2026.4 (020's readme: "No need for any backwards-compatibility")?

Read: 020-01 (section 4, F1, and the index sections F3, F4, F6); 020-02;
020-03's Binson parts; 020-04, section 3; 021-04, 06, 07 and 08;
`DbObject.java` (its Javadoc, the 2013 notes at its end, `Builder.build`,
`parse`, the lookup), `DbValue`, `DbArray`, the `Db*` value classes,
`Entries`, `FieldIndexFunction`, `IndexBuilderImp`, `RwEnvironmentImp`,
`KvToObjectImp`; 012 and 006-08 for C. binson.org in full: the spec,
BINSON-SPEC-1 (2014), BINSON-SCHEMA, the list of implementations; then
each implementation's source on GitHub (twelve repositories, section 8).

Run, on F53: the sizes of eight sample objects both ways (S); what
binson-java and DbObject's reader accept, refuse and change (BJ, DB);
encode, decode and one-field reads, both ways (B, two JVM runs; W, a
worst case); field order and strictness in binson-js (JS), binson-python
(PY), binson-c-light (C) and Swift's strings (SW).

The terms: **today** is BergDB's code at `a7fe143` (021-08's reader);
**the field table** is DbObject's per-field 16-bit hash and 32-bit
offset after its header; **in order** is a read that walks the fields
from the start.


## 3. The two formats

DbObject, version 1 (`DbObject.Builder.buildInner`; code):

    object = "bergo" version(1) count(int16) count*info count*field
    info   = hash(int16) offset(int32)        ; offset from the object's start
    field  = type(1 char) nameLen(int16) name value
    n: 1 byte (0 or 1)   i: int32   l: int64   d: float64 (raw bits)
    s, b: int32 length (-1: null) and bytes    o: int32 size, then an object
    a: elements, each a type byte and a value, then 'z' ('Z': a null array)

Little-endian; fields sorted by the unsigned bytes of their UTF-8 names;
names 1 to 32,767 bytes; at most 32,767 fields; the hash is
`(short) (len + 23 * name.charAt(0) + 43 * name.charAt(len - 1))` over
the Java `String`, that is over UTF-16 units (DB8).

Binson, BINSON-SPEC-1.1 (docs; the ABNF in short):

    object  = 0x40 *(string value) 0x41       value = one of the seven
    boolean = 0x44 (true) / 0x45 (false)      double = 0x46 float64
    integer = 0x10 int8 / 0x11 int16 / 0x12 int32 / 0x13 int64
    string  = 0x14/0x15/0x16 length (int8/16/32), then UTF-8 bytes
    bytes   = 0x18/0x19/0x1a length (int8/16/32), then the bytes
    array   = 0x42 *value 0x43

Rules: values "stored using as few bytes as possible"; fields in "the
lexicographical order of the UTF-8 bytes of the name", "compared as
unsigned numbers"; no two fields of an object with one name;
little-endian. "With these definitions, the rules of section 3 give each
Binson object exactly one serialization."

One object both ways, `Payment {from "1001", to "1002", amount 500}` (S2):

    DbObject, 71 bytes:
      626572676f 01 0300                       bergo, version 1, 3 fields
      391c 1a000000  7d1b 2b000000  131d 3a000000           hashes, offsets
      6c 0600 616d6f756e74 f401000000000000    l "amount" 500
      73 0400 66726f6d 04000000 31303031       s "from" "1001"
      73 0200 746f 04000000 31303032           s "to" "1002"
    Binson, 35 bytes:
      40
      14 06 616d6f756e74 11 f401               "amount" 500 (int16)
      14 04 66726f6d 14 04 31303031            "from" "1001"
      14 02 746f 14 04 31303032                "to" "1002"
      41

The fields come in the same order in both: the two formats share the
field model, and differ in the header, the table, the widths and null.


## 4. The types

| Type | DbObject today | Binson 1.1 |
|---------|------------------------------------|----------------------------------|
| boolean | `n`, a byte 0 or 1                 | two type bytes, 0x44 and 0x45    |
| integer | `i` (int32) and `l` (int64)        | one integer, int64, minimal size |
| double  | `d`, raw bits kept (DB7)           | float64; NaN 7ff8... recommended |
| string  | `s`, well-formed UTF-8 (021-04)    | UTF-8 "should" be valid only     |
| bytes   | `b`                                | bytes                            |
| array   | `a`, any values mixed              | array, any values mixed          |
| object  | `o`, nested with its own header    | object                           |
| null    | of `s`, `b`, `a`, `o` (020-04: go) | none: "Binson has no nulls :-)"  |

**int and long.** A Java `byte`, `short`, `char` or `int` is stored as
`i`, a `long` as `l`; Binson stores each as one integer in the fewest
bytes. What is lost is the writer's declared width. Question 1's option
(A) decides exactness "by the value, not the type" (020-02, section
2.3, reason 3), so the width is not used there: a stored 5 reads into an
`int` whether it was `i` or `l`. Under Binson question 1's table loses
rows: "integer: into `long` always; into `int` and smaller if it fits;
into `double` and `float` if held exactly". A JavaScript or Python
binding no longer chooses between `i` and `l`. A long index reads `i`
and `l` today (`FieldIndexFunction`, `TYPE_LONG`); it reads the integer.

**double.** Both store the 64-bit pattern. DbObject keeps NaN payloads
(`doubleToRawLongBits`, DB7); Binson recommends one NaN pattern, and
binson-java 3.5 writes it, but its reader keeps any (BJ12: a signalling
NaN is read and written back as `7ff8...`). -0.0 and 0.0 are two values
in both (BJ13). A BergDB profile would make the NaN rule a must.

**strings.** BergDB's rule (021-04, Frans, 09:33: "option 1,
absolutely") is that every string is well-formed UTF-8, refused at a put
otherwise. Binson 1.1 makes it a recommendation: "A Binson
implementation need not check this." So the rule stays BergDB's, in its
profile: binson-java writes `?` for a lone surrogate (BJ1), the fault
005-26 had and 021-04 removed; binson-js writes U+FFFD (JS3). On the read
side (021-06, open) binson-java and binson-c-light accept ill-formed
UTF-8 (BJ2, C5), and Java and JavaScript decode `ED A0 80` to one and
three U+FFFD (BJ2, JS8); binson-python refuses it (PY5). A field name is
a string too; Binson allows the empty name (BJ6), DbObject refuses it.

**null.** Binson's choice is the one 020-02 leans to (question 1b, (d),
Frans 14:31): a field is present with a value, or absent. Under Binson
020-04's rules for the put and the get stay as written; its format part
(section 3.1, four null encodings to refuse) is not needed, since
Binson has no encoding for a null. binson-java refuses a null at a put,
in an array, and in JSON (020-03, BN1 to BN3; BJ21).

**How 020-02's questions come out under Binson:**

* Question 1b, null: no null by the format; (d)'s put and constructor
  check unchanged; nothing to remove from the bytes.
* Question 1, exactness: by the value, as (A) and (D) propose; one
  integer type makes the table shorter; (D)'s report says "stored
  integer 1099511627776 into `int` field `count`".
* Question 2, the closed list: unchanged; the Java types map to the
  seven as they map to the eight today.
* Question 3, the kind of a value: Binson marks an object with one byte,
  0x40, against `bergo`'s five; section 7.
* Question 4, the format and its spec: the spec exists; BergDB writes a
  profile of it (section 9).


## 5. The bytes

### 5.1. Size

S, bytes per object, as `toDbObject` writes them and as binson-java
writes the same fields (a null field left out; none of these has one):

| Sample (where it is stored) | Fields | DbObject | Binson | Ratio |
|------------------------------------|----|-----|-----|------|
| `Person` (PubTester)               | 1  | 30  | 15  | 2.00 |
| `Payment` (PubTester, index tests) | 3  | 71  | 35  | 2.03 |
| `Account` (PayTest, night)         | 1  | 32  | 13  | 2.46 |
| `Foobar` (BryanRepro, level2.sh)   | 7  | 243 | 181 | 1.34 |
| `Dialog`, two nested objects       | 2  | 102 | 36  | 2.83 |
| `Data.Index`, an index, 1 level    | 5  | 146 | 95  | 1.54 |
| `Data.Index`, an index, 2 levels   | 5  | 168 | 111 | 1.51 |
| `Customer` (made up, two arrays)   | 12 | 349 | 225 | 1.55 |

Per object: 8 bytes against 2 (an empty object, S5); a nested object
adds 4 + 8 bytes of size and header and its field's 6-byte info against
2. Per field: 9 bytes plus the name (6 info, 1 type, 2 name length)
against 2 plus the name (names under 128 bytes); then the value, fixed
widths against the fewest bytes. S6, one field named `amount`, bytes
added to an object:

| Value | DbObject | Binson |
|--------------|----|----|
| int 5        | 19 | 10 |
| int 100000   | 19 | 13 |
| long 5       | 23 | 10 |
| long 2^40    | 23 | 17 |
| double 1.5   | 23 | 17 |
| boolean      | 16 | 9  |
| string hello | 24 | 15 |
| bytes[16]    | 35 | 26 |

DbObject's 2013 note ("Overhead for a single int", at the end of
`DbObject.java`) counted 22 bytes for a wrapped `int` and asked for
less; in Binson `{p: 8}` is 7 bytes. A value's bytes go to the stream,
to reclaim's copies, and to the memory of resident nodes (the MEM
metric, 006-02); a large value is dominated by its strings and bytes,
where the two differ by a few bytes (Foobar, 1.34).

### 5.2. One object, one byte string

Both writers are deterministic (P2): fields sorted by name bytes, one
encoding per value. They differ in what a reader accepts:

* **DbObject's reader is lenient** (DB1 to DB6, run on 021-08's reader):
  it accepts a field info whose hash is not its name's (the field is
  then invisible: `getType` 'z', `getInt` 0, DB2), infos out of order
  (DB3), two infos for one field with another field hidden (DB4),
  bytes after the last field (DB5), and string bytes that are not UTF-8
  (read as U+FFFD, DB6; 021-06). Each is a second byte string for one
  object, or bytes that read differently by the lookup taken. A strict
  reader could check all of it in its one pass; 021-07 and 021-08 did
  not aim at that.
* **binson-java's reader enforces the canonical form** for order,
  uniqueness and integer sizes (BJ7 to BJ10), and binson-c-light and
  binson-python for order and integer sizes (C3, C4, PY3, PY4).
  binson-java accepts bytes after the end (BJ14; binson-c-light and
  binson-python refuse them, C6, PY7), any NaN pattern (BJ12) and
  ill-formed UTF-8 (BJ2, BJ3). binson-js accepts a non-minimal integer
  (JS7).

So "one object, one byte string" holds for both writers, and for neither
reader as it is; a BergDB profile reader closes the gaps in either.

### 5.3. The header and the markers

DbObject's header is 8 bytes: `bergo`, a version byte (1; a reader
refuses others), and the field count (−1 for a null object). Binson has
no magic and no version in its bytes: an object is 0x40 ... 0x41, and the
version is the spec's (BINSON-SPEC-1.1 "does not change the Binson
format" of 2014). A format version for BergDB's objects then lives
outside the Binson bytes: in a BergDB header (option (c)), or in the
database's or stream's version.

### 5.4. Limits

* **Name length**: DbObject 1 to 32,767 UTF-8 bytes (005-21); Binson 0 to
  2^31 − 1, and recommends names of `[a-zA-Z][a-zA-Z0-9_]{0,49}`.
* **Fields per object**: DbObject 32,767; Binson unlimited, "should" be
  under 100; binson-java's reader refuses more than 1,000 by default
  while its writer writes them (BJ11, BJ23).
* **Sizes**: both have 32-bit lengths; Binson recommends objects under 40
  million bytes, and binson-java's reader refuses larger ones by default
  (BJ16), before it allocates.
* **Depth**: DbObject's reader refuses more than 1,001 objects or 2,001
  objects and arrays on a path (021-08); the spec has no limit;
  binson-java has none and ends in `StackOverflowError` at 10,000 nested
  arrays or objects with a 1 MB stack (BJ4, BJ5), the fault 021-08
  removed from DbObject; binson-c-light's limit is a setting, 10 by
  default and at most 255 (C7 to C9); binson-python stops at Python's
  recursion limit (PY8).
* **Top level**: an object in both; DbObject wraps a top-level array in a
  field `array` and a primitive in `p` (`toDbObject`); Binson refuses a
  top-level array (BJ18), so the wrapping stays.

A BergDB profile must name its limits so that every binding can meet
them: a depth of 1,001 objects is beyond binson-c-light (255) and near
binson-python's default recursion limit.


## 6. Reading

### 6.1. How a field is found

* **DbObject's format**: scan the table's 16-bit hashes, compare the
  name at the offset, read the value: no other field is touched. A
  nested object has a 32-bit size, so a path `a.b` jumps; an array has
  no size or count and is walked.
* **Binson**: walk the fields in order; a string or bytes value is
  skipped by its length; an array or a nested object has no length and
  is walked to its end marker. Since the names are sorted, a reader
  stops at the first name past the one it wants.
* **Today's code does not use the table on reads.** `new
  DbObject(bytes)` checks the nesting (021-08), then parses every field
  (`DbField.parse` in the constructor, since the 2017 import), making a
  `String` of every name and string value and copying every nested
  object's bytes. Every read path constructs one first: a get and a scan
  (`KvToObjectImp`), index maintenance (`RwEnvironmentImp.indexEntries`
  reads the previous value), a build (`IndexBuilderImp`), and the index
  definitions at every start (`IndexManager`). `FieldIndexFunction` then
  calls `has` and `get` for each field; a nested path re-parses the
  nested object at each step.

### 6.2. Measured

B, ns per operation, the medians of two JVM runs (11 rounds each, run 1 /
run 2); how in section 14. "Today" is BergDB's code; "header lookup" is a
sketch of a reader that uses only the table (`Study.dbFind`); "direct
writer" a sketch of a Binson writer from reflection (`Study.writeBinson`);
BinsonLight is binson-java-light's pull parser, which checks neither
order nor integer sizes.

| Operation | Payment | Foobar | Index | Customer |
|---------------------------------------|---------|-----------|-----------|-----------|
| encode, DbObject today                | 670/673 | 1418/1440 | 1384/1379 | 2513/2523 |
| encode, binson-java                   | 386/390 | 635/636   | 796/791   | 1865/1853 |
| encode, direct Binson writer          | 179/179 | 132/128   | 185/182   | 573/561   |
| decode into the class, DbObject today | 672/665 | 857/713   | 1019/994  | 1972/1970 |
| decode, binson-java and mapping       | 285/283 | 548/542   | 587/590   | 1389/1390 |
| decode, BinsonLight pull reader       | 101/100 | 178/180   | 330/334   | 642/659   |
| parse only, `new DbObject` today      | 307/308 | 281/282   | 569/568   | 618/620   |
| parse only, binson-java (strict)      | 325/322 | 391/389   | 374/376   | 885/886   |
| one field, DbObject today             | 417/417 | 342/343   | 703/707   | 716/722   |
| one field, DbObject header lookup     | 17/17   | 26/26     | 18/18     | 30/30     |
| one field, binson-java                | 330/327 | 395/394   | 384/378   | 893/888   |
| one field, BinsonLight in order       | 86/80   | 179/172   | 132/127   | 371/369   |
| first field, header lookup            | 10/10   | 9/9       | 9/9       | 10/10     |
| first field, BinsonLight in order     | 26/26   | 27/27     | 26/26     | 25/26     |

The field read: `from` (second of 3) in `Payment`, `uuid` (last of 7) in
`Foobar`, `state` (third of 5) in the index definition, `zip` (last of
12, after two arrays) in `Customer`.

W, the worst case for a read in order: a field `name` behind an `int[]`
field `arr` (one run):

| Object | DbObject today | Header lookup | BinsonLight | binson-java |
|----------------------|--------|----|--------|---------|
| `arr` of 100 ints    | 489    | 22 | 568    | 1,869   |
| `arr` of 10,000 ints | 35,377 | 17 | 49,676 | 187,243 |

### 6.3. What it means

* **A get into a class** reads every field, so the table does not help;
  the cost is the decoder's. A Binson pull reader into the class was 3 to
  7 times faster than today's DbObject path on these objects (B), most of
  it implementation: today parses twice (the constructor, then a lookup
  per class field) and allocates per field.
* **Index maintenance and builds** read one to a few fields of each
  object. The table's lookup is 10 to 30 ns at any position; Binson in
  order is 25 ns for an early field and grows with what comes before it:
  80 to 370 ns on these objects, about 5 ns per array element walked
  (W). Today's code pays 340 to 720 ns for any field. So against today
  Binson in order is faster on the four objects and slower behind an
  array (W: 568 against 489 ns at 100 ints, 50 µs against 35 µs at
  10,000); against what DbObject's format allows, it is 2.5 to 12 times
  slower on the four objects, and without bound behind large arrays or
  nested objects. A build of 10 million objects at 400 ns per object is
  4 s of CPU; next to the reads of the values from the stream, that
  matters only for objects with large arrays or nested objects that sort
  before the indexed field.
* **Scans** convert every object: as a get.
* **Writes** are single pass in Binson, with no sizes or offsets to
  compute first: a direct writer took 130 to 570 ns (B); DbObject's
  writer needs every field's size before the table, and a nested
  object's size before its bytes. Today's `toDbObject` also parses the
  object it built (`buildInner` ends with `new DbObject(bytes)`).
* **Safety** (021-07, 021-08): a reader must refuse bad bytes without an
  `Error`, in either format. A table lookup that skips validation still
  needs bounds checks on its path; a Binson walk checks what it walks.
  Both need the depth limit.

The figures are a guide, not a benchmark: one machine, small objects,
sketches beside real code.


## 7. Telling an object from other bytes

Today (020-01, section 4.2, and N4): nothing is stored; a value is an
object when its key has no suffix (or `.obj`) and its bytes start with
`bergo` (`Entries.isProbablyDbObject`). A `byte[]` or `String` value that
starts with `bergo` is an object to a build, to `get(key, Object.class)`
and to a primary scan (N4); `PubPromiseTester` changes such a first byte
to avoid it.

* **Binson's marker is one byte**, 0x40 (`@`): a `String` value
  "@home" or a `byte[]` starting with 0x40 at an object key would pass a
  first-byte test. A strict parse of the whole value (0x40 ... 0x41,
  sorted names, minimal integers) is a much stronger test, but still a
  guess, and it costs a parse per value in a scan.
* **So with Binson, question 3 has to be answered, not left to a
  marker.** Three ways: (i) a BergDB header before the Binson bytes,
  holding the kind and a version (option (c)); (ii) the kind in the
  Core's entry, a stream format change under 018-01's rule; (iii) a rule
  of the keys or directories: an object key or an indexed directory
  holds objects only, refused otherwise at the put (020-01, section 14,
  decision 6). (iii) needs no bytes, and makes 015-46's case (a
  `String` put over an object in an indexed directory) a refused put.
* Should a value's kind be stored? With DbObject's format it may stay a
  guess, as `bergo` is a fair marker; with Binson it must be stored ((i)
  or (ii)) or fixed by a rule ((iii)). Either removes a guess from every
  scan and build, whatever the format.


## 8. Other languages

### 8.1. The implementations

binson.org names twelve, the Rust one by its crate. Metadata from GitHub
and crates.io on 2026-11-07 (`impl/repos.tsv`):

| Language | Repository | Licence | Last commit | API |
|------------|---------------------------------|---------------|------------|---------------|
| Java       | franslundberg/binson-java       | MIT           | 2026-10-07 | tree, JSON    |
| Java       | franslundberg/binson-java-light | public domain | 2026-10-07 | pull, writer  |
| C          | assaabloy-ppi/binson-c          | MIT           | 2026-10-07 | streaming C89 |
| C          | assaabloy-ppi/binson-c-light    | MIT           | 2024-08-07 | in place      |
| JavaScript | assaabloy-ppi/binson-js         | MIT           | 2019-09-11 | tree          |
| Go         | assaabloy-ppi/binson-go         | MIT           | 2026-10-07 | pull, writer  |
| Go         | hakanols/binson-go              | MIT           | 2021-01-29 | tree          |
| Swift      | assaabloy-ppi/binson-swift      | MIT           | 2019-10-28 | tree          |
| Python     | assaabloy-ppi/binson-python     | MIT           | 2025-08-26 | tree          |
| PHP        | assaabloy-ppi/binson-php        | MIT           | 2018-12-08 | arrays        |
| Erlang     | assaabloy-ppi/binson-erlang     | MIT           | 2019-06-13 | encode/decode |
| Rust       | crates.io binson 0.1.0 (dvdplm) | MIT           | 2017-11-30 | writer only   |

Notes, each from the code or a run:

* **binson-java** (release 3.5, 2,903 lines, Frans's): a `HashMap` tree,
  sorted at write; strict reader (order, uniqueness, integer sizes,
  `maxSize` 40e6 and `maxFieldCount` 1,000 as settings); no depth limit
  (BJ4, BJ5); no UTF-8 check either way (BJ1 to BJ3); JSON both ways,
  `bytes` as a `"0x..."` string, no null (BJ19 to BJ21).
* **binson-java-light** (one file, 679 lines, public domain by its
  README; GitHub finds no licence file it knows): a pull parser over a
  byte array without copies, and a writer; it checks neither order nor
  integer sizes ("Invalid Binson bytes can be produced").
* **binson-c-light** (c99, about 1,600 lines, "No dynamic memory
  allocation", tested on Cortex-M3 and M4): checks order, integer sizes
  and bytes after the end; depth a setting up to 255; no
  UTF-8 check (C1 to C9). The best fit for a C binding and for 006-08's
  small target.
* **binson-js** (ES module, BigInt through JSBI): sorts names with
  JavaScript's `sort()`, by UTF-16 units, not UTF-8 bytes. For names that
  mix U+E000–U+FFFF and characters above U+FFFF it writes the other
  order (JS1); binson-java and binson-c-light refuse its bytes (BJ25,
  C2), and it refuses binson-java's (JS9). It accepts a non-minimal
  integer (JS7); `putInteger` refuses 2^53 + 2 as a `Number` (JS4).
* **binson-python** ("not production stable", "a tool when testing"):
  the strictest run here: order, sizes, bytes after the end, and UTF-8
  both ways (PY1 to PY7); it needs `six`.
* **binson-swift**: a `[String: BinsonValue]` dictionary; Swift's `String`
  equality is canonical equivalence, so two names that differ only in
  normalization (`é` as one or two code points) are one key (SW1): a
  Binson object with both cannot be held.
* **Go** (ASSA ABLOY's): a port of binson-java-light, which checks no
  order; Håkan Olsson's sorts by bytes (`sort.Strings`; code).
* **Rust**: "This is not a complete implementation. For now only
  serialization works [...] lexicographically. This is not implemented."
  (its README); 2,072 downloads in all.

### 8.2. What a binding gets, and what it still needs

**For free**, where a good library exists (Java, C, Go, Python): the
encoder and decoder of the bytes, mostly strict, and a published spec
to test against. Not for Rust (a new codec), and with fixes for
JavaScript (the name order) and Swift (names as bytes, not `String`
keys).

**Still BergDB's**, in every binding, whatever the library:

* the profile's checks: well-formed UTF-8 at the put and at the read
  (021-04, 021-06), the depth limit (021-08), the field and size limits,
  the NaN pattern, non-empty names if chosen;
* the kind of a value (section 7) and any header;
* the conversion between the language's objects and the stored object:
  question 1's exactness and (D)'s report, question 1b's null as
  absence, question 2's closed list; this is most of a binding's object
  code, and it does not depend on the format;
* conformance vectors: a set of byte strings with their meaning and the
  refusals, shared by every binding (as 012-05's cross harness did for
  the stream). The JS9/BJ25 pair shows why: two implementations of one
  spec disagreed on the bytes.

With DbObject's format every binding writes its own codec from a spec
not yet written, including the UTF-16 hash (DB8: a C or Rust binding
must count a name's UTF-16 units and take its last one).

### 8.3. C: the clone and a small target

The C clone (012, release 2026.2's Core) treats an object as bytes and
has no Pub layer (012-01: a Pub database opens in C at the Core's
level); nothing changes there. A C Pub layer, or 006-08's embedded
target, would take binson-c-light (in place, no allocation, a bounded
state stack) or write a DbObject codec: about the same size, but with
the table's offsets and sizes to compute before writing.


## 9. Governance: Binson's spec as BergDB's object spec

* **The spec**: BINSON-SPEC-1.1, published October 2026, three pages,
  "Copyright Frans Lundberg 2014-2026", shared under CC BY-ND 4.0: it may
  be copied and cited ("Feel free to include it in your repo"), not
  published in a changed form. BergDB's object spec would cite it and
  add rules, which the licence allows; Frans holds the copyright anyway.
* **A profile, not a change**: every BergDB object is a Binson object;
  not every Binson object is a BergDB object. That is how I-JSON (RFC
  7493) restricts JSON ("a restricted profile of JSON": UTF-8, no
  duplicate names, no unpaired surrogates). The profile's rules:
  1. strings and names are well-formed UTF-8: a writer refuses, a
     reader reports (021-04, 021-06);
  2. depth at most N objects and M levels (021-08's 1,001 and 2,001, or
     lower so that small readers meet it);
  3. at most F fields per object, names of at most L bytes (non-empty?);
  4. NaN written as `0x7ff8000000000000` (a must, not "should");
  5. no bytes after the object's end (or a BergDB header before it);
  6. the top-level wrapping of arrays and primitives (`array`, `p`).
* **Still Binson?** Yes, as long as the rules only refuse: any Binson
  reader reads BergDB's objects. A field table or a header inside the
  object would not be Binson; a header before it (option (c)) leaves the
  payload Binson, and a binding strips it before calling a library.
* **Versions**: Binson 1 to 1.1 kept the bytes; BergDB would pin 1.1. A
  version of BergDB's own object format (the profile's rules, a header,
  a table later) needs its own number: in a header, or in the stream's
  or database's version.
* **The coupling**: Binson's types are fixed at seven and Binson has
  users outside BergDB (ASSA ABLOY's libraries), so BergDB cannot add a
  type and stay Binson. 020-02's shape 1 wants a closed, small list; the
  only types DbObject has beyond Binson are null (going) and the
  int/long split (not used by question 1's (A)).
* **018-01's rule** (Frans approves every change of the stream format)
  applies if 020-01's decision 7 puts objects under it: the index
  definitions are objects and every start reads them (020-04, section
  3.2). The switch is such a change; Frans's decision on this study is
  the approval, recorded in 020's log.


## 10. The cost of the change

**Java, to remove or rewrite** (code; sizes in lines with comments):

* the format layer: `DbObject.java` (1,254 with its notes; the builder,
  the parse, the nesting check, the lookup), `DbArray` (354), the six
  `Db*` value classes (591), `DbValue.parse` and the null values
  (`toNullDbValue`); the reflection (`toDbObject`, `toJavaObject`,
  `DbValue.toDbValue`) stays, writing to and reading from new code;
* new: a Binson profile writer (about 150 lines), a strict reader with
  021-07's refusals (bad lengths, bad type bytes, cut bytes) and 021-08's
  depth limit, plus order, integer sizes, UTF-8 and bytes after the end
  (about 300), and `DbObject`'s API as a view over Binson bytes (`has`,
  `getX`, nested paths, `getType` with one integer type; about 300);
* index code: `FieldIndexFunction` (a long index reads the integer;
  a few lines), `Entries.isProbablyDbObject` and `IndexBuilderImp`'s
  filter (the kind: section 7); `RwEnvironmentImp`, `IndexManager`,
  `KvToObjectImp` keep calling `new DbObject(bytes)`;
* 020-04's plan: its put, get and index rules stay; its format steps
  (the null encodings) go.

**Tests**: of `DbObjectTester`'s 79 tests, about 10 build or read raw
bytes (`testReaderBadLengths`, `testReaderCutBytes`,
`testReaderNestedObjectSizeMinusOne`, `testByteArray1`, the assumption
tests, ...) and are rewritten for Binson bytes; the round trips stay,
some with `i`/`l` expectations changed; new tests for each profile
refusal; PubTester's object tests are API-level and stay; a set of
conformance vectors (section 8.2).

**Data**: no backward compatibility is needed, but every database with
an object or an index stops opening (the index definitions are objects,
read at every start) unless a reader of version 1 is kept for them; the
night tests' and benchmarks' databases are made again, as after 005-50.
StreamDigest's workloads put `String`s and `byte[]`s only (020-04,
section 3.2): no digest changes.

**Not affected**: the Core, the stream format, the Lean model (objects
are values to it), the C clone.

**Size of the work**: M, 3 to 5 days with tests, about 020-04's plan
plus a second pass over 021-07 and 021-08's reader; in 2026.4, whose
theme is a bug-free release, it is new code where 021-07 and 021-08 just
hardened the old.


## 11. Pros, cons and risks

**For Binson:**

1. The same model as the decisions so far: the closed list of shape 1,
   no null as question 1b leans, one integer as question 1's exactness
   by value; DbObject's 2013 type list with int and long merged and null
   left out (020-03: Frans's note of 2013-05-22).
2. Smaller: 1.3 to 2.8 times on typical objects (S), most for small ones;
   a value's bytes are written to the stream, copied by reclaim and held
   in memory while resident.
3. A short, published, versioned spec with a canonical form; BergDB's
   object spec becomes Binson plus a page of rules (question 4).
4. Simpler writers in every language: one pass, no table, no sizes, no
   UTF-16 hash (DB8).
5. Existing, strict codecs in Java, C (for small targets) and Python.
6. Faster than today's code on the four objects measured, slower behind
   an array (B, W); most of the difference is implementation.

**For DbObject's format:**

1. A field is found in 10 to 30 ns at any position, also behind large
   arrays and objects (W); index reads of large objects stay cheap,
   once the reader uses the table.
2. An in-band marker and version (`bergo`, 1).
3. Fixed widths: no minimal-size rule for a reader to check.
4. No coupling to a format with other users; BergDB may add a type.
5. No change in 2026.4: no new reader in a bug-free release.

**Risks of the switch:**

1. A read in order behind a large array or object (W: 50 µs at 10,000
   elements); if user indexes on such objects matter, a field table must
   come back (option (c2)).
2. The ecosystem is thinner than binson.org's list: interop faults (JS9,
   BJ25, SW1), old or partial libraries (Rust, JS, Swift, PHP); a
   binding cannot trust a library without the conformance vectors.
3. Generic Binson libraries do not keep BergDB's rules (UTF-8, depth):
   a binding that uses one unwrapped stores what BergDB refuses.
4. The kind of a value must be decided (section 7) before or with the
   switch.
5. New code in the bug-free release, and old databases that stop
   opening.

**Risks of keeping DbObject's format:** its spec is still to write, and
every binding writes its own codec, the UTF-16 hash included; its reader
is lenient (DB2 to DB5) until made strict; its objects stay about twice
as large.


## 12. The options

**(a) Keep DbObject's format**, version 1, as 020-04 leaves it (no
null). Write its spec (020-02, question 4), with the hash defined over
UTF-16 units. Make its reader strict: each info's hash is its name's,
infos in name order, offsets increasing and contiguous, no bytes after
the last field, names unique. Make the reads use the table (a lookup
without the whole parse, as `Study.dbFind`), with bounds checks.
Consequences: no format change in 2026.4; the size stays; every other
language writes a codec; the fastest field reads. Cost: S to M.

**(b) Binson with a BergDB profile.** A stored object is a Binson object
under the rules of section 9; the kind of a value by section 7's (ii) or
(iii); `DbObject` stays as the API, a view over Binson bytes, which may
build a table in memory at its first lookup. Consequences: half the
bytes; any Binson reader reads BergDB's objects; the format's version is
the database's; reads in order. Cost: M.

**(c) Binson behind a BergDB header.** The stored value is a short
header, then a Binson object under the profile:

* **(c1) a header of kind and version**, for example two or three bytes
  (an object marker and a version), or `bergo` and a version 2 (6
  bytes). It answers question 3 in the value (section 7, (i)) and gives
  BergDB's format a version of its own. A `Payment` is 37 to 41 bytes
  against 71. Cost: M.
* **(c2) a header and a field table**: (c1) and DbObject's table (a hash
  and an offset per top-level field) before the Binson bytes: lookups as
  in (a) for top-level fields, a nested path in order. 6 bytes per
  field: a `Payment` is about 55. Cost: M, plus the table's rules (a
  hash over UTF-8 bytes) in every binding.

**(d) DbObject's format made closer to Binson's types**: a version 2 with
one integer type, no null, a hash over UTF-8 bytes, names non-empty, a
strict reader, maybe minimal-size integers and lengths. Keeps the table
and the marker; shrinks the values. BergDB's own spec and codecs in
every language, and Binson's types without Binson's libraries. Cost: M.

**(e) Another standard format**, for completeness, not studied in depth:
CBOR's deterministic encoding (RFC 8949, section 4.2.1) has mature
libraries in every language, but also null, undefined, tags and maps
with any keys, which a profile would have to refuse, and it orders map
keys by their encoded bytes (shorter names first), not Binson's or
DbObject's order. It has no field table either.


## 13. Recommendation: (c1)

Binson under a BergDB profile, behind a short BergDB header that holds
the kind of the value and a version of BergDB's object format; no
stored field table in this version; `DbObject` kept as the API over the
new bytes; made in 2026.4 with 020-04's no-null rules.

1. **The model is already Binson's.** Shape 1 chose a small closed list,
   as Binson's; question 1b leans to no null, as Binson; question 1's
   (A) decides by the value, so the int/long split is not used. What
   is left between the two is null, which question 1b's (d) removes,
   and the split. Two formats for one model would leave BergDB with
   a spec to write and codecs to port that Binson already has.
2. **Half the bytes** for small objects, such as the index definitions
   and the tests' objects measured (S).
3. **The header keeps BergDB's decisions BergDB's.** It answers question
   3 in the value, as Binson's one-byte marker cannot, and its version
   lets a later format add a field table ((c2)) or change the profile
   without touching Binson.
4. **The read cost is known, and small on typical objects.** Reads in
   order were faster than today's code on the four objects and slower
   behind an array (B, W); against a table they lose most on objects
   with large arrays or objects before the indexed field. Until such
   indexes matter, a table in memory, built at the first lookup, serves
   repeated lookups; (c2) is the step if they do.
5. **2026.4 is the time.** No backward compatibility is needed; 020-04
   opens the format anyway (its null encodings); the spec is to be
   written now (question 4). After 2026.4 the switch needs a migration.

When another option is better: **(a)** if no new reader should enter
the bug-free release (then (c1) after it, with a migration); **(d)** if
field lookups on large objects are a priority and BergDB should own its
format outright; **(b)** if question 3 is answered by keys or
directories (section 7, (iii)) and a version outside the value is
enough: then the header has nothing to hold.

For Frans to decide, in this order: whether objects go to Binson ((b),
(c1), (c2)) or stay ((a), (d)); then question 3 (the kind of a value),
which decides between (b) and (c1); then the profile's limits (depth,
fields, names), with the bindings that must meet them.


## 14. The measurements, how they were made

* **Machine**: F53, macOS 27, arm64, 10 cpus; OpenJDK 27 (2026-09-15),
  `-Xms1g -Xmx1g`, the default collector. Before each run: no
  `QUIET-BLOCK` marker, no gate, level script, night or performance run,
  and no other JVM but VS Code's (`ps`); load average 1.6 to 1.7 (the
  editor and the Claude sessions).
* **Code**: BergDB's `java/build/bergdb.jar` at `a7fe143` (021-08's
  reader; no Java change since); binson-java master `45346ad` (release
  3.5) and binson-java-light v1.2.0, compiled with javac 27.
* **Programs** (`/Users/f/fl/bench/006-14/020-binson/java/`): `Study`
  (the samples, the reflection to and from Binson, the direct writer,
  the BinsonLight reader into a class, the header lookup), `Probes`,
  `Cross`, `Bench`, `Worst`. Every sample's bytes were checked: the
  direct writer's equal binson-java's, and each round trip gives the same
  bytes (S, "checks").
* **Bench**: per operation, 0.8 s of warm-up, then 11 rounds of about
  100 ms; the median ns per operation, and in the outputs the rounds'
  minimum and maximum. Two JVM runs (`out-bench-1.txt`, `-2.txt`, 20:54
  and 20:56): the medians agree within 4 %, but for `Foobar`'s DbObject
  decode (857 and 713) and `Payment`'s BinsonLight read (86 and 80);
  within a run, the rounds' range is within 5 % of the median for most
  rows, with single slow rounds up to 2.4 times (`Index` one field today, 681 to
  1,682). `Worst` ran once after them, the same way.
* **Not measured**: a BergDB build or get end to end (the stream reads
  and the transaction around the decode); multi-threaded reads; large
  strings; another JVM or machine.
* **Other languages**: node 26.9.0 (binson-js copied out of its clone and
  imported), Python 3.14 with `-I` and a two-line `six`, cc for
  binson-c-light (`-std=c99 -O1`), Swift 6.4 (Swift's `String` only, not
  binson-swift).

Verified by running: the sizes (S), every BJ, DB, JS, PY, C and SW line,
and the timings (B, W). From the code without running: binson-c,
binson-go (both), binson-swift's use of `String` keys, binson-php,
binson-erlang, the Rust crate, and BergDB's read paths (section 6.1).
From documentation: the spec, the licences, the release dates.


## 15. Sources

Read on 2026-11-07; copies in `/Users/f/fl/bench/006-14/020-binson/sources/`
and the clones in `impl/`.

* [Binson]: https://binson.org/, BINSON-SPEC-1.1 (sections 1 to 6, the
  example, "Changes from BINSON-SPEC-1"), page version 2026-10-07;
  https://binson.org/BINSON-SPEC-1.1.pdf; https://binson.org/BINSON-SPEC-1.pdf
  (May 2014).
* [Binson Schema]: https://binson.org/binson-schema.html, page version
  2026-10-06.
* binson-java: https://github.com/franslundberg/binson-java (master
  `45346ad`, release 3.5); binson-java-light:
  https://github.com/franslundberg/binson-java-light (v1.2.0).
* binson-c: https://github.com/assaabloy-ppi/binson-c; binson-c-light:
  https://github.com/assaabloy-ppi/binson-c-light (`20a6243`).
* binson-js: https://github.com/assaabloy-ppi/binson-js (`c5d55c1`).
* binson-go: https://github.com/assaabloy-ppi/binson-go,
  https://github.com/hakanols/binson-go.
* binson-swift: https://github.com/assaabloy-ppi/binson-swift;
  binson-python: https://github.com/assaabloy-ppi/binson-python
  (`79c50ac`); binson-php: https://github.com/assaabloy-ppi/binson-php;
  binson-erlang: https://github.com/assaabloy-ppi/binson-erlang.
* Rust: https://crates.io/crates/binson (0.1.0),
  https://github.com/dvdplm/binson-rust.
* [I-JSON]: RFC 7493, "The I-JSON Message Format", March 2015,
  https://www.rfc-editor.org/rfc/rfc7493.
* [CBOR]: RFC 8949, section 4.2.1, "Core Deterministic Encoding
  Requirements", https://www.rfc-editor.org/rfc/rfc8949.
* BergDB: `java/src/bergdb/pubimp/` at `a7fe143`; 020-01, 020-02, 020-03,
  020-04; 021-04, 021-06, 021-07, 021-08; 012-01; 006-08.


## 16. Log

2026-11-07. Written by agent b05 of coord-1107 (006-14) at Frans's
request (20:42); the programs and outputs in
`/Users/f/fl/bench/006-14/020-binson/`. No code changed.
