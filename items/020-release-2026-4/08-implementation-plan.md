# 020-08 Objects in format 2: the implementation plan

Created 2026-11-08 by Frans Lundberg. Status: open; step 1 done (section
8.1); the other steps decided under Frans's delegation of 2026-11-08,
22:17 (section 2). How format 2 of stored objects (020-07; 020-02, section
4), the no-null rules of 020-04 as Frans chose them, (c), the conversion
rules of 020-09 and the API's removals (020-02, section 5.1b) get into the
Java code: the design, the changes file by file and method by method, the
tests, the measurements, the steps and commits with their gates, the
documentation, the C clone, an estimate and the risks.

Frans, 2026-11-08, 17:12, asked for this plan with 020-07, at XHigh, with
no code. The decisions it implements are 020-02, section 4 (4.1 to 4.12);
the spec is 020-07, whose rules (R1 to R15) and condition codes (section
7.2) are cited here. The API's decisions since (020-02, sections 2 and
5.1b) and 020-09's rules are in sections 3, 4.9 and 4.10 and steps 7 and
8, brought in on 2026-11-08 (section 12).

Code read at `ea5654a` (`java/` unchanged since `a7fe143`); line numbers
are that commit's, in `java/src/bergdb/pubimp/` unless named. Steps 7 and
8 were read at `b9d87e7`, whose `java/` differs only by step 1 and
`PayDemo`.


## 1. In short

* **One codec**, a new package-private class `ObjectFormat`: the full
  check with 020-07's conditions, the lookup by binary search, the readers
  of each value and the writer's encodings. `DbObject`, `DbArray` and the
  value classes keep their roles and API, rewritten onto it. Done in step
  1 (section 8.1).
* **One binding**, a new package-private class `DataObjects`: 020-09's
  check of Data Object classes and its conversion both ways, layer 2 of
  020-02, section 5.1b; `DbObject` and the value classes keep layer 1.
* **Steps, each a commit** gated by `java/before-commit.sh` ("BEFORE
  COMMIT OK"), in the order 1, 2, 7, 8, 3, 4, 6: (1) the codec, the
  vectors and the format's harness, done; (2) the switch: every object
  written and read in format 2, one integer, depth 16, a null field left
  out; (7) the removals: `put(Object)`, the key field,
  `MissingKeyFieldException` and `PubUtil`; (8) the binding, by 020-09;
  (3) old objects and index definitions refused with a clear message; (4)
  the measurements; (6) the Javadoc, the release notes and 020-04's index
  tests. Step 5, (d)'s constructor check, is dropped: Frans chose (c). The
  numbers stay as first written, so that 020-02, 020-07 and 020-10 keep
  pointing right. `createFast()` goes in 020-10's step I2, which owns the
  index API and its testers.
* **Tests**: 52 existing test methods and helpers change in step 2; 20 in
  step 7, and `PubUtil`'s 9 go; 7 in step 8, with 51 test classes made
  Data Objects and 46 calls of `toJavaObject` changed; 1 in step 6. New:
  the conformance vectors run by Java and the format's harness (step 1,
  done), about 10 tests of format 2 (steps 2 and 3), and 020-09's 176
  cases and three properties (step 8).
* **Size**: about 6 days of an agent's work after step 1, 7 in all, plus
  the gates and an hour of a quiet machine (section 11).
* **Before it starts**: nothing is left; Frans's delegation of 22:17
  settles section 2's points.


## 2. What Frans says before it starts

The points as written for Frans on 2026-11-08, and their state:

1. **"ok-and-implement"** of this plan, and so of 020-04's rules as far
   as they are in it: given for step 1 (19:43: "3. Yes, OK."); for the
   other steps, under the delegation below.
2. **020-07, Q1**: decided as recommended (19:43: "2. As recommended."):
   a scalar is not a level.
3. **020-04, Q1, the put of a null field**: decided, (c) (21:47): a null
   field is left out, no put is refused for it, and a null array element
   is refused (020-09, section 4.3). Step 5 is dropped.
4. **The API choices of section 3**: decided since, by Frans or under the
   delegation (section 3).
5. **020-07, Q6**: step 1 took the default, the vectors in
   `java/src/bergdb/pubimp/doc-files/`.
6. **The refusal of a start** that meets index definitions in format 1:
   as recommended, a `VersioningStreamException` with section 5's message
   (`IndexManager`), under the delegation.

Since 19:43 (020-02, sections 2 and 5.1b): question 1 decided, best
effort, (C) (21:47), with the rules in 020-09 (21:59); Data Objects with
public fields only (20:44); the layers (20:23, 20:44); no key field and
no `put(Object)` (19:21); `createFast()` goes (19:43).

Frans, 22:17, delegated the rest: "make the decisions needed to get the
2026.4 release ready". Under it the coordinator decided, for this plan:

* the steps go ahead in the order 1, 2, 7, 8, 3, 4, 6, each under section
  8's gate: the delegation stands for Frans's ok of every step but the
  first. Step 2 comes first, as 020-10's step I1 waits for it (020-10,
  section 10);
* section 3's choices, as written there, and 020-09's (its section 6);
* `createFast()` and its 36 calls in the testers go with 020-10's step
  I2, which owns `IndexBuilder`, `IndexBuilderImp` and the index testers
  (020-10, section 10.1), not in a step of this plan; section 6.1 has
  what I2 meets in `PubTesterIndexJobs`;
* `java/src-dev/frans/WebsiteCode.java`'s `Person`, a package-private
  class with a package-private field, becomes a public class with a public
  field and public constructors in step 8, as `PayDemo`'s changes, which
  Frans allowed: else its put is refused (020-09, section 3);
* the files that this plan and 020-10 both change are changed by one step
  at a time, in the coordinator's order (section 8).


## 3. The API decisions, and where each joins

020-02, section 5, within a shape that stays: plain Java objects put and
got by key (Frans, 2026-11-08, 17:26: "So the main design is good as is.
Let's keep it."). Each point where format 2 and the binding meet the API,
with its decision and the step that makes it; "delegated" marks the
coordinator's under Frans's delegation of 22:17:

| Point (020-02)                    | Decision                                        | Step       |
|-----------------------------------|-------------------------------------------------|------------|
| 4.1's put rule (020-04, Q1)       | (c): a null field left out (Frans)              | 2          |
| question 1, the conversion        | (C), best effort, by 020-09 (Frans)             | 8          |
| question 2, the closed list       | public fields only (Frans); 020-09, section 3   | 8          |
| question 2: final fields, records | refused (delegated; 020-09, V2, V3)             | 8          |
| question 5, `key`, `put(Object)`  | both go (Frans)                                 | 7          |
| `createFast()` (5.1b)             | goes, `start().join()` (Frans)                  | 020-10, I2 |
| `getType` of an integer (5.1)     | `'l'` for every integer (delegated)             | 2          |
| `has(name, 'i')`, `getInt` (5.1)  | an integer within `int`'s range (delegated)     | 2          |
| `DbObject` copies its bytes (4.3) | yes, and checks them fully (delegated)          | 2          |
| `byte[]` at an object key (4.5)   | the header and the full check (delegated)       | 2, 3       |
| `DbObject` public (5.1)           | into `bergdb.pub` (020-10, step B3)             | 020-10, B3 |
| a key form for lookups (5.1)      | names as UTF-8 bytes, `FieldRef` (delegated)    | 2          |
| the conversion by hand (5.1b)     | `toDbObject`, `toJavaObject(Class)` (delegated) | 8          |

* **Copy and full check** (4.3): `new DbObject(bytes)` copies the bytes and
  makes the full check, as today's constructor copies and parses them
  (line 155); its lookups then run on a copy in the cache, 020-02,
  section 4.3's warm rows. A view over the database's own array, with a
  check of the header only and lookups that check what they touch (020-07,
  section 7.4, Q2), is for a later release (delegated), measured first
  (section 7).
* **The integer's type**: today `i` and `l`; format 2 has one integer
  (4.7). `getType` answers `l` (`DbObject.LONG`) for every integer, and
  `INT` stays for `has` and `getInt`, true and the value for an integer
  within `int`'s range, by the value as question 1's (A) would. Three
  tests change their asserts (section 6.1).
* **The `byte[]` guess**: `Entries.isProbablyDbObject` takes the header
  byte `82` in place of `bergo`; for a get as `Object.class` and a primary
  scan the value is an object only if it also passes the full check, so a
  `byte[]` that happens to start with `82` (1 in 256 of random bytes, where
  `bergo` was 1 in 2^40) still reads as a `byte[]`. A build skips it, as
  today a `byte[]` starting with `bergo` (`IndexBuilderImp`, line 489).
* **The conversion by hand** (delegated): `DbObject.toDbObject(Object)`
  and `DbObject.toJavaObject(Class)` stay the ways to convert between a
  Data Object and a `DbObject` (Frans, 21:47: "Users who want full control
  need to get object of type DbObject and from that convert to Data
  Objects explicitely"); from step 8 they call `DataObjects`, and
  `toJavaObject` has no `ClassToObject` argument.


## 4. The design

### 4.1. One codec: `ObjectFormat`

A new package-private final class in `pubimp` (`@author Frans Lundberg`, or
none; its Javadoc cites bergdb 020-07), static methods on `byte[]`, no
allocation but for results:

* constants: `HEADER` (`0x82`), the type bytes, `MAX_FIELDS` (32,767),
  `MAX_LEVELS` (16), `MAX_NAME` (255), `NAN` (`0x7ff8000000000000L`);
* `checkStored(byte[] b)`: the full check of 020-07, section 7.1, one
  pass, recursion at most 16 deep, every limit before reading or
  allocating, refusing with `BadFormatException` whose message starts
  with the condition's code (`past-end: ...`, 020-07, section 7.3) and
  names format 1 for `bergo` (`format-1`);
* `isStoredObject(byte[] b)`: the same, true or false, for the guess of
  section 3;
* `find(byte[] b, int start, int end, byte[] name)`: the binary search of
  020-07, section 8.2, on the object at `start` filling `[start, end)`;
  the value's start, or −1; local checks as `F2.find` (020-07, section
  7.4), cheap where the bytes are checked;
* `valueEnd(b, p, limit)`, `typeAt(b, p)` (as `DbObject`'s type chars),
  `integerAt`, `doubleBitsAt`, `stringAt` (a `String` from checked UTF-8),
  `bytesAt`, `isObjectAt`, and the object's head (w, n, the table, the
  fields' start);
* the writer's encodings: `integer(long)`, `doubleBits(long)` (NaN made the
  one pattern), `stringHeader(int)`, `bytesHeader(int)`, `boolean`, the
  array's `42` and `43`, and `frame(...)`: an object's type byte, count and
  ends in front of its fields;
* a strict UTF-8 check (020-07, R11; as `F2.utf8Fault`), as Java's decoder
  is not used to check (it replaces).

It is written from 020-07, not from `F2.java`; `F2.java` and `check.py`
(`/Users/f/fl/bench/006-15/020-07/`) are references. Java 17
(`build.sh`: `--release 17`).

### 4.2. `DbObject`: a checked copy, read by lookups

* **State**: `bytes` (a stored value, header included, for an object made
  from bytes or by the Builder; the parent's array for a nested object),
  `start` and `end` (the object's extent in `bytes`), its head (`w`, `n`,
  the table, the fields' start), and `key`. Gone: `hashes`, `fieldCount`,
  `isNull`, `MAGIC`, the field infos.
* **From bytes**: `new DbObject(byte[] b, String key)` copies `b` (as
  today), runs `ObjectFormat.checkStored` and reads the head. Nested
  objects (`getObject`, an array's element) are views on the same array,
  not copies: the array is the object's own, and was checked.
* **Lookups**: each getter encodes the name to UTF-8 strictly (a name with
  a lone surrogate is absent: `StringUtil.toBytes` would give `?` and
  could find a field named so), then `ObjectFormat.find`; nested paths
  jump through the tables without making `DbObject`s.
* **`getBytes()`**: the stored value; for an object made from bytes or
  by the Builder, the array itself (today's contract, line 323); for a
  nested view, a new array of the header and its bytes.
* **`write` and `getByteSize`**, used when it is nested in another object
  or an array: its object bytes without the header (today with a 4-byte
  size before them).

### 4.3. The value classes

`DbValue` keeps `getType()`, `getByteSize()`, `write(byte[], int)` and
`toJavaObject`; each class writes Binson's encoding (020-07, section 4.1).
`DbValue.parse(char, byte[], int)` becomes `DbValue.read(byte[] b, int p,
int end)`, by the type byte. `DbInt` goes: `DbLong` is the integer, with
`DbInt`'s conversions. `DbArray` holds its bytes from `42` to `43` and
counts its elements when read. Every container knows its height in
levels, for the Builder's depth check (section 4.7).

### 4.4. The writer: the Builder, bottom up

020-05, section 12b.6's way 1, which is today's shape: each nested object
and array is built first and copied into its parent once per level, as
today. `Builder.build()` sorts the fields by their names' unsigned bytes
(as today), computes each field's size (`1 + L + value.getByteSize()`) and
the ends in 64 bits, refuses what 020-07, section 6.1, refuses, picks the
smallest w, and writes the header, the type byte, the count, the ends and
the fields into one array of the exact size. It does not run the full
check on its own output (today's `buildInner` constructs a `DbObject`,
line 1147, which parses it): the harness checks every built value
(section 6.3). A back-to-front writer (way 2) is an optimization for
later, if step 4 shows the writer matters.

### 4.5. Integers

`byte`, `short`, `char`, `int` and `long` fields and wrappers become one
integer (`DbValue.handleSpecialType`), in the fewest bytes. `checkFits`
(lines 219 to 254) tests the integer type `l` where it tested `i` or
`l`; its ranges stay. A long index reads the integer
(`FieldIndexFunction`). The API's part: section 3. Step 8 removes
`checkFits`: a value that does not fit is clamped (020-09, section 5.4).

### 4.6. Null: what the switch needs

Format 2 has no encoding for null, so step 2 changes the put (020-04,
section 4's step B, by (c), which Frans chose, 21:47):

* `toDbObject(null)` throws `IllegalArgumentException` (today
  `Builder.buildNull()`, line 459);
* a null array element is refused, naming `[i]` (020-04, section 2.1,
  rule 3);
* a null field is left out ((c), decided); (d)'s constructor check is
  not made (step 5 dropped);
* `isNull`, `buildNull`, `defaultValue`, `toNullDbValue` and the null
  branches of the value classes go (020-04, section 4, step A's lines,
  which format 2 replaces: 020-04, section 11).

The path exception of 020-04, section 2.1 (one base class for a lone
surrogate, a null element, too deep and a name too long, each level adding
its step on the way out) is made here. Step 8 carries these rules into
`DataObjects` (020-09, section 4.3), with two more refusals of the kind (a
class that is not a Data Object, a value of another class).

### 4.7. Depth and the path

020-07, R14: the top object is level 1, every object and array one more.
`toDbObject`'s `Path` (lines 492 to 556) counts arrays too (today objects
only, `MAX_DEPTH` 1,000) and refuses level 17 with the path, as
`inner.list[2]`; `createDbArray` (lines 505 to 521) enters and leaves it.
The Builder refuses a value whose height would put a container above
level 16, from each container's height, with no walk. `MAX_DEPTH`,
`MAX_READ_OBJECTS` and `MAX_READ_LEVELS` (lines 474 to 490) become one
`ObjectFormat.MAX_LEVELS`, 16. Step 8 moves `toDbObject`'s path into
`DataObjects` (020-09, section 4.7).

### 4.8. Old objects, and the kind of a value

Format 1 (`bergo`, version 1) is refused wherever an object is read, with
a message naming the format (020-07, `format-1`; 020-02, section 4.11):
by `ObjectFormat.checkStored`, so at a get (`ObjectCreationException`), in
index maintenance (`DataFormatException`), and at a start that reads an
index definition. Where today a value is first classified by its bytes
(`Entries.isProbablyDbObject`), a format-1 value at an object key must not
fall through as a `byte[]` or be skipped: a new `Entries.isFormat1Object`
lets it reach the reader, which refuses it, in a get as `Object.class`, a
primary scan and a build (section 5).

### 4.9. The binding: `DataObjects` (step 8)

A new package-private final class in `pubimp` (`@author Frans Lundberg`,
or none; its Javadoc cites bergdb 020-09), layer 2 of 020-02, section
5.1b, written from 020-09:

* **The class check** (020-09, section 3): a `ClassValue` holding a
  class's result: valid, with its stored fields in the order of their
  names' UTF-8 bytes (each a `Field`, its name's bytes, its type) and its
  public no-argument `Constructor`; or not valid, with the reason and the
  field. Field types are checked recursively, each class once.
* **The put** (020-09, section 4): `toDbObject(Object)` by the declared
  types, through `DbObject.Builder` and `DbArray.Builder`, with step 2's
  path, depth and null rules (sections 4.6 and 4.7) and 005-23's cycle
  check; every refusal an `IllegalArgumentException` of the path
  exception.
* **The get** (020-09, section 5): `toJavaObject(DbObject, Class)`: the
  check first, then a new object by `Constructor.newInstance()`, each
  stored field found by its name's bytes (step 2's lookup; a walk of both
  in name order if step 4 shows it worth it), 020-09's conversions, one
  static method per field type, and `Field.set`; the top level of 020-09,
  section 5.9.
* **Exceptions**: 020-09, sections 3.3 and 5.2.
* About 700 lines with Javadoc; its tests are a new `DataObjectsTester`
  (section 6.2: T11, H1). Both join `Pack`'s list.

No `setAccessible` and no `BlankConstructorFactory`: a Data Object's
constructor and fields are public (020-09, V1 to V6). The code it replaces:
the bodies of `DbObject.toDbObject` and `toJavaObject`,
`getEligibleFields`, `DbValue`'s conversions, `DbArray.toJavaObject`,
`DbByteArray.toJavaObject` and `BlankConstructorFactory` (section 5).

### 4.10. The removals (step 7)

020-02, section 5.1b: `put(Object)`, the key field and
`MissingKeyFieldException` go. A field named `key` becomes an ordinary
field, and a `DbObject` read at a key no longer answers `key` with the
database key: it is the stored object exactly. The tests that call
`put(Object)` take `put(key, object)`, and those that read the database
key from the field read what was stored (section 6.1). `createFast()`
goes too (19:43), in 020-10's step I2 (section 2).


## 5. The changes, file by file

### `pubimp/ObjectFormat.java` (new)

Section 4.1. About 400 lines with Javadoc. Its tests are in a new
`ObjectFormatTester` (section 6.2); both join `Pack`'s list.

### `pubimp/DataObjects.java` (new, step 8)

Section 4.9; 020-09.

### `pubimp/DbObject.java`

* **Class Javadoc** (lines 18 to 74): the types `n`, `l` (the integer),
  `d`, `s`, `b`, `a`, `o`, and `z` for absent; one integer; no null; the
  format is 020-07's, format 2; 021-04's paragraph on strings stays
  (step 6 writes it; step 2 makes the type list true).
* **Constants and state** (lines 86 to 113): `HEADER_SIZE`, `MAGIC`,
  `INT` as a stored type, `FIELD_INFO_SIZE`, `KEY_FIELD_HASH`, `hashes`,
  `fieldCount`, `isNull` go; `HEADER` (the byte `0x82`) public, for
  `Entries` and the tests; the state of section 4.2.
* **Constructors** (lines 122 to 209): section 4.2; `checkNesting`,
  `checkLevels`, `scanObject`, `scanValue`, `checkSignature` (lines 218 to
  320) go, `ObjectFormat.checkStored` does it all; a private constructor
  for nested views.
* **`getBytes`** (323 to 328), **`getByteSize`**, **`write`** (856 to 866):
  section 4.2. **`isNull`** (330 to 332) goes.
* **`getFieldCount`** (337 to 341): n, plus 1 for `key` until step 7.
* **`has`, `internalGet`, `internalNestedGet`, `internalSimpleGet`** (346
  to 419): one private `find(String name)` and `findPath(String[])`, each
  giving the value's offset or −1; `has(name, type)` compares
  `ObjectFormat.typeAt`, with section 3's rule for `INT`.
* **`getType`, `getDbValue`, the getters** (701 to 819): through `find`;
  absent or another type gives 0, false or null, as today; `getObject`
  a view; `getArray` a `DbArray` read from the value's bytes.
* **`readFieldInfo`, `readFieldOffset`, `hash`** (826 to 854) go.
* **`toDbObject`, `toDbObjectOnPath`** (457 to 605): null refused at the
  top (section 4.6); a null field per section 4.6; the depth count of
  section 4.7; the wrapping of a top-level array (`array`) and primitive
  (`p`) stays (020-07, section 12). Step 8 moves them into `DataObjects`.
* **`toJavaObject`** (615 to 696): the `isNull` branches go; each eligible
  field by `find`, as today by `getDbValue` (lines 672 to 693); step 8
  moves it into `DataObjects` (section 4.9).
* **`parse`** (868 to 881): goes into `DbValue.read`.
* **`DbField`** (883 to 997): holds the name's UTF-8 bytes and the value;
  refuses a name of 0 or more than 255 bytes (today more than 32,767, line
  911) with `IllegalArgumentException`; `write` writes `L`, the name, the
  value; `parse` goes.
* **`Builder`** (1011 to 1156): `buildNull` goes; `addInt` adds an
  integer; `addField`'s 32,767 limit stays (line 1029);
  `buildInner(boolean)` becomes `build()` of section 4.4. `main` (1158 to
  1162) goes. The 2013 notes at the end stay.
* **Step 7**: what step 2 kept of the field `key` goes: the state `key`,
  the constructor `DbObject(byte[], String)`, `KEY_FIELD` and the `key`
  branches of the lookups, `getType`, `getDbValue` and `getString` (today
  lines 102 to 112, 138 to 145, 389 to 398, 705 to 707, 731 to 733 and
  793 to 795), and the comment of lines 76 to 78.
* **Step 8**: `getEligibleFields`, `toDbObject`'s path and `toJavaObject`
  move into `DataObjects`; `toDbObject(Object)` and `toJavaObject(Class)`
  stay as calls of it (section 3), `toJavaObject` without its
  `ClassToObject`.

### `pubimp/DbValue.java`

* Class Javadoc (11 to 21): seven types. Constructor (73 to 89): no `i`.
* `checkFits` (219 to 254): `type == 'l'` for integers (section 4.5).
* `parse` (339 to 371) becomes `read(byte[] b, int p, int end)` by the
  type byte, making `DbObject` views and `DbArray`s.
* `defaultValue` (376 to 415) and `toNullDbValue` (417 to 431) go.
* `toDbValue(Class, Object)` (440 to 462) becomes `toDbValue(Object)`
  (020-04, section 4: `dstType` was used for null only); null refused.
* `handleSpecialType` (464 to 503): `B`, `C`, `S`, `I`, `J` give a
  `DbLong`.
* `createDbArray` (505 to 521): a null element refused with `[i]`; the
  depth count; the path exception's base class caught.
* Step 8: the conversions go, as `DataObjects` holds 020-09's:
  `toJavaObject`, `checkFits`, `isPrimitiveOrWrapper`,
  `getPrimitiveTypeChar`, `getSpecialTypeChar` and their tables,
  `toDbValue`, `handleSpecialType`, `createDbArray`, and the cross-type
  conversions (`toByte`, `toChar`, `toShort`, `toFloat`, and `toBoolean`,
  `toInt`, `toLong`, `toDouble` where a class does not hold that type).
  Each value class keeps its own value's getter.

### `pubimp/DbArray.java`

* Javadoc (12 to 34): seven types; never null; no element null.
* `toString`, `isNull`, the null branches of `toJavaObject`, `toIntArray`,
  `toLongArray`, `toDoubleArray` (62 to 156): the null parts go.
* `parse` (162 to 182) becomes a read of `[p, end)`, counting the
  elements with `ObjectFormat.valueEnd`; the `ElementIterator` (184 to
  271) reads each element with `DbValue.read`; `z`, `Z` and their checks
  go (format 2's reader refuses at the check).
* `Builder` (277 to 310): `buildNull` goes; `add` writes the element's
  encoding; `build` adds `43`; the height of section 4.7.
* Step 8: `toJavaObject` goes, to `DataObjects`; `toIntArray`,
  `toLongArray` and `toDoubleArray` take 020-09's element rules
  (delegated: one set of conversions; 7 asserts of `DbObjectTester` use
  them, with values that fit).

### The value classes' files

`DbBoolean`, `DbLong`, `DbDouble`, `DbString` and `DbByteArray`;
`DbInt.java` goes.

* `DbBoolean`: `44` or `45`; its `parse` (43 to 54) becomes a read.
* `DbLong`, the integer: `ObjectFormat.integer`; `getByteSize` 2, 3, 5 or
  9; `DbInt`'s `toInt`, `toFloat`, `toDouble` and its tests move here.
* `DbDouble`: `46` and `Double.doubleToLongBits` (one NaN); today
  `Bytes.doubleToBytesLE`, which keeps the raw bits (`common/Bytes.java`,
  line 124, `doubleToRawLongBits`): DB7 of 020-05.
* `DbString`: keeps its UTF-8 bytes, computed once (today `utf8Size`, then
  `toBytes` again in `write`, lines 73 to 90); the length in the fewest
  bytes; null refused in the constructor (020-04); `LoneSurrogateException`
  becomes the path exception of section 4.6.
* `DbByteArray`: the length in the fewest bytes; null refused.

### `pubimp/Entries.java`

* `isProbablyDbObject` (79 to 87): an object key and the first byte
  `0x82`, at least 3 bytes; `startsWithMagic` (89 to 98) goes.
* New `isFormat1Object(key, value)`: an object key and `bergo` with the
  version 1.
* New, for section 3's guess: `isStoredObject(key, value)`, the header
  and `ObjectFormat.isStoredObject`.

### `pubimp/KvToObjectImp.java`

* `entryToMixedTypeObject` (87 to 99): an object if `isStoredObject` or
  `isFormat1Object` (the reader then refuses it, naming format 1); else as
  today.
* `entryToDbObject` (101 to 114): unchanged; the message now names the
  condition.
* Step 7: `entryToDbObject` makes `new DbObject(value)`, without the key,
  which stays in the message.
* Step 8: a class other than `String`, `byte[]`, `DbObject` and `Object`
  is checked first, also for a key without a value (020-09, section 3.3),
  then converted by `DataObjects`; the get's exceptions are 020-09,
  section 5.2's; `newObject`, `factories` and `implements ClassToObject`
  go.

### `pubimp/RwEnvironmentImp.java`

* Step 7: `put(Object)` (lines 277 to 300) goes, with its import of
  `MissingKeyFieldException`. Step 8: `ObjectInfo` (line 653) converts by
  `DataObjects`.
* No change of code in step 2. `indexEntries` (361 to 432) reads the
  previous value with `new DbObject` (line 401): a format-1 value gives a
  `DataFormatException` naming format 1 (step 3's test). `ObjectInfo`
  (626 to 657) puts a `DbObject` as it is: checked or built, so no check
  at the put; if the API makes `DbObject` a view later, a put of one made
  from bytes must make the full check (020-07, section 7.4).

### `pubimp/FieldIndexFunction.java` and `FieldRef.java`

* `createIndexEntry` (45 to 99): `TYPE_LONG` reads the integer, one
  branch in place of `l` then `i` (lines 61 to 67); each level makes one
  lookup and reads the value at its offset, in place of `has` and a
  getter, two parses today.
* `FieldRef`: the parts' UTF-8 bytes, made once (020-02, section 4.3: "an
  index function holds its names as bytes").

### The index code: `IndexManager`, `IndexBuilderImp`, `UseIndexBuilderImp`

* `IndexManager.storeIndex` (368 to 385): unchanged; the definitions are
  written in format 2 (vector `index-definition`, 96 bytes).
* `IndexManager.initFromDatabase` (131 to 153): a definition in format 1
  stops the start with section 2, item 6's exception: "The database holds
  index definitions in the object format of BergDB 2026.3 and before
  (format 1), which 2026.4 does not read (bergdb 020-02, section 4.11).
  Make the database again from its data." `DatabaseImp.createAndStart`
  (81 to 114) then closes it, as for any start that throws. Whether the
  start has written anything by then (`Db.start()` runs first, line 93)
  is checked and said in the message.
* `IndexManager.getActiveIndex` (501 to 544): the message of the
  `InternalDataException` (line 537) names the format for format 1.
* `IndexBuilderImp.TheStopCondition.handleKvt` (679 to 700): a value is
  taken if `isProbablyDbObject` or `isFormat1Object`; the build loop (484
  to 500) refuses a format-1 value with a `DataFormatException` naming
  the key, which ends the build as failed, the database going on (the
  rule of lines 353 to 356); other values that fail the check are skipped,
  as today.
* `UseIndexBuilderImp`'s filter (738 to 752): a scan of objects keeps a
  format-1 value, which its conversion (line 669) then refuses.

### `pubimp/Data.java`, `IndexEntryBuilder.java`

No change. `Data.Index`'s `int version = 1` is the integer 1; it is a
Data Object (020-09, K18's shape), and it goes in 020-10's step I2.
`IndexEntryBuilder`'s null check (lines 131 to 141) stays, with 020-04's
comment in step 6.

### `pubimp/PubUtil.java` (deleted, step 7)

All of it is the field `key`: `KEY_FIELD`, `readExistingKeyField`,
`setKeyFieldIfItExists` (used by its tests only), `getField`, and 9
tests. Step 2 keeps it.

### `pubimp/Pack.java`

`ObjectFormat` and `ObjectFormatTester` in (step 1); `DbInt` out (step 2);
`PubUtil` out (step 7); `BlankConstructorFactory` out, `DataObjects` and
`DataObjectsTester` in (step 8).

### The removals' other files (step 7)

* `pub/WBuilder.java` (lines 40 to 56), `pub/RwEnvironment.java` (52 to
  67), `pubimp/WBuilderImp.java` (32 to 37): `put(Object)` and its
  Javadoc go.
* `pub/MissingKeyFieldException.java`: deleted.
* `pub/DataFormatException.java`: its Javadoc names
  `WBuilder.put(Object)`; it names `put(String, Object)` instead, and from
  step 8 no longer "a stored value that does not fit the Java type or
  field it is read into" (020-09, section 5.2).
* `pub/package.html` (line 8) and `src/overview-pub.html` (line 12):
  "put(Object)" leaves the paragraph on what is experimental.
* `java/src-dev`, which `build.sh` compiles: `bergdb/demo/GetStarted4.java`
  (`env.put(acc0)`, `env.put(acc1)`), `bergdb/test/DeleteIndexTester.java`
  and `CreateIndexTester.java` (`put(new Employee(...))`, 5 calls) take
  `put(key, object)`; `frans/PayDemo.java`'s `Account.key` (line 205)
  goes (Frans allowed it, 020-02, section 5.1b). The last three are
  020-10's I2's files too (its `createFast()` in `PayDemo`, line 78): one
  step at a time.

### The binding's other files (step 8)

* `pubimp/BlankConstructorFactory.java`, `ObjectFactory.java` and
  `ClassToObject.java`: deleted; `DatabaseImp`'s `classToObject` and
  `getClassToObject()` (lines 46, 72, 146 and 147) go (`DatabaseImp` is
  020-10's I2's file too).
* `pubimp/DbByteArray.java`, `DbDouble.java`, `DbString.java`: their
  `toJavaObject` and cross-type conversions go (`DbValue`'s bullet).
* The test classes, 51 in 7 files, become Data Objects: public static,
  with public fields and a public no-argument constructor (section 6.1).
* `java/src-dev`: `bergdb/test/night/CcDbNightTest.java`'s `Stats.cards`
  (a night test) becomes public; `bergdb/demo/GetStarted1.java`'s
  `Person`, `GetStarted4.java`'s `Account` and `frans/WebsiteCode.java`'s
  `Person` become public classes with public fields and constructors
  (section 2).

### Not touched

The Core, the stream's format, `docs/`, the Lean model (objects are values
to it), the C clone (section 10), StreamDigest (its workloads put no
object and make no index).


## 6. Tests

### 6.1. Existing tests

Counted at `ea5654a` for step 2; "changes" means its asserts, its calls or
its bytes change, the test staying.

`DbObjectTester`, 80 `@Nano` methods:

* **48 unchanged**: `test0` to `test2`, `testAssumption1` and 2,
  `testLong`, `testSetObjectFields1` to 3 and 5, `tSetObjectFields4`,
  `testBadFormatException`, `testByteArray1` and 2, `testBoolean1` and 2,
  `testObjectMultiLevel`, `testIntArray1` and 2, `testLongArray1`, 2 and
  4, `testDoubleArray1`, 2 and 4, `testPrimitiveArrays0` and 1,
  `testStrings1`, `testCircularRefs`, `testHierarchy`,
  `testPrivateConstructor`, `testTypeSwitch`, `testArray0`, 2 and 3,
  `testPrimitive0` to 4, `testNestedField1` to 5, `testCycleRefused`,
  `testDeepRefused` (its message keeps "deeper than"),
  `testLoneSurrogates`.
* **8 change for format 2**: `testInt1`, `testInt2` (`getType` is `l`),
  `testObject1` (`has("myInt", 'l')` is true); `testNarrowingOutOfRange`,
  `testNarrowingInRange`, `testBuilderRefusesNull` (`DbInt` gone);
  `testDeepAtLimit` (16 levels, now a unit test: it took 2 s at 1,000);
  `testBuilderRefusesTooDeep` (16).
* **6 of 021-07 and 021-08 on format-1 bytes**: `testReaderCutBytes` and
  `testReaderNestingDepth` are written again for format 2 (every prefix
  refused; 16, 17 and 100,000 levels by hand);
  `testReaderNestedObjectSizeMinusOne`, `testReaderBadLengths`,
  `testReaderBadTypeByte` and `testReaderNullMarkAfterAnElement` go:
  their faults have no form in format 2, and the vectors' `past-end`,
  `length` and `type` records take their place. The helpers
  `firstField`, `firstValue`, `nestedArrays` and `nestedObjects` (lines
  1321 to 1523) are written again.
* **18 for null** (020-04, section 5.1's list, all in step 2 as format 2
  has no null): `testString1`, `testByteArray3`, `testObject2`,
  `testSetObjectFields6`, `testIntArray3`, `testLongArray3`,
  `testDoubleArray3`, `testPrimitiveArrays2`, `testStrings0`,
  `testStrings2`, `test5DIntArray`, `test4DCustomerArray`,
  `testStrings2D`, `testNullField0`, `testNullField1`, `testStringArray0`,
  `testArray1`, `testArray4`. Under (c), as Frans chose, each changes
  once: the 5 that put a null over an initial value (`testString1`,
  `testObject2`, `testSetObjectFields6`, `testNullField0`,
  `testNullField1`) read that value back.

The value classes' `@Nano` tests: `DbArray` (5): `test1` and
`testIterator1` change (no `isNull`; an int in an array is 4 bytes, not
6), `testNull` goes; `DbString` (3): all change (null; the read's
signature); `DbInt` (4) go, 2 moving to `DbLong`; `DbLong`, `DbDouble`,
`DbByteArray` (1 each) and `DbBoolean` (2): the serialize tests change
with the read's signature; `DbObject.testLongFieldName`: kept, with the
boundary at 255 and 256 bytes.

Elsewhere: `PubTester.testMalformedObjectRefused` (format-1 offsets, lines
162 to 168) is written again for format 2, and
`PubTester.nullStringArrayField2` is refused (020-04);
`PubPromiseTester`, line 412, and `PubTesterIndex`, lines 243 to 248, take
`DbObject.HEADER` for `MAGIC`. Unchanged: `Entries`' 7, `KvToObjectImp`'s
5, `DbValue`'s 1, `FieldIndexFunction.Tester`'s 2; `PubTester`'s other
object tests (the `getInt` reads of lines 2130 to 2196 keep working by
section 3's rule); `PubTesterIndex`, lines 801 to 805, `getInt` and
`getLong` of `amount` (the same rule); `PubTesterPrimary`, lines 401 to
406. In step 6: `PubTesterIndexJobs.testBuildOverAnObjectItCannotIndex`
(020-04, section 5.1).

In all: **52 test methods and helpers** change or go in step 2 (32 of
`DbObjectTester`, 15 in the value classes, 2 in `PubTester`, 1 in
`PubPromiseTester`, 1 in `PubTesterIndex`, 1 in `DbObject`), and 1 in
step 6. 020-04 counted about 23 for version 1.

**Step 7, the removals**, counted at `b9d87e7`:

* `PubTester`, 19: the 13 that call `put(Object)` take `put(key,
  object)` (`minimalCodeToStoreObject`, `testSync1` to `testSync6`,
  `testKeyField1`, `testKeyField3`, `testKeyFieldInSuperClass0`,
  `testKeyFieldWithDbObject1`, `testAnonymous1`, `testDbObject1`); the 6
  that read the database key from the field `key` assert what was stored
  (`testKeyField0`, `testKeyField0Private`, `testKeyField2`,
  `testKeyFieldInSuperClass1`, `testKeyFieldWithIterator`,
  `testKeyFieldWithDbObject0`).
* `PubTesterOutput.testEnvironmentAfterRun`: its `env.put(new
  Item(...))` takes a key.
* `PubUtil`'s 9 tests go with it.

**Step 8, the binding**, counted at `b9d87e7`:

* The test classes become Data Objects, public static with public fields
  and a public no-argument constructor, their tests' code unchanged: 51
  classes, `DbObjectTester` 24, `PubTester` 10, `PubTesterIndex` 8,
  `PubTesterNestedFields` 5, `PubTesterComposite` 2, `PubTesterPrimary`
  1, `KvToObjectImp` 1. `PubTester.WithObject` gets `public int o`, so
  that `testMalformedObjectRefused` and `testDeepObjectRefused` still test
  the reader, not the class check. The index testers are 020-10's I2's
  and I3's files too: one step at a time.
* The 46 calls of `toJavaObject(c, new KvToObjectImp())` lose the second
  argument: `DbObjectTester` 41, `PubTesterPrimary` 2, `KvToObjectImp` 2,
  `PubTesterIndex` 1.
* 7 change: `DbObjectTester.testPrivateConstructor` becomes a refusal
  (020-09, K2); `testNarrowingOutOfRange` and `testNarrowingInRange`
  expect 020-09's clamps in place of 005-22's `DataFormatException`;
  `PubTester.testAnonymous0` and `testKeyFieldWithDbObject0` put a public
  class (an anonymous one is refused, 020-09, K16);
  `PubTester.testKeyField0Private` becomes a refusal (its class's fields
  are private); and step 2's T4 expects the clamp.

**`createFast()`, for 020-10's step I2**, counted at `b9d87e7`: 36 calls
in 35 methods of 5 testers, `PubTesterIndex` 21, `PubTesterIndexJobs` 5
tests and its helpers `createIfFree` and `deleteAndReplace`,
`PubTesterNestedFields` 4, `PubTester` 2, `PubTesterComposite` 1. In the
33 tests no object is in the directory when the index is made, so
`start().join()` does the same. The 2 helpers make the index over a
directory that holds `/items/old`, and `deleteAndReplace` runs inside a
build's hook in 2 tests: with `start()`, the 6 tests that use them
(`testBuildDeletedBeforeItsStep`, `testBuildDeletedInItsStep`,
`testBuildDeletedBeforeActivation`, `testExpiryInDeletionIsNotAFailure`,
`testDeleteTwice`, `testDeleteAgainAsTheFirstEnds`) join the job outside
any hook and expect the old object in the new index too, `[100, 200]` in
place of `[100]`, their purpose (015-22, 019-38) checked to hold.

So this plan's steps change test methods 80 times (52, 20, 7 and 1),
remove 9, and change 51 test classes.

Night and level tests: `PayTest` and `CcDbNightTest` (night) and
`BryanRepro` (`level2.sh`) put objects through the Pub API on new
databases: they pass unchanged through steps 2 and 7; in step 8
`CcDbNightTest`'s `Stats.cards` becomes public (else its put is refused),
and `PayTest`'s and `BryanRepro`'s classes are Data Objects already. A
database kept between runs with objects or an index would be refused
(4.11); none is known, and the night run after step 3 shows it.

### 6.2. New tests

In `ObjectFormatTester` unless named; each fails on the code before its
step, or is new code's test.

* **T1. The vectors** (step 1): every record of `object-vectors.txt`
  (020-07, section 13.2): `checkStored` accepts each valid value and
  refuses each invalid one with a message starting with one of its codes;
  the test's reference decoder gives each value, compared with its VN;
  `find` gives each lookup's result; the recipes give their length and
  SHA-256; the Binson column both ways, through a converter in the test.
* **T2. The vectors through `DbObject`** (step 2): each valid value read
  by `new DbObject`, its getters and paths giving the VN's values, and
  built again by the Builder from its VN to the same bytes; each invalid
  one refused with `BadFormatException`; a get of each at a key gives
  `ObjectCreationException` in `w()` and `rw()`, and the database goes on.
* **T3. Writer refusals** (step 2): a name of 0 and of 256 bytes (Builder
  and `toDbObject`); 32,768 fields (Builder); level 17 by objects and by
  `int[]` dimensions, each naming its path (`Object[]` is refused as a
  type from step 8, 020-09, V9); a null element at every depth naming
  `[i]`; `toDbObject(null)`.
* **T4. One integer** (step 2): `byte`, `short`, `char`, `int`, `long` and
  their wrappers holding 5 give the same bytes (`10 05`); the MIN and MAX
  of each; a stored `long` read into an `int` field when it fits, and
  `DataFormatException` when it does not (005-22; from step 8, clamped,
  020-09); `getType` and `has` by section 3.
* **T5. Doubles** (step 2): a NaN with a payload is stored as
  `0x7ff8000000000000` and read back as NaN; −0.0 reads back as −0.0
  (`doubleToRawLongBits`); a `float` NaN.
* **T6. Sizes** (step 2): `Payment` 36 bytes, `Person` 16, the index
  definition of one level 96 (020-05, section 12b.3, plus the header).
* **T7. Lookup names** (step 2): `getString("a\uD800")` on an object with
  a field `a?` is absent.
* **T8. Old objects refused** (step 3, in `PubTester`): the format-1
  vectors' bytes at a key: a get as a class, as `DbObject` and as `Object`
  gives `ObjectCreationException` naming format 1, in `rw()` too, and the
  database goes on; a put or a delete of the key in an indexed directory
  gives `DataFormatException`; a build over a directory holding it ends
  failed with the message; a primary scan of objects refuses it; a start
  of a database with a format-1 index definition, written through the
  Core API, is refused with section 2's exception and closes.
* **T9. The kind of a value** (step 3): a `String` value is never an
  object; a `byte[]` starting with `82` that fails the check is a
  `byte[]` to a get as `Object` and is skipped by a build (section 3).
* **T10. A long index over one integer** (step 2, in `PubTesterIndex`):
  `int` and `long` fields of one value give one sort key; the entries of
  `Payment`s equal those of 2026.3 (`IndexEntryBuilder` is unchanged).
* 020-04's new tests (its section 5.2): N1, N3, N4 and N5 in step 2, by
  (c); N2, N6, N7 and N8, (d)'s, are not made; N13 is H1's R1; N10 is T8;
  N11 and N12 in step 6. N9's Builder part and N14 were done by 021-07.
* **T11. 020-09's cases** (step 8, in a new `DataObjectsTester`): G1 to
  G122, K1 to K18 and W1 to W36 (020-09, sections 8.2 to 8.4), each as
  written there.
* **H1. 020-09's properties** (step 8): R1, the round trip; R2, the get
  against a reference of 020-09, section 5, written in the test; R3,
  principle 4 (020-09, section 8.5). Seeded, in the unit group under 2
  seconds, more seeds in a night test (`bergdb.dev.Night`). It is 020-01,
  section 15's H1, objects into their classes and back.

### 6.3. H0, the harness of the format

As 018's harnesses (018-01, section 6; 018-04's 6.7: against a simple
reference in the test), it checks the codec against a second codec
written in the test from 020-07 (as `check.py`: about 250 lines, a writer
bottom up, a decoder, a lookup by a linear scan):

* **H0a. Random values** (step 1 for the codec, step 2 through the
  Builder and `toDbObject`'s value classes): seeded random trees of every
  type and edge (the integer and length boundaries, every double class,
  strings from U+0000 to U+10FFFF, names of 1 to 255 bytes, depth 1 to 16,
  widths 1, 2 and 4); for each, the reference's bytes equal the Builder's;
  `checkStored` accepts them; the decode equals the tree; every lookup
  and nested path equals the tree's, absent names included.
* **H0b. Mutations**, as 020-05's F7 and 020-07, section 5.1: every byte
  of ten samples changed ten ways and every cut; the full check and the
  reference agree on each; each accepted mutant is written again to the
  same bytes; each lookup on each mutant gives the full read's value or
  `BadFormatException`, never another exception.

In `before-commit.sh`'s unit group with a fixed seed and sizes that take
under 2 seconds (`before-commit.sh` must stay fast: memory of 2026-11-05);
a run with more seeds as a night test (`bergdb.dev.Night`), a few
minutes. H1 (section 6.2, step 8) is 020-01, section 15's H1, generated
objects into their classes and back; H0a is its storage half.


## 7. Measurements

020-02, section 6, points 2 and 3, and a check that nothing else moved.
In step 4, after step 3's commit, on F53, quiet (nothing else running;
another session's markers and `ps` checked first), `JAVA_HOME` set.

* **The reference**: `java/stress/performance.sh build pre-f2` at the
  commit before step 2 (a preserved build of format 1), and the
  candidate at step 3.
* **`java/stress/ObjectBench.java`** (new, a small benchmark beside
  `Perf.java`, compiled by `build.sh` with the stress tests): it uses only
  what both builds have (`DbObject.toDbObject`, `new DbObject(byte[])`,
  `getLong` and `getString` by name, `getBytes`, the Pub API's puts, gets
  and `indexBuilder`), runs each build in its own JVM in ABBA order, and
  prints medians of 5 runs:
  * **M1, the writer**: `toDbObject` of 020-05's samples (`Person`,
    `Payment`, `Foobar`, `Dialog`, `Data.Index`, `Customer`, `Order`,
    `Blob`), ns an object; format 1 took 670 to 2,523 ns (020-05, section
    6.2);
  * **M2, the read of bytes**: `new DbObject(bytes)`, the copy and the
    full check, against format 1's copy and full parse (340 to 720 ns for
    one field read, 020-02, section 4.3) and binson-java's strict parse
    (322 to 886 ns);
  * **M3, lookups**: `getLong` and `getString` of one field, and a nested
    path (`Dialog`'s `personB.id`), hot, on a `DbObject` made once;
  * **M4, a get end to end**: 200,000 `Payment`s in memory, `get` into
    `Payment.class` and as `DbObject` with one getter, uniform keys, one
    thread, ns a get (2026.2's Core get: about 0.8 µs, 020-02, section
    4.3);
  * **M5, an index update**: puts of `Payment` into a directory with a
    string index on `from`, one a transaction, puts a second;
  * **M6, a build**: a string index over 1,000,000 `Payment`s, seconds to
    done;
  * **M7, bytes**: the stream's length after 1,000,000 `Payment`s, bytes
    a value (36 against 71 expected).
* **`java/stress/performance.sh quick`** on the candidate against the
  reference (`ab pre-f2 current`): the Core's numbers are expected not to
  move; a move is looked into.
* **Where**: a subitem of 020 with the next number, with the commit, the
  machine, the JVM and the numbers; a line in 020's readme.

What would change the plan: M2 and M5 show whether the full check at
every read costs enough to want 020-07, section 7.4's lookups on unchecked
bytes (Q2) and a view without a copy (the API's, 4.3); M1, whether the
writer needs way 2 (section 4.4).


## 8. The steps and commits

Each step is one commit, its tests written first and seen to fail on the
code before it (or new code's own), gated by `java/before-commit.sh`
printing "BEFORE COMMIT OK". The coordinator commits (memory of the
concurrent sessions: work in a scratch clone, gate the combined tree).
The order is 1, 2, 7, 8, 3, 4, 6 (section 2); the numbers stay as first
written.

* **Step 1. The codec, the vectors and the harness.** `ObjectFormat`,
  `ObjectFormatTester` (T1, H0a and H0b on the codec), the vectors file
  moved to `java/src/bergdb/pubimp/doc-files/object-vectors.txt` and
  020-07, section 13.5, pointing there; `Pack`. Nothing uses the codec
  yet: no behaviour changes. About 1 day. Done (section 8.1).
* **Step 2. The switch.** `DbObject`, `DbValue`, `DbArray`, the value
  classes, `DbInt` gone, `Entries`, `KvToObjectImp`, `FieldIndexFunction`,
  `FieldRef`, `Pack`; section 3's rules and section 4.6's null rules; the
  52 tests of section 6.1; T2 to T7 and T10, H0a and H0b through
  `DbObject`; 020-04's N1, N3, N4, N5. Then `java/stress/level2.sh` once,
  for `BryanRepro` (objects through restarts and reclaim; it needs Lean
  for its conformance steps, which this change does not touch). About 2
  days. 020-10's step I1 waits for it.
* **Step 7. The removals** (section 4.10): `put(Object)`, the key field,
  `MissingKeyFieldException`, `PubUtil`, their Javadoc and `src-dev`'s
  calls (section 5); the 20 tests of section 6.1, `PubUtil`'s 9 gone. No
  stored byte changes. About half a day.
* **Step 8. The binding** (section 4.9; 020-09): `DataObjects` and
  `DataObjectsTester` (T11, H1); the conversions of `DbObject`, `DbValue`,
  `DbArray` and the value classes moved or removed; `KvToObjectImp`,
  `BlankConstructorFactory`, `ClassToObject`, `ObjectFactory`,
  `DatabaseImp`, `RwEnvironmentImp`; the 51 test classes, the 46 calls
  and the 7 tests of section 6.1; `src-dev`'s classes. About 2 days.
* **Step 3. Old data refused.** `Entries.isFormat1Object`,
  `KvToObjectImp`, `IndexBuilderImp`, `UseIndexBuilderImp`, `IndexManager`
  (the start and `getActiveIndex`); T8, T9. About half a day. Before
  020-10's step I2, which keeps its refusal (020-10, section 10.2).
* **Step 4. The measurements** of section 7, and `ObjectBench.java`
  committed. About half a day, and an hour of the quiet machine.
* **Step 5. (d)'s constructor check**: dropped. Frans chose (c)
  (2026-11-08, 21:47; 020-02, section 5.1b): no put is refused for a null
  field, and no constructor runs at a put.
* **Step 6. The documentation and 020-04's index part** (its step D):
  section 9's Javadoc and `releases/next.md`; 019-42's comments; N11, N12
  and `testBuildOverAnObjectItCannotIndex`. Gate: `before-commit.sh` and
  `java/javadoc-pub.sh` ("JAVADOC PUB OK"). About 0.75 days.

With 020-10 (section 10.1 there), one step at a time on a shared file:
`RwEnvironmentImp` and `WBuilderImp` (steps 7 and 8; 020-10's I1 and I2),
`IndexManager`, `IndexBuilderImp` and `UseIndexBuilderImp` (step 3; I1 to
I3), `DatabaseImp` (step 8; I2), the index testers and `PubTester` (steps
2, 7 and 8; I2 and I3), `CreateIndexTester`, `DeleteIndexTester` and
`PayDemo` (step 7; I2). 020-10's I2 removes `Data.java` and with it
`IndexManager`'s two conversions (lines 382 and 540); if step 8 comes
first, it changes them to `toJavaObject(Class)`.

Then the day's coordinator runs `java/night.sh` (the night tests with
objects, the level scripts) when the machine has room, and a line goes to
`news.md` if it runs unattended.

No other level script is needed: the Core, the stream and the Lean model
are not touched. The principles (018-01, section 2) are checked at each
commit; P7 (a failed database stops) is kept: no reader path throws an
`Error` or an unchecked JDK exception (T2, H0b), and a refusal inside
`rw()` is the action's exception.

### 8.1. Step 1, done (2026-11-08)

Made in a clone at `ade9be7`, tests first (each failed on a stub of the
API before the code); not committed (the coordinator commits):

* `java/src/bergdb/pubimp/ObjectFormat.java`, new, 831 lines: section
  4.1's codec, written from 020-07. The full check (`checkStored`,
  `isStoredObject`; `checkValue` for one value), every message starting
  with its code; `find`, the binary search, checking what it touches
  (020-07, section 7.4); the readers of checked bytes (`typeAt` gives `l`
  for every integer); the writer's encodings (`writeInteger`,
  `writeDouble` with the one NaN, `writeStringHead`, `frame` and more)
  and checks (`utf8`, `nameBytes`, `checkName`, `checkCount`,
  `checkLevel`, `checkStoredSize`), each an `IllegalArgumentException`
  whose message starts with its code.
* `ObjectFormatTester.java`, new: T1 on every record (32 valid with 343
  lookups, 84 invalid, 2 generated, 8 Binson inputs, the counts
  asserted), the Binson column by a converter in the test; `Ref`, a
  second codec in the test (another order of checks, Java's strict UTF-8
  decoder); H0a, 400 random values of seed 1; H0b, the ten vectors of
  `SAMPLES`, 13,585 mutants; the writer's refusals and encodings; 100,000
  nested arrays refused at level 17. 7 tests in the unit group, 0.6 s.
  The night test `testHarnessNight`: 30 seeds a day, each 5,000 values
  and 40 mutated samples, 103 s; `main(SEED)` repeats a seed.
* The vectors moved unchanged to
  `java/src/bergdb/pubimp/doc-files/object-vectors.txt` (section 2, item
  5's default), which `build.sh` copies into the jar; 020-07, section
  13.5, points there. `Pack`: `ObjectFormat` and `ObjectFormatTester` in.

Nothing uses the codec: no behaviour changes. 28 faults planted one at a
time in a copy of the codec (each check off, each boundary moved by one,
signed compares) were each caught. Gate: BEFORE COMMIT OK (119 s).

Where the plan and the spec differ (the spec wins):

* Section 6.3, H0b: "each lookup on each mutant gives the full read's
  value or `BadFormatException`". On a refused mutant 020-07, section
  7.4, lets a lookup answer absent or another field's value; H0b checks
  the full read's value on an accepted mutant, and on a refused one no
  exception but `BadFormatException`.
* Section 4.1, `find`: "local checks as `F2.find`". F2's also refuses an
  object that does not fill its extent; `find` checks only what 020-07,
  section 7.4, lists, so a caller may give the parent's extent.

For step 2: the writer's checks name no place, the Builder and
`toDbObject` add it (020-07, section 6.1; section 4.6's path exception);
`find` gives the value's start, and `valueEnd` its end on checked bytes;
T2 can reuse the tester's `readVectors`, `Vn`, `Ref` and `codecWrite`
(the Builder's shape). 020's readme still links the vectors' old place.


### 8.2. Step 2, done (2026-11-08)

Made in the clone `clone-objects` on `8876480`, tests first (each new test
failed on the code before); committed by the objects' agent of the night
(006-15, section 3b):

* `DbObject`: a checked copy of a stored value of format 2 (020-07), read
  by `ObjectFormat.find`; nested objects are views on the parent's bytes;
  `getBytes()` of a nested one is a new array, the header first. The
  Builder writes bottom up, sorts by the names' unsigned bytes, refuses a
  name of more than 255 bytes, 32,768 fields and a height above 16. `HEADER`
  (`0x82`) is public; `MAGIC`, `isNull()`, `buildNull()`, `hash()`,
  `parse()`, `MAX_DEPTH` and the format-1 reader are gone. `getType` gives
  `l` for every integer; `has(name, INT)` and `getInt` take an integer
  within `int`'s range (section 3).
* `DbValue.read` by the type byte; the value classes write Binson's
  encodings (one NaN, `-0.0` kept); `DbInt` is gone, its tests in `DbLong`;
  `DbString` and `DbByteArray` refuse null; `DbArray` is `42 ... 43`, its
  Builder refuses a height above 15.
* `toDbObject`: null refused at the top; a null field left out; a null
  array element refused, naming `[i]`; the path counts arrays, level 17
  refused (`'inner[0][0]...'`); `DbValue.PathException`, one class for a
  lone surrogate, a null element and a long name, each level adding its
  step.
* `Entries.isProbablyDbObject`: an object key and the header, 3 bytes or
  more; a get as `Object` reads such a value with the full check and gives
  the `byte[]` if it fails (section 3).
* Tests: new `DbObjectFormatTester`, 13 tests, 0.5 s (T2 to T7, H0a
  through the Builder, H0b through `DbObject`); in `DbObjectTester`
  020-04's N1, N3, N4, and the 32 of section 6.1 changed or gone; N5 and
  T10 in `PubTester`; the value classes' tests; `Entries.testIsObject5`.

Decided in the step, under Frans's delegation (22:17):

* The tests through `DbObject` are a new class, `DbObjectFormatTester`,
  not `ObjectFormatTester` (the codec's tests); T10 is in `PubTester`, not
  in `PubTesterIndex`, which 020-10's I1 and I2 own.
* `FieldIndexFunction` and `FieldRef` are not changed: `has(path, 'l')` is
  true for every integer, so a long index reads every integer by its first
  branch; the `i` branch is dead code, and I2 removes both classes.
* No `Entries.isStoredObject`: `KvToObjectImp` makes the `DbObject` and
  gives the `byte[]` on `BadFormatException`, one full check, not two.
* `PubTesterIndexJobs.testBuildOverAnObjectItCannotIndex` (section 6.1:
  step 6) changed in this step, as it failed: a null `String` is absent, so
  the build ends done with two entries (020-04, N11); its body only.
* The Builder's 32,768th field is an `IllegalArgumentException` (was
  `IllegalStateException`), as 020-07, section 6.1, says of refusals; a
  null name to a getter is an `IllegalArgumentException`.
* `PubTesterIndex.testNonObjects2`'s value that is not an object starts
  with `DbObject.HEADER` (`82 61 62`); `PubPromiseTester`'s random bytes
  avoid `HEADER` in place of `MAGIC`.

Gate: BEFORE COMMIT OK (117 s); `level2.sh` afterwards (section 8).


### 8.3. Step 7, done (2026-11-09)

Made in `clone-objects` on step 2's commit, tests first (each changed test
failed on step 2's code):

* `put(Object)` gone from `WBuilder`, `RwEnvironment`, `WBuilderImp` and
  `RwEnvironmentImp`; `MissingKeyFieldException` and `PubUtil` (with its 9
  tests) deleted; `DbObject`'s key (its state, `DbObject(byte[], String)`
  and the `key` branches of the getters) gone: a `DbObject` read at a key
  is the stored object exactly, and a field named `key` an ordinary field.
  `KvToObjectImp`, `RwEnvironmentImp.indexEntries` and `IndexBuilderImp`'s
  build make `new DbObject(bytes)`.
* Javadoc: `DataFormatException` names `put(String, Object)`;
  `pub/package.html` and `overview-pub.html` drop "put(Object)" from the
  paragraph on what is experimental (020-10's B2 rewrites both later).
* `src-dev`: `GetStarted4`, `CreateIndexTester` and `DeleteIndexTester`
  put at a key; `PayDemo`'s `Account.key` gone (Frans allowed it).
* Tests: `PubTester`'s 19 of section 6.1 (13 put at a key, 6 assert the
  stored field) and a new `testKeyIsAnOrdinaryField` (020-09, G113 and
  W31; that the removed API is gone, by reflection);
  `PubTesterOutput.testEnvironmentAfterRun` puts at a key.

Decided in the step, under Frans's delegation (22:17):

* The night test `PayTest` (`src-dev/bergdb/test/night/`) read each
  account's database key from its field `key` after a primary scan, which
  section 6.1 missed: it now stores the key in the field at its put, one
  line, so the night run checks the scan's order as before.

Gate: BEFORE COMMIT OK.


## 9. The documentation

* **`DbObject`'s class Javadoc**: section 5's list; the format by its ID
  (bergdb 020-07, format 2); 020-04, section 6.2's paragraph on absence
  without its sentence on the version-1 encodings.
* **`DbArray`, `DbValue`**: seven types, no null.
* **`pub/package.html`**: 020-04, section 6.1's "Null and absent fields"
  (by Frans's answer to its Q1), and a short section "Objects": the seven
  types and how Java's map to them (one integer: `byte` to `long`; one
  double: `float`, `double`), names of 1 to 255 bytes, depth 16, NaN, no
  null; objects of 2026.3 and before are not read (4.11); the format is
  BergDB's own, its spec 020-07. `src/overview-pub.html`: a sentence.
* **Step 7's Javadoc**: `put(Object)` and `MissingKeyFieldException` leave
  the Javadoc (section 5).
* **Data Objects and the conversion** (step 6): `pub/package.html`'s
  "Objects" says what a Data Object is (020-09, section 3, in a
  paragraph), what a put refuses, and how a get converts: by name, the
  nearest value, the type's zero, never a throw for the data, and
  `ObjectCreationException` for a class that is not a Data Object; the
  rules in full by their ID (bergdb 020-09). `Connection.get`'s and
  `ReadInterface.get`'s Javadoc: the class is a Data Object (not "in
  general a public no-argument constructor"), and `@throws
  ObjectCreationException`. `DbObject.toDbObject` and `toJavaObject`: the
  same, by reference.
* **`Connection`, `WBuilder`, `RwEnvironment`**: 020-04, section 6.2's
  sentences, and in `put`'s `@throws IllegalArgumentException`: a name
  longer than 255 bytes, a nesting deeper than 16 levels.
* **`releases/next.md`**, under "Pub API":
  * **Objects are stored in format 2** (bergdb 020-02, section 4; 020-07;
    Frans, 2026-11-08): about half the bytes (`Payment` 36 against 71); a
    field found without reading the others; a strict reader that refuses
    any other byte string, naming the rule. Objects and index definitions
    of 2026.3 and before are refused: a get throws
    `ObjectCreationException`, index maintenance `DataFormatException`, a
    build fails, and a database with an index does not start: such
    databases are made again. StreamDigest's workloads put no object: no
    digest changes.
  * **One integer type**; `getType` answers `l` (section 3).
  * **Depth 16** levels of objects and arrays (was 1,000 objects); **names
    of at most 255 bytes** (was 32,767); **one NaN**, a NaN's payload not
    kept.
  * **No null** (020-04, section 6.3's first two bullets, by Frans's Q1).
  * `DbObject.isNull()`, `DbArray.isNull()`, the `buildNull()` methods,
    `DbObject.MAGIC` and `DbInt` are gone.
  * **Data Objects** (020-09): a class put or got is public, with a public
    no-argument constructor and public fields, its other instance fields
    transient; `put(Object)` and `MissingKeyFieldException` are gone
    (`put(key, object)`); a field named `key` is an ordinary field. (020-10
    writes `createFast()`'s line.)
  * **A get converts best effort** (020-09): the nearest value or the
    type's zero, no `DataFormatException` for a value that does not fit;
    `ObjectCreationException` for a class that is not a Data Object.
  * 021-07's and 021-08's bullets (the old reader's refusals and depth)
    are folded into the first bullet: the reader they hardened is gone.
* **`docs/levels.md`, `README.md`**: "DbObject and the user indexes are
  experimental in 2026.3" stays until the release says otherwise; no
  change here.


## 10. The C clone, the Core and Lean

* **The C clone** (item 012) has no object code: it is a port of the
  Core of release 2026.2, kept stable (012's readme), and treats every
  value, objects and index definitions included, as bytes (020-05,
  sections 8.3 and 12b.8). It needs nothing: a database that Java 2026.4
  writes, with objects and indexes, opens in C at the Core's level as
  before, and 012-05's cross harness puts no object.
* **A C codec of 020-07** (about 300 lines, in place, without malloc:
  020-05, section 12b.8) is for a C Pub layer or 006-08's small target,
  not for 2026.4. When one is made, it runs the same vectors file, a
  third implementation beside Java's and `check.py`.
* **The Core, the stream and the Lean model** are not touched: objects
  are values to them. The format is under 018-01's rule (4.12): 020-07,
  approved by Frans, is the approval this plan implements.


## 11. Estimate and risks

**Work**, an agent at high effort (xhigh for steps 2 and 8):

| Step                             | Code, lines          | Tests, lines | Days |
|----------------------------------|----------------------|--------------|------|
| 1. Codec, vectors, harness, done | +831                 | +600      | 1    |
| 2. The switch                    | +700 −900            | +500 −350 | 2    |
| 7. The removals                  | −350                 | +100 −200 | 0.5  |
| 8. The binding (020-09)          | +700 −600            | +1,200    | 2    |
| 3. Old data refused              | +80                  | +200      | 0.5  |
| 4. Measurements                  | +400 (`ObjectBench`) | -         | 0.5  |
| 5. (d)'s check                   | dropped              | -         | 0    |
| 6. Documentation, index part     | +40, Javadoc +250    | +100      | 0.75 |

About 7 days in all, 6 after step 1, plus the gates (2 minutes a commit,
`level2.sh` once, `javadoc-pub.sh` once) and an hour of a quiet F53 for
step 4. The steps are in the order of section 8; step 4 waits for a quiet
machine and may come after step 6.

**Risks**, each with what meets it:

1. **New code in the bug-free release** (020-05, section 11, risk 5): the
   reader and the writer are new. Met by the vectors, checked by two
   implementations; the reference codec in the test (H0a); the mutation
   harness (H0b: no exception but the refusal); the night run.
2. **Old databases**: every database with an object is unreadable, and
   one with an index does not start (4.11, decided). Met by the messages
   (T8) and the release notes; the night's and benchmarks' databases are
   made new each run (none with objects is kept, as far as known: step 3's
   night run shows it).
3. **The API choices taken under the delegation** (section 3) may be
   changed by Frans later: then `DbObject`'s getters, 3 tests and
   `releases/next.md` change. Each choice is in one place.
4. **The cost of the full check at every read**: index maintenance reads
   the previous value of each object put in an indexed directory, and a
   build every object. Today's reader parses everything (340 to 720 ns),
   so the full check is not expected to be slower; step 4 measures it
   (M2, M5, M6), and 020-07, Q2 and the API's copy decide the way out.
5. **Puts refused that 2026.3 took**: objects deeper than 16 levels
   (arrays counted), field names over 255 bytes, a null array element.
   Met by the messages, naming the path, and the release notes.
6. **The `byte[]` guess** (4.5): a random `byte[]` at an object key starts
   with `82` 1 time in 256. Met by the full check in the guess (section
   3): a get as `Object` still gives the `byte[]`; a build skips it, as
   before; only the API's rule (020-01, decision 6) removes the guess.
7. **The writer's sizes** (020-05, section 11, risk 2 of (f)): the ends
   before the fields. Met by computing in 64 bits, the harness, and the
   vectors at every width boundary.
8. **Java 17**: `build.sh` compiles with `--release 17`; the codec uses
   nothing newer.
9. **Public fields only** (step 8): every class put today with a field
   that is not public, or that is not public itself, is refused: 51 test
   classes, a night test's, three demos' (section 6.1). Met by the class
   check's message, which names the field, and the release notes.
10. **Best effort hides a changed class**: a get converts and never says
    so (Frans's choice for 2026.4, 020-02, section 2). Met by the
    documentation (section 9) and the `DbObject` get for full control.
11. **Two plans on shared files** (section 8): met by one step at a time
    on each shared file, in the coordinator's order.


## 12. Log

2026-11-08. Written for coord-1108 at Frans's request (17:12), after his
decisions of 15:51 to 17:09 (020-02, section 4), with 020-07; read-only
at `ea5654a`. No code changed. Waits for Frans's "ok-and-implement" and
the answers of section 2.

2026-11-08. Step 1 done in a clone at `ade9be7` (section 8.1):
`ObjectFormat`, `ObjectFormatTester` (T1, H0a, H0b, a night test), the
vectors moved into `java/`; BEFORE COMMIT OK (119 s). Two differences
from 020-07 noted, the spec followed.

2026-11-08. Brought up to date with Frans's API decisions of 19:10 to
21:59 (020-02, sections 2 and 5.1b) and with 020-09, what they left open
decided under his delegation of 22:17 (section 2), and fitted to 020-10's
steps, by coord-1108's agent: two new steps, 7 (the removals) and 8 (the
binding, 020-09); step 5 dropped; the order 1, 2, 7, 8, 3, 4, 6;
`createFast()` left to 020-10's step I2; sections 1 to 6, 8, 9 and 11;
the tests of steps 7 and 8 counted at `b9d87e7`; about 7 days in all.
Step 1's record (section 8.1) unchanged. No code changed.
