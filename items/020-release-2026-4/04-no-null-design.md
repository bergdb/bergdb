# 020-04 No stored null: the design and the change plan

Created 2026-11-07 by Frans Lundberg. Status: open. The design and the
change plan for 020-02's question 1b, option (d), "null is absence,
exactly": the rules, the format and its spec, the code sites at `7edcbe2`,
the tests, the Javadoc and the release notes, so that the implementation
can start at Frans's "ok-and-implement" without more study. No code is
changed before it. The study is 020-03; the options and the
recommendation are in 020-02, section 2b.

Frans, 2026-11-07, 14:31: "About null or not. Based on your
investigation, I lean towards: no null values. Make a note of this and
prepare the required changes. But don't code it yet. Might sleep on it or
study it one more time before I give it an ok-and-implement. Now it is ok
to design and document. Prepare for it."

Where the points that need Frans's decision are: section 8, Q1 to Q6,
each with a recommendation. Where (c) and (b) would differ: section 2.6.

Note (2026-11-08): this design is written for DbObject's format version
1. 020-05 recommends since 2026-11-08 a new format, option (f), and
Frans leans to it (020-02, section 4.2). What (f) changes here, and what
stays: section 11. Some of section 4's lines were done since by 021-07
and 021-08 (section 11).


## 1. In short

* **The put**: a null field, at any depth, is left out of the stored
  object. A null array element is refused, and so is a null field to
  which the class's no-argument constructor gives a non-null value (a
  get would read that value, not null). A null at the top is refused, as
  today. Each refusal is an `IllegalArgumentException` naming the place
  (`inner.names[3]`), before anything is written.
* **The get**: an absent field keeps the value the constructor gave it,
  for every type, primitives too. No null value is ever read.
* **Indexes**: one rule. An object has an entry for a combination of
  fields when each of them is present with a type its level accepts;
  else no entry, and nothing is refused. 019-42's refusal of a null
  `String` goes.
* **The format**: no null encodings. Every object written after the
  change is a valid version-1 object that 2026.3 reads too; a reader refuses
  the old null encodings with `BadFormatException`. The version byte
  stays 1 (Q4). No index definition holds a null, so a start reads the
  same bytes as before.
* **The size**: about 300 lines of code changed in 8 files, about 23
  existing tests changed and 14 new ones, and a Javadoc section; about
  one day of an agent's work, in three commits, the first of which is
  (c) and the second (d) (section 9).


## 2. The rules

The rules of (d), as recommended in 020-02, section 2b.4. "Eligible"
fields are those `DbObject.toDbObject` stores today: not static, final,
transient or synthetic, of the class and its superclasses (020-01,
section 4.2). Question 2 of 020-02 (the closed list of types) may narrow
them; these rules hold for whatever it keeps.

### 2.1. The put

1. **A null field of a reference type** (`String`, `byte[]`, an array, a
   wrapper such as `Integer`, a nested object, an `Object` field) is left
   out of the stored object: the object has no field of that name. It is
   so at any depth: in the outermost object, in a nested object, in an
   object that is an array's element.
2. **Unless the constructor gives it a value.** If the class's
   no-argument constructor gives the field a non-null value, the put is
   refused: a get would read the constructor's value, not null
   (section 2.2).
3. **A null array element** is refused, at any depth and in an array of
   any element type (`String[]`, `Integer[]`, `Customer[]`, a row of an
   `int[][]`): an array has no absent elements. So is an array not filled
   (`new String[3]`). The message names the element's index.
4. **A null at the top** is refused, as today: `put(key, null)` and
   `WBuilder.put(key, null)` with `IllegalArgumentException` ("object ==
   null not allowed", `RwEnvironmentImp.put`). `DbObject.toDbObject(null)`
   is refused too; today it returns a null object (`Builder.buildNull`).
5. **A null wrapper** (`Integer count = null`) is absent, like any null
   field; it is no longer a null `o`, an object (020-03, BG1). A
   primitive field is never null and is always stored.
6. **A `DbObject` put as it is** (`put(key, dbObject)`) holds no null:
   the Builder refuses one (section 2.4), and `new DbObject(bytes)`
   refuses the null encodings (section 3).

The messages (drafts):

* Null over an initial value: "The field 'inner.name' is null, but the
  no-argument constructor of com.example.Inner gives it a value: BergDB
  stores a null field as absent, and a get would read the constructor's
  value, not null. Set the field, or give it no initial value (the
  package bergdb.pub, "Null and absent fields")."
* A null element: "The array element at 'names[3]' is null: BergDB stores
  no null, and an array has no absent elements (the package bergdb.pub,
  "Null and absent fields")."

The path is built as 021-04 builds a lone surrogate's: the exception
carries the path, and each level adds its step on the way out (a field's
name in `DbObject.toDbObjectOnPath`, an element's index in
`DbValue.createDbArray`). `DbString.LoneSurrogateException` and its
`in(step)` become one package-private base class, a path exception, with
two kinds: a lone surrogate and a null.

### 2.2. The constructor check of (d)

* **What is checked**: a null eligible field of a reference type, in an
  object of class C, where C is the object's runtime class (the
  outermost object, a nested object or an array's element object). The
  check asks: does C's no-argument constructor give this field a
  non-null value?
* **How the initial values are found**: one instance of C, made by its
  declared no-argument constructor (any access, made accessible), as
  `BlankConstructorFactory` makes one for a get; the eligible reference
  fields that are not null in it are C's "fields with an initial value".
* **When**: lazily, the first time a put meets a null field in an object
  of C. A class whose objects never hold a null field never has its
  constructor run at a put.
* **Cached**: per class, for the JVM's life, in a `ClassValue` (bound
  weakly to the class, so an unloaded class drops it), not per database:
  the answer depends on the class only, and the put's conversion
  (`DbObject.toDbObject`, `RwEnvironmentImp.ObjectInfo`) has no database
  at hand. Two threads may compute it at once and run the constructor
  twice; harmless. A computation that fails is not cached.
* **The same `ClassValue` may hold C's eligible fields**, which
  `getEligibleFields` today finds by reflection, with `setAccessible`, for
  every object put and read. Caching them is optional and saves more
  than the check costs; it is a separate change if wanted.
* **A class without a no-argument constructor** (an inner class, a class
  with constructors that take arguments): not checked, and its null
  fields are left out. A get into such a class fails anyway
  (`ObjectCreationException`), so no read shows the difference. Whether
  a put of such a class is refused is question 2's (Q2).
* **A constructor that throws**: the put is refused, with
  `IllegalArgumentException` naming the field and the class, and the
  constructor's exception as its cause; only a put of an object of that
  class with a null field meets it. A `VirtualMachineError` (an
  `OutOfMemoryError`) passes as it is, as on every BergDB path (P7). An
  `ExceptionInInitializerError` cannot come: an object of C exists, so C
  is initialized. So no user class makes the put throw an `Error` of its
  own (020-01, N2). (`BlankConstructorFactory`, for gets, has 020-01's
  S2-F21 still; this change does not touch it.)
* **A constructor with side effects** runs once more per class and JVM,
  as it runs at every get today. The Javadoc says so: the no-argument
  constructor of a stored class should have no side effects, and should
  give a field a non-null value every time or never.
* **Where it runs**: inside `toDbObject`, so in the caller's thread for
  `put` and `w()`, before the transaction, and inside the action for
  `rw()`, where the refusal is the action's exception: the transaction is
  not committed, and the database does not fail.
* **The cost**: nothing for an object without a null field (each field
  is tested for null already). For each null field, a `ClassValue` get
  and a set look-up, some tens of nanoseconds. Once per class, one
  constructor call and a read of its eligible fields. Today's put calls
  `getEligibleFields` for every object, which costs more than all of it.
* **What it does not cover**: a field whose declared type differs from
  its value's class (`Animal a = new Dog()`) is read back into the
  declared type, which may have other fields; the check uses the class
  that was put. That is question 2's (polymorphic fields), not null's.

### 2.3. The get

* An absent field keeps the value the class's constructor gave it, for
  every type, primitives and wrappers included. Today too, for a missing
  field (`DbObject.toJavaObject`, line 543: a field is set only if the
  stored object has it).
* A null is never read: no null into a primitive (the null case of
  S2-F6), no null array element into an `int[]` (BG4's bare
  `IllegalArgumentException`), no typed null of the wrong type (a null
  `Integer` stored as an `o`).
* Not removed by this change, for question 1: a present value of another
  kind. A `String` read into an `int` or `Integer` field is 0, silently,
  for any string, not only a null one (BG3's cause: `DbString` has no
  `toLong()`, so `DbValue.toLong()` answers 0); an object read into an
  `int` field throws `Bug` (`DbObject.toJavaObject` returns null for the
  missing `p`, and `Field.set` refuses it).
* A 2026.3 object with a null: refused by the reader (section 3.2, Q3):
  `ObjectCreationException` at a get, `DataFormatException` where index
  maintenance reads it.
* The field `key` is set from the database key at a read, whatever was
  stored (`DbObject.getDbValue`, line 598), so a `key` field put as null
  reads back as the key. That is the field `key`'s rule (020-02,
  question 5), not null's; (d)'s "reads back equal" excepts it until
  question 5 decides.

### 2.4. DbObject's own API

* `DbObject.Builder`: `addString(name, null)`, `addObject(name, null)`,
  `addArray(name, null)` and `addDbValue(name, null)` throw
  `IllegalArgumentException` ("leave the field out"); so do
  `new DbString(null)` and `new DbByteArray(null)`.
  `DbArray.Builder.add(null)` refuses already. Today `addString` stores a
  null `s`, and the other three throw an `AssertionError` with `-ea`, or a
  `NullPointerException` without it (`DbField`, line 762). Q5.
* `DbObject.isNull()`, `DbArray.isNull()`, `DbObject.Builder.buildNull()`
  and `DbArray.Builder.buildNull()` go: no object or array is null.
* `getType(name)` answers the type of a present field, or `z` for an
  absent one, as today; `z` is not a type (section 3.3).
* `has(name, type)` is true when the field is present with that type.
* `getString`, `getByteArray`, `getArray` and `getObject` return the
  value of a present field, never null; null for an absent field (or one
  of another type), Java's way to say absent. `getInt`, `getLong` and
  `getDouble` return 0, `getBoolean` false; `has` or `getType` tells.
  As today (020-02, section 2b.5). Q6.
* `getFieldCount()` counts present fields (and the key, as today).

### 2.5. Indexes

One rule, in place of today's three (020-03, section 5.3, BG6):

> For each combination of one field per level, an object has one entry
> when each field of the combination is present with a type that its
> level accepts: `l` or `i` for `long`, `d` for `double`, `s` for a
> string type. A nested field (`inner.name`) is present when each part
> but the last is present as an `o` and the last is present. Otherwise
> the combination gives no entry, and the put is not refused.

* What changes: a null `String` in a `string` index gave a refused put
  (`IllegalArgumentException`, "A null String cannot be indexed") and a
  failed build (019-42); now no entry, as a missing field. A null
  `Integer` gave no entry because a null `o` is not an `l`; now because
  it is absent: the same entries. A null nested object: no entry, as
  before.
* No entry of a non-null object changes, so no index's bytes change.
* `UseIndexBuilder.eq(null)` stays refused: it is an argument, not data.
* 019-42's check in `IndexEntryBuilder.sortBytesFromString` stays as it
  is, unreachable from data: a null there is BergDB's bug, and an
  `IllegalArgumentException` fails a build, not the database.
* 020-01, section 6.5, question 1 ("which make none (a missing field; a
  null; NaN)") loses "a null"; NaN is a question of its own.

### 2.6. Where (c) and (b) differ

The format, the readers, the get, the Builder and the indexes are the
same in (b), (c) and (d); only the put of a null differs.

* **(c) Null is absence.** As (d), without the constructor check: a null
  over a non-null initial value is left out and reads back as the
  initial value, silently (Gson's way, 020-03, JL3). No constructor runs
  at a put. Section 2.2 and its tests go; the Javadoc documents the
  asymmetry. Step C of section 9 is not made.
* **(b) Null is refused.** Every null, a field's too, is refused with
  its path, whatever the constructor does. An unset `String` field fails
  the put: every reference field must be set. No constructor runs at a
  put. Tests that put an object with a null field expecting it to read
  back (`PubTester.nullStringField`, `nullStringArrayField1`,
  `testKeyField2` and its kin, which put a null `key`) become refusals,
  and so do the night test `PayTest` (`Account.key`) and most classes of
  `DbObjectTester`. Not recommended (020-02, section 2b.4, reason 2).


## 3. The format

For DbObject's format version 1. Under 020-05's option (f) this section
is replaced but for the spec text on absence (section 11).

### 3.1. What changes in the bytes

The object format (`DbObject.Builder.buildInner` defines it) has four
null encodings today, three written and one only read:

* a null `s` or `b`: the 32-bit length −1, no bytes (`DbString.write`,
  `DbByteArray.write`);
* a null `a`: the single byte `Z` in place of the elements and their
  ending `z` (`DbArray.Builder.buildNull`);
* a null `o`: a whole object whose 16-bit field count is −1,
  `626572676f01ffff` with its 32-bit size 8 before it when nested
  (`DbObject.Builder.buildNull`; BG5);
* read only: a nested object's 32-bit size −1, which `DbObject.parse`
  reads as Java's null (line 739). Java never writes it; a reader meets
  it only in bytes from elsewhere, and then fails with an
  `AssertionError` or a `NullPointerException` (section 10).

After the change no writer writes any of them, and a reader refuses each
with `BadFormatException`. Nothing else changes: the bytes of an object
without nulls are the same, field for field. An object that had null
fields is shorter, by each such field's type byte, name and value, and
by 6 bytes of field info each.

### 3.2. Old databases, the version byte, and 018-01's rule

* **The version byte stays 1** (Q4). Every object written after the
  change is a valid version-1 object, and 2026.3 reads it: the new
  format is a subset of the old. A version 2 would make every object's
  bytes differ for no reader's benefit, and every start reads the index
  definitions, which are `DbObject`s: a reader of version 2 only would
  refuse every database with an index. If question 3 brings a version 2
  (the kind of a value stored), the null rule rides along.
* **Old databases** (no backward compatibility is needed: Frans,
  2026-11-06, 12:05; 020-01, section 14, decision 7 is open): a database
  of 2026.3 or before starts as before. Its objects without nulls read
  as before. An object with a null is refused by the reader (Q3): its
  get throws `ObjectCreationException`, and a put or a delete of its key
  in an indexed directory throws `DataFormatException`, since index
  maintenance reads the previous value (`RwEnvironmentImp.indexEntries`,
  line 401); such an object can then be removed only by deleting the
  directory's indexes first, or replaced by a `String` or `byte[]` put
  outside indexed directories. The release notes say so.
* **The index definitions** (`/#i/dii/-<name>`, `Data.Index`, written by
  `IndexManager`, line 382, read at every start): no field of one is
  null (`Data.createIndexDo` sets `dirs`, `fields`, `typeStrings` and
  `state` from a built index, each element non-null, and `version` is
  1). Their bytes do not change, and a start reads them as before. So
  what a start reads (018-01, section 2) changes only in that the reader
  refuses encodings no definition holds. StreamDigest's workloads put
  `String`s and `byte[]`s only: no digest changes.
* **018-01's rule** (every change of the stream format approved by Frans
  before it is made) holds for 2026.4 if 020-01's decision 7 says the
  object format is under it; Frans's "ok-and-implement" of this design is
  then the approval, recorded in this item's log.

### 3.3. The spec text

For the object format's spec (020-02, question 4), the part on null and
absence, written for a binding in another language:

> **Absence.** An object holds zero or more fields with distinct names.
> A field that is present holds one value of its type; no type has a
> null value. A field that the object does not hold is absent. Absence
> is the only way to say that a field has no value, and every reader
> meets it: in an object written before its class had the field, or by
> another language.
>
> **Encodings** (version 1). A string (`s`) is a 32-bit little-endian
> length n, 0 ≤ n, then n bytes of well-formed UTF-8. A byte array (`b`)
> is a length n, 0 ≤ n, then n bytes. An array (`a`) is its elements,
> each a type byte (`n`, `i`, `l`, `d`, `s`, `b`, `a` or `o`) and a
> value, then the byte `z`; every index from 0 to its length − 1 holds a
> value. An object is `bergo`, the version byte 1, a 16-bit
> little-endian field count c, 0 ≤ c ≤ 32,767, then c field infos and c
> fields; nested (`o`), it is preceded by its 32-bit size, at least 8.
>
> **A reader refuses** as malformed: a negative length of a string or a
> byte array; the byte `Z` anywhere in an array; a negative field count;
> a nested object's size below 8; `z` or `Z` as a field's type byte. (A
> length of −1, `Z` and a field count of −1 were the null encodings of
> BergDB 2026.3 and before.)
>
> **`z` is not a type.** In an array it ends the elements. An API may
> use it to answer "no such field", as Java's `DbObject.getType` does.
>
> **A writer** stores its language's "no value" in a field (Java's and
> C#'s `null`, Python's `None`, JavaScript's `null` and `undefined`,
> Swift's `nil`, Rust's `None`, a nil pointer in Go) by leaving the field
> out. It refuses a "no value" where nothing can be left out: an array
> element, and the value at a key. A writer whose classes give fields
> initial values (Java, C#, Kotlin) refuses a "no value" in a field to
> which the class gives a non-null initial value, since a reader of that
> class would read the initial value.
>
> **A reader** gives an absent field its language's value for a missing
> field: the class's initial value (Java, C#, Kotlin), `None` or `nil`
> for an optional (Rust, Swift), no key (Python, JavaScript), the zero
> value (Go). A present field is never "no value".


## 4. The change plan, file by file

Lines at `7edcbe2`, in `java/src/bergdb/`. Steps A to D are those of
section 9.

**`pubimp/DbObject.java`**

* Class Javadoc, lines 42 and 45 to 50: `z - zero ... reserved for
  null-capability` and the sentences that say a string, an object, a
  byte array and an array "can have the value null": replaced by the
  text of section 6.2 (step D).
* Field `isNull` (line 110), the constructor's field count (lines 160 to
  171: −1 is null; `fCount < -1` refused) and `isNull()` (213 to 215):
  the field and the method go; a count below 0 throws
  `BadFormatException` (step A).
* `toDbObject` (Javadoc 333, code 340 to 343): null throws
  `IllegalArgumentException` instead of `Builder.buildNull()` (step B).
* `toDbObjectOnPath`, the field loop (447 to 466): after `f.get` (452), a
  null value of a reference field is left out (`continue`), unless the
  check of section 2.2 says the class's constructor gives the field a
  value, which throws the path exception with the field's name (step B
  leaves out; step C adds the check). The catch at 463 to 465 takes the
  path exception's base class.
* New: the per-class check of section 2.2, a private static nested
  class with its `ClassValue`, or a package-private class of its own in
  `pubimp` (`@author Frans Lundberg` or none) (step C).
* `toJavaObject(Class, ClassToObject)` (482 to 485): the `isNull()`
  branch goes. Lines 490 to 493 (no wrapped `array` field) stay: no null
  reaches them, and an object without the field is question 1's.
* `toJavaObject(Object, ClassToObject)` (526 to 537): the `isNull()`
  branch and its `defaultValue` go; Javadoc "Returns 'dest'".
* `getType` Javadoc (565 to 567) and the getters (620 to 686): Javadoc
  only, the absent case as section 2.4 says.
* `parse` (735 to 750): a size below 8 throws `BadFormatException`
  (today −1 returns null).
* `DbField` constructor (759 to 762): `value == null` throws
  `IllegalArgumentException` (today an assert). `DbField.parse` (856 to
  857): a bad type byte throws `BadFormatException`, not
  `IllegalArgumentException` (step A).
* `Builder.buildNull` (883 to 887) goes; `buildInner(boolean isNull)`
  (957 to 1012, the count at 990) loses its parameter; `addString`
  (929) refuses null through `DbString` (step A).

**`pubimp/DbValue.java`**

* `toJavaObject` (160 to 209): no change for null; its `toString()` for
  `String` (204 to 206; S2-F4) and the 0 of `toLong()` (128 to 130; BG3)
  are question 1's.
* `defaultValue` (373 to 415): goes; its only caller was
  `DbObject.toJavaObject`'s null branch.
* `toNullDbValue` (417 to 431): goes.
* `toDbValue(Class, Object)` (433 to 462): the null branch (441 to 443)
  goes, and with it the parameter `dstType`, used only for null:
  `toDbValue(Object)`; its callers (`DbObject`, lines 432, 441 and 461;
  `createDbArray`, 514) never pass null.
* `createDbArray` (505 to 521): a null element throws the path exception
  with `"[" + i + "]"` (step B); the catch at 515 takes the base class.

**`pubimp/DbArray.java`**

* Class Javadoc, line 28: "it may have the value null" goes.
* `toString` (62 to 65), `isNull` (67 to 69), `toJavaObject`'s null
  branch (91 to 93), and the null returns of `toIntArray`,
  `toLongArray` and `toDoubleArray` (117 to 119, 131 to 133, 145 to 147):
  go.
* `ElementIterator` (190 to 202): `Z` anywhere throws
  `BadFormatException` (today it ends the array, at any position);
  `hasNext` tests `z` only. An `o` element whose `DbObject.parse` fails
  throws `BadFormatException` (today a `NullPointerException` at 241).
* `Builder.buildNull` (277 to 283): goes.
* `@Nano testNull` (320 to 324): becomes a test that bytes `Z` are
  refused (section 5.1).

**`pubimp/DbString.java`**

* Constructor (22 to 36): null throws `IllegalArgumentException`;
  Javadoc "A string value, or null" changes.
* `getByteSize` and `write` (72 to 89): the null branches go.
* `parseToString` (105 to 116): a negative size throws
  `BadFormatException` (today −1 returns null, and below −1 a
  `NegativeArraySizeException` escapes). 021-06 (open) changes this
  method's decoding too: whichever comes second merges.
* `@Nano test0` (124) and `testSerialize1` (148 to 151): section 5.1.

**`pubimp/DbByteArray.java`**

* Constructor (17 to 27): null throws `IllegalArgumentException`;
  `getByteSize`, `toString`, `write`, `toJavaObject` (29 to 66): the null
  branches go; `parseToByteArray` (74 to 88): −1 refused as every
  negative size.

**`pubimp/DbBoolean.java`, `DbInt.java`, `DbLong.java`,
`DbDouble.java`**: no null; no change.

**`pubimp/KvToObjectImp.java`**: no change. `entryToDbObject` (101 to
114) turns the reader's `BadFormatException` into
`ObjectCreationException`, which is how a 2026.3 object with a null
reaches a get. `createObject`'s `value == null` (53 to 55) is a missing
key, not a null value, and stays.

**`pubimp/BlankConstructorFactory.java`**: no change (gets).

**`pubimp/RwEnvironmentImp.java`**: no change in code. `put(String,
Object)` (305 to 342) refuses a null at the top; `ObjectInfo` (639 to
656) calls `toDbObject` (653), where the refusals of section 2.1 come
from; a `DbObject` put as it is (650) holds no null.
`indexEntries` (361 to 432) reads the previous value with
`new DbObject` (401): the path of section 3.2's old objects.

**`pubimp/FieldIndexFunction.java`**: no change in code; the Javadoc
of `createIndexEntry` (41 to 45) states section 2.5's rule.

**`pubimp/IndexEntryBuilder.java`**: `sortBytesFromString` (131 to 141):
the check stays; its comment says that no stored object holds a null
`String` since 020-04, so it guards BergDB's own code.

**`pubimp/IndexBuilderImp.java`**: the comment at 352 to 355 ("such as
an object that the index function cannot index") names the null `String`
no more; the rule (a `RuntimeException` ends the build as failed, and
the database goes on) stays.

**`pubimp/Data.java`, `IndexManager.java`**: no change; no definition
holds a null (section 3.2). `Data.Index.check` (50 to 155) keeps its
null checks: an absent field reads as the constructor's null.

**`pub/package.html`, `src/overview-pub.html`, `pub/Connection.java`,
`pub/WBuilder.java`, `pub/RwEnvironment.java`**: section 6 (step D).

**`releases/next.md`**: section 6.3 (step D).

Not touched: the Core, the stream, the Lean model, the C clone (objects
are bytes to it), `docs/levels.md` (it says only that objects are
experimental).


## 5. The tests

### 5.1. Existing tests

020-03 counted about a dozen in `DbObjectTester`; 19 of its 72 set a
null, and 4 more hold nulls by default (classes whose reference fields
are not set). Each, with what it becomes under (d); "passes" means
unchanged.

`pubimp/DbObjectTester.java` (line of the test):

* `testString1` (168): `TestClass1.s = null` over `"a string"`: refused.
  Becomes a refusal test naming `s`.
* `testByteArray3` (207): a null `byte[]`, no initial value: absent.
  `has("field", 'b')` becomes false and `getType` `z`.
* `testObject2` (308): `ObjectClass.nested = null` over `new Nested()`:
  refused, naming `nested`.
* `testSetObjectFields6` (364): `m1.obj.nested = null`: refused, naming
  `obj.nested`.
* `testIntArray3` (412), `testLongArray3` (455), `testDoubleArray3`
  (504): a null array, no initial value: absent; `has` false, `getType`
  `z`, `getArray` null.
* `testPrimitiveArrays1` (581): nulls with no initial value: absent,
  read back into a new instance as null. Passes.
* `testPrimitiveArrays2` (599): an object with every array null, read
  into an instance that `setThem1` filled: the absent fields are not
  set, so the filled values stay and the test's asserts fail. Becomes:
  read into a new instance (nulls), and into the filled one, whose
  values stay: the rule of section 2.3, stated.
* `testStrings0` (661) and `testStrings2D` (796): `Strings.setThem1` puts
  null elements (`{"a", null}`) and a null row: refused. `setThem1` gets
  no null elements (a row of its own length, an empty row for the null
  one); `s0b` and `s2b`, null with no initial value, stay and read back
  null.
* `testStrings2` (696), `testStringArray0` (937), `testArray1` (960): a
  null `String` element: refused, naming `strings[0]`, `array[2]`, `[0]`.
* `test5DIntArray` (733): `array[0][0][0] = null`: refused, naming
  `array[0][0][0]`. Becomes a full 5-D array.
* `test4DCustomerArray` (778): `new Customer[1][2][3][3]` with one
  element and one row set to null and most elements never set: refused
  at the first null, `array[0][0][0][1]`. Becomes a jagged array with
  every element set.
* `testArray4` (1001): an `int[][]` with a null row: refused, naming
  `[1]`. Becomes an empty row.
* `testNullField0` (909): as `testString1`: refused.
* `testNullField1` (923): `A.field = null` over `new TestClass1()`:
  refused, naming `field`.
* `testCycleRefused`, `testDeepRefused`, `testDeepAtLimit` (1182 to 1235)
  and `testLoneSurrogates` (1265): null fields with no initial value
  (`Link.next`, `StringsClass`): absent. Pass.

The `@Nano` tests of the `Db*` classes:

* `DbString.test0` (124): `new DbString(null)` becomes a refusal.
* `DbString.testSerialize1` (148 to 151): the null round trip becomes:
  `parse` of the length −1 throws `BadFormatException`.
* `DbArray.testNull` (320 to 324): becomes: `parse` of `Z` throws
  `BadFormatException`.

Elsewhere:

* `PubTester.nullStringField` (1302) and `nullStringArrayField1` (1319):
  null with no initial value: absent, reads back null. Pass.
* `PubTester.nullStringArrayField2` (1331): `{"", null}`: the put is
  refused, naming `strings[1]`, and nothing is written (the get returns
  null).
* `PubTester.testKeyField2`, `testKeyFieldInSuperClass1`,
  `testKeyFieldWithIterator` (1914, 1998, 2017): a null `key` with no
  initial value: absent, read back as the database key. Pass.
* `PubTesterIndexJobs.testBuildOverAnObjectItCannotIndex` (231): its
  `Named(null)` gives no entry now, and the build ends done with 2
  entries. Its first part becomes new test N11; the restart part (a
  start takes a failed build again) needs another object an index cannot
  index. With no null left, the implementer finds one (an indexed value
  too large for a key, if the Core refuses it: 020-01, section 6.5,
  question 6) or drops it; a failed build stays covered by
  `testErrorInBuildFailsTheDatabase`'s `RuntimeException` and, later, by
  H3.
* Night tests: `PayTest` (`Account.key` null, no initial value) and
  `CcDbNightTest` (`Stats`, an `int`): pass; `PayTest`'s objects are 16
  bytes shorter (no `key` field: its type, name, length and field
  info). `BryanRepro` (`level2.sh`) sets every
  field: passes. `PubPromiseTester` puts `String`s and `byte[]`s only.
* The index testers (`PubTesterIndex`, `PubTesterComposite`,
  `PubTesterNestedFields`) put no null: pass.

### 5.2. New tests

Each says what it checks and why it fails on today's code. In
`DbObjectTester` unless named.

* **N1. A null field is absent.** An object with null `String`,
  `byte[]`, `String[]`, nested object and `Integer` fields, none with an
  initial value, gives a `DbObject` without them: `getType` is `z` for
  each and `getFieldCount` counts the others; read back, each is null.
  Today the five are stored as nulls of `s`, `b`, `a`, `o`, `o` (BG1).
* **N2. A null over an initial value is refused, at every depth.** A
  null `String name = "x"` in the outermost object, in a nested object
  and in an object that is an array's element is refused with
  `IllegalArgumentException` naming `name`, `inner.name` and
  `items[2].name`; a null `Integer count = 42` too. Today each is stored,
  and reads back as null.
* **N3. A null array element is refused, at every depth.** `String[]
  {"a", null}`, `Integer[] {1, null}`, a `Customer[]` with a null, an
  `int[][]` with a null row, a `new String[2]` not filled, and a
  top-level `String[]` with a null, each refused naming the element
  (`names[1]`, `rows[1]`, `[0]`). Today each is stored.
* **N4. Absent and null-at-the-put give the same bytes.** An object with
  a null field and one of a class without that field give equal bytes,
  and equal index entries. Today the bytes differ by the null field.
* **N5. A put of a refused object writes nothing.** In `PubTester`:
  `w().put` of a valid object and an object with a null element in one
  transaction throws, and neither key exists afterwards; inside `rw()`,
  the refusal is the action's exception, and the database goes on.
  Today both are written.
* **N6. The constructor runs only when needed.** A class whose
  no-argument constructor counts its calls: puts of 100 objects without
  a null field run it 0 times; puts of 100 with a null field run it once
  (twice at most). Today it runs 0 times, and the null is stored.
* **N7. A constructor that throws.** A class whose constructor throws
  an `IllegalStateException`: a put of an object with a null field is
  refused with `IllegalArgumentException` whose cause is it, inside
  `rw()` too without failing the database; a put without a null field is
  taken. Today both are taken.
* **N8. No no-argument constructor.** A class whose only constructor
  takes an argument, with a null `String` field: taken, the field absent.
  Today stored as a null `s`.
* **N9. The Builder refuses null.** `addString`, `addObject`, `addArray`,
  `addDbValue` with null, `new DbString(null)`, `new DbByteArray(null)`
  and `toDbObject(null)` each throw `IllegalArgumentException`. Today
  `addString` stores a null, the next three throw an `AssertionError`
  (with `-ea`), and `toDbObject(null)` returns a null object.
* **N10. The reader refuses the null encodings.** `new DbObject(bytes)`
  of the bytes BG5 printed (`626572676f01ffff`, a null object), of an
  object with an `s` field of length −1, a `b` of −1, an `a` that is `Z`,
  an array with `Z` after an element, and a nested `o` of size −1, each
  throws `BadFormatException`; a get of such a value at a key throws
  `ObjectCreationException`. Today the first four read as nulls, `Z`
  after an element ends the array, and the last throws an
  `AssertionError` or a `NullPointerException`.
* **N11. A null indexed field gives no entry.** In `PubTesterIndexJobs`:
  `Named("a")`, `Named(null)`, `Named("c")` with a `string` index over
  `name`: the put is taken and the index has 2 entries; a build over the
  same three objects ends done, with the same 2 entries. Today the put
  throws "A null String cannot be indexed", and the build fails (019-42).
* **N12. One index rule.** In `PubTesterIndex`: a `long` index over `v`
  and a `string` index over `inner.name`, over objects with the field
  present, absent from the class, null, and with a null `inner`: entries
  for the present ones only, equal to those of objects whose class lacks
  the fields. Today the null `String` case throws (N11); the others pass,
  so the test fails only by its `String` part.
* **N13. The round trip of everything that is taken.** A class with a
  field of each kind, each null where the constructor allows it and set
  otherwise, puts and reads back equal, field by field. Today it passes;
  it guards (d)'s promise, and is the seed of H1.
* **N14. Malformed lengths are `BadFormatException`.** A string length
  of −2, a field name length below 0, a bad field type byte: each
  `BadFormatException`. Today `NegativeArraySizeException`, and an
  `IllegalArgumentException` for the type byte, which `KvToObjectImp`
  does not turn into `ObjectCreationException` (section 10). Optional:
  it is not null's, but it is the same lines.

### 5.3. The harnesses

* **H1** (020-01, section 15, objects round trip) lists "nulls" among
  its generated cases. Under (d): a generated null field with no initial
  value expects absence and a null read back; a null over an initial
  value and a null element expect a refusal with the path; the reference
  (a plain field map) has no null entries, and a class pair with a field
  added expects the constructor's value. Under (c), the second case
  expects the initial value read back. H1 is not written; its spec takes
  this when it is.
* **H2** (indexes as a function of the data): its reference index
  function is section 2.5's rule, with no null case.


## 6. The documentation

The model is 021-04: the rule in full once, in the package `bergdb.pub`'s
documentation, and a sentence with a link wherever a put or a get is
documented.

### 6.1. The rule in full: bergdb.pub, "Null and absent fields"

A new section of `pub/package.html`, after "Strings" (line 37), draft:

    <h2 id="null">Null and absent fields</h2>

    <p>BergDB stores no null. An object (a value that is neither a String
    nor a byte[]) is a set of named fields, and a field that is there
    holds a value of its type: a string, an array, a nested object, never
    null. A field that has no value is absent. It is a rule of BergDB's
    object format, the same in every language that writes or reads a
    database, not a detail of Java.</p>

    <p>A put stores a null field of the object, at any depth, as absent:
    the field is left out. A null Integer, or another wrapper, is absent
    too. A get of an absent field leaves the field as the class's
    no-argument constructor set it, whatever its type; so a null put
    reads back as null. A get meets absence also in an object written
    before its class had the field, or in another language.</p>

    <p>A put refuses, with IllegalArgumentException and before anything is
    written, a null that would not read back, or that cannot be absent;
    the message names its place from the outermost object, such as
    "inner.names[3]":</p>
    <ul>
    <li>a null field to which the class's no-argument constructor gives a
    non-null value, as in <code>String name = "x";</code>: a get would read
    "x". To find these fields, the constructor runs once per class, the
    first time a put meets a null field in an object of the class; it
    should have no side effects, as for a get. A class without a
    no-argument constructor is not checked.</li>
    <li>a null element of an array, at any depth, such as an element of
    <code>new String[3]</code> not set: an array has no absent
    elements.</li>
    <li>a null value at a key, as for a String or a byte[].</li>
    </ul>

    <p>The reason: absence is a "no value" that every reader in every
    language must handle anyway, for objects written before a field
    existed. A stored null would be a second one, beside it, in every
    rule and every language; and BergDB does not change data silently, so
    a null that a get would read as something else is refused.</p>

    <p>What to do: for a field with an initial value that may be null,
    drop the initial value, or set the field before the put. For an
    array with gaps, store a placeholder, or an object per element with
    an optional field. An application that needs "no value" apart from
    "not written" stores it explicitly, as a field of its own.</p>

    <p>A user index gives an object no entry for a field that is absent
    (Database.indexBuilder()).</p>

`src/overview-pub.html`, after its sentence on strings (lines 19 to 21):
"An object holds no null: a null field is stored as absent, and a null
array element is refused. In full: Null and absent fields, in the
package bergdb.pub."

### 6.2. The other places

* `Connection`, class Javadoc after "Strings." (lines 21 to 24): "Null.
  An object holds no null: a put stores a null field as absent, and a
  get leaves an absent field as the class's constructor set it; a put
  refuses a null array element, and a null field over a non-null initial
  value. The rule in full: the package's Null and absent fields (bergdb
  020-04)."
* `Connection.put` (Javadoc 211 to 237), `WBuilder.put(String,
  Object)` and `put(Object)` (18 to 55), `RwEnvironment.put(Object)` and
  `put(String, Object)` (50 to 84): in `@throws IllegalArgumentException`,
  "or if the object holds a null that cannot be stored, an array element
  or a field over a non-null initial value: the message names it (the
  package's Null and absent fields)".
* `Connection.get` (Javadoc 145 to 180) and `RwEnvironment.get` (15 to
  31): "An absent
  field of the stored object leaves the field as the constructor set it
  (the package's Null and absent fields)."
* `Database.indexBuilder` or `IndexBuilder`'s class Javadoc: "An object
  has no entry for a field that is absent, or present with a type the
  index does not take."
* `DbObject`'s class Javadoc (pubimp, outside the Pub API's Javadoc), in
  place of lines 42 and 45 to 50:

      z - absent     Not a type: getType() answers 'z' for a field the
                     object does not have. In the bytes, 'z' ends an array.

      <p>No type has a null value: a field holds a value of its type, or
      the object does not have it (the Pub API's package bergdb.pub, "Null
      and absent fields"; bergdb 020-04). toDbObject() leaves a null field
      out, and refuses a null array element and a null field over a
      non-null initial value; the Builder, DbString and DbByteArray refuse
      null; a reader refuses the null encodings of 2026.3 and before (a
      length of -1, an array 'Z', a field count of -1) with
      BadFormatException. getString(), getByteArray(), getArray() and
      getObject() return null for an absent field, Java's way to say
      absent; getInt() and the other numbers 0, getBoolean() false; has()
      and getType() tell.</p>

* `DbArray`'s class Javadoc, line 28: "The array may be of zero length;
  it is never null, and no element is null."

### 6.3. releases/next.md

Under "Pub API", draft:

* **An object holds no null** (bergdb 020-02, question 1b; 020-04;
  Frans, 2026-11-07, DATE OF THE OK). A null field of an object, at any
  depth, is stored as absent, and a get leaves an absent field as the
  class's no-argument constructor set it, so a null put reads back as
  null. A put refuses with `IllegalArgumentException`, naming the place,
  a null array element and a null field to which the constructor gives
  a non-null value (a get would read that value); to find these, the
  constructor runs once per class at a put. A null wrapper (`Integer`)
  was stored as a null object and is now absent. `DbObject.Builder`,
  `DbString` and `DbByteArray` refuse null; `DbObject.isNull()`,
  `DbArray.isNull()` and the `buildNull()` methods are gone.
* **A user index gives no entry for a null `String` field**, as for a
  missing field; the put was refused with "A null String cannot be
  indexed", and a build over one failed (bergdb 019-42).
* **The object format has no null encodings** (020-04, section 3): an
  object written now is read by 2026.3 too. An object with a null,
  written by 2026.3 or before, is refused when read: a get throws
  `ObjectCreationException`, and a put or a delete of its key in an
  indexed directory throws `DataFormatException`. Index definitions hold
  no null, so every database starts as before. The stream's bytes:
  StreamDigest's workloads put no object; no digest changes.


## 7. How it fits question 1 and option (D)

* **Question 1's table** (020-02, section 2.2): its rows "null, a
  reference type: null" and "null, a primitive: throws" become one,
  "absent, any type: the constructor's value (the field is not set)".
  This holds for (A), (B), (C) and (D) alike: absence is not a
  conversion. The table's other rows (a present value of another type or
  kind) are question 1's; BG3's silent 0 for a `String` into an `int`
  stays until it is decided (section 2.3).
* **Option (D)'s report** (020-02, section 2.5): under (d) "a field of
  the class that is not stored" is the one "no value", and it covers a
  Java null at the put as well as a field added since. For a field
  whose constructor value is null they cannot be told apart, and need
  not be: the value read is what was put. So:
  * an absent field never makes a conversion not exact (`isExact()`);
  * the report lists an absent field only where the constructor gives
    it a non-null value, the only case where absence can change what
    the application sees (type evolution, or another language's object);
  * (D)'s question 2 (`isExact()` against `isComplete()`) then needs no
    null case.
* **What stays open until those are decided**: the conversion of a
  present value of another kind (question 1); the closed list, `Object`
  and polymorphic fields, final fields, and whether a put requires a
  no-argument constructor (question 2, and Q2 here); the kind of a value
  and a format version 2 (question 3); the spec's home and 018-01's rule
  for the object format (question 4, 020-01's decision 7); the field
  `key` (question 5). None of them blocks this change: each rule here
  holds for whatever they decide, and section 3.3's text joins the spec
  when question 4 makes it.


## 8. Questions for Frans

* **Q1. Which option?** (d) null is absence, exactly; (c) null is
  absence, a null over an initial value read back as that value; (b)
  every null refused. Recommended: (d), for 020-02's reasons (section
  2b.4). If running the constructor at a put is not wanted, (c), with the
  asymmetry documented. The implementation is the same for the three
  up to step B of section 9.
* **Q2. A class without a no-argument constructor**: its null fields
  left out, unchecked (recommended until question 2), or the put
  refused, since such an object cannot be read back into its class? The
  same for a constructor that throws: refuse only a put that needs it (a
  null field; recommended), or every put of the class.
Note (2026-11-08): under 020-05's option (f), Q3 widens to every object
of 2026.3 (020-02, section 4.11), Q4 is replaced by (f)'s header (020-02,
section 4.5), and Q5 was done by 021-07, by that entry's default: every
add method of the Builder refuses null (section 11).

* **Q3. An object with a null from 2026.3**: refused by the reader
  (recommended: no backward compatibility is needed, the spec stays
  simple, and no binding must know the old encodings), or read with a
  null field as absent (a few lines; a null element still refused)?
  Under the recommendation such an object in an indexed directory can be
  removed only after its indexes are deleted (section 3.2).
* **Q4. The version byte**: stays 1 (recommended: the new format is a
  subset, 2026.3 reads it, and every start reads index definitions, so a
  version 2 would need a reader of both), or 2, so that an old object is
  told by its version?
* **Q5. `DbObject.Builder` with null** (`addString(name, null)`):
  refused (recommended; binson-java's choice, 020-03, BN1), or the field
  left out, as `toDbObject` does for a class?
* **Q6. `DbObject.getString` of an absent field**: null, and 0 or false
  for the numbers, as today (recommended for now; 020-02, section
  2b.5), or a throw, as binson-java's `getString` (BN2)? Part of
  `DbObject`'s API, which question 1's (D) may redesign; not needed for
  this change.


## 9. The work: size and order

After Frans's "ok-and-implement", in this order; each step's tests come
with it, written first and seen to fail on the code before the step.

1. **Step A, the format** (the same in (b), (c), (d)): `DbString`,
   `DbByteArray`, `DbArray`, `DbObject`'s reader and Builder refuse null
   and the null encodings, with `BadFormatException` for every malformed
   length; `isNull`, `buildNull`, `defaultValue` and `toNullDbValue` go.
   Tests N9, N10, N14; the `Db*` `@Nano` tests. Size S: about 120 lines
   changed, 60 of them removed.
2. **Step B, the put** ((c); (b) refuses where (c) leaves out): a null
   field left out, a null element and `toDbObject(null)` refused, the
   path exception's base class. Tests N1, N3, N4, N5; the existing tests
   of section 5.1. Size S: about 60 lines of code; the existing tests
   about 150 lines.
3. **Step C, the check of (d)**: section 2.2's class info, constructor
   run and refusal. Tests N2, N6, N7, N8, N13. Size S: about 80 lines of
   code, 150 of tests.
4. **Step D, gets, indexes, documentation**: the dead null branches of
   the get, 019-42's comments, N11 and N12 and the rewrite of
   `testBuildOverAnObjectItCannotIndex`, the Javadoc of section 6, and
   `releases/next.md`. Size S: about 40 lines of code, 100 of Javadoc.

Steps A and B make one commit, which is (c) without its Javadoc; step C
a second, which makes it (d); step D a third. If Frans chooses (c), step
C is not made and step D documents the asymmetry; for (b), step B
refuses instead of leaving out, and step C is not made.

The gate for each commit: `java/before-commit.sh` (BEFORE COMMIT OK),
and `java/javadoc-pub.sh` (JAVADOC PUB OK) for step D. No level script
is needed: the Core is not touched; `level2.sh` runs `BryanRepro`, whose
objects hold no null.

In all, about one day of an agent's work (xhigh is not needed; high),
plus the gates.

Under 020-05's option (f), step A is not made: (f)'s codec takes its
place, with no null in it; steps B to D stay (section 11).

What can be done before the ok: nothing in code. Two things are
independent of null and could be done now if Frans wants, each a 021
entry: the reader's malformed lengths and type bytes as
`BadFormatException` (N14 and part of step A; section 10), and the
optional cache of the eligible fields per class (section 2.2). And
021-06 (open) changes `DbString.parseToString` too: whichever is done
second merges.


## 10. Found in the code, not in 020-03

The second, third and fourth points were fixed on 2026-11-07 by 021-07
and 021-08 (section 11).

* **BG3's silent 0 is not null's.** Any `String` read into an `int` or
  `Integer` field gives 0, not only a null one: `DbString` has no
  `toLong()`, and `DbValue.toLong()` answers 0 (`DbValue`, lines 128 to
  130); `checkFits` does not look at strings (247). (d) removes the null
  case only; the rest is question 1's. And an object (`o`) read into an
  `int` field throws `Bug`, null or not (`DbObject.toJavaObject`, 507 to
  510, then `Field.set` at 553). 020-02, section 2b.4, reason 3, counts
  both as gone by (d); they go with question 1.
* **A fourth null encoding, read only**: a nested object's size −1,
  which `DbObject.parse` reads as Java's null (739 to 741). No writer
  writes it; reading it gives an `AssertionError` with `-ea` or a
  `NullPointerException` (the `DbField` constructor, 762; in an array,
  `DbArray`'s iterator at 241). Inside `rw()` an `AssertionError` fails
  the database (019-10): data from another writer can do that (020-01,
  N2).
* **The reader's other refusals are not `BadFormatException`**: a string
  or byte array length below −1, or a field name's negative length, gives
  a `NegativeArraySizeException` (`DbString.parseToString`, 112;
  `DbObject.readFieldInfo`, 700); a bad field type byte an
  `IllegalArgumentException` (`DbField.parse`, 857). `KvToObjectImp`
  catches only `BadFormatException`, so these reach the caller of a get
  as they are. And `Z` after an element ends an array silently
  (`DbArray`, 201).
* **`DbObject.Builder`'s nulls are uneven today**: `addString(name,
  null)` stores a null `s`; `addObject`, `addArray` and `addDbValue` with
  null throw an `AssertionError` (with `-ea`) or a
  `NullPointerException`, and an `AssertionError` in `rw()` fails the
  database.
* **The field `key` is not an exact round trip**: whatever was put, a
  read sets it to the database key (`DbObject.getDbValue`, 598). (d)'s
  promise excepts it until question 5.
* **The index definitions hold no null**, so the change does not touch
  what a start reads (section 3.2), and no StreamDigest workload puts an
  object.
* **More tests than counted**: 19 of `DbObjectTester`'s 72 set a null
  (020-03: about a dozen), several through arrays not filled
  (`new Customer[1][2][3][3]`) and a shared `setThem1`: 13 of them are
  refused under (d), 5 change their asserts, 1 passes; 4 more hold
  nulls by default and pass (section 5.1).


## 11. Under 020-05's option (f), and since 021-07

Added 2026-11-08. This design was written for DbObject's format version
1, with section 4's lines at `7edcbe2`. 020-05 recommends since
2026-11-08 a new format, option (f), DbObject's table with Binson's
values (020-05, section 12b), and Frans leans to it, with no null and a
binary search for fields (2026-11-08, 15:22; 020-02, sections 4.1 to
4.3). If (f) is chosen:

* **What stays**: the rules of section 2: the put, the constructor check
  of (d), the get, `DbObject`'s own API but its encodings, and the
  index rule, where "`l` or `i` for `long`" reads "an integer" (020-02,
  section 4.7); the spec text's paragraphs on absence, on the writer and
  on the reader (section 3.3); the documentation of the rule (sections
  6.1 and 6.2, but `DbObject`'s sentence on the encodings); the tests of
  the rules, N1 to N8 and N11 to N13, and section 5.1's changes of the
  existing tests; section 7; Q1, Q2 and Q6.
* **Section 3.1**: (f) has no null encoding to refuse: none of its type
  bytes is a null (020-05, section 12b.1). A value of 2026.3 (`bergo`,
  version 1) is refused as a whole, or read by a reader of version 1
  kept for it: 020-02, section 4.11, in place of Q3.
* **Section 3.2**: in place of the version byte 1 and Q4, (f)'s header,
  0x82, is "format 2" (020-05, section 12b.2; 020-02, section 4.5). 2026.3 does not read 2026.4's objects, so "the new format is a
  subset of the old" no longer holds; the index definitions are objects,
  so their bytes change, and a start reads them in (f) (020-02, section
  4.11). StreamDigest's workloads still put no object: no digest
  changes.
* **Section 3.3**: "Encodings (version 1)" and "A reader refuses" are
  replaced by (f)'s rules (020-05, section 12b.1), which have nothing
  null to refuse. An array ends with 0x43 in (f), so "`z` is not a type"
  keeps only its API half: `getType` answers `z` for an absent field.
* **Section 4**: the lines of the format layer (`DbObject`'s Builder,
  `parse` and field infos; `DbArray`; the `write` and `parse` of
  `DbString` and `DbByteArray`; `DbValue.parse`) are rewritten by (f)'s
  codec (020-05, section 10), and their null branches go with them. The
  lines of the reflection (`toDbObject`, `toDbObjectOnPath`,
  `createDbArray`, the new class check), and those of `KvToObjectImp`,
  `RwEnvironmentImp`, `FieldIndexFunction` (a long index reads the
  integer), `IndexEntryBuilder`, `IndexBuilderImp`, `Data` and
  `IndexManager`, stay.
* **Section 5**: N10 becomes "the reader refuses 2026.3's bytes", or
  reads them, by 020-02, section 4.11; the `@Nano` tests of `DbString`
  and `DbArray` go with their classes.
* **Section 6**: `DbObject`'s Javadoc paragraph on the encodings
  (section 6.2) and the third bullet of section 6.3 ("an object written
  now is read by 2026.3 too") change: (f)'s objects are not read by
  2026.3.
* **Section 9**: step A is not made; (f)'s codec takes its place, with
  no null in it. Steps B, C and D stay: they change the reflection, the
  gets, the indexes and the documentation, which (f) keeps, and can come
  before or after the codec. 020-05's cost for (f), M, 3 to 5 days,
  includes this plan (020-05, section 10).

Since (f) was decided (020-02, section 4.2, 2026-11-08): its spec is
020-07, and the plan that carries this design's rules into the code with
it, steps B to D included, is 020-08.

Done since, on today's format (2026-11-07):

* **021-07**: the reader's malformed lengths and bad type bytes give
  `BadFormatException` (N14; section 10's third point); a nested
  object's size −1 is refused (section 3.1's fourth encoding; section
  10's second point); `Z` after an element is refused (`Z` as an array's
  first byte is still a null array); every add method of
  `DbObject.Builder` refuses null with `IllegalArgumentException`
  (section 2.4's "Today ..." sentence; section 10's fourth point; Q5, by
  that entry's default; N9's Builder part). A string's length −1 still
  reads as a null string, and a field count of −1 as a null object.
* **021-08**: the reader refuses an object nested deeper than the
  writer's limit (1,001 objects, 2,001 objects and arrays).
* So of section 9's "What can be done before the ok", only the optional
  cache of the eligible fields per class is left. Section 4's line
  numbers are `7edcbe2`'s; 021-07 and 021-08 moved some.


## 12. Log

2026-11-07. Written by coord-1107's agent p04 at Frans's word (14:31:
"Now it is ok to design and document. Prepare for it."), read-only at
`7edcbe2`; no code changed. Not decided: Q1 to Q6 wait for Frans.

2026-11-08. Section 11 added by coord-1108's agent d02 (020-02, section
4): what 020-05's option (f), which Frans leans to, changes in this plan
(the format, its spec text, the code sites, the tests, step A) and what
stays (the rules of the put, the get and the indexes, steps B to D); and
what 021-07 and 021-08 did since. Notes in the opening, sections 3, 8, 9
and 10. The log is now section 12. Not decided: Q1 to Q6.

2026-11-08, 21:47. Frans decided Q1: (c), a null field is left out at a
put, no put refused for it (020-02, section 5.1b); and question 1 of
020-02: best effort on a get, for 2026.4.

