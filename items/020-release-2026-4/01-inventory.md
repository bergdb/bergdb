020-01. Inventory: the non-Core part of BergDB
==============================================

Created 2026-11-06 by Frans Lundberg, from his plan for 2026.4 (020's
readme): an inventory of the non-Core part, feature by feature, before any
fix, for his keep, simplify or drop decisions.

**Status: written; nothing decided.** Read at `92844c2`, with one probe in
a clone (section 2). The recommendations are proposals; Frans decides,
feature by feature.


## 1. In short

* **What it is.** The non-Core part is what a user can reach that is not
  the Core of 2026.3 (018-01, section 1, D4): D6's experimental list,
  which is two things, objects (a value that is neither a `String` nor a
  `byte[]`) and user indexes, with what is under them in `pubimp`. Seven
  features and a boundary (section 3): F1 objects and their format, F2 the
  get into another class, F3 index definition and index functions, F4
  index maintenance in transactions, F5 index builds and deletions as
  jobs, F6 index reads, F7 the primary scan, F8 the API's boundary.
* **Its size.** About 6,400 non-blank lines of code and 5,700 of tests,
  against about 52,600 (code and tests) in the Core Layer's packages; and
  ICU 50.1, bundled for string collation: 2.0 MB of the 3.4 MB jar.
* **Its known faults.** 10 open entries of 015 and 26 open faults of
  review S2 (015-49), about 33 distinct faults, every one in 2026.1 too.
  The largest clusters: objects by reflection (F1, F2: 10 faults), the
  index jobs' state and status (F5: 11), the scan builder (F6: 4), and one
  cause behind three entries (F4: 015-28, 015-43, S2-F12).
* **New here** (section 12, not registered): since 019-10 (today), an
  index build that meets an object whose indexed `String` field is null
  fails the database, and the build that every start resumes fails it
  again within a second (N1, probed): a database the Pub API can no
  longer run. Errors made from the user's data now fail the database
  inside `rw()` but not outside it (N2, probed). `useIndex()` changes
  `transactionInfo()`, a Core promise (N3, probed). 015-37 is fixed in
  effect by 019-38 and still open (N6).
* **The first decision** (section 14): the shape of 2026.4's objects and
  indexes. Either objects stay, narrowed to a closed list of types, with
  indexes defined by data over their fields (recommended); or values
  become the application's own bytes, with indexes defined by functions
  in code. Most other choices follow from it.
* **The summary** is section 13; the first harness of each kept feature,
  section 15.


## 2. Scope, sources and method

* **The Core**, as 018-01 (section 1, D4) has it: the Core Layer and the
  Pub API but D6's list. **D6's list**: `Database.indexBuilder` and
  `deleteIndex`, `Connection.useIndex` and `usePrimary`, `IndexBuilder`,
  `UseIndexBuilder`, `UsePrimaryBuilder`, and a value that is neither a
  `String` nor a `byte[]` (`put(Object)`, a put of an object at a key, a
  get into another class); since W1 also `Database.PRIMARY`,
  `StartupInfo.getStartupJobs()`, `DbObject` and `DbArray`, and four
  exceptions (018-01, section 8, 10:32).
* **Read whole**: `pub/` `Database`, `Connection`, `ReadInterface`,
  `WBuilder`, `RwEnvironment`, `Transaction`, `Kv`, `StartupInfo`,
  `IndexBuilder`, `UseIndexBuilder`, `UsePrimaryBuilder`, the exceptions,
  `util/Job`, `JobStatus`; `pubimp/` `ConnectionImp`, `DatabaseImp`,
  `WBuilderImp`, `WTransaction`, `RwTransaction`, `RwEnvironmentImp`,
  `Data`, `IndexManager`, `IndexBuilderImp`, `UseIndexBuilderImp`,
  `UsePrimaryBuilderImp`, `IndexFunction`, `FieldIndexFunction`,
  `IndexEntryBuilder`, the collators and their factories,
  `KvToObjectImp`, `KvToObjectConverter`, `ClassToObject`,
  `ObjectFactory`, `BlankConstructorFactory`, `Entries`, `FieldRef`.
  **In part**: `DbObject` (the format, the conversions), `DbValue`
  (`toDbValue`), `PubKeys`, `PubUtil`, the testers' method lists.
* **The faults**: 015-23, 28, 29, 30, 36, 37, 39, 43, 46, 49, 61; the
  reviews behind them (016-06/S1, S1-F4 and F7; 016-06/S2, all; 016-07's
  R3, F5, F7, F9, F11; 016-06/R8's F6 by its entry); the fixes 019-38,
  015-40, 015-41, S2-F24; 019-39 and 019-40; 005-22, 23 and 26.
* **A probe**, in the clone `/Users/f/fl/bench/006-13/v1` at `92844c2`:
  `/Users/f/fl/bench/006-13/v1-probe/V1Probe.java`, five cases, each a
  few seconds (section 12). No performance test.
* **Sizes** are non-blank lines (comments and Javadoc included), split by
  a script into code and tests (a tester file, or a `@Nano` method, is a
  test). A file that serves two features is split by its methods, so the
  per-feature figures are rounded estimates.


## 3. The features

| ID | Feature                     | What the user calls                                  |
|---|---|---|
| F1 | Objects and their format    | `put(key, obj)`, `put(obj)`, `DbObject`, `DbArray`   |
| F2 | The get into another class  | `get(key, C)`, C not `String` or `byte[]`            |
| F3 | Index definition, functions | `indexBuilder()`, `IndexBuilder`, collations         |
| F4 | Index maintenance           | every put and delete in an indexed directory         |
| F5 | Index builds and deletions  | `start()`, `deleteIndex()`, `Job`, `getStartupJobs()` |
| F6 | Index reads                 | `useIndex()`, `UseIndexBuilder`, `Kv`                |
| F7 | The primary scan            | `usePrimary()`, `UsePrimaryBuilder`                  |
| F8 | The API's boundary          | `pubimp`'s public classes, `Kv.ikey()`, the jar      |

Shared by all: the write path (`RwEnvironmentImp`, `WTransaction`,
`RwTransaction`), which the Core's `String` and `byte[]` puts use too;
and `KvToObjectImp`, which every get goes through, also a `String` get.


## 4. F1. Objects and their format

### 4.1. Promises

* `Connection.put(key, object)` and `WBuilder.put`, `RwEnvironment.put`:
  "Special handling is provided for object of type byte[] and
  java.lang.String"; any other object is stored. `put(Object)` takes the
  key from the object's `String` field `key`, else
  `MissingKeyFieldException`.
* `DbObject`'s class Javadoc: a value of named, typed fields, eight types
  (`n` boolean, `i` int, `l` long, `d` double, `s` string, `b` bytes, `a`
  array, `o` object; `z` reserved); "The byte format needs to stay
  stable, since objects are stored in databases for a long time".
  `toDbObject`: the fields "that are not transient, not static, and not
  synthetic".
* Decided before: a cycle or a nesting deeper than 1,000 is refused with
  the field path (005-23); a lone surrogate in a string is stored as `?`
  (005-26).
* docs/levels.md: only section 1's line that they are experimental.
* **Unclear or missing**: which Java types are stored, and what a put of
  any other does (S2-F18 found `Date` stored as nothing and an enum
  refused with a JDK exception); final fields (left out, against the
  Javadoc: S2-F9); a field that hides a superclass's (S2-F19); the rule
  that an object's key has no suffix (or `.obj`), which only an
  exception's message says; what a `String` or `byte[]` at such a key
  means (015-46); whether the format is kept between releases; limits
  (the field count is 16 bits).

### 4.2. How it is built

* **Java to DbObject** (`DbObject.toDbObject`, `DbValue.toDbValue`): by
  reflection over the eligible fields of the class and its superclasses
  (not static, final or transient; set accessible). `byte`, `short`,
  `char` and `int` become `i`; `float` and `double` become `d`; a `String`
  `s`; a `byte[]` `b`; another array `a`, element by element; any other
  object `o`, by recursion. A top-level array is wrapped in a field
  `array`, a top-level primitive in a field `p`. The conversion runs in
  the caller's thread at the put, for `w()` before the transaction, for
  `rw()` inside its action.
* **The bytes**: `bergo`, a version byte (1), a 16-bit field count (−1:
  a null object), then per field its name's 16-bit hash and its 32-bit
  offset, then the fields, sorted by the bytes of their names (so the
  bytes do not depend on the order reflection gives), each with its type,
  name and value; little-endian. Deterministic (P2), as checked here by
  reading `Builder.build`.
* **The key field**: on a put, a field `key` is stored as any other; on a
  read, `DbObject` answers `key` with the database key, not the stored
  value (`getDbValue`).
* **What tells an object from other bytes**: nothing stored. A value is
  an object when its key has no suffix (or `.obj`) and its bytes start
  with `bergo` (`Entries.isProbablyDbObject`). A put of an object at a key
  with a suffix is refused; a `String` or `byte[]` may go anywhere.
* **In a transaction**: an object put, and a delete of a key without a
  suffix, go to `objectOps`, and the transaction runs through
  `RwTransaction.executeRw`: it reads the previous value to keep the
  indexes (F4), so a `w()` of objects can conflict and run again, with the
  sleeps of an `rw()`. A `w()` of `String` and `byte[]` puts only (and
  deletes of keys with a suffix) goes straight to `Db.execute`.
* **The Core**: an object is a value of the Core's; reclaim, eviction and
  restarts see bytes. A start reads no user object; it does read the
  index definitions, which are `DbObject`s (F3), so this format is under
  what a start reads.
* **Size**: about 1,850 lines of code (`DbObject` but its reads,
  `DbValue`, `DbArray`, the six `Db*` value classes, `PubUtil`, the object
  half of `RwEnvironmentImp`); tests with F2's.

### 4.3. Known faults

* 015-46 = S1-F7 = S2-F3: a `String` or `byte[]` put over an object in an
  indexed directory leaves its index entries, and an object put or a
  delete there then throws `DataFormatException` for good (with F4).
* S2-F8: an array that holds itself throws `StackOverflowError` at the
  put; inside `rw()` it fails the database since 019-10 (N2, probed).
* S2-F9: a final field is not stored, silently: lost data.
* S2-F18: a field of a JDK value class is stored as nothing (`Date` reads
  back as the time of the read, `Instant` cannot be read), an enum or a
  collection is refused with a reflection exception; a `DbObject` in a
  field is stored as nothing.
* S2-F19: a field that hides a superclass field of the same name is not
  stored; both read back the superclass's value: lost data.
* N4 (section 12): the kind of a value is not stored; the suffix rules
  are not in the Javadoc.
* Fixed: 015-41 (2026-11-05, night 006-12): a `String` or `byte[]` put
  and an object put, or a delete, of one key in one transaction lost
  their order; the last call now wins. 015-40 (2026-11-03): two writes of
  one key, the same family. 005-23, 005-26 (2026-10-21).

### 4.4. Tests

* `DbObjectTester` (72 tests, 1,042 lines): round trips of each type,
  arrays to five dimensions, nulls, nested objects, hierarchies, a
  private constructor, narrowing (005-22), cycles and depth (005-23), lone
  surrogates; and the `@Nano` tests of the `Db*` classes (about 325
  lines).
* `PubTester`: about 20 of its 116 tests put objects (`testKeyField*`,
  `testDbObject*`, `testStoreArray`, `testStorePrimitive`,
  `testRwObjectPutThenStringPut`, ...). `BryanRepro` (`level2.sh`) and
  the night tests `CcDbNightTest` and `PayTest` use objects too.
* Not covered: a list of types that is the promise (each test picks its
  own); JDK classes, enums, collections, final and hidden fields
  (S2-F9, F18, F19); a `String` or `byte[]` put over an object in an
  indexed directory (015-46); a test that the bytes of an object are those
  of a written spec.

### 4.5. Open questions of meaning

1. Which Java types are stored, and how? A closed list (primitives and
   their wrappers, `String`, `byte[]`, arrays of these, classes made of
   them), or "any class", as today?
2. What does a put of anything else do: refuse at the put, with
   `IllegalArgumentException` and the field path (as 005-23 does for a
   cycle)?
3. Final fields: stored and set by reflection, or refused, or left out
   and said so? A field that hides another: refused?
4. Is the kind of a value (`String`, bytes, object) part of the stored
   value, or of its key's suffix, or of the directory (an indexed
   directory holds objects only)? May a `String` replace an object at an
   object key (015-46's design choice)?
5. Is the object format part of the stream's format, under 018-01's rule
   that Frans approves its changes (section 2; 010-P2)? It is under what a
   start reads only through the index definitions (F3). Who writes its
   spec, as 012-02 did for the stream? The C clone (012) reads a Pub
   database at the Core's level; objects are bytes to it, and stay so
   unless C gets a Pub layer.
6. Keep `put(Object)` and the field `key`?

### 4.6. Options

* **(a) Keep and fix.** Fix S2-F8 (arrays on 005-23's path), F9 (store
  final fields, or document), F18 (refuse what cannot round-trip, or add
  forms for enums and times), F19 (refuse), and 015-46 (F4). Reflection
  over any class stays: a surface without an end, which no harness covers,
  so faults of its kind will be found after the release. Cost: M (2 to 4
  days), and the round-trip harness (H1) only samples it.
* **(b) Simplify: a closed list of types.** The promise is a table: the
  primitives and their wrappers, `String`, `byte[]`, arrays of these and
  of such classes, and classes (records too) whose fields are of these,
  with a no-argument constructor. Anything else, final and hidden fields
  included, is refused at the put with the field path; nothing is stored
  as nothing. `put(Object)` and the key field go (one way to put). With
  no backward compatibility, the format may get a version 2 that stores
  the kind of a value, so that no suffix or magic bytes decide it
  (question 4).
  The spec is written in an item. Fixes most of F1's and F2's faults by
  construction, and makes the round trip checkable over the whole table.
  Cost: M, plus H1 (M).
* **(c) Replace: the application's own serializer.** Values are `String`
  and `byte[]`; the application writes JSON, protobuf or its own bytes.
  About 2,500 lines of code and 1,400 of tests go (F1 and F2); the tests
  that put objects (`PubTester`'s 20, `BryanRepro`, the night tests) are
  rewritten. Indexes then cannot read fields: they need functions in code
  (F3, option c). Frans named "serialization of Java objects" in the
  theme; this option leaves it to the application. Cost: S to remove, M
  for the tests, and F3's cost.
* **(d) Drop**: as (c), with nothing in its place.
* **Recommendation: (b)**, with (c) if the first decision (section 14)
  goes to functional indexes. Reason: the theme keeps object
  serialization; a closed list turns an open surface into a finite one
  that a harness can cover, and each refusal is a class of bugs that needs
  no fix (P13).


## 5. F2. The get into another class

### 5.1. Promises

* `Connection.get(key, clazz)`: "The class must in general have a
  no-argument constructor ... The matching field of the object create
  will be set based on the fields of the DbObject stored in the
  database." `DbObject.class` gives the stored object, `byte[].class` the
  bytes, `String.class` UTF-8. `Object.class` is named only in the
  paragraph on shared arrays (015-47).
* `ObjectCreationException`: "Thrown when an object should have been
  created, but could not be created". `DataFormatException`: "data in the
  database has an illegal format". 005-22: a stored number too large for
  its field throws `DataFormatException` with the field's name.
* **Unclear or missing**: what a class that changed since the put gets (a
  field added, removed, of another type); what a primitive field gets
  from a null, a missing field or another kind; the rules of
  `Object.class`; that the field `key` is set from the database key;
  that the constructor runs once more the first time (S2-F21).

### 5.2. How it is built

* Every get, also of a `String`, goes through `KvToObjectImp.createObject`
  after `Db.getOne`, outside the Core's call: `String.class` decodes,
  `byte[].class` returns the database's array, `DbObject.class` parses,
  `Object.class` picks by the key and the bytes (an object if the key has
  no suffix and the bytes start with `bergo`; a `String` if the key ends
  with `.txt`; else the bytes), any other class parses and fills a new
  instance (`DbObject.toJavaObject`).
* The instance comes from the class's no-argument constructor, made
  accessible, through a `BlankConstructorFactory` kept per class and
  database (its own constructor calls the class's once to test it).
* Field by field: a stored field of the same name is converted to the
  field's type (`DbValue.toJavaObject`, `checkFits`); a missing one leaves
  the field as the constructor set it.
* Inside `rw()`, the get runs in the action, so since 019-10 an `Error`
  of this code fails the database; outside it, the same `Error` fails only
  the call (N2).
* **Size**: about 640 lines of code (`KvToObjectImp`,
  `BlankConstructorFactory`, three small interfaces, `Entries`, the reads
  of `DbObject`, `DbValue` and `DbArray`, two exceptions).

### 5.3. Known faults

* S2-F4: a stored double read into a `String` field reads as "d:1.5".
* S2-F5: a stored double of 2^63 reads into a `long` as `Long.MAX_VALUE`.
* S2-F6: a stored value of another kind read into a primitive field gives
  0, or throws `Bug` (a null `Integer` into an `int`); since 019-10, in
  `rw()` it fails the database (N2, probed).
* S2-F7: the numbers, strings and booleans of an `Object[]`, or of an
  `Object` field, read back as null: lost data.
* S2-F21: a constructor that throws gives `Bug`, and runs once more than
  the reads; in `rw()` it fails the database since 019-10.
* 019-40, C4 (open): the words of where an `Error` does not fail the
  database name "the Pub API's conversion".

### 5.4. Tests

* With F1's: `DbObjectTester` (`testTypeSwitch`, `testNarrowing*`,
  `testNullField*`, `testPrivateConstructor`), `KvToObjectImp`'s own five.
* Not covered: a class changed between the put and the get, as a table;
  `Object.class` at each kind of value; an `Error` from the conversion in
  `rw()`; a constructor that throws later.

### 5.5. Open questions of meaning

1. The table of a stored kind against a field's type: which pairs give a
   value, which leave the field, which throw `DataFormatException` (005-22
   chose "throw" for numbers too large)?
2. May any user data, or any user class, make BergDB throw an `Error`, or
   fail the database (P7 is for the environment and for bugs)? The answer
   in N2 should be "no".
3. Keep `Object.class` (and how does it tell the kinds apart), and
   `DbObject.class` (a document view of the stored value)?
4. Is the field `key` set from the database key?

### 5.6. Options

* **(a) Keep and fix**: S2-F4, F5, F6 (throw), F7 (convert by the stored
  kind), F21 (`ObjectCreationException` with the cause, no test call);
  N2. Cost: S to M.
* **(b) Simplify with F1's (b)**: the table of question 1 is the promise;
  every mismatch throws `DataFormatException` with the field's name; a
  missing field keeps the constructor's value; no `Error` comes from the
  user's data or class; `Object.class` goes, or returns by the stored kind
  if F1 stores it; `DbObject.class` stays if `DbObject` stays public.
  Cost: S to M with F1.
* **(c) Replace or drop**, with F1's (c): only `String` and `byte[]` gets.
* **Recommendation: (b)**, with F1. Reason: the class-evolution table is
  the promise a harness needs; without it, "bug" is undefined.


## 6. F3. Index definition and the index functions

### 6.1. Promises

* `Database.indexBuilder(name)`: a unique name, not empty, without `/` or
  whitespace (and since S2-F24 without a lone surrogate);
  `IndexAlreadyExistsException`.
* `IndexBuilder`: `callSequence = 1*dir 1*(type 1*field) (createFast /
  start)`. Types: `long` (long fields), `double` (NaN unspecified; −0.0
  and 0.0 one value), `string` or `string/unicode` (code points),
  `string/<language>[/L1..Ln]` (ICU 50.1, 85 languages, level L1 by
  default); a build without ICU has `string/unicode` only, and an index of
  another kind "can be impossible to use" there. `dir()` several times:
  an index over several directories. `field()` several times: "one index
  that indexes multiple fields". `nestedField("a.b.c")`. A later `type()`
  starts a composite level.
* `createFast()`: "Creates this index immediately and makes it active
  without adding index entries for existing database objects. Only new
  objects (added/updated) will be indexed." `start()`: F5.
* `IndexManager`'s comment: the definitions survive a restart; "in the
  order of 10,000 indexes" are expected.
* **Unclear or missing**: what entry an object gets: none when a field is
  missing (the code), none or one when a `String` field is null (it
  throws: S2-F26); that several fields at a level give one entry for each
  combination, so an object can be in the index twice; an `int` field in a
  `long` index (indexed, as `float` in a `double` index); whether a
  directory's subdirectories are indexed (a build says yes, the writers
  no: S2-F16); a directory given twice (S2-F20); the size of an indexed
  value; a database opened without ICU (S2-F10).

### 6.2. How it is built

* **The definition** (`IndexManager.Index`): its name, directories,
  fields per level (`FieldRef`, dotted for nested), type strings and
  collators, state (creating, active, deleting), and an
  `IndexFunction`, `FieldIndexFunction`, which makes one entry for each
  combination of one field per level when every field of it exists with
  an accepted kind (`l` or `i` for `long`, `d` for `double`, `s` for
  `string`).
* **Stored** as a `DbObject` of `Data.Index` made by reflection, at
  `/#i/dii/-<name>`: `dirs`, `fields` (a level's fields joined by commas),
  `typeStrings`, `state`, `version` 1. Written by `addIndex`,
  `setIndexStateToActive` and `ensureDeletingState` with `Db.execute`
  directly, with a virtual write hash of each directory
  (`/#i/div/<dir>`, a hash only, nothing stored). Read at every start
  (`initFromDatabase`, through `usePrimary` on the internal directory) and
  at every `useIndex` (at the read's lookup time).
* **An entry** is a KV with an empty value and the key `/#i/di/d<name>/`,
  then each level's sort bytes, then `0x00`, the directory's number + 1
  and the object's name in that directory. A `long`: 8 bytes, big-endian,
  of the value + 2^63. A `double`: its bits made two's-complement, then as
  a `long`. A `string`: its UTF-8 bytes each + 2 and a final `0x00`, or
  ICU 50.1's sort key, which ends with `0x00`. The object's key is found
  again from the last `0x00` (`getObjectKey`).
* **Memory**: every definition is in two maps under one lock
  (`nameToIndex`, and `dirToActiveIndexes` for creating and active
  ones). The definition's state in memory is changed before its
  transaction (S2-F27, 015-23).
* **ICU**: `bergdb.icu50`, ICU4J 50.1's collator module repackaged in
  2013, 2.0 MB of the 3.4 MB jar, found by reflection
  (`OptionalIcuCollatorFactory`). One collator per index, shared by every
  writer and the build without a lock (S2-F1). Its sort keys are stored,
  so ICU's version is part of every such index's bytes (N9).
* **Size**: about 1,860 lines of code (`IndexBuilder`, the builder half of
  `IndexBuilderImp`, most of `IndexManager`, `Data`, `FieldRef`,
  `IndexFunction`, `FieldIndexFunction`, `IndexEntryBuilder`, seven
  collator classes, `src-icu`'s two, two exceptions), and ICU's 703
  classes.

### 6.3. Known faults

* S2-F1: an ICU collator is used by several threads at once and gives
  wrong sort bytes: lost and invented entries (15 of 6,000 objects in its
  probe); the stream's bytes depend on the threads' timing (P2).
* S2-F10: a database with an ICU index does not start without ICU.
* S2-F14: a composite level with two or more fields loses its commas in
  the stored definition ("x,y" stored as "xy" at level 1): after a
  restart the index is another, with lost and stale entries.
* S2-F15: `nestedField()` takes an empty part; every put of an object
  with the outer field to the index's directories then throws (with
  `-ea` an `AssertionError`, which since 019-10 fails the database: the
  path of N2, not probed for this case).
* S2-F20: a directory given twice returns each object twice.
* S2-F26 (with F4 and F5): a null indexed `String` field makes the put
  throw and the build fail; N1.
* Fixed: S2-F24 (2026-11-05): an index name with a lone surrogate.

### 6.4. Tests

* `PubTesterIndex` (59 tests, 1,703 lines), `PubTesterComposite` (24, 753),
  `PubTesterNestedFields` (4, 153), the `@Nano` tests of
  `FieldIndexFunction`, `IndexEntryBuilder` and `IndexManager.Tester`:
  long, double and string types, negatives, ±infinity, int and long mixed,
  composite levels with `eq` and `startAt`, two fields at level 0,
  collations `sv`, `sv/L3`, `pl`, nested fields, restarts.
* Not covered: two fields at a level above 0 across a restart (S2-F14),
  collators under threads (S2-F1), a start without ICU, null and NaN
  values, a directory twice, subdirectories, large indexed values.

### 6.5. Open questions of meaning

1. What is an index, as a function: an object to zero or more sort keys?
   Which kinds make an entry for each type (an `int` in `long`, a `float`
   in `double`), and which make none (a missing field; a null; NaN)?
2. Which objects: a directory's own, or also its subdirectories'? One
   directory or several?
3. One field per level, or several (one entry per combination)?
4. String order: code points only, or ICU's languages? If ICU stays, is
   its version part of the format (N9), and what does a database without
   it do with such an index?
5. Is `createFast()`'s meaning (only objects put after the creation) kept?
   It needs its own invariant (F4) and misses data silently.
6. Limits: the size of an indexed value (an entry's key holds it whole),
   entries per object, the number of indexes.
7. Are the definition's key and bytes and the entries' key layout part of
   the stream's format (018-01, section 2, "the reserved internal keys")?

### 6.6. Options

* **(a) Keep and fix**: freeze or lock the ICU collator (S2-F1, with
  S2's doubt D3 checked), keep an index without its collator unusable
  instead of refusing the start (S2-F10), the comma (S2-F14), check
  `nestedField`'s parts (S2-F15), refuse a directory twice (S2-F20), a null
  `String` gives no entry (S2-F26). Cost: S to M. The surface stays:
  multi-field levels, multi-directory indexes, 85 collations, `createFast`.
* **(b) Simplify.** One directory per index, its own objects only (as the
  writers do); one field per composite level, composite levels kept;
  nested fields kept, their parts checked; types `long`, `double`,
  `string` in code-point order, maybe `bytes`; no ICU (the jar shrinks to
  about 1.4 MB; an application that needs a language's order stores its
  own sort key in a field and indexes that); no `createFast()`; a missing
  or null field, or NaN, gives no entry; the definition stored in a small
  fixed form, not by reflection on `Data.Index`; and entries under a
  directory of the index's generation (its name and its creation's time),
  so that no index ever sees another's entries (F5). A format change of
  the reserved internal keys: Frans approves it (018-01, section 2, if it
  holds for 2026.4). Cost: M.
* **(c) Replace: index functions in code.** The application gives each
  index a function from a value's bytes to sort keys, with a version, at
  every start (`DatabaseBuilder`); BergDB stores the name, the version and
  the directory; a start with another version rebuilds. Works with any
  serializer (F1's c). New questions: a start without the function, a
  function that throws (a refusal), that is not deterministic (P2), that
  changes without a new version (silently wrong). Cost: M to L, a new API.
* **(d) Drop**: not open (Frans: "Yes. That is included.").
* **Recommendation: (b).** Reason: it removes the largest fault clusters
  (ICU's threads and start, the stored comma, multi-directory ids, the
  build's subdirectories) and keeps the definition as data in the stream,
  which a start uses without the application's code (P10).


## 7. F4. Index maintenance in transactions

### 7.1. Promises

* Implied by `IndexBuilder`: an index holds the objects of its
  directories, "added/updated", kept up to date by the writes.
* `IndexManager`'s closing note: a write reads a virtual key of its
  directory, so that a transaction runs again "in case an index is added
  while Connection.set(String, Object) is being executed";
  `deleteIndexInternal`: after the index is deleting "there should be no
  more index entries added".
* **Missing**: the invariant itself (question 7.5.1); that an object put
  in an indexed directory can conflict and run again, also in a `w()`;
  what a `String` at an object key does.

### 7.2. How it is built

* After the action (or at once for a `w()`), `RwEnvironmentImp.indexEntries`
  takes, for each object put or delete, the directory's creating and
  active indexes from the map, adds the directory's virtual hash and each
  index's info key to the read set, reads the previous value at the read
  time, deletes the entries of the previous object and puts those of the
  new one, in the same transaction (`indexOps`; a put of an entry stays
  over its delete, 015-40). `Db.execute` checks the read set (STM): a
  conflict runs the whole again after 10 to 640 ms.
* The read time is that of the first read; when the action read nothing,
  it is set by `indexEntries`' own read of the previous value, after the
  map was read, or never (no index: `Long.MAX_VALUE`, so the virtual hash
  never conflicts). That gap is 015-28, 015-43 and S2-F12's cause.
* `String` and `byte[]` puts touch no index; a delete of a key without a
  suffix does (it is an object op).
* Key replace (`${transactionTime}`, Core): an entry's key holds the
  object's name with the same transformation.
* **Size**: about 220 lines of code (`indexEntries`, `setIndexEntry`,
  `ObjectInfo`, `IndexSetter`, the virtual hashes).

### 7.3. Known faults

* 015-28: a write into a directory with no index, racing the index's
  creation, is never indexed (no read, so no conflict).
* 015-43 = S1-F4: the index set is read before the read time: a new index
  misses the object, a deleted one gets an entry after its deletion job.
* S2-F12: that entry is then found by a new index of the same name
  (invented data in another index). One cause with the two above; S1's
  fix (the read time taken before the map) is one fix for the three.
* 015-46 = S2-F3 (with F1): a `String` or `byte[]` over an object leaves
  its entries; a later object put or delete there throws.
* S2-F1 (F3): wrong sort bytes from writers' threads.
* S2-F26 (F3): a null indexed `String` makes the put throw; with `-ea`
  it fails the database since 019-10 (N2, probed).
* Fixed: 015-40 (2026-11-03), 015-41 (2026-11-05).

### 7.4. Tests

* `PubTesterIndex`: `testWithDeletesAndUpdates`, `testKvDelete`,
  `testCreateWhileWriteOps1` and `2`, `testKeyReplaceWithIndex`,
  `testNonObjects1` and `2`; `CreateIndexTester` (f-tests: a build while
  writes go on, a build over a restart).
* Not covered: the interleavings of 015-28, 015-43 and S2-F12 (S1's and
  S2's probes force them with hooks; none is a test of `main`); a
  differential check of entries against the objects at past times.

### 7.5. Open questions of meaning

1. The invariant: at every lookup time T at which an index is active, are
   its entries exactly the function of the objects of its directory at T?
   For an index made by `createFast()`, of the objects put since its
   creation? This is the reference model of H2 (section 15).
2. A write racing a creation, an activation or a deletion: run again, or
   taken by the build? (Today neither, in the gap.)
3. A put whose object the index cannot index (a null, a value too long):
   refused, or stored with no entry?
4. A `String` or `byte[]` at an object key in an indexed directory:
   refused, or a value with no entry (015-46)?
5. Is it promised that a `w()` of objects may run again after a conflict,
   with its sleeps, as an `rw()`?

### 7.6. Options

* **(a) Keep and fix**: the read time before the map (S1-F4's fix, one for
  015-28, 015-43 and S2-F12); a value that is not an object has no
  entries (015-46); a null gives no entry (S2-F26). Cost: S.
* **(b) Simplify with F3's (b)**: with entries per generation, an entry
  can never land in another index; the maintenance is "delete f(old), put
  f(new), at the read time, with the directory's index set read at that
  time". A scan may also check each object against its entry (F6), so
  that a stale entry gives no wrong object. Cost: S on top of (a).
* **(c) Replace**: the same, written as a layer over `Db`'s four data
  methods (P12). It nearly is one already; nothing to gain.
* **Recommendation: (a) and (b).** Reason: small, and it is the heart of
  "an index is a function of the data at a lookup time".


## 8. F5. Index builds and deletions: the jobs

### 8.1. Promises

* `IndexBuilder.start()`: a background job; the index is creating until
  the job is done and active; it cannot be used before; a stop continues
  it at the next start; a deletion before the end stops it, it writes
  nothing to a later index of the name, and its status has progress 100
  and a note that says so.
* `Database.deleteIndex(name)`: starts a job that deletes the index; a
  job that runs already is returned. `NoSuchIndexException`.
* `Job`: `getStatus()` (immutable), `join()` and `join(ms)` (an interrupt
  ends the wait, 005-46). `JobStatus`: progress −1, 0 to 99, 100
  "finished"; a note. `StartupInfo.getStartupJobs()`: the jobs a start
  resumed.
* docs/levels.md, section 3: an index job's thread fails the database on
  anything that ends its work; a refused transaction or an expired read
  is retried, not a failure (019-38).
* **Unclear or missing**: what "100" means after a stop, a failure or a
  deletion (015-61, S2-F11, 019-40 C5); a build that cannot finish (N1);
  when a deleted index's name is free; that `close()` does not wait for
  the jobs' threads (they end at their next step).

### 8.2. How it is built

* **A build** (`IndexBuilderImp.createInThread`): a daemon thread of the
  lowest priority, started by `start()` or by a start
  (`finishOngoingJobs`, inside `DatabaseImp.createAndStart`, before the
  start returns). Steps of an `rw()` on its own connection: a `getMany`
  of up to 25 objects of the directory after the last key, the info key
  of the index in the read set (a deletion makes the step run again and
  stop, 015-22), the entries put; after each step a sleep of half its
  time (at most a second, its comment says; the cap is not applied,
  N10). At the end of the last directory the state
  becomes active (unless deleting). The progress is kept in memory only:
  a start begins again at the first directory (entries are idempotent).
* **Errors** (019-10, 019-38): a stop or a failure ends the thread; a
  refusal or an expiry waits 10 to 640 ms and takes the step again, also
  one that will never pass (a step too large, or 005-02's ordinals); any
  other exception fails the database, also one that the user's data
  causes (N1).
* **A deletion** (`DatabaseImp.deleteIndexInternal`): the state set to
  deleting and stored (`ensureDeletingState`), a `sync()`, then a thread
  that deletes the entries in transactions of 100 (`Db.execute`, no read
  set), deletes the definition and syncs; one job per index (015-21). At
  a start, a deleting index's job is started again.
* **Status**: a build's `JobStatus` captures its progress but reads the
  count from the live state (015-39); a deletion's is 100 when its thread
  has ended, for whatever reason (015-61).
* **The Core**: the build reads at its step's time and writes in its
  step's transaction, like an application; reclaim and eviction see KVs.
* **Size**: about 800 lines of code (the job half of `IndexBuilderImp`,
  `IndexCreateState`, the deletion in `DatabaseImp`, the job methods of
  `IndexManager`, `Job`, `JobStatus`, `StartInfoImp`).

### 8.3. Known faults

* 015-23 = R3-F9: a refused deletion leaves the index active but no
  longer maintained, also after a restart.
* 015-29: `deleteIndex(Database.PRIMARY)` throws `Bug` and leaves the
  primary deleting: every `usePrimary` throws until a restart.
* 015-30: a build step reads past its directory, over all later
  non-objects (time only).
* 015-36 = R3-F11: an interrupted `deleteIndex` leaves the index deleting
  with no job until a retry or a restart.
* 015-37 = R3-F5: an interrupted retry of a build step ended the build.
  Fixed in effect by 019-38 (N6); the entry is open.
* 015-39 = R3-F7: a kept build status changes its note.
* 015-61 = R8-F6: a deletion that `stop()` ends early says "Done!
  Deleted"; 019-40, C5: also after a failure.
* S2-F11: a build's job says done when the database stopped; a resumed
  build of a deleted index says it created it.
* S2-F16: a build indexes the objects of subdirectories, which the
  writers never update: stale entries.
* S2-F26 and N1: a null indexed `String` stops a build for good; since
  019-10 it fails the database at every start.
* S2-F27: a refused creation leaves the index in memory: its name is
  taken, and writers write its entries, which a later index of the name
  finds.
* Fixed: 019-38 (2026-11-06): a refusal, an expiry or an interrupt in a
  job no longer fails the database. 015-20, 015-21, 015-22 (2026-11-03):
  filtered pages, a second deletion job, a build that wrote into a new
  index after a deletion.

### 8.4. Tests

* `PubTesterIndexJobs` (10 tests, 433 lines): a deletion before, in and
  after a build's step; an `Error`, an interrupt, an expiry and a refusal
  in a build and a deletion (019-38); a deletion twice.
  `PubTesterIndex`: `testCreateInThread1` and `2`, `testDeleteIndex1` and
  `2`, `testCreateDuringRestart`. f-tests `CreateIndexTester` (2) and
  `DeleteIndexTester` (1).
* Not covered: refusals of the metadata transactions (015-23, S2-F27), an
  interrupt of `deleteIndex`'s caller (015-36), statuses kept and read
  later (015-39), a stop during a deletion (015-61), a build over a value
  it cannot index (S2-F26, N1), subdirectories (S2-F16).

### 8.5. Open questions of meaning

1. What may a job do to the database? A proposal: only the environment
   and BergDB's bugs fail it (P7); the user's data never does: an object
   the index cannot index gets no entry, and a step that can never pass
   ends the build as failed, with the reason in its status.
2. What does an index read see while a build runs: `NoSuchIndexException`
   (today, with the message "No index named ... at the given lookup
   time")? And at a lookup time before the activation, after it?
3. A job's status: which states (working, done, stopped with the
   database, failed, deleted), each a snapshot; is `Job` needed, or a
   method that tells an index's state?
4. When is a deleted index's name free, and may anything of the old index
   reach a new one (S2-F12, S2-F27; R3-F1 and F2, fixed by 015-21, 22)?
5. Does a refused or interrupted metadata change leave memory as the
   stream is (015-23, 015-36, S2-F27)?
6. Should `close()` wait for the jobs' threads (harness 6.2 checks that
   no BergDB thread is left)?
7. A start resumes a build from its first directory: is a long build
   redone at every restart acceptable (P4)?

### 8.6. Options

* **(a) Keep and fix** each: store first, then the maps (015-23, S2-F27);
  refuse `PRIMARY` (015-29); the prefix check first (015-30); an internal
  sync that an interrupt does not end (015-36, R3-F11's fix); 015-37's
  entry closed (N6);
  a snapshot status (015-39); "stopped" apart from "done" (015-61, S2-F11,
  C5); the directory's own objects (S2-F16); no entry for a null (S2-F26).
  Cost: M.
* **(b) Simplify.** Entries per generation (F3's b). A deletion is one
  transaction that deletes the definition: the index is gone and its name
  free when `deleteIndex` returns, and no state "deleting" is seen; the
  old entries are garbage that an internal cleanup removes in steps,
  resumed at a start, with no `Job`. A build keeps a job, whose status is
  an immutable snapshot of three states (building with a count, active,
  failed with the reason); `getStartupJobs()` goes, or becomes a method
  that tells an index's state. A user's object never stops a build (the
  no-entry rule). Most of the eleven faults go with the state they live
  in. Cost: M.
* **(c) Replace: builds by the caller's thread.** Not proposed: a large
  directory's build takes long, and a stop must resume it.
* **(d) Drop builds**: an index only for an empty directory. Not proposed:
  a user cannot index data already stored.
* **Recommendation: (b).** Reason: the jobs' faults are in their states
  and their status texts, which (b) mostly removes; what stays has a
  simple reference (H3).


## 9. F6. Index reads

### 9.1. Promises

* `Connection.useIndex(name, type)`: `NoSuchIndexException` "if the index
  does not exist"; `setLookupTime` applies to it.
* `UseIndexBuilder`: `inclusive(false)` excludes "an exact match with the
  start value"; `backward()`; `nextLevel()`; `eq()` for a `String`, a
  `long`, a `double` at the current level; `startAt()`, "a suffix to
  prefixString" after `prefix()`; `prefix()` on a string level, after
  which no `prefix()`, `nextLevel()` or `eq()`; `objects()` and `kvs()`.
  Its comments sketch other designs (operators, `select`).
* **Unclear or missing**: that a scan reads its entries and objects at
  one lookup time; what it returns for an entry whose object changed
  (today the object, unchecked) or is gone (skipped); which call orders
  are valid (S2-F2, F13, F22); a `LookupTimeNotAvailableException` from
  the iterator when reclaim's cut overtakes a long scan; an object with
  two entries (multi-field levels) returned twice; the effect on the
  connection's `transactionInfo()` and frozen time (N3).

### 9.2. How it is built

* `UseIndexBuilderImp`'s constructor reads the definition at the
  connection's lookup time, through the connection's `GetData` (so it
  freezes a frozen time and changes `transactionInfo()`, N3), makes a new
  `Index` with new collators, and refuses one that is not active.
* `prepare()` makes the start key and the prefix from the index's
  directory, the `eq()` bytes, the `startAt()` bytes and the `prefix()`
  bytes; `inclusive` is turned into `plusOne()` of the start for a
  secondary index.
* The iterator reads pages of `Db.getMany` (100 entries, 50 MB or 1 s,
  P8) at the actual lookup time of the definition's read, and for each
  entry reads its object at the same time (`getBytesAtLookupTime`, the
  connection's `GetData` again); a missing object is skipped as stale;
  `KvToObjectImp` makes the result (F2).
* **Size**: about 870 lines of code (`UseIndexBuilder`, most of
  `UseIndexBuilderImp`, which F7 shares, `getActiveIndex`,
  `getObjectKey`, `Kv`).

### 9.3. Known faults

* S2-F2: `inclusive(false)` without `startAt()` gives an empty scan.
* S2-F13: `prefix()` on a secondary string index finds at most exact
  matches at the start of the index.
* S2-F22: `eq()` or `startAt()` on a later level, with no `eq()` on the
  levels before, applies to the first level.
* S2-F23: `hasNext()` says true and `next()` throws when the last entries
  are stale.
* N3 (section 12): `useIndex()` changes `transactionInfo()`.
* Fixed: 005-15 (`plusOne`'s carry, 2026-10-21), 015-20 (a filtered page
  taken for the end, 2026-11-03).

### 9.4. Tests

* `PubTesterIndex` (the scans: `testStartAt*`, `testEq*`, `testBackward*`,
  `testIterHistory`, `testLongs256`, `testStartKeyCarry`, collations),
  `PubTesterComposite` (`eq` and `startAt` on levels).
* Not covered: `inclusive(false)` alone, `prefix()` on a secondary index,
  a later level alone, stale last entries, a scan overtaken by a cut, the
  connection's state after a scan, every call order (the builder's state
  machine).

### 9.5. Open questions of meaning

1. The scan's meaning, as a reference: the entries of the index at one
   lookup time, in order, filtered by `eq()` on a prefix of the levels, a
   bound or a string prefix on the next level, in a direction; each
   object read at that time. Must each returned object still match its
   entry (a check that makes stale entries harmless)?
2. Which call sequences are valid; is each invalid one refused at the
   call?
3. Is an expiry in the middle of an iteration promised, as a
   `LookupTimeNotAvailableException` from `hasNext()` or `next()`?
4. Does a scan count as a read for `freezeLookupTime()` and for
   `transactionInfo()` (N3)?
5. An `rw()` cannot read an index or a directory (`RwEnvironment` has no
   scan, N8): is an atomic "insert unless the index has the value" needed?

### 9.6. Options

* **(a) Keep and fix**: S2-F2, F13 (code points; for ICU, L1 or a
  filter), F22, F23, N3. Cost: S to M.
* **(b) Simplify the builder**: `eq(values...)` for a prefix of the
  levels, then at most one of a range on the next level (`from`, `to`,
  each inclusive or not) or a string prefix, and `backward()`; each call
  checked at once; the iterator looks ahead and checks each object against
  its entry; a scan leaves `transactionInfo()` and the frozen time as a
  `get()` would, as decided. Cost: M (an API change; the tests rewritten).
* **(c) Replace with a byte range**: the user encodes the bounds. Smaller
  code, more user error. Not proposed.
* **Recommendation: (b).** Reason: three of the four faults are the
  builder's state; a smaller grammar is a smaller reference.


## 10. F7. The primary scan

### 10.1. Promises

* `Connection.usePrimary(type)`: "iterate objects according to the
  primary key"; `UsePrimaryBuilder`: `dir()` ("Sets the directory to
  iterate"; it must end with `/`), `inclusive()`, `backward()`,
  `startAt()`, `objects()`, `kvs()`. `byte[]` and `Object` give the
  database's own arrays (015-47).
* **Unclear or missing**: that `dir()` is needed (without it the scan
  returns the database's internal entries, S2-F17); that only the
  directory's own keys are listed, not its subdirectories; which values a
  type returns (`String.class` skips the `String`s and returns objects as
  text, S2-F25); that it is **the Pub API's only listing of keys**, also
  for a user of `String` and `byte[]` values only, the Core of 2026.3.

### 10.2. How it is built

* A wrapper of `UseIndexBuilderImp` with the index `PRIMARY` (a fixed
  in-memory definition, never stored): `dir()` sets the prefix to the
  directory's key and `-` (its files), `startAt()` appends a name; the
  iterator pages `Db.getMany` at `Db.lookupTime(wanted)`, and for a class
  other than `Object`, `byte[]` and, wrongly, `String`, skips the values
  that are not objects.
* **Size**: about 155 lines of its own (`UsePrimaryBuilder`,
  `UsePrimaryBuilderImp`, `PrimaryKeyCollator`) on F6's engine.

### 10.3. Known faults

* S2-F17: `startAt()` before `dir()` finds nothing; without `dir()` the
  scan returns internal entries (index entries, definitions).
* S2-F25: `usePrimary(String.class)` leaves out the `String` values and
  returns the objects' bytes as strings.
* 015-29 (F5): after `deleteIndex(PRIMARY)` every `usePrimary` throws.

### 10.4. Tests

* `PubTesterPrimary` (23 tests, 492 lines): forward, backward, exclusive,
  history, non-objects, mixed types, byte arrays, sort order, a
  subdirectory, the root, filtered pages. Also `PubTester`'s
  `testDirManyObjects*`, `BryanRepro` (`level2.sh`), `CcDbNightTest`,
  `PayTest`, and `IndexManager.initFromDatabase` at every start.
* Not covered: `String.class` among objects, the call order, the absence
  of `dir()`, an expiry; harness 6.7 (018-04) has no scan.

### 10.5. Open questions of meaning

1. Is the listing of a directory part of the Pub API that 2026.4 promises
   for `String` and `byte[]` values, not experimental?
2. Is `dir()` required, or does no `dir()` mean the user's keys only?
3. What each type returns: `String.class` every value as text, or the
   values that are not objects?
4. Are subdirectories listed (as keys, or not at all)?

### 10.6. Options

* **(a) Keep and fix**: S2-F17, S2-F25, 015-29. Cost: S.
* **(b) Simplify and promote**: a listing of a directory's keys and values
  at a lookup time (by this name or another), `dir` required, internal
  keys never, each type's values as decided, `startAt`, `backward`,
  `inclusive`; out of the experimental list; its promises added to harness
  6.7's reference (a sorted map of each key's versions by time). Cost: S
  to M.
* **(c) Drop**: the Pub API then cannot list keys at all. Not proposed.
* **Recommendation: (b).** Reason: small, needed by every user, and its
  reference already exists in 6.7.


## 11. F8. The rest: the API's boundary

What a user can reach that is in neither the Core nor D6's list:

* **`pubimp`'s public classes.** The jar has no `module-info`, so every
  public class and method is reachable: `get(key, DbObject.class)`
  returns a `pubimp` class (W1 marked `DbObject` and `DbArray`);
  `ConnectionImp.getDb()` and `DatabaseImp.getDb()` give the Core `Db`
  under a Pub database; `UsePrimaryBuilderImp.dirInternal()` scans
  internal directories; `IndexBuilderImp.bunchSize()`,
  `WTransaction.getTrans()`, `IndexManager`'s public methods.
* **`Kv.ikey()`**, public, "not intended for the Pub API user"; in
  `TransactionInfo`'s KVs (Core) it throws `UnsupportedOperationException`.
* **`Job` and `JobStatus`** (`pub.util`): used only by index jobs.
* **`DataFormatException`** (`pub`): thrown only by objects and indexes.
* **The jar**, release 2026.2's too: it holds `src-dev`'s classes
  (`bergdb.dev`, `bergdb.test`, `bergdb.demo`; `build.sh`'s `Main-Class`
  is `bergdb.dev.Run`) and ICU's (`bergdb.icu50`, 712 entries).
* **Key suffixes** (`.obj`, `.txt`): rules of F1 and F2 that a user meets
  through the Core's `String` and `byte[]` keys (N4).

Known faults: none registered; N5 (section 12) names the boundary.

Options: **(a)** leave it a convention; **(b)** say it and narrow it: the
Javadoc and README name the API (`bergdb.pub`, `bergdb.pub.util`, the Core
API's `Db`, and `DbObject` if kept, moved into `pub`); `Kv.ikey()` goes;
`pubimp`'s methods that only BergDB uses lose `public` where the packages
allow; a release jar without `src-dev`. Cost: S. **(c)** a `module-info`,
which only the module path enforces. **Recommendation: (b)**: a contract
needs a boundary, and (b) is cheap.


## 12. Findings of this inventory

Not registered; for the coordinator to register in 019 if Frans wants
them. The probe is `/Users/f/fl/bench/006-13/v1-probe/V1Probe.java`, run
on the clone's jar (`92844c2`), with and without `-ea`.

* **N1. A build over a null indexed `String` fails the database, at every
  start** (019-10 with S2-F26). Probe `build`: three objects in `/p/`, one
  with `name == null`, `indexBuilder("byName").type("string")
  .dir("/p/").field("name").start()`. The job stays "Working, processed 0
  entries" (−1), and the database fails with the
  `NullPointerException` (without `-ea`) or the `AssertionError` (with).
  Two restarts: each resumes the build (`getStartupJobs()` 1) and the
  database fails again within 0.5 s. The resumed build starts before
  `start()` returns, so the application can at best race it with
  `deleteIndex()`, and after the failure it cannot delete the index:
  through the Pub API the database cannot run again. The Core API still
  reads it. The same path holds for anything else an index function
  throws in a build that is not a `DbException`: S2's doubt D1 (a nested
  field that does not parse), S2-F15. Before 019-10 the build stopped
  silently, and the database went on. By 018-01's severities (its D1),
  class A, "a database that cannot run again", in experimental code;
  whether it is a 2026.3 matter is question 1 of section 14.
  Fixed by 019-42 (b) (2026-11-06): the build ends as failed and the
  database goes on, with and without `-ea`; a start takes it again.
* **N2. The user's data turns into an `Error` that fails the database in
  `rw()` and not outside it** (019-10 with S2-F6, F8, F26, probed; S2-F21
  and F15 by the same paths, not probed). Probes:
  a get of a null `Integer` into an `int` field throws `Bug`, and the
  database goes on; the same get in `rw()` fails it. A put of an object
  with a self-holding array throws `StackOverflowError`; in `w()` the
  database goes on, in `rw()` it fails. With `-ea`, a put of an object
  with a null indexed `String` (S2-F26) fails the database even in `w()`
  (the `AssertionError` is thrown inside `executeRw`); without `-ea` it
  is a `NullPointerException`, and the database goes on. 019-40's C4 asks
  for the words; the behaviour is not decided.
* **N3. `useIndex()` changes `transactionInfo()`**. Probe `txinfo`: after
  `get("/s/b")`, `transactionInfo()` has its put's KV and time; after
  `useIndex("byV", P.class)` alone, it has 0 KVs and another time (the
  definition's transaction); after a scan, the last object read. The
  Javadoc of `transactionInfo()` (Core) says "the transaction that wrote
  the last value retrieved with the get() method" (and counts `exists()`).
  The definition's read and the objects' reads use the connection's
  `GetData`. A `useIndex` as the first read after `freezeLookupTime()`
  freezes the time the same way (from the code).
* **N4. The kind of a value is not stored.** An object is a value whose
  key has no suffix (or `.obj`) and whose bytes start with `bergo`: a
  `byte[]` that starts so is an object to a build, to `get(Object.class)`
  and to a primary scan, and not to the writers. The rules (an object put
  at a key with a suffix is refused; `.txt` gives a `String` to
  `Object.class`) are in no Javadoc. With 015-46 and S2-F25.
* **N5. The API's boundary is a convention** (section 11).
* **N6. 015-37 is fixed in effect by 019-38.** Its scenario (R3-F5: an
  interrupt while a build step waits to run again) is
  `PubTesterIndexJobs.testInterruptInBuildIsNotAFailure`, which passes: the
  build ends done. To close after a check against R3-F5's probe.
* **N7. A build step refused for good is retried for ever** (019-38): a
  step of 25 objects whose indexed strings make it too large, or 005-02's
  end of ordinals, waits 640 ms and tries again, with "Working" as its
  status. From the code, not probed.
* **N8. An `rw()` cannot scan.** `RwEnvironment` has no index read and no
  listing: a uniqueness check by an index cannot be atomic with the
  write. A gap, not a fault.
* **N9. ICU's sort keys are in the stream.** An index of `string/sv`
  holds ICU 50.1's keys; another ICU version may give other keys for the
  same strings, so a change of ICU is a change of those indexes' bytes,
  and of the order their scans give.
* **N10. A build's pause after a step has no cap.**
  `IndexBuilderImp.sleepFiftyPercentOfDuration` says "never longer than 1
  second", but sets `ms` where it sleeps `msToSleep`: a step that took 20
  s (its conflicts' waits included) is followed by a pause of 10 s. Time
  only; from the code, not probed.

Checked and right, beyond S2's section 4: a `DbObject`'s fields are
sorted by name before they are written, so its bytes do not depend on
reflection's order; a scan reads its entries and its objects at one
lookup time.


## 13. Summary table

Sizes are non-blank lines of code and of tests (section 2), rounded; a
test figure in brackets is shared with the features named. The faults
are the open known ones mapped in sections 4 to 11, with this
inventory's findings (N); the second table lists them.

| Feature                 | Code  | Tests         | Faults | Recommendation                     |
|---|---|---|---|---|
| F1 Objects, format, put | 1,850 | (1,370 F1-F2) |      6 | Simplify: a closed list of types   |
| F2 Get into a class     |   640 | (1,370 F1-F2) |      6 | Simplify, with F1                  |
| F3 Definition, function | 1,860 | (2,610 F3-F6) |      7 | Simplify: no ICU, one field/level  |
| F4 Maintenance          |   220 | (2,610 F3-F6) |      5 | Fix the read time; generation dirs |
| F5 Builds and deletions |   800 |           700 |     15 | Simplify: deletion in one step     |
| F6 Index reads          |   870 | (2,610 F3-F6) |      5 | Simplify the scan builder          |
| F7 Primary scan         |   155 |           490 |      3 | Keep, fix, promote out of D6       |
| F8 Boundary             |     - |             - |      1 | State it and narrow it             |

| Feature | Open faults                                                                        |
|---|---|
| F1      | 015-46 (S2-F3); S2-F8, F9, F18, F19; N4                                            |
| F2      | S2-F4, F5, F6, F7, F21; N2                                                         |
| F3      | S2-F1, F10, F14, F15, F20, F26; N9                                                 |
| F4      | 015-28, 015-43, S2-F12 (one cause); 015-46 and S2-F26 (with F1, F3)                |
| F5      | 015-23, 29, 30, 36, 37 (N6), 39, 61; S2-F11, F16, F26, F27; 019-40 C5; N1, N7, N10 |
| F6      | S2-F2, F13, F22, F23; N3                                                           |
| F7      | S2-F17, F25; 015-29 (with F5)                                                      |
| F8      | N5                                                                                 |

F3's code has ICU's 703 classes (2.0 MB of the jar) on top. The tests
leave out `PubTester`'s 20 object tests and the night tests (about 360
lines). N8 is a gap, not a fault, and is in no row.


## 14. The order of decisions

1. **N1, now.** Since 019-10 an experimental feature can make a database
   fail at every start. Options: (a) fix S2-F26's cause in 2026.3 (a null
   indexed `String` gives no entry, as a missing field; a few lines and a
   test), and say in `releases/next.md` that a build that meets any other
   object it cannot index fails the database; (b) also make a build's
   unexpected exception end the build as failed, not the database (a
   change of 019-10's rule for this thread); (c) leave it a known issue of
   the experimental part. Recommended: (a) now, (b) in 2026.4 with F5's
   design. Frans decides whether it touches 2026.3's goal (018-01, D2).
2. **The shape of objects and indexes** (F1, F3). Shape 1: objects stay,
   narrowed to a closed list of types (F1 b, F2 b), and indexes are
   defined by data over their fields (F3 b). Shape 2: values are the
   application's bytes (F1 c), and indexes are functions in code, given
   at every start with a version (F3 c). Recommended: shape 1. Reasons:
   the theme names object serialization; a definition stored as data
   needs no code at a start; the reference model of an index is the same
   simple function in both, so shape 2 buys less code in BergDB at the
   price of a new API and new questions (a start without the function, a
   function that is not deterministic or changes without a new version).
3. **ICU** (F3): drop it, code-point order only (recommended), or keep it
   and fix S2-F1, F10, F13 and decide N9.
4. **The primary scan** (F7): promote it to the kept, non-experimental
   Pub API (recommended), with its type rules (question 10.5.3).
5. **What a job may do** (F5, question 8.5.1), and the job model: deletion
   in one transaction with entries per generation, a build's status as a
   snapshot (F5 b, recommended).
6. **The smaller choices**, each a line: `createFast()` (drop), several
   fields at a level (drop), several directories (drop), subdirectories
   (not indexed), nested fields (keep, checked), `put(Object)` and the
   field `key` (drop), `Object.class` gets (drop, or by a stored kind),
   final fields (refuse, or store), the kind of a value (N4: stored, or
   an indexed directory holds objects only), the scan builder's grammar
   (F6 b), `rw()` scans (N8: not in 2026.4?).
7. **The format**: are the object format and the index keys under
   018-01's rule that Frans approves format changes, and where is their
   spec written?
8. **The boundary** (F8 b).

Each decision is then written as the promise (the Javadoc, and a section
of docs/levels.md for the non-Core part, which has none today), before
the harnesses, as 018-01 did for 2026.3.


## 15. The first harness of each kept feature

Each against a simple reference in the test, as harness 6.7 (018-04):

* **H1. Objects round trip (F1, F2).** Generated classes over the table
  of types (nested, arrays to several dimensions, nulls, empty, the edges:
  MIN and MAX, NaN, −0.0, lone surrogates, depth 1,000); each value put
  and read back into its class equals it field by field, and everything
  outside the table is refused at the put with its field path. Then pairs
  of classes (a field added, removed, of another type): the read gives
  the table's answer. Reference: the type table and a plain field map.
  Checks also that no user class or data makes an `Error` or fails the
  database, in `w()` and `rw()` (N2).
* **H2. Indexes as a function of the data (F3, F4, F6).** Random puts and
  deletes of objects (and `String`s at object keys, as decided), index
  creations, deletions and new indexes of a used name, restarts, with
  reclaim on. After each step, and at random past lookup times, every
  scan of every active index (each `eq`, bound, prefix and direction)
  equals the reference: the sorted list of (f(object), key) over the
  objects at that time, computed by a second, simple implementation of
  the index function; an index not active at the time is refused. Then
  the races, forced by hooks as S1 and S2 did: a write at each point of a
  creation, an activation and a deletion (015-28, 015-43, S2-F12). The
  main harness of 2026.4.
* **H3. Jobs under faults (F5).** As harness 6.2 (018-03) for the jobs: a
  refusal, an expiry, an interrupt, a stop or an `Error` at every step of
  a build and of a deletion, and at their metadata transactions. After
  each run: the final state (active, failed, deleted) and the index's
  content equal H2's reference; each status kept stays the same; the
  database fails only on an injected `Error`; a restart finishes the
  work.
* **H4. The primary scan (F7).** An extension of harness 6.7's reference
  (each key's versions by time): every listing of a directory at a lookup
  time, with `startAt`, `backward` and `inclusive`, over `String`, `byte[]`
  and object values, equals the sorted keys of the reference. The
  cheapest of the four; it can come first.


## 16. Log

2026-11-06. Written by coord-1106's agent v1 (xhigh), read-only at
`92844c2`, with the probe of section 12 in the clone
`/Users/f/fl/bench/006-13/v1`. Nothing decided.
