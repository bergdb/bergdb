Notes for the next release
==========================

What the release notes of the next release after 2026.3 must say, collected
here as the changes are made, so that the release does not have to find them
again. The release folds them into its `releases/VERSION/readme.md`, as
[2026.3](2026.3/readme.md) has them under its changes, and
empties this file. A change of the stream's bytes, within the format,
names the StreamDigest configurations whose digests changed and the entry
that keeps its digests before and after (bergdb 018-01, section 2).

Emptied at release 2026.3 (2026-11-07), whose notes hold what was there.


### Pub API

* **`Time.utc` and `Time.resolve` refuse a null with
  `IllegalArgumentException`** (bergdb 021-01; 2026-11-07). `Time.utc(null)`
  and `Time.resolve(zone, null)` threw a `NullPointerException`, and
  `Time.resolve(zone, null, s)` (a null current time) too; each now throws
  `IllegalArgumentException`, as `resolve(zone, now, null)` and a null zone
  did.
* **A string with a lone surrogate inside an object is refused** (bergdb
  021-04; Frans, 2026-11-07, option 1) with `IllegalArgumentException` at
  the put, before anything is written, as keys (015-49) and String values
  (019-44) are: it was stored with `?` in its place, silently, and the
  object read back held other characters. It covers every string of an
  object: a field's value, an array's element, at any depth, and a field's
  name; the message names the field and an array element's index
  (`inner.names[3]`). `DbObject.toDbObject`, `DbObject.Builder` and
  `DbString` refuse it. A `char[]` field keeps any chars and reads back
  exactly; a `byte[]` keeps any bytes. The stream is unchanged: Java has
  only ever written well-formed UTF-8, and old `?`s read as before.
* **A stored value that is not a well-formed object is refused at a get
  with `ObjectCreationException`** (bergdb 021-07; 2026-11-07), from the
  object reader's `BadFormatException`, inside `rw()` and outside, and the
  database goes on; an index update that reads such a previous value
  throws `DataFormatException`. A nested object of size −1, which no
  writer writes, gave an `AssertionError` (with `-ea`), which failed the
  database inside `rw()`; a bad length, a bad field type byte or bytes
  that end inside a field gave a `NegativeArraySizeException`, an
  `IllegalArgumentException`, an `IndexOutOfBoundsException` or, for a
  length near 2^31, an `OutOfMemoryError`; and `Z` after an array's
  element ended the array silently. `DbObject.Builder`'s add methods
  refuse a null name or value with `IllegalArgumentException`:
  `addString` stored a null string, the others gave an `AssertionError`
  or a `NullPointerException`. Well-formed objects are read and written
  as before; the stream is unchanged.
* **An object nested deeper than the writer writes is refused** (bergdb
  021-08; 2026-11-07) as 021-07's faults are: more than 1,001 objects
  (`toDbObject`'s 1,000 and a null object below them), or more than 2,001
  objects and arrays counted alike, on a path from the top. Before, such
  bytes from another writer gave a `StackOverflowError`, or, since the
  reader copies each nested object, an `OutOfMemoryError` (a 2.2 MB value
  of 100,000 objects), each failing the database inside `rw()`.
  `DbObject.Builder`, and so a put of an object, refuses to build deeper
  with `IllegalArgumentException`: a chain of more than 2,000 arrays was
  stored. The stream is unchanged.
* **Objects are stored in format 2** (bergdb 020-08, steps 1 and 2; the
  format of 020-07, decided by Frans on 2026-11-08, 020-02, section 4). A
  stored object is the header byte 0x82 and the object: a table of its
  fields' ends, the fields in the order of their names' bytes, the values
  as Binson's. `DbObject` is a checked copy of the stored bytes, which a
  field's lookup searches by its name, and a nested object is a view on
  them. Names have 1 to 255 bytes, an object at most 32,767 fields, and
  objects and arrays nest at most 16 levels deep; `DbObject.Builder` and a
  put of an object refuse more with `IllegalArgumentException`, which
  names the path. One integer: a `byte`, `short`, `char`, `int` or `long`
  field is stored as one integer, in the fewest bytes; `getType` answers
  `l` for each, `has(name, INT)` and `getInt` take one within `int`'s
  range, and `DbInt` is gone. One NaN; -0.0 is kept. No stored null
  (020-04, option (c)): a null field is left out at a put, a null array
  element and `toDbObject(null)` are refused with
  `IllegalArgumentException` naming the element, `DbString` and
  `DbByteArray` refuse null, and `isNull()`, `Builder.buildNull()` and
  `DbObject.MAGIC` are gone. A get as `Object` gives a `byte[]` for bytes
  that start with 0x82 and fail the format's check. An object that 2026.3
  stored (format 1) is not read as an object: a get of it as `DbObject` or
  a class throws `ObjectCreationException` naming format 1. Format 2's
  reader and writer replace format 1's, and with them the limits of
  021-07 and 021-08 above.
* **`put(Object)` and the key field are gone** (bergdb 020-08, step 7;
  Frans, 2026-11-08, 19:21; 020-02, section 5.1b), with
  `MissingKeyFieldException`. `WBuilder` and `RwEnvironment` put at a key
  only, `put(key, object)`, as `Connection` does. A `DbObject` read at a
  key is the stored object exactly: no field `key` answers the database
  key, and a field named `key` is an ordinary field, at a put and at a
  get. `new DbObject(byte[], String)` is gone. A program that used
  `put(object)` or the key field does not compile, or keeps the key in a
  field of its own.
* **Objects are put and got as Data Objects, by 020-09's rules** (bergdb
  020-08, step 8; 020-09, Frans's principles of 2026-11-08 and the rules
  decided under his delegation of 22:17). A class that a put, a get or a
  scan takes, other than `DbObject`, a `String` and a `byte[]`, must be a
  Data Object: a public class with a public no-argument constructor,
  whose public, non-static, non-transient fields are of the types on
  020-09's closed list, and whose other instance fields are transient;
  checked once per class, with the classes it reaches. Else a put throws
  `IllegalArgumentException` and a get `ObjectCreationException`, checked
  first, also at a key without a value; a non-static member class is not
  one. The put is exact, by each field's declared type: a null field is
  left out, and a null array element, a value of another class than its
  field's, a cycle or a level past 16 is refused with
  `IllegalArgumentException` naming the path, before anything is written.
  The get is best effort (020-09, section 5): each field by its name, the
  stored value if it fits the field's type, else the nearest value
  (integers clamped), else the type's zero; it never throws for the data,
  and a constructor that throws gives an `ObjectCreationException` with it
  as the cause. `DbObject.toDbObject(Object)` and `toJavaObject(Class)`
  apply the same rules; `toJavaObject(Object, ClassToObject)` is gone.
* **The primary scan, `Connection.usePrimary()`, is no longer
  experimental** (bergdb 020-10, step P1; section 3.5). `dir()` is
  required and the first call: without it `objects()` and `kvs()` throw
  `IllegalStateException`, where they listed the database's internal keys
  too (S2-F17). `startAt()`, `inclusive()` and `backward()` come after
  `dir()`, at most once each, and each call is checked at once: `startAt()`
  refuses a null or empty name, one with '/' or a lone surrogate. After
  `objects()` or `kvs()` the builder is spent; both may be called again,
  and each iterator lists from the beginning at the lookup time that
  `usePrimary()` took, as a get resolves it; that is a read for
  `freezeLookupTime()`, and `transactionInfo()` is left as it was. A
  listing has its directory's own keys only, not its subdirectories'.
  Each type lists the values of its kind, as a get gives them: `byte[]`
  and `Object` every value, `String` the values that are not objects (it
  gave an object's bytes as text and left out the Strings, S2-F25),
  `DbObject` and a class the objects; a value that a class cannot be made
  from throws `ObjectCreationException` from `next()`, and the iterator
  goes on. A program that listed without `dir()` must call it.
* **A directory starts with '/' and has no "//"** (bergdb 021-09):
  `IndexBuilder.dir()` and `UsePrimaryBuilder.dir()` refuse "p/", "a/b/",
  "//" and "/p//" with `IllegalArgumentException`; they were taken, as
  directories that no key of the user's is in.


### Core API

* **The Core's String puts refuse a lone surrogate** (bergdb 021-05;
  2026-11-07) with `IllegalArgumentException`, as the Pub API does:
  `Trans.Builder.put(String, String)`, in its key and its value, and
  `Keys.toBytes(String)`, and so every Core call that takes a String key.
  They wrote `?` in its place, so that two keys were one. The check scans
  a key's chars only when its UTF-8 bytes hold a `?`.
* **A bkey that is not the bkey of well-formed UTF-8 has no ikey**
  (bergdb 021-06; decided 2026-11-08 under Frans's delegation).
  `Keys.bkey2ikey` and `Keys.toString(long[])` throw
  `IllegalArgumentException` for a bkey with the byte 0 or 0x31 ('/' + 2),
  or whose bytes, each 1 as '/' and every other less 2, are not well-formed
  UTF-8 (RFC 3629, the new `StringUtil.isWellFormedUtf8`); the new
  `Keys.bkey2ikeyOrNull` returns null for it. They decoded such bytes with
  U+FFFD in place of each ill-formed sequence, so that two bkeys gave one
  ikey, whose bkey was another (021-04's CK1 and CK2). Such a key, written
  with the Core API, is reached by its bkey only; `Connection.usePrimary()`
  leaves it out, and a key whose name in its directory has a '/';
  `Keys.toDisplayString` shows it, for messages only, as the printers of
  key nodes do. The rule is in the Core's `key-encoding.md`, "Conversion
  bkey --> ikey".


### Format

* **Stored objects and the index definitions are in format 2** (bergdb
  020-08, step 2; see the Pub API): the bytes of every object
  that the Pub layer stores change, and so do those of an index's
  definition under `/#i/dii/`, which today's index code stores as an
  object. The Core's records and the stream's format are unchanged.
  StreamDigest's digests are unchanged: its workloads use the Core API and
  put no object.


### Build and tools

* **A release jar without the development classes** (bergdb 020-10, step
  B1): `java/build.sh` makes `build/bergdb-release.jar` beside
  `build/bergdb.jar` (unchanged, the jar of the tests and scripts): the
  classes and resources of `src` only, without `src-dev`'s (the packages
  `bergdb`, `bergdb.dev`, `bergdb.test`, `bergdb.demo` and `frans`), and
  no `Main-Class`; until ICU goes, its classes are in both jars. The build
  fails unless its entries are `bergdb.jar`'s without `src-dev`'s, `jdeps`
  finds no class that it uses outside it and the JDK, and a program
  compiled and run with it alone on the class path
  (`java/stress/release-jar/ReleaseDemo.java`) works. The release ships it.


### Internal

* **The first parts of 2026.4's user indexes, used by nothing yet**
  (bergdb 020-10, steps I0 and H2's first part): the index keys and their
  encodings (`IndexKeys`), the definition and the index function
  (`IndexDefinition`), and harness H2's reference and generators
  (`IndexReference`, `IndexHarness`), with their tests. No change that a
  user sees.


### Documentation

* **BergDB's rule for strings is stated once, in the Pub API's Javadoc**
  (bergdb 021-04; 2026-11-07): every string BergDB stores, a key, a String
  value, each string in an object and an index name, is a sequence of
  Unicode scalar values stored as well-formed UTF-8 (RFC 3629), in every
  language; a writer refuses a string it cannot store so (in Java, a
  String with a lone surrogate), and a reader may rely on it. The package
  `bergdb.pub`, section "Strings", holds it in full, with why and what to
  do with data that is not text (a `byte[]`, or a `char[]` in an object);
  the overview, `Connection`, `WBuilder.put` and `RwEnvironment.put` link
  to it, and the Core's `key-encoding.md` states it for keys.
* **The Pub API's Javadoc says what is, not how it was** (bergdb 021-01;
  2026-11-07). The sentences on how a method or an exception behaved before
  a change, and their dates, are gone from `Database`, `DatabaseBuilder`,
  `CryptoKey`, `DbException`, `DbFailedException`, `DatabaseMissingException`,
  `DatabaseNotCreatedException` and `SyncLevel`; the release notes keep the
  history. `DataFormatException` says that it belongs to the object code
  and the user indexes, experimental in 2026.3 (bergdb 018-01, D6), and
  where it is thrown. `Time.utc` and both `Time.resolve` document
  `BadFormatException` for a bad time string and `IllegalArgumentException`
  for a null argument.
* **A start's heap** (bergdb 019-45): a start needs about twice the
  startup distance of heap above what the running database needs,
  whatever the cache budget (docs/levels.md, section 7); W7's 600 MB heap
  at a 200 MB startup distance was too small for a start.
