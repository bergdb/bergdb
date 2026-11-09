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


### Platforms

* **BergDB runs on Android** (bergdb 006-18-03; Frans, 2026-11-09: "Is
  this an easy fix we can get into 2026.4, let's fix it."): the Core from
  API level 33 (Android 13), objects (Data Objects and `DbObject`) from API
  level 34 (Android 14); checked on an emulator, not yet on a phone. Two
  changes made it run, and change nothing on a JVM:
  * `BufferedStream`'s wait statistics (005-46) took the JVM's uptime from
    `java.lang.management`, which Android lacks, at the first wait for
    room in the write buffer, and threw `NoClassDefFoundError` out of
    `Db.execute`. They take it from there where it exists, and elsewhere
    the time since their class was initialized.
  * Data Objects' checks V5 and V6 (020-09) called
    `ClassLoader.getPlatformClassLoader()` and `Class.getModule()`, which
    no Android level has, and refused every class. V6 now checks modules
    only where Java has them, and V5 takes Android's boot class loader as
    the platform's.

  The jar is dexed by d8, which desugars what it needs. R8 needs
  `-dontwarn` for `java.lang.management.**`, `javax.management.**`,
  `com.sun.management.**`, `java.lang.module.**`, `java.lang.Module` and
  `java.lang.ModuleLayer`, and must keep the fields that `findVarHandle`
  finds by name: `bergdb.dag.Handle.state`, `bergdb.dag.TopNode.rootPointer`
  and `rootPointerPos` (006-18-03, section 6). An app opens a database in
  an absolute directory, off the main thread, and syncs before it goes to
  the background. The Core's default cache budget, 200 MB
  (`DbBuilder.cacheSizeIndicator()`), is above a typical Android heap,
  192 MB (an app's is 192 to 512 MB), and a read of a large database then
  fails with `OutOfMemoryError`: an application of the Core sets a smaller
  one, such as 50 MB, which the check's did; each database also holds its
  10 MB write buffer. The Pub API's default, a fifth of the heap
  (`DatabaseBuilder.cacheSizeInMb()`), fits.
* **A known difference on Android: ill-formed UTF-8 read as a String**
  (020-09, section 5.6). The bytes are decoded by the platform's UTF-8
  decoder, and Android's can put more U+FFFD than Java's: `ed a0 80` reads
  as three U+FFFD where Java gives one (020-09's case G88). Well-formed
  UTF-8, which is all that Java writes, reads the same.


### Pub API

* **Encryption is removed from the API** (bergdb 020-28; Frans,
  2026-11-09, 16:12). `DatabaseBuilder.cryptoKey()`, `bergdb.pub.CryptoKey`
  and `bergdb.pub.util.BadCryptoKey` are gone. A new user's password vault
  (020-24-07) found that the encryption of 2026.3 and before was not safe:
  its keystream depended only on the key and the position in the stream,
  so two databases with one key, a copy of a database written on beside
  it, and a database written on after a crash of the operating system or
  a power loss cut its tail reused keystream, and one who saw both
  versions of the files learned the data (U7-1); and it had no integrity:
  one who knew a part of the data could change a value, with a checksum
  that matched, and the database read it without an error (U7-3). A safe
  design changes the stream's format; it is item 017-10, for a later
  release. Instead: to keep the data secret on disk, use full-disk
  encryption (FileVault on macOS, LUKS on Linux, BitLocker on Windows), or
  encrypt the values in the application before it puts them. A database
  that an earlier release encrypted is refused, and the start writes
  nothing: with its `created.txt`, which names the key, `start()` throws a
  `VersioningStreamException` that says so; without it, a
  `StreamFormatException`, "Invalid magic bytes in stream: the stream is
  not a BergDB stream, or it is damaged; or an earlier release of BergDB,
  2026.3 or before, encrypted it, and this release cannot read it: it has
  no encryption". To move such a database to 2026.4, export it with 2026.3
  first: start it with 2026.3 and its key, copy its data to a new database
  that 2026.3 creates without a key, and start that one with 2026.4; the
  history is not copied. A start refused for the magic bytes, of a stream
  that is not a BergDB stream or is damaged where the start reads first,
  throws that `StreamFormatException` where it threw `BadCryptoKey`. The
  stream's format is unchanged, and `created.txt` keeps its line "crypto
  key: none (not encrypted)". The encryption's code, `SalsaStream` and the
  key, stays inside BergDB with its tests, not API, for that later design,
  with the fixes made to it for 2026.4 before the removal: `getKeyData()`
  gives a copy (020-20, N1), `NULL` round-trips and `parse()` takes exactly
  three parts (020-21, 020-25, C1), one write and one force per flush in
  place of up to 50 (020-24-07, U7-2), a builder of `memory()` restarts on
  its closed stream (U7-5), and the message with the right key on a
  damaged stream (U7-7).
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
  database goes on; such a value has no entry in an index, so a put over
  it and a delete of it work (`IndexBuilder`, rule 1). A nested object of
  size −1, which no writer writes, gave an `AssertionError` (with `-ea`),
  which failed the
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
  021-08; 2026-11-07); format 2 then replaced these limits by its 16 levels
  of objects and arrays (020-08's entry, below). It was refused as 021-07's
  faults are: more than 1,001 objects (`toDbObject`'s 1,000 and a null
  object below them), or more than 2,001
  objects and arrays counted alike, on a path from the top. Before, such
  bytes from another writer gave a `StackOverflowError`, or, since the
  reader copies each nested object, an `OutOfMemoryError` (a 2.2 MB value
  of 100,000 objects), each failing the database inside `rw()`.
  `DbObject.Builder`, and so a put of an object, refuses to build deeper
  with `IllegalArgumentException`: a chain of more than 2,000 arrays was
  stored. The stream is unchanged.
* **`DbObject`, the stored object, is API** (bergdb 020-10, step B3): it
  moved from `bergdb.pubimp` to `bergdb.pub`, with `DbObject.Builder`,
  `DbArray`, `DbValue` and the value classes `DbBoolean`, `DbLong`,
  `DbDouble`, `DbString` and `DbByteArray`; change the imports: a class
  compiled against 2026.3 that uses `bergdb.pubimp.DbObject` or one of these
  fails with `NoClassDefFoundError` until it is compiled again. Their
  Javadoc says what a program may rely on: the model of 020-07, no stored
  null, one byte string per object (`getBytes()` compares objects), the
  lookups, which give null, 0 or false for an absent field or one of
  another kind (`has(name, type)` tells them apart), and immutability.
  `DbObject` is immutable: `getBytes()` returns a copy, as
  `DbByteArray.getByteArray()` now does, and a put of a `DbObject` stores
  a copy and checks its bytes (`IllegalArgumentException` if they break a
  rule). `DbObject.Builder` and `DbArray.Builder` are final. The getters
  and `has()` that take `String[]` name parts refuse a null array, an empty
  one or a null part with `IllegalArgumentException` (B3's review).
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
  that start with 0x82 and fail the format's check. Objects that 2026.3
  stored (format 1) are refused (the next entry). Format 2's reader and
  writer replace format 1's, and with them the limits of 021-07 and 021-08
  above.
* **Objects and index definitions of 2026.3 and before are refused**
  (bergdb 020-08, step 3; 020-02, section 4.11: an older database is not
  read). A value that 2026.3's writer wrote as an object (format 1:
  `bergo`, the version 1 and its fields' table, recognised by the whole
  structure) at an object key is refused wherever it is read as an
  object, with a message that names format 1: a get as `Object`,
  `DbObject` or a class throws
  `ObjectCreationException`, and so does `next()` of a primary scan that
  lists it as an object; an index build over it ends failed, naming the
  key, and the database goes on. It has no index entry, so a scan of an
  index leaves out a key where a write through the Core put one, whatever
  the scan's type (bergdb 020-23, Z2; 2026-11-09: since 020-08's step 3, in
  this release's development, a scan as `byte[]` returned its bytes as a
  match of a query that they do not hold, and one as an object threw
  `ObjectCreationException`, against 020-22's floor). Such an object at a
  key can be overwritten or deleted, in an indexed directory too; a
  `byte[]` put of one there throws `DataFormatException`. A start of
  a database that holds an index definition of format 1 throws
  `VersioningStreamException`, which says to make the database again, and
  closes it. A `String` value that only begins with `bergo` and the byte 1
  is no longer taken for such an object: it was (a get as `Object` threw,
  and in an indexed directory its put was refused). A `String` put into an
  indexed directory is never refused as one; but a get as `Object`, and an
  index's build, which read the stored bytes alone, take a `String` whose
  bytes are a whole object of format 1 for one. The guess left: a `byte[]`
  that passes format 2's full check is an object, and one whose bytes are a
  whole object of format 1 is refused as one (`Connection.get`'s Javadoc).
* **A String value too large to store is refused at its put** (bergdb
  020-08, with the fix of format 1's recognition and its review): a
  `String` value of more than 2^31 - 9 bytes of UTF-8, or a `String` field
  above a stored value's limit, throws `IllegalArgumentException` before
  anything is written, where its encoding met an `OutOfMemoryError`, which
  failed the database inside `rw()`; and a `String` value or field whose
  UTF-8 fits a stored value no longer throws `OutOfMemoryError` in its
  encoding, whatever its size.
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
  (integers clamped; a double into an integer field cut toward zero, as
  Java's `(long) x`, then clamped: 12.7 is 12, NaN 0), else the type's
  zero; it never throws for the data,
  and a constructor that throws gives an `ObjectCreationException` with it
  as the cause. `DbObject.toDbObject(Object)` and `toJavaObject(Class)`
  apply the same rules; `toJavaObject(Object, ClassToObject)` is gone. A
  field's class is checked with each of its superclasses below `Object`,
  and a field of a type variable is refused; a primary scan checks its
  class first, also over a directory without an object.
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
  `DbObject` and a class the objects; an object that cannot be made into
  the class (one of format 1, or a constructor that throws) throws
  `ObjectCreationException` from `next()`, and the iterator goes on. A
  program that listed without `dir()` must call it.
* **A directory starts with '/' and has no "//"** (bergdb 021-09):
  `IndexBuilder.dir()` and `UsePrimaryBuilder.dir()` refuse "p/", "a/b/",
  "//" and "/p//" with `IllegalArgumentException`; they were taken, as
  directories that no key of the user's is in.
* **A '.' in a directory's name no longer gives its keys a suffix**
  (bergdb 021-10, with 020-08's step 3): the suffix is the part after the
  last '.' of the key's last part, so `/v1.2/k` is an object key, `/d/.h`
  has the suffix `h` and `/d/x.` none. The
  whole key's last '.' gave every key under `/v1.2/` the suffix `2/k`, and
  an object put there was refused.
* **A String value that is not well-formed UTF-8 is refused at a get**
  (bergdb 021-06, its second half): a get as `String`, or as `Object` at a
  `.txt` key, throws `DataFormatException` for such a stored value, which
  it read with U+FFFD in place of each ill-formed sequence; the primary
  scan as `String` throws it from `next()` and goes on. The Pub API writes
  only well-formed UTF-8 (021-04): such a value comes from the Core API or
  another writer.
* **Every write keeps the user indexes** (bergdb 020-10, step I1; F4): a
  put or a delete at an object key, of any value, deletes the old value's
  entry and puts the new one's, so a `String` or `byte[]` put over an
  object removes its entry, where it removed nothing, and an object put
  over a `String` no longer throws (015-46). A write fixes its read time
  first and reads its directory's indexes after it, under the index
  manager's lock, so that a creation, an activation or a deletion that
  races with it is seen, or makes it run again (015-28, 015-43). The cost:
  every put or delete at a key without a suffix, of any value, now takes
  that lock and a read time, also where no index is, and a `w()` with such
  a key may run again after a conflict, as an `rw()` does (020-08, step 4,
  measures it).
* **User indexes on a new layout, with jobs** (bergdb 020-10, step I2; F3
  and F5; Frans, 2026-11-08, 22:08). `IndexBuilder`: `dir()` once and
  first, then for each of 1 to 8 levels `type()` and `field()` or
  `nestedField()`, each call checked at once. The types are `long`,
  `double`, `string`, in code-point order, and the new `bytes`, in
  unsigned byte order, for an application's own collation key;
  `string/unicode` and `string/LANG` went with ICU. A value has one entry
  or none: none for an absent field, a value of another kind (no kind is
  converted), NaN, or levels of more than 4,096 bytes. `createFast()` is
  gone: `start()` returns the build's `Job`, and `start().join()` waits.
  A build runs in the background; its status is a snapshot, BUILDING with
  a count, ACTIVE, or FAILED with a reason (`JobStatus.state()`, `count()`,
  `reason()` and `note()`; `progress()` is gone); a stop leaves it
  BUILDING, and the next start takes it again. `Database.deleteIndex(name)`
  is one transaction and returns nothing: the name is free when it
  returns, and a cleanup removes the old entries in the background, also
  after a restart. `Database.indexJob(name)` gives an index's job, and
  `StartupInfo.getStartupJobs()` is gone. "primary" is a name like any
  other. An index on a directory has its own values only, not its
  subdirectories'. A `join()` from any thread waits for the build's end; a
  build ends also while writers write its directory hard (each step tries
  again, last under the index manager's lock); an `Error` in a creation,
  an activation or a deletion fails the database; and once a definition's
  change has committed, the database's memory has it too, whatever is
  thrown, so memory and stream never disagree (the reviews of I1, I2 and
  harness H3). A build reads its directory up to the last key it had when
  the build began, as the writers keep the index for the keys put after it,
  so a build ends also while writers append to the directory; a step reads
  at most 25 values or about 1 MB of them, and a write of a key with a
  suffix does not make it run again, so a build holds up no write at an
  object key for long; and the cleanup of a deleted index takes a time
  linear in its entries (bergdb 020-18, F1 and F3 to F5; 2026-11-09).
* **`Job.join()` throws when the build failed** (bergdb 020-10, section
  3.2; Frans, 2026-11-09): `join()` and `join(millis)` of a build that
  ended FAILED throw the new `bergdb.pub.util.IndexBuildException`,
  unchecked, at every call, also on the job of `Database.indexJob(name)`,
  as `Future.get()` throws for a task that failed. Its `getStatus()` is
  the FAILED status, with the reason as before, and its cause the exception
  that failed the build: a `DataFormatException` for data that the build
  cannot take, such as an object of format 1, another `RuntimeException`
  for a bug, none when the index was deleted during its build, whose note
  says so and no longer that the next start takes the build again (bergdb
  020-19, F1; 020-18, F2). Before, they returned the status, and
  `start().join()`, the natural call, passed a failed build silently. They
  return as before otherwise: ACTIVE, or BUILDING after a stop, a time-out
  or an interrupt; `Job.getStatus()` never throws. `IndexBuildException` is
  not a `DbException`: a failed build is neither a refusal nor a failure of
  the database, which goes on.
* **The scan of a user index** (bergdb 020-10, step I3; F6): with
  `UseIndexBuilder`, `eq()` on levels 1 to k, then `from()` and `to()`,
  each inclusive or not, or `prefix()` on level k + 1, and `backward()`,
  then `objects()` or `kvs()`; each call is checked at once
  (`IllegalStateException` for a call out of that order,
  `IllegalArgumentException` for a value of another type than its level's,
  a null, NaN or a lone surrogate); `inclusive()`, `nextLevel()` and
  `startAt()` are gone. A scan reads at the connection's lookup time,
  fixes a frozen time as a get does, leaves `transactionInfo()` as it was,
  and gives only the values that their entries still match: `hasNext()`
  never says true before a `next()` that throws `NoSuchElementException`;
  a conversion that throws, throws from `next()`. `Database.PRIMARY` is
  gone.
* **`Kv.ikey()` is gone, and `bergdb.pubimp` is narrowed** (bergdb 020-10,
  step B2; section 7): `Kv` has `key()` and `value()`; `ikey()` was "not
  intended for the Pub API user", no caller used it, and the Kvs of
  `transactionInfo()` threw `UnsupportedOperationException` from it. The
  classes of `bergdb.pubimp` that nothing outside it uses are
  package-private, among them `ConnectionImp`, `IndexManager`,
  `IndexBuilderImp`, `UseIndexBuilderImp`, `UsePrimaryBuilderImp`,
  `RwEnvironmentImp`, `WBuilderImp`, `WTransaction` and `Entries`; of the
  public ones, the methods that BergDB's tests and tools use say "Internal,
  not API". So the classes behind the API's interfaces (`ConnectionImp`,
  `WBuilderImp`, `WTransaction`, `RwTransaction`, `RwEnvironmentImp`,
  `IndexBuilderImp`, `UseIndexBuilderImp`, `UsePrimaryBuilderImp` and
  `StartInfoImp`) are package-private: a call by reflection through an
  object's class (`obj.getClass().getMethod(...).invoke(...)`, as a
  dynamic language without type hints or a bean tool may make) throws
  `IllegalAccessException`, where 2026.3 allowed it; call through the
  `bergdb.pub` interfaces, whose `Method` objects work. The API is
  `bergdb.pub`, with `DbObject` since step B3, `bergdb.pub.util` and the
  Core's `Db`.
* **A directory that cannot be listed is refused with `StreamIoException`**
  (bergdb 020-20; 2026-11-09), as one that cannot be opened: no permission
  to read it, or an I/O error in its listing. `start()` threw a
  `DatabaseMissingException` for such a directory with `created.txt`, whose
  message said to restore or remove the database's files, and a
  `NullPointerException` for one without it. The cause is the
  `IOException`. The Core's `FileStream` throws that `IOException` from its
  constructor, where it threw the `NullPointerException`.
* **An `rw()` reads one state, also after a get whose conversion threw**
  (bergdb 020-13, bug 1; 2026-11-09): an action that caught the exception of
  its first get's conversion, such as the `DataFormatException` of a `String`
  get of bytes that are not well-formed UTF-8, read its next keys at the
  latest time and was checked against that time, so it could commit having
  read two states of one key, where `RwEnvironment.get` promises one, the
  latest as of the action's first read. Now the first read fixes the read
  time before the value is converted. In 2026.3 and before too, with the
  conversions that threw there.
* **Key replace in an object key's directory is refused** (bergdb 020-14,
  X1; 020-13, bug 3; 2026-11-09): with `setEnableKeyReplace(true)`, a put
  at an object key (no suffix, or `.obj`) whose directory holds
  `${transactionTime}` throws `IllegalArgumentException` at the call,
  before anything is written; in its name it is replaced as before. The
  index maintenance took the key as written: an index of the directory as
  written lost the entry of an object that the put did not change, and an
  index of the directory the put landed in missed the new object, also
  after a restart.
  A put with `${transactionTime}` in its name no longer deletes the index
  entries of the object at the key as written, which it took for the
  previous value. A key with another suffix is replaced anywhere, as before.
* **A Data Object class whose static initializer throws an `Error` is
  refused at a get** (bergdb 020-14, X2; 020-13, bug 2; 2026-11-09) with
  `ObjectCreationException`, the `Error` as its cause, as for an
  `Exception` there (`ExceptionInInitializerError`); a
  `VirtualMachineError` passes. Java does not wrap an `Error` of a static
  initializer, such as an `AssertionError`: it escaped the get, and inside
  `rw()` failed the database.
* **A Data Object's stored fields must be declared in exported packages**
  (bergdb 020-14, X3; 2026-11-09): a class that inherits a public field
  from a public class of a package that its module does not export to
  BergDB is not a Data Object, refused at a put with
  `IllegalArgumentException` and at a get with `ObjectCreationException`,
  naming the field and the package. The check took it, and the put and a
  get of a stored object with the field threw at the field's access. A
  class whose field's generic type names a class that is not there is
  refused so too: a `TypeNotPresentException` escaped the put and the get.
* **A time string is parsed strictly** (bergdb 020-21, 1; Frans, 2026-11-09,
  020-13 and 020-19's Q1): `Time.utc` and both `Time.resolve` refuse with
  `BadFormatException` a field outside its range, a month outside 01 to
  12, a day outside its month, an hour above 23, a minute or a second above
  59, which a lenient calendar rolled over ("2013-13-01" was 2014-01-01,
  "2013-02-30" 2013-03-02, "25:00" the next day, "00:00:75" 00:01:15); and
  a string that breaks the format in another way, which Java's number
  parsers took: seconds as "1e1" or with a space after them, a minus time's
  number as "1d", "NaN" or "0x1p3", a sign in a field. Each field is ASCII
  digits of its length, a minus time's number digits with an optional
  fraction. A time outside `Time`'s range, before 1970 or after 2198-05-04,
  is a `BadFormatException` too, as a minus time before 1970 was; it was an
  `IllegalArgumentException` for an absolute time or a time of day. A
  fraction of a second beyond 100 ns is rounded half up on its digits, not
  through a double; the strings of the format give the times they gave. A
  minus time's duration is its number times its unit, exactly, rounded
  half up to 100 ns (bergdb 020-23, Y1): it went through a double and was
  truncated, so "-0.0000021 s" was 20 units, not 21, a large number could
  be a unit off, and `Time.MAX` minus its own seconds was refused as before
  1970. A year and a month take a time of day, as the grammar says, on the
  month's first day: "2020-06 12:34" is 2020-06-01 12:34 (bergdb 020-23,
  Y2); it was refused.
* **`WBuilder.execute()` spends the builder** (bergdb 020-21, 2; Frans,
  2026-11-09, 020-19's Q2): a second `execute()`, and a `put()` or a
  `delete()` after `execute()`, throw `IllegalStateException` and write
  nothing, also when `execute()` threw, as `IndexBuilder` is spent after
  `start()`; only an `execute()` refused because another thread is in a
  call of the connection (021-22) leaves the builder unspent. Before, a
  second `execute()` ran the same writes again as a new transaction, and a
  `put()` after it added to them. Get a new builder with `Connection.w()`
  for each transaction.
* **`Database.setRetainDuration(null)` throws `IllegalArgumentException`**
  (bergdb 020-21, 3; Frans, 2026-11-09, 020-13), as every null argument of
  the API does; it threw a `NullPointerException`.
* **`Connection.useIndex(name, String.class)` is refused at the call**
  (bergdb 020-21, 3; 020-13) with `IllegalArgumentException`, whatever the
  data and whether the index exists: an index's values are objects, which a
  get does not give as a `String`. The call was taken, and every `next()`
  threw `DataFormatException`.
* **`Job.join(millis)` refuses a negative time** (bergdb 020-21, 3; 020-19)
  with `IllegalArgumentException`, as `Thread.join(millis)` does; it
  returned at once.
* **`Duration.seconds(NaN)` throws `IllegalArgumentException`** (bergdb
  020-21, Q1; Frans, 2026-11-09, 11:23), as a negative duration does: it
  gave a duration of 0, as `Math.round(NaN)` is 0. The API's other methods
  that take a double are values (`DbDouble`, which keeps one NaN) or index
  bounds (`UseIndexBuilder`, which refuse NaN already).
* **`Time.add(null)` and `Time.isBetween()` with a null throw
  `IllegalArgumentException`** (bergdb 020-25, C2), as every null argument
  of the API does (020-21, 3); they threw a `NullPointerException`.
* **The default cache size is clamped** (bergdb 020-25, C3) to 4 to 100,000
  MB, as a value given to `DatabaseBuilder.cacheSizeInMb()` is: a fifth of
  the JVM's maximum heap gave 2 or 3 MB under a heap of 20 MB, and more
  than 100,000 MB over one of 500 GB. A JVM without a maximum heap gets
  100 MB, as before, now in the Javadoc.
* **`transactionInfo()` leaves out a key that is no Pub key** (bergdb
  020-22, R22-1; Frans, 2026-11-09, Q5): for a transaction written through
  the Core's `Db` with a key of the Pub API and another key, such as a key
  whose first byte is not the bkey of `/`, `/x`, or `/dq/-a/b` (a name with
  a `/`), the KVs of `Connection.transactionInfo()` held the other key, and
  its `key()` threw `IllegalArgumentException`, or, for a key such as
  `/-q/-t`, gave the Pub key of another key (`/q/t`, whose key is
  `/dq/-t`). Now such a KV is left out, as the index entries are (005-42)
  and as `usePrimary()` leaves out such keys (021-06). A scan of an index
  leaves out such a key too: a value and its entry written through the
  Core at a directory's own prefix, such as `/dr/-` (an empty name), were
  given under `/r/`, no key.
* **Malformed index data written through the Core is refused, and a build
  skips a key that is no key of its directory** (bergdb 020-16, F16-1 to
  F16-3; 2026-11-09; 020-22's detection floor). A value at exactly
  `/#i/didef/` or `/#i/didel/` makes a start refuse the database with
  `InternalDataException` naming the key, and one at `/#i/dii/` with
  `VersioningStreamException`: the start took the prefix's own key for the
  end of its read and started without the index definitions or the
  cleanups under it, so writes were not indexed and scans gave stale
  results. A scan that meets an entry whose key part is no key's throws
  `InternalDataException` naming the entry, where it threw
  `IllegalArgumentException`. A build skips a key whose name holds a `/`,
  such as `/dp/-a/b`, as `usePrimary()` does: for one that held an object,
  the build failed at every start, or put an entry that named another key.
  Only a write through the Core's `Db` makes such data.
* **`transactionInfo()` while another thread writes no longer fails the
  database** (bergdb 021-13; 2026-11-09). A get that read a value just
  after another thread's put could give the position of the put's record
  before the record was in the stream in whole: the writer sets its
  nodes' positions before it appends it. `Connection.transactionInfo()`
  (the Core's `Db.getTrans`) then read the record in part, took it for
  corrupt data and failed the database (`DbFailedException`, the cause a
  `StreamFormatException`, "Bad item byte size ... beyond the stream's
  record bytes"), so that every later call threw until a restart, which
  lost nothing; or it found none of the record and threw
  `IllegalArgumentException`, which its Javadoc does not name. Now the call
  waits until the writer has appended the record. A get that read the
  value before its positions were set gives the documented
  `IllegalStateException` ("call get() again"), as before. In 2026.1 to
  2026.3; found by a new-user application (020-24-01, U1-1 and U1-2).
* **`currentTime()` keeps its promise with a clock that goes back**
  (bergdb 020-23, Z1; 2026-11-09). `Connection.currentTime()`,
  `Database.currentTime()` and the Core's `Db.currentTime()` gave the
  clock's time, at least the last transaction's, and kept it as the time
  that the next transaction must pass: after a clock that went back, a
  later call gave an earlier time than an earlier call, and a transaction
  after it could take a time before the earlier one, so that a read at
  that time changed. Now the times it gives never decrease, and every
  later transaction's time is after them. Its time is also at most
  2^56-1025, unless a transaction's is later: with the clock in the last
  1024 units, or out of range, it gave the clock's time, and took the
  times kept for reclaim's transactions after a user's (015-55), or threw
  `IllegalArgumentException` from `Time`. Since the 2017 code: in 2026.1
  with the default clock when the system clock was set back, and since
  2026.2 (005-69) with a `Clock` of the application's
  (`DatabaseBuilder.clock()`) that goes back, as `Clock.getTime()` allows.
* **A `currentTime()` while the clock is out of range no longer keeps
  every transaction refused** (bergdb 021-26; 2026-11-09).
  `Connection.currentTime()`, `Database.currentTime()` and the Core's
  `Db.currentTime()` with the clock after 2^56-1025 (out of range, or in
  the 1024 units kept for reclaim) gave 2^56-1025 and kept it as the time
  that the next transaction must pass, so every user transaction after it
  was refused ("No database time is left for a user transaction") until a
  restart, also when the clock was back in the range. Now such a clock's
  time is not taken: `currentTime()` gives the last time it gave or the
  last transaction's, and the transactions, refused while the clock is out
  of range, go on when it is back. Since 020-23's Z1 (today, never
  released); before it, a later `currentTime()` with the clock back ended
  the refusals. Found by a black-box user of the C port (022), U2-1.
* **`transactionInfo()` gives the transaction that wrote a value that
  reclaim has rewritten** (bergdb 021-17; 2026-11-09). With a finite
  retain duration, reclaim rewrites live values in transactions of its
  own, from its first iteration on, long before it cuts anything, and a
  get then reads reclaim's copy. `Connection.transactionInfo()` threw
  `LookupTimeNotAvailableException` for every such copy ("reclaim has
  rewritten the value, and the transaction that wrote it is no longer
  available"): for a value 10 ms old with a minute retained and nothing
  cut, and for every value written once, from reclaim's first iteration
  on; a later lookup time never helped. Now it follows the copy back to
  the transaction that wrote the value and gives its time and KVs, always
  when that time is at or after the first available lookup time; it throws
  only for a transaction before that time that reclaim has removed, or
  whose value it rewrote at or before that time, and the message says so.
  A record that holds a KV under reclaim's prefix but is no copy of the
  value, which only a write through the Core's `Db` makes, is refused with
  `InternalDataException`, and the database goes on. The stream is
  unchanged. In 2026.1 to 2026.3; found by a new-user application
  (020-24-06, U6-1).
* **Messages that name the user's key** (bergdb 020-24-05, U5-9;
  2026-11-09). A put of an object at a key with another suffix said "Bad
  key, expected no suffix (or possibly the obsolete '.obj' suffix), key
  was: '/dk/-x.OBJ'.": the key in BergDB's internal form, and ".obj",
  which the Javadoc documents, called obsolete. Now it says "Bad key for an
  object, '/k/x.OBJ': an object is put only at a key without a suffix or
  with the suffix ".obj", in lower case.". A get as `DbObject` or as a Data
  Object class of a value that is not a stored object ended its message
  with " ukey=/g/str"; now the message starts "The value at /g/str cannot
  be read as an object: ". A get as `String` of a stored object says that
  the value is an object, not a String, where it said only that the value
  is not well-formed UTF-8. The exceptions are as before. In 2026.1 to
  2026.3; found by a new-user application.
* **A start that fails on the storage throws the storage's exception**
  (bergdb 020-24-08, U8-2; 2026-11-09). A start whose read failed on the
  storage in its last steps, as with the first stream file deleted, or
  whose read met a failure of the storage in the background, as its own
  write on a full disk, threw a `DbFailedException`, "Cannot call
  getOne(): the database failed (the cause) and must be restarted." or "A
  read failed on the storage (the cause). [...] must be restarted.",
  which named a call that the application did not make and asked for a
  restart, which failed the same way. Now it throws the storage's `StreamIoException` (or
  `StreamFormatException`), as `DatabaseBuilder.start()` says and as the
  start's earlier steps did, and has closed what it opened, as before.
  `create()` of a path that is a regular file says "Directory P could not
  be opened: it exists and is not a directory." where it said "Not a
  directory" without the path (U8-11). Found by a new-user application.
* **An rw() action may use its environment from several threads**
  (bergdb 021-21, U11-1 and U11-3; 2026-11-09). An action that read or
  wrote through its `RwEnvironment` from several threads, with a parallel
  stream or a task it waited for, which the Javadoc did not forbid, read
  another key's value, committed only part of its puts with no error (546
  of 6,000 keys), and then failed the database ("Bad value pointer -1",
  reported as a failure of the storage). Now the environment takes its
  threads' calls one at a time, uncontended for one thread: every read is
  at the transaction's read time and every put is committed. And the
  environment is closed when the action returns, before the commit, where
  it was closed after it: a thread left by the action could put while the
  transaction was made, and an object was committed without its index
  entry; now every call after the return throws the documented
  `IllegalStateException`, from any thread, and changes nothing, and each
  run of the action has an environment of its own. A single-threaded
  `rw()` costs the same. In 2026.3 and before; found by a new-user
  application (020-24-11).
* **A Connection, an iterator or a WBuilder shared by threads refuses
  instead of corrupting** (bergdb 021-22, U11-2 and U11-6; 2026-11-09).
  Threads that read through one `Connection`, which the Javadoc forbids,
  shared its read state: gets returned another key's value or null, threw
  `ArrayIndexOutOfBoundsException`, and failed the database with a
  message of corrupt data ("A read failed on the storage", "Bad value
  pointer -1"), which loses an in-memory database. Now a call of a
  connection while another thread is in a call of it throws
  `IllegalStateException` ("A Connection is used by one thread at a
  time") and reads and changes nothing; a call inside a call of the same
  thread, as in a Data Object constructor or an rw() action, is taken.
  Every call that reads, writes, runs a transaction, syncs, starts a scan
  or sets the lookup time is checked, also `Database.connection()` of the
  thread whose connection another thread is using. An iterator of
  `usePrimary()` or `useIndex()` read by threads at once skipped values
  and threw internal exceptions; it now refuses in the same way. A
  `WBuilder` that threads put into lost puts, or a thread spun in its map
  forever; it now takes their calls one at a time, and a put after
  `execute()`, also one that waited for it, throws
  `IllegalStateException`. A compare-and-set per call: no cost measured
  for one thread. In 2026.3 and before; found by a new-user application
  (020-24-11).
* **`transactionInfo()` after a get whose Data Object constructor reads**
  (bergdb 020-24-11, U11-5; 2026-11-09). A get whose class's constructor
  read another key through the same connection left
  `Connection.transactionInfo()` describing the constructor's read; it now
  describes the get's value. Found by a new-user application.
* **A put of an object too large to store is refused before anything is
  copied** (bergdb 021-23; 2026-11-09). A put copied each element of an
  array into the array's buffer and checked the array's size only then, so
  an object small in memory and too large to store, such as an array of
  2,100 references to one 1 MiB `byte[]` (2.2 GB stored), threw
  `OutOfMemoryError` with a heap below about 5 GB, from `put()`, `w()` and
  `DbObject.toDbObject()`, and inside `rw()` the error failed the
  database; with 8 GB of heap the refusal came at a resident size of 4.6
  GB, its message "size: a value of 2147493890 bytes; ..." without the
  place. An object of 25 fields of one 100 MiB array was cloned, 2.6 GB,
  before its refusal. Now a put counts the object's stored bytes first, without a
  copy, and refuses it with `IllegalArgumentException` where the count
  passes 2^31 - 9 bytes, the largest Java array, in about 10 ms: "The
  object is too large: its stored value passes 2147483639 bytes at
  'parts[2047]'. ..."; nothing written, and the database goes on. The
  count adds a walk of the object to each put of one, without a copy. In
  2026.4's Data Objects (020-09); found by a new-user application
  (020-24-12, U12-1).
* **A database whose directory was deleted writes nothing into a new one
  at its path** (bergdb 021-20, from 020-24-10, U10-1; 2026-11-09). A
  database's directory deleted after `stop()`, while the database still
  wrote in the background, or while it ran, and a new database created at
  the path: the start was taken, as the lock was the directory's, and the
  old database made its next stream files by name in the new directory. The
  new database then failed to start (`StreamFormatException`, "Could not
  find *any* valid meta block") or lost its synced data, with no error to
  either. Now, in the process, a start at the path is refused as in use
  (`StreamIoException`, cause `DirectoryInUseException`) until a database
  started there has closed, also when its directory was deleted, moved or
  replaced since; and a file database checks, before it makes, deletes or
  opens again a stream file by its name, that the path still has its
  directory, and fails otherwise (`DbFailedException`, or a
  `StreamIoException` of `close()`). `Database.stop()` says to delete a
  database's directory only after `close()` has returned. In 2026.1 to
  2026.3. Found by a new-user application.
* **A database's directory replaced while the database moved to its next
  stream file** (bergdb 021-24; 2026-11-09). The check of 021-20 came
  before the database forced its last file, which with per-append forcing
  off (a Core option; a database of the Pub API forces each append) can
  take seconds: a directory replaced during that force got the next stream
  file, the old database's `sync()` and `close()` returned, and the
  database at the path no longer started. A cut's check came before the
  close of the file, which waits for reads in progress. Now the database
  checks its directory right before it makes, deletes or opens again a
  stream file, with nothing that waits in between, and again after.
  Still not prevented: a replacement in the microseconds between the
  check and the step, which can leave an empty stream file in the new
  directory (a start there is refused until it is removed) or, at a cut,
  delete the new directory's file of the same name; the database then
  fails. `Database.stop()` says so. Found by a Codex review (round 4) of
  021-20.
* **A closed database releases its write buffer** (bergdb 020-24-10,
  U10-3; 2026-11-09). A closed `Database` that the application still
  referenced held its write buffer, 10 MB, until the object was dropped:
  30 closed databases kept in a list of recent documents held 331 MB. The
  buffer is released when the database's storage thread ends, at
  `close()` or at the end of the background close after `stop()`; such a
  database now holds about 0.5 MB (a memory database its data too).
* **Starts at once on a directory that does not exist** (bergdb 020-24-10,
  U10-5; 2026-11-09): the starts that lost the race to make the directory
  threw `StreamIoException` "Directory ... could not be created.", as
  `mkdirs()` returns false when another thread made it; now they are
  refused as in use, as `DatabaseBuilder.start()` says.
* **`sync()` after `close()` returns** (bergdb 020-24-10, U10-6;
  2026-11-09), from `Database` and from a `Connection`, as its Javadoc says
  for a durable transaction: the close wrote and forced every transaction.
  It threw `StreamIoException`, "StorageManager has error: Storage is
  closing.". So does `sync()` after `stop()` once the background close is
  done; during it, a `sync()` of a transaction not yet durable throws as
  before.


### Core API

* **`DbBuilder.createdTxt(File)` takes no crypto key** (bergdb 020-28;
  2026-11-09): `createdTxt(File dir, String cryptoKeyInfo)` is now
  `createdTxt(File dir)`, as release 2026.4 has no encryption in its API;
  `created.txt`'s line "crypto key:" says "none (not encrypted)" (or, for
  the internal `SalsaStream`, its key's name). A start whose stream's magic
  bytes are wrong throws a `StreamFormatException`, with the
  `BadMagicBytes` as its cause, where it threw the Pub API's
  `BadCryptoKey`; its message names, among the causes, a stream that an
  earlier release encrypted.
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
* **A read that keeps no index node no longer takes a writer's node from
  it** (bergdb 019-46): a race in the Core since handles (2026.2). A read
  whose cache policy keeps no index node (`Dag.CACHE_NOTHING`) removed the
  empty handle it had made (`Cache3.dropIfEmpty`) while the writer could
  take that handle, load the node into it and make it canonical; the
  removal then evicted the writer's object in the middle of its
  transaction, so that its record named an old version of the node, and
  later reads gave old values. Only a program that read through the Core
  API with a `GetData` or `GetMany` set to `Dag.CACHE_NOTHING`, while
  another thread wrote, could meet it: no read of BergDB's own or of the
  Pub API uses that policy. Found under load by
  `EvictionAccountingTester`, whose reads use it.
* **A start no longer keeps a large value of its first transaction in
  memory** (bergdb 019-47): a start reruns every transaction of the
  startup section but the first, whose values it links into the section's
  node versions; its admission of large values (015-68: a value over 1 MiB
  in the stream is reached by a stream pointer) took only those that the
  rerun reported, so a value over 1 MiB of the section's first transaction
  stayed in its leaf for as long as the database ran, unless the budget
  forced its eviction. Now the start admits every resident key node's
  values as a written record's. In 2026.2 and 2026.3; a start with a large
  budget, whose section began with such a value's transaction, showed it.
* **A pointer to a node of another type is refused also where it is linked
  by node id** (bergdb 021-11; 2026-11-09). 019-32's check, that a pointer
  names a node of the type it expects, was made where a pointer is
  followed, but not where the Core gives a pointer the handle of the node
  that its position names: a start's links to the nodes in memory (rule 4)
  and the writer's links before a node is written. A damaged node, its
  checksum right, whose pointer named a version of a node of another type
  got that node's handle, and a read threw a `ClassCastException` (with
  `-ea`, an `AssertionError`). Now the start refuses the stream, or the
  write fails the database, with `StreamFormatException`. Valid streams
  are read as before; the stream's bytes are unchanged.
* **A start validates the key nodes it reads from before its startup
  section** (bergdb 021-12; 2026-11-09), as it validates the section's
  (`DbStarter.validateNode`): their sizes, times increasing, the last
  time's index and their pointers, and that no time is after the startup
  time. A damaged one, its checksum right or a byte flipped by 0xff, made
  the start throw an `AssertionError`, also without `-ea`, from its check
  of the nodes in memory or from its rerun; now the start refuses the
  stream with `StreamFormatException`. Valid streams are read as before;
  the stream's bytes are unchanged.
* **A close no longer waits a quarter of the buffer time for nothing**
  (bergdb 020-13, bug 4; 2026-11-09): when `close()` came while the
  storage's writer thread wrote the buffer, that thread then waited for its
  timer, a quarter of the buffer time, before it wrote the bytes buffered
  since, which `close()` waited for: up to 12.5 ms more at the default
  buffer time of 50 ms, and 15 s with a buffer time of a minute (the Core's
  `DbBuilder`). A lost wake-up in `BufferedStream`, in 2026.3 and before.
* **`GetMany.GetN` and `GetMany.PrefixN` give at most their count, none for
  0** (bergdb 020-27; 2026-11-09): with a count of 0 they gave every KV (of
  the prefix), as the count passed 0 before it was compared; "Gets at most
  N kvs". `PrefixN` keeps a copy of its prefix, as `Prefix` and `Endpoint`
  do: it kept the caller's array, as its copy went to the parameter. No
  reader of BergDB uses a count of 0.
* **`GetMany.StopCondition.eod()` is called also for a lookup time before
  the first transaction** (bergdb 020-27; 2026-11-09): a `getMany()` at a
  time when the database had no state returned no KV without calling
  `eod()`, which the interface promises at the end of the database. BergDB's
  own readers do not depend on it.
* **`DbBuilder.cacheSizeIndicator()` refuses a value below 1** (bergdb
  020-27; 2026-11-09) with `IllegalArgumentException`, as
  `Db.setCacheSizeIndicator()` does: it took one, and a start then threw an
  `AssertionError` (with `-ea`) or ran with a budget of 0 or less. The Pub
  API's `DatabaseBuilder` clamps its value to 4 to 100,000 MB and never
  passed one.
* **The Core API refuses a null argument with `IllegalArgumentException`**
  (bergdb 020-27, Q2; Frans, 2026-11-09), as the Pub API does, with a
  message that names the parameter, before anything else, also after
  `stop()`: `Db`'s `start(params)`, `getOne()`'s key and `GetData`,
  `getMany()` and a `GetMany` whose `stopCondition` is null, `execute()`
  and `printDag()`; `DbBuilder`'s `clock()` (at the call; `build()` refused
  it), `evictionSchedule()`, `mainStream()` (it removed the stream set
  before), `createdTxt()`'s directory and `testSetup(stream)`; every key,
  value, read key and hash array of `Trans.Builder`; the key or prefix of
  `GetMany`'s `Endpoint`, `Prefix` and `PrefixN`. They threw
  `NullPointerException`, or `AssertionError` with `-ea`;
  `Trans.Builder.delete((long[]) null)` was taken and `build()` threw;
  `start(null)` closed the storage; a null eviction schedule or
  `createdTxt()` directory was taken, and the start threw or wrote no
  `created.txt`. None failed the database. Each method's Javadoc says it.
* **The Core API refuses an argument out of its range with
  `IllegalArgumentException`** (bergdb 020-27, Q2, range checks), never an
  assert that depends on `-ea`: a key of no segments (`long[0]`) in
  `Trans.Builder`'s `put()`, `delete()` and `keyRead()` and in
  `Db.getOne()`; `Db.getMany()` with a `startKey` of no segments, a
  `result` that is not empty, or a stop condition whose `handleKvt()`
  answers none of its four values; `GetMany.GetN` and `PrefixN` with a
  negative count; `Trans.Builder.addReadHashes()` with a length outside 0
  to the array's length. With `-ea`, a put or a delete of such a key, such
  a `startKey` and such an answer failed the database (an
  `AssertionError`); without it, the key was written, the scan gave no KV,
  the answer was taken as CONTINUE, a `result` was added to, and a length
  too large threw `ArrayIndexOutOfBoundsException` after some hashes were
  added.
* **A read at a position near `Long.MAX_VALUE` is a read past the end**
  (bergdb 021-14; 2026-11-09). The storage's check of a read's end,
  `position + length`, overflowed for a position within `length` of
  `Long.MAX_VALUE`, and the read went on: `BufferedStream` took bytes of
  its ring buffer or threw `IndexOutOfBoundsException`, and `MemoryStream`
  returned with the array as it was or threw an `IOException` that is not
  `EOFException`. A damaged stream, its checksums right, can carry such a
  position in a node's pointer: the start was refused, or the database
  failed, as at any read past the end, but with an
  `IndexOutOfBoundsException` as the cause. On Linux and Android,
  `OneFileStream`, the simple stream for tests, threw the `IOException` of
  `lseek`'s `EINVAL`. Now such a read throws `EOFException`, as
  `AppendOnlyStream.read()` says. In 2026.3 and before.
* **A start's refusals name a node the same way in every run** (bergdb
  021-15; 2026-11-09): the texts of the `StreamFormatException` of a key
  node's validation at a start (`KeyNode.validateStreamNode`: a pointer's
  bad position, a node of size 0) and of `DbStarter` (a node's position,
  an unexpected stream pointer, the first record's nodes), and of
  `KeyNode.check`'s `AssertionError`, named the node by its `toString()`,
  which holds the object's identity hash, so that two runs gave two texts;
  one printed the whole node over many lines. Now each names it by its
  kind, id and position, as "key node 22807 at 36536" (`Node.name`), as a
  port of the Core that matches the texts needs.
* **A long key no longer makes a start or a put overflow the stack**
  (bergdb 021-16; 2026-11-09). A key is a tree of key nodes with a level
  per segment of 7 bytes, and walks of that tree were recursions with a
  frame per level. With the JVM's default stack, a database with a key of
  about 90 KB or more (Core or Pub API) did not start: the start's check
  of the nodes in memory (`Dag.visitMemoryNodes`) threw
  `StackOverflowError`; with `-Xss16m` it started, and nothing was lost.
  A put of a key of 1,000,000 bytes after one of 100,000 with the same
  start threw `StackOverflowError` in the transaction's size check
  (`Dag.dirtyNodeBound`, 005-31) and failed the database. These walks, and
  `Dag.visitMemoryPointersOnce` and `DagNodeIterator` (for tests), are
  loops with a stack of their own now, in the same order. A key's length
  still has no limit. In 2026.1 to 2026.3; found by a new-user
  application (020-24-05, U5-1 and U5-2). The stream is unchanged.
* **A start reruns a transaction of a long key in time linear in its
  nodes** (bergdb 021-16, Q2; 2026-11-09). The rerun of the startup
  section looked up each node it made in the transaction's record by a
  scan of the record (`StoredTrans.findNode`), so its time grew with the
  product of the two counts, and a long key makes a node per 7 bytes: a
  database with a key of 100,000 bytes and then one of 1,000,000 with the
  same start took 4.9 to 5.9 s to start, now 0.5 to 0.6 s. Now a map from
  id to node; the nodes found are the same. In 2026.1 to 2026.3.
* **`GetMany.Prefix` and `GetMany.PrefixN` give the prefix's own key**
  (bergdb 021-18; 2026-11-09). They stopped at a key equal to the prefix,
  as `Keys.isPrefix` is a strict prefix, so that the usual prefix scan,
  `startKey` the prefix and `inclusive` true (its default), gave no KV at
  all whenever the prefix was itself a key, and a backward scan left that
  key out. Now they add it, as a key that starts with the prefix, and stop
  at the first key that does not. No reader of BergDB's own uses them: the
  Pub API's listings, index builds and index scans have bounds of their
  own, and a directory's prefix is no key of the Pub API. In 2026.1 to
  2026.3; found by a new-user application (020-24-09, U9-1).
* **`Kvt.time` and `GetData.kvTime` are documented as the time of a key
  node entry, not of the write** (bergdb 021-19; 2026-11-09). `GetMany`'s
  Javadoc said that a result's KV holds "the time it was last written";
  it holds the time of the transaction that made the key node entry that
  points to the value. A transaction that replaces a full key node, by a
  time or space split, makes every entry the node keeps anew at its own
  time, so a key that it did not write reads its time: a transaction that
  puts 27 keys and one that puts a 28th give all 28 the second's time. The
  time of the write is `Db.getTrans(tpos).tt`, with `GetData.tpos` (for a
  scan's KV, from a `getOne()` of its key); for a value that reclaim has
  copied, `tpos` is reclaim's step, also documented now. No change of
  behaviour: there is no exact value time (bergdb 011-01, Q9, 2026-10-13),
  and the Pub API has none since 2026.1. Found by a new-user application
  (020-24-09, U9-3).


### Format

* **Stored objects and the index definitions are in format 2** (bergdb
  020-08, step 2; see the Pub API): the bytes of every object that the Pub
  layer stores change, and so do those of an index's definition, an
  object of format 2 (020-10, section 4.2). The Core's records and the
  stream's format are unchanged. StreamDigest's digests are unchanged: its
  workloads use the Core API and put no object.
* **The user indexes' internal keys are new** (bergdb 020-10, section 4;
  their layout approved in principle by Frans on 2026-11-08, 22:08,
  020-01, section 14.1, its details under his delegation of 22:17): a
  definition at `/#i/didef/-NAME`; the entries under `/#i/dient/dNAME/`
  and the generation G, the creation's time, so that no index sees
  another's entries; a deleted generation's marker `/#i/didel/dNAME/-G16`
  until its cleanup ends. 2026.3's keys, `/#i/dii/` and `/#i/di/`, are no
  longer written: a start that finds a key under `/#i/dii/` throws
  `VersioningStreamException` (020-08, step 3). So a database of 2026.3
  with an index does not start, and one with objects starts but refuses
  them when they are read (the Pub API's entries); make such a database
  again. The Core's records are unchanged.


### Build and tools

* **A release jar without the development classes** (bergdb 020-10, step
  B1): `java/build.sh` makes `build/bergdb-release.jar` beside
  `build/bergdb.jar` (unchanged, the jar of the tests and scripts): the
  classes and resources of `src` only, without `src-dev`'s (the packages
  `bergdb`, `bergdb.dev`, `bergdb.test`, `bergdb.demo` and `frans`), and no
  `Main-Class`. The build fails unless its entries are `bergdb.jar`'s
  without `src-dev`'s, `jdeps` finds no class that it uses outside it and
  the JDK, and a program compiled and run with it alone on the class path
  (`java/stress/release-jar/ReleaseDemo.java`) works. The release ships it.
* **The jars seal the packages `bergdb.pub` and `bergdb.pubimp`** (bergdb
  020-10, B3's review): no class of another jar or directory joins them,
  so no program extends `DbValue` or reaches their package-private
  members; the build checks the release jar's manifest.
* **ICU is gone** (bergdb 020-10, step B2; Frans, 2026-11-08, 22:08: no
  ICU, 020-01, section 14.1): `src-icu/` (the package `bergdb.pubimpicu`),
  `java/in/icu-for-bergdb.jar` (ICU 50 as `bergdb.icu50`) and its license,
  and the collator classes of `pubimp`, which 020-10's I2 left unused. Both
  jars are about 2 MB smaller: `bergdb.jar` 1.8 MB, the release jar 1.6
  MB, and the build checks that the release jar holds no class of ICU's
  packages. A string index orders its values by their code points (020-10,
  step I2).
* **`java/build.xml` is gone** (bergdb 020-10, step B2), the Ant script of
  2013 to 2017 that no script ran, with `java/in/jarjar-1.4.jar` and
  `java/in/style.css`, which only it used. `java/build.sh` is the build.


### Internal

* **The user indexes' code and its checks** (bergdb 020-10, steps I0 to
  I3): the keys and the levels' encodings (`IndexKeys`), the definition
  and the index function (`IndexDefinition`), the manager, the build and
  the scan, rewritten; with the races' tests (`PubTesterIndexRaces`) and
  the harnesses H2, an index as a function of the data (`IndexReference`,
  `IndexHarness`), H3, the jobs under faults (`IndexJobsHarness`), and H4,
  the primary scan (`PrimaryHarness`).
* **The tests' check that every database is stopped finds the index
  threads** (bergdb 020-21, 4; 020-13): the unit, f and night groups fail
  when a test leaves a user index's build or cleanup thread
  (`IndexBuild-*`, `IndexCleanup-*`) alive, as they did for the storage and
  eviction threads (bergdb 005-55).
* **Three stress tools for the Pub layer, each a step of `night.sh`**
  (bergdb 020-15 to 020-17; 2026-11-09): `java/stress/kill-restart.sh`,
  which kills a child JVM with SIGKILL during work on objects and indexes
  and checks every restart (`KillRestartHarness`, 1,000 kills);
  `java/stress/fuzz.sh`, a fuzzer of 2026.4's readers of bytes, each
  against its spec (`FormatFuzzer`, 12 minutes); and
  `java/stress/harness-soak.sh`, long runs of the randomized harnesses with
  new seeds (two rounds). The unit tests run `FormatFuzzer` briefly.


### Documentation

* **BergDB's rule for strings is stated once, in the Pub API's Javadoc**
  (bergdb 021-04; 2026-11-07): every string BergDB stores, a key, a String
  value, each string in an object and an index name, is a sequence of
  Unicode scalar values stored as well-formed UTF-8 (RFC 3629), in every
  language; a writer refuses a string it cannot store so (in Java, a
  String with a lone surrogate), and a reader may rely on it. The package
  `bergdb.pub`, section "Strings", holds it in full, with why and what to
  do with data that is not text (a `byte[]`, or a `char[]` in an object);
  `Connection`, `WBuilder.put` and `RwEnvironment.put` link to it, and the
  Core's `key-encoding.md` states it for keys.
* **The Pub API's Javadoc says what is, not how it was** (bergdb 021-01;
  2026-11-07). The sentences on how a method or an exception behaved before
  a change, and their dates, are gone from `Database`, `DatabaseBuilder`,
  `DbException`, `DbFailedException`, `DatabaseMissingException`,
  `DatabaseNotCreatedException` and `SyncLevel`; the release notes keep the
  history. `DataFormatException` says where it is thrown: the objects, the
  user indexes and String values. `Time.utc` and both `Time.resolve` document
  `BadFormatException` for a bad time string and `IllegalArgumentException`
  for a null argument.
* **Objects and Data Objects in the Pub API's Javadoc** (bergdb 020-08,
  step 6): `bergdb.pub`'s package documentation has the sections "Objects"
  and "Null and absent fields", and `Connection`, the puts and the gets say
  what a put refuses and how a get converts.
* **Where an object may be put** (bergdb 020-11): `Connection.put`,
  `WBuilder.put` and `RwEnvironment.put` say that an object, neither a
  `String` nor a `byte[]`, is put only at an object key, without a suffix
  or with `.obj`, and is refused elsewhere with `IllegalArgumentException`
  ("Bad key"); `bergdb.pub`'s section "Objects" says what a suffix is.
* **The API's boundary, objects and user indexes in docs/levels.md**
  (bergdb 020-10, B2): its section 11, the README and the Javadoc's
  overview name the API (`bergdb.pub`, `bergdb.pub.util` and the Core's
  `Db`; the release jar) and describe objects, the user indexes and the
  primary scan, with no experimental list left.
* **The Pub API's corners said** (bergdb 020-21, 3; 020-13, section 4.2;
  020-19, section 6): `Connection.useIndex` lists
  `LookupTimeNotAvailableException` for a lookup time behind the cut;
  `Job.join` returns BUILDING after a failure of the database, as after a
  stop; `Duration.seconds` rounds to clock units and gives `MAX` above it;
  `Connection.delete` of a key without an entry still commits a
  transaction with a time of its own; `DbObject.toDbObject` wraps a
  `String` in "p", as a wrapper, and refuses a `byte[]`, now with a message
  that says why (it gave the class check's "a primitive or an array is not
  a class of fields"), and `toJavaObject(byte[].class)` reads "array", not
  "p"; `DatabaseBuilder.start()` of a `memory()` builder whose database has
  closed starts on the closed stream, reads the data and fails at its first
  write.
* **The rules for writes through the Core in a database of the Pub API**
  (bergdb 020-22; Frans, 2026-11-09, A2: "Core is root, with a detection
  floor"). `Db`'s Javadoc, "Keys and the layers above", says which keys a
  `Db` may write: every key that does not start with the bkey of `/d`, `/-`
  or `/#` is the Core user's, never read for its meaning or changed by
  BergDB; the Pub API's keys may be written, but only the Pub API's writes
  keep its indexes, so a Core put at an object key of an indexed directory
  can be left out of the index's scans until the key is written again
  through the Pub API or the index is made again (bergdb 020-27: a put that
  keeps the indexed fields changes nothing); keys under `/#` are BergDB's.
  Malformed internal data is refused with `InternalDataException`; a scan
  of an index never returns a value that does not match its query.
  `bergdb.pub`'s "The API and its jar", the Core's `key-encoding.md` and
  docs/levels.md, section 11, point to it.
* **The Pub API's Javadoc checked against its behaviour** (bergdb 020-19;
  2026-11-09), promise by promise for the classes that 2026.4 changed
  most, each promise with a test (`PubTesterJavadoc`). Corrected:
  `Database.setCacheSizeInMb()` after `stop()` sets the value (J1);
  `DbObject.toDbObject()`'s message names the place of a lone surrogate
  (J2), as a put's does since 021-04; `ReadInterface.get()` and
  `RwEnvironment.get()` take the class of a primitive, its wrapper and an
  array (J3); `DbException`'s example of a refusal (J4); the
  `DataFormatException` of a `byte[]` put of a format-1 object in an
  indexed directory, from `Connection.put()`,
  `WBuilder.execute()` and `Connection.rw()` (J5); the `DbException` of an
  interrupted sync (J6); `Time`'s grammar (J7, then made strict by 020-21);
  and the `DbException` of a refused write, a transaction too large (about
  1.88 GB in the stream), a database stopping or stopped, or an interrupt
  while it waits to run again after a conflict, for `rw()` and, at an
  object key, for `Connection.put()`, `delete()` and `WBuilder.execute()`
  (J8; 020-23, V1-2). `IndexBuilder.start()` and `Database.deleteIndex()`
  say that a crash before the change is durable can undo it, as for any
  transaction (020-15, KR-O1).
* **The Core API's Javadoc checked against its behaviour** (bergdb 020-27;
  2026-11-09), promise by promise for `Db`, `DbBuilder`, `Trans.Builder`
  and `GetMany`, each promise with a test (`DbTesterJavadoc`,
  `PubTesterCoreKeys`). Corrected: a second `Db.start()` throws
  `IllegalDbStateException` (J1); `Db.getMany()` is refused after `stop()`
  too (J2); `setCacheSizeIndicator()` below 1 and `sync()` of a null level
  are refused, and `SyncLevel.NONE` returns at once (J3); `getOne()` gives
  null for a key without a value (J4); `DbBuilder`'s refusals and its
  buffer's least size and time (J5); `GetMany`'s order and its four
  answers (J6). In "Keys and the layers above" (020-22): a Core put at an
  indexed object key can leave the value out of the index's scans, and one
  that keeps the indexed fields changes nothing (K1); BergDB never reads
  the Core user's keys for their meaning or changes them (K2); writes of
  BergDB's keys through the Db under a running Database are seen only in
  part until the next start (K3).
* **What the Core API is** (bergdb 020-27, Q1; Frans, 2026-11-09):
  `Db`'s Javadoc names it, at its top, and `DbBuilder`'s, the Core's
  package page and `bergdb.pub`'s "The API and its jar" point there. The
  Pub API is the stable, default and preferred API. The Core API is for
  low-level control and the most performance, less stable (it may change
  faster between releases) and less safe, its writes able to break the Pub
  API's data ("Keys and the layers above"); it is mostly the layer that the
  Pub API is built on. It is `Db`, `DbBuilder` (but for its members for
  tests), `Trans.Builder` and `Trans`'s outputs, `GetData`, `GetMany` and
  its stop conditions, `Kvt`, `StoredTrans` from `getTrans()`, `StartInfo`,
  `Keys.toSegments()` and `toBytes()`, `FileStream` and `MemoryStream` as a
  stream, and the exceptions they name; the rest, such as `Db.Internal`,
  `ExecuteData`, `TestHooks` and `lookupTime()`, is internal and may change
  without notice. "The API and its jar" said "Db with the types of its
  signatures", which by the letter took in those internals.
* **A start's heap** (bergdb 019-45): a start needs about twice the
  startup distance of heap above what the running database needs,
  whatever the cache budget (docs/levels.md, section 7); W7's 600 MB heap
  at a 200 MB startup distance was too small for a start.
* **What a stop does to the calls that run** (bergdb 020-24-03, U3-1, U3-3
  and U3-5, from a new user's application): `Database.stop()` and `close()`
  said that "a transaction that runs completes"; one whose commit has begun
  does, and another call that runs at the stop is refused with
  `IllegalDbStateException`, nothing of it written, the database not
  failed: an `rw()` whose action runs, which `close()` does not wait for, a
  put not yet at its commit, `get()`, `exists()`, `useIndex()`, and a scan's
  iterator at its next read. The three `sync()`s say that at a stop, before
  the transaction is durable, they throw a `DbException` (a
  `StreamIoException`, "Storage is closing."), the database not failed and
  the transaction still written by `close()`; the Javadoc of `get()`,
  `exists()`, `useIndex()`, `rw()` and the two scans says what a stop does
  to them.
* **Which connection a thread uses: one rule** (bergdb 020-24-03, U3-8):
  `Connection` said to make one for each thread with
  `Database.newConnection()`, the package page that `db.connection()` gives
  each thread its own. Now both say: `connection()`, the thread's own, the
  same object at each call in it; `newConnection()` for a second view, such
  as a reader at another lookup time. `Connection` adds that `connection()`
  sets the lookup time of the thread's connection to `Time.MAX` at each call,
  so code that reads at a lookup time keeps its connection.
* **When reclaim cuts, and a delete's history** (bergdb 020-24-03, U3-9;
  020-24-01, U1-11): `Database.setRetainDuration()` says when reclaim
  starts and cuts: an iteration begins when the stream has grown by more
  than twice the startup distance and a quarter of the duration has passed,
  and the cut comes when it has rewritten the live values and its end is
  older than the duration; so nothing is cut before the stream has grown by
  about four times the startup distance in a small database (about 200 MB of
  puts with the default 50 MB), however short the duration. A user who set
  one second and wrote 140 MB saw no state expire. `Connection.delete()` and
  the package page say that a deleted value stays readable at earlier lookup
  times until reclaim cuts them, forever by default. The message of
  `LookupTimeNotAvailableException` closes its parenthesis: "Cannot lookup at
  time T (UTC): the first time available for lookup is F (UTC)."; it had
  "(T's UTC, the first time ... F (F's UTC).".
* **Key replace: the text, where, and when it is off** (bergdb 020-24-01,
  U1-3, U1-4 and U1-6; 020-24-02, I-6): `Connection.setEnableKeyReplace()`
  says what replaces `${transactionTime}`, the transaction's time in clock
  units as 18 decimal digits with leading zeros, so that such keys are in
  time order; that every put of the connection is replaced, those of `w()`
  and of an `rw()` action too (`WBuilder.put()` and `RwEnvironment.put()`
  say so), with the setting as it was at `put()`, `w()` or `rw()`; that the
  puts of one transaction at such a key are puts at one key, the last
  counting; and that with key replace off, the default also for the
  connection of `Database.connection()`, the text is a part of the key as
  written.
* **A read at a lookup time sees the transaction of that time** (bergdb
  020-24-01, U1-7 and U1-12): `Connection.setLookupTime()` says that a read
  at lookup time t reads the state that the transactions of time t and
  earlier made, the one of time t included, and that a null throws
  `IllegalArgumentException`.
* **A local time in a change of summer time** (bergdb 020-24-01, U1-9):
  `Time.resolve()` says what it does with a local time that the change to or
  from summer time skips or repeats: it takes it as standard time, as
  `java.util.GregorianCalendar` does, so a skipped 02:30 is the time the
  clocks show as 03:30, and a repeated one is the second; it was silent, and
  since 020-21 says that the parse is strict.
* **A double into an integer field, and a read-modify-write after a class
  changed** (bergdb 020-24-02, I-1 and I-4): the package's "Objects",
  `DbObject.toJavaObject()` and this file said that a get sets "the nearest
  value"; a double, or a text with a fraction, read into an integer field is
  cut toward zero, as Java's `(long) x`, then clamped (12.7 is 12), as
  020-09, section 5.4 decided, and now they say so. "Objects" says what a get
  into a class and a put back store: what the object holds, so the put drops
  a stored field that the class does not have and keeps a converted value as
  converted.
* **The order of an index scan's keys, and an empty prefix** (bergdb
  020-24-02, I-8): `UseIndexBuilder` says that the keys of equal levels are
  in the order of their names' UTF-8 bytes, as the primary scan lists a
  directory, and that `prefix("")`, or an empty `byte[]`, takes every value
  of the level.
* **Reclaim's settings over a crash, the size on disk, and the first
  available lookup time** (bergdb 020-24-06, U6-2 to U6-4, U6-6 and U6-7,
  from a new user's metrics service): `Database.setRetainDuration()` and
  `setStartupDistanceInMb()` say that, as for any transaction, a crash
  before the setting is durable (`sync()`) can undo it, as
  `IndexBuilder.start()` says. `setRetainDuration()` says what stays on
  disk: the stream from the last cut point on, about the stream written
  within the retain duration plus one or two iterations, each at least
  twice the startup distance, a quarter of the duration's stream and four
  times the live data, with sizes measured; `DatabaseBuilder` and
  `setStartupDistanceInMb()` say that the startup distance paces reclaim.
  `getFirstAvailableLookupTime()` says that it is `Time.units(0)`
  (1970-01-01) before the first cut, that it moves only when reclaim
  decides a cut, at a commit, and only forward within a run: a restart
  after a crash can give an earlier time, if the crash came after a cut
  was decided and before its record was durable; the stream was then not
  cut, and every state from that time is readable and right.
  `Connection.get()`, `exists()` and `ReadInterface` list
  `LookupTimeNotAvailableException`, an `IllegalArgumentException`.
* **Memory, the cache budget, an index's build and a scan's iterator**
  (bergdb 020-24-04, U4-1 to U4-3, U4-5 and U4-6, from a new user's
  catalogue of 2 million objects with a budget of 4 MB):
  `DatabaseBuilder.cacheSizeInMb()` says that a budget below what the
  database must keep (the nodes changed since its startup position, about 2
  to 3 times the startup distance of heap) makes reads go at the pace of
  eviction while anything is written, so that a useful budget is well above
  it; `startupDistanceInMb()` says that the startup distance, not the
  budget, sets the heap a database needs, with the catalogue's figures (at
  the default 50 a start failed in 256 MB and ran in 384 MB; at 5 it ran in
  96 MB), and the conditions of its startup times, which were measured with
  100,000 and 1 million keys, with the larger figures of 006-19.
  `IndexBuilder.start()` says that a build pauses after each step for half
  its time, by design, and that `JobStatus.count()` gives its progress
  without a total. `UsePrimaryBuilder` and `UseIndexBuilder` say that an
  iterator holds nothing to release, so one not read to its end may be
  dropped.
* **Data Objects: the rules and conversions a new user met** (bergdb
  020-24-05, U5-3, U5-6 to U5-8, U5-10 and U5-11, from a new user's
  document store): the package's "Objects" says that a public final field,
  and a field that hides a superclass's field, make a class not a Data
  Object (020-09, V3 and V8), and that `DbObject` is not a field type; which
  conversions a get makes (a `char` read into a `String` gives its number,
  "65"; bytes into a `String` are decoded as UTF-8; booleans and numbers);
  that a get by another version of a class may give an array with null
  elements, which a put refuses (020-09, section 5.7); and that the suffixes
  are case-sensitive. `DbObject` and `DbValue.toString()` say that
  `toString()` gives a short tag, "o" for an object, and that the value
  classes have no `equals()` of their own. `Connection.transactionInfo()`
  says how to walk the versions of a key, newest first.
* **Damaged files, a full disk, the lock file** (bergdb 020-24-08, U8-1,
  U8-3, U8-4, U8-8 to U8-10, from a new user's log store on a file system
  that misbehaves): `Database`'s "The files" says that a start cannot tell
  a crash's cut tail from a lost last stream file, so that a last file
  deleted, emptied or cut while the database is stopped loses synced
  transactions without an error (also in `sync()` and `docs/levels.md`,
  section 8); that a tail of zeros or other bytes, which a power loss can
  leave on some file systems, is refused with a `StreamFormatException`
  ("Bad transaction size ... spos P"), and how to cut the stream at P; and
  that a full disk is freed only from outside, or by copying the files to
  a larger disk. `DatabaseBuilder.create()` says that a directory with
  stream files and without `created.txt` is opened, not made new;
  `start()` says what `bergdb.lock` does, that deleting it lets a second
  process start on the same files, and that a start may write, so a full
  disk may refuse it. `Job.join()` says that ACTIVE is not yet durable.
  A stream message's typo, "Was is modified", is fixed.
* **The Core API as an embedded key-value store** (bergdb 020-24-09, U9-4
  to U9-10, U9-12 to U9-14, from a new user's application on `Db` alone):
  `Db`'s Javadoc has new sections. "Opening a database": the stream to
  give the builder (`FileStream` on a directory, `MemoryStream`), which the
  `Db` closes, the builder's defaults, and an example that writes, reads
  and closes. "Keys and values": any bytes make a key, the empty array too;
  scans give the unsigned order of the bytes; no maximum length, but a long
  key costs in proportion to its length; an empty value is a value, a null
  one is refused. "Threads": which calls may run at once, and what state a
  read sees. "Optimistic transactions": the read time and the keys read
  (`Trans.Builder.lookupTime()`, `keyRead()`, the hashes), with an example
  of a retry on `RerunException`. "Keys and the layers above" says that the
  Core itself writes BergDB's keys, also with no Pub API
  (`setStartupDistance()` a live 200 kB value at `/#i/-dummy`, the reclaim
  settings at `/#i/dreclaim/-settings.txt`), which a scan returns, and how
  to skip them (the keys that start with 01 25). `getTrans()` says that a
  delete of a key without a value is not listed, and what a get gives for a
  value that reclaim has copied (its step's transaction, and how to find
  the original, as 021-17 does for the Pub API). `getTransactionCount()`
  and `getKvCount()` count since the start; `currentTime()`,
  `getFirstAvailablePos()`, `Trans`'s outputs, `GetData`'s, `Kvt`'s,
  `StartInfo`'s and `GetMany`'s defaults (a new `GetMany` for each call)
  are documented; `Trans.Builder` says that a delete never replaces a put
  of the same key; a read that runs at `stop()` may throw
  `StreamIoException` ("Storage is closing."), the database not failed.
  The test methods of `Keys`, `Trans`, `StoredTrans`, `RerunException` and
  `FileStream` are no longer public, so the Javadoc does not list them, and
  two `<` that the Javadoc showed as "invalid input" are escaped.
* **Calls of the database inside an rw() action, and what an action
  throws** (bergdb 020-24-11, U11-4 and U11-7): `Action.run()` and
  `Connection.rw()` say that a call of a Connection or the Database inside
  the action is a transaction of its own, committed at once, not undone,
  and made again at each run, and that one that writes what the action
  read makes `rw()` run the action again and again until the thread is
  interrupted or the database stops; that whatever the action throws
  other than an Error, a checked exception too, `rw()` throws as it is,
  nothing written; and `rw(null)`'s `IllegalArgumentException`.
  `RwEnvironment.get()` says that an action that catches its
  `ObjectCreationException` goes on and commits.
* **Data Objects: the class rules, the conversions and the heap of a put**
  (bergdb 020-24-12, U12-2, U12-3 and U12-5 to U12-8, from a new user's
  domain model of Java types): the package's "Objects" says that a put of
  a large object needs heap of about 4 to 5 times its stored size, and
  which `OutOfMemoryError` fails the database (also at `Connection.put()`);
  that a referenced array is stored once per reference; that a Data Object
  class is top-level or static nested, that a superclass that declares a
  stored field is public, that no class of the Java platform is a
  superclass, and that a class with a field of a type variable is not a
  Data Object (020-09, V1, V4, V5 and V9); which texts read as numbers, by
  Java's grammar; what a float stored as a double means for an index's
  `eq()`, for a read as a `String` and for size; and that a stored
  `byte[]` reads as null into an `int[]` while an array reads into a
  `byte[]` clamped. `Connection.get()`
  says that a get as a primitive, a wrapper or an array class reads the
  field "p" or "array" of any stored object, and gives null without one;
  `IndexBuilder` says how to find a float by a "double" level.
* **Many small databases, opened and closed** (bergdb 020-24-10, U10-2,
  U10-4, U10-7, U10-9, from a new user's application with one database per
  document): `DatabaseBuilder.startupDistanceInMb()`, `Database` and the
  package's "Good to know" say that every started database holds a write
  buffer of 10 MB of heap until it closes, whatever its data and settings,
  so that many small databases open at once need heap accordingly, with no
  setting in this release; `Database.stop()` and "Good to know" say that
  `stop()` followed by `System.exit()`, or `stop()` in a shutdown hook, can
  lose transactions that returned, as `System.exit()` does not wait for the
  background close: call `close()` there; `Database.stop()` describes the
  write buffer and the buffer time, 50 ms; `StartupInfo.getStartupDuration()`
  says that it is the recovery's time, and what `start()` does besides.
* **The Javadoc agrees with itself and with the code** (bergdb 020-24-15,
  from a new user who ran every example of the documentation; 2026-11-09).
  `Database.stop()` and `close()` name the calls that throw
  `IllegalDbStateException` after them (every read and transaction,
  `setRetainDuration()`, `setStartupDistanceInMb()`, `deleteIndex()` and
  an `IndexBuilder`'s `start()`) and those that are taken, `sync()` and
  `setCacheSizeInMb()` among them, where they said to call nothing more.
  `WBuilder` says that an `execute()` refused because another thread is in
  a call of the connection leaves the builder unspent. `DbException` says
  that malformed internal data (`InternalDataException`) refuses the call
  that meets it and the database goes on, where it said to restart.
  `DatabaseBuilder.start()` names the refusal of a database with an index
  of 2026.3, and the `StreamIoException` of a path that is not a directory
  for `create()` only (`open()` throws `DatabaseMissingException`);
  `create()` no longer says that a directory with `created.txt` and no
  stream byte gets a new database. `Connection` says one thread at a time,
  not a single thread; the package's Data Object rules name 020-14's X3.
  The overview runs its program with `bergdb-2026.4.jar`, and the
  overview, README.md and the package page say that the documentation of
  `Db` is its Javadoc in the source, `java/src/bergdb/core/Db.java`, which
  the published Javadoc does not hold. No change of behaviour.
* **What a key costs, what the size limit counts, what a crash keeps, and
  a start after a large transaction** (bergdb 020-24-13, U13-1 to U13-3
  and U13-7, from a new user's bulk import and export; 2026-11-09).
  `Connection`'s "Keys" and the package's "Good to know" say that a long
  key costs many times its length: in a test, about 70 bytes of the
  stream for a key of 13 bytes, 1,200 to 1,400 for one of 114 bytes.
  `Connection.put()` gives the size limit of a transaction to the byte,
  1,879,048,178, and what it counts besides the keys and values: 28 bytes
  a put, 24 a delete, a key as 8 bytes for each 7, each pair rounded up
  to 4 bytes, the index entries too. `Database`'s "What a
  crash keeps" gathers what a resumable import relies on: each
  transaction, an `rw()` too, whole or absent; a prefix of them, in commit
  order; a `sync()` covers every transaction committed before its own.
  `DatabaseBuilder.startupDistanceInMb()` says that a transaction larger
  than the startup distance makes every start read all of it, until about
  twice the startup distance has been written after it.


### Known issues and limits

* **Reclaim stops cutting a log keyed by time** (bergdb 021-25; found by a
  new user of the C library, 022-06-3, U3-1 and U3-2). Under a workload
  whose keys sort in the order of time, each transaction putting a new key
  and deleting an old one (a FIFO, such as an audit log), with a retain
  duration, reclaim cuts as expected at first and then falls behind until
  it stops cutting, after some 200,000 transactions: the directory grows
  beyond what the retention needs. With a startup distance of 2 MB, a
  retain duration of 20 s and 1,024 live keys of 80 to 479 bytes, the last
  cut came at about transaction 200,000; after 300,000 transactions the
  first available time was 182 s back and the directory 135 MB, for
  300 KB of live data. Now and then a transaction of one put and one
  delete writes a record of 1 to 4 MB, growing with the run. No data is
  lost and every read is right. The same in 2026.3.

* **Fixed: puts no longer slow down after reclaim has passed many deleted
  keys** (bergdb 021-25, fix (c); 020-24-14, U14-1). Every transaction
  cleared the longest key access path that a reclaim step had ever
  followed (28,544 entries from transaction 180,000 of the FIFO above), so
  with index creations and deletions under a retain duration of 2 s, puts
  in another directory fell from 224,000 to 6,100 per second after 1,000
  cycles; now 202,000. The stream is unchanged, and so is the known issue
  above: reclaim still stops cutting there.
