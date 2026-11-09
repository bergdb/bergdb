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
  `ObjectCreationException`, and so does `next()` of a primary scan or an
  index scan that lists it as an object; an index build over it ends
  failed, naming the key, and the database goes on. Such an object at a
  key can be overwritten or deleted, in an indexed directory too; a
  `byte[]` put of one there throws `DataFormatException`. A start of
  a database that holds an index definition of format 1 throws
  `VersioningStreamException`, which says to make the database again, and
  closes it. A `String` value is never taken for such an object, whatever
  its first bytes: one that began with `bergo` and the byte 1 was (a get as
  `Object` threw, and in an indexed directory its put was refused). The
  guess left: a `byte[]` that passes format 2's full check is an object,
  and one whose bytes are a whole object of format 1 is refused as one
  (`Connection.get`'s Javadoc).
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
  (integers clamped), else the type's zero; it never throws for the data,
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
  harness H3).
* **`Job.join()` throws when the build failed** (bergdb 020-10, section
  3.2; Frans, 2026-11-09): `join()` and `join(millis)` of a build that
  ended FAILED throw the new `bergdb.pub.util.IndexBuildException`,
  unchecked, at every call, also on the job of `Database.indexJob(name)`,
  as `Future.get()` throws for a task that failed. Its `getStatus()` is
  the FAILED status, with the reason as before, and its cause the exception
  that failed the build: a `DataFormatException` for data that the build
  cannot take, such as an object of format 1, another `RuntimeException`
  for a bug, none when the index was deleted during its build. Before, they
  returned the status, and `start().join()`, the natural call, passed a
  failed build silently. They return as before otherwise: ACTIVE, or
  BUILDING after a stop, a time-out or an interrupt; `Job.getStatus()`
  never throws. `IndexBuildException` is not a `DbException`: a failed
  build is neither a refusal nor a failure of the database, which goes on.
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
  never says true before a `next()` that throws. `Database.PRIMARY` is
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
* **A start's heap** (bergdb 019-45): a start needs about twice the
  startup distance of heap above what the running database needs,
  whatever the cache budget (docs/levels.md, section 7); W7's 600 MB heap
  at a 200 MB startup distance was too small for a start.
