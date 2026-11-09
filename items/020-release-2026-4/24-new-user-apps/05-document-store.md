# 020-24-05 A document store behind a small service

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u5, for coord-1109, round 2
of the common brief of 020-24): only the release jar on the class path, built from a clone
of main at `cf287ad`, and only what a user reads (README.md, `java/src/overview-pub.html`,
the Javadoc of `bergdb.pub` and `bergdb.pub.util`, `releases/next.md`). The implementation
and 020-09 were read only afterwards, to explain U5-1, U5-2 and U5-3.


## 1. The application

A document store behind a web-style service: a class whose public methods are the
requests (`DocStore.java`), and a main that drives it end to end and checks every result
(`DocStoreApp.java`). `Probes.java` holds what a user tries beyond the main flow. All are
in `/Users/f/fl/bench/2026-11-09/app-u5/app/`, with `run.sh`, which compiles them and runs
three JVMs one after the other (write and check; open again with a cache of 4 MB and check
every value again; the probes), prints `APP OK`, and then runs the reproductions of U5-1
and U5-2, which print what they meet. The output of the last run is `run.txt` there. The
minimal reproductions are in `/Users/f/fl/bench/2026-11-09/app-u5/probe/`.

How it uses BergDB:

* Documents are Data Objects at object keys under `/docs/`: `Document` with nested `Meta`,
  `Author[]`, `Section[]` (recursive by type, with `Paragraph[]` and `String[][]` cells),
  `String[]`, `byte[]`, `Double`, `Integer[]`; `AllTypes` with every type of the closed
  list (the eight primitives, their wrappers, `String`, `byte[]`, arrays of each, arrays of
  two and three dimensions, objects, arrays of objects and arrays of arrays of objects).
  A PUT is one `rw()`: the document and the service's markers of its directories.
* Attachments are `byte[]` values in the directory named by the document's key: the
  document `/docs/files/report` has `/docs/files/report/a-0.bin` and so on; a DELETE of a
  document deletes its attachments in the same transaction.
* A listing is a page of `usePrimary(type).dir(d).kvs()`. The first page calls
  `freezeLookupTime()` and reads its time with `getLookupTime()`; the token of the next
  page is `UNITS/NAME`, the time and the last name, and later pages read at that time with
  `startAt(NAME).inclusive(false)`, forward or `backward()`.
* Subdirectories: BergDB lists a directory's own keys only, so each PUT also writes
  `/dirs` + parent + child + `.d` for each directory of its key (U5-5), and a browse walks
  those.
* History: the versions of a document by `get()`, `transactionInfo().time()` t, and a get
  at t minus one unit, back to its creation or a delete (U5-11); an undelete reads the
  document at a time before the delete.
* Generic access: each document read as a `DbObject` and walked with the names of its
  Java class (`DbCheck.java`), through the typed getters, `getDbValue()`, `getType()`,
  `has()`, the nested getters and `DbArray`'s elements.
* An index of a shelf by a nested field, `meta.author.name`.

What it checks, and exits with 1 on a wrong result:

* Every document field by field, as its class (`Deep.java`: doubles by their bits, one NaN,
  -0.0 kept) and as a `DbObject`; its stored bytes equal `DbObject.toDbObject()`'s;
  `toJavaObject()`; `get(key, Object.class)`. 600 random documents (strings of every plane,
  controls, NUL, noncharacters, ZWJ sequences, combining marks, texts of 1,000 to 21,000
  code points, null fields at random, empty strings and arrays, NaN, ±Infinity, extremes
  of each integer type) and 40 objects of `AllTypes`, with up to three more nested in
  each, and lone surrogates in `char`, `char[]` and `Character[]`.
* The depth limit: chains of 14 to 18 objects (16 stored, 17 refused naming the path,
  nothing written), 300 random documents with sections up to 8 deep, stored exactly when
  the application's own count of levels is at most 16 (294 stored, 6 refused); in the
  probes, arrays of 15 and 16 dimensions in an object and at a key, the Builders at 16 and
  17 levels, names of 255 and 256 bytes, 32,767 fields and the 32,768th.
* 53 names of keys a user tries (spaces, `.`, `..`, `x.`, `a.b.c`, `x.OBJ`, emoji, NUL,
  tab, newline, U+FEFF, U+FFFF, `#i`, `${transactionTime}`, names of 255 to 10,000 chars),
  each put, got, `exists()` and listed once, in code point order (U+FFFD before U+1F600);
  é precomposed and decomposed as two keys; keys 10, 100 and 1,000 directories deep; a key
  that is also a directory.
* A tree of 2,066 documents in 40 directories under three tenants (`acme`, `bolag åäö`,
  `😀 co`), found by the markers and listed in pages of 7 and of 1,000, forward and
  backward, against the model; a writer adding 300 documents and deleting 34 in one
  directory while the reader pages through it, each listing equal to the state at its
  token's time.
* Attachments of 0, 1, 2, 127, 128, 255, 256, 65,535, 65,536, 2^20 - 1, 2^20, 2^20 + 1
  bytes, 3 MB and 8 MB, a 2 MB one with a non-ASCII name and a 5 MB `byte[]` field, by
  content and SHA-256, after a restart with a cache of 4 MB.
* Schema evolution over three versions of an article class: int to long and long to
  String, a field renamed, added (with and without an initial value) and removed, String
  to String[] and to an object, String[] to Tag[], double to int, boolean to String; each
  version's data read by each version's class, the documented results checked, the others
  printed (`SCHEMA` lines in `run.txt`); an old class updating a new document in `rw()`.
* 50,000 documents in one directory, paged 100 at a time: the first page 0.3 to 2.3 ms,
  the slowest 4.6 to 32 ms under a machine load of 25 to 40; a page from a name in the
  middle.

Size: `DocStoreApp.java` 935 lines, `Probes.java` 491, `Gen.java` 256, `DocStore.java` 227,
`Docs.java` 187, `DbCheck.java` 175, `Deep.java` 102, `run.sh` 17; 125 calls of `check()`,
about 11,700 checks in a run of the writer, 11,400 in the verifier. A run takes about 16
seconds on F53 under a load of 25 to 40, and writes about 60 MB.

The last run: every check passed; the reproductions of U5-1 and U5-2 show both bugs.


## 2. The findings

Most severe first. A reproduction names a file in `probe/longkey/`, `Probes.java`, the
application's `DocStore.java`, or the application.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U5-1  | bug | critical | a key of 90 KB is stored; the next start overflows    | LongKey6 |
| U5-2  | bug | high     | a 1 MB key sharing a 100 KB prefix fails the database | LongKey4 |
| U5-3  | doc | medium   | a get may give null elements that a put refuses       | Probes   |
| U5-4  | API | medium   | no free-form part in a document, no field names       | Probes   |
| U5-5  | API | medium   | no listing of subdirectories, no delete of a tree     | the app  |
| U5-6  | doc | low      | Data Object rules missing: final and hidden fields    | Probes   |
| U5-7  | doc | low      | conversions not given: a char to "65", bytes to text  | Probes   |
| U5-8  | doc | low      | the suffixes are case-sensitive: `x.OBJ`, `notes.TXT` | Probes   |
| U5-9  | API | low      | messages: the internal key, ".obj" obsolete, "ukey="  | Probes   |
| U5-10 | API | low      | `DbObject.toString()` is "o"; no `equals()`           | Probes   |
| U5-11 | API | low      | no call for a key's versions                          | DocStore |

Met again, found by round 1: I-1 (a double into an int is cut toward zero: 4.7 gives 4,
{1.5, 2.5, -0.5} gives {1, 2, 0}, where the Javadoc says "the nearest value"), I-2 (a
`DbObject` cannot list its fields; part of U5-4), I-4 (an older class's update drops the
newer fields: `headline` and `authors` gone after a v1 `rw()` of a v3 document), I-7
(`DbObject.Builder` has no `addDouble`, `addBoolean` or `addByteArray`: `addDbValue(new
DbDouble(x))`), U1-3 (the format of `${transactionTime}`: 18 digits with leading zeros, so
`"/inbox/" + t.units()` misses the key that a POST made).

### U5-1. A key of about 90 KB is stored, and the next start overflows (bug, critical)

A put at a key whose UTF-8 has about 90,000 bytes or more commits, reads back, lists and
closes without an error; the next start throws `StackOverflowError` from
`DatabaseBuilder.start()`, and the database does not open. Nothing in the Javadoc limits a
key's length (`Connection`, "Keys": it starts with '/', has at least one more character,
does not end with '/', and has no "//" and no lone surrogate), and no put refuses a long
key. In the runs, with the JVM's default stack: keys of 50,007, 58,898 (10,000
directories deep), 60,007, 70,007 and 80,007 bytes started again; keys of 90,003 bytes
(ASCII, or 45,000 'é'), 100,003 (25,000 emoji), 100,007 and 128,898 (20,000 directories
deep) did not. With `-Xss16m` the same start works and the value is there, so no data is
lost, but a user does not know that.

```java
// probe/longkey/LongKey6.java, shortened
String key = "/d/" + "k".repeat(100000) + ".txt";
try (Database db = Factory.database().create("db6").start()) {
    db.connection().put(key, "v");                 // ok, and the close is ok
}
try (Database db = Factory.database().open("db6").start()) {   // StackOverflowError
}
```

Why, read afterwards: the start ends with `DbStarter.postStartupCheck()`, whose
`checkThatValueNodesHaveSpos()` walks every node in memory with `Dag.visitMemoryNodes()`,
which recurses in `visitNodeWithChildren()`, one frame per level of the key tree. A key is
a tree of 8-byte segments (the Core's `key-encoding.md`, "skey"), so a key of N bytes has
about N / 8 levels: the trace of the 100 KB key has 12,345 frames of
`visitNodeWithChildren`. Any other recursive walk of the key tree has the same bound
(U5-2 is one). Why critical: data that was written and acknowledged cannot be opened at
the next start, found only then; a service that takes its keys from its clients, as a
path in a URL, can be made to fail its next start by one request with a long path.
Suggested: a maximum key length in the Javadoc, refused at every call that takes a key
with `IllegalArgumentException` (the Core's calls too), or walks without recursion.

### U5-2. A 1 MB key after a 100 KB key of its prefix fails the database (bug, high)

In a memory database or a directory: a put at `"/d/" + "k".repeat(100000) + ".txt"`, then
a put at `"/d/" + "k".repeat(1000000) + ".txt"`: the second put throws
`StackOverflowError`, and the database has failed: every later call throws
`DbFailedException` with the `StackOverflowError` as its cause. A 1 MB key alone, or after
one of 1,000 chars, or two of 300,000 chars, is stored. The Javadoc says that an Error in a
transaction fails the database ("Errors" in `Database`), but the input is legal. In a
directory, the restart then meets U5-1, as the first key is 100 KB. Read afterwards: the
recursion is `Dag.freshTreeBound()`, one frame per segment level of the new key's tree
below the shared prefix. `probe/longkey/LongKey4.java`; `repro.sh` runs U5-1 and U5-2.

### U5-3. A get may give null array elements, which a put of it refuses (doc, medium)

The get is best effort and "never throws for the data": a stored `String[]` read into a
`Tag[]` field gives `[null, null]`, a stored `Tag[]` read into a `String[]` gives `[null]`
(the element's zero). A put refuses a null array element. So a read-modify-write of a
document by a class of another version, the common case in schema evolution, throws:

```java
c.put("/m/basket", basket);              // names: String[] {"x", "y"}
Names n = c.get("/m/basket", Names.class);   // names: Item[] -> [null, null]
c.put("/m/basket", n);                   // IllegalArgumentException: the array element
                                         // at 'names[0]' is null
```

In the application, a v1 `rw()` that reads a v3 article (whose `tags` are `Tag[]`) and
puts it back with one field changed throws the same. It is 020-09's design (section 5.7:
"So a get may make arrays with null elements; a put of the object back is refused"), but
the Javadoc says only "the type's zero (0, false or null)", and a user does not learn that
the object a get gives may not be put back. Suggested: say it in the package's "Objects",
or give an element that cannot be converted no place (a shorter array), or null for the
whole field.

### U5-4. No free-form part in a document, and no field names (API, medium)

A document store holds user-defined attributes beside its typed fields. A Data Object
cannot hold them: a field of type `DbObject` is refused at the put ("its field 'attrs' is
of the type bergdb.pub.DbObject, which BergDB does not store (V9)") and at the get, and a
`Map` is a class of the Java platform. So such a document must be a `DbObject` as a whole,
which has free-form names (`a.b`, `with space`, `😀`, `$ref` work), but which cannot list
its fields: `getFieldCount()` is its only method of that kind (I-2), and `toString()` gives
"o" (U5-10). A generic view of a document (JSON for the service), a PATCH that changes one
field and keeps the others, and a copy that keeps the fields a newer version added, cannot
be written. `DbCheck.java` walks a `DbObject` with the names of the Java class that put it.
Suggested: the field names of a `DbObject` (a list, or an iterator of name and
`DbValue`), a `Builder` from a `DbObject`, and `DbObject` as a field type of a Data Object.

### U5-5. No listing of subdirectories, and no delete of a tree (API, medium)

`usePrimary().dir(d)` lists d's own keys, not its subdirectories', as its Javadoc says. A
user who keeps documents in a tree (`/docs/TENANT/PROJECT/2026/11/doc`) cannot find the
tree's directories, nor delete a tenant: `/docs/acme/` lists nothing although 866 documents
are below it. The application keeps its own markers, `/dirs/docs/acme.d` and so on, written
in each PUT's transaction, which every writer must remember; a document written another
way is not found. A user index covers one directory too, so "the documents by author in
the whole tree" needs one index per directory. Suggested: a listing of a directory's
subdirectories (the Core's keys are ordered with '/' as the byte 1, so a skip from one
subdirectory to the next looks cheap), or a scan of a whole subtree.

### U5-6. Data Object rules that the Javadoc does not give (doc, low)

The package's "Objects" says: "BergDB stores its public fields that are not static and not
transient, and those of its superclasses". Two kinds of such fields are refused instead, at
a put with `IllegalArgumentException` and at a get with `ObjectCreationException`: a
`public final` field ("its field 'created' is final; a get could not set it (V3)"), common
in immutable-style classes, and a field that hides a superclass's field of the same name
("two of its fields are named 'x', one hiding the other (V8)"). `DbObject` and the value
classes are not on the closed list, which the Javadoc's "Not on it" could name. The
messages cite V3, V8, V9 and "bergdb 020-09, section 3", which a user does not have.

### U5-7. Conversions that the Javadoc does not give (doc, low)

The Javadoc names "a text read as a number, a number written as a text" and the zero for
the rest. A `char` is stored as an integer, so a `char` field changed to `String` reads
'A' as "65", and back, "B" into a `char` gives 0: a natural type change (a grade, an
initial) changes the data. A `byte[]` read into a `String` is decoded as UTF-8 ({104, 105}
gives "hi"); `true` into an `int` gives 1, 1 into a `boolean` true, `true` into a `String`
"true", "yes" into a `boolean` false, a `String` into a `char[]` null. Each is reasonable,
but a user learns them by trying. Suggested: the table of 020-09, section 5, in the
package's Javadoc, with a note on `char`.

### U5-8. The suffixes are case-sensitive (doc, low)

An object put at `/k/x.OBJ` or `/k/x.Obj` is refused ("Bad key"), and a `String` at
`/k/notes.TXT` is given by `get(key, Object.class)` as a `byte[]`. The Javadoc writes
".obj" and ".txt" and never says that case matters; a file store meets `README.TXT`. One
sentence would do.

### U5-9. Messages with the internal key and internal words (API, low)

The refusal of an object at `/k/x.OBJ` says "Bad key, expected no suffix (or possibly the
obsolete '.obj' suffix), key was: '/dk/-x.OBJ'.": the key in the Core's encoding, not the
user's, and ".obj" called obsolete where the Javadoc documents it. `get(key,
DbObject.class)` of a `String` at an object key ends with "ukey=/g/str"; a get as `String`
of an object (the int 42 put at a key) says "is not well-formed UTF-8", where the value is
an object. Related to U3-6.

### U5-10. DbObject.toString() is "o", and DbObject has no equals() (API, low)

A `DbObject` in a log line or a debugger shows "o" (a `DbArray` "a:2"), whatever its
fields. Two equal objects are not `equals()`; the class Javadoc says to compare
`getBytes()`, so this is documented, but an immutable value class without `equals()` and
`hashCode()` surprises, as in a `Set` or a test's `assertEquals`.

### U5-11. No call for a key's versions (API, low)

A document store shows a document's revisions. BergDB keeps them, but has no call that
lists a key's versions; `DocStore.history()` walks them: a get, `transactionInfo().time()`
t, `setLookupTime(t - 1 unit)`, again, to the creation or a delete (versions 8, 7, 6 of
`/docs/wiki/home`, back to its delete). It works, one read of the storage per version for
`transactionInfo()`, and needs a connection of its own; a call such as `versions(key)`
would say what the walk only implies.


## 3. What went well

* Every round trip was exact, as a class and as a `DbObject`, before and after a restart
  with a cache of 4 MB: Unicode of every plane in values, field names and keys, NUL and
  noncharacters, lone surrogates in `char`, `char[]` and `Character[]`, NaN, -0.0f,
  extremes of every integer type, empty strings, arrays and objects, null fields absent
  and wrapper fields null again, a 5 MB `byte[]` field, attachments of 0 bytes to 8 MB.
* The depth limit is exact: refused at 17 levels and stored at 16, for objects, arrays,
  both mixed and the Builders, and the message names the path
  (`child.child.child.child.child.(6 more).child...`); nothing is written.
* The key rules hold at their edges: every bad key refused by put, get and exists; dots in
  directory names, `.`, `..`, `x.` and `.obj` as the Javadoc says; listings in code point
  order, not UTF-16 order; 10,000 directories deep (58,894 chars) works and restarts.
  Directories named `.`, `..`, NUL, `a\u0000`, emoji and U+FFFF, and 200 names of 20,004
  chars that share a prefix, list and restart right (`probe/dirs/Dirs.java`).
* Eight request threads of the service, 300 PUTs each into shared new directories, each
  `rw()` with its markers: 2,400 documents and 5 markers, none lost
  (`probe/more/More.java`). A directory with no keys of its own above 100,000 keys lists
  in under a millisecond.
* Paging with a frozen time is simple and right: `freezeLookupTime()`, then
  `getLookupTime()` gives the time for the token, and every later page reads that state,
  while a writer adds and deletes in the directory. Paging deep into 50,000 documents
  costs about what the first page does.
* Schema evolution is safe in the cases the Javadoc names: an added field takes its
  constructor's value, a removed one is ignored, int to long, long to String and back, a
  text read as a number and clamped ("9999999999" into an `int` gives 2,147,483,647), int
  to double.
* The error messages of the object model name the class, the field and why (with the
  exceptions of U5-9), and a refusal writes nothing.
* A single-file program in the overview's style (a package-private class run as
  `java -cp jar Doc.java`, its Data Object nested in it) works.


## 4. Fixes

Made 2026-11-09 for coord-1109, in `clone-x25`, by the rule for 2026.4: a
plain bug fixed with a failing test first; elsewhere the Javadoc made true
and complete where the code is as designed; no new API and no change of
meaning. The tests are in `PubTesterJavadocNewUsers`. The commits, with
020-24-04's `e91238f` after them, gated on one tree under the gate lock:
BEFORE COMMIT OK (145 s, unit 1577, f 86), JAVADOC PUB OK.

* **U5-1, U5-2**: fixed by 021-16 (`01d5352`, `520963d`).
* **U5-3** (`084069b`): the package's "Objects" says that a get by another version
  of a class may give an array with null elements, which a put refuses
  (020-09, section 5.7). The alternatives of the finding (a shorter array,
  null for the whole field) change the meaning: for Frans.
* **U5-4, U5-5**: new API, for Frans's list; not done.
* **U5-6** (`084069b`): "Objects" says that a public final field and a field that
  hides a superclass's field make a class not a Data Object (V3, V8), and
  that `DbObject` and the value classes are not on the closed list (V9). The
  messages' "(V3)" and "bergdb 020-09, section 3" are left as they are.
* **U5-7** (`084069b`): "Objects" gives the conversions of 020-09, sections 5.4 to
  5.7, that a user meets: a `char` as its number, "65"; text into a `char`
  as a number; booleans and numbers; bytes and text as UTF-8.
* **U5-8** (`084069b`): "Objects" says that a suffix is case-sensitive.
* **U5-9** (`b81232f`, a plain bug, tests failing first): the refusal of an object
  at "/k/x.OBJ" names the user's key, not "/dk/-x.OBJ", and no longer calls
  ".obj" obsolete; a get as an object of a value that is not one starts "The
  value at KEY cannot be read as an object: " where it ended with " ukey=";
  a get as `String` of an object says that it is an object.
* **U5-10** (`084069b`): `DbObject` and `DbValue.toString()` say that `toString()`
  is a short tag ("o") and that the value classes have no `equals()` of
  their own. A `toString()` with the fields, and `equals()`, are new API:
  for Frans's list.
* **U5-11** (`084069b`): `Connection.transactionInfo()` says how to walk a key's
  versions. A `versions(key)` is new API: for Frans's list.
