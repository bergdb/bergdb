# 020-24-15 A new user who learns BergDB by copying the documentation

Created 2026-11-09 by Frans Lundberg.

A new user of 2026.4 learns BergDB by copying its documentation (u15, for coord-1109,
round 5 of the common brief of 020-24). Each code example in the public documentation was
compiled and run exactly as written, against the release jar alone. Then the documentation
was read as a whole, looking for places that contradict each other, links that lead
nowhere, and claims about 2026.4 that today's changes made false.

The jar and the Javadoc were built from a clone of main at `b0eba12`, with `java/build.sh`
and `java/javadoc-pub.sh` (JAVADOC PUB OK). Main's `java/`, README.md and
`releases/next.md` are unchanged since then (main at `48d2b00`), so the line numbers below
hold for both. The implementation was read only to settle which of two texts is right.
Nothing in BergDB was changed.


## 1. The application

Everything is in `/Users/f/fl/bench/2026-11-09/app-u15/app/`. `run.sh` runs every
example, compares the output with what the documentation shows, and exits with 1 on a
difference. Its last run printed ALL EXAMPLES OK. The parts:

* `overview/Demo.java` is the overview's first program, as it stands. It is run from
  source, as the overview shows: `java -cp <jar> Demo.java put`, then `get`, `delete` and
  `get`, on JDK 27 and on JDK 17.
* `pkg/Hello.java` is the package page's "A first program". Every example that follows on
  that page is pasted in order at the end of its try block, as the page says to do.
  `Account` goes beside main, and the two imports the page names are added. The output is
  compared with the examples' `//` comments, line by line.
* `ex/Examples.java` holds the class Javadoc examples:
  * `Database`'s try-with-resources;
  * `IndexBuilder`'s "by-salary", with an `Employee` class, which the example assumes;
  * `UseIndexBuilder`'s two scans, with the `Payment` and `Person` classes and the
    "by-from-amount" and "by-name" indexes that they assume;
  * `WBuilder`'s put and delete;
  * all 15 time strings of the table and ABNF in `Time.resolve()`, at a fixed current time,
    and `Time.utc()` of the absolute ones.
* `core/CoreEx.java` holds the two examples of the Core API in `Db`'s class Javadoc: the
  write, read and close on a `FileStream`, then the optimistic retry loop with
  `RerunException`, with a small `increment()`, which the example assumes.
* Probes of the rules that the text states around the examples:
  * `rules/Rules.java`: object keys and suffixes (".OBJ", "x.", "/v1.2/k"), a get as
    `Object.class`, an array or a wrapper put at a key, and the null refusals;
  * `rules/NotDir.java`: `create()` and `open()` of a regular file;
  * `../old/`: a database encrypted with release 2026.3's jar and its `CryptoKey`, started
    with 2026.4, with and without its `created.txt`.

About 400 lines of Java. There are no code examples in README.md, the `bergdb.pub.util`
package page or `releases/next.md`. The other Javadoc snippets are inline call shapes, such
as `c.get(..)`.

To check consistency, `releases/next.md` (1,202 lines) was compared entry by entry with the
Javadoc of the methods it names. The Javadoc of `bergdb.pub`, `bergdb.pub.util` and `Db`
was read for rules that it states in two places. Every `href` and anchor of the generated
Javadoc was checked by a script, as were README.md's links.


## 2. The findings

All the findings are in the documentation: no example gave a wrong result. U15-1 to U15-5
are contradictions that a user would act on.

| ID | Kind | Severity | What |
|---|---|---|---|
| U15-1  | doc      | medium | The Core's `Db` is API, but no published Javadoc has it                |
| U15-2  | doc      | medium | `WBuilder.execute()`: spent "whatever it threw", and also unspent      |
| U15-3  | doc      | medium | `close()`/`stop()`: use nothing more; `sync()` after `close()` works   |
| U15-4  | doc      | medium | next.md: a String is "never" a format-1 object; the Javadoc: it can be |
| U15-5  | doc      | low    | `InternalDataException`: "restart" against "the database goes on"      |
| U15-6  | doc, API | low    | Exceptions that calls throw are named from non-API packages            |
| U15-7  | doc      | low    | `start()`: `StreamIoException` for a non-directory, also for `open()`  |
| U15-8  | doc      | low    | `create()`: "gets a new database" and then "refuses" in one comment    |
| U15-9  | doc      | low    | `Connection`: "a single thread" against "one thread at a time"         |
| U15-10 | doc      | low    | Six next.md entries that today's Javadoc and code made stale           |
| U15-11 | code     | low    | Three `FileStream` test methods are public again                       |
| U15-12 | doc      | low    | The overview runs its demo with `bergdb.jar`, not the users' jar       |
| U15-13 | doc      | low    | Developer notes on the users' package pages                            |
| U15-14 | doc      | low    | Two refusals that next.md states and the method Javadoc leaves out     |

The details. Paths are under `java/src/bergdb/` unless given in full.

* **U15-1. The Core's `Db` is API, but no published Javadoc contains it.**
  * Three places say that the API is `bergdb.pub`, `bergdb.pub.util` and the Core's
    `Db` "with the types of its signatures": README.md (Build and test),
    `java/src/overview-pub.html:88` and `pub/package.html`, "The API and its jar".
  * `java/javadoc-pub.sh:25` builds only `bergdb.pub` and `bergdb.pub.util`. The Javadoc
    zip of release 2026.3 holds no `bergdb/core` file.
  * So Db's documentation is found only in the source: its two examples, its key kinds and
    its threads. So are the types that a user of `Db` needs: `DbBuilder`, `Trans`, `Keys`,
    `GetMany`, `Kvt`, `FileStream`, `MemoryStream` and `RerunException`. The
    `doc-files/key-encoding.md` that Db's Javadoc cites is in the jar, and no page links
    to it.
  * Both examples compile and run as written.
  * Fix: give `javadoc-pub.sh` the source files of `Db` and of those types (javadoc takes
    single `.java` files) and copy `core/doc-files`. Or, if that is not wanted for 2026.4,
    say in the overview's last paragraph that Db's documentation is its source comment, in
    the release's source zip.
* **U15-2. Is the builder spent when `WBuilder.execute()` throws? The Javadoc gives two
  answers.**
  * `pub/WBuilder.java:14` says "execute() spends the builder, whatever it threw".
    `:80-81` says "also if this method throws". next.md:427-431 says "also when
    `execute()` threw".
  * `pub/WBuilder.java:20-22` (021-22) says that execute() "throws IllegalStateException,
    and leaves the builder unspent, while another thread is in a call of the connection".
  * The code agrees with `:20-22`: `connection.enter()` throws before the builder is
    marked spent.
  * Fix: at `:14`, `:81` and in next.md 020-21, add "except for the IllegalStateException
    of a busy connection, which leaves it unspent". Name that case in `:84`'s
    `@throws IllegalStateException`.
* **U15-3. After `close()`, use nothing more, but `sync()` works.**
  * `pub/Database.java:182` (close()): "this Database object must not be used anymore".
  * `:137` (stop()): "After this method, call only close() on this Database".
  * `:239-242` (sync()), changed today (U10-6, `10335ee`, next.md:651-657): "If it is
    durable, this method returns, also then: after close(), or after stop() once the
    database has closed". next.md's J1 (line 966) says the same of
    `setCacheSizeInMb()` after `stop()`.
  * Fix: in stop() and close(), "then call only close(), sync() or setCacheSizeInMb()",
    or name the calls that are allowed after them in one place and refer to it.
* **U15-4. Can a String be taken for a format-1 object? next.md says never, and is
  wrong.**
  * next.md:185-187: "A `String` value is never taken for such an object, whatever its
    first bytes".
  * `pub/Connection.java:229-233`, `UsePrimaryBuilder.java:33-35` and
    `IndexBuilder.java:36-39` say that a String whose bytes are a whole object of
    format 1 is taken for one.
  * The Javadoc is right: "bergo\u0001\u0000\u0000", put as a String and read with a get
    as `Object.class`, throws `ObjectCreationException` ("format-1"). Only a String
    *put* into an indexed directory is never refused for it.
  * Fix next.md: "A String value that only begins with `bergo` and the byte 1 is no
    longer taken for such an object, and its put into an indexed directory is never
    refused; one whose bytes are a whole object of format 1 still is."
* **U15-5. Does an `InternalDataException` mean a restart?**
  * `pub/util/DbException.java:20-21`: "Corrupt internal data (InternalDataException)
    means that the stream does not work either; restart the database."
  * `pub/Connection.java:327-330` (`transactionInfo()`, 021-17) and next.md:530-531:
    refused "with `InternalDataException`, and the database goes on". Db's class Javadoc
    ("BergDB's keys"): "refused with InternalDataException, at a start or at the read that
    meets it". The code only throws; it does not fail the database.
  * Fix `DbException`: "Corrupt internal data (InternalDataException) refuses the call
    that met it, and the database goes on; the data stays as it is."
* **U15-6. Exceptions that calls throw are named from packages that are not API.**
  * In 21 places, the Javadoc of `bergdb.pub` and `bergdb.pub.util` names what a call
    throws, or its cause, by classes of `bergdb.storage` (`StreamIoException`,
    `StreamFormatException`, `VersioningStreamException`), `bergdb.stream`
    (`DirectoryInUseException`) or `bergdb.core` (`InternalDataException`). Examples:
    `pub/DatabaseBuilder.java:160-163` and `:197-215`, `pub/Database.java`'s sync(),
    `pub/util/IndexBuildException.java:14`.
  * None of these classes is API by "The API and its jar", and none is in the published
    Javadoc. All of them are `DbException`s: the two refusals of an encrypted database
    were `instanceof DbException` in the probe.
  * But a user who must tell "directory in use" apart has to test the cause against
    `bergdb.stream.DirectoryInUseException`, a class that may change in any release.
  * Fix: say once in "The API and its jar" that these are `DbException`s, named for their
    messages, and that an application catches `DbException`. For Frans's API list: an API
    exception, or a method, for "directory in use".
* **U15-7. `start()` names `StreamIoException` for a path that is not a directory, for
  `open()` too.**
  * `pub/DatabaseBuilder.java:203-205` (`@throws DbException`): "a StreamIoException if
    the directory of create() or open() cannot be opened or listed (... a path that is not
    a directory)".
  * `:44` and `:229` say `DatabaseMissingException` for `open()`.
  * The probe agrees with `:44`: `create("afile")` threw `StreamIoException`
    "Directory afile could not be opened: it exists and is not a directory", and
    `open("afile")` threw `DatabaseMissingException` "No database in afile: it is not a
    directory".
  * Fix `:205`: "a path that is not a directory, for create()".
* **U15-8. `create()` gives a new database, then refuses one, in one comment.**
  * `pub/DatabaseBuilder.java:21-24`: "a directory that holds no stream file (*.bergdb)
    with a byte ... gets a new, empty database".
  * `:28-30`: start() refuses one that has `created.txt` and no stream file with a byte.
  * Fix `:22`: "a directory that holds neither created.txt nor a stream file (*.bergdb)
    with a byte".
* **U15-9. A connection: "a single thread" or "one thread at a time"?**
  * `pub/Connection.java:13-14`: "A Connection object assumes it and any objects returned
    from its methods are accessed from a single thread".
  * `:16-26` ("Threads", 021-22) says one thread at a time. It also defines a `WBuilder`
    that threads share, and an `rw()` environment that several threads use.
  * Fix: replace the sentence with "A connection is used by one thread at a time
    (Threads, below)".
* **U15-10. Six next.md entries that today's Javadoc and code made stale.** In each case
  the Javadoc is right, and the fix is to next.md.
  * 966-967 (J2): "only `DbObject.toDbObject()`'s message names the place of a lone
    surrogate". A put names it too (`pub/WBuilder.java:64-66`,
    `pub/package.html:296-301`, next.md:98; a put threw "The string at 'inner.names[3]'
    has a lone surrogate").
  * 106-107 (021-07): "an index update that reads such a previous value throws
    `DataFormatException`". `pub/IndexBuilder.java:27-33`, rule 1: such a value has no
    entry, and a put over it or a delete of it works.
  * 338-339: "`hasNext()` never says true before a `next()` that throws".
    `pub/UseIndexBuilder.java:32-35`: before one that throws `NoSuchElementException`; a
    conversion that throws, and `LookupTimeNotAvailableException`, come from `next()`.
  * 1183: "a field of a type variable is not stored". `pub/package.html:286-293`, next.md:231
    and the code: the class is not a Data Object, and is refused at a put and at a get.
  * 911: "the overview ... link to it" (Strings). `overview-pub.html` has no such link.
  * 118-127 (021-08) gives limits of 1,001 objects and 2,001 objects and arrays as the
    rule, which format 2's 16 levels replaced (next.md:150-156,
    `pub/DbObject.java:38-39`). Fold it into 020-08, or start it with "replaced by".
* **U15-11. Three `FileStream` test methods are public again.**
  * `stream/FileStream.java:3108`, `:3145` and `:3177` are public static tests that came
    today with `2557286` (021-20) and `5ca4249` (U10-5).
  * next.md:1160-1162 says that the test methods of `FileStream` and the other types of
    Db's signatures are no longer public, so that their Javadoc does not list them.
  * Fix: make the three tests package-private.
* **U15-12. The overview runs its demo with `bergdb.jar`.**
  * `java/src/overview-pub.html:65-71`: "with BergDB's jar (here bergdb.jar)".
  * README.md says that `bergdb.jar` holds the tests and tools of `src-dev`, and that
    `bergdb-release.jar` is the jar for users. A release ships `bergdb-2026.4.jar`.
  * Fix: "(here bergdb-2026.4.jar)" in the text and the four command lines.
* **U15-13. Developer notes on the users' package pages.**
  * `pub/package.html:413-419`, "The package's dependencies": nanotest, the @Nano
    methods, pubimp, and the circular package dependency "by design".
  * `pub/util/package.html:5-9`: "Technically, this package is important to avoid
    circular package dependencies".
  * A user of the API cannot use any of this.
  * Fix: make them HTML comments, or move them to a developer note.
* **U15-14. Two refusals that next.md states and the method Javadoc leaves out.**
  * next.md:183-185 and 842-843: a start of a database with an index definition of
    2026.3 throws `VersioningStreamException`. The package page says it ("Objects": "does
    not start"); `DatabaseBuilder.start()`'s `@throws` (`:197-232`) does not.
  * next.md:396-404 (020-14, X3): a Data Object class in a package that its module does
    not export to BergDB is refused. The Data Object rules (`pub/package.html:275-293`)
    leave it out.
  * Fix: one line in each.

Checked, and in agreement with the text:

* Every example: its output is as shown, character for character.
* Both refusals of an encrypted database: with its `created.txt`, a
  `VersioningStreamException` that names the key and says how to move the data; without
  it, a `StreamFormatException`, "Invalid magic bytes ... 2026.3 or before, encrypted
  it". Each start wrote nothing.
* No text offers encryption any more. `DatabaseBuilder.start()`, the package's
  "Encryption", next.md and `Db` agree.
* The suffix rules: ".OBJ" is refused; "x." and "/v1.2/k" are object keys. A String at an
  object key, read as `Object.class`, gives a `byte[]`. An array and a wrapper are stored
  in the fields "array" and "p". A null value and an unset array element are refused.
* The limits, stated in several places and the same in each: 2^31 - 9 bytes, 1.88 GB, 16
  levels, 255 bytes, 1 to 8 index levels, 4,096 bytes, the 10 MB write buffer, 50 ms, the
  clamps 5 to 1000 and 4 to 100,000, and the retain duration's default.


## 3. What went well

* Copying works. Every example in the overview, on the package page, in the class
  Javadoc and in Db's Javadoc compiles and runs as written, and prints exactly what its
  comments say. The overview's program runs from source on JDK 17 and 27, as the
  overview says.
* The package page's examples build on each other, as it says. Pasted in order into its
  first program, they ran on the first try. Only the two imports that the page names
  were needed.
* The links: every `href` and anchor of the generated Javadoc resolves, and so does every
  link of README.md. `javadoc-pub.sh` is clean under doclint.
* The removal of encryption is complete in the user's documentation. The refusal of an
  old encrypted database tells the user what happened and what to do, in both cases.
* The many hands of today left few real contradictions in the Javadoc: four in the
  method texts (U15-2, U15-3, U15-5, U15-7). Most of what disagrees is next.md lagging
  behind the Javadoc.


## 4. Fixes

By fixer x28 for coord-1109, 2026-11-09, in `/Users/f/fl/bench/2026-11-09/clone-x28`, branch
`x28-rebased` (worktree `clone-x28-rb`), on main at `b3a6b05`. Documentation only: no change
of behaviour, no API added. The calls after `stop()` and `close()` were probed for U15-3; the
others were settled by reading the code.

* U15-1, the documentation part: `ebfd835`. The overview, README.md and the package's "The
  API and its jar" say that the documentation of the Core API is its Javadoc in the source,
  from `java/src/bergdb/core/Db.java` on, in the release's source zip; `javadoc-pub.sh` is
  unchanged. Whether to publish it: question Q1 below.
* U15-2: `ebfd835`. `WBuilder`'s class text, `execute()` and next.md's 020-21 entry say that
  an `execute()` refused because another thread is in a call of the connection leaves the
  builder unspent (`WBuilderImp.execute`: `enter()` throws before `spent` is set).
  `execute()`'s `@throws IllegalStateException` names that case.
* U15-3: `ebfd835`. A probe of every `Database` call after `stop()`, after the background
  close, and after `close()`, for a file and a memory database. Every read and transaction
  through any connection, `setRetainDuration()`, `setStartupDistanceInMb()`, `deleteIndex()`
  and an `IndexBuilder`'s `start()` throw `IllegalDbStateException` (`DbStoppingException`).
  `close()`, `stop()`, `sync()`, `setCacheSizeInMb()`, the getters, `connection()`,
  `newConnection()` and `indexJob()` are taken. `stop()` and `close()` now say exactly that.
* U15-4: `ebfd835`, next.md's 020-08 entry, as proposed.
* U15-5: `ebfd835`. `DbException`: malformed internal data refuses the read or the start that
  meets it, and a running database goes on. The `InternalDataException`s of a transaction's
  index entries come before its go point (`RwTransaction`); those of reclaim's state come at
  the start (`Reclaim.initFromDb`).
* U15-6: left. It is an API question: Q2 below.
* U15-7: `ebfd835`. "a path of create() that is not a directory".
* U15-8: `ebfd835`. "neither created.txt nor a stream file (*.bergdb) with a byte".
* U15-9: `ebfd835`. "A connection is used by one thread at a time (Threads, below)."
* U15-10: `ebfd835`. All six next.md entries. For 021-07, a probe confirmed the text: a
  malformed object in an indexed directory, a put over it and a delete of it worked, and the
  index held the new value.
* U15-11: `6cdd63f`. The three tests are package-private. Nano's `TestRunner` takes
  `getDeclaredMethods()`, and the other tests of `FileStream` are package-private already.
  `unit.sh -c FileStream` ran all 40 unit tests.
* U15-12: `ebfd835`. `bergdb-2026.4.jar` in the text and in the four command lines.
* U15-13: left. These are developer notes, and they are not wrong.
* U15-14: `ebfd835`. `start()`'s `@throws` names the `VersioningStreamException` of a
  database with an index of 2026.3 (`IndexManager.start`). The Data Object rules name X3.
* From 006-18-03: `b5f6bad`, next.md's Platforms. The 200 MB default budget is the Core's
  (`DbBuilder.cacheSizeIndicator()`; the check's `KillDemo` used `Db`), above the 192 MB
  heap, so an application of the Core sets a smaller one, such as 50 MB. The Pub API's
  default is a fifth of the heap (`DatabaseBuilder.cacheSizeInMb()`), about 38 MB, so it
  fits.

Questions for Frans:

* Q1 (U15-1). Should the Javadoc of the Core API be published? 020-27 named its classes
  today in `Db`'s "The Core API".
  * Recommendation: yes, but in the release after 2026.4. `javadoc-pub.sh` would take the
    named classes as single source files and copy `core/doc-files`.
  * Not tonight: their doclint and their links to internal classes are untried, and 2026.4's
    users have the pointer to the source.
* Q2 (U15-6). The Pub Javadoc names exceptions of packages that are not API:
  `StreamIoException`, `StreamFormatException`, `VersioningStreamException`,
  `DirectoryInUseException` and `InternalDataException`, in 21 places. All of them are
  `DbException`s.
  * Recommendation, for 2026.4: one sentence in "The API and its jar" saying that they are
    `DbException`s, named for their messages, and that an application catches `DbException`.
  * For the next release: an API way to tell "directory in use" apart, such as
    `bergdb.pub.util.DirectoryInUseException` or a method. An application needs it to choose
    between a retry and a failure.
