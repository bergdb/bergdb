015-05. Decide: a start on an empty or missing directory creates a database
===========================================================================

Status: done (2026.3): decided 2026-11-05, `create(p)` and `open(p)`,
`dir(p)` removed; made the same day (see Log). Kind: Decide. Created
2026-11-03 by Frans Lundberg. Closed 2026-11-05.

For Frans, after release 2026.2. 015-01's case 3: a volume that is not
mounted, or a wrong path. The directory is empty or missing; the start
creates it (with its missing parents, `mkdirs`) and a new database in it,
and says nothing. 015-01's fix (A with A+) covers cases 1 and 2, where
`created.txt` shows that a database was there; it cannot cover case 3
without a change of the Pub API's usage.

The options (015-01, "The options"):

* B1: `start()` refuses a directory with no stream byte unless the
  builder was told `createIfMissing()` (as LevelDB's and RocksDB's
  `create_if_missing`, false by default). Covers case 3. Every program
  that creates a database must call it: about 40 builder calls in the
  repository, the Javadoc's examples and README. A new setting (P10).
* B2: the opposite default, with a new `mustExist()`. Compatible, but
  protects only the programs that call it; 015-01's Javadoc recipe (check
  `created.txt` before `start()`) gives the same with no new method.
* E: create only the last directory (`mkdir`, not `mkdirs`). Covers a
  missing mount point (macOS's `/Volumes/X`), not an empty one (Linux's
  `/mnt/x`). Changes `dir()`'s promise.
* Nothing more: case 3 stays a known issue, with the recipe.

What other databases do
-----------------------

How other databases treat a start, or an open, of a database that is not
there. From their documentation as Claude knew it on 2026-11-05, not
checked again against their current versions.

Refused unless the program asks for a new one:

| Database | How a program asks for a new one |
|---|---|
| LevelDB, RocksDB | `Options.create_if_missing`, false by default; `error_if_exists` refuses an existing one |
| Berkeley DB (C) | `DB_CREATE` to `DB->open` and `DB_ENV->open`; with `DB_EXCL`, an existing one is refused |
| Berkeley DB Java Edition | `EnvironmentConfig.setAllowCreate(true)`, false by default |
| Apache Derby | `;create=true` in the JDBC URL; without it, a missing database is "not found" |
| PostgreSQL | `initdb` makes a cluster; the server refuses a data directory without one |

Created by default, with a way to refuse:

| Database | Default, and the way to refuse |
|---|---|
| SQLite | `sqlite3_open` creates the file; `sqlite3_open_v2` without `SQLITE_OPEN_CREATE` refuses |
| H2 (embedded) | creates; `IFEXISTS=TRUE` in the URL refuses (a server creates none by default since 1.4.198) |
| HSQLDB | creates; the property `ifexists=true` refuses |

Created by default, with no flag:

| Database | What happens |
|---|---|
| MongoDB | databases and collections are made at their first write |
| Redis | without its dump or append file, the server starts empty |

The directory: none of these creates missing directories for its
database. SQLite creates the file but not its directory; LMDB's
`mdb_env_open` requires an existing directory (it creates the files in
it); `mongod` refuses a `--dbpath` that does not exist, and Redis a `dir`
that does not exist. BergDB's `dir()` creates the directory and its
missing parents (`mkdirs`), so a path below a volume that is not mounted
gets a new database on the volume beneath.

The same two forms in files: POSIX `open` creates only with `O_CREAT`
(and refuses an existing file with `O_EXCL`); Java's
`Files.newOutputStream` creates by default (`CREATE`), and `CREATE_NEW`
refuses an existing file.

In short: the storage engines nearest to BergDB (LevelDB, RocksDB,
Berkeley DB) refuse by default; the embedded SQL databases (SQLite, H2,
HSQLDB) create by default and offer a way to refuse; none creates missing
directories.

Recommendation: B1 in the next release with a public API, since it is
the only option that covers case 3, and 2026.2 is internal (016-01, D1);
until then the recipe. Frans decides.

The decision
------------

Frans, 2026-11-05, 11:34, in a discussion with session bergdb-e8 (after
his view at 11:12 that an application checks its own state after a start
anyway, and that he likes the simple `dir(p).start()`):

    Factory.database().create(p).start();  // like today, creates if needed
    Factory.database().open(p).start();  // opens an existing database in p or throws

"'Create' obviously allows creation. I think 'open' is for things that
exists already. Like opening a file. I would expect an exception from
open(p) if p does not exist."

What it means (proposed by bergdb-e8, and Frans's answers at 11:39: "do as
proposed"):

* `DatabaseBuilder.create(p)` is today's `dir(p)`: it opens the database
  in `p`, or creates `p` (with its missing parents) and a new database
  when `p` holds none. 015-01's refusal stays: a directory with
  `created.txt` and no stream byte is a lost database, not a new one. A
  directory with other files and no database gets a new database, as
  today. Java's `StandardOpenOption.CREATE` has the same meaning (create
  if missing, else open); `CREATE_NEW` would refuse an existing one.
* `DatabaseBuilder.open(p)` opens the database in `p`, or throws 015-01's
  `DatabaseMissingException` when `p` is missing, is not a directory, or
  holds no stream byte; it then creates and writes nothing. It covers
  case 3 whole, an empty mount point too.
* `dir(p)` is removed. Its call sites take `create(p)`, and the tools
  that only read an existing database take `open(p)`. `memory()` is
  unchanged.
* No new setting (P10): the intent is in the method that names the
  directory. The check is in `DatabaseBuilderImp.start()`, beside
  015-01's; the Core Layer does not change (P12), nor does the stream.

Superseded: B1 (`createIfMissing()`), chosen on 2026-11-03.

Done when: Frans has chosen, and the choice is an Implement entry or a
known issue.

Found 2026-11-03 in 015-01's study.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:18. Frans: "As recommended." B1 after the release; a known
issue of 2026.2 until then, with the recipe in `DatabaseBuilder`'s Javadoc.

2026-11-05, 11:12. Opened again for discussion by Frans with session
bergdb-e8; "What other databases do" added at his request.

2026-11-05, 11:39. Decided by Frans: `create(p)` and `open(p)`, `dir(p)`
removed (section "The decision"); B1 superseded. The change started by
session bergdb-e8's agent.

2026-11-05. Done by session bergdb-e8's agent, as decided:

* `DatabaseBuilder.create(String)` is `dir(String)` renamed, with its
  Javadoc: its first sentence says that it opens the database in the
  directory or creates one there, as NIO's `StandardOpenOption.CREATE`;
  015-01's paragraph on `created.txt` follows, and the recipe for an
  application that must never create a database is now "use
  `open(String)`". The directory lock's paragraph (005-63, 015-56) moved
  to `start()`, as it holds for both methods.
* `DatabaseBuilder.open(String)` is new. Its first sentence: it opens the
  existing database in the directory and never creates one, and `start()`
  throws a `DatabaseMissingException` if the directory is missing, is not
  a directory, or holds no stream file with a byte. The check,
  `DatabaseBuilderImp.refuseNoDatabase`, is in `start()` after 015-01's
  `refuseMissingStream` (whose message tells more of a directory with
  `created.txt`), before the directory is opened, with
  `FileStream.hasStreamBytes`; so the start creates and writes nothing.
  The builder keeps the directory and a flag; the last of `create()`,
  `open()`, `memory()` counts. `DatabaseMissingException`'s Javadoc names
  the new case.
* `dir(String)` is gone, and so is `DatabaseBuilderImp.dir(File)`, which
  no code called. 49 builder calls moved: 47 to `create(p)` (tests in
  `PubTester` and `PubInterruptTester`, the demos and manual and night
  tests in `src-dev`, `stress/BryanRepro.java`, the overview's example)
  and 2 to `open(p)`: `bergdb.demo.GetStarted3`, which reads the database
  that `GetStarted2` made, and `PubTester.testStopThenReturnFromMain`'s
  read of the child's database. README.md and docs/levels.md show no
  builder call; `java/bench` has none. Tools under `items/` keep `dir(`
  (015-19).
* Tests, in `PubTester`: `testOpenRefusesMissingDirectory` (a missing
  directory with a missing parent; also `create(p).open(p)`),
  `testOpenRefusesFile`, `testOpenRefusesDirectoryWithoutStream` (an empty
  directory, the unmounted mount point; one with another file; one with
  an empty first stream file, which `create()` then makes a database in),
  `testOpenRefusesCreatedTxtWithoutStream`: each asserts the exception and
  that the files under the test's directory, their names, lengths and
  bytes, are as before; `testOpenExisting`, `testCreateMissingAndEmpty`
  (a missing directory with two missing parents, and an empty one) and
  `testOpenEncrypted`. Before the change `open()` and `create()` did not
  exist, so the tests could not fail on the old code; with
  `refuseNoDatabase` switched off, the first three fail.
* 010-01: no new setting (P10), the intent is in the method that names
  the directory; the Core Layer and `DbBuilder` are unchanged (P12), and
  so is the stream (P2); the refusal says what happened and what to do,
  and writes nothing (P7's spirit); no global state (P9); the check lists
  the directory once, as 015-01's (P5); P1, P3, P4, P6, P8 and P11 are not
  touched.
* `releases/next.md`: a "Pub API" section with the change.
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (104 s)`, unit 1167, f 81;
  `stress/core-build.sh unit`: `CORE BUILD OK` (747 tests);
  `javadoc-pub.sh`: `JAVADOC PUB OK`.
