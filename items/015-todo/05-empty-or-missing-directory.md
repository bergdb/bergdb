015-05. Decide: a start on an empty or missing directory creates a database
===========================================================================

Status: open. Kind: Decide. Created 2026-11-03 by Frans Lundberg.

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
