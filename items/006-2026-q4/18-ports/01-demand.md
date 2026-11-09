# 006-18-01 Demand and landscape

Created 2026-11-09 by Frans Lundberg. Part of 006-18, the study of BergDB
in languages other than Java. This part asks which languages, and why:
where there is demand for something like BergDB, and where its traits fit.
How a port or a binding is made is the study's other part. Status: done.

Written on 2026-11-09 by pd18, one of the study's two agents, started by
coord-1109. Its web sources were read on 2026-11-09 (section 12).


## 1. In short

* **SQLite holds most of the demand for an embedded store, in every
  language.** Stack Overflow's 2026 survey has SQLite at 42.1 percent of
  respondents, up from 37.5 percent in 2025. DuckDB, the only other
  embedded store found in the list, is at 5.7 percent (W2, W3). Where
  SQLite is enough, BergDB has no
  case. It has a case where the stores in use leave a gap.
* **The gaps users write about are the same in every language:**
  * history kept by hand;
  * files that never shrink;
  * compaction stalls;
  * slow startup or replay;
  * C++ builds and cgo;
  * map-size limits;
  * stores whose maintainers left them.

  BergDB answers history, startup, space and stalls. It does not answer
  write amplification (it has its own), sync, SQL, access from several
  processes, or, for now, a stable format and a permissive licence
  (section 6).
* **The demand for reading the past is clearest where it is now built at
  great cost:**
  * in the browser and in local-first apps (LiveStore, Automerge, Jazz);
  * in Rust (SurrealKV, whose format is not yet frozen);
  * in Go (immudb, under the BSL and with no pruning);
  * on Elixir's Nerves devices (CubDB, with retention done by hand).

  No embedded store with history was found for .NET, Android, Swift or
  Flutter.
* **The ranking (section 9):**

  | Rank | Language or platform                                                 |
  |----|----------------------------------------------------------------------|
  | 1  | Rust                                                                 |
  | 2  | JavaScript and TypeScript: the browser, Node and Bun, one WASM build |
  | 3  | Python                                                               |
  | 4  | Go                                                                   |
  | 5  | C# and .NET                                                          |
  | 6  | Dart and Flutter                                                     |
  | 7  | Java and Kotlin on Android                                           |
  | 8  | Swift                                                                |
  | 9  | Elixir and Erlang                                                    |
  | 10 | Lua                                                                  |
  | 11 | Ruby                                                                 |
  | 12 | PHP                                                                  |

  * C, C++ and Zig are served by the C port (022) as it is.
  * Kotlin on the JVM uses Java's BergDB.
  * Deno drops out: its team joined Cloudflare on 2026-10-09, and its
    development ends after one more year (W52).
* **To study first:**
  1. Rust: a native port, or a crate over the C port.
  2. JavaScript and TypeScript: the C port as WebAssembly, on the
     browser's Origin Private File System (OPFS).
  3. Python: a binding to the C port, shipped as wheels.
  4. Go: a native port, since Go's users avoid cgo.
  5. C#, if there is room for a fifth.

  A cheap check outside the study: Java's BergDB, unchanged, on Android
  13 or later (section 5.10).
* **What is uncertain (section 11):**
  * the demand for reads at a past time is inferred from neighbours and
    complaints; nobody was asked;
  * the AGPL would shrink every row of the ranking;
  * BergDB's write cost at the small startup distances that phones and
    browsers need is not measured;
  * local-first users mostly want sync, which BergDB does not have.


## 2. The question and the earlier work

Frans, 2026-11-09, 12:05: "investigate the feasibility of BergDB ports to
languages than Java. The work on porting the Core to C (022 and earlier
item) has shown that this is feasible with limited human work. [...] The
languages included in the study should be the ones where you think there
is demand for something like it, popular languages, and languages where
BergDB can be implemented from a technical point of view."

There are three ways for a language to get BergDB:

* **A native port of the Core**, and maybe of the Pub layer.
* **A binding** to the C port (012, 022) through the language's foreign
  function interface (FFI).
* **Java's BergDB as it is**, on a JVM language or on Android.

Two specifications do not depend on the language:

* the stream format (012-02);
* the object format (020-07).

Binson, which the object format builds on, has libraries in twelve
languages, of uneven quality (020-05, section 8.1).

**The earlier work.** The study searched for earlier work on other
languages and found the following.

* **Frans's notes of 2008 to 2016** (F1-007):
  * **2008, the log's question 4**, "Support for multiple languages to
    read/write database files?": "No, but possibly export to JSON, XML
    [...] We could support other languages (C-sharp, PHP, ...) that could
    use the binary representation of the database files. But we don't to
    keep things simple." Among the features: "For Java only, but format
    could be supported by other languages too."
  * **2010-05-13**: "maybe KissDB could support JVM, .NET virtual machine
    and be translated to C++ [...] Or why not just compile the Java code
    to a native library."
  * **2012-04-12** (`2012-04-gcj.txt`): KissDB was compiled with GCJ to
    native code, so that it could be used "as a library on Linux C
    projects without any hassle, just like any so library", and IKVM was
    named for .NET.
* **006-08**: a C clone for an embedded target is feasible. It estimated
  35 to 90 kB of code on a Cortex-M4 (section 6.3).
* **012 and 022**: the C clone was made in 13.5 hours of unattended work.
  Its library is 170 to 236 kB and it writes Java's bytes (012-16,
  sections 1 and 3). 022 updates it to 2026.3 today.
* **017-01**, BergDB's future: its option 3 names "an embedded database
  for Java (or a port to Rust or Go)" for audit logs, event sourcing,
  time-travel queries and edge devices (017-01's readme; options.md,
  section 3.3). options.md, section 7.1, adds: "Not needed for any of
  these: a Rust version". A Rust
  port would compete with redb and sled, whose single authors earn
  nothing from them.
* **020-03 and 020-05**: what a binding needs of the object format. "No
  value" is shown by leaving a field out, in the way each language does
  it (020-04). The Binson libraries' faults are listed (020-05, section
  8.2).

Nothing before this study ranked languages by demand.


## 3. What BergDB offers a user in another language

Each trait, what a user would get from it, and its limit. The figures
are from the cited items.

* **An append-only stream is the only storage.**
  * What a user gets: a copy of the files is a copy of the database.
    Writes are in order, which suits flash and copying to elsewhere.
  * The limit: index nodes are written into the stream too. With 10M
    keys and uniform updates, a put of a 24-byte key and an 8-byte value
    cost 867 bytes of stream at a 50 MB startup distance, 524 bytes at
    200 MB and 190 bytes at 1000 MB with today's code (007-07, section
    10; 006-19; 006-08, section 6.4's 681, 373 and 180 were from the take
    used before 2026-10-28).
* **Every past state can be read at a time**, within the retain duration.
  * What a user gets: audit, undo, debugging and reads "as of" a time,
    without history tables.
  * The limit: the past is kept only for the retain duration, once
    reclaim runs. There are no branches and no sync.
* **Startup is bounded.** Startup reads only the tail of the stream
  (T3).
  * What a user gets: neither an app launch nor a start after a crash
    grows with the database. A warm start on 10M keys at 50 MB takes
    0.91 s in C and 2.49 s in Java (012-16, section 3).
  * The limit: a cold start on 10M keys took about 46 s on s1 (017-01).
    The startup section is up to about twice the startup distance, so a
    phone or a browser needs a small distance, which costs writes.
* **There is no stop-the-world of BergDB's own.** Reclaim cuts the front
  of the stream, and eviction works in bounded steps (009).
* **Data can be larger than memory.** A database six times its memory
  budget runs on disk (009-03). The C port has run a million keys in a
  4 MB budget (012-16).
* **The code is small.**
  * The Java Core is 14,677 code lines (006-08, section 5).
  * The C library is 170 to 236 kB, against LMDB's 53 kB and SQLite's
    731 kB (012-16, section 3; 006-08, section 6.3).
* **The model is proved in Lean**: recovery, restart invariance, reclaim,
  eviction and T3. Java is checked against it by trace conformance. No
  competitor found offers this (017-01, options.md, section 5.3).
* **Not there today**:
  * SQL;
  * user indexes outside Java's Pub layer;
  * opening one database from several processes;
  * sync or replication (since 2026-11-04);
  * readers on other threads in C (012-16, section 4);
  * a stream format kept across releases (005-50);
  * a permissive licence (AGPL-3.0);
  * users.


## 4. Popularity and trend

The editions used (all checked, W1 to W6):

* **TIOBE**: November 2026, the rank and the rating.
* **Stack Overflow survey**: 2026 (published 2026-10-06), the percent of
  all respondents who used the language, with 2025 in brackets.
* **RedMonk**: January 2026 (published 2026-04-14).

The table is sorted by TIOBE rank. The trend is this study's own summary
of the columns and of TIOBE's change from a year before.

| Language   | TIOBE     | SO used 2026 (2025) | SO admired | RedMonk | Trend   |
|------------|-----------|-------------|------|----|---------|
| Python     | 1, 20.86% | 58.0 (57.9) | 50.6 | 2  | stable  |
| C          | 2, 11.48% | 21.8 (22.0) | 45.9 | 10 | stable  |
| Java       | 3, 8.89%  | 27.6 (29.4) | 38.5 | 3  | stable  |
| C++        | 4, 8.35%  | 24.3 (23.5) | 45.8 | 7  | stable  |
| C#         | 5, 3.39%  | 27.1 (27.8) | 50.0 | 4  | falling |
| JavaScript | 6, 2.42%  | 62.0 (66.0) | 42.0 | 1  | falling |
| Go         | 10, 1.69% | 16.5 (16.4) | 49.5 | 12 | stable  |
| Rust       | 11, 1.63% | 18.0 (14.8) | 67.4 | 20 | rising  |
| PHP        | 12, 1.58% | 17.7 (18.9) | 35.7 | 4  | stable  |
| Swift      | 18, 0.89% | 5.9 (5.4)   | 48.5 | 11 | stable  |
| Dart       | 20, 0.74% | 4.9 (5.9)   | 42.3 | 18 | mixed   |
| Ruby       | 30, 0.54% | 5.8 (6.4)   | 42.4 | 9  | falling |
| Lua        | 32, 0.49% | 9.4 (9.2)   | 40.8 | -  | stable  |
| Kotlin     | 33, 0.44% | 10.8 (10.8) | 43.1 | 14 | stable  |
| TypeScript | 41, 0.26% | 43.8 (43.6) | 53.0 | 6  | rising  |
| Zig        | 51 to 100 | 2.8 (2.1)   | 58.3 | 82 | rising  |
| Elixir     | 51 to 100 | 2.6 (2.7)   | 62.1 | -  | stable  |
| Erlang     | 51 to 100 | 1.5 (1.5)   | 49.1 | -  | stable  |

**TIOBE.** Changes against November 2025:

| Language | Change                                                  |
|-------|---------------------------------------------------------|
| Rust  | 14 to 11; out of the top 10 this month, Go in its place |
| Dart  | 26 to 20, top 20 for the first time                     |
| PHP   | 16 to 12                                                |
| Swift | 21 to 18                                                |
| C#    | -4.26 points, but language of the year 2025 (W7)        |

TIOBE counts search hits, so it puts TypeScript at 41 while 43.8 percent of
Stack Overflow's respondents use it.

**GitHub Octoverse:**

* **2025** (W5): TypeScript passed Python in August 2025, with about
  2.64M monthly contributors against 2.6M. Luau (Roblox's Lua) grew
  fastest, by 194 percent.
* **2026** (W4): TypeScript, Python and JavaScript are the top three.
  Rust is "the fastest-growing of the top languages", about doubled
  (+162 percent, against TypeScript's +134, Python's +118 and Java's
  +30). C, Kotlin, Swift, Dart and Zig are not mentioned.

**Stack Overflow's database question:**

| Database | 2026 (n = 12,061) | 2025  |
|--------|-------|-------|
| SQLite | 42.1% | 37.5% |
| DuckDB | 5.7%  | 3.3%  |

RocksDB and LevelDB are not listed in either year (W2, W3).

**What it means for the study.** By popularity, the size of the user base
puts these languages first:

* Python, JavaScript and TypeScript;
* Java (done);
* C# and C++ (C++ is served by C).

By trend, Rust rises fastest. Go, PHP and Swift are stable, and Ruby
falls. Dart rises with Flutter. Elixir, Erlang and Zig are small, but
their users like them (Elixir 62.1 percent admired, Zig 58.3).


## 5. What each language's users store with today

Each block gives:

* the stores in use, with signals of use: downloads, stars and release
  dates, from the registries' APIs on 2026-11-09;
* what users complain about;
* any history or append-only design;
* the opening for BergDB.

### 5.1 C and C++

* **Stores in use:**
  * SQLite, everywhere.
  * LMDB (OpenLDAP, Postfix, Kong). It was the way out when Berkeley DB
    moved to the AGPL in 2013 (W28).
  * libmdbx (Erigon, Reth), RocksDB (blockchain nodes: Solana's validator
    "writes the ledger into RocksDB"; stream processors), and LevelDB,
    now legacy (W29, W30).
  * On microcontrollers:
    * FlashDB, 2.9k stars, with a KV mode and a time-series mode: "Power-off
      protection", "wear balance" (W31);
    * ESP-IDF NVS, which "works best for storing many small values" (W33);
    * Zephyr ZMS, a log-structured ring whose garbage collection moves
      the valid data forward and whose partition should be about twice
      the data (W32);
    * littlefs files used as logs.
* **Complaints:**
  * SQLite: "the WAL file will grow without bound" while some reader is
    always active (W27).
  * LMDB and MDBX: the file does not shrink, and MDB_MAP_FULL can stop
    even deletes (W28, W30).
  * RocksDB: writes slow down at 20 level-0 files and stop at 36. Solana's
    validators "began to hit write stalls", and opening a database with
    many SST files is slow (W29).
* **History**: none of the mainstream stores keeps a readable past. LMDB
  gives a reader a snapshot only. FlashDB's time-series mode and ZMS are
  append-only rings, with no reads at a past state.
* **Opening**: Linux-class devices, gateways and data loggers, which need
  safety at power loss, retention by time and a bounded startup. The C
  port is the offer. C++ needs only a header with RAII on top of it.

### 5.2 Rust

* **Stores in use** (crates.io; downloads in the last 90 days, W11):

  | Crate    | Downloads | Version, date             | Note                        |
  |----------|-------|---------------------------|-----------------------------|
  | rusqlite | 57.8M | 0.41.1                    | SQLite                      |
  | rocksdb  | 7.78M | 0.25.0, 2026-08-16        | C++ inside                  |
  | redb     | 6.73M | 4.5.0, 2026-11-05         | pure Rust; 4.9k stars       |
  | sled     | 3.65M | 0.34.7, 2021-09-12        | 1.0 alpha since; 9.1k stars |
  | heed     | 3.07M | 0.23.1, 2026-10-26        | LMDB, for Meilisearch       |
  | fjall    | 760k  | 3.1.13; 3.0 of 2026-01-02 | pure Rust LSM; 2.4k stars   |

  Smaller ones: turso, a Rust rewrite of SQLite, still in beta; surrealkv,
  persy, native_db and canopydb (W13). For microcontrollers (no_std):
  * ekv: an LSM on raw NOR flash, 1.0;
  * sequential-storage: a map and a queue appended to flash, 7.1.0, January
    2026 (W17).
* **Complaints:**
  * sled: "sled is beta", "the on-disk format is going to change",
    "sled uses too much space sometimes" (W10).
  * librocksdb-sys: "a somewhat infamous source of lengthy build times".
    It needs Clang and builds about 481K lines of bundled C++ (W14).
  * Feldera left RocksDB for an engine of its own (W15).
  * fjall: one process only (W13).
  * redb: while a savepoint exists, pages freed after it are not freed
    (W12). In redb's own benchmark its uncompacted file was 4.00 GiB,
    against LMDB's 2.61 and fjall's 1.00 (W12).
* **History**: SurrealKV calls itself a "versioned, embedded" key-value
  store. It has `get_at(key, ts)`, `history`, and versions kept for a
  retention period, but "the on-disk formats are not frozen yet" (W16).
* **Opening**: a pure-Rust store with a stable format, reads at a past
  time and a bounded startup has no settled incumbent.

### 5.3 Go

* **Stores in use** (W18 to W22):
  * bbolt, 9.8k stars (etcd);
  * BadgerDB, 15.8k stars;
  * Pebble, 6.1k stars (CockroachDB; geth's default for new nodes);
  * goleveldb, "not actively maintained" by geth's docs;
  * NutsDB;
  * SQLite, through mattn/go-sqlite3 (cgo) or modernc.org/sqlite (pure Go).
* **Complaints:**
  * bbolt: it "cannot truncate data files and return free pages back to
    the disk"; one writer at a time (W18).
  * Badger: its value-log garbage collection is not guaranteed to free a
    file (W19).
  * Pebble: write amplification from compactions, and write stalls (W20).
  * cgo: a build with `CGO_ENABLED=0` fails at run time with "go-sqlite3
    requires cgo", and cross-compiling needs a C toolchain (W22).
  * geth: a graceful shutdown can write more than 1 GB to LevelDB, "which
    can take several minutes" (W21).
  * Prometheus: replaying its write-ahead log is the slowest part of
    startup, sometimes 5 to 10 minutes (W26).
* **History:**
  * immudb: embeddable, append-only, with history queries, but under the
    Business Source License 1.1 and with pruning only on its roadmap
    (W23).
  * Dolt: `AS OF` a Dolt commit, also embedded (W24).
  * Badger: keeps versions per key.
  * Litestream 0.5 (October 2025): point-in-time restore of SQLite, and
    reads at a past time through its VFS (W25).
* **Opening**: a pure-Go, permissively licensed key-value store with
  history and reclaim at the front.

### 5.4 Zig

* **Stores in use**: bindings to LMDB and SQLite. TigerBeetle has an LSM
  of its own, with static allocation, which others do not reuse (W13).
* **Opening**: small. Zig imports C headers directly, so the C port
  serves it as it is.

### 5.5 C# and .NET

* **Stores in use** (NuGet, total downloads, W34):

  | Package               | Downloads | Note                                        |
  |-----------------------|--------|---------------------------------------------|
  | Microsoft.Data.Sqlite | 142.9M | 10.0.14, 2026-10-25                         |
  | LiteDB                | 48.6M  | stable 5.0.21 of 2024-07-05; 6.0 prerelease |
  | RocksDB (bindings)    | 9.1M   | 11.12.0, 2026-11-02                         |
  | LightningDB (LMDB)    | 3.6M   |                                             |
  | Microsoft.FASTER.Core | 1.9M   | last 2024-05-07, moved into Garnet          |

  Also ZoneTree, a pure C# LSM with 507 stars.
* **Complaints**: the risk that a maintainer leaves.
  * Realm .NET's Device Sync ended on 2025-09-30, and the database lives
    on only as community open source (W35).
  * FASTER's development went into Garnet's internal engine.
  * LiteDB has had no stable release for over two years, and its
    encryption is marked "currently not secure, DO NOT USE".
* **History**: Marten's event store keeps its events in PostgreSQL;
  KurrentDB is a server. No embedded .NET store with history was found.
* **Opening**: an empty field after Realm and FASTER, for desktop apps
  and for event sourcing without PostgreSQL.

### 5.6 Python

* **Stores in use:**
  * `sqlite3`, in the standard library. Since Python 3.13 `dbm.sqlite3`
    is the default dbm (W36).
  * Downloads in the last month (W37):

    | Package    | Downloads |
    |------------|-------|
    | duckdb     | 54.9M |
    | diskcache  | 24.5M |
    | lmdb       | 2.53M |
    | sqlitedict | 1.35M |
    | rocksdict  | 758k  |
    | plyvel     | 448k  |
* **Complaints:**
  * shelve is pickle, so it is unsafe to load from an untrusted source.
    It has no concurrent reads and writes, and "dbm.ndbm can silently
    corrupt the database file" on macOS (W36).
  * DuckDB's wheels are 14 to 22 MB.
* **History**: the eventsourcing library, on SQLite or PostgreSQL (W38).
  Versioning by triggers on SQLite: Simon Willison's sqlite-history and
  sqlite-chronicle (W39).
* **Opening**: medium. A large use of embedded key-value caches
  (diskcache) and event sourcing, but SQLite is in the standard library.

### 5.7 JavaScript and TypeScript on Node, Bun and Deno

* **Stores in use** (npm, downloads a week, 2026-11-02 to 08, W50):
  * better-sqlite3: 16.45M;
  * lmdb (lmdb-js): 8.34M;
  * @libsql/client: 6.01M;
  * sqlite3: 2.87M;
  * the level family: level, classic-level and leveldown, the last
    deprecated.
* **Built-in SQLite:**
  * `node:sqlite` is a release candidate (stability 1.2) in Node 25.7 and
    later, and still so in Node 26's docs (W51).
  * Bun has `bun:sqlite` built in (W54).
  * Deno KV is SQLite locally and still needs `--unstable-kv` (W53).
* **Deno**: its team joined Cloudflare on 2026-10-09. The runtime gets
  one more year of monthly releases, then "we will end our development
  of the Deno runtime". Deno Deploy shuts down after six months (W52).
* **Complaints:**
  * Native addons in Electron fail with an ABI mismatch until they are
    rebuilt and unpacked from the asar archive (W55).
  * Stores held in memory, such as LokiJS (unmaintained since 2023) and
    NeDB, limit the data to RAM and read the whole file at the start
    (W56).
* **History**: none of these stores reads at a past time. NeDB is
  append-only, with no history API.

### 5.8 The browser and local-first apps

* **Stores in use** (npm, downloads a week, W50; much of it pulled in by
  other packages):
  * IndexedDB wrappers: idb 36.2M, idb-keyval 15.5M, localforage 10.7M,
    Dexie 3.38M.
  * SQLite in WASM: @sqlite.org/sqlite-wasm 1.41M, sql.js 6.34M.
  * PGlite, about 3 MB gzipped.
  * DuckDB-WASM, about 12 MB gzipped (W65).
  * Sync engines:

    | Engine    | Downloads a week | Note                   |
    |-----------|-------|------------------------|
    | Electric  | 2.48M |                        |
    | Instant   | 480k  |                        |
    | Zero      | 314k  | 1.0 in June 2026 (W63) |
    | Triplit   | 300k  |                        |
    | PowerSync | 174k  |                        |
    | Automerge | 114k  |                        |
    | LiveStore | 11k   |                        |
    | yjs       | 15.7M |                        |
* **Notion** (2024-07-10, W57) moved to SQLite in WASM on OPFS, behind a
  SharedWorker.
  * Navigation became about 20 percent faster.
  * Tabs writing at once "caused corrupt data".
  * The WASM download slowed the first load, so it is now loaded later.
* **Complaints:**
  * IndexedDB's cost is per transaction. In RxDB's test, 1k documents took
    about 80 ms in one transaction and about 2 s with one transaction each
    (W58).
  * Under storage pressure an origin's data is deleted "all of its data,
    not parts of it" (W59).
  * Safari deletes the data that script wrote for an origin with no user
    interaction in seven days of use (W59).
* **History, the strongest demand found:**
  * LiveStore keeps an event log that it materializes into SQLite. Its
    docs say "All the client app data should fit into a in-memory SQLite
    database"; a user says "as the data grows the materialization gets
    slower"; its log compaction was still planned in 2025 (W60).
  * Automerge 3 keeps the full history. A document that "hadn't loaded
    after 17 hours" now loads in 9 s (W61).
  * Jazz and Loro offer time travel, and Datahike offers as-of queries on
    IndexedDB, in preview (W62).
  * Linear bootstraps a whole workspace into IndexedDB, and large
    workspaces "may see performance degradation" (W64).
* **The platform**: OPFS's synchronous access handles work only in
  workers. They are in Chrome 102, Firefox 111 and Safari 15.2, and
  Baseline since March 2023 (W95). One handle at a time, except Chrome's
  `readwrite-unsafe` mode.
* **Opening**: a store under a sync engine, not instead of one. Such a
  store offers reads at a past time, a bounded startup, data larger than
  memory, and a log whose front is cut. These are what LiveStore and
  Automerge lack or built at great cost. The C port in WASM would be about
  the size of SQLite's WASM build.

### 5.9 Swift

* **Stores in use** (GitHub stars, W66):

  | Store                           | Stars, signal    |
  |---------------------------------|------------------|
  | Core Data and SwiftData         | Apple's own      |
  | GRDB                            | 8.7k             |
  | SQLite.swift                    | 10.2k            |
  | Point-Free's SQLiteData         | 1.0 after a year |
  | Realm Swift                     | 16.6k            |
  | MMKV (Tencent; iOS and Android) | 18.8k            |
  | Couchbase Lite, ObjectBox       | -                |

  Realm Swift's sync ended on 2025-09-30, and its community branch lags
  (W35).
* **Complaints about SwiftData** (W67):
  * a developer went back to Core Data over its speed on iOS 18;
  * reads "degraded sharply with over 100k objects".
* **History**: SwiftData's History API (iOS 18) tracks changes for sync.
  It does not read a past state.
* **Opening**: medium. Realm's users without sync need a new home, but
  Apple's stores and SQLite dominate.

### 5.10 Kotlin, and Java on Android

* **Stores in use:**
  * Room. Room 2.7 runs on Kotlin Multiplatform. Room 3.0 (alpha,
    2026-03-13) is "KMP-first", adds JavaScript and WasmJS targets with a
    web driver on OPFS, and puts Room 2 in maintenance (W68).
  * SQLDelight, 6.9k stars.
  * DataStore, for small data sets.
  * MMKV.
  * ObjectBox, which adds "around 2.3 MB" to an app (W72).
  * Realm Kotlin, dormant since 2025-10.
* **Stores on the JVM rarely work on Android.** H2's developers say it
  does not support Android, and Xodus fails on `ManagementFactory` (W71).
  Kotlin on the JVM uses Java's BergDB as it is.
* **Java's BergDB on Android** (not tested):
  * The Core uses only `java.base` (006-08, section 6.6).
  * `dag.Handle` and `dag.TopNode` use `VarHandle` (handles, 009), which
    Android has from API level 33, Android 13 (W70).
  * Android 14 brought about 300 `java.base` classes up to Java 17, and
    ships them through system updates to "over 600 million devices"
    (W69).
  * `core.Jmx` uses `javax.management`, which Android lacks, but `Db` does
    not need it.

  So the Core may run on Android 13 or 14 and later as it is; a test on
  an emulator would tell.
* **History**: no Android or Kotlin Multiplatform store offers it.
* **App start**: Android vitals counts a cold start of 5 s or longer as
  excessive (W75). Android also kills apps in the background. Both make a
  bounded startup and crash recovery useful.

### 5.11 Dart and Flutter

* **Stores in use** (pub.dev, likes and downloads in 30 days, W73):

  | Package            | Likes  | Downloads | Note                        |
  |--------------------|--------|-------|-----------------------------|
  | shared_preferences | 10,589 | 9.20M |                             |
  | sqflite            | 5,577  | 3.23M |                             |
  | drift              | 2,491  | 1.91M | SQLite                      |
  | hive_ce            | 574    | 1.31M | fork of the abandoned Hive  |
  | hive               | 6,263  | 1.18M | last push 2024-06-28        |
  | sembast            | 1,197  | 411k  |                             |
  | objectbox          | 1,581  | 182k  |                             |
  | isar_community     | 162    | 113k  | fork of the abandoned Isar  |
  | isar               | 2,448  | 4.0k  | last stable three years ago |

  Realm for Flutter is deprecated.
* **Complaints**: Hive and Isar were left by their author, and Realm by
  MongoDB. A 2026 post says: "Avoid Hive and Isar for new offline-first
  projects in 2026" (W74). hive_ce is "Inspired by Bitcask" and keeps
  every value of an open box in memory (W73), so its startup and its
  memory grow with the data.
* **Opening**: a maintained key-value store with a bounded startup and
  eviction answers exactly the design that Hive's users live with. The
  barrier is trust: users went to SQLite (drift, sqflite) because it will
  last.

### 5.12 Ruby, PHP, Elixir and Erlang, Lua

* **Ruby:**
  * The sqlite3 gem has 201M downloads.
  * Rails 8 (2024-11-07) runs its queue, cache and cable on SQLite in
    production (W40).
  * The lmdb gem has 442k downloads.
  * Little need beyond SQLite was found.
* **PHP:**
  * SQLite through PDO; APCu, which is in memory and per host; and dba,
    which supports LMDB since PHP 7.2 (W41).
  * A process for each request fits an in-process store with its own
    threads badly.
  * No embedded store with history was found.
* **Elixir and Erlang:**
  * Stores in use:
    * ETS, DETS and Mnesia (W42). DETS is limited to 2 GB, and its repair
      after an unclean close "can take a substantial time".
    * CubDB (W43): pure Elixir, an "append-only, immutable B-tree", safe
      at power loss, "a great fit for Nerves projects", with "no need to
      cross-compile native code". 253k downloads; its last release, 2.0.2,
      is of 2023.
    * exqlite (3.34M), a rocksdb NIF, and Khepri, which replaces Mnesia
      for RabbitMQ's metadata (W45).
  * A Nerves thread (2024-10-11, W44) asks for retention by time:
    * a device logs at 50 Hz with 30 days of retention, an estimated 110
      to 150M records and over 10 GB;
    * CubDB's author answers that compaction "will need to catch up with
      writes that happened while the compaction was ongoing", and
      suggests a new database for each day.

    That is BergDB's reclaim with a retain duration, almost word for
    word.
* **Lua**: lsqlite3 (W48). Kong moved to LMDB (lua-resty-lmdb) to "help
  with the restart time of Kong", and its users then meet "Configuration
  does not fit in LMDB database" (W46). LuaJIT's FFI calls C directly.


## 6. The complaints, and what BergDB answers

| Complaint, and where it is met                                  | BergDB                           |
|-----------------------------------------------------------------|----------------------------------|
| History kept by hand: triggers, Dolt commits, restores          | yes: reads at a past time        |
| Space never returned: LMDB, MDBX, bbolt, Badger, SQLite's WAL   | yes: reclaim cuts the front      |
| Compaction stalls: RocksDB, Pebble, CubDB                       | yes: bounded steps (009)         |
| Map-size limits: LMDB, Kong, DETS at 2 GB                       | yes: no map; the stream grows    |
| Long startup or replay: Prometheus, geth, DETS, Hive, LiveStore | yes: only the tail is read (T3)  |
| C++ builds and cgo: librocksdb-sys, go-sqlite3, NIFs on Nerves  | half: C17, small; ports avoid it |
| Abandoned or unstable stores: sled, Hive, Isar, Realm, LiteDB   | not by design: needs upkeep      |
| Write amplification: RocksDB, Pebble                            | no: index nodes in the stream    |
| One writer or one process: bbolt, fjall, SQLite                 | no: one process, one order       |
| Licence: Berkeley DB's AGPL, immudb's BSL                       | no, while BergDB is AGPL-3.0     |
| Sync between devices (local-first)                              | no: no replication               |

Two rows need a word more:

* **Write amplification.** BergDB's own amplification is the 867 bytes a
  put at 10M keys and 50 MB (section 3; 006-19). It is no worse in kind than an
  LSM's, but it is not an answer to that complaint.
* **Abandoned stores.** That row is about Frans, not the code. A port
  answers it only if someone keeps the port.


## 7. Where the traits meet a need

Each use, the languages, the evidence and the fit.

1. **Linux-class devices, gateways and data loggers.**
   * Languages: C, Rust, Elixir (Nerves), Go.
   * Evidence: Nerves asks for retention by time and safety at power loss
     (W44). FlashDB and ZMS show the ring pattern on flash (W31, W32).
   * Fit: strong where there is a file system.
   * On microcontrollers it is open:
     * the C port's 170 to 236 kB;
     * the write cost at small startup distances, not measured (006-08,
       section 6.8);
     * Rust's ekv and sequential-storage are already there.
2. **The browser and local-first apps.**
   * Languages: JavaScript and TypeScript.
   * Evidence: LiveStore keeps all data in memory and has no compaction;
     Automerge's history took hours to load before version 3; Linear's
     bootstrap; Notion's SQLite in WASM (W57, W60, W61, W64).
   * Fit: medium to strong, as the store under a sync engine.
   * Risks:
     * the browser deletes a whole origin's data;
     * one tab owns the files, so a SharedWorker or a lock is needed;
     * BergDB has no sync.
3. **Mobile apps.**
   * Languages: Kotlin and Java on Android, Swift, Dart.
   * Evidence:
     * Android's 5 s cold-start limit, and kills in the background (W75);
     * Hive keeps everything in memory (W73);
     * the abandoned stores (W35, W74);
     * no mobile store reads at a past time.
   * Fit: medium. SQLite is entrenched, and history on a phone mostly
     serves sync.
4. **Audit logs and regulated history.**
   * Languages: Go, C#, Java, Python, Rust.
   * Evidence:
     * DORA applies since January 2025, and Codenotary credits it for
       record sales (017-01, E15);
     * Amazon's QLDB ended on 2025-07-31 (E20);
     * immudb went to the BSL (W23).
   * Fit: strong in technique, but these are bought as compliance
     products (017-01, options.md, section 5.2).
5. **Event sourcing.**
   * Languages: C#, Python, Elixir, Java, Go.
   * Evidence: the libraries keep events in PostgreSQL or SQLite (Marten,
     Commanded, eventsourcing; W38). The servers charge more since 2024
     (Kurrent, Axon; 017-01, E16, E17).
   * Fit: medium. BergDB could be an in-process store with reads of the
     state at a time t, but it is a key-value store, not an event store
     with subscriptions.
6. **Desktop apps**: document history, undo, autosave, recovery after a
   crash.
   * Languages: C#, Swift, Rust, JavaScript in Electron, Dart.
   * Evidence: weak. No direct source was found, beyond the users that
     Realm left.
   * Fit: medium.
7. **Edge and serverless.**
   * Languages: JavaScript and TypeScript, Rust, Go.
   * Evidence: point-in-time recovery is expected (Cloudflare's Durable
     Objects keep 30 days, W47; Litestream 0.5, W25). Deno KV and Deno
     Deploy end (W52), and Supabase buys Turso (017-01, E23).
   * Fit: weak for functions without a durable local disk. Medium for
     edge nodes with a disk.
8. **Infrastructure**: blockchain nodes, metadata stores, observability
   agents.
   * Languages: Go, Rust, C++.
   * Evidence: startup and replay (geth, Prometheus), stalls (Solana),
     space (MDBX) (W21, W26, W29, W30).
   * Fit: medium. Their sizes, terabytes, are far beyond what BergDB has
     measured (10M to 100M keys).
9. **CLI tools and caches.**
   * Languages: Python, Rust, Go.
   * Evidence: diskcache's 24.5M downloads a month (W37), and Rust users'
     dislike of C++ builds (W14).
   * Fit: medium. History is a bonus there, not the need.


## 8. How a library is distributed and found

The last two columns say how a binding to the C port and a native port
would ship there.

| Ecosystem      | Registry                        | Binding to the C port             | Native port   |
|----------------|---------------------------------|-----------------------------------|---------------|
| Rust           | crates.io, 373,209 crates       | a `-sys` crate built by `cc`      | a crate       |
| Python         | PyPI, wheels                    | wheels by cibuildwheel; abi3      | too slow      |
| Node, Bun      | npm                             | Node-API prebuilds, or WASM       | possible      |
| Browser        | npm with a `.wasm`              | Emscripten build of the C port    | possible      |
| Deno           | JSR, `npm:`                     | FFI or npm's WASM; Deno ends      | no            |
| .NET           | NuGet                           | `runtimes/{rid}/native`, P/Invoke | close to Java |
| Java, Kotlin   | Maven Central (Central Portal)  | Java's BergDB itself              | -             |
| Android        | Maven Central, AAR              | `.so` per ABI, 16 KB pages        | Java as is    |
| Kotlin MP      | Maven Central, klib per target  | cinterop with the C library       | -             |
| Swift          | SwiftPM, Swift Package Index    | a C target in the package         | possible      |
| Dart, Flutter  | pub.dev                         | `dart:ffi`, build hooks           | possible      |
| Go             | modules from source             | cgo, which users avoid            | needed        |
| Ruby           | RubyGems                        | precompiled platform gems         | no            |
| PHP            | Packagist; PIE replaces PECL    | an extension, or FFI              | no            |
| Elixir, Erlang | Hex.pm                          | a NIF, precompiled per target     | a rewrite     |
| Lua            | LuaRocks                        | LuaJIT FFI, or a C module         | no            |
| Zig            | `build.zig.zon` by URL and hash | `@cImport` of the header          | no            |

Notes, each from its source:

* **Rust**: crates are built from source on the user's machine, so a C
  core needs only a C compiler (W80). The C port is C17 with no C++,
  unlike librocksdb-sys (W14). Pure Rust is still preferred for
  cross-builds and WASM.
* **Python** (W81, W82):
  * cibuildwheel builds wheels for manylinux, musllinux, macOS, Windows,
    and also iOS, Android and Pyodide.
  * The stable ABI (abi3) gives one wheel per platform for many Python
    versions.
  * Free-threaded Python needs wheels of its own until `abi3t` (PEP 803,
    3.15 and later).
  * PEP 783, accepted on 2026-04-06, lets PyPI take Emscripten (WASM)
    wheels.
* **Node** (W83, W84):
  * Node-API is stable across Node's major versions.
  * napi-rs and prebuildify publish one npm package for each platform,
    which the root package lists as `optionalDependencies`.
  * Bun runs most Node-API addons.
  * Electron's rebuilds (W55) favour WASM.
* **.NET**: a package carries every platform's library under
  `runtimes/{rid}/native`. NativeAOT needs `LibraryImport` rather than
  `DllImport` (W85).
* **Maven Central**: OSSRH closed on 2025-06-30, and publishing goes
  through the Central Portal. The Java FFM API is final in JDK 22 (W86).
* **Android**: apps that target Android 15 must support 16 KB pages. The
  page says updates without it cannot be released from 2027-02-01 (W88).
  Java's BergDB has no native code, so this does not apply to it.
* **Swift** (W89):
  * the Swift Package Index lists 12,487 packages;
  * SwiftPM compiles C targets itself;
  * a `binaryTarget` (XCFramework) is for Apple's platforms only;
  * CocoaPods' trunk becomes read-only on 2026-12-02.
* **Dart**: build hooks, "native assets", came in Dart 3.10. They build
  or download native code at `run`, `build` and `test` (W90).
* **Go**: cgo is off when cross-compiling or when no C compiler is found
  (W22). A binding costs users their static, cross-compiled binaries. A
  port in Go is the way.
* **PHP**: pecl.php.net calls PECL deprecated, with PIE as its successor
  (W92).
* **Elixir**: a precompiled NIF is downloaded per target and checked
  against a checksum in the Hex package, as rustler_precompiled does
  (W93). Nerves still cross-compiles, which CubDB's FAQ sells against.
* **Zig**: there is no central registry (W94).
* **The browser**: synchronous access handles on OPFS, in a worker (W95).


## 9. The ranking

Three ratings for each language:

* **Demand**: popularity (section 4), and how much embedded storage its
  users use (section 5).
* **Opening**: what the stores in use leave for BergDB's traits: the
  complaints that BergDB answers, a missing store with history, and
  incumbents that were abandoned (sections 5 to 7).
* **Cost**: the cost of the route. L, low: Java as it is, or a thin
  binding. M, medium: a WASM build or an FFI layer. H, high: a native
  port.

| Rank | Language or platform     | Demand | Opening | Route                             | Cost |
|----|--------------------------|--------|--------|-----------------------------------|------|
| 1  | Rust                     | high   | high   | native port; a `-sys` crate first | M-H  |
| 2  | JS and TS: browser, Node | high   | high   | the C port in WASM, on OPFS       | M    |
| 3  | Python                   | high   | medium | binding to the C port, wheels     | L    |
| 4  | Go                       | high   | high   | native port, no cgo               | M-H  |
| 5  | C# and .NET              | high   | medium | NuGet binding, or a native port   | L, M |
| 6  | Dart and Flutter         | medium | high   | `dart:ffi` on the C port          | L-M  |
| 7  | Java, Kotlin on Android  | medium | medium | Java's BergDB as it is, API 33+   | L    |
| 8  | Swift                    | medium | medium | a SwiftPM C target                | L-M  |
| 9  | Elixir and Erlang        | low    | high   | a NIF on the C port, or a port    | M    |
| 10 | Lua                      | low    | low    | LuaJIT FFI on the C port          | L    |
| 11 | Ruby                     | low    | low    | a native gem on the C port        | L    |
| 12 | PHP                      | medium | low    | an extension or FFI               | L    |
| -  | C                        | high   | high   | exists (022)                      | -    |
| -  | C++, Zig                 | -      | -      | the C port's header               | L    |
| -  | Kotlin on the JVM        | -      | -      | Java's BergDB as it is            | -    |
| -  | Deno                     | -      | -      | dropped: development ends         | -    |

The reasoning for each rank:

1. **Rust.**
   * Demand: the fastest-growing of the top languages on GitHub, and 18.0
     percent on Stack Overflow, up from 14.8.
   * Opening: users are unhappy with what they have. sled is in beta with
     a format to change, librocksdb-sys builds slowly, redb's files are
     large, and fjall is for one process only. The one versioned store,
     SurrealKV, has no frozen format.
   * BergDB's proved model also suits a community that values
     correctness.
   * Against it: the field is crowded, and its authors earn nothing
     (017-01, options.md, section 7.1). A `-sys` crate over the C port is
     a cheap first step; pure Rust is what users ask for.
2. **JavaScript and TypeScript: the browser, Node and Bun.**
   * Demand: the largest user base (TypeScript first on GitHub), and the
     clearest demand for history, logs and large local data (section
     5.8).
   * Route: one WASM build of the C port would serve the browser, Node,
     Bun and Deno in its last year, and would avoid Electron's rebuilds.
     The C port's single caller suits a worker.
   * Against it: the browser deletes data under pressure; one tab owns
     the files; and the demand is for sync, which BergDB lacks. Its place
     is under a sync engine.
3. **Python.**
   * Demand: the largest by popularity, with a large use of embedded
     key-value caches.
   * Cost: the lowest, since wheels are a solved problem (W81).
   * Against it: SQLite is in the standard library, and the demand for
     history in Python is not shown beyond event sourcing. A native
     Python port makes no sense.
4. **Go.**
   * Demand: a middle-sized user base (16.5 percent on Stack Overflow)
     that uses embedded stores more than most: etcd, CockroachDB, geth
     and Prometheus are written in Go.
   * Opening: users dislike cgo, the stores' files do not shrink, the one
     store with history is under the BSL, and startup replay is a known
     pain (Prometheus, geth).
   * Route: Go has a collector and threads, as Java has, so a port maps
     Java's design more directly than C did. It must be native.
   * 017-01 already named Go beside Rust.
5. **C# and .NET.**
   * Demand: large (27.1 percent on Stack Overflow, RedMonk's 4th), though
     TIOBE has it falling.
   * Opening: an empty field after Realm and FASTER, and no store with
     history.
   * Route: NuGet ships native libraries well. C# is the language closest
     to Java, so a native port would be the most mechanical of all
     (Frans's 2010 note named .NET).
6. **Dart and Flutter.**
   * Opening: the sharpest found on the client. Hive, Isar and Realm were
     abandoned, and hive_ce keeps all values in memory.
   * Demand: medium but rising; TIOBE's top 20 for the first time.
   * Route: build hooks make FFI on the C port shippable.
   * Against it: trust; users fled to SQLite.
7. **Java and Kotlin on Android.**
   * Cost: no port at all, if the Core runs on API 33 or later (section
     5.10). A bounded startup and crash recovery suit Android's kills and
     its 5 s cold-start limit.
   * Opening: medium. Room and SQLite serve most apps, and history there
     mostly serves sync.
8. **Swift.**
   * Route: SwiftPM compiles the C port as a C target.
   * Against it: Apple's stores and SQLite (GRDB, SQLiteData) dominate.
     Realm's users and SwiftData's complaints are the opening, a modest
     one.
9. **Elixir and Erlang.**
   * Opening: the best fit by words. Nerves asks for exactly retention by
     time, safety at power loss and no stalls.
   * Against it: the user base is small, and Nerves users avoid native
     code, so a NIF loses CubDB's selling point and a port is a rewrite.
10. **Lua.** Kong's restart time is a real case, but a small one. The
    FFI on the C port costs little.
11. **Ruby.** Rails went all in on SQLite. No demand beyond it was found.
12. **PHP.** It is popular, but a process for each request fits an
    in-process store with background threads badly.

**Outside the ranking:**

* **C** is done (022). It is the base for most of the rows above.
* **C++ and Zig** need only the C header.
* **Kotlin on the JVM** has Java's BergDB.
* **Deno** drops out: its development ends about a year after
  2026-10-09.


## 10. The languages to study first

1. **Rust.** The study's question: a native port or a crate over the C
   port, and what each gives a Rust user. Also: the format kept stable
   across releases, since sled's users complain of that; BergDB against
   SurrealKV, redb and fjall; and whether embedded `no_std` is in scope.
   It probably is not, since ekv and sequential-storage hold it.
2. **JavaScript and TypeScript.** One WASM build of the C port, for the
   browser and for Node and Bun. The questions:
   * how stream files map to OPFS files;
   * one owner of the files, through a SharedWorker or Web Locks;
   * the quota, and the deletion of a whole origin;
   * a small startup distance and its write cost;
   * whether a sync engine (LiveStore, PowerSync, Zero) would sit on top
     of it.
3. **Python.** A binding to the C port, shipped as abi3 wheels. The
   questions: the C port takes one caller at a time, so how does that
   meet the GIL and free-threaded Python; and the API's shape, a mapping
   with reads at a time.
4. **Go.** A native port, checked byte for byte against Java with the
   cross harness, as C was (012-05). The questions: how goroutines and
   atomics map Java's threads; the collector, against C's manual frees;
   and BergDB against bbolt, Badger, Pebble and immudb.
5. **C#**, if there is room for a fifth: a NuGet binding is cheap, and a
   native port would follow Java's design most closely.

A check outside the study: Java's BergDB, unchanged, in an Android 13
emulator. A smoke test of `Db` on a file is enough to know whether rank 7
costs anything.


## 11. What is uncertain

* **The demand for reading the past.** It is inferred from neighbours
  (SurrealKV, immudb, Litestream, LiveStore, Automerge, Jazz) and from
  complaints. No survey asks about it, and no user was asked. A port
  should start with a user who has this need.
* **The licence.** Under AGPL-3.0, most of this demand is not reachable.
  The ecosystems above are mostly MIT and Apache, the Berkeley DB move to
  the AGPL in 2013 drove users away (W28; 017-01, E1), and apps in stores
  rarely take copyleft. The ranking assumes a permissive licence or a
  dual one, which is Frans's decision (017-01).
* **Small startup distances.** Phones and browsers need startup to read
  a few MB, not twice 50 MB. The write cost and the memory at such
  distances are not measured (006-08, section 6.8).
* **The format across releases.** It changed between 2026.1 and 2026.2
  (005-50). Users of other languages complain of exactly that (sled), and
  a binding multiplies the cost.
* **Sync.** Local-first users want sync more than history. BergDB has
  none (017-03).
* **The measures.**
  * The indexes disagree: TIOBE puts TypeScript at 41.
  * Stack Overflow's survey had about 30,900 responses in 2026, and
    RedMonk notes that its decline hurts new languages.
  * Registry downloads include CI and dependencies pulled in by other
    packages: PGlite's 40M a week is not 40M users.
* **News of the last weeks**, which may still change: Deno's end
  (2026-10-09); CocoaPods' trunk read-only from 2026-12-02; Room 3 on the
  web.
* **Facts not checked on their source pages**: those marked "found" in
  section 12. Among them are the Swift and Flutter complaints, the cgo
  numbers, and Prometheus's replay times.


## 12. Method and sources

The web was searched on 2026-11-09 in three parts, by research agents of
this study's session:

* popularity and distribution;
* the systems and server languages;
* the client platforms.

Two surprising claims were read again on their pages by this file's
author: the TIOBE edition (W1) and Deno's end (W52). Each source below
has its date, or "acc." for an undated page read that day, and a mark:

* **checked**: read on the source page;
* **found**: seen in a search result or a summary only.

The registries' figures (crates.io, PyPI through pypistats, npm, NuGet,
RubyGems, Hex, pub.dev, GitHub stars) are from their APIs on 2026-11-09.
They are all checked.

Popularity:

* W1. TIOBE Index, November 2026. https://www.tiobe.com/tiobe-index/.
  Checked.
* W2. Stack Overflow Developer Survey 2026, technology and databases.
  https://survey.stackoverflow.co/2026/technology;
  https://stackoverflow.blog/2026/10/06/the-results-of-the-2026-developer-survey-are-here/,
  2026-10-06. Checked.
* W3. Stack Overflow Developer Survey 2025.
  https://survey.stackoverflow.co/2025/technology. Checked.
* W4. Octoverse 2026.
  https://github.blog/news-insights/octoverse/octoverse-commits-pushes-reach-new-highs-in-2026-as-developers-build-with-agents/,
  2026-10-28. Checked; that the growth figures are of merged pull
  requests is found.
* W5. Octoverse 2025.
  https://github.blog/news-insights/octoverse/octoverse-a-new-developer-joins-github-every-second-as-ai-leads-typescript-to-1/,
  2025-10-28. Checked.
* W6. RedMonk, January 2026.
  https://redmonk.com/sogrady/2026/04/14/language-rankings-1-26/,
  2026-04-14. Checked.
* W7. C#, TIOBE's language of the year 2025.
  https://visualstudiomagazine.com/Articles/2026/01/08/Csharp-Grabs-Language-of-the-Year-TIOBE-Predicts-TypeScript-Rise.aspx,
  2026-01-08. Found; TIOBE's hall of fame checked.

The systems and server languages:

* W10. sled's README. https://github.com/spacejam/sled, acc. Checked.
* W11. crates.io: sled, redb, fjall, rocksdb, heed, rusqlite.
  https://crates.io/api/v1/crates/{name}, acc. Checked.
* W12. redb: https://github.com/cberner/redb (its benchmark);
  https://docs.rs/redb/latest/redb/struct.WriteTransaction.html
  (savepoints), acc. Checked.
* W13. fjall: https://github.com/fjall-rs/fjall, acc. Checked. The
  smaller crates: https://lib.rs/database-implementations, acc. Checked.
  TigerBeetle's LSM:
  https://tigerbeetle.com/blog/2022-10-12-a-database-without-dynamic-memory/,
  2022-10-12. Found.
* W14. librocksdb-sys's build time:
  https://github.com/penumbra-zone/penumbra/pull/4496, 2024-05-29;
  https://lib.rs/crates/rocksdb, acc. Checked.
* W15. Feldera, "RocksDB: not a good choice for high-performance
  streaming".
  https://feldera.com/blog/rocksdb-not-a-good-choice-for-high-performance-streaming,
  2024-07-21. Checked.
* W16. SurrealKV. https://docs.rs/crate/surrealkv/latest, acc. Checked.
* W17. ekv: https://docs.rs/ekv. sequential-storage:
  https://github.com/tweedegolf/sequential-storage. Both acc. Found.
* W18. bbolt. https://github.com/etcd-io/bbolt, acc. Checked.
* W19. BadgerDB: https://github.com/hypermodeinc/badger, acc., checked.
  Its value-log GC:
  https://discuss.dgraph.io/t/badgerdb-consume-too-much-disk-space/17070,
  found.
* W20. Pebble: https://github.com/cockroachdb/pebble, acc., checked.
  CockroachDB's storage layer:
  https://www.cockroachlabs.com/docs/v25.4/architecture/storage-layer,
  found.
* W21. geth's databases.
  https://geth.ethereum.org/docs/fundamentals/databases, acc. Checked.
* W22. cgo: https://pkg.go.dev/cmd/cgo, acc., checked. SQLite with and
  without cgo: https://github.com/multiprocessio/sqlite-cgo-no-cgo,
  found.
* W23. immudb. https://github.com/codenotary/immudb, acc. Checked.
* W24. Dolt embedded: https://www.dolthub.com/blog/2022-07-25-embedded;
  https://docs.dolthub.com/sql-reference/version-control/querying-history.
  Found.
* W25. Litestream 0.5: https://fly.io/blog/litestream-v050-is-here/;
  https://fly.io/blog/litestream-vfs/, 2025-10. Found.
* W26. Prometheus's WAL replay:
  https://ganeshvernekar.com/blog/prometheus-tsdb-wal-and-checkpoint;
  https://groups.google.com/g/prometheus-users/c/DFZPJ4K6e-Q/m/B8OuBGI4BAAJ.
  Found.
* W27. SQLite's WAL. https://www.sqlite.org/wal.html, acc. Checked.
* W28. LMDB:
  https://openldap.org/lists/openldap-technical/201306/msg00092.html,
  2013-06. The move from Berkeley DB: https://lwn.net/Articles/557820,
  2013-07. Found.
* W29. RocksDB's write stalls:
  https://github.com/facebook/rocksdb/wiki/Write-Stalls, found. Solana:
  https://www.helius.dev/blog/what-is-rocksdb, acc., checked. Slow opens:
  https://newreleases.io/project/github/facebook/rocksdb/release/v11.8.1,
  found.
* W30. libmdbx's README and Erigon's disk footprint:
  https://erigon.substack.com/p/more-on-the-disk-footprint-of-erigon.
  Found.
* W31. FlashDB. https://github.com/armink/FlashDB, acc. Checked.
* W32. Zephyr ZMS.
  https://docs.zephyrproject.org/latest/services/storage/zms/zms.html,
  acc. Checked.
* W33. ESP-IDF NVS.
  https://docs.espressif.com/projects/esp-idf/en/stable/esp32/api-reference/storage/nvs_flash.html,
  acc. Checked.
* W34. NuGet: LiteDB, Microsoft.Data.Sqlite, RocksDB, LightningDB,
  Microsoft.FASTER.Core (https://www.nuget.org/packages/{name}).
  ZoneTree: https://github.com/koculu/ZoneTree. Garnet's Tsavorite:
  https://microsoft.github.io/garnet/docs/dev/tsavorite/intro, found. The
  rest acc., checked.
* W35. The end of Realm's Device SDKs.
  https://www.mongodb.com/docs/atlas/device-sdks/deprecation.md, acc.
  Checked.
* W36. Python's shelve and dbm:
  https://docs.python.org/3/library/shelve.html;
  https://docs.python.org/3/library/dbm.html, acc. Checked.
* W37. pypistats: duckdb, diskcache, lmdb, sqlitedict, rocksdict, plyvel.
  https://pypistats.org/api/packages/{name}/recent, acc. Checked.
* W38. eventsourcing 9.5.6, 2026-10-13.
  https://pypi.org/project/eventsourcing/. Checked.
* W39. sqlite-history.
  https://simonwillison.net/2023/Apr/15/sqlite-history/, 2023-04-15.
  Found.
* W40. RubyGems: sqlite3 and lmdb (https://rubygems.org/api/v1/gems/), acc.,
  checked. Rails 8:
  https://rubyonrails.org/2024/11/7/rails-8-no-paas-required,
  2024-11-07, found.
* W41. PHP's dba. https://www.php.net/manual/en/dba.requirements.php, acc.
  Checked.
* W42. Erlang's DETS. https://www.erlang.org/doc/apps/stdlib/dets.html,
  acc. Checked.
* W43. CubDB: https://github.com/lucaong/cubdb;
  https://cubdb.hexdocs.pm/faq.html; https://hex.pm/api/packages/cubdb.
  Acc. Checked.
* W44. "Storage on embedded Nerves device: CubDB limits".
  https://elixirforum.com/t/storage-on-embedded-nerves-device-cubdb-limits/66616,
  2024-10-11. Checked.
* W45. Hex: exqlite, rocksdb, khepri, acc., checked. Khepri as RabbitMQ's
  default: https://www.rabbitmq.com/blog/2025/09/01/6-khepri-default,
  2025-09-01, found.
* W46. Kong's LMDB:
  https://konghq.com/blog/new-storage-engine-for-kong-hybrid-and-db-less-deployments;
  https://developer.konghq.com/support/error-configuration-does-not-fit-in-kong-cache/.
  Found.
* W47. Durable Objects' point-in-time recovery.
  https://developers.cloudflare.com/durable-objects/best-practices/access-durable-objects-storage/,
  acc. Found.
* W48. lsqlite3. https://luarocks.org/modules/dougcurrie/lsqlite3, acc.
  Checked.

The client platforms:

* W50. npm's weekly downloads, 2026-11-02 to 2026-11-08.
  https://api.npmjs.org/downloads/point/last-week/{name}. Checked.
* W51. node:sqlite. https://nodejs.org/api/sqlite.html (Node 26's docs);
  https://github.com/nodejs/node/pull/61262, 2026-02-21. Checked.
* W52. "Deno is joining Cloudflare". https://deno.com/blog/cloudflare,
  2026-10-09. Checked.
* W53. Deno KV: https://docs.deno.com/deploy/kv/manual;
  https://docs.deno.com/deploy/migration_guide/, acc. Checked.
* W54. bun:sqlite: https://bun.com/docs/runtime/sqlite, found. Bun's sale
  to Anthropic, 2025-12-03: found.
* W55. better-sqlite3 in Electron:
  https://docs.triliumnotes.org/developer-guide/troubleshooting/better-sqlite3.html;
  https://github.com/WiseLibs/better-sqlite3/issues/1062. Found.
* W56. NeDB's design (the @seald-io/nedb docs), found. LokiJS:
  https://github.com/techfort/LokiJS, last push 2023-06-22, checked.
* W57. Notion, "How we sped up Notion in the browser with WASM SQLite".
  https://www.notion.com/blog/how-we-sped-up-notion-in-the-browser-with-wasm-sqlite,
  2024-07-10. Checked.
* W58. "Slow IndexedDB". https://rxdb.info/slow-indexeddb.html,
  2026-09-15; RxDB is a vendor. Checked.
* W59. MDN, "Storage quotas and eviction criteria".
  https://developer.mozilla.org/en-US/docs/Web/API/Storage_API/Storage_quotas_and_eviction_criteria,
  2026-01-05. Checked.
* W60. LiveStore on Hacker News.
  https://news.ycombinator.com/item?id=44105412, 2025-05-27. Checked.
* W61. Automerge 3. https://automerge.org/blog/automerge-3/, 2025-07.
  Checked.
* W62. Jazz: https://jazz.tools/docs/concepts/local-first-data-model.
  Loro: https://loro.dev. Datahike:
  https://cljdoc.org/d/io.replikativ/datahike. Acc. Found.
* W63. Zero 1.0. https://www.infoq.com/news/2026/06/zero-version-1,
  2026-06. Found.
* W64. Linear, "Improving performance at scale" (linearapp.notion.site).
  Found.
* W65. PGlite's size: https://electric-sql.com/product/pglite. DuckDB-WASM:
  https://github.com/duckdb/duckdb-wasm/issues/1561. Found.
* W66. GitHub's API: GRDB.swift, SQLite.swift, sqlite-data, realm-swift,
  MMKV, ObjectBox, SQLDelight, drift, Dexie.js, LiveStore. Acc. Checked.
* W67. SwiftData:
  https://fatbobman.com/en/posts/wwdc-2025-first-impressions/;
  https://blog.jacobstechtavern.com/p/high-performance-swiftdata;
  https://developer.apple.com/videos/play/wwdc2024/10075. Found.
* W68. Room 3.0.
  https://developer.android.com/blog/posts/modernizing-the-room,
  2026-03-13. Checked.
* W69. Java on Android: https://developer.android.com/build/jdks;
  https://developer.android.com/about/versions/14/features, acc. Checked.
* W70. VarHandle, "Added in API level 33".
  https://developer.android.com/reference/java/lang/invoke/VarHandle,
  acc. Found.
* W71. H2 on Android:
  https://groups.google.com/g/h2-database/c/lGhaLAnWmU0. Xodus on Android:
  Stack Overflow, question 50143352. Found.
* W72. ObjectBox's FAQ. https://docs.objectbox.io/faq, acc. Checked.
* W73. pub.dev: https://pub.dev/api/packages/{name}/score;
  hive_ce's README,
  https://raw.githubusercontent.com/IO-Design-Team/hive_ce/main/hive/README.md.
  Acc. Checked.
* W74. Flutter's local databases:
  https://parthshethflutterblog.blogspot.com/2026/05/flutter-local-database-comparison.html,
  2026-05; r/dartlang, 2025-01. Found.
* W75. Android vitals, app startup time.
  https://developer.android.com/topic/performance/launch-time, acc.
  Found.

Distribution:

* W80. crates.io's summary. https://crates.io/api/v1/summary, acc.
  Checked.
* W81. cibuildwheel: https://cibuildwheel.pypa.io/en/stable/. maturin:
  https://www.maturin.rs/. Acc. Checked.
* W82. PEP 783: https://peps.python.org/pep-0783/, accepted 2026-04-06,
  checked. PEP 803: https://peps.python.org/pep-0803/, found.
* W83. Node-API: https://nodejs.org/api/n-api.html, checked. napi-rs:
  https://napi.rs/docs/deep-dive/release, found.
* W84. Deno's FFI: https://docs.deno.com/runtime/fundamentals/ffi/. Bun's
  Node-API: https://bun.com/docs/runtime/node-api. Acc. Checked.
* W85. NuGet's native assets:
  https://learn.microsoft.com/en-us/nuget/create-packages/supporting-multiple-target-frameworks,
  2025-10-31. LibraryImport:
  https://learn.microsoft.com/en-us/dotnet/standard/native-interop/pinvoke-source-generation,
  2025-12-04. Checked.
* W86. OSSRH's end:
  https://central.sonatype.org/news/20250326_ossrh_sunset/, 2025-03-26,
  found. JEP 454: https://openjdk.org/jeps/454, checked.
* W87. Kotlin Multiplatform publishing.
  https://kotlinlang.org/docs/multiplatform/multiplatform-publish-lib-setup.html,
  acc. Found.
* W88. Android's 16 KB pages.
  https://developer.android.com/guide/practices/page-sizes, acc. Checked.
* W89. The Swift Package Index: https://swiftpackageindex.com/, acc.,
  checked. CocoaPods' trunk:
  https://blog.cocoapods.org/CocoaPods-Specs-Repo/, 2024-11-30, updated
  2025-05, checked. SE-0482, found.
* W90. Dart's hooks. https://dart.dev/tools/hooks, 2026-07-15. Checked.
* W92. PECL and PIE: https://pecl.php.net/, acc., checked. PIE's RFC:
  https://wiki.php.net/rfc/adopt_pie_deprecate_pecl, found.
* W93. rustler_precompiled.
  https://hexdocs.pm/rustler_precompiled/precompilation_guide.html.
  Found.
* W94. Zig's packages.
  https://nesbitt.io/2026/01/29/zig-and-the-mxn-supply-chain-problem.html,
  2026-01-29. Found.
* W95. createSyncAccessHandle:
  https://developer.mozilla.org/en-US/docs/Web/API/FileSystemFileHandle/createSyncAccessHandle;
  https://raw.githubusercontent.com/mdn/browser-compat-data/main/api/FileSystemFileHandle.json.
  Acc. Checked.
