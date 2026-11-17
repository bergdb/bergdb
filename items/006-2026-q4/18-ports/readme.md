006-18-ports
============

Created 2026-11-09 by Frans Lundberg. Status: open.

BergDB in languages other than Java: which languages, by which route, at
what cost, and what to do first. The study has two parts, written on the
same day by two agents independently: 006-18-01, demand and landscape,
and 006-18-02, technical feasibility (section 8). This readme joins them.
Below, "01" and "02" are those two parts.


## 1. The request

Frans, 2026-11-09, 12:05: "investigate the feasibility of BergDB ports to
languages than Java. The work on porting the Core to C (022 and earlier
item) has shown that this is feasible with limited human work. Add the
study as a subitem of 006. There may have been some minor work on this
before. Check this before you start. The languages included in the study
should be the ones where you think there is demand for something like it,
popular languages, and languages where BergDB can be implemented from a
technical point of view. Good luck!"

The earlier work, found by 01 (section 2): Frans's notes of 2008 to 2016
(2010: "maybe KissDB could support JVM, .NET virtual machine and be
translated to C++"; 2012: KissDB compiled with GCJ to a `.so` for C, and
with IKVM for .NET), 006-08 (a C clone for an embedded target is
feasible), 012 and 022 (the C port), 017-01 (its option 3: "an embedded
database for Java (or a port to Rust or Go)") and 020-03 and 020-05 (what
a binding needs of the object format). Nothing before ranked languages.


## 2. In short

* Feasible in every popular language: nothing in the Core's bytes or files
  is Java's own, and the C port (012, 022), Java's bytes exactly, is the
  base of a binding in every language but Go. The hard part of a native
  port is Java's concurrency, which only Go and C# translate as it is.
* Measured: C took 13.5 hours to Levels 0 to 4, about 2 to follow a
  release. Estimated: a binding 1 to 20 hours, a native port 15 to 40.
* The order: C on Linux (the base), a check of Java's Core on Android,
  bindings in Rust and Python, WebAssembly, Go as a native port.
* BergDB fills gaps in history, space, stalls and startup, not in sync or
  SQL; under AGPL-3.0 little of the demand is reachable.


## 3. The combined ranking

01 ranks by demand and by the opening that the stores in use leave; 02
orders by cost, risk and reach. The combined order takes the languages
that 01 found in demand and orders the work by 02's costs and
dependencies: what the others build on first, a cheap check before a
build, a binding before a native port, and a native port only where a
binding does not serve.

| #  | Language or platform | Route | Hours | 01's rank | 02's step |
|---|---|---|---|---|---|
| 0  | C on Linux, the base    | the C port on Linux; cross sets on s1  | 8–16        | -     | 1 |
| 1  | Java, Kotlin on Android | Java's Core, API level 33 or later     | 4–10        | 7     | 4 |
| 2  | Rust                    | a crate over C; native only for a user | 6–12        | 1     | 3 |
| 3  | Python                  | a binding to C; abi3 wheels            | 10–20       | 3     | 2 |
| 4  | JavaScript, TypeScript  | C as WebAssembly: OPFS, Node, Bun      | 15–30       | 2     | 5 |
| 5  | Go                      | a native port with Java's threads      | 25–40       | 4     | 6 |
| 6  | C#, .NET                | a binding; native after a pause test   | 6–10; 15–30 | 5     | 7 |
| 7  | Dart, Flutter           | `dart:ffi` on C, after C on Android    | 8–16        | 6     | 4 |
| 8  | Swift                   | C as a SwiftPM target                  | 4–8         | 8     | 4 |
| 9  | Elixir, Erlang          | a NIF on C                             | -           | 9     | - |
| 10 | Lua, Ruby, PHP          | FFI or an extension on C               | -           | 10–12 | - |
| -  | C++, Zig                | a wrapper over `bergdb.h`              | 2–4; 1–3    | -     | 1 |
| -  | Kotlin on the JVM       | Java's BergDB as it is                 | 0           | -     | - |
| -  | Deno                    | dropped: its development ends          | -           | -     | - |

Hours are 02's estimates of wall-clock hours of unattended work in 012's
way, without long runs on a quiet machine and without Frans's decisions
(02, section 5.2); "-" where 02 made none. 01's rank is its section 9,
02's step its section 9. Deno's team joined Cloudflare on 2026-10-09 and
its development ends a year later (01's W52).

Where the two orders differ, and why:

1. **C on Linux.** 02 puts it first: C builds on macOS only today
   (`F_FULLFSYNC`; "s1 cannot build C", 022-01, section 5), and every
   binding but Apple's, servers, Android's NDK and s1's cross sets need
   Linux. 01 counts C as done and offers it to Linux devices and to the
   bindings' users without that caveat. Combined: first, as the base.
2. **Rust.** 01 first: the fastest-growing of the top languages, and its
   users are unhappy with sled (beta, format to change), librocksdb-sys
   (slow C++ builds), redb (large files) and fjall (one process); the one
   versioned store, SurrealKV, has no frozen format. 02 third: as a
   binding, cheap, its types stating C's rules; a native Rust port with
   readers in threads is the riskiest port, and its field is crowded
   (017-01, options.md, section 7.1). Both start with a crate over C; 01
   adds that pure Rust is what users ask for. Combined: second, as a crate.
3. **JavaScript and TypeScript.** 01 second: the clearest demand for
   history is in the browser and in local-first apps (LiveStore,
   Automerge, Linear). 02 fifth: 15 to 30 hours, a platform module for
   OPFS whose directory calls are asynchronous, and the browser's
   durability can be tested only in part. Combined: fourth, after the
   cheap bindings; its place is under a sync engine, not instead of one.
4. **Python.** 01 third (the largest user base, but no demand for history
   shown beyond event sourcing, and SQLite in the standard library); 02
   second (the cheapest way to the widest use; C's one caller matches
   Python). Combined: third.
5. **Java on Android.** 01 seventh by demand, but "a cheap check outside
   the study"; 02 fourth. Combined: first of the languages, as a check:
   it needs no second implementation.
6. **Swift and Dart.** 02 puts both with Android in its step 4: Swift is
   cheap on F53's own platform, Dart follows C on Android. 01 puts Dart
   sixth (the sharpest opening on the client: Hive, Isar and Realm were
   abandoned) and Swift eighth (Apple's stores and SQLite dominate).
   Combined: Dart before Swift, by demand.
7. **Go and C#** are in the same order in both, Go first, both as native
   ports in the end. 02 allows a cgo binding first while demand is
   unclear; 01 says Go's users avoid cgo, so a port in Go is the way.
8. **Elixir, Erlang, Lua, Ruby and PHP** are in 01 only (ranks 9 to 12);
   02 does not cover them. Low in both readings.


## 4. Where the two parts disagree on facts

Checked against the code (`main`, 2026-11-09) and the items:

1. **Java's Core on Android, unchanged or not.** 01 (section 5.10): the
   Core uses only `java.base` (006-08, section 6.6), `core.Jmx` is not
   needed by `Db`, so the Core "may run on Android 13 or 14 and later as
   it is". 02 (section 4.8): small changes, as `BufferedStream`'s wait
   statistics call `java.lang.management`. 02 is right:
   `BufferedStream.Waits.add` takes the JVM's uptime from
   `ManagementFactory.getRuntimeMXBean()` whenever the writer waits for
   room in the write buffer and the wait is among the five longest, so at
   the first such wait. It came with 005-46 (`1165c90`, 2026-10-27,
   11:21), after 006-08's count at `f410135` (07:38). Android has no
   `java.lang.management`: one call to change. `VarHandle` is in
   `dag.Handle`, `dag.KeyNode` and `dag.TopNode` (01 names two of them; 02
   adds `Eviction`, which has none).
2. **The embedded target's size.** 02 (section 4.1) writes "the embedded
   target of 006-08 (150 to 200 kB of code)". That is 012-16's measured C
   on arm64 (151 to 178 kB in an application, 170 to 236 kB the library);
   006-08 estimated 35 to 90 kB on a Cortex-M4, as 01 cites. The measured
   151 to 236 kB are on another CPU with other flags, but well above the
   estimate. Whether C fits a microcontroller is open in both.
3. **022's effort.** 02 counts steps 0 to 4 to `3271494` (11:57): 1.6
   hours, 3,683 lines added. Step 4's corrupt-stream set landed after it
   (`a0ba4b7`, 12:16): about 2 hours from 10:21, 4,840 lines added and 558
   removed in `c/`, 3,571 of the added lines tests. Steps 5 (the long
   runs, about 2 hours of a quiet F53) and 6 (the report) remain.
4. **The licence.** 01 makes it the first uncertainty; 02 does not
   mention it, and its order assumes that a binding reaches users.
5. **Native ports in JavaScript, Swift and Dart.** 01's distribution
   table (section 8) calls them "possible"; 02 does not recommend them
   (no 64-bit integers in JavaScript, no shared heap in Dart's isolates,
   ARC on Swift's read path). 01's word is about shipping, 02's about
   doing; no conflict in practice.

The other figures agree: C's 13.5 and 21 hours, Java's 14,677 code lines
of Core, C's 4 MB budget for a million keys, and the roles of Go and C#
as the natural native ports.


## 5. The facts that decide it

**The C port is the base.**

* 012 made it at release 2026.2; 022 brings it to 2026.3 today, then to
  2026.4. It writes Java's stream byte for byte, checked by the cross
  harness (`full`: 1,357 crash cuts and 498 corrupt variants, 0
  differences; 012-16, section 2). At 2026.2, `bergdb.h` had 33
  functions for 35 of `Db`'s 45 public methods.
* C++, Zig, Swift and Rust call C directly; Python, Node, .NET and Dart
  through their FFIs; the browser and Node through WebAssembly. Go's users
  avoid the route (cgo costs their static, cross-compiled binaries), and
  so do Elixir's Nerves users, who chose CubDB for having no native code.
* A binding inherits C's limits (02, section 3.2): one caller per
  database, so readers wait for each other, the opposite of Java's readers
  that never block; durable at sync or close, not within 50 ms; no Pub
  layer, so keys and values of bytes; macOS only (Linux "a day or two",
  012-16, section 7; Windows not started); an API that changes with Java
  (022's D2 removed `retain_duration` and `BERGDB_SYNC_STRONG`).
* A binding pays at a Java release only when `bergdb.h` changes; each
  native port pays 2 to 6 hours a release (02, section 5.2).
* C is code in an item, which items/readme.md calls a prototype for that
  item only, and 022 follows Java "at least 2026.3 and 2026.4" (Frans,
  022's readme). A base for bindings must be kept longer than that.

**Java's concurrency is the hard part of a native port.**

* The Core's bytes and files ask nothing that a language lacks (02,
  sections 2.1 and 2.2): wrapping 64-bit integers, reads and writes at a
  position, file and directory forces, a lock, the deletion of whole
  files; no file is truncated, and no floating point decides anything
  since 005-79. JavaScript needs `BigInt` or 32-bit halves, Python masks.
* Java's readers take no lock and write no shared memory; the writer
  publishes by release and acquire; handles change by compare-and-set; and
  the collector keeps an evicted node alive for a reader that still holds
  it (009-02, section 3).
* Go and C# have a collector and a memory model and can translate this.
  C, C++, Rust, Swift and Zig need safe memory reclamation (epochs, RCU,
  hazard pointers), for which BergDB has no design; reference counts on
  the read path write the shared memory that 009 removed. The Lean model
  does not cover concurrency.
* C avoided the question: one caller at a time. Readers in other threads
  for C: 25 to 50 hours by 02's estimate, its highest risk.

**What C cost, measured** (02, section 5.1, and 022's commits):

| Work | Wall clock | Lines |
|---|---|---|
| 012: the C Core, Levels 0 to 4        | 13.5 h                  |                |
| 012: and its API, measurements, tests | 21 h                    | 53,661 in `c/` |
| 015-02: C follows release 2026.2      | about 2 h               | 1,691          |
| 022-01, steps 0 to 4: C to 2026.3     | about 2 h, no long runs | +4,840, −558   |

Frans's part was decisions and short prompts; his time was not measured.
What made it fast (012-16, section 8.7): byte equality as the single
test, the format written first, Java's vectors, and a harness that
compared the two from the start. Any later port reuses them: the cross
harness takes any implementation whose runner, dumper and scanner have
C's command lines (02, section 6). Every figure for another language is
an estimate from this one port.

**The gaps BergDB fills, and those it does not** (01, sections 5 and 6):

* SQLite holds most of the demand in every language (42.1 percent of
  Stack Overflow's 2026 respondents). Where SQLite is enough, BergDB has
  no case.
* It fills: history kept by hand (reads at a past time, within the retain
  duration); space never returned (LMDB, MDBX, bbolt, Badger, SQLite's
  WAL; reclaim cuts the front); compaction stalls (RocksDB, Pebble, CubDB;
  bounded steps); map-size limits; long startup or replay (Prometheus,
  geth, Hive, LiveStore; only the tail is read, T3).
* It does not fill: sync between devices, which local-first users want
  most; SQL; several processes; write amplification (867 bytes of stream
  a put at 10M keys and a 50 MB startup distance, 006-19); a
  format kept across releases (005-50); the trust that a maintainer stays.
* The clearest demand for history is where it is now built at great
  cost: the browser and local-first apps, Rust (SurrealKV), Go (immudb,
  under the BSL), Elixir's Nerves devices (CubDB, retention by hand). No
  embedded store with history was found for .NET, Android, Swift or
  Flutter.

**The licence.**

* BergDB is AGPL-3.0 (`LICENSE`), and the repository is private (017-01).
  The C port and any binding carry the same licence.
* The ecosystems are mostly MIT and Apache; Berkeley DB's move to the AGPL
  in 2013 sent its users to LMDB (01's W28); apps in stores rarely take
  copyleft; immudb's BSL is itself a complaint. 01's ranking assumes a
  permissive or a dual licence.
* The choice is 017-01's option 1 (AGPL as now, Apache or MIT, or dual).
  It does not block work inside the repository, but it decides whether a
  published port reaches anyone.

**Android 13 or later may run Java's Core, almost unchanged.**

* `VarHandle` is on Android from API level 33 (Android 13); Android 14
  brought `java.base` up to Java 17, BergDB's minimum (01's W69, W70).
  Which of the two is the floor is for the check to show.
* One call must change, in `BufferedStream`'s wait statistics (section
  4, point 1). `Jmx` is not needed by `Db`; Data Objects need R8 keep
  rules for their field names (02, section 4.8).
* Not run: the Android SDK and an emulator are not on F53. 02 estimates 4
  to 10 hours.
* If it runs, Java and Kotlin on Android, and Kotlin Multiplatform's
  Android side, get BergDB with no second implementation; bounded startup
  meets Android's 5 s limit for a cold start and its kills in the
  background (01's W75).

**The Pub layer.** A binding gives keys and values of bytes. Format 2
(020-07) is language-neutral and has vectors; the indexes have none yet;
Data Objects are Java's, by reflection, and each language converts its own
objects (02, section 7). Written once in C under every binding, after
2026.4 freezes format 2: 15 to 30 hours by 02's estimate, better than one
Pub layer per language from two bindings on.


## 6. The first steps

The recommendation: build on the C port, and make no native port until a
user asks for one; a binding is the cheap way to learn whether anyone
does. Steps 1 and 2 are independent of each other.

1. **Check Java's Core on Android.**
   * Cost: 4 to 10 hours (02's estimate), most of it the Android SDK and
     an emulator; the one call of section 4 changed in a copy in this
     item; a smoke test of `Db` on a file, then 006-08's `CoreDemo`.
   * Shows: whether Android and Kotlin cost anything at all, and which
     API level is the floor.
   * Frans decides first: whether Android is in scope; the SDK and an
     emulator on F53 (several GB, and a slot when F53 has room); and
     whether the one-line change goes into `java/`: a change of the Core,
     best after 2026.4's tag.
2. **C on Linux.**
   * Cost: 8 to 16 hours, 500 to 1,500 lines (02's estimate; "a day or
     two", 012-16, section 7): `plat.c`'s forces for Linux, the build and
     the cross sets on s1.
   * Shows: C where servers, Android's NDK and most binding users are; a
     second machine for C's cross sets; the base of every binding but
     Apple's.
   * Frans decides first: that C becomes a maintained base rather than
     022's clone: where it lives (today an item's code), how long it
     follows Java, a versioned `bergdb.h`; and whether Linux is 022's
     next step after 2026.4 or an item of its own. Before 022's 2026.4
     port lands, it would collide with 022's work in `c/`.
3. **A first binding: Rust, a crate over C** (or Python).
   * Cost: Rust 6 to 12 hours (`cc` builds C's sources, so no binaries to
     ship); Python 10 to 20 with wheels, which need a CI that BergDB does
     not have.
   * Shows: whether `bergdb.h` makes a good API in another language (a
     read context's values borrowed from it, a database `Send` but not
     `Sync`), the cost of packaging, and something to show the users of
     01's first language.
   * Frans decides first: the licence, or at least whether ports will be
     published (017-01, option 1): a private binding shows the API but
     tests no demand; and Rust first (01's order) or Python first (02's).

Not now: WebAssembly (15 to 30 hours) until a local-first user wants
history under a sync engine; native ports in Go (25 to 40) and C#
(15 to 30, after a measurement of .NET's pauses under eviction) until a
user asks; C's readers in other threads and a C Pub layer until two
bindings need them. Not at all: native ports in Python, JavaScript, Swift,
Zig, Dart, C++ and Kotlin/Native. At any time, a Python scanner and dumper
(4 to 8 hours) would be an independent second reader of the format, a
check rather than a port (02, section 9).


## 7. What is uncertain

The ones that matter most, first:

1. **The demand for reading the past** is inferred from neighbours
   (SurrealKV, immudb, Litestream, LiveStore, Automerge, Jazz) and from
   complaints; no survey asks about it, and no user was asked (01,
   section 11). A port should start with a user who has the need.
2. **The licence.** Under AGPL-3.0 most of 01's demand is out of reach.
3. **Every effort figure outside C** is extrapolated from one port, made
   one way: a plan before the code, byte equality as the oracle. Such
   figures are loose in both directions: 012-18 estimated 4 to 6 hours of
   coding for 2026.3, and steps 0 to 4 landed in about 2.
4. **Concurrency.** Readers in other threads without a collector have no
   design, and the Lean model does not cover concurrency. Until then a
   binding's readers wait for each other.
5. **Small startup distances**, which phones and browsers need: their
   write cost and memory are not measured (006-08, section 6.8).
6. **The format and the API across releases** (005-50; 022's D2): each
   binding and each native port multiplies the cost of a change.
7. **The platforms not tried:** Android was read, not run; OPFS's
   durability rests on MDN and one run in a bug report, by which Chrome
   forced nothing for a new file (02's W6); collectors' pauses under
   eviction are measured for Java only; Windows is untested for Java and
   C; BergDB has no CI and no Windows machine.
8. **Sync.** Local-first users want sync more than history, and BergDB
   has none (017-03).


## 8. Files

* [01-demand.md](01-demand.md). 006-18-01, demand and landscape: what
  BergDB offers a user in another language, popularity and trend, what
  each language's users store with today and complain of, where the traits
  meet a need, distribution, the ranking by demand and opening, and what
  is uncertain; web sources W1 to W95, dated and marked checked or found.
* [02-technical.md](02-technical.md). 006-18-02, technical feasibility:
  what the Core needs of a language and a platform, a native port against
  a binding to the C port, WebAssembly, each language, the effort
  measured and estimated, conformance, the Pub layer, the order by cost,
  risk and reach, and what is uncertain; facts marked [M] measured, [R]
  read, [W] web, [E] estimate; web sources W1 to W20, numbered apart from
  01's.
* [03-android-check.md](03-android-check.md). 006-18-03, the Android
  check (Frans, 12:43: "Android ... is in scope"): the Core runs on Android
  13 (API 33) with one fix (`java.lang.management` in `BufferedStream`),
  objects need a second (`DataObjects`) and API 34; both fixes on a branch,
  not in 2026.4; the emulator runs, the floors, G88 (ART decodes `ed a0 80`
  to three U+FFFD, 020-09 pins Java's one), and the effort to a supported
  Android release (3 to 5 days).


## Log

2026-11-09. Created at Frans's request (12:05) by coord-1109: 01 and 02
written independently by its agents pd18 and pt18, from the brief's
reading list and the web; this readme by ps18 from the two, with the
facts of section 4 checked in the code and Git. Nothing built or run.

2026-11-09. 006-18-03, the Android check, by coord-1109's agent an18
(12:44 to 13:37), at Frans's word (12:43).
