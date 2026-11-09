# 006-18-02 Technical feasibility

Created 2026-11-09 by Frans Lundberg. Status: done.

Part of 006-18, BergDB in languages other than Java: what it takes,
technically, to have BergDB in C, C++, Rust, Go, Python,
JavaScript/TypeScript, C#/.NET, Kotlin, Swift, Zig and Dart. What the
Core needs of a language and a platform (section 2); the two ways, a
native port or a binding to the C port (section 3); each language
(section 4); the effort, from 012's and 022's figures (section 5); how a
port shows that it is BergDB (section 6); the Pub layer (section 7); the
table and the recommended order (sections 8 and 9); what is uncertain
(section 10). Demand is the study's other part; the order here is by
cost, risk and reach.

Frans, 2026-11-09, 12:05: "investigate the feasibility of BergDB ports to
languages than Java. The work on porting the Core to C (022 and earlier
item) has shown that this is feasible with limited human work. [...] The
languages included in the study should be the ones where you think there
is demand for something like it, popular languages, and languages where
BergDB can be implemented from a technical point of view."

How each fact is known, marked where it matters:

* **[M] measured**: a figure of 012, 015-02 or 022, from their reports,
  logs and Git history.
* **[R] read**: in BergDB's code or items, `main` at `94a1520` and the
  tree of 2026-11-09, noon; or in Frans's notes of 2012 to 2016 (F1-007).
* **[W] web**: a source of section 11, read on 2026-11-09.
* **[E] estimate**: this study's, with its basis named. Every effort
  figure for a language other than C is one.

Nothing was built or run: F53 was busy, and the brief allowed reading and
web research only.


## 1. In short

* **The Core asks little that a language cannot give**: 64-bit integers
  with wrapping arithmetic, bytes, reads and writes at a position, a file
  force and a directory force, a lock, and the deletion of whole files.
  No floating point decides anything since 005-79, no file is truncated,
  and nothing in the stream is Java's own [R]. Every candidate can write
  the stream byte for byte; JavaScript only with `BigInt` or 32-bit
  halves.
* **What is hard is what Java's runtime gives for free**: readers that
  never block, that read index nodes while one writer appends to them and
  while eviction drops them. Java does it with its memory model (volatile
  publication, compare-and-set on handles; 009-02, section 3) and its
  garbage collector, which keeps a dropped node alive for a reader that
  still holds it. A language with a collector and a memory model (Go, C#)
  can translate it. One without (C, C++, Rust, Swift, Zig) needs safe
  memory reclamation (epochs, RCU, hazard pointers), for which BergDB has
  no design. Reference counting on the read path (Rust's `Arc`, Swift's
  ARC) writes shared memory, which 009 removed from Java's reads so that
  readers scale. The C port avoids the question: one caller at a time.
* **Two ways.** A native port costs about what 012 cost and must follow
  every Java release. A binding to the C port costs hours to days and
  follows C. A binding inherits C's limits: one caller per database (a
  lock in the binding, so readers wait for each other), durability at
  sync or close (no storage thread), macOS only today (Linux "a day or
  two", 012-16, section 7), and no Pub layer.
* **Measured** [M]: 012 made the C Core, Levels 0 to 4, in 13.5 hours of
  unattended agent work from Frans's go, and was done in 21 hours: 53,661
  lines, 21,226 of them the library and 25,085 tests. Following a release
  took about 2 hours (2026.2, 1,691 lines) and 1.6 hours of wall clock
  for 022's steps 0 to 4 (2026.3; 3,683 lines added, 2,504 of them
  tests; its long runs not yet made). Frans's part was decisions and
  short prompts.
* **Estimated** [E]: a binding, 1 to 20 hours, most 4 to 12;
  JavaScript/TypeScript through WebAssembly with the browser's file
  system (OPFS), 15 to 30 hours; a native port, 15 to 40 hours, as 012;
  a C Pub layer, 15 to 30 hours; readers in other threads for C, 25 to 50
  hours and the highest risk.
* **Conformance carries over.** The cross harness (012-05) runs any
  implementation that provides a runner, a dumper and a scanner with C's
  command lines; Java's vectors (12 text files) and the object vectors
  (020-07) are language-neutral. A binding needs only API tests.
* **The Pub layer** is half language-neutral (format 2, the index keys
  and encodings) and half Java's (Data Objects by reflection, Java's
  conventions, threads for index jobs). Each language converts its own
  objects; the format and the indexes are best written once, in C, when
  there are two bindings or more.
* **Recommended order** (section 9): C on Linux first, with the C++ and
  Zig wrappers; then the cheap bindings that fit C's model: Python, Rust,
  Swift, and Java itself on Android; then JavaScript/TypeScript through
  WebAssembly (browser and Node); then Go as the first native port with
  Java's concurrency; C# after a measurement of its collector's pauses;
  Dart once C builds for Android. Not recommended: native ports in
  Python, JavaScript, Swift, Zig, Dart, C++ or Kotlin/Native, and a
  native Rust port before there is demand for one.


## 2. What the Core needs of a language and a platform

### 2.1. Bytes: the stream format

From 012-01, sections 3 and 6.2, and 012-02 [R]:

* Little-endian integers of 1, 2, 4 and 8 bytes; records at multiples of
  8; a meta block of 128 bytes at every multiple of 200,000; a
  Fletcher-16 checksum per node (no checksum per record; 017-08).
* Keys in segments of up to 7 bytes, packed in 64-bit compare values
  (klongs), compared signed or unsigned as Java's code does; an ikey's
  UTF-8 bytes with `/` as 1 and every other byte plus 2.
* Java's integer semantics: wrapping (`Keys.hash`), `>>>`, shift counts
  masked, Java's division, signed bytes. C needs `-fwrapv` and the 228
  lines of `jsem.h`, "Java's semantics in C".
* No floating point decides anything in the Core Layer since 005-79,
  which `doubles.py` checks before every commit (levels.md, section 2):
  no language's rounding can change the bytes.
* Text in the stream: reclaim's table (a `StringMap` of decimal longs),
  its settings (`retain=<d>\nfraction=<f>\n`, 015-87), and the dummy
  transaction of `setStartupDistance`.
* Times in 100 ns units since 1970, below 2^56; a database id of 16
  random bytes.

64-bit integers by language (the languages' own rules, not tried here):

| Language   | 64-bit integers that wrap |
|---|---|
| C, C++     | `int64_t`, wrapping by `-fwrapv` or unsigned types (`jsem.h`) |
| Rust       | `i64`, `u64`; `wrapping_*` (a plain overflow panics in debug) |
| Go         | `int64`, `uint64`; they wrap by the spec |
| C#         | `long`, `ulong`; they wrap unless `checked` |
| Kotlin     | `Long`, as Java |
| Swift      | `Int64`, `UInt64`; `&+`, `&*` (a plain overflow traps) |
| Zig        | `i64`, `u64`; `+%`, `*%` (a plain overflow is illegal) |
| Dart       | `int`: 64 bits, wrapping, on native targets; 53 bits on the web |
| Python     | unbounded `int`: every result masked to 64 bits by hand |
| JavaScript | none: `BigInt` (each value allocated) or two 32-bit halves |

### 2.2. Files and forces

C's platform module (`plat.h`, 149 lines; `plat.c`, 406) is the whole
list of what the Core asks of an operating system [R]: list a directory;
make directories; open a file to read, or to read and write; read and
write at a position; a file's length; force a file (`F_FULLFSYNC` on
macOS, else `fsync`); force a directory; delete a file; an exclusive lock
on `bergdb.lock`; the time in milliseconds; random bytes. And an I/O seam,
so that the power-loss model can drop what was not forced. No file is
truncated: reclaim's cut deletes whole files from the front
(`FileStream.pretruncate`), and a start completes a torn tail by
appending (levels.md, section 8).

The order of the forces is part of the promise (levels.md, section 8;
022-01, step 3) [R]:

1. a new file and its directory entry are forced before the file takes
   appends;
2. the old last file is forced before a new file is made (the switch
   force, which C lacked until 022-01's step 3);
3. the files are forced before a cut's deletes, and the directory after
   each delete;
4. the crash contract (014-01, section 7): after a crash the stream is a
   prefix of what was appended, at least up to what was forced; the
   storage provider ensures it.

On macOS a plain `fsync` does not flush the drive's cache; `F_FULLFSYNC`
does. What each standard library's force does there:

| Language     | A file's force on macOS                                   | A directory's |
|---|---|---|
| Java         | `force(true)`: `F_FULLFSYNC` (levels.md, 8) [R]           | open it, force [R] |
| C, C++, Zig  | `fcntl(F_FULLFSYNC)` by hand, as C's `plat.c` [R]         | `open`, the same |
| Rust         | `sync_all`: `F_FULLFSYNC` since 2019 (W1)                 | open it, `sync_all` |
| Go           | `Sync`: `F_FULLFSYNC` since 1.12, `fsync` on ENOTSUP (W2) | open it, `Sync` |
| Node         | `fsync`: libuv tries `F_FULLFSYNC`, then a barrier (W3)   | open it, `fsync` |
| .NET         | `Flush(true)`: `F_FULLFSYNC` (W4)                         | no managed API [E] |
| Python       | `os.fsync` is plain `fsync`; `fcntl.F_FULLFSYNC` (W5)     | `os.open`, `fsync` |
| Swift, Dart  | not checked; `fcntl` through Darwin or FFI                | the same |
| Browser OPFS | `flush()` "persists [...] to disk" (W6)                   | none exists |

The column matters for native ports only: a binding uses C's `plat.c`.

**Windows.** Neither Java nor C is tested there (levels.md, section 8).
A directory cannot be forced, and a file that another handle has open can
be deleted only if it was opened to allow it [E]. Frans's run of KissDB on
Windows in 2012, through IKVM, failed its tests that delete stream files
(`2012-08-four-environments.txt`) [R]. A Windows version of `plat.c` is
a task of its own (section 5.2).

### 2.3. Threads and a memory model

Java's Core has these threads [R]: the application's readers (`getOne`,
`getMany`) and writers (`execute`, serialized by `writeLock`, with the
STM's optimistic check); the storage thread (`BufferedStream`: chunks
written within the buffer time, 50 ms, and group commit); the eviction
thread (`bergdb-evictor`); `FileStream`'s thread that deletes a cut's
files (005-46); and the closer of `stop()`. The Pub layer adds a thread
per index build and cleanup (`IndexBuilderImp`, `IndexManager`).

The design (`Db.java`, its note "Concurrency" of 2015 and 2026; 009-02,
section 3) [R]:

* **Readers never block**, but on stream reads. A reader takes no lock
  and writes no shared memory: "What the fast path must not do
  (Masstree's rule, 004-01, 3.4): take a lock, or write shared memory"
  (009-02, 3.1). 009 removed the readers' empty `synchronized (readSync)`
  blocks for that reason: every get wrote the monitor's word, which all
  readers share, and readers did not scale.
* **Publication by release and acquire.** The writer appends to a key
  node beyond its `size` and then writes `size` (volatile); a reader
  reads `size` first. The writer's changes happen before the clock's
  volatile write, from which a reader takes its lookup time.
* **Handles** (009): a node's object in a volatile field, the state
  changed by compare-and-set, the written position volatile because a
  plain `long` may tear (JLS 17.7). Seven jcstress tests and a control
  that shows a race check the barriers (`java/stress/jcstress/`).
* **The collector is the reclaimer.** Eviction sets a handle's object to
  null while a reader may still follow the node; the reader's reference
  keeps it alive. Correctness "cannot depend on a favorable GC schedule"
  (011-08, section 7), but its safety does depend on there being a
  collector.

What a port needs for the same design:

* **Atomics with acquire and release, and compare-and-set**, in a defined
  memory model: C11, C++11, Rust, Go (its model of 2022), C#, Swift 6
  (the `Synchronization` module's `Atomic`, W20), Zig, Kotlin on the JVM.
  Python cannot express the design, with or without its lock; JavaScript
  workers share bytes (`SharedArrayBuffer`), not objects; Dart's isolates
  share no heap.
* **Safe memory reclamation**: a collector (Go, C#, Kotlin/JVM, Dart), or
  epochs, RCU or hazard pointers (C, C++, Rust, Zig, Swift). Reference
  counts on the read path (Rust's `Arc`, Swift's ARC, C++'s
  `shared_ptr`) write a shared counter at each step down the tree, the
  write that 009 removed; so does a reader-writer lock's read side. C++26
  has an RCU library, `<rcu>` (W11); Rust has crossbeam-epoch; C has
  liburcu. No BergDB design uses them, and the Lean model does not cover
  concurrency (levels.md, section 1).

C's answer (012-01, 4.2; `bergdb.h`) [R]: no threads, no locks, no
atomics. A database is used by one thread at a time, as a `FILE`;
different databases by different threads. What Java's threads do happens
in the calls: the buffer is written when full, at sync and at close;
eviction runs at the end of calls. Calm when idle (P3) follows. The cost:
a transaction is durable at sync or close, not within 50 ms; and readers
in parallel need the caller's lock.

### 2.4. Memory: eviction and the bytes per key

* Level 4 evicts the index to a budget; what stays is pinned: the super
  root, D (bounded by the startup distance), the record being written and
  the newest written top node (levels.md, section 7; 006-08, 6.4) [R].
* MEM, Java's heap bytes per key-value pair: 129 to 130 on F53; C's
  allocator, 123 for the same workload; with 24-byte keys C needs 3 to 7
  percent less than Java [M, 012-15, 6.3]. The layout (arrays of 64-bit
  klongs) sets the size, not the language, in any language that stores
  an array of `long` flat.
* C counts every byte in its allocator, so its budget is exact: at a 4 MB
  budget on a million keys, at most 3,999,972 bytes resident [M, 012-16,
  2]. Java's budget is an estimate of the heap.
* The collector's cost (README, "Pauses") [M]: with ZGC, or Shenandoah
  without generations, no get or commit waits more than about 20 ms for
  BergDB's own work; with G1 the pauses "reach hundreds of milliseconds
  under eviction". Eviction makes objects that live a while and then die,
  a pattern that generational collectors handle badly. So a concurrent
  collector without generations (Go's) is the safer fit, and a
  generational one (.NET's, V8's, Dart's) a risk to measure [E].
* A language that boxes its integers (Python's `int`, JavaScript's
  `BigInt`) multiplies the bytes per key [E].

### 2.5. The needs, by language

| Language   | 64-bit bytes  | Forces         | Atomics, model | Reclamation       | Budget |
|---|---|---|---|---|---|
| C          | yes, `jsem.h` | yes            | C11         | by hand; none yet | exact |
| C++        | yes           | yes            | C++11       | C++26's RCU       | exact |
| Rust       | yes           | yes            | yes         | epoch crates      | exact |
| Go         | yes           | yes            | yes (2022)  | collector         | estimated |
| C#         | yes           | dirs: P/Invoke | yes         | collector         | estimated |
| Kotlin/JVM | Java's        | Java's         | Java's      | collector         | Java's |
| Swift      | yes, `&+`     | `fcntl`        | Swift 6     | by hand; ARC      | exact |
| Zig        | yes, `+%`     | yes            | yes         | by hand           | exact |
| Dart       | native only   | through FFI    | none shared | collector         | typed lists |
| Python     | by masking    | `fcntl`        | no          | collector         | boxed |
| JavaScript | `BigInt`      | Node; OPFS     | no          | collector         | typed arrays |


## 3. Two ways: a native port, or a binding to the C port

### 3.1. A native port

* It is another implementation, with its own conformance (section 6) and
  its own cost at every Java release. For C [M]: about 2 hours for 2026.2
  (015-02); 1.6 hours of wall clock for 022's steps 0 to 4 of 2026.3, and
  about 2 hours of a quiet F53 for its long runs (012-18, 5.1); 022-02
  estimates 3 to 4.5 hours and 1.5 hours of runs for 2026.4.
* It can be idiomatic: no C toolchain, easy cross-compilation (pure Go,
  pure Rust), and Java's concurrency where the language allows it.
* It reads Java with fresh eyes: 012 found 005-70, a correctness bug, and
  six more findings (012-16, 5); 022's step 2 found 021-11, fixed in
  `da6c5b0` ("Found by reading in the C port") [M].

### 3.2. A binding to the C port

C's API is `bergdb.h`: 33 functions for 35 of `Db`'s 45 public methods
(012-16, 2), now at 2026.3 (022) [R]. What a binding meets:

* **The cost of a call**: none for C++, Zig, Swift and Rust, which call
  C directly; tens of nanoseconds for Go's cgo (about 54 ns from Go to C,
  149 ns from C to Go, W13) and .NET's P/Invoke; more for Python and
  Node-API [E]. C's `getOne` from memory takes about 1.2 µs (844,453 a
  second at 1M keys, 012-16, 3) [M], so a call's cost matters little.
  `getMany`'s callback per pair (6.7 million pairs a second in C) does: a
  binding should copy batches out rather than call back for each pair
  [E].
* **Lifetimes**: a value from `bergdb_get` is valid until the read
  context's next call (012-01, 5). Rust can say so in a lifetime; other
  languages copy.
* **One caller**: the binding holds a lock per database. In a host with
  threads (Go, C#, Rust, free-threaded Python, a Java server) readers then
  wait for each other and for the writer: the opposite of Java's "readers
  never block" [R]. Until C gets readers in other threads (012-16, 7,
  step 5; section 5.2).
* **When bytes reach the disk**: C writes its buffer only when full, at
  sync and at close; a transaction that nobody syncs is not written
  within 50 ms as in Java (`c/readme.md`, section 9) [R]. A binding can
  sync on a timer, at a force each time; or C can write the buffer at the
  start of any call when the buffer time has passed (012-01, 4.3) [E].
* **Platforms**: C builds on macOS with Apple clang 21 only. Linux is "a
  day or two" (012-16, 7: `F_FULLFSYNC` becomes `fsync`, and the cross
  sets run there); s1 cannot build C today (022-01, 5) [R]. Windows is
  not started. iOS is Darwin, and Android is Linux with its own C library
  [E].
* **Distribution**: where the ecosystem builds C from source (SwiftPM's
  C targets, Cargo with the `cc` crate, Zig's build, Dart's build hooks
  with `native_toolchain_c` since Dart 3.10, W14), a binding ships C's
  sources. Where it expects binaries (Python's wheels, npm, NuGet,
  Maven), it needs a build per OS and CPU (macOS arm64 and x64; Linux
  glibc and musl, x64 and arm64; Windows) and a CI that BergDB does not
  have [E].
* **No Pub layer**: C is the Core only (012-01, 1). A binding's users
  get keys and values of bytes until the Pub is ported (section 7).
* **Safety**: C is tested under AddressSanitizer and
  UndefinedBehaviorSanitizer, with `leaks` and allocation failures in
  turn (012-16, 2, item 6) [M]. The boundary is the binding's: a use
  after close, a database used by two threads. A binding should make
  them impossible (Rust's types) or checked (a flag, a lock) [E].

### 3.3. WebAssembly

C compiles to WebAssembly with Emscripten or wasi-sdk [E: not tried]. It
needs no threads, which matters: in a browser, threads need
`SharedArrayBuffer`, and that needs a cross-origin isolated page (the
headers COOP and COEP) (W8).

* **The browser**: the origin private file system (OPFS). Its
  `FileSystemSyncAccessHandle`, in a dedicated worker, reads and writes
  at an offset and has `getSize`, `truncate`, `flush` and `close`,
  synchronous since Chromium 108; `flush()` "persists any changes [...]
  to disk"; widely available since March 2023 (W6). The directory's
  operations (`getFileHandle`, `removeEntry`, `entries`) are
  asynchronous, so C's synchronous `plat.c` needs JSPI or Asyncify, or
  SQLite's way: a pool of handles opened before use (`opfs-sahpool`,
  which needs no COOP or COEP; W7). A file has one sync handle at a
  time, which is the lock; another tab talks to the worker that owns the
  database. There is no directory force: whether a new file's name
  survives a power loss is the browser's affair. In one run of 2026-09,
  a `flush()` made one fsync in Chrome and in Firefox, while a file's
  creation, write, close and delete made none in Chrome and 21 in
  Firefox, about 75 ms on Linux (W6): by that count Chrome forced
  nothing for a new file, where BergDB's rule 1 (2.2) asks for a force
  of the file and its name. A browser may evict an origin's
  storage unless `navigator.storage.persist()` is granted [E].
* **Memory**: WebAssembly's 32-bit memory has 4 GB; it grows and never
  shrinks. 64-bit memory shipped in Chrome 133 and Firefox 134, not in
  Safari (W9). BergDB's budget bounds the index's memory, so Level 4,
  data larger than memory, is what makes BergDB fit a browser: the data
  in OPFS, a budget of some tens of MB [E].
* **Node**: the same module with Node's files (Emscripten's NODEFS, or
  WASI), whose `fsync` goes through libuv's `F_FULLFSYNC` (W3); or a
  Node-API addon of C.
* **WASI**: 0.3 is stable, without threads, which later 0.3 releases are
  to add (W10).
* A precedent: SQLite's own WebAssembly build keeps databases in OPFS
  (W7).

### 3.4. A third way: compile the Java code

In 2012 Frans compiled KissDB with GCJ into a native library, "kissdb.so",
"as a library on Linux C projects without any hassle", and with IKVM into
.NET; both passed the unit tests on Linux and ran gets at most 2 times
slower than Java (`2012-04-gcj.txt`, `2012-08-four-environments.txt`, the 2012 log of
June 8 and December 6 and 7, where he used it from C#) [R]. Today GCJ is
gone, and IKVM supports Java SE 8 only (W16), while BergDB needs 17.
GraalVM's Native Image builds a shared library with a C API (W15): one
implementation, nothing to keep in step. But its default collector,
Serial, is a "stop and copy" collector, neither parallel nor concurrent,
and G1 is not in every edition and platform (W15): under eviction the
pauses would be G1's or worse [E]. Worth a day's experiment when F53 is
free [E], not a plan.


## 4. Language by language

### 4.1. C

Done: 012 (release 2026.2), 022 (2026.3 in progress; 2026.4 studied in
022-02) [R]. What other languages would build on and is missing: Linux;
Windows; readers in other threads; a Pub layer; a versioned API, as a
binding must follow changes such as 022's D2, which removed
`retain_duration` and `BERGDB_SYNC_STRONG` from `bergdb.h`. The embedded
target of 006-08 (150 to 200 kB of code, raw flash) is open.

### 4.2. C++

* **A wrapper over C**: one header, RAII for the database and its read
  contexts, `std::span` and `std::string_view`, errors as exceptions or
  `std::expected`: 2 to 4 hours [E]. Recommended.
* **A native port** gains nothing over C, unless C++'s atomics and RCU
  (C++26, W11) make it the language of a concurrent native version. C11
  with liburcu can do the same. Not recommended now.

### 4.3. Rust

* **The needs**: all; wrapping operations by name; `sync_all` forces
  with `F_FULLFSYNC` (W1); a directory is forced by opening it.
* **A binding**: `extern "C"` declarations (or bindgen) and the `cc`
  crate, which compiles C's sources in `build.rs`, so no binaries to
  ship. A safe wrapper: a read context's values borrow from it, and a
  database is `Send` but not `Sync`, which states the one-caller rule in
  types. 6 to 12 hours with tests [E].
* **A native port**: with C's design (one caller), the node table and
  C's counted references become an arena with indices; about 012's size,
  20 to 30 hours [E]. With readers in threads: unsafe code, epoch
  reclamation, and tests with loom and Miri, 15 to 30 hours more and a
  high risk [E]. 017-01 (options.md, 7.1) found no need for one: "A Rust
  port would compete with redb and sled".
* **Memory**: no collector; an exact count, as C.
* **The Pub**: serde, with `Option` for an absent field (020-03, 6.2).

### 4.4. Go

* **The needs**: `int64` wraps; `File.Sync` forces with `F_FULLFSYNC`
  (W2); typed atomics (`atomic.Int64`, `atomic.Pointer`) for Java's
  volatile fields and compare-and-set; mutexes for monitors; goroutines
  for the storage and eviction threads.
* **A native port**: of the languages without a JVM, the nearest to
  Java's design: its threads become goroutines, its volatile fields
  atomics, and the collector keeps a node alive for a reader. Errors are
  values, as in C. 25 to 40 hours, 012's size with the concurrency
  [E]. The race detector and Go's memory model take jcstress's place.
  Risks: a translation that misses a volatile (a racy slice, string or
  interface may tear in Go); the collector's assists slowing the writer
  under eviction [E].
* **The collector**: concurrent, without generations, as BergDB's advice
  for Java (ZGC, Shenandoah without generations); `GOMEMLIMIT` bounds the
  heap. Its pauses under eviction are not measured [E].
* **A binding with cgo**: 6 to 10 hours [E]. But cgo costs Go's easy
  cross-compilation and static binaries, and Go's own databases are
  mostly pure Go (bbolt, Badger, Pebble) [E]. A stopgap.
* **The Pub**: reflection over exported struct fields with tags, as
  `encoding/json`: close to Java's rule of public fields (020-09, 3) [E].

### 4.5. Python

* **A binding**: a CPython extension (the C API, cffi or nanobind) over
  C. One caller per database fits Python: release the interpreter's lock
  during I/O and hold a lock per database, which the free-threaded build
  of 3.14, now officially supported (W17), needs anyway. 6 to 12 hours,
  and 4 to 8 more for wheels with cibuildwheel (macOS, manylinux,
  musllinux; Windows when C runs there) [E].
* **A native port**: possible (masking, `array('q')`,
  `fcntl.F_FULLFSYNC`), but 30 to 100 times slower and several times the
  memory per key, with no readers in parallel [E]. Useful only as an
  independent second reader of the format, as 020-07's `check.py` was for
  the object vectors: a scanner and a dumper in Python, 4 to 8 hours, a
  tool for conformance, not a product [E].
* **The Pub**: dicts and dataclasses; `int` and `float` are distinct, as
  in format 2; `None` as absence (020-03, 6.2).

### 4.6. JavaScript and TypeScript

* **A native port**: no 64-bit integers (`BigInt` allocates; pairs of
  32-bit halves are error-prone), no objects shared between workers, a
  generational collector. Not recommended.
* **WebAssembly** (section 3.3): C compiled, a platform module for OPFS in
  the browser and one for Node's files, a TypeScript API, tests in a
  headless browser: 15 to 30 hours [E]. One artifact for every OS. The
  power-loss model runs through C's I/O seam, but OPFS itself cannot be
  tested for a power loss here [E].
* **A Node-API addon**: 6 to 12 hours, and binaries for each platform, as
  better-sqlite3 ships them [E].
* **The Pub**: JavaScript has one number type, so a binding must decide
  whether `1` is format 2's integer or double, which Java's binding takes
  from the field's declared type; integers above 2^53 need `BigInt`;
  names and strings must be compared as UTF-8 bytes, not UTF-16 units
  (binson-js's fault JS1, 020-05, 8.1) [R].

### 4.7. C# and .NET

* **A native port**: the language nearest to Java: classes, a collector,
  `volatile`, `Volatile.Read` and `Write`, `Interlocked.CompareExchange`,
  `lock`, exceptions, generics over value types. A translation from Java
  class by class, with Java's threads: 15 to 30 hours [E].
  `FileStream.Flush(true)` forces with `F_FULLFSYNC` on macOS (W4); a
  directory force needs P/Invoke on Unix and has no counterpart on
  Windows [E].
* **The collector**: generational, with a background collection of the
  old generation; compaction and some phases stop the threads; Satori, a
  low-latency collector, is experimental (W19). Java's evidence (G1 at
  hundreds of milliseconds under eviction) makes this the main risk:
  measure a prototype's pauses under eviction before the port [E].
* **A binding by P/Invoke**: 6 to 10 hours, and NuGet's packages per
  runtime [E].
* IKVM, Frans's way of 2012, now supports Java 8 only (W16).
* **The Pub**: reflection or source generators, over public fields and
  properties.

### 4.8. Kotlin

* **Kotlin on the JVM** (and Scala, Clojure, Groovy): BergDB's jar as it
  is, no work. A Kotlin API (extension functions, `use`) is optional.
* **Android**: Java's own Core on Android's runtime. `VarHandle` needs
  API level 33 (W12), and `Handle`, `KeyNode`, `TopNode` and `Eviction`
  use it [R]; earlier levels need `AtomicReferenceFieldUpdater` and its
  kin instead. `BufferedStream`'s wait statistics call
  `java.lang.management` [R], which Android lacks [E]. Data Objects'
  field names need keep rules against R8's shrinking [E]. 4 to 10 hours
  and an emulator [E]. A low risk: Java's code itself, nothing new to
  keep in step.
* **Kotlin/Native and Multiplatform** (iOS): cinterop to C [E]. A
  Multiplatform library would put Java's Core behind its JVM and Android
  side and C behind its native side: two implementations behind one API,
  10 to 20 hours [E].
* **The Pub**: kotlinx.serialization, a compiler plugin, no reflection
  [E].

### 4.9. Swift

* **A binding**: SwiftPM builds C targets from source, so the package is
  C's sources and a Swift wrapper; C's `plat.c` uses Darwin's
  `F_FULLFSYNC`, as on iOS [E]. 4 to 8 hours. Tests on iOS need Xcode's
  simulator, which F53 lacks: it has the Command Line Tools only (012-16,
  8.1) [R].
* **A native port**: ARC writes reference counts on the read path,
  unsafe pointers avoid them, and Swift 6 checks data races strictly; no
  gain over the binding. Not recommended.
* **The Pub**: `Codable`. Swift's `String` compares by canonical
  equivalence, so field names must be handled as bytes (binson-swift's
  SW1, 020-05, 8.1) [R].

### 4.10. Zig

* **A binding**: `@cImport` of `bergdb.h`, and Zig's build compiles C:
  1 to 3 hours [E].
* **A native port**: as C in effort. Zig is before 1.0, and 0.16 (April
  2026) changed every file function to take an `Io` parameter (W18): a
  moving target for a port that must stay stable. Not recommended.

### 4.11. Dart and Flutter

* **A binding**: `dart:ffi`, with build hooks and code assets (Dart 3.10,
  W14) that compile C for each target at build time. Isolates share no
  heap, so one isolate owns a database, as C's one caller [E]. 8 to 16
  hours, and builds with Android's NDK and for iOS for Flutter's mobile
  targets [E]. Flutter on the web would take WebAssembly's way (3.3).
* **A native port**: Dart's `int` has 53 bits on the web, and isolates
  cannot run Java's readers in parallel. Not recommended.
* **The Pub**: Flutter has no reflection at run time (`dart:mirrors` is
  not available there), so code generation, as `json_serializable` [E].


## 5. Effort

### 5.1. Measured

| Work                                        | Wall clock             | Lines |
|---|---|---|
| 012: C Core, Levels 0 to 4, from the go     | 13.5 h                 |  |
| 012: and API, measurements, robustness      | 21 h                   | 53,661 in `c/` |
| 015-02: C follows release 2026.2            | about 2 h coding       | 1,691 |
| 022-01, steps 0 to 4: C to 2026.3           | 1.6 h, no long runs    | +3,683, −523; tests 2,504 |
| 022-02's estimate for 2026.4 (not measured) | 3 to 4.5 h, 1.5 h runs | 650 to 1,100 |

Sources: 012-16, sections 3 and 8.2; 012-18, section 1; 022-01's log and
the commits `86dade8` (10:21) to `3b0d54b` (11:57) of 2026-11-09
(`git diff --numstat`, paths under `test/` counted as tests); 022-02,
section 1.

012's lines (012-16, 3) [M]: the library 21,226 (16,146 code lines, for
the 14,677 code lines of Java's Core, 006-08, 5: 1.10 times); `bergdb.h`
927; tests 25,085; tools (scanner, dumper, runner, checkers) 4,463;
benchmarks 1,322; examples 424; and beside the code 26,835 lines of
expected outputs, vectors and workloads, and 10,654 lines of Markdown.
Today's `c/` in 022: 50,047 lines of `.c` and `.h`, 22,203 of them in
`src/` [R].

The way of working [M, 012-16, 8]: one planning session, then a
conductor and 20 subagents in clones, two to four at a time, at max and
xhigh effort; about 42 points of a week's usage for the account, other
sessions included. Frans's part: decisions D1 to D7, two comments on the
plan, about ten prompts and answers to nine questions; his time was not
measured. What made it fast (012-16, 8.7): byte equality as the single
test, the format document and Java's scanner first, Java's vectors, and a
harness that compared the two implementations from the start. A second
native port reuses all of these.

### 5.2. Estimated

The rule [E]: the lines of the work divided by 012's rate, plus what is
new to it.

* **The rate** [M]: 012, 53,661 lines in 21 hours, about 2,500 lines an
  hour with two to four agents; 015-02, about 850 an hour with one; 022's
  steps 0 to 4, about 2,300 an hour with three.
* **A native port's lines** [E]: Java's Core is 14,677 code lines; C
  took 1.10 times that; Go and Rust about 1.0 to 1.3 times, C# about 1.0,
  Python 0.6 to 0.8. Tests and tools about 1.4 times the library, as in
  012.
* **What is new**: for a port with Java's threads, the concurrency's
  design, tests (Java's seven jcstress tests are the start) and review,
  30 to 60 percent more; for a binding, packaging and CI; for the
  browser, a platform module and browser tests.
* **The hours** are wall-clock hours of unattended work in 012's way,
  without the long runs on a quiet machine and without Frans's decisions.

| Work                                 | Hours | Lines         | Basis |
|---|---|---|---|
| C on Linux                           | 8–16  | 500–1,500     | 012-16, 7: "a day or two" |
| C on Windows                         | 16–32 | 1,000–2,000   | `plat.c`; no Windows machine |
| C++ wrapper                          | 2–4   | 500–1,000     | `bergdb.h`'s 33 functions |
| Zig wrapper                          | 1–3   | 200–500       |  |
| Swift binding, macOS and iOS         | 4–8   | 1,000–2,000   |  |
| Rust binding                         | 6–12  | 2,000–3,000   |  |
| Python binding and wheels            | 10–20 | 2,000–3,000   | the binding 6–12, wheels 4–8 |
| Node-API binding and binaries        | 10–20 | 2,000–3,000   |  |
| WebAssembly, browser and Node        | 15–30 | 3,000–5,000   | OPFS module, worker, TS API |
| Go: binding with cgo                 | 6–10  | 1,500–2,500   |  |
| C#: binding by P/Invoke              | 6–10  | 1,500–2,500   |  |
| Dart: binding with FFI               | 8–16  | 2,000–3,000   | Android and iOS builds |
| Java's Core on Android               | 4–10  | 100–500       | `VarHandle`, management API |
| Kotlin Multiplatform over Java and C | 10–20 | 2,000–4,000   | after Android and Linux |
| Go, native, with Java's threads      | 25–40 | 40,000–55,000 | 012's size and concurrency |
| C#, native from Java, with threads   | 15–30 | 35,000–50,000 | a translation |
| Rust, native, one caller             | 20–30 | 40,000–55,000 | 012's design |
| Rust, readers in threads, more       | 15–30 | 5,000–10,000  | epochs, loom, Miri |
| C: readers in other threads          | 25–50 | 5,000–10,000  | no design yet; 009's barriers |
| C Pub layer: format 2, indexes       | 15–30 | 15,000–25,000 | Java's Pub, about 6,200 lines |
| Index vectors, language-neutral      | 4–8   | 1,000–2,000   | as 020-07's object vectors |
| Python scanner and dumper, a tool    | 4–8   | 1,000–2,000   | as 020-07's `check.py` |
| Each native port, per Java release   | 2–6   | 1,000–4,000   | C's 2 h and 1.6 h; 022-02 |

A binding pays nothing per Java release but when `bergdb.h` changes; a
native port pays every time, so N native ports cost N times C's
following.


## 6. Conformance: how a port shows that it is BergDB

* **Byte equality with Java**, 012's method. The stream is a function of
  the transactions, their times and the settings (010-01, P2); nothing in
  it is Java's own (012-01, 3.2) [R]. The cross harness (`cross.sh quick`,
  `full`, `scale`; 012-05) runs workloads in a text format with Java's
  `Run` and `Dump` and with side B's tools, `bergdb-run`, `bergdb-dump`
  and `bergdb-scan`, and compares the files (from reclaim's decided cut),
  the dumps, the scans, crash cuts, corrupt variants (with Java's
  exception names and texts), runs in turns between the two, and runs at
  small budgets: 1,357 crash cuts and 498 corrupt variants in `full`, 0
  differences [M, 012-16, 2]. Any language whose three tools take C's
  command lines and print C's texts plugs in [R].
* **Java's vectors**: `c/test/unit/vectors/`, 12 text files, 337 KB,
  written by Java's own classes (bytes, checksums, the Dag, keys, klongs,
  key nodes, records, reclaim, `StringMap`, top nodes, the STM's key set,
  Java's arithmetic) [R]. Unit tests per module, without a JVM.
* **StreamDigest**: 12 configurations in 3 modes, a digest each; since
  022's D3, Java's `Run` gives StreamDigest's own digests (022-01, step 0)
  [R]. A port that gives the digests runs Java's own workloads.
* **Power loss**: C's I/O seam and `power.sh` (images of C's and Java's
  runs, started by both; 022-01, step 3) [R]; a native port needs a seam
  of its own.
* **Robustness**: C's allocation failures in turn (628 runs in its gate)
  and the sanitizers [M]; a language with a collector meets an
  out-of-memory error in its own way [E].
* **The Lean model**: Java's runs are checked against it by traces
  (`java/stress/TraceExport.java`, 1,513 lines; `docs/trace-format.md`);
  C has no exporter (012-16, 7, step 6) [R]. Equal bytes and equal reads
  check a port against Java, which is checked against the model; an
  exporter of its own is optional [E].
* **A binding**: C's conformance carries over. The binding needs API
  tests: C's functional tests, and `CoreDemo`'s output, which C's
  `examples/compare.sh` already compares with Java's [R]. The cross
  runner's workload format could be every binding's shared API test:
  workload in, dump out [E].
* **The Pub**: format 2's vectors (020-07, 13; 38 KB: 32 valid records, 84
  invalid, 343 lookups, 8 Binson inputs), which "every binding runs"
  [R]. The indexes have no language-neutral vectors; `IndexReference`
  (Java) is harness H2's model (020-10, 9.1) [R]. A port of the indexes
  needs such vectors first (section 5.2). The Pub's writes are the
  Core's key-value pairs, so Pub workloads could be compared byte for
  byte too, once the cross harness learns Pub operations [E].


## 7. The Pub layer

The size [R, counted here, comment and blank lines left out]:
`bergdb.pub`, about 1,850 code lines; `pubimp`'s production code, about
6,200 code lines without its testers, harnesses and `IndexReference` (the
tests' model, 851): `ObjectFormat` 678, `DataObjects` 677, the indexes
(`IndexKeys`, `IndexDefinition`, `IndexManager`, `IndexBuilderImp`,
`UseIndexBuilderImp`, `UsePrimaryBuilderImp`, `Entries`) about 2,580,
transactions and connections about 1,080, `TimeResolver` 417,
`DatabaseBuilderImp` 322, `PubKeys` 248. 2026.4 is not released; format
2 is frozen at the release (020-07) [R]. Port it after the release.

**Language-neutral**, ported from the specs [R]:

* format 2: "A reader and a writer can be written in any language from
  this document and BINSON-SPEC-1.1 alone" (020-07, header); about 300
  lines in any language (020-05, 12b.8), checked by the vectors;
* the reserved keys under `/#i/` (part of the stream's format, 018-01,
  2); the index keys, the level encodings (`long`, `double`, `string` in
  code-point order, `bytes`) and the definitions as format-2 objects
  (020-10, 4); no ICU since 2026.4;
* maintenance: every put and delete at an object key deletes f(old) and
  puts f(new) in the same transaction; a scan checks each entry against
  its object (020-10, 1 and 5).

**Java-shaped**, each language its own:

* Data Objects by reflection (020-09): "These are the rules of Java's
  binding. A binding in another language converts in its own way over
  the same stored objects" (020-09, 2) [R]. By language [E]:

  | Language   | Objects to format 2 |
  |---|---|
  | Rust       | serde; `Option` for absence |
  | Go         | reflection and struct tags, as `encoding/json` |
  | Python     | dicts, dataclasses |
  | JavaScript | plain objects; integer or double is ambiguous; `BigInt` |
  | C#         | reflection or source generators |
  | Kotlin     | kotlinx.serialization; Java's on the JVM |
  | Swift      | `Codable`; names as bytes |
  | Dart       | code generation (no reflection in Flutter) |
  | Zig        | `comptime` reflection |
  | C, C++     | by hand, or a builder |

* Java's conventions: a top-level array in a field `array`, a primitive
  in a field `p` (020-07, 12); a field `key` set from the database key
  (020-02, question 5) [R].
* Index jobs in threads, a thread per build and cleanup: in a binding
  with one caller they become steps run in the calls, as C runs eviction
  [E].
* Time strings: `TimeResolver` follows `bergdb.pub.Time`'s rules with
  Java's `TimeZone`; the API only, not the stored bytes [R].
* The API's shape: `Connection`, `RwEnvironment`, `WBuilder`, the
  exceptions.

**Where the Pub goes for bindings** [E]:

* (a) in each language: 6,000 to 9,000 lines and their tests per
  language, each kept in step with Java's;
* (b) once, in C, under every binding: format 2, the index keys,
  maintenance and scans in C, and each binding converting its objects to
  format 2's bytes (about 300 lines and its conversion). Maintenance must
  happen inside the transaction, which (b) gives in one place. 15 to 30
  hours (section 5.2). Better than (a) from two bindings on.


## 8. The table

Effort in wall-clock hours of unattended agent work (section 5.2), all
estimates but C's. Risk: of missing Java's promises or of the work
taking much longer.

| Language | Approach                  | Hours       | Risk     | What is hard |
|---|---|---|---|---|
| C        | the port (012, 022)       | done [M]    | low      | Linux, Windows; readers in threads |
| C++      | wrapper over C            | 2–4         | low      | nothing |
| Rust     | binding; native on demand | 6–12; 20–30 | low; mid | native with threads: epochs, +15–30 |
| Go       | native, Java's threads    | 25–40       | medium   | a missed volatile; collector assists |
| Python   | binding, wheels           | 10–20       | low      | wheels per OS and CPU |
| JS, TS   | C as WebAssembly          | 15–30       | medium   | OPFS: async names, forces, eviction |
| C#, .NET | native from Java          | 15–30       | medium   | pauses under eviction; Windows |
| Kotlin   | Java (JVM, Android)       | 0; 4–10     | low      | Android: `VarHandle`, management, R8 |
| Swift    | binding, SwiftPM          | 4–8         | low      | iOS tests need Xcode |
| Zig      | binding, `@cImport`       | 1–3         | low      | Zig before 1.0 |
| Dart     | binding, FFI, build hooks | 8–16        | medium   | mobile builds; no reflection |

Every binding also needs C on Linux (8 to 16 hours) for any platform but
Apple's, and gives the Core only until a C Pub layer (15 to 30 hours)
exists.


## 9. The recommended order

By cost, risk and reach; the study's demand part may move steps 2 to 7,
not step 1.

1. **C on Linux** (8 to 16 hours), with the **C++ and Zig wrappers** (3
   to 7). Every binding but Apple's needs Linux; servers and Android run
   it; s1 can then run C's cross sets. The wrappers need nothing else.
2. **Python, a binding** (10 to 20). The cheapest way to the widest use:
   C's one caller per database matches Python's model, so the binding
   loses nothing that Python could use. Its wheels need a CI.
3. **Rust, a binding** (6 to 12). Rust's types state C's rules
   (lifetimes, `Send` but not `Sync`), and Cargo builds C's sources. A
   native Rust port waits for demand: it is the riskiest native port once
   readers run in threads, and its field is crowded (017-01).
4. **Swift, a binding, and Java on Android** (8 to 18 together). Apple's
   platforms are F53's own, and SwiftPM builds C; Android runs Java's own
   code with small changes. **Dart**'s binding (8 to 16) follows when C
   builds for Android.
5. **JavaScript and TypeScript, through WebAssembly** (15 to 30). The most
   distinctive: a durable store with history and data larger than memory
   in a browser tab, which BergDB's design suits (one writer, no threads
   in C, a memory budget, a stream of files); Node gets the same module.
   Its risks are the browser's (OPFS's durability, storage eviction) and
   can be tested only in part.
6. **Go, a native port** (25 to 40). The first port that carries Java's
   concurrency (goroutines, atomics, a collector that keeps nodes alive
   for readers), and pure Go is what Go's users expect. A cgo binding (6
   to 10) can come first while demand is unclear.
7. **C#, a native port from Java** (15 to 30), after a prototype has
   measured .NET's pauses under eviction; a P/Invoke binding (6 to 10)
   before it if asked.
8. **C: readers in other threads** (25 to 50), when a binding's users
   need parallel reads; and **a C Pub layer** (15 to 30) after 2026.4,
   once two bindings want objects and indexes, with language-neutral
   index vectors first.

Not now: native ports in Python, JavaScript, Swift, Zig, Dart, C++ and
Kotlin/Native; a native Rust port until there is demand; GraalVM's shared
library only as a day's experiment (3.4). A Python scanner and dumper (4
to 8 hours) is worth making at any time, as an independent check of the
format, not as a port.


## 10. What is uncertain

* **Every effort figure outside C** is extrapolated from one port, made
  one way: a plan that existed before the code, and byte equality as the
  oracle. A port without a plan, or in a language where agents write
  worse code, may take longer. 012-18's estimate for 2026.3 was 1,500 to
  2,000 lines in 4 to 6 hours of coding; 3,683 lines landed (tests and
  harness included) in 1.6 hours of wall clock with three workers:
  estimates of lines and hours are loose, in both directions.
* **Durability by language** comes from the libraries' sources and
  documents on the web, not from BergDB's power-loss model; Swift's and
  Dart's forces on macOS and .NET's directory force were not checked.
  Windows is untested for Java and C. OPFS's durability rests on MDN's
  one sentence and one run of a benchmark in a bug report (W6), by which
  Chrome forced nothing for a new file.
* **Pauses under eviction** are measured for Java only. Go's, .NET's,
  V8's and Dart's collectors are not measured with BergDB's workload.
* **Readers in other threads without a collector** have no design, and
  the Lean model does not cover concurrency.
* **Android** was read, not run: whether Java's Core runs there with
  only the changes of 4.8 is not known.
* **The Pub** of 2026.4 is not final; index vectors do not exist.
* **Distribution**: BergDB has F53 (macOS) and s1 (Linux), no Windows
  machine and no CI service; every binding that ships binaries needs one.


## 11. Sources

Read on 2026-11-09.

* W1. Rust pull request 60121 (2019), `sync_all` with `F_FULLFSYNC` on
  macOS and iOS: https://github.com/rust-lang/rust/pull/60121
* W2. Go, `internal/poll/fd_fsync_darwin.go`:
  https://go.dev/src/internal/poll/fd_fsync_darwin.go; issue 26650 (the
  change in 1.12): https://golang.org/issue/26650
* W3. libuv, `src/unix/fs.c` (branch v1.x), `uv__fs_fsync`:
  https://raw.githubusercontent.com/libuv/libuv/v1.x/src/unix/fs.c
* W4. .NET, pull request 124725, `SystemNative_FSync` and `F_FULLFSYNC`:
  https://github.com/dotnet/runtime/pull/124725
* W5. Python, "Call F_FULLFSYNC in os.fsync for macOS", 2025-02-03, no
  decision on the page:
  https://discuss.python.org/t/call-f-fullfsync-in-os-fsync-for-macos/79332
* W6. MDN, `FileSystemSyncAccessHandle.flush()`:
  https://developer.mozilla.org/en-US/docs/Web/API/FileSystemSyncAccessHandle/flush;
  Chrome, synchronous methods since Chromium 108:
  https://developer.chrome.com/blog/sync-methods-for-accesshandles;
  Mozilla's bug 2072928 (a run of 2026-09-15: 1.01 fsyncs per `flush()`
  in Chrome and Firefox; per file created, written, closed and deleted,
  21 in Firefox and 0 in Chrome):
  https://bugzilla.mozilla.org/show_bug.cgi?id=2072928
* W7. SQLite, "Persistent storage options" of its WebAssembly build
  (`opfs`, `opfs-sahpool`):
  https://sqlite.org/wasm/doc/trunk/persistence.md
* W8. Cross-origin isolation for `SharedArrayBuffer`:
  https://web.dev/articles/coop-coep;
  https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/SharedArrayBuffer
* W9. Memory64 in Firefox 134 and Chrome 133:
  https://spidermonkey.dev/blog/2025/01/15/is-memory64-actually-worth-using.html;
  WebKit's bug 300538, "Add support for Memory64":
  https://bugs.webkit.org/show_bug.cgi?id=300538;
  WebAssembly 3.0: https://webassembly.org/news/2025-09-17-wasm-3.0/
* W10. WASI's releases (0.3 stable) and the 0.3 announcement:
  https://wasi.dev/releases; https://bytecodealliance.org/articles/WASI-0.3
* W11. RCU in C++26: P2545R4,
  https://open-std.org/JTC1/sc22/wg21/docs/papers/2023/p2545r4.pdf;
  https://people.kernel.org/paulmck/stupid-rcu-tricks-rcu-api-in-cpp26
* W12. Android, `VarHandle`, added in API level 33:
  https://developer.android.com/reference/java/lang/invoke/VarHandle
* W13. cgo's cost: Shopify, v8go's profiler (54 ns Go to C, 149 ns C to
  Go): https://shopify.engineering/adding-v8-cpu-profiler-v8go;
  https://www.cockroachlabs.com/blog/the-cost-and-complexity-of-cgo/
* W14. Dart's hooks and code assets: https://dart.dev/tools/hooks;
  https://pub.dev/packages/code_assets
* W15. GraalVM Native Image, its C API and its collectors:
  https://docs.oracle.com/en/graalvm/jdk/24/docs/reference-manual/native-image/native-code-interoperability/C-API;
  https://www.graalvm.org/21.3/reference-manual/native-image/MemoryManagement/
* W16. IKVM 8.16.0 on NuGet, Java SE 8: https://www.nuget.org/packages/ikvm/
* W17. PEP 779 and Python 3.14, the free-threaded build supported:
  https://peps.python.org/pep-0779/;
  https://python.org/downloads/release/python-3140
* W18. Zig 0.16.0's release notes:
  https://ziglang.org/download/0.16.0/release-notes.html
* W19. .NET's collector and latency:
  https://learn.microsoft.com/dotnet/standard/garbage-collection/latency;
  Satori, experimental:
  https://blog.applied-algorithms.tech/a-week-with-satori-the-experimental-low-latency-gc-for-net
* W20. Swift 6 and its `Synchronization` module:
  https://swift.org/blog/announcing-swift-6/;
  https://forums.swift.org/t/accepted-with-modifications-se-0410-atomics/69244


## Log

2026-11-09. Written for coord-1109 by pt18, one of 006-18's two agents:
read the items of the brief (012, 012-18, 022-01, 022-02, 006-08,
017-01, 017-07, 020-03, 020-05, 020-07, 020-09, 020-10, 011-08, 009-02),
C's code in 022 and Java's Core and Pub, and Frans's notes of 2012 to
2016 (GCJ, IKVM, "kissdb-for-c"); web research for section 11. Nothing
built or run.
