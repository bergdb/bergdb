012-01. Overview plan: BergDB's Core in C
=========================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Create item 012-bergdb-c. The item is for a project to create
a clone of the Core of BergDB written in C. [...] The API for users should
correspond to the functions of the public methods of Db. The package
bergdb.core defines the Core to be ported to C. The stream format must be
identical to that used by BergDB Java. Check this. A database created in
Java must open in C. One created in C must open in Java. The target is this
machine, F53, Macbook. [...] You can choose C standard and the compiler.
Choose a simple way to build. Nothing fancy. Chose how to test this. Unit
tests. Functional testing. Testing of the stream format compared to the
Java implementation. Create item 012-01 with an overview plan for this
project. The next step after that is to create a set of tasks for the
project. Each task gets a plan as a Markdown file."

**Status: decided, not started.** Written on the evening of 2026-10-27,
while Frans was away, together with the next step, the task plans 012-02
to 012-16 (section 7). On 2026-10-28 Frans took the decisions of section
11 and commented on two points, which this version answers: the clock
(section 4.4) and memory (section 4.5). The implementation starts when he
says so, in a new Claude Code session that conducts it (D7, section 9.1).
Reviewed on 2026-10-28 at 13:34, with the task plans, against Java's `main`
at `e5dd2fd`: after the paced take (`b8ac8a1`) and 005-53 and 005-52
(`decc677`).

**The conductor's prompt**, which starts the work (section 9.1):

    You are the conductor of bergdb item 012, the C clone of BergDB's
    Core. Read items/012-bergdb-c/01-overview-plan.md in full, and 013-01
    for the way of working. Then work through 012's tasks unattended, as
    its section 9 says, with the decisions of its section 11. Start with
    phase A.


# 1. The goal

A clone of BergDB's Core in C, on F53: the same database, a multiversion
ordered map from (key, time) to value in one append-only stream, with index
nodes written lazily into it and a startup that reads only the stream's
tail. Its API is the C counterpart of `Db`'s public methods (section 5).
Its stream is Java's, byte for byte (section 3), so the two are one
database format:

    A database made by BergDB Java opens in BergDB C, and one made by C
    opens in Java. For the same transactions, at the same times and with
    the same settings, C writes the same files with the same bytes as Java.

Done when:

1. **Java to C.** Every database of the cross sets (section 6.4), made by
   Java with restarts, crashes and reclaim's cuts, opens in C, and every
   read gives what Java gives: `getOne` at sampled times, `getMany`
   forward and backward, `getTrans` of every transaction.
2. **C to Java.** The same with the roles swapped. Java opens C's
   databases with assertions on and its audit on (`DbBuilder.audit`).
3. **The same bytes.** For every workload of the cross sets, C writes the
   same files, with the same names and bytes, as Java: also with restarts
   in C, in Java, and in turns between them, and after a crash at any
   position. With reclaim, from the cut that reclaim decided (section 3.2,
   point 8).
4. **The API.** Each of `Db`'s 45 public methods (since `decc677`) has
   its C function, or is
   left out for a reason written in 012-03. A C version of 006-08's
   `CoreDemo` runs.
5. **The levels.** Levels 0 to 4 of `docs/levels.md`: the multiversion map,
   restart, bounded startup, reclaim, and eviction to a memory budget.
6. **Quality.** The C gate (section 6.5) passes: a build without warnings,
   the unit tests, the functional tests and the quick cross set, under
   AddressSanitizer and UndefinedBehaviorSanitizer, and no leaks. The deep
   cross set passes too.
7. **Scale.** A database of 10M keys, written by C and by Java from one
   workload: the same bytes. C starts Java's and reads it, and Java C's.
8. **Measured.** Speed, memory and code size against Java on F53,
   recorded. No target; correctness and the bytes come first (P11).
9. **Reported.** 012's outcome, with the evidence and the next steps.

Not in 012:

* **Replicas** (`addReplica`, `removeReplica`): one stream only.
* **Encryption** (`SalsaStream`): an encrypted database is refused.
* **Threads.** The C clone has none of its own, and one caller at a time
  uses a database (section 4.2). Java's readers beside a writer are not
  cloned.
* **The upper layers**: `pub`, `pubimp`, ukeys, `created.txt`. A database
  made through the Pub API opens in C at the Core's level.
* **Other platforms.** F53 only (macOS on Apple silicon). The code is kept
  portable where it costs nothing (section 4.2), and a later item decides
  more.
* **The Lean conformance of C's runs.** A C trace exporter for the trace
  checker (`docs/trace-format.md`) is possible later. Until then the same
  bytes as Java's records carry Java's conformance over.
* **Anything that Java does not have** (P12). The clone adds no feature.
* **Changes to Java.** 012 changes nothing in `java/` or `lean/`, but for
  decision D6b's move of the format document to `docs/`, which leaves a
  pointer in place of the 2015 text in `java/src/bergdb/core/doc-files/`.
  A Java bug that the port finds is registered in 005 (section 9).


# 2. Where 012 starts

* **006-08** found the Core independent and a C clone feasible: the Core
  is 121 files and 14,677 code lines without tests, two thirds of BergDB's
  production code; a clone would be about 10,000 to 17,000 lines of C
  (006-08, sections 5 and 6). Its section 6.2 says what a clone ports,
  rewrites and leaves out; section 4.2 here follows it. Its first steps
  (6.8): the stream format written down, a reader in C first, then the
  writer checked byte for byte against Java.
* **The largest classes** (code lines without tests, 006-08's
  `runs/closure-lines.txt`): `Db` 1,320, `KeyNode` 1,219, `Dag` 802,
  `StorageManager` 802, `Reclaim` 714, `FileStream` 661, `StoredTrans`
  521, `DbStarter` 501, `NodeCollection` 456, `RecoverableStream` 421,
  `Eviction` 401, `GetMany` 336.
* **The model.** `docs/sis-model.md` and the Lean proofs are about the
  algorithm, not about Java, so they hold for a faithful clone too. The
  alignments say how Java maps onto the model: 011-11 for Level 2, 001-07
  for reclaim, 001-08 and 009-05 for eviction.
* **Java's own checks of its bytes**, which the cross tests reuse:
  `StreamDigest` (twelve configurations of `RestartInvariance`'s
  workloads, each in three modes: plain, with reads, with restarts),
  `RestartInvariance` (the same stream with and without restarts),
  `EvictionInvariance` (the same stream with every eviction schedule) and
  006-08's `CoreSame` (6,000 transactions with index writes, eviction,
  reclaim and restarts, in a directory).
* **The principles** (010-01) that matter most here: P2, a deterministic
  stream, which makes byte equality possible at all; P7, a failed database
  stops, which makes errors simple in C (no undo); P9, no global state;
  P10, few settings; P11, simple before optimal; P12, a small Core Layer.
* **F53**: an Apple M1 Pro, 10 cores, 32 GB, macOS 27.0.1; Apple clang
  21.0.0 from the Command Line Tools; GNU Make 3.81; OpenJDK 27
  (Homebrew). Homebrew's gcc 16 and cmake are there too; the plan does not
  need them.


# 3. The stream format, and what "identical" takes

## 3.1 The format

The code is the definition: `MetaBlock`, `RecoverableStream`,
`StoredTrans`, `StoredTopNode`, `StoredKeyNode`, `StoredValueNode`,
`NodeChecksum` and `FileStream`. The text of 2015,
`core/doc-files/stream-format.txt`, is partial and says so. In short, all
numbers little-endian:

| Part | Layout |
|---|---|
| Meta block | 128 bytes at every multiple of 200,000: "berg", version 154, time, the position of the last whole record, the database id (16 bytes), the startup distance, the maximum node size (since 2026-10-27, 005-50), zeros, and the last byte 10 |
| Framing | Records between the meta blocks; a record that reaches a meta block continues after it. A position counts every byte of the stream, meta blocks included; a record's size counts its own bytes only. Records start at multiples of 8 |
| Record | Size (4), format 5 (1), three zero bytes, time (8), startup position (8), the newest top node's position (8); the top nodes, the key nodes, the value nodes; 0 (4); the got-dirty count (4) and its (id, position) pairs; zeros to a multiple of 8; the last byte 10 |
| Node | Size (4), type (10 top, 20 key, 30 value, 40 delete), format (2, 2, 4), a Fletcher-16 checksum (2); then the node: a key node's previous position, leaf flag and size, id, klongs and pointers; a top node's number of pointers and ordinal, id, root time, root pointer, and its other pointers with their times; a value node's id, offset in its record, value (none for a delete) and key |
| Keys | Segments of up to 7 bytes packed into 64-bit compare values (`Klong`); an ikey's bytes are UTF-8 with `/` as 1 and every other byte plus 2 (`core/doc-files/key-encoding.md`) |
| Directory | `FileStream`: files `NNNNNNNNNNNNNN.bergdb`, the 14-digit number being the file's first position divided by 100,000, of sizes 200 kB, 1 MB, 5 MB, 20 MB, 100 MB, 500 MB, 2 GB and on; reclaim's cut deletes whole files from the front |

012-02 writes all of it down, field by field, with the places in the code
that decide each field.

## 3.2 What I checked

Frans asked to check that the stream can be identical. I read the format
classes, the write path's ordering (`TransNodes`, `TransSeq`), the clock,
the builder's settings, reclaim's stored table, `FileStream`'s naming, and
how `StreamDigest` and `CoreSame` compare streams, and searched the Core
for hash-ordered collections, randomness, clocks and floating point. The
findings:

1. **Identical bytes are possible.** By P2 the bytes are a function of the
   transactions, their contents, times and order, and of the settings
   stored in the stream. Java checks this for its own runs:
   `RestartInvariance` byte for byte across restarts, `StreamDigest` across
   builds and JVM runs (its 36 digests identical in today's commits, such
   as `4085e2e`), `EvictionInvariance` across eviction schedules,
   `CoreSame` across two builds. Nothing in the format is Java's own: no
   Java serialization, no object hashes, no class names. A faithful port of
   the writer can write the same bytes.
2. **What must be fixed for a comparison.** The database id (random by
   default, from `SecureRandom`; `DbBuilder.id` or `testId()`), the times
   (every time in the stream is a transaction's, read from the clock
   through `DbClock`; the test clock gives them, section 4.4), the
   maximum node size and the startup distance (both in every meta block,
   and both decide the index writes), and reclaim's retain duration,
   internal fraction and step reserve (they decide reclaim's records; the
   reserve is a test setting, counted in index nodes at a fixed size each,
   and its default splits no step in practice). The cache size and
   eviction do not change the bytes (`EvictionInvariance`), nor do the
   buffer's size and time, which decide only when bytes are written.
3. **Order.** A record's nodes come in the order of `TransNodes`' arrays,
   and the got-dirty list is an `ArrayList`: insertion order, decided by
   the algorithm, which C can follow. The iterations over hash maps found
   in the Core do not decide what is written: `DbStarter` updates pointers
   entry by entry, and `Dag.dirtyNodeBound` adds up a bound. 012-02 audits
   the rest of the writer, startup and reclaim the same way.
4. **Floating point.** Reclaim computes `(long) (0.25 * retainDuration)`
   and `(long) (internalFraction * growth)`. Since `b8ac8a1` (below,
   point 9) the take decides with doubles too: a record's share of D, a
   chain of products and quotients of longs, and a dither in [0, 1) from
   the stream length, SplitMix64's finalizer (`TransSeq.take`,
   `TransSeq.dither`). C gives the same with IEEE doubles, the operations
   in Java's order, no fused multiply-add (`-ffp-contract=off`), and
   Java's saturating conversion from double to long (section 6.2).
5. **Java's integer arithmetic.** Some results rely on wrapping, such as
   `Keys.hash` (`value * 37 + l`), and the code uses `>>>` and signed
   bytes. C needs wrapping arithmetic (`-fwrapv`, or unsigned types),
   explicit unsigned shifts and masked shift counts (section 6.2).
6. **Text in the stream.** Reclaim stores its table as a key-value pair
   (`/#i/dreclaim/-table.txt`), a `StringMap` text of decimal numbers,
   `true`, `false` and `null`. `setStartupDistance` writes a dummy
   transaction of 200,000 zero bytes under `/#i/-dummy`, or nothing when
   the clamped value is the one in force (005-53, `decc677`). C must write
   the same text and the same dummy, in the same cases.
7. **The 2015 text is out of date in places.** `MetaBlock`'s own comment
   says the valid block's last byte is 1; the code writes 10. The code
   wins; 012-02 lists every such difference.
8. **Reclaim's physical cut depends on timing.** It waits for the bytes to
   be durable, and a restart syncs, so which front files exist at a given
   moment may differ between two runs of one workload. The bytes from the
   cut that reclaim decided (`getFirstAvailablePos`) do not. So, as
   `StreamDigest` does, the comparison with reclaim is of the files and
   bytes from the decided cut; without reclaim, of all files and bytes.
9. **Java moves.** 005-50 put the node size in the meta block on
   2026-10-27 (`c1f1f15`); both Java and C refuse databases from before
   it. On 2026-10-28 007-03's step 3, the paced take with its deadline,
   came into `main` (`b8ac8a1`, 007-07): the same format, but every
   stream changed (`StreamDigest`, 36 of 36). The C clone ports the take
   as it is now. The same day 005-53 and 005-52 came in (`decc677`):
   `setStartupDistance` writes nothing for the value in force, and `Db`
   has a setter and a getter of the cache size, 45 public methods in all;
   `StreamDigest`'s digests did not change. So the C clone follows Java's
   `main`, and its cross tests show at once when Java's bytes change
   (section 9).

The conclusion: the stream can be identical, given a faithful port of the
writer, startup and reclaim, the settings and times fixed as in point 2,
Java's arithmetic in C (points 4 and 5), and a comparison from reclaim's
decided cut (point 8). Section 6.4 says how it is checked.


# 4. What the clone is

## 4.1 Ported, rewritten, left out

After 006-08, section 6.2:

| Part | Java | In C |
|---|---|---|
| Keys and klongs: `Klong`, `Keys`, `Spos`, `Bytes`, `NodeChecksum` | about 600 code lines | ported |
| The index: `KeyNode`, `TopNode`, `ValueNode`, `TopDs`, `Dag`, `GetMany` | 2,900 | ported |
| The record format and the framing: `StoredTrans`, the three `Stored*Node`, `MetaBlock`, `RecoverableStream`, `NodeStream` | 1,700 | ported |
| The database: `Db`, `Trans`, `TransNodes`, `TransSeq`, `KeyModSet`, `DbStarter`, `NodeCollection` | 3,000 | ported; `Db` without its threads and locks |
| The clock: `DbClock`, `SystemClock`, `CoreTestClock` | 100 | ported, the test clock with them: equal streams need deterministic times (4.4) |
| Reclaim: `Reclaim`, `CutStream`, `StringMap` | 850 | ported |
| Memory: `Cache3`, `Eviction`, `Residents`, `Handle` | 900 | rewritten: a node table, eviction to a budget in the calls, and C's rules for freeing (4.5) |
| The write path: `StorageManager`, `BufferedStream` | 1,200 | rewritten: one buffer, written in the calls |
| Storage: `FileStream`, `FileStreamIo`, `MemoryStream` | 900 | rewritten for POSIX files, the same directory; a memory stream for tests |
| Encryption, replicas, JMX, `DbUtil`, `Audit` | | left out, or test-only in C |

## 4.2 Rules of the design

* **One caller at a time.** No threads, no locks, no atomics: a database
  handle is used by one thread at a time, as a `FILE` is. Work that Java
  does in its own threads happens in the calls: writes when the buffer is
  full, at `sync` and at close; eviction at transaction ends and after
  loads, where Java already evicts (levels.md, section 7). Calm when not
  used (P3) follows.
* **No global state** (P9). Everything hangs off the database handle.
* **Errors are return codes.** Before a transaction's go point, a refused
  transaction leaves everything as it was; after it, a failure fails the
  database, and every later call but close gets that failure (P7, levels.md
  section 3). So no undo, as in Java.
* **Memory without a garbage collector.** One allocator module that counts
  every byte; one owner for most memory; counted references for the
  objects that Java shares; frees at safe points, so that the ported code
  can keep Java's order (4.5).
* **The platform in one place.** Files, forces and the clock go through
  one small module; the rest is ISO C. Thus a later port to Linux or to an
  embedded target replaces one file.
* **Faithful before clever.** Java's algorithm, decisions and order are
  ported as they are, also where C would allow something else, since the
  bytes must match (P2, P11). Optimizations come only after 012, and only
  where they keep the bytes.

## 4.3 Durability without a thread

Java's `BufferedStream` writes the buffer within the buffer time (20 ms)
from a thread of its own, and `FileStream` forces each write. The C clone
has no thread: a transaction's record goes to the buffer, the buffer is
written with `write` when it is full, at `sync` and at close, and `sync`
and close force with `F_FULLFSYNC`, as Java's `force(true)` does on macOS.
The bytes are the same (P2); what differs is when a transaction that
nobody syncs becomes durable. 012-13 writes the rule down. A simple
improvement, should it be wanted: write the buffer at the start of any
call when the buffer time has passed.

## 4.4 Time and the clock

Frans, 2026-10-28, on the first version of this plan, which counted
Java's test clocks among the parts left out: "Not sure this is a good
idea. To create equal streams, we need deterministic time." Right: the
clock is ported whole, the test clock with it.

* **Where the stream's times come from** (checked in the code on
  2026-10-28). Every time in the stream is a transaction's time, and
  `DbClock.transactionBegin` reads it from the database's clock: at the
  creation, for the primordial transaction (whose time every meta block
  carries), and at each `execute`, which also runs the dummy transaction
  of `setStartupDistance` and reclaim's steps and table. The only other
  read of the clock is `DbClock.currentTime`, behind `Db.currentTime()`.
  Lookup times never read it, and reclaim spaces its iterations and finds
  its cut by transaction times (`t.tt - lastTStart()`). So the bytes are
  as deterministic as the clock.
* **`DbClock` is ported exactly.** A transaction's time is the clock's,
  but later than the last transaction's and than the last
  `currentTime()`'s. So a call of `bergdb_current_time` can move the next
  transaction's time, when the clock has not moved since, and C must make
  that call where Java's caller makes it. A clock time outside 0 to
  2^56 − 1 refuses the transaction (005-18). A lookup time is clamped to
  the last transaction's time.
* **The clock is an option of `bergdb_open`**, a function and its
  context, as `DbBuilder.clock(Clock)` is in Java:
  * by default the system clock, ported from `SystemClock`'s code:
    milliseconds since 1970 times 10,000. Its comment promises strictly
    increasing times, but the code sets its last time only when the clock
    is at or below it, which from 0 never happens, so it returns equal
    times within a millisecond, and earlier ones when the system clock is
    set back. `DbClock` makes transaction times increase in any case, so
    nothing in a database depends on it; the conductor registers it in
    005 (D5);
  * the **test clock**, ported from `CoreTestClock` into the library, as
    Java has it in `bergdb.core`: a time that the caller sets, forward
    only, and that does not move by itself. Java's `TestClock`, which
    006-08's `CoreSame` uses, differs only in refusing a time out of range
    when it is set; `DbClock` refuses such a time anyway, at the next
    transaction, so C needs one test clock;
  * or a function of the caller's.
* **The cross tests run on the test clock**, in both languages. The
  runners set it before each transaction and before the creation, which
  reads it; keep it across restarts, as `StreamDigest` keeps its clock;
  and call `currentTime` where the workload says (012-05). The same
  workload then gives the same times, and the same times the same bytes
  (3.2, point 2). The system clock is never part of a comparison.

## 4.5 Memory: allocating and freeing

Frans, 2026-10-28, on "freed by hand" in the first version of 4.2: "Not
sure what this means exactly. Tell me more about the plan for allocating
and freeing memory." The plan follows.

**What Java leaves to its garbage collector**, and C must do itself:

1. *Shared objects.* A pointer of an index node holds the child's handle
   (009) or a value object, and several resident objects may hold the same
   one. When a full node is replaced (`KeyNode.lastVersionGivenDel`), the
   replacement copies its live pointers, so the old and the new object
   share values and child handles; `Eviction`'s own tests count objects
   that two pointers name. An evicted node's handle dies and leaves the
   node table, but stays in the pointers that held it until each is
   followed again or its holder goes (`Handle`, 009-02).
2. *Temporaries.* Objects that live for part of a call: the halves of a
   split (`first`, `last`), a version read for one operation only (not
   cached). And the code holds objects in local variables while it changes
   pointers, in any order.
3. *Failures.* An exception unwinds, and whatever was half built is
   collected.

**In C**, with `malloc` and `free`, and no garbage collector library and
no general arenas:

1. **One allocator module.** Every allocation and free of the library goes
   through it, per database (P9). It counts the live bytes by kind (index
   objects, values, handles, the node table, buffers, the caller's
   objects), which gives the memory budget its exact figure (P8) and the
   tests an exact leak check; it turns a failed allocation into NOMEM; and
   in the test build it can make the Nth allocation fail.
2. **One owner for most memory.** The database owns its state: the stream
   and its write buffer, the node table, D, reclaim's state, the settings,
   and a few buffers allocated once and grown when needed. The caller owns
   what it is given: a transaction, which owns copies of its keys and
   values; a read context, which owns the buffer a returned value is
   copied into, valid until the context's next call; a `getTrans` result.
   Each has its free function and is freed before the database is closed.
   A callback (`getMany`'s, the key and value transformations) gets data
   valid during the callback only, and may not call the database (STATE).
3. **Counted references for what Java shares.** Index objects, values and
   handles count their long-lived holders: the handle that holds an
   object, the pointers that hold a handle or a value, the node table, D,
   the record being written, and the database's own fields (the super
   root, the newest written top node). Local variables do not count.
4. **Frees at safe points.** An object whose count falls to 0, or that is
   made without a holder, goes on the database's pending list, not to
   `free`. At a safe point, where the code holds nothing uncounted, the
   pending objects that still have no holder are freed: at the end of
   every call, and inside long calls at points their tasks name (between
   the puts of a large transaction, between the leaves of a `getMany`,
   whose cursor counts what it holds, between the records a startup
   reads). So the ported code follows Java's line by line, with locals and
   pointer changes in Java's order, and nothing is freed while the call
   still uses it. A free is small work: an object releases what its own
   pointers hold, values and dead handles, never a subtree, so there is no
   pause (P1).
5. **Eviction** (Level 4, 012-12) frees memory where Java evicts, at
   transaction ends and after loads; in C, at the end of the call, a safe
   point. Java's rules decide what may go (not pinned, and written), a
   CLOCK batch takes objects down to the low watermark, their handles die
   as in Java, and the memory is freed at once. The budget is compared
   with the allocator's count, not with Java's estimates. Eviction may
   take other objects than Java's would; no byte changes
   (`EvictionInvariance`, and C's own invariance test).
6. **Close frees everything.** It collects each object reachable from the
   node table, D, the database's fields and the pending list, frees it
   once, and then the database's state. It does not trust the counts, so
   it works after a failure (P7) too. Afterwards the allocator's count is
   0.
7. **Failures.** NOMEM before a transaction's go point refuses the
   transaction and leaves the database as it was; after the go point it
   fails the database (P7). An open that fails leaves nothing open.
8. **The stack.** No large buffers on the stack and no recursion deeper
   than the tree, as a caller's thread may have a small stack (512 KB for
   a secondary thread on macOS).

**The checks** (6.4, 6.5): after every test's close, the allocator's count
is 0; AddressSanitizer in the test build (a use after free, a double free,
an overflow); macOS's `leaks` on the release build; a debug check that
recounts every count by a walk and compares, as Java's audit and
`Residents`' resync do; and allocation failures in turn, as SQLite tests
its out-of-memory paths: each allocation of a small workload made to fail,
one run each, and every run gives NOMEM, then the database as before or
failed, and close frees everything.

**Where it is done**: the allocator in 012-04; the counts and the pending
list with the nodes in 012-07, whose design step lists every holder that
Java has; `getMany`'s cursor in 012-08; eviction in 012-12; the
allocation-failure runs from 012-09 on, each task adding its own paths,
and completed in 012-14; the bytes per key-value pair, against Java's MEM
metric, in 012-15.


# 5. The C API

One header, `bergdb.h`, with the prefix `bergdb_`. Times are 64-bit
numbers in BergDB's units (100 ns since 1970, as in Java), positions are
64-bit stream positions, keys are byte strings (bkeys; the conversion to
segments is BergDB's, `Keys.toSegments`), and every function returns a
status code. The design, with the types and the error codes, is 012-03.
The mapping from `Db`'s 45 public methods (at `e5dd2fd`; 012-03 counts
them again at its start):

| `Db` (Java) | C | Note |
|---|---|---|
| `builder()`, `start()`, `start(StartParams)` | `bergdb_open` | the builder's settings in a struct: node size, startup distance, cache budget, retain duration, the clock (the system clock by default, or the test clock, 4.4), id; `StartParams` is for Java's tests |
| `stop()`, `close()` | `bergdb_close` | writes, forces and frees; with no thread, stop is close |
| `trans()`, `execute(Trans)`, `execute(Trans.Builder)` | `bergdb_trans_*`, `bergdb_execute` | put, delete, the read set and its lookup time (STM, `RerunException`); key and value transformations as callbacks |
| `newGetData()`, `getOne(...)` | `bergdb_get` | a read context in place of `GetData`; the value stays valid until the context's next call |
| `newGetMany()`, `getMany(...)` | `bergdb_get_many` | start key, direction, inclusive; the stop conditions of `GetMany` (end key, count, prefix) and a callback |
| `getTrans(tpos)` | `bergdb_get_trans` | the time, the positions and the transaction's key-value pairs |
| `sync(level)`, `sync(pos, level)` | `bergdb_sync` | NONE, ORDINARY, STRONG; with one stream, STRONG is ORDINARY |
| `currentTime()`, `lookupTime(t)` | `bergdb_current_time`, `bergdb_lookup_time` | |
| `getStartupDistance()`, `setStartupDistance(n)` | `bergdb_startup_distance`, `bergdb_set_startup_distance` | the setter checks the state, clamps, writes nothing for the value in force, else Java's dummy transaction, and puts the setting back if the dummy is refused (005-53) |
| `getCacheSizeIndicator()`, `setCacheSizeIndicator(n)` | `bergdb_cache_budget`, `bergdb_set_cache_budget` | for the run only, not in the stream (005-52); the setter evicts at its own end, where Java wakes its eviction thread |
| `getRetainDuration()`, `setRetainDuration(d)`, `setReclaimInternalFraction(f)`, `getInternalFraction()` | reclaim's settings | |
| `getStreamLength()`, `getDurableLength()`, `getLastTransPosOfLastValidMetaBlock()`, `getFirstAvailableLookupTime()`, `getFirstAvailablePos()`, `getReclaimIterationCount()`, `getTransactionCount()`, `getKvCount()`, `getGetOpCount()`, `getCachePutSize()`, `getDirtyFraction100()`, `getDirtyFraction1000()`, `getAccessData()` | `bergdb_stats`, or one function each | status; 012-03 decides |
| `printDag(out)`, `checkNodes()` | `bergdb_debug_print`, `bergdb_debug_check` | for tests |
| `addReplica`, `removeReplica`, `getStorageInfos()` | left out | one stream; `getStorageInfos` as a line of the status, if wanted |
| `getOneInternal`, `internal()` | left out | Java's internals |

A database is a directory, as Java's `FileStream`, or a memory stream for
tests. `bergdb_open` creates the database when the directory has no
`.bergdb` files, as Java does.


# 6. Language, build and tests

## 6.1 Language and compiler

**C17** (ISO/IEC 9899:2018), with no compiler extensions in the code:
supported by every compiler that a later port may meet, and enough for
this code (fixed-width integers, `static_assert`, no threads needed).
**Apple clang 21** from the Command Line Tools, as `cc`, the compiler F53
has. The flags:

* always: `-std=c17 -Wall -Wextra -Wpedantic -Wshadow -Wconversion
  -Werror -fwrapv -ffp-contract=off`;
* the release build: `-O2`; the library's size measured also at `-Os`;
* the test build: `-O1 -g -fsanitize=address,undefined
  -fno-sanitize-recover=all`, on every unit, functional and cross test.

`-Wconversion` may prove too noisy for code that mirrors Java's casts;
012-04 decides with the first modules and writes down why.

## 6.2 Java's semantics in C

The rules that keep C's arithmetic Java's, written once in 012-04 and
followed by every task:

* `long` is `int64_t`, `int` is `int32_t`, `byte` is `int8_t` where its
  sign matters and `uint8_t` for bytes in buffers. Overflow wraps, as in
  Java (`-fwrapv`; unsigned types where it is intended).
* `>>>` is a shift of the unsigned type. Shift counts are masked as Java
  does (`& 63` for `long`, `& 31` for `int`).
* `/` and `%` truncate in both languages; a division by zero is checked
  where Java would throw.
* A cast from double to long uses a helper with Java's semantics: NaN
  gives 0, and values out of range give the limits. No fused
  multiply-add.
* Comparisons follow the Java code's own: signed where it uses
  `Long.compare` or `<`, unsigned where it uses `Long.compareUnsigned` or
  masks.
* Text written to the stream (reclaim's table) is formatted as Java's
  `"" + long` and `StringMap` format it.

## 6.3 The build

Plain `sh` scripts, as `java/build.sh`; no make, no cmake. In the C
directory, `items/012-bergdb-c/c/` (decision D1):

    readme.md            what it is; how to build and test
    build.sh             builds build/: the library, the tools, the tests
    before-commit.sh     the C gate (section 6.5)
    include/bergdb.h     the API
    src/                 the implementation: one .c and .h per module
    test/unit/           unit tests and test.h, a test framework of one header
    test/func/           functional tests: programs that use bergdb.h only
    test/cross/          the cross tests with Java: cross.sh, the Java harness, workloads
    tools/               bergdb-scan, bergdb-dump, bergdb-run

`build.sh` compiles every module in one `cc` call per build (release and
test), a few seconds for about 15,000 lines; no incremental build is
needed. The Java side of the cross tests is compiled by `javac` from
`java/src`'s Core Layer packages into the C directory's own `build/`, as
006-08's `core-build.sh` does, so the C work never touches `java/build/`.

## 6.4 The tests

**Unit tests**, in C, per module: the byte codecs, Fletcher-16, klongs
and keys, positions and the framing, the meta block, each node's
serialization, the key node's and the top node's operations, the Dag,
`getMany`, the take, the record serializer and parser, `DbClock`,
`StringMap`. Java's own unit tests of the same classes (`KeyNodeTester`,
`DagTester`, `TopTester`, the `@Nano` tests of `Klong`,
`RecoverableStream`, `StoredTrans`, `TransSeq` and others) are ported
where they test behaviour that C has. Test vectors that Java generates
(klongs, keys, checksums, nodes and records as bytes) are kept as small
files, so the unit tests run without Java; the cross tests generate them
again and compare, which catches drift.

**Functional tests**, in C, through `bergdb.h` only: the C `CoreDemo`;
puts, deletes and reads at many times; `getMany` in both directions with
each stop condition; `getTrans`; a restart after every transaction; a
crash cut at every position of a small stream; refused transactions (the
read set, the record limit, a clock out of range) and a failed database
(P7); `DbClock`'s rules (4.4); reclaim and its first available time; a
small memory budget; large values; a million keys.

**Cross tests with Java**, the heart of it. A workload is a text file
(012-05): the settings, then transactions with their times, puts and
deletes, and `sync`, `restart`, `check` and setting changes between them.
A Java runner (on `Db`, `DbBuilder`, a settable clock and the test id) and
a C runner run the same file; crashes are copies of a finished directory,
cut. The checks:

1. *Codecs*: Java's vectors and C's agree (above).
2. *Scan*: a Java scanner and a C scanner print every record and node
   field of a stream; for every stream of the sets, the two texts are
   equal. This checks C's parser on everything Java writes, and it
   explains a byte difference: the first differing position, and the
   record and the field it falls in.
3. *Same bytes*: Java and C run each workload; the directories have the
   same files and bytes (with reclaim, from the decided cut). The
   workloads: `StreamDigest`'s twelve configurations, exported draw for
   draw, in its three modes; `CoreSame`'s; and random ones from seeds,
   with small node sizes and startup distances so that splits and index
   writes come often.
4. *Java to C*: C opens each Java database and dumps it: the latest state,
   reads at sampled times, `getMany` both ways, `getTrans` of each
   transaction. The dump equals Java's of the same database.
5. *C to Java*: the reverse, with Java's assertions and audit on.
6. *In turns*: one workload with the implementation changed at every
   restart (Java, C, Java, ...): the bytes equal both pure runs. This
   checks that each startup rebuilds what the other had in memory (D, the
   take's state, reclaim's state).
7. *Crashes*: a stream cut at chosen and random positions, inside records
   and inside meta blocks; Java and C recover alike: the same zero fill,
   the same bytes after the next transactions, the same reads.

**Sanitizers, leaks and memory.** Every C test runs in the test build
(6.1); the functional tests also under macOS's `leaks`, in the release
build, as `leaks` is not run under AddressSanitizer. Every test checks
that the allocator's count is 0 after close, and the allocation-failure
runs of 4.5 make each allocation of small workloads fail in turn.

## 6.5 The gate and the deeper sets

* `before-commit.sh` must print `C BEFORE COMMIT OK` before C code is
  committed: the build with `-Werror` in both modes, the unit tests, the
  functional tests, and the quick cross set. A target of about 2 minutes,
  as Java's gate.
* `test/cross/cross.sh full`: the deep cross set, at the end of every task
  and before a milestone: all of `StreamDigest`'s configurations at their
  full size, `CoreSame`, a few hundred random seeds, crashes at a thousand
  positions, workloads in turns. About 10 to 20 minutes.
* `test/cross/cross.sh scale`: the 10M-key workload (done item 7), by hand,
  outside other sessions' timed runs.
* Java's gates do not change: 012 does not touch `java/`.


# 7. The tasks

Each task is a subitem with a plan of its own, `nn-short-name.md`: the
goal, what to read in Java and in the docs, the steps, the tests, "Done
when", the effort, the risks; and, as the work goes, its progress and
outcome. The first thirteen are the clone; the last three measure and
report.

| ID | Task | After | Effort |
|---|---|---|---|
| 012-02 | The stream format, written down: every field, where Java decides it, the determinism audit; Java's scanner | | max |
| 012-03 | The C API: `bergdb.h` from `Db`'s 45 methods; types, errors, ownership, one caller | | high |
| 012-04 | The C project: layout, `build.sh`, the test framework, the gate, the rules of 6.2; bytes, Fletcher-16, klongs and keys, with Java's vectors | | high |
| 012-05 | The cross harness, Java's side: the workload format, Java's runner and dumper, the exported workloads, the compare scripts, the reference outputs | 02 (scanner) | high |
| 012-06 | The stream reader: memory and directory streams, meta blocks, the framing, records and nodes parsed; C's scanner equals Java's | 02, 04, 05 | high |
| 012-07 | The index nodes: klongs, key nodes with their versions, searches and splits, value nodes, top nodes and `TopDs`, in memory | 04, 06 | max |
| 012-08 | The Dag and reads: put, delete, `getOne` and `getMany` at a time; C reads Java's databases by replaying the whole stream (Level 1) | 07 | max |
| 012-09 | The write path: creation, `execute` with its checks and the read set, `TransNodes`, the take and the startup position, ids and vpos, the record writer, meta blocks, `DbClock`, appends to files: the same bytes without restarts | 08 | max |
| 012-10 | Startup and recovery: the torn record's fill, `DbStarter`'s rerun, Rule R, rule 4 by position, `NodeCollection`'s loads; restarts, crashes and turns between Java and C (Levels 0 to 2 done) | 09 | max |
| 012-11 | Reclaim: iterations, steps, the table, safe positions, the cut and the front files; the same bytes from the decided cut (Level 3) | 10 | max |
| 012-12 | The memory budget: a node table and eviction to a budget in the calls; the bytes unchanged; a database larger than its budget (Level 4) | 10 | high |
| 012-13 | The rest of the API and durability: settings, status, sync levels, the buffer and forces, close; the C `CoreDemo`; the API's text | 11, 12 | high |
| 012-14 | Robustness and scale: random runs by the thousand, crash and power-loss faults through an I/O seam, corrupt streams refused cleanly, 10M keys | 13 | high |
| 012-15 | Speed, memory and size against Java on F53, in quiet windows | 13 | high |
| 012-16 | The report: what works, the evidence, the departures, the next steps | 14, 15 | high |

Sizes, roughly, in lines of C without tests: 06 about 1,800; 07 2,500; 08
2,000; 09 2,500; 10 2,000; 11 1,100; 12 700; 13 600. About 13,000 in all,
inside 006-08's estimate.


# 8. Order and milestones

* **Phase A, foundations: 012-02 to 012-05, side by side.** 012-05 needs
  012-02's Java scanner, which comes first in 012-02.
  *M1: the format written down, the API designed, C builds and tests run,
  Java's reference outputs exist.*
* **Phase B, reading: 012-06, 012-07, 012-08**, in order.
  *M2: C reads Java's databases: every stream scans alike, and C's reads
  by full replay equal Java's.*
* **Phase C, writing and restarting: 012-09, then 012-10.**
  *M3: Levels 0 to 2. C writes Java's bytes; each opens the other's
  databases; restarts, crashes and turns between the two give the same
  bytes.*
* **Phase D, Levels 3 and 4: 012-11 and 012-12**, side by side, both
  after 012-10.
  *M4: reclaim's cuts and the memory budget, the same bytes.*
* **Phase E: 012-13, then 012-14 and 012-15 side by side, then 012-16.**
  *M5: done (section 1).*

A guess at the pace, not a promise: M1 on the first day; M3 within a week;
M5 in two to three weeks of unattended sessions, depending on the usage
budget and on what the port finds.


# 9. How the work runs unattended

The way of working is 013-01's, the unattended night, stretched over days:
its ground rules, the day's development with subagents, the check-ins that
survive a usage limit, the quiet blocks of timed runs at night, and the
write-up for Frans in the morning. What follows is 012's own.

## 9.1 The start

Frans starts the work (D7) with a new Claude Code session, started as he
starts his BergDB sessions so that it has the same memory notes, and makes
it the conductor (013-01's lead session) with the prompt at the top of
this plan. His go approves the task plans 012-02 to 012-16 with this plan. The
conductor's first steps:

1. Read `AGENTS.md`, `items/readme.md`, `news.md`, `git log` and
   `git status`, this plan, and the task files of phase A.
2. See which other sessions work, on what, and whether a quiet block or
   `night.sh` is due (013-01, sections 3 and 7).
3. Record Java's `main` HEAD as the reference of the first tasks, and write
   the start into 012's log and `news.md`.
4. Set up what keeps unattended work going, as 013-02, sections 7 and 8,
   say for unattended mode: a state file (`/Users/f/fl/bench/012/state.md`),
   a check-in every 20 minutes, the watchdog. Recurring check-ins expire
   after 7 days, so the conductor renews them weekly. It runs in the same
   permission mode as Frans's coordinator, or messages between the two
   wait for his approval (013-02, section 6).
5. Start phase A: 012-02, 012-03 and 012-04 at once, and 012-05 once
   012-02's scanner exists; each task's status line says when it started.

## 9.2 The rules

* **A conductor session** works through section 8's order, with up to four
  subagents at a time in phase A and one or two later (the tasks are
  mostly in sequence). Subagents run Opus 5.5 at the task's effort (section
  7: max for the hard ones, high for the rest), each with a brief that
  points to its task file and to this one. Fewer agents when the 5-hour
  budget runs low or when other work, such as an unattended night like
  006-09, needs it: that work comes first.
* **Clones.** Each task works in a scratch clone of `bergdb`; the main tree
  takes only finished, gated work, copied in last. Shared files
  (`items/readme.md`) get targeted edits only.
* **State in the files.** Each task file has a progress section with what
  is done, the clone's path and the next step, written as the work goes,
  so that an agent stopped by a usage limit is resumed from it. The
  conductor keeps 012's log and its own state file, so that Frans can
  replace it by a fresh session at any time, with the prompt at the top of
  this plan; best between tasks, as subagents report only to the session
  that started them (013-02, section 1).
* **The Java reference.** At its start, a task records the Java commit it
  is checked against (`main`'s HEAD) and runs the quick cross set. If Java
  changed its bytes since the last task (Java's commits say whether
  `StreamDigest` is identical), C follows first.
* **Java bugs.** A bug that the port finds in Java is registered as a 005
  entry, with a probe that shows it, and not fixed in a 012 task. Until
  Java is fixed, C does as Java does where the bytes depend on it; after
  the fix, C follows.
* **Gates and commits.** A task is done when its "Done when" holds,
  `before-commit.sh` prints `C BEFORE COMMIT OK`, and `cross.sh full`
  passes. Then it is committed as decision D2 says: 012's files only,
  staged right before the commit, with a path list (013-01, section 9).
* **Frans's daily coordinator** (013-02), if one runs: the conductor is
  one of the sessions that report to it (013-02, sections 2 and 6). It
  asks it before a heavy run (`cross.sh full` and `scale`, the large runs
  of 012-14 and 012-15) and before taking a 005 number, tells it what it
  commits, and leaves it the machine while it times anything. 012's
  commits stay the conductor's (Frans, 2026-10-28: "The 012 conductor will
  commit as planned"), also while a coordinator owns the other commits to
  `main`.
* **Usage.** 012 is weeks of agents. The conductor reads the 5-hour and
  the weekly windows with 013-02's `usage.sh` (section 9) and paces
  itself: fewer agents, or high effort in place of max, when a window
  runs low; no new work when the weekly window is nearly used up, and a
  line in `news.md` saying so.
* **A stuck task** (no "Done when" item moved in a day of work, or the
  same failure after three attempts) stops at a safe point and writes in
  its file what it knows and what it tried. The conductor reports it in
  `news.md` ("needs a look") and goes on with another task, if one is
  free.
* **Other sessions.** The cross tests start JVMs and the builds use CPU.
  Neither runs while another session's timed block runs (look for its
  conductor, a timed JVM, and busy sessions in `~/.claude/sessions`) or
  while `night.sh` runs (from 02:10, about an hour); the C work waits, and
  never stops another session's runs.
* **Decisions.** A task that meets a question for Frans (the format, a Java
  bug that blocks the bytes, the scope) stops at a safe point, writes the
  question in its file with its options, and the conductor goes on with
  another task.
* **News.** `tools/news.sh` at each milestone, at a failure, and at a
  question for Frans; a summary at the end of each unattended night.


# 10. Risks

* **Byte equality is unforgiving.** Every decision of Java's writer must be
  the same in C: which nodes a record holds and in what order, splits, ids,
  vpos, the take, the got-dirty list, the meta blocks, the padding. Against
  it: a port, not a redesign; the scanners, which point at the first
  differing field; workloads with small nodes and startup distances, which
  exercise splits and the take on every few transactions; the comparison
  after every task, not only at the end.
* **Startup is the hardest part.** `DbStarter` and `NodeCollection` (Rule
  R, `posToId`, rule 4 by position since 005-57) must rebuild D, the take's
  state and reclaim's state exactly, or the next records differ. Against
  it: sis-model.md, 011-11, 005-57 and 005-58; the runs in turns between
  Java and C, which compare exactly this; max effort.
* **A moving reference.** Java's `main` changes daily: the paced take
  changed every stream on 2026-10-28 (3.2, point 9), and 005-52 and
  005-53 changed `Db`'s methods the same day. Against it: a pinned commit
  per task, the quick cross set at each task's start, and Java's
  `StreamDigest` notes.
* **Java's semantics.** Overflow, shifts, signed bytes, casts from double,
  fused multiply-add. Against it: the rules of 6.2,
  UndefinedBehaviorSanitizer, `-fwrapv`, `-ffp-contract=off`, and Java's
  vectors.
* **Hidden nondeterminism in Java**, if any: a hash-ordered iteration that
  decides the bytes, or timing, as reclaim's physical cut. Against it:
  012-02's audit, and comparisons from the decided cut. A real case would
  be a Java bug (P2), registered in 005.
* **Size and pace.** About 13,000 lines of C and their tests, written
  unattended. Against it: tasks with clear ends, milestones that each give
  something usable, and the state written as the work goes.
* **Disturbing other work.** CPU, JVMs, shared files and the usage budget.
  Against it: section 9's rules.


# 11. Decisions

Decided by Frans, 2026-10-27, in his request: the item and its tasks as
subitems, each with a plan; the Core to clone is `bergdb.core`; the API
corresponds to `Db`'s public methods; the stream is identical to Java's,
and each opens the other's databases; F53 is the only target for now;
unit, functional and stream tests against Java; the implementation runs
unattended as far as possible, from 2026-10-28 as first intended, now when
Frans says so (D7); 006-09's unattended work comes first.

Decided by this plan, as Frans left them to it ("You can choose C standard
and the compiler. Choose a simple way to build. [...] Chose how to test
this."): C17 with Apple clang 21 (6.1), `sh` scripts for the build (6.3),
and the tests and gate of 6.4 and 6.5. Frans may change any of them.

Decided by Frans on 2026-10-28: D1a, D2a, D3a, D4a, D5 as recommended,
D6b, and for D7: "When I say so. I plan to start a new Claude Code session
for this. It will be the conductor that can work unattended with 012."
Later the same day he changed D1: "Keep the C code in
items/012-bergdb-c/c/ indefinitely for now."
His comments of the same day, on the test clocks and on memory, are
answered in 4.4 and 4.5; of "The platform in one place" (4.2) he wrote:
"Very good! Good design."

The decisions as they were put to Frans, each with its outcome:

**D1. Where the C code lives.**

* D1a. **In the item, `items/012-bergdb-c/c/`, until 012-16; then moved to
  a top-level `c/`** if Frans accepts the result, with a line for it in
  README.md and AGENTS.md. This follows items/readme.md as written ("Code
  in an item is a prototype [...]"; "A result leaves an item on purpose"):
  nothing outside `items/` changes until the clone has proved itself. The
  cost is one move at the end.
* D1b. **A top-level `c/` from the start**, beside `java/` and `lean/`, with
  README.md and AGENTS.md saying so now. The C code is a second
  implementation of the Core rather than an experiment on Java, and it
  gets its final path at once.
* D1c. **A branch `012-bergdb-c` in a worktree**, as 009's switch: `main`
  untouched until a merge. Not recommended: the C code changes nothing that
  `main` has, so a branch only adds merges.
* Recommended: D1a. **Decided: the C code lives in
  `items/012-bergdb-c/c/`, indefinitely for now**: D1a without its move,
  so nothing moves at 012-16, and README.md and AGENTS.md get no line.

**D2. Commits.**

* D2a. **The conductor commits each task on `main` when its gates pass**,
  in Frans's name with no AI attribution, only its own files, and pushes
  `main` to `origin`, as 009's unattended steps do (009-01, section 6) and
  as 006-09 commits. The work is safe from one task to the next, and Frans
  reads it in `git log`.
* D2b. **Nothing is committed**; the finished tasks wait in the main tree
  for Frans. Safer for `main`, but days of uncommitted work beside other
  sessions' commits.
* Recommended: D2a. **Decided: D2a.**

**D3. The scope of the first clone.**

* D3a. **Levels 0 to 4** (section 1), in the order of section 8. All four
  are needed for "a database made by Java opens in C" in general: Java's
  databases may have reclaim's cuts, and may be larger than memory.
* D3b. **Levels 0 to 2 first**, then a stop for Frans's go before reclaim
  and eviction. Earlier feedback, a pause in the unattended run.
* Recommended: D3a, with the milestones of section 8 as natural points to
  stop if Frans wants to. **Decided: D3a.**

**D4. The Java reference.**

* D4a. **Java's `main`**, pinned per task, with C following each change of
  Java's bytes (section 9).
* D4b. **A fixed commit** for the whole of 012, and C brought up to date at
  the end. Simpler for the tasks; but 007-03's step 3 may change the
  bytes before 012 ends, and the catch-up is then a task of its own.
* Recommended: D4a. **Decided: D4a.**

**D5. Bugs that the port finds in Java.** Recommended: as section 9, a 005
entry each, not fixed in 012; C does as Java does until Java is fixed.
The alternative is a fix in `java/` by the 012 session, gated as any Java
change, which mixes the two projects. **Decided: as recommended.**

**D6. The stream format's document.** 012-02 is a subitem now.

* D6a. **It stays 012-02**, a document of the item, as history once 012
  is done; nothing outside the item changes.
* D6b. **Once the C clone writes Java's bytes, it becomes
  `docs/stream-format.md`**, kept up to date with the code like
  `docs/trace-format.md`, as the format is then shared by two
  implementations; `core/doc-files/stream-format.txt` of 2015 is replaced
  by a pointer to it. A change outside the item, so with Frans's go then.
* Recommended: D6b, decided at 012-10's end. **Decided: D6b**, now, which
  gives the go: the move is made when 012-10 is done, and `news.md` says
  so.

**D7. When the implementation starts.** Recommended: when Frans has
answered D1 to D6, or said "as proposed", on 2026-10-28; until then
nothing of 012 is written beyond the plans. **Decided: when Frans says
so**, by starting the conductor in a new Claude Code session (9.1).
