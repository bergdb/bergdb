012-03. Task: the C API
=======================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done, 2026-10-28 16:21** (started 15:55): "Done
when" holds, and the C gate passes; `cross.sh full` was not run, as the
header and the examples are only compiled. Approved with 012-01 by
Frans's go (012-01, 9.1).
Phase A (012-01, section 8). Effort: high. After: nothing.


# 1. The goal

`bergdb.h`, the C clone's whole API, designed before the code: the C
counterpart of `Db`'s public methods (012-01, section 5), with Java's
semantics where C can have them, and the reason for each departure.

Done when:

1. `include/bergdb.h` declares every type and function, each with a
   comment that says what it does, its errors, and who owns what. It
   compiles alone with the flags of 012-01, 6.1 (012-04's build checks
   it).
2. This file holds the table of `Db`'s public methods (45 since
   `fd8f513`, with 005-52's setter and getter of the cache size; count
   them again at the start), `DbBuilder`'s settings and the inner types
   (`Trans.Builder`, `GetData`, `GetMany` with its stop conditions,
   `StoredTrans`, `StartInfo`, `SyncLevel`), each with its C counterpart
   or the reason it is left out.
3. The error codes cover every exception that `Db`'s methods declare,
   each mapped.
4. The rules are written: one caller at a time; ownership of keys, values
   and results, and lifetimes, as 012-01, 4.5 says (the caller's objects
   and their free functions, freed before close; data given to a callback
   valid during it only; no call of the database from a callback); what a
   failed database (P7) still allows; the units of time; the clock (012-01,
   4.4); what `bergdb_open` creates.
5. Two small examples are written against the header (and compile): C's
   `CoreDemo` (006-08) and a `getMany` with a prefix.


# 2. Read first

* `Db`'s Javadoc and each public method's comment and code, `DbBuilder`,
  `Trans` and `Trans.Builder`, `GetData`, `GetMany` and its stop
  conditions, `StoredTrans`'s public fields, `StartInfo`, `SyncLevel`,
  `KeyTransformation`, `ValueTransformation`, and the exceptions of
  `pub.util`, `storage` and `core`.
* `docs/levels.md`, section 3 (a transaction or a read that fails).
* 010-01: P7, P9, P10, P12. 012-01, sections 4 and 5. 006-08's
  `CoreDemo.java`.


# 3. The work

1. Go through `Db`'s methods one by one and write the table (done item 2).
2. Decide, and write why:
   * **Handles and contexts.** An opaque `bergdb_db`; a transaction
     builder `bergdb_trans`; a read context in place of `GetData` that owns
     the buffer a value is returned in; a result type for `getTrans`.
   * **Options.** A struct with Java's defaults (`bergdb_options_init`):
     the node size (8, 14, 30 or 62; 30 by default), the startup distance
     (50 MB), the cache budget (200 MB), the retain duration (forever),
     the internal fraction (0.25), the clock (a function and its context;
     by default the system clock, milliseconds times 10,000 as Java's
     `SystemClock`; the test clock, `CoreTestClock`'s, in the library, so
     that times and bytes can be deterministic: 012-01, 4.4), the
     database id (random, or given, or the test id). Java's checks of each
     (a startup distance of at least 10, a retain duration of at least one
     second, and so on).
   * **Keys.** Byte keys (bkeys), converted to segments inside as
     `Keys.toSegments(byte[])`; a helper for ikeys, as Java's
     `Keys.toBytes(String)`, since the Core's string keys are ikeys.
   * **Values.** How `getOne`'s null (no value: never put, or deleted) is
     told apart from an empty value; how long a returned value stays
     valid (in the read context's buffer, until its next call; 012-01,
     4.5).
   * **`getMany`.** A range struct (lookup time, start key, inclusive,
     direction) and the stop conditions (none, end key, count, prefix), or
     a callback that returns `ADD`, `STOP`, `CONTINUE` or `ADD_AND_STOP`
     as Java's; both, if simple.
   * **Transactions.** Put, delete, the read set (`keyRead`, the lookup
     time; refusal as `RerunException`), the key and value transformations
     as callbacks that must not fail; after `execute`, the time and the
     positions (`tt`, `tpos`, `lastPos`, `nextPos`).
   * **Errors.** One enum: OK, RERUN, NOT_AVAILABLE (a lookup time or a
     position before the first available one), FAILED (the database has
     failed; the first failure's text is kept), IO, FORMAT (corrupt, or
     another version), STATE (not started, or closing), ARG, LIMIT (the
     record limit, the top node ordinals), NOT_CREATED (an incomplete
     creation), NOMEM. A text for the last error of a handle.
   * **Status.** One struct filled by one call, or one function per
     getter: choose the simpler to keep in step with Java.
   * **Replicas and encryption** left out (012-01, section 1); an
     encrypted database gives FORMAT.
3. Write the header, then the examples against it.


# 4. Tests

The header compiles alone; the examples compile (they link once the
functions exist, in 012-13). Later tasks implement the functions and test
them; this task checks only the design.


# 5. Notes

* Small and like Java (P12): no function that Java's `Db` does not have,
  but for the C necessities (free functions, the error text, the ikey
  helper).
* The header may change as the implementation teaches; each change after
  this task is noted in this file's progress section, with its reason.


# 6. The API, as designed

`c/include/bergdb.h` is the API: its top comment has the rules (sections
A to G), and each declaration says what it does, its errors and who owns
what. This section maps Java onto it and gives the reasons. Java's
reference: `main` at `0b6d08e`, `java/` as of `fd8f513` (section 7).

## 6.1 The C API in one table

| C | What | Java |
|---|---|---|
| `bergdb_open`, `bergdb_close` | open (create, start), close | `builder()`, `DbBuilder.build()`, `start()`; `stop()`, `close()` |
| `struct bergdb_options`, `bergdb_options_init` | the settings, Java's defaults | `DbBuilder` |
| `struct bergdb_start_info` | what the open read | `StartInfo` |
| `bergdb_trans_new`, `_free`, `_put`, `_put_transformed`, `_delete`, `_key_read`, `_lookup_time` | a transaction: the builder | `trans()`, `Trans.Builder` |
| `struct bergdb_transform` | key and value transformations | `KeyTransformation`, `ValueTransformation` |
| `bergdb_execute`, `struct bergdb_executed` | execute; where it went | `execute(Trans)`, `execute(Trans.Builder)`; `Trans`'s outputs |
| `bergdb_read_new`, `_free` | a read context | `newGetData()`, `newGetMany()` |
| `bergdb_get_one`, `struct bergdb_one` | a value at a time | `getOne`, `GetData`'s outputs |
| `bergdb_get_many`, `struct bergdb_range`, `bergdb_range_init`, `bergdb_stop_fn`, `struct bergdb_many`, `struct bergdb_kvt` | pairs in key order | `getMany`, `GetMany`, its stop conditions, `Kvt` |
| `bergdb_get_trans`, `struct bergdb_stored` | a stored transaction | `getTrans`, `StoredTrans` |
| `bergdb_sync` | durability | `sync(SyncLevel)`, `sync(long, SyncLevel)` |
| `bergdb_current_time`, `bergdb_lookup_time` | the clock's times | `currentTime()`, `lookupTime(long)` |
| `bergdb_set_startup_distance`, `_set_cache_size_indicator`, `_set_retain_duration`, `_set_reclaim_internal_fraction` | the setters | Db's four setters |
| `bergdb_stats`, `struct bergdb_stats` | the status | Db's getters |
| `bergdb_debug_print`, `bergdb_debug_check` | for tests | `printDag`, `checkNodes` |
| `bergdb_errmsg`, `bergdb_errname`, `enum bergdb_error` | errors | the exceptions (6.5) |
| `bergdb_ikey_to_bkey`, `bergdb_bkey_to_ikey` | key conversions | `Keys.toBytes(String)`, `Keys.bkey2ikey` |
| `struct bergdb_test_clock`, `bergdb_test_clock_time`, `_set`, `bergdb_clock_fn` | clocks | `Clock`, `CoreTestClock` |
| `bergdb_test_id` | the test id | `DatabaseId.TEST_ID` |
| `struct bergdb_mem` | the allocator's counts | none: C's (D12) |

33 functions, 12 structs, 3 opaque types, 4 enums and the test id. Beyond
`Db`'s methods and the types of `bergdb.core` and `dag` that they use
(`CoreTestClock` among them), only C's necessities (section 5):
the two free functions, the error text and names, the key conversions,
the initializers of two structs (Java's constructors), and the
allocator's counts.

## 6.2 `Db`'s 45 public methods

In `Db.java`'s order. "Left out" says why.

| # | `Db` | C | Note |
|---|---|---|---|
| 1 | `getStreamLength()` | `bergdb_stats`: `stream_length` | |
| 2 | `getStartupDistance()` | `bergdb_stats`: `startup_distance` | |
| 3 | `getDirtyFraction100()` | left out | read only by `Jmx` (left out, 012-01, 4.1); it only decays, or is NaN (6.8, F3) |
| 4 | `getDirtyFraction1000()` | left out | the same |
| 5 | `setStartupDistance(int)` | `bergdb_set_startup_distance` | state first, clamped, nothing for the value in force, else the dummy transaction, the setting put back if it is refused (005-53) |
| 6 | `getCachePutSize()` | left out | read only by `Jmx`; a constant, 10,000 (`Cache3.putSize`, which "nothing advances"; 6.8, F2). C's figure of the memory is `struct bergdb_mem` |
| 7 | `getCacheSizeIndicator()` | `bergdb_stats`: `cache_size_indicator` | |
| 8 | `setCacheSizeIndicator(long)` | `bergdb_set_cache_size_indicator` | evicts at its own end where Java wakes its thread (005-52) |
| 9 | `getRetainDuration()` | `bergdb_stats`: `retain_duration` | |
| 10 | `setRetainDuration(long)` | `bergdb_set_retain_duration` | |
| 11 | `setReclaimInternalFraction(double)` | `bergdb_set_reclaim_internal_fraction` | |
| 12 | `getInternalFraction()` | `bergdb_stats`: `internal_fraction` | |
| 13 | `getReclaimIterationCount()` | `bergdb_stats`: `reclaim_iteration_count` | |
| 14 | `getFirstAvailableLookupTime()` | `bergdb_stats`: `first_available_lookup_time` | |
| 15 | `getFirstAvailablePos()` | `bergdb_stats`: `first_available_pos` | |
| 16 | `getTransactionCount()` | `bergdb_stats`: `transaction_count` | |
| 17 | `getKvCount()` | `bergdb_stats`: `kv_count` | |
| 18 | `getGetOpCount()` | `bergdb_stats`: `get_op_count` | |
| 19 | `getDurableLength()` | `bergdb_stats`: `durable_length` | |
| 20 | `getLastTransPosOfLastValidMetaBlock()` | `bergdb_stats`: `last_trans_pos_of_last_valid_meta_block` | |
| 21 | `addReplica(...)` | left out | replicas (012-01, section 1) |
| 22 | `removeReplica(String)` | left out | replicas |
| 23 | `getStorageInfos()` | left out | a figure per stream, for replicas; with one stream, `stream_length` and `durable_length` say it |
| 24 | `currentTime()` | `bergdb_current_time` | |
| 25 | `lookupTime(long)` | `bergdb_lookup_time` | |
| 26 | `start()` | `bergdb_open` | the open is build and start in one call: a C handle exists only started (D1) |
| 27 | `start(StartParams)` | left out | test-only (a given startup position and distance); no caller but `start()` (`BigDb`'s is a comment) |
| 28 | `stop()` | `bergdb_close` | with no thread, stop is close |
| 29 | `close()` | `bergdb_close` | |
| 30 | `printDag(PrintStream)` | `bergdb_debug_print(db, FILE *)` | C's own text |
| 31 | `newGetData()` | `bergdb_read_new` | one read context for the three reads (D1) |
| 32 | `newGetMany()` | `bergdb_read_new` | |
| 33 | `getOne(long, long[], GetData)` | `bergdb_get_one` | a bkey, not segments (D3) |
| 34 | `getTrans(long)` | `bergdb_get_trans` | |
| 35 | `getOneInternal(long, long[], GetData)` | left out | internal: `getOne` without the state check, for `Db`'s warm-up and `Reclaim` |
| 36 | `getMany(GetMany)` | `bergdb_get_many` | |
| 37 | `sync(SyncLevel)` | `bergdb_sync(db, 0, level)` | |
| 38 | `sync(long, SyncLevel)` | `bergdb_sync` | a position at or past the end is ARG (D11) |
| 39 | `checkNodes()` | `bergdb_debug_check` | FAILED on a failed database (D14) |
| 40 | `execute(Trans.Builder)` | `bergdb_execute` | the C transaction is the builder |
| 41 | `execute(Trans)` | `bergdb_execute` | |
| 42 | `getAccessData()` | left out | internal: minus the node table's access clock, which `Db` writes into what its operations follow, for eviction's age policy (`Cache3`); C's node table is its own (012-12) |
| 43 | `internal()` | left out | Java's internals |
| 44 | `builder()` | `bergdb_options_init`, `bergdb_open` | |
| 45 | `trans()` | `bergdb_trans_new` | |

35 of the 45 have a C counterpart, in 19 functions (13 getters are the
fields of `struct bergdb_stats`, filled by one); 10 are left out: 3 dead
figures read only by JMX, 3 of replicas, 4 internal or test-only.

## 6.3 `DbBuilder`'s settings

| `DbBuilder` | C | Note |
|---|---|---|
| defaults (the constructor) | `bergdb_options_init` | node size 30, startup distance 50,000,000, cache size indicator 200,000,000, retain forever, the system clock, a random id |
| `maxNodeSize8()`, `14()`, `30()`, `62()` | `max_node_size`: 8, 14, 30, 62 | else ARG; another than the stream's is FORMAT (005-50) |
| `startupDistance(int)` | `startup_distance` | at least 10, else ARG, as Java |
| `cacheSizeIndicator(long)` | `cache_size_indicator` | no check, as Java |
| `noEvict()` | `BERGDB_NO_EVICT` | `Long.MAX_VALUE` |
| `retainDuration(long)` | `retain_duration` | at least one second, else ARG, as Java |
| `retainForever()` | `BERGDB_FOREVER`, the default | |
| `clock(Clock)` | `clock`, `clock_ctx` | a function and its context |
| `systemClock()` | `clock` NULL, the default | `SystemClock`'s code |
| `id(DatabaseId)` | `id[16]` | for a database the open creates |
| `testId()` | `bergdb_test_id` copied to `id` | |
| (the random id) | `id` all zeros, the default | `CREATE_LATER_MARKER` is zeros, and `createFromBytes` refuses zeros, so zeros cannot be an id |
| `mainStream(AppendOnlyStream)` | `bergdb_open`'s `dir`; NULL for memory | a `FileStream` or a `MemoryStream` (D13) |
| `stream(name, aos)`, `stream(name, aos, bufferSize, bufferTime)` | left out | replicas; C's one buffer has a fixed size and no buffer time (012-01, 4.3) |
| `createdTxt(File, String)` | left out | the Pub API's `created.txt` |
| `testSetup()`, `testSetup(stream)`, `testSetupExceptStream()` | the options of `examples/get_many_prefix.c` | the test clock, `BERGDB_NO_EVICT`, forever, the test id; `dir` NULL |
| `evictionSchedule(schedule, seed)` | left out | Java's eviction tests; C's own invariance test (012-12) sets its schedules inside |
| `reclaimStepReserve(long)` | left out | for the stress programs; Java's default (4 MiB) |
| `audit(int)` | left out | Java's audit; C has its own debug checks (012-01, 4.5) |
| `secondTopOrdinal(long)` | left out | 005-02's tests; a later task adds it inside if a cross test needs it |
| `build()`, `start()` | `bergdb_open` | |
| `getStreamCount()`, `getMainStream()`, `closeStreams(Throwable)` | left out | the streams are the open's own, and a failed open closes them |
| (not a builder setting) `Db.setReclaimInternalFraction` | the setter only | as Java: the task's list had it among the options; the workload format (012-05, 6.1) sets it right after the start, as C does |

## 6.4 The inner types

**`Trans.Builder`**

| Java | C | Note |
|---|---|---|
| `put(byte[], byte[])` | `bergdb_trans_put` | copies the key and value |
| `put(long[], byte[])` | left out | segments are internal; a bkey gives the same (D3) |
| `put(long[], KeyTransformation, byte[], ValueTransformation)` | `bergdb_trans_put_transformed` | a bkey |
| `put(String, String)`, `put(String, byte[])` | `bergdb_ikey_to_bkey`, then `bergdb_trans_put` | a string value is its UTF-8 bytes |
| `delete(byte[])`, `delete(long[])`, `delete(String)` | `bergdb_trans_delete` | a bkey; an ikey through the helper |
| `keyRead(long[])`, `keyRead(String)` | `bergdb_trans_key_read` | a bkey |
| `lookupTime(long)` | `bergdb_trans_lookup_time` | negative: ARG |
| `addReadHash`, `addReadHashes`, `addVirtualWriteHash` | left out | the Pub API's virtual keys (directories, indexes: `RwEnvironmentImp`, `IndexManager`); a hash is internal (`Keys.hash` of segments) |
| `build()` | in `bergdb_execute` | sorted by key; for a key given twice the last counts, but a delete does not replace a put |

**`Trans`**: `tt`, `tpos`, `lastPos`, `nextPos`, `startupPos`, `nodeCount`
are `struct bergdb_executed`; the inputs (`kvs`, `writeKeyHashes`,
`readTime`, `readKeyHashes`) are made by the builder's calls; `listener`
(test hooks) and `isInternal()` (the database's own transactions) are left
out. A transaction can be executed again (`Trans.testTransReuse`); unlike
Java's, it belongs to its database (D1).

**`KeyTransformation.transform(Trans, int)`** is `bergdb_transform.key`:
it gets the transaction's time and the key, and may give another key. In
Java it sets the key and the write hash; its only user
(`RwEnvironmentImp.replaceTransformation`) sets the hash to `Keys.hash` of
the new key, which is what C does. **`ValueTransformation.transform(long,
byte[], byte[])`** is `bergdb_transform.value`, with the previous value
(the one before the transaction, NULL if none); NULL as the new value
makes the put a delete, as Java's null does in `dag.putKv`. Both replace
the transaction's key or value, as Java's `Kv.setKey` and `transformValue`
do, so a transaction executed again starts from them.

**`GetData`**: `actualLookupTime`, `kvTime`, `tpos` are `struct
bergdb_one`'s; `followMemoryPointerCount` and `followStreamPointerCount`
are left out (written by `Dag`, read nowhere); `nodeDepth` and `OpData`'s
fields (the pointer follower and listener, the cache policy, the access
data) are internal.

**`GetMany`**: `lookupTime`, `startKey`, `inclusive`, `forward`
(`setBackward()`) are `struct bergdb_range`'s; `stopCondition` is the
range's stop conditions (below); `actualLookupTime`, `result` and
`getOpCount` are `struct bergdb_many`'s; `gd` is the read context; `cache`
is left out (read nowhere: no effect in Java); `Chain` is internal.

**`GetMany.StopCondition`**: `handleKvt` is `bergdb_stop_fn`, with
`ADD`, `STOP`, `CONTINUE`, `ADD_AND_STOP` as `enum bergdb_stop_answer`
(Java's numbers); `eod()` is `bergdb_many.eod`. Java's conditions:

| Java | `struct bergdb_range` |
|---|---|
| `DontStop` (the default) | none |
| `Endpoint(key)`, `Endpoint(key, inclusive)`, `Endpoint(key, inclusive, backward)` | `end_key`, `end_inclusive` (true by default, as `Endpoint(key)`'s code); `backward` is the read's direction |
| `GetN(n)`, `GetOne` | `max_count` n, 1 (0: none, as `GetN(0)`, which never stops) |
| `Prefix(p)` | `prefix` |
| `PrefixN(p, n)` | `prefix` and `max_count` |
| one's own | `stop`, `stop_ctx` |

**`Kvt`**: `key`, `value`, `time`, `spos` are `struct bergdb_kvt`.

**`StoredTrans`**: `tt`, `tpos`, `lastPos`, `startupPos`, `topPos` are
`struct bergdb_stored`'s, and `getValueNodes()`, the value and delete
nodes in record order, its `values` (each a `bergdb_kvt` with the key, the
value or NULL for a delete, the transaction's time and the node's
position). Left out: the index nodes of `nodes`, `gotDirtyIdsAndSpos`
(the record's internals, which the scanners show: 012-02, 012-06),
`getValueNode(long[])` (deprecated), `findNode(long)`, `parse`, `print`,
`toString`, the constants, `Serializer`, `Parser` and `StoredTrans.Kv`.
The cross harness's dumper (012-05, 6.3) needs exactly what C keeps.

**`StartInfo`**: `startPos`, `startupDistance`, `startTime`,
`transCount`, `lastPos` are `struct bergdb_start_info`'s. Java's
`startupDistance` is -1 on every start (6.8, F1); C keeps it, so that
C's runner prints what Java's prints. **`StartParams`** is left out
(test-only).

**`SyncLevel`** is `enum bergdb_sync_level`, with Java's numbers;
`STRONG` is `ORDINARY` with one stream, as Java's with no replica.

**`Clock`** is `bergdb_clock_fn`, `Clock.UNITS_PER_SEC`
`BERGDB_UNITS_PER_SEC`; **`CoreTestClock`** is `struct bergdb_test_clock`
with `bergdb_test_clock_time` and `bergdb_test_clock_set`; `TestClock`
(core's copy of the Pub API's) is not needed: it differs only in
refusing an out-of-range time when set, which `DbClock` refuses anyway at
the transaction (012-01, 4.4). **`SystemClock`** is the default.
**`DatabaseId`**: the options' `id`; `TEST_ID` is `bergdb_test_id`.

**`Keys`**: `toBytes(String)` is `bergdb_ikey_to_bkey`, `bkey2ikey` (and
`toString(long[])`, the same of the segments' bytes) `bergdb_bkey_to_ikey`
before Java's UTF-8 decoding; the rest is internal (`src/keys.h`).

**Left out as internal or test hooks**: `Db.Internal`, `ExecuteData`,
`Aux`, `ReadSync`, `WriteLock`, `StartListener`, `PrintStartListener`,
`TransactionListener`, `TestHooks`, `Trans.Listener`, `Kv`. `Db`'s
`AutoCloseable` is `bergdb_close`.

## 6.5 The error codes

Every exception that `Db`'s methods declare or throw, and those of
`DbBuilder` and of `FileStream`'s constructor (which C's open makes):

| Code | Java | Where |
|---|---|---|
| `BERGDB_OK` 0 | | |
| `BERGDB_RERUN` | `RerunException` | `execute`: the read set's conflict |
| `BERGDB_NOT_AVAILABLE` | `LookupTimeNotAvailableException` | reads before the first available time, a read a cut overtook, `getTrans` of a removed transaction |
| `BERGDB_FAILED` | `DbFailedException` | every transaction and read after a failure; the call that fails it; `sync` on a failed storage; `setStartupDistance` |
| `BERGDB_IO` | `StreamIoException`, `FileStream`'s `IOException` | the open; the close (D10). After the open, an I/O error fails the database (FAILED) |
| `BERGDB_FORMAT` | `StreamFormatException`, `VersioningStreamException`, `BadMagicBytes` and `BadCryptoKey` (which start throws for it), `StreamChecksumException`, `InternalDataException`, `BadDirStateException` | the open; after it, corrupt data fails the database |
| `BERGDB_STATE` | `IllegalDbStateException`, `DbStoppingException`, `IllegalStateException` (a second `start()`) | a call from a callback (D9); "not started" and "stopping" cannot occur, as a handle exists from its open to its close |
| `BERGDB_ARG` | `IllegalArgumentException` | the builder's and setters' checks, `getTrans`'s positions, `put`'s null, `lookupTime`'s negative time, C's NULL pointers and lengths over `INT32_MAX`, `sync` past the end (D11), a stop function's bad answer |
| `BERGDB_LIMIT` | `DbException` | `execute`: the size (005-17), the dirty nodes (005-31), the top node ordinals (005-02), the clock's range and the end of times (005-18); the open: the clock at the creation |
| `BERGDB_NOT_CREATED` | `DatabaseNotCreatedException` | the open (005-33) |
| `BERGDB_IN_USE` | `DirectoryInUseException` | the open (005-63) |
| `BERGDB_NOMEM` | `OutOfMemoryError` | anywhere; a refusal before a go point (after it, FAILED: D7) |

Not mapped: `BadReplicaException` (replicas), `BadFormatException` (the
Pub API's), `Bug` and `AssertionError` (a bug: C's `assert`, 012-04's
readme, rule 12).

## 6.6 The decisions

Each with its reason; Frans may change any.

* **D1. Handles.** Three opaque types: `bergdb_db`; `bergdb_trans`, the
  transaction builder, which `bergdb_execute` builds and executes; and
  `bergdb_read`, one read context in place of `GetData` and `GetMany`,
  that owns the buffer its results are copied into (012-01, 4.5). One
  context for the three reads keeps the types and free functions few, and
  `getTrans` needs no result type of its own to free: its result is a
  plain struct in the context, as `getOne`'s and `getMany`'s. A
  transaction and a read context belong to the database that made them,
  as their memory is counted by its allocator (P9: no global allocator);
  Java's `Trans` can run on another `Db`. The open is build and start in
  one call: Java's builder and its unstarted `Db` have no use in C, and a
  handle that exists only started removes "not started" from every call.
  The read calls take the database and the context, as Java's
  `db.getOne(time, key, gd)`.
* **D2. Options.** One struct with Java's defaults
  (`bergdb_options_init`), checked by the open as Java's builder checks
  them; `opt` NULL is the defaults. The fields are `DbBuilder`'s settings;
  the internal fraction is not one, as in Java (6.3). The id: zeros give a
  random one. The clock is a function and its context, NULL for the system
  clock; the test clock is in the library, as `CoreTestClock` is in
  `bergdb.core`, so that every C caller can make deterministic times and
  bytes (012-01, 4.4).
* **D3. Keys** are bkeys (bytes and a `size_t` length), converted to
  segments inside, as `Keys.toSegments(byte[])`; segments stay internal,
  so `put(long[], ...)` and its likes have no C form. The ikey helper
  converts both ways (`Keys.toBytes(String)`, `bkey2ikey`), as a program
  that reads keys back as text needs the second, and `CoreDemo` uses it
  (`Keys.toString`). Lengths over `INT32_MAX`, longer than a Java array,
  are ARG.
* **D4. Values.** A returned value pointer is NULL exactly where Java's
  value is null: no value (never put, or deleted); an empty value has a
  non-NULL pointer and length 0. A pointer given in is never NULL (Java's
  `put` refuses null; a delete is its own call). A returned value is
  copied into the read context's buffer, valid until the context's next
  call, its free or the close: the index object that holds it may be
  evicted and freed at the end of the call (012-01, 4.5). Java's getOne
  copies nothing; C copies one value.
* **D5. `getMany`.** A range struct (lookup time, start key, inclusive,
  direction) with Java's stop conditions as fields and a callback, both:
  the fields are Java's five classes, simple to use, and the callback is
  `StopCondition` itself, for everything else (the Pub API's conditions
  are all its own). Several may be given; each pair goes through them in a
  fixed order, and the first answer that is not ADD decides (bergdb.h,
  `struct bergdb_range`). Java's own combinations are kept: `PrefixN` is a
  prefix and a count, `GetN(0)` never stops. A combination Java has no
  class for (an end key and a count) is one that a Java caller writes as a
  `StopCondition` of its own, so it adds no feature (P12). The results go
  into the read context, as Java's `result` list; `eod` is Java's `eod()`.
  An end key takes the read's direction, as Java's `Endpoint` with a
  `backward` flag that differs from the read's has no use.
* **D6. Transactions.** Put, delete, the read set and its lookup time,
  `RerunException` as RERUN; the transformations as callbacks with in-out
  pointers, which cannot fail (they run after the go point) and give their
  new key or value in memory of their own, copied at once; after
  `bergdb_execute`, the time and the positions in `struct
  bergdb_executed`. The hash-level builder calls are the Pub API's (6.4).
* **D7. Errors.** One enum: the task's list and `BERGDB_IN_USE`, as
  `DirectoryInUseException` (005-63) is its own class in Java, and "open
  elsewhere, try later" is a different answer from an I/O error. Every
  failure after a go point returns FAILED, also out of memory, where Java
  throws an `Error` as it is: in C, the code says whether the database
  goes on, and the text says why. A handle's last error text
  (`bergdb_errmsg`, with the first failure's text after FAILED); a code's
  name (`bergdb_errname`), for runners and messages; `bergdb_open`, which
  has no handle when it fails, writes its text into the caller's buffer
  (`BERGDB_ERRBUF_SIZE`, as `pcap_open_live`'s), and returns no half-open
  handle, so a failed open leaves nothing to close (012-01, 4.5, point 7).
  Java's start throws `DbFailedException` when reclaim's table cannot be
  read; C's open gives IO or FORMAT, as there is no database left to fail.
* **D8. Status.** One struct filled by one call, `bergdb_stats`: each of
  `Db`'s getters is a field, so a getter that Java adds is a field, and the
  map stays one line per getter; the setters are functions. One function
  per getter would add eleven functions for no gain. The fields are all
  cheap in C (no locks), and the call works on a failed database, as
  Java's getters do.
* **D9. Callbacks** may not call their database: STATE, and nothing done
  (a free does nothing; the close frees the object). Simple to check (a
  flag in the database), and it keeps the ported code's state consistent
  during a callback, which Java guards by its locks.
* **D10. Close** frees the transactions and read contexts not yet freed
  (they are counted by the database's allocator, so after any close its
  count is 0, as 4.5 requires), and returns IO when its last write or
  force fails. In C, the close writes what the buffer holds (no thread
  wrote it within 20 ms), so its failure is the only report that
  unsynced transactions are lost; Java's `close()` drops it (6.8, F5).
* **D11. Sync past the end** is ARG. Java waits for another thread's
  transaction to reach the position; with one caller, nothing could, and
  the call would hang.
* **D12. The allocator's counts in the API** (`struct bergdb_mem`, the
  options' `mem`). A C necessity with no Java counterpart: without a
  garbage collector, the tests check through `bergdb.h` alone (the
  functional tests, 012-01, 6.4) that every byte is freed at the close,
  and make allocations fail in turn (4.5); a caller may read its database's
  exact memory (P8). Its fields are `src/mem.h`'s `struct mem`, which the
  task that writes `bergdb_open` makes one definition with it (6.10).
* **D13. A database in memory**: `dir` NULL, a stream in memory that the
  database owns and the close drops, as Java's `testSetup()`. Restarts
  on one memory stream (Java's tests reuse a `MemoryStream`) are not in
  the API: functional tests restart in directories; 012-13 adds a memory
  stream object of the caller's if they prove too slow (6.10).
* **D14. Debug calls** refuse a failed database (FAILED): its memory may
  be half changed, and `checkNodes` would stop on an assert; Java's has no
  state check.
* **D15. Names** are Java's in snake case (`cache_size_indicator`,
  `get_one`, `set_reclaim_internal_fraction`), not 012-01's sketch
  (`cache_budget`, `bergdb_get`), so that each line of 6.2 to 6.4 reads
  across.
* **D16. Replicas and encryption** are left out (012-01, section 1); an
  encrypted database is refused at the open with FORMAT (its magic bytes,
  Java's `BadMagicBytes`).

## 6.7 The rules

Done-when item 4, in `bergdb.h`'s top comment: one caller at a time
(section A); errors, refusals and failures, and what a failed database
still allows (B); ownership and lifetimes: the caller's objects and their
free functions, freed before the close or by it, results valid until the
context's next call, the pointers the database keeps (C); callbacks: data
valid during the call only, no call of the database (D); keys and values
(E); the units of time and the clock (F); what `bergdb_open` creates (G).

## 6.8 Findings in Java

For the conductor, who decides on 005 entries (012-01, section 9: not
fixed in 012). None changes the stream's bytes. F1 to F4 and F6 are shown
by a probe on Java's `main` at `0b6d08e` (the Core Layer compiled by
`test/cross/java-build.sh`; the probe, `ApiProbe.java`, was a scratch file
of this task, kept nowhere): `StartInfo.startupDistance=-1`,
`getCachePutSize=10000`, `getDirtyFraction100` 0.099 after one
transaction and NaN after an empty one, `getInternalFraction=NaN` after
`setReclaimInternalFraction(Double.NaN)`, and `Endpoint(key)` returns the
end key.

* **F1. `StartInfo.startupDistance` is -1 on every start.** `startInner`
  sets it from its parameter, `StartParams.NULL` for `start()`, as
  `handleStartParams` replaces only its own local `params`. 012-05's
  `Run` prints it (`startupDistance=-1`); C keeps the -1.
* **F2. `getCachePutSize()` is a constant**, 10,000: `Cache3.putSize`
  is set at the construction and "nothing advances" it (`Cache3`'s
  comment on the access clock). Read only by `Jmx`.
* **F3. `getDirtyFraction100()` and `1000()` only decay**: `Aux.updateStats`
  sets `ordinaryNodeCount` to the record's node count, so `dirtyNodeCount`
  is always 0, and the figures fall from 0.10 by 1% (0.1%) a
  transaction, and turn NaN for good after an empty transaction, whose
  record has no node (0/0). Read only by `Jmx`.
* **F4. `setReclaimInternalFraction(NaN)` passes** `Reclaim`'s check
  (`f < 0.001 || f > 0.90` is false for NaN). C does as Java.
* **F5. `close()` and `stop()` drop `closeStorage`'s `IOException`**: a
  failed last flush is reported only by a start that throws (as
  suppressed). C's close returns it (D10).
* **F6. `GetMany.Endpoint(long[] key)`'s comment says "Non-inclusive"**,
  but the code makes it inclusive (`this(key, true, false)`). C follows
  the code.
* **F7. Dead fields**: `GetMany.cache` is read nowhere, and `GetData`'s
  `followMemoryPointerCount` and `followStreamPointerCount` are only
  written.

## 6.9 Questions for Frans

None. The departures from Java (D7's FAILED after the go point, D10, D11,
D14) are the C necessities of one caller and no garbage collector, each
with its reason above.

## 6.10 Notes for the tasks that implement it

* **`src/mem.h`** (012-04): `struct mem` and `enum mem_kind` have the
  fields and kinds of `bergdb.h`'s `struct bergdb_mem` and `enum
  bergdb_mem_kind`, in the same order. The task that writes `bergdb_open`
  (012-09) makes them one definition (mem.h on bergdb.h's), so that the
  options' `mem` is the allocator's own struct.
* **Error names in the cross texts.** Java's runners print the exception's
  class (`error=RerunException`); C's will print `bergdb_errname`, and
  several Java classes are one C code (FORMAT). So `cross.sh` must map
  Java's names to C's codes by 6.5's table before it compares the `start
  error=` and `refused` lines, or Java's runners print the C name too:
  for 012-09 and 012-13 to settle with 012-05's harness.
* **`bergdb_close` has no text** for its IO: the database is gone. A
  caller that needs one syncs first (`bergdb_sync` has the handle's text).
* **A memory stream across restarts** (D13): 012-13 decides with the
  functional tests.
* **The header changes** as the implementation teaches: each change after
  this task is a line in this file's progress, with its reason (section
  5).


# 7. Progress

* **2026-10-28 15:55, start.** In the clone `/Users/f/fl/bench/012/03-c-api`
  (of `main` at `0b6d08e`). The Java reference: `main` at `0b6d08e`, whose
  `java/` is as of `fd8f513` (no commit since touches `java/`). `Db` has
  **45 public methods** there, counted again with
  `grep -E '^    public [^=]*\(' java/src/bergdb/core/Db.java` (the
  constructor is package-private): as 012-01 says.
* **16:05, `bergdb.h`'s first full draft** (commit `ee4247d`): compiles
  alone with the build's flags, with `-Weverything` and as C++.
* **16:12, the examples** (`fbd2956`): `examples/core_demo.c` (C's
  `CoreDemo`) and `examples/get_many_prefix.c`; both compile with the
  build's flags (`-fsyntax-only`; they link in 012-13).
* **16:16, section 6** (`44f9294`): the tables, the error codes, the
  decisions D1 to D16, the rules' places, the findings F1 to F7, the
  notes.
* **16:18, Java probes** (scratch files, not kept; the Core Layer compiled
  by `test/cross/java-build.sh` into the clone's `build/java/`): the
  prefix example's calls on Java's `Db` print exactly the output now in
  `get_many_prefix.c`'s comment; `CoreDemo.java` prints what
  `core_demo.c`'s comment says; Java's Core takes the empty bkey; F1 to F4
  and F6 shown (6.8). The C gate with the header and the examples:
  `build.sh` BUILD OK, `before-commit.sh` C BEFORE COMMIT OK (21 s, the
  quick cross set included) (`c8cffaa`).
* **16:19, the header read against section 6** (`19b687b`): STATE among
  the refusals, the empty bkey, open's error buffer, close's code without
  text, put's NULL rule, getMany's negative count, the clock checked when
  it returns, the key transformation before the value's.
* **16:21, done.** "Done when": (1) `include/bergdb.h` declares every
  type and function with what it does, its errors and who owns what, and
  compiles alone with 6.1's flags (also with `-Weverything` and as C++);
  (2) the tables of 6.2 to 6.4; (3) the error codes against every
  exception of `Db`'s methods (6.5); (4) the rules in the header's
  sections A to G (6.7); (5) the two examples, which compile, with Java's
  outputs to compare once they link. `build.sh` BUILD OK, `before-commit.sh`
  C BEFORE COMMIT OK (23 s). No question for Frans; findings F1 to F7 for
  the conductor (6.8). Next: the conductor checks and copies the files
  into the main tree; the implementing tasks follow 6.10.
