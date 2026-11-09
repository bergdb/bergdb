# 020-10 The indexes of 2026.4: the design for implementation

Created 2026-11-08 by Frans Lundberg. Status: decided, for tonight's
implementation (2026-11-08 to 09). The user indexes of release 2026.4 as
020-01, section 14.1, decided them (Frans, 22:08 to 22:12), written exact
enough to code and test from: the API, the stored layout, the maintenance,
the jobs, the boundary, the fault map, the harnesses and the steps, with
the files each step owns. Where 020-01 left a gap, it is decided here
under Frans's delegation (22:17: "make the decisions needed to get the
2026.4 release ready"; he does not need to review the internal keys'
layout); each such decision gives its reason and is listed in section 11.
No code changed.

Read with: 020-01 (the inventory; its sections 6 to 11 for today's code
and faults, 13 for the fault table, 14.1 for the decisions, 15 for the
harnesses); 020-07 (format 2 of stored objects); 020-08 (the objects'
steps; its step 2 changes files the index steps use); 020-09 (the
conversion rules of a get, which a scan of objects uses for its values,
not for its entries); 018-01, section 2 (the rule on the stream's format).


## 1. In short

* **Shape** (020-01, F3 b): an index has one directory (its own values,
  not its subdirectories'), 1 to 8 levels, one field per level (a name or
  a nested path), each level of type `long`, `double`, `string` (code-point
  order) or `bytes` (unsigned byte order). No ICU, no `createFast()`.
* **An index is a function**: f(object) is one entry or none. A level whose
  field is absent, of another stored kind, or NaN gives no entry; a value
  that is not an object has no entries (015-46). Every entry is checked
  against its object at a scan, so a stale entry never gives a wrong
  result.
* **Stored**: a definition per name, a format-2 object (020-07) at
  `/#i/didef/-<name>`; entries under a directory of the index's
  generation, the name and the creation's time G, so that no index ever
  sees another's entries; a cleanup marker for a deleted generation.
* **Maintenance** (F4 a, b): every put and delete at an object key, of
  any value, deletes f(old) and puts f(new) at the transaction's read
  time, which is fixed before the directory's index set is read; index
  definitions change under the index manager's lock.
* **Jobs** (F5 b): `start()` writes the definition and returns the
  build's `Job`; `start().join()` waits. A deletion is one transaction:
  the name is free when `deleteIndex()` returns; an internal cleanup
  removes the old entries in steps, resumed at a start, with no `Job`. A
  build's status is a snapshot: building with a count, active, or failed
  with a reason. `getStartupJobs()` goes; `Database.indexJob(name)` gives
  an index's job.
* **Reads**: `UseIndexBuilder` is `eq` on a prefix of levels, then at most
  one range (`from`, `to`) or one prefix on the next level, and
  `backward()`; each call is checked at once. `UsePrimaryBuilder` is
  promoted out of the experimental list, `dir()` required.
* **Boundary** (F8 b): the API is `bergdb.pub`, `bergdb.pub.util` and the
  Core's `Db`; `Kv.ikey()` goes; a release jar without `src-dev` and ICU;
  `DbObject` moves into `bergdb.pub` last.
* **Steps**: nine commits (section 10), for up to three agents: A the
  index core (I0, I1, I2), B the primary scan and then the index reads
  (P1, I3), C the boundary and the main harness (B1, H2, B2, B3).
  I1 waits for 020-08's step 2.


## 2. What is decided, and where

| Topic                        | Decided by                       | Here       |
|---|---|---|
| No ICU; code points; `bytes` | Frans, 22:08 and 22:12 (020-01, 14.1)         | 3.3, 4.4 |
| F3 (b), one dir, one field   | Frans, 22:08                                  | 3.1, 3.3 |
| F4 (a) and (b)               | Frans, 22:08                                  | 5        |
| F5 (b)                       | Frans, 22:08                                  | 3.2, 6   |
| F6 (b), F7 (b)               | Frans, 22:08                                  | 3.4, 3.5 |
| F8 (b)                       | Frans, 22:08                                  | 7        |
| N8: no scans in `rw()`       | Frans, 22:08                                  | 3.6      |
| The layout of the keys       | in principle Frans 22:08; exact: here (22:17) | 4        |
| `createFast()` goes          | Frans, 19:43 (020-02, 5.1b)                   | 3.1      |
| No stored null; NaN; −0.0    | Frans, 16:12 to 16:34 (020-02, 4.1, 4.8)      | 3.3      |
| One integer type             | Frans, 16:25 (020-02, 4.7)                    | 3.3      |
| Every other gap              | this item, under the delegation (22:17)       | 11       |


## 3. The API

Signatures as they are to be in `bergdb.pub` and `bergdb.pub.util`. The
Javadoc of each method says what is written here; the class Javadoc of
`IndexBuilder` holds the definition of the index function (3.3). The
"Experimental in 2026.3" paragraphs go from every class below.

### 3.1. `IndexBuilder`

```java
public interface IndexBuilder {
    /** The directory whose values are indexed, such as "/persons/": its own values,
     *  not its subdirectories'. Called once, before type().
     *  @throws IllegalArgumentException  dir invalid (PubKeys.udir2idir's rules)
     *  @throws IllegalStateException     dir() called before */
    IndexBuilder dir(String dir);

    /** Starts the next level, of type "long", "double", "string" or "bytes".
     *  At most 8 levels. @throws IllegalArgumentException another type string
     *  @throws IllegalStateException  no dir() yet; the level before has no field;
     *          8 levels already */
    IndexBuilder type(String type);

    /** The level's field: a top-level field name, as one part (a '.' in it is part
     *  of the name). Once per level, after type().
     *  @throws IllegalArgumentException  null, empty, more than 255 UTF-8 bytes, or a
     *          lone surrogate
     *  @throws IllegalStateException     no type() yet, or the level has its field */
    IndexBuilder field(String name);

    /** The level's field as a nested path: "car.size.length" split at '.', each
     *  part a name as for field(); 1 to 16 parts; no empty part (S2-F15). */
    IndexBuilder nestedField(String path);

    /** As nestedField(String), with the parts given; a part may hold '.'. */
    IndexBuilder nestedField(String[] parts);

    /** Creates the index: writes its definition, in state building, in one
     *  transaction, and starts its build in a background thread. From its return,
     *  every write of the directory keeps the index (section 5). Returns the build's
     *  job; start().join() waits until the index is active (at once for an empty
     *  directory: the use of the removed createFast()).
     *  @throws IllegalStateException       no dir(), no level, a level without field,
     *          or start() called before
     *  @throws IndexAlreadyExistsException an index of the name exists (building or
     *          active) */
    Job start();
}
```

* `Database.indexBuilder(String name)`: the name is 1 to 255 UTF-8 bytes,
  without `/`, whitespace (`Character.isWhitespace`) or a lone surrogate
  (`IllegalArgumentException`, at once). The name's existence is checked
  at `start()`, not here (today it is checked at both; the check here was
  a race anyway).
* Every call is checked at once, in the order given; the builder is spent
  after `start()`, whatever it threw.
* Removed: `createFast()`, `dir()` twice (S2-F20), several fields at a
  level, the type strings `string/unicode` and `string/<language>`, the
  field name rules "no space, no comma" (they served the stored commas,
  S2-F14), `IndexBuilderImp.bunchSize()` from the API's reach (section 7).

### 3.2. Jobs, status and deletion

```java
package bergdb.pub.util;

/** The build of an index, in this process. */
public interface Job {
    /** A snapshot: immutable, all its values taken at the call (015-39); it
     *  never throws, also for a FAILED build. */
    JobStatus getStatus();
    /** Waits until the build ends in this process: the status is then ACTIVE,
     *  or BUILDING if the database stopped (the next start resumes it). A FAILED
     *  build throws IndexBuildException, at every call (Frans, 2026-11-09).
     *  An interrupt ends the wait and keeps the flag (005-46). */
    JobStatus join();
    /** As join(), at most millis ms; 0 waits as join(). */
    JobStatus join(int millis);
}

/** Thrown by join() and join(millis) of a FAILED build: unchecked, not a
 *  DbException. The message names the index and the reason. */
public class IndexBuildException extends RuntimeException {
    /** The job's last status, FAILED. The cause is the exception that failed
     *  the build, null for "deleted". */
    public JobStatus getStatus();
}

public interface JobStatus {
    enum State { BUILDING, ACTIVE, FAILED }
    State state();
    /** The values of the directory the build has read, in this process. */
    long count();
    /** FAILED: why, in English, with the cause's class and message; else null. */
    String reason();
    /** One English line made from the three above. */
    String note();
}
```

* `progress()` goes: its −1, 0 to 99 and 100 meant several things
  (015-61, S2-F11, 019-40 C5).
* **FAILED**: the build met an exception that is neither a stop of the
  database nor a refusal or expiry (which it retries, 019-38), such as a
  BergDB bug or a format-1 object (020-08, step 3); or the index was
  deleted while it was building (reason "deleted"). A failure is kept in
  memory only: the definition stays building, and the next start takes
  the build again (019-42's rule). The database goes on; only an `Error`
  fails it (P7).
* **`join()` of a FAILED build throws** (Frans, 2026-11-09, 08:29: "Do as
  you propose"): `join()` and `join(millis)` throw `IndexBuildException`
  (`bergdb.pub.util`, unchecked) at every call, also on the job of
  `Database.indexJob(name)`, as `Future.get()` and
  `CompletableFuture.join()` throw for work that failed. Its `getStatus()`
  is the FAILED status, and its cause the exception that failed the build:
  a `DataFormatException` or an `InternalDataException` (data the build
  cannot take, such as a format-1 object), another `RuntimeException` (a
  bug), none for "deleted"; the job keeps that exception, and the reason
  string is as before. They return ACTIVE, or BUILDING after a stop, a
  time-out or an interrupt; `getStatus()` never throws and is the way to
  poll. Why: the natural `start().join()`, the Javadoc's example, passed a
  failed build silently. Not a `DbException`: that is a refusal, which a
  caller may make again, or a failure of the database (`DbException`'s
  Javadoc), and a failed build is neither; a loop that retries on
  `DbException` would call a `join()` that throws for ever.
* `Database`:
  ```java
  IndexBuilder indexBuilder(String name);
  /** Deletes the index in one transaction: when this returns, the index is gone
   *  at every later lookup time and its name is free; its entries are removed in
   *  the background. @throws NoSuchIndexException no index of the name */
  void deleteIndex(String name);
  /** The job of the index's build in this process: the one start() returned, or
   *  the one a start resumed; for an index that was active at the start, a job
   *  whose status is ACTIVE with count 0, which join() returns at once.
   *  @throws NoSuchIndexException no index of the name now */
  Job indexJob(String name);
  ```
* `Database.PRIMARY` goes: the primary scan is not an index (3.5), and
  "primary" is a name like any other (015-29 goes with it).
* `StartupInfo.getStartupJobs()` goes; `indexJob(name)` replaces it.
* A deletion and a creation are each one transaction, refused or done:
  a refusal throws the Core's `DbException` to the caller and changes
  nothing, in the stream or in memory (015-23, S2-F27).

### 3.3. The index function

The index I has the directory d, levels 1 to n, and for each level i a
type t_i and a path p_i (1 to 16 names). For a value v at a key k of d:

1. If k has a suffix (it is not an object key, `Entries.isObjectKey`), or
   v is not a stored object of format 2 (header `0x82` and 020-07's full
   check), v has **no entry**. Bytes that start with `0x82` but fail the
   check are not an object (020-08, section 3). An object of format 1 is
   refused (020-08, step 3): a build fails, a write is refused (6.1, 5).
2. For each level i: follow p_i in the stored `DbObject` (not a converted
   Data Object: 020-09's rules play no part here). Each part but the last
   must name a field that holds an object. The value found must be of the
   level's stored kind:

   | Type     | Accepted stored kind (020-07, section 3) | No entry for         |
   |---|---|---|
   | `long`   | integer (any width, 0x10 to 0x13)        | every other kind     |
   | `double` | double (0x46)                            | NaN; every other kind |
   | `string` | string (0x14 to 0x16)                    | every other kind     |
   | `bytes`  | bytes (0x18 to 0x1a)                     | every other kind     |

   No kind is converted to another: an integer gives no entry in a
   `double` level, a double none in a `long` level, a string none in a
   `bytes` level. Booleans, arrays and objects give no entry at any
   level. An absent field (no stored null exists, 020-02, 4.1), or a path
   through a field that is absent or not an object, gives no entry.
3. Each level's value is encoded as section 4.4 says, L_i. If the levels
   take more than 4,096 bytes in all, v has no entry. Else f(v) is the one
   entry L_1 ‖ ... ‖ L_n.

So each value has zero or one entry per index. Java's `int`, `long`,
`short`, `byte` and `char` fields are integers (one integer type, 020-02,
4.7) and go in a `long` level; `float` and `double` fields are doubles;
`String` fields are strings; `byte[]` fields are bytes. The double −0.0 is
indexed as 0.0 (one key, as IEEE 754's `==` and today), while the object
keeps −0.0. The Javadoc of `IndexBuilder` states this section as the
promise; an application that needs a language's order stores its own
collation key (`java.text.Collator.getCollationKey(s).toByteArray()`) in
a `byte[]` field and indexes it as `bytes` (020-01, 14.1).

### 3.4. `UseIndexBuilder`

```java
public interface UseIndexBuilder<T> {
    /** Equality on the next level: level 1 first, then 2, and so on. The argument's
     *  Java type must match the level's type: eq(long) for long, eq(double) for
     *  double, eq(String) for string, eq(byte[]) for bytes. */
    UseIndexBuilder<T> eq(long value);
    UseIndexBuilder<T> eq(double value);
    UseIndexBuilder<T> eq(String value);
    UseIndexBuilder<T> eq(byte[] value);

    /** The lower bound on the level after the eq() levels. */
    UseIndexBuilder<T> from(long value, boolean inclusive);
    UseIndexBuilder<T> from(double value, boolean inclusive);
    UseIndexBuilder<T> from(String value, boolean inclusive);
    UseIndexBuilder<T> from(byte[] value, boolean inclusive);

    /** The upper bound on the same level as from(). */
    UseIndexBuilder<T> to(long value, boolean inclusive);
    UseIndexBuilder<T> to(double value, boolean inclusive);
    UseIndexBuilder<T> to(String value, boolean inclusive);
    UseIndexBuilder<T> to(byte[] value, boolean inclusive);

    /** The values of that level that start with prefix: a string level by code
     *  points, a bytes level by bytes. */
    UseIndexBuilder<T> prefix(String prefix);
    UseIndexBuilder<T> prefix(byte[] prefix);

    /** Descending order; ascending by default. */
    UseIndexBuilder<T> backward();

    Iterable<T> objects();
    Iterable<Kv<T>> kvs();
}
```

* **The grammar**: `eq*` on levels 1 to k (k < n for a bound or a prefix,
  k ≤ n for eq alone), then at most one `from` and one `to`, or one
  `prefix`, on level k + 1; `backward()` anywhere before `objects()` or
  `kvs()`. Each call is checked at once: a call out of the grammar, a
  second `from`, `to`, `prefix` or `backward`, an `eq` after a bound, a
  level past n: `IllegalStateException`; a type that does not match the
  level, a null, NaN, a `String` with a lone surrogate:
  `IllegalArgumentException`. After `objects()` or `kvs()` every builder
  call is `IllegalStateException`; `objects()` and `kvs()` may be called
  again, and each iterator starts from the beginning at the same lookup
  time.
* `from` above `to` in the index's order gives an empty scan, not an
  exception (it is data, not a misuse). −0.0 as an argument is 0.0.
* Removed: `inclusive()` (S2-F2), `nextLevel()`, `startAt()` (S2-F22,
  S2-F13).
* **The scan's meaning**, which is the reference of harness H2 (9.1): at
  the scan's lookup time T, the entries of the index whose levels 1 to k
  equal the `eq` values and whose level k + 1 meets the bound or prefix,
  in the order of (L_1, ..., L_n, key), ascending or descending. For each,
  the value at its key at T is read; if it is not an object, or f(value)
  is not the entry's levels, the entry is skipped (a stale entry gives no
  result); else the value is returned, converted to T by 020-09's rules
  (a conversion that throws throws from `next()`). `hasNext()` looks
  ahead past skipped entries, so it never says true before a `next()`
  that throws `NoSuchElementException` (S2-F23).
* `Kv<T>.key()` is the user's key; `value()` the converted value.

### 3.5. `UsePrimaryBuilder`

Promoted: not experimental; part of the Pub API that 2026.4 promises for
every kind of value. Its method names stay, so its callers (PayTest,
CcDbNightTest, BryanRepro, the demos) do not change.

```java
public interface UsePrimaryBuilder<T> {
    /** The directory to list, its own keys only; the first call, required.
     *  @throws IllegalArgumentException dir invalid; IllegalStateException called
     *          before */
    UsePrimaryBuilder<T> dir(String dir);
    /** The first key to list: its name in the directory (no '/'); inclusive by
     *  default. @throws IllegalStateException no dir() yet, or called before */
    UsePrimaryBuilder<T> startAt(String name);
    /** Whether a key equal to startAt's is listed; default true. */
    UsePrimaryBuilder<T> inclusive(boolean inclusive);
    UsePrimaryBuilder<T> backward();
    /** @throws IllegalStateException no dir() (S2-F17) */
    Iterable<T> objects();
    Iterable<Kv<T>> kvs();
}
```

* **What it lists**: at the lookup time T, the keys of the directory's
  own values (not its subdirectories', never an internal key) in key
  order, ascending or descending, from `startAt` if given; for each, the
  value converted to T, and the keys whose value is not of T's kind are
  skipped:

  | T                          | Listed                                              |
  |---|---|
  | `byte[].class`             | every value, its stored bytes                       |
  | `Object.class`             | every value, as `get(key, Object.class)` gives it   |
  | `String.class`             | every value that is not an object, decoded as by `get` |
  | `DbObject.class`, a class C | the objects, as `get(key, C)` gives them (020-09)  |

  So `usePrimary(String.class)` no longer gives an object's bytes as text
  (S2-F25). An object is a value with format 2's header that passes the
  full check (020-08, section 3).
* Its reference is harness 6.7's (018-04): each key's versions by time
  (H4, 9.3).

### 3.6. Reads and the connection

* `Connection.useIndex(name, T)` reads the index's definition at the
  connection's lookup time, resolved to an actual time t at the call; the
  definition must exist and be active at t, else `NoSuchIndexException`
  ("no index of the name at the lookup time", or "the index is building
  at the lookup time"). Every iterator of the builder reads its entries
  and values at t. `usePrimary` takes t the same way.
* Both count as reads for `freezeLookupTime()`: the first read after it
  fixes the frozen time, whether a `get()`, an `exists()`, a `useIndex()`
  or a `usePrimary()` (as `setLookupTime`'s Javadoc lists them). Neither
  changes `transactionInfo()`, which describes `get()` and `exists()`
  only (N3): the definition, the entries and the values are read with
  `Db` directly, not through the connection's `GetData`.
* A scan whose t falls behind reclaim's cut while it runs throws
  `LookupTimeNotAvailableException` from `hasNext()` or `next()`; this is
  promised in the Javadoc of both builders.
* At a past t, a scan of an index that was active at t works, also when
  the index was deleted since: its generation's entries are still there
  at t (the cleanup deletes them at later times), until reclaim's cut.
* No scan in `rw()` in 2026.4 (N8, decided); `RwEnvironment` is unchanged.


## 4. The stored layout

The reserved internal keys are part of the stream's format (018-01,
section 2). Frans approved the new layout in principle (22:08) and
delegated its details (22:17); this section is the layout, and the
Javadoc of `IndexManager` cites it (bergdb 020-10, section 4).

### 4.1. The keys

All are ikeys under `/#i/` (key-encoding.md's IKP), made bkeys by its rule
(each byte + 2, `/` as 1); G is the index's generation (4.3).

| Key | Value | Written by |
|---|---|---|
| `/#i/didef/-<name>`                          | the definition (4.2) | create, activate, delete |
| bkey(`/#i/dient/d<name>/`) ‖ G8 ‖ levels ‖ K | empty                | writers, builds, cleanup |
| `/#i/didel/d<name>/-<G16>`                   | empty                | delete, cleanup          |
| `/#i/div/<idir>`, virtual: a hash only       | nothing stored       | create, delete           |

* G8 is G as 8 bytes, big-endian; G16 is G as 16 lowercase hexadecimal
  digits. K is the bkey of the value's ikey after its directory's idir:
  the file part, `-<name>` (first byte `0x2f`), with no byte below 2.
* The old keys: `/#i/dii/` (definitions of format 1) and `/#i/di/` (their
  entries). A start that finds a key under `/#i/dii/` refuses the
  database with 020-08, section 5's message for format 1 (its step 3).
  `/#i/di/` is never read or written.

### 4.2. The definition

A stored object of format 2 (020-07), written with `DbObject.Builder` (or
`ObjectFormat`'s writer) field by field and read with `new DbObject(bytes)`
and its getters: no reflection, no `Data.Index` (which goes). Exactly
these fields, no other:

| Field     | Stored kind          | Value                                                  |
|---|---|---|
| `version` | integer                 | 1                                                       |
| `dir`     | string                  | the directory as the user gave it, such as `/p/q/`      |
| `gen`     | integer                 | G, > 0                                                  |
| `state`   | string                  | `building` or `active`                                  |
| `levels`  | array of 1 to 8 objects | each exactly {`type`: string, `path`: array of strings} |

`type` is `long`, `double`, `string` or `bytes`; `path` has 1 to 16
strings, each a name of 1 to 255 bytes (020-07's names). The index's
name is not stored in the object: it is its key's.

A reader (a start, `useIndex`) makes 020-07's full check and then checks
every row of the table, the name from the key (3.1's rule) and `dir` by
`PubKeys.udir2idir`; any failure is an `InternalDataException` that names
the key and the rule broken. At a start that refuses the database (the
stream's internal data is bad); at `useIndex` it is thrown to the caller.
The definition is a conformance vector of 020-07's file
(`index-definition-2`), added by step I0.

### 4.3. The generation

G is the creation's time: the time of the latest transaction when the
creation runs, which it reads under the index manager's lock (5.2), as a
read at `Long.MAX_VALUE` resolves it. G differs for every creation of one
name: a creation B of a name that an index A had commits after A's
deletion D, under the same lock, so G_B ≥ t_D > t_A > G_A (t: the
transaction's time). Two names may share a G; the entries' key holds
both. No index ever reads or writes another generation's entries, so a
late writer or build of a deleted index cannot reach a new index of the
name (S2-F12, S2-F27, R3-F1 and F2's family).

### 4.4. The level encodings

Each makes a byte string whose unsigned lexicographic order is the
values' order, and which no other level's string is a proper prefix of
(so the levels, then K, sort as tuples):

* **long**: 8 bytes, big-endian, of v + 2^63 (v XOR `0x8000000000000000`),
  as today (`IndexEntryBuilder.sortBytesFromLong`).
* **double**: NaN gives no entry (3.3). Else as today
  (`sortBytesFromDouble`): x = `Double.doubleToLongBits(v)`; s = x if
  x ≥ 0, else −(x AND `0x7fffffffffffffff`); then s as a long. So −0.0
  and 0.0 are one key, −∞ the least, +∞ the greatest.
* **string** and **bytes**, one encoding E over the bytes (a string's are
  its UTF-8, well-formed by 020-07): each byte `00` written `01 01`, each
  `01` written `01 02`, every other byte as it is; then `00`. A string's
  order is then its code points' (UTF-8 keeps it), a bytes value's its
  unsigned bytes', a prefix's (E without the final `00`) a prefix of the
  values that start with it, and `"a"` sorts before `"a\u0000"`. Today's
  string encoding (each byte + 2) goes: one encoding for both types.
* An entry is parsed from its start: the prefix of its generation, then
  each level by its type (8 bytes; or up to the `00` that ends E, every
  `01` followed by `01` or `02`), then K (non-empty, first byte `0x2f`,
  no byte below 2). A key that does not parse is an
  `InternalDataException` naming it.
* The scan's range (3.4): with base = the generation's prefix ‖ L(eq_1)
  ‖ ... ‖ L(eq_k) and succ(x) the least string above every string that
  starts with x: no bound, [base, succ(base)); `from(v, true)` starts at
  base ‖ L(v), `from(v, false)` at succ(base ‖ L(v)); `to(v, true)` ends
  before succ(base ‖ L(v)), `to(v, false)` before base ‖ L(v); `prefix(p)`
  is [base ‖ E'(p), succ(base ‖ E'(p))), E' being E without its `00`.

### 4.5. What a start reads and checks

In `DatabaseImp.createAndStart`, after `Db.start()`, before it returns:

1. Any key under `/#i/dii/`: refuse (format 1, 4.1).
2. Every definition under `/#i/didef/`, read with `Db.getMany` at the
   start's time (not `usePrimary`): checked (4.2), then held in memory.
3. Every marker under `/#i/didel/`: its name and G parsed; a marker
   whose (name, G) is a live definition's is an `InternalDataException`.
   Each starts a cleanup (6.2).
4. Every definition in state `building` starts a build from the first key
   of its directory (6.1); `indexJob(name)` returns its job.

A start reads no entry and no user value. Its cost is one prefix scan of
the definitions and one of the markers, both small.


## 5. Maintenance (F4 a and b)

### 5.1. The rule

A transaction (an `rw()` or a `w()`) that leaves, at an object key k of a
directory d, a new value or no value, and commits at the read time R:

1. **R is fixed first.** If the transaction has read nothing yet, R is
   taken now, as a read at `Long.MAX_VALUE` resolves it (the latest
   transaction's time), before anything below. S1-F4's fix: today the
   index set is read before R exists (015-28, 015-43, S2-F12).
2. The hash of `/#i/div/<idir of d>` goes into the read set, whether d has
   an index or not. A creation or deletion of an index of d writes it, so
   a transaction that read the set before that commit runs again (015-28).
3. **The index set** S of d (building and active indexes) is read from
   the manager, under its lock, after step 1.
4. If S is empty, nothing more. Else the previous value at k is read at R
   (its key's hash in the read set), and for each index I of S: the
   entries f_I(old) are deleted, and f_I(new) is put; an entry both
   deleted and put stays (015-40). "Old" and "new" are any values: one that
   is not an object has no entries (3.3, rule 1), so a `String` or a
   `byte[]` put over an object deletes its entries, and an object put over
   a `String` deletes none (015-46). A previous value in format 1 has no
   entries, as no index of 2026.4 indexed one, so a put over it and a
   delete of it work; a new value in format 1, of a `byte[]` put, refuses
   the transaction with `DataFormatException` naming the key (020-08,
   step 3; since 2026-11-09, after the review of `e92a95a`, decided under
   Frans's delegation: the previous value refused it too, so such a key
   could not be written or deleted while the index existed, also after a
   build that failed over it).
5. The writer does not put the definition's key in its read set (today it
   does): the activation of an index does not change S, and so does not
   make writers run again. A build step does read it (6.1).

Several calls on one key in one transaction: the last wins (015-41); the
rule sees only the value the transaction leaves.

**Which writes**: every put and delete at an object key (no suffix, or
`.obj`), whatever the value: an object, a `String`, a `byte[]`, a
`DbObject`. Today a `String` or `byte[]` put is not an object op, which
is 015-46's cause. A put or delete at a key with a suffix never touches an
index (such a value is never an object). So a `w()` whose puts or deletes
include an object key goes through `RwTransaction.executeRw` (today: only
if it has object puts), carries R and step 2's hash, and may run again
after a conflict, which only an index definition of that directory, or
(in an indexed directory) a concurrent write of the same key, can cause.

### 5.2. The index manager's lock

The invariant: **a transaction whose read time R is at or after the time
of an index definition's change sees that change in the set it reads at
step 3.** It holds by one rule on each side:

* A definition change (creation, activation, deletion) takes the
  manager's lock, reads G or checks the name, executes its one
  transaction, and only when that succeeded changes the in-memory maps;
  then releases the lock. A refused transaction leaves memory as it was
  (015-23, S2-F27).
* A writer reads S under the same lock, after R is fixed (5.1, step 1).

If the writer reads S before the change took the lock, the change's time
is after R, and step 2's hash makes the writer run again. If after, S has
the change. A change that commits after R while the writer computed its
entries with the old S also makes it run again (step 2). The lock is held
by a writer for one map lookup; an implementation may replace it by a
sequence counter that gives the same invariant, with a test that forces
each order (9.2).

### 5.3. Key replace

With key replace (`${transactionTime}`), K is the replaced name, as the
value's key. The entry's `KeyTransformation` replaces only within K:
today's replaces anywhere in the entry's key, so an indexed `String` that
holds `${transactionTime}` had its level bytes replaced (N11, new, from
the code: `RwEnvironmentImp.replaceTransformation` with
`UnicodeCollator`'s bytes, which are the key's encoding). Fixed by step I2.

The directory and the previous value (the Codex review's X1, 020-14;
2026-11-09, decided under the delegation, for Frans to confirm): the key
is replaced at the commit, when its time is known, after steps 1 to 4.
So a put at an object key with `${transactionTime}` in its directory is
refused with `IllegalArgumentException` at the call: the directory it
lands in, and so its index set, is not known at step 3 (until then the
directory as written was used). In the name, the put lands at a key whose
name holds its commit's time, after R: step 4 takes no previous value,
where it read the key as written, another key, and deleted that object's
entries. A key written as it is, whose name holds a later time's digits,
is not looked for: if a replaced put lands on it, its old entry stays,
and a scan, which gives only the values that their entries still match,
leaves it out (3.4). The alternative, kept for Frans: allow the directory,
with each change of an index definition writing one more hash that such a
put reads, and refuse the put only when an index's directory matches the
key with 18 digits in place of `${transactionTime}`.


## 6. Jobs (F5 b)

### 6.1. The build

* One daemon thread of the lowest priority per building index in this
  process, started by `start()` or by a start (4.5), on its own
  connection.
* **A step** is an `rw()`: a `getMany` of at most 25 values of the
  directory's own keys (the prefix idir ‖ `-`, so it stops at the
  directory's end: 015-30, S2-F16) after the last key of the step before;
  the definition's key hash added to the read set; if the in-memory index
  of this generation is no longer building (deleted), the build ends
  FAILED "deleted"; else f(v) is put for each value read (3.3; a value
  with no entry is counted and skipped: a user's value never stops a
  build, N1). The values' hashes are in the read set, so a concurrent
  write of one makes the step run again.
* The status's count is the values read by the committed steps.
* After a step, a pause of half its time, at most one second (N10: today
  the cap is computed and not used).
* **The end**: the activation, one transaction under the lock (5.2):
  the definition rewritten with state `active`, with its key's hash in the
  read set; a conflict takes it again. Then the status is ACTIVE.
* **Errors**: a stop of the database (`DbStoppingException`,
  `IllegalDbStateException`, `StreamIoException`, `DbFailedException`)
  ends the thread, status BUILDING; a refusal (`DbException`) or an
  expiry (`LookupTimeNotAvailableException`) waits 10 to 640 ms and takes
  the step again (019-38); any other `RuntimeException` ends the build
  FAILED with it as the reason, the database going on (019-42); an
  `Error` fails the database (019-10, P7). A step can no longer be too
  large to commit: 25 entries of at most 4,096 bytes of levels are far
  below the transaction's limit (N7); a database that refuses every
  transaction (005-02's ordinals) makes the build wait, as every writer.
* A start resumes a build from the first key of its directory (entries
  are idempotent). A long build is redone at each restart: accepted for
  2026.4 (020-01, 8.5.7), as builds are rare and a start does not wait
  for them.

### 6.2. The deletion and the cleanup

* **`deleteIndex(name)`**: under the lock, the index of the name in
  memory (else `NoSuchIndexException`); one transaction at the latest time:
  delete `/#i/didef/-<name>`, put the marker `/#i/didel/d<name>/-<G16>`,
  write the hash of `/#i/div/<idir>`, with the definition's key hash in the
  read set. When it succeeded: the index out of the maps, its in-memory
  state deleted (its build ends at its next step), and the cleanup of
  (name, G) started. No `sync()`, no thread to wait for, no state
  `deleting` anywhere (015-36, 015-61, S2-F11).
* **The cleanup** of (name, G): a daemon thread, steps of a `getMany` of up
  to 100 keys under the generation's prefix at the latest time and one
  transaction that deletes them (no read set: no one writes a deleted
  generation, by 5.2 and 6.1); a pause as a build's; when a step finds
  none, one transaction deletes the marker, and the thread ends. Errors as
  a build's, but a `RuntimeException` ends the thread silently (the
  marker stays, the next start resumes it). No `Job`, no status.
* A deleted index's entries are garbage until their cleanup; they are in
  a generation no definition names, so nothing reads them.


## 7. The boundary (F8 b)

* **The API, named** in the Javadoc overview (`overview-pub.html`),
  `bergdb.pub`'s `package.html`, and the README: the packages `bergdb.pub`
  and `bergdb.pub.util`, and the Core API as 018-01 names it (`Db` and the
  types of its signatures). Everything else, `bergdb.pubimp` included, is
  not API, whatever is public in it.
* **`Kv.ikey()` goes**, with its implementations (`UseIndexBuilderImp`,
  `UsePrimaryBuilderImp`, `ConnectionImp.transactionInfo`'s, and the Core's
  `TransactionInfo` KVs if they implement `Kv`), and the one internal use
  (`IndexManager.initFromDatabase`, rewritten by I2).
* **`pubimp` narrowed**: every public method or class of `pubimp` that no
  other package uses (by `grep` over `src`, `src-dev`, `stress`) loses
  `public`: `IndexManager` and its methods, `IndexBuilderImp`'s
  internals, `UsePrimaryBuilderImp.dirInternal()` (gone),
  `WTransaction.getTrans()`, the definition and key classes of I0. A
  method that `src-dev` or `stress` uses stays public, with a Javadoc
  line "internal, not API". `ConnectionImp.getDb()` and
  `DatabaseImp.getDb()` stay public if the tests or tools use them.
* **The release jar**: `build.sh` makes, besides `build/bergdb.jar` (all
  of `src` and `src-dev`, for the tests and every script, as today),
  `build/bergdb-release.jar`: the classes and resources of `src` only, no
  `Main-Class`, no ICU; and it fails if that jar holds an entry under
  `bergdb/dev/`, `bergdb/test/`, `bergdb/demo/`, `frans/` or
  `bergdb/icu50/`. The release (`releases/2026.4/`) ships the release jar.
* **ICU gone**: `src-icu/` (`bergdb.pubimpicu`), `in/icu-for-bergdb.jar`,
  `in/ICU-LICENSE.html`, `OptionalIcuCollatorFactory`, `IcuInfo` (and its
  use in `src-dev/bergdb/dev/Info.java`), `BergCollatorFactory`,
  `CollatorFactory`, `KCollator`, `UnicodeCollator`, `PrimaryKeyCollator`;
  `build.sh`'s `-cp $ICU` and its `unzip`. The jar loses about 2.0 MB
  (020-01, section 6.2).
* **`DbObject` into `bergdb.pub`**, with the classes its public signatures
  name (`DbArray`, `DbValue`, as the objects' API leaves them); the codec
  and the value classes stay in `pubimp`. Last, after the objects' steps
  of 020-08 that change `DbObject`'s API.
* `Job` and `JobStatus` stay in `pub.util` (3.2); `DataFormatException`
  stays in `pub`.


## 8. The fault map

Every open fault of 020-01's section 13, second table, for F3 to F8, and
the findings that touch indexes. "Gone" means the design has no place for
the fault; the test still shows its scenario gives the right result. The
step is where the fix and the test land (section 10).

**F3, definition**

| Fault | What; how the design removes or fixes it | Test; step |
|---|---|---|
| S2-F1  | ICU collator shared by threads: no ICU (7) | H2 with 4 writer threads; I2   |
| S2-F10 | no start without ICU: no ICU               | release jar's check; B1, B2    |
| S2-F14 | a level's commas lost: one field; `path`   | definition round trip; I0, I2  |
| S2-F15 | empty nested part: refused at the call     | `testNestedFieldEmptyPart`; I2 |
| S2-F20 | a directory twice: one `dir()`             | `testDirTwice`; I2             |
| S2-F26 | null `String` throws: absent, no entry     | H2, absent fields; I2          |
| N9     | ICU's keys in the stream: no ICU           | gone; I2                       |

**F4, maintenance**

| Fault | What; how the design removes or fixes it | Test; step |
|---|---|---|
| 015-28 | write racing a creation: R first, vhash  | `testRacesCreate`; I1                |
| 015-43 | set read before R: R first, lock (5.2)   | `testRacesCreate`, `Activate`, `Delete`; I1 |
| S2-F12 | old entry in a new index: generations    | `testRacesDelete`, H2; I1, I2        |
| 015-46 | `String` over an object: all writes kept | `testStringOverObject`, H2; I1       |
| S2-F26 | as in F3                                 | as in F3                             |

**F5, jobs**

| Fault | What; how the design removes or fixes it | Test; step |
|---|---|---|
| 015-23    | refused deletion: one transaction        | `testDeletionRefused` (H3); I2          |
| 015-29    | `deleteIndex(PRIMARY)`: `PRIMARY` gone   | `testIndexNamedPrimary`; I2, I3         |
| 015-30    | build reads past its dir: prefix         | `testBuildStopsAtDir`; I2               |
| 015-36    | interrupted deletion: no deleting state  | `testDeleteWithInterruptFlag`; I2       |
| 015-37    | interrupt ended a build: 019-38 (N6)     | `testInterruptInBuildIsNotAFailure`; I2 |
| 015-39    | kept status changes: a snapshot          | `testStatusIsSnapshot`; I2              |
| 015-61    | stopped deletion says done: no job       | gone; I2                                |
| S2-F11    | done when the DB stopped: BUILDING       | `testStopDuringBuild` (H3); I2          |
| S2-F16    | build indexes subdirectories: own keys   | `testSubdirNotIndexed`, H2; I2          |
| S2-F26    | as in F3; a build is never stopped       | H3; I2                                  |
| S2-F27    | refused creation in memory: lock (5.2)   | `testCreationRefused` (H3); I2          |
| 019-40 C5 | deletion done after a failure: no job    | gone; I2                                |
| N1        | null `String` fails each start: no entry | H3, 019-42's test; I2                   |
| N7        | step refused for good: levels ≤ 4,096 B  | `testLargeValueNoEntry`; I2             |
| N10       | pause without cap: cap applied           | `testPauseCapped`; I2                   |

**F6, reads**

| Fault | What; how the design removes or fixes it | Test; step |
|---|---|---|
| S2-F2  | `inclusive(false)` alone: in `from`, `to` | H2, exclusive bounds; I3           |
| S2-F13 | `prefix()` on a secondary index: E'       | H2, prefixes; I3                   |
| S2-F22 | later level alone: the grammar's checks   | `testGrammar`, H2; I3              |
| S2-F23 | `hasNext` true, `next` throws: look-ahead | `testStaleLastEntries`; I3         |
| N3     | `transactionInfo` changed: `Db` reads     | `testScanKeepsTransactionInfo`; I3 |

**F7, F8 and new**

| Fault | What; how the design removes or fixes it | Test; step |
|---|---|---|
| S2-F17 | no `dir()`, internal keys: `dir` first | `testPrimaryNeedsDir`, H4; P1     |
| S2-F25 | `String.class` gives objects: by kind  | H4, mixed kinds; P1               |
| 015-29 | as in F5                               | as in F5                          |
| N5     | the boundary a convention: section 7   | jar check, javadoc-pub.sh; B1, B2 |
| N11    | key replace in level bytes: K only     | `testKeyReplaceIndexedText`; I2   |

The race tests are `PubTesterIndexRaces.testRacesCreate`,
`testRacesActivate` and `testRacesDelete` (section 9.2: a write at each
point of each change, 36 forced orders); this table named them
`testRaceWriteCreate` and `testRaceSetBeforeReadTime` until 2026-11-09
(020-11). `testRaceDeleteRecreate` exists too, a sequential case.

Also touching indexes, and settled: N2 (an `Error` from the user's data
in `rw()`): the index path's case was S2-F26's assertion, gone with the
no-entry rule and 019-42's `IllegalArgumentException`; the get's cases
are 020-09's. N4 (the kind not stored): a build, a writer and a scan take
a value as an object by format 2's header and full check (3.3), and a
`byte[]` that passes that check is an object: a documented guess (020-08,
section 3; the Javadoc of `IndexBuilder` says it). N6: 015-37 is closed by
step I2's commit message with the test named above. N8: decided, no scans
in `rw()`.

"No known issues" in the morning means: each row above has its test in
`before-commit.sh` passing, or is "gone" with its code removed.


## 9. The harnesses

Each against a simple reference in the test, as 018's harnesses (018-02
to 018-08): the reference is written apart from the code (it compares
Java values, not encoded bytes), and each harness has a seed, a size for
`before-commit.sh` (unit group, a few seconds) and a larger run in the
Nano group `night` (`bergdb.dev.Night`), each `@Nano("night")`.

### 9.1. H2: an index is a function of the data (F3, F4, F6)

* **Model**: per key of two directories (`/h/a/`, `/h/a/sub/`), the
  versions by time: a Java map of field values (integers, doubles with
  −0.0, NaN and ±∞, strings with `\u0000`, `\u0001`, astral characters,
  bytes with `00`, `01`, `ff`; fields absent; a nested object or not), or
  a `String`, or a `byte[]`, or no value.
* **Operations**, random by the seed: puts of objects, `String`s and
  `byte[]`s at object keys, deletes, in `w()` and `rw()`, several per
  transaction; index creations (1 to 3 levels, all four types, nested
  paths), `start().join()` or not; deletions; a creation of a used name;
  restarts (I2 on); reclaim on, with a short retain duration.
* **Reference f**: from the model's Java values by 3.3's table
  (`Long.compare`; `Double.compare` with −0.0 as 0.0, NaN none; strings by
  code points; bytes unsigned), and the scan's reference: the sorted list
  of (levels, key) over the model at t, filtered by 3.4's grammar.
* **Checks**, after each step and at 5 random past lookup times: every
  active index, with every `eq` prefix of a random object's values, a
  random bound pair (each inclusive or not), a random prefix, both
  directions: `kvs()` equals the reference, key by key and value by value;
  a building or absent index is `NoSuchIndexException`; and the raw
  entries of each generation at t (a package-private method of
  `IndexManager`, for tests) equal f over the model exactly (so a stale
  entry that the scan's check would hide still fails the harness).
* **Size**: unit, 4 seeds × 400 operations, at most 3 s; night, 40 seeds ×
  5,000 operations with restarts every 500 and 4 writer threads. `main`
  repeats one seed. File `IndexHarness.java` (new).
* **Its own check**: three faults planted one at a time (an entry not
  deleted, a bound off by one, −0.0 apart from 0.0) are each found.

### 9.2. The races (F4)

Deterministic tests with hooks, as S1's and S2's probes did, in
`PubTesterIndexRaces.java` (new), at most 1 s in all: a hook in
`RwEnvironmentImp` after R is fixed and after S is read, and one in the
manager before and after a definition's commit. For each of creation,
activation and deletion, and each of the four points, a write of an
object, a `String` and a delete runs there; then the raw entries equal f
over the values at the latest time. Covers 015-28, 015-43, S2-F12 and the
lock rule's two orders.

### 9.3. H3: jobs under faults (F5)

As harness 6.2 (018-03): a build of 60 objects (3 steps) and a cleanup (2
steps), with a fault injected at each step and at the creation's, the
activation's and the deletion's transaction: a refusal, an expiry, an
interrupt, a stop of the database, a `RuntimeException`, an `Error`. Then:
the status (BUILDING after a stop, FAILED with the reason after a
`RuntimeException`, ACTIVE else), each status read earlier unchanged, the
database failed only after the `Error`, memory and stream agree (a
refused change left both as they were), and after a restart the index's
entries equal H2's reference and every marker is gone. Unit: every
injection point once, at most 3 s; night: with random points and 500
objects. File `IndexJobsHarness.java` (new).

### 9.4. H4: the primary scan (F7)

Harness 6.7's reference (018-04: each key's versions by time) over a
directory with a subdirectory, `String`, `byte[]` and object values: every
listing at a random lookup time, with `startAt`, `inclusive`, `backward`,
for each of `byte[]`, `Object`, `String`, `DbObject` and a Data Object
class, equals the reference's keys and values by 3.5's table. Unit: 3
seeds × 500 operations, at most 2 s; night: 30 seeds × 5,000. File
`PrimaryHarness.java` (new).


## 10. The implementation steps

Frans's order was F4, F5, F3, F6, F7, F8. Adjusted, for the code's
dependencies:

* The new pure parts of F3 (the encodings, the definition's bytes, the
  function) come first, as I0: they touch no shared file and let I1 to I3
  build on tested code.
* F4 (I1) next, on today's layout: the read time and 015-46 are in the
  write path, which the layout does not change.
* F5 and F3's layout are one step (I2): the generations are what lets a
  deletion be one transaction, and both rewrite `IndexManager` and
  `IndexBuilderImp`; two steps would write the layout twice.
* F7 (P1) runs from the start in parallel: its own files, needed by no
  other step; it stops the primary scan's use of the `PRIMARY` pseudo-index
  that I2 removes.
* F8 is split: the release jar (B1) now; the removals (B2) when nothing
  uses what they remove; the `DbObject` move (B3) after the objects' API.

Each step is one commit, tests first, gated by `java/before-commit.sh`
("BEFORE COMMIT OK"), in a scratch clone, handed to the coordinator, who
commits. Estimates are an agent's hours, gates included.

| Step | Agent | What | Waits for | Estimate |
|---|---|---|---|---|
| I0 | A      | encodings, definition, function (pure)   | nothing                    | 2 h   |
| P1 | B      | F7, the primary scan, H4                 | nothing                    | 2.5 h |
| B1 | C      | F8: the release jar                      | nothing                    | 1 h   |
| I1 | A      | F4: read time, lock rule, 015-46, races  | I0; 020-08 step 2          | 2.5 h |
| I2 | A      | F5 + F3: layout, jobs, API, H3           | I1; P1                     | 7 h   |
| I3 | B      | F6: the scan builder                     | I2                         | 3 h   |
| H2 | C      | harness H2                               | I3 (coded from 9.1 before) | 2 h   |
| B2 | C      | F8: ICU, `Kv.ikey()`, narrowing, Javadoc | I3; H2                     | 2 h   |
| B3 | A or C | F8: `DbObject` into `bergdb.pub`         | 020-08's API steps         | 1 h   |

The critical path is 020-08 step 2, then I1, I2, I3, H2 and B2: about 17
hours after step 2 (I3 can go to B, who is free after P1). The night does
I0, P1, B1, likely I1 and part of I2; the next day the rest. C, idle
between B1 and I3, writes H2's model and reference (test code only)
against section 3's API, to run when I3 lands.

### 10.1. Who owns which file

A file is changed by its owner's steps only. Shared: `Pack.java` (each
step appends its new test classes; the coordinator merges the lines) and
the item's own files. `PubTester.java` belongs to the objects' steps; I2
changes only its two index tests (`createFast` to `start().join()`), and
the coordinator merges.

Paths are under `java/src/bergdb/` unless named otherwise.

* **I0**: new `pubimp/IndexKeys.java` (4.4: the encodings, E, succ, the
  entry's build and parse) and `pubimp/IndexDefinition.java` (4.2: write,
  read from bytes, check; `read(Db, name, t)`, the definition at a lookup
  time; 3.3: the function over a `DbObject`); their testers
  `IndexKeysTester.java` and `IndexDefinitionTester.java`; the vector
  `index-definition-2` in `pubimp/doc-files/object-vectors.txt`.
* **I1**: `pubimp/RwEnvironmentImp.java`, `WTransaction.java`,
  `RwTransaction.java`, `WBuilderImp.java` (the routing of 5.1),
  `IndexManager.java` (the lock rule, the hooks); new
  `PubTesterIndexRaces.java`.
* **P1**: `pub/UsePrimaryBuilder.java`; `pubimp/UsePrimaryBuilderImp.java`
  (its own iterator over `Db.getMany`, no `UseIndexBuilderImp`, its
  constructor's signature kept, `dirInternal` kept until I2);
  `PubTesterPrimary.java`; new `PrimaryHarness.java`.
* **B1**: `java/build.sh`, `java/readme.txt`.
* **I2**: `pub/IndexBuilder.java`, `pub/Database.java`,
  `pub/StartupInfo.java`, `pub/util/Job.java`, `pub/util/JobStatus.java`,
  `pub/IndexAlreadyExistsException.java`, `pub/NoSuchIndexException.java`;
  `pubimp/IndexManager.java`, `IndexBuilderImp.java`, `DatabaseImp.java`,
  `StartInfoImp.java`, `FieldRef.java`, `RwEnvironmentImp.java`
  (`setIndexEntry`, N11); gone: `FieldIndexFunction.java`,
  `IndexFunction.java`, `IndexEntryBuilder.java` (into I0's classes),
  `Data.java`; `UseIndexBuilderImp.java`, only so far as the new layout
  needs (the definition read with I0's `read`, the keys with
  `IndexKeys`, no collator; today's grammar kept for I3 to replace);
  the testers `PubTesterIndex.java`, `PubTesterComposite.java`,
  `PubTesterNestedFields.java`, `PubTesterIndexJobs.java` (ICU,
  multi-directory and multi-field tests out, `createFast` replaced), new
  `IndexJobsHarness.java`; `PubTester.java`'s two index tests;
  `src-dev`: `bergdb/test/CreateIndexTester.java`,
  `bergdb/test/DeleteIndexTester.java`, `frans/PayDemo.java`. It may keep
  `IndexManager.PRIMARY` and `Database.PRIMARY` for I3 to remove.
* **I3**: `pub/UseIndexBuilder.java`; `pub/Connection.java` (the Javadoc
  of `useIndex`, `usePrimary`, `freezeLookupTime`); `pub/Database.java`
  (`PRIMARY` out, after I2); `pubimp/UseIndexBuilderImp.java` (rewritten
  for 3.4), `ConnectionImp.java` (`useIndex`, the time of `usePrimary`,
  N3, `PRIMARY` out); the scan tests of `PubTesterIndex.java`,
  `PubTesterComposite.java` and `PubTesterNestedFields.java`.
* **H2**: new `pubimp/IndexHarness.java`.
* **B2**: `src-icu/` (gone); `java/in/icu-for-bergdb.jar` and
  `java/in/ICU-LICENSE.html` (gone); `java/build.sh`; the collator classes
  of `pubimp` and `IcuInfo.java` (gone); `src-dev/bergdb/dev/Info.java`;
  `pub/Kv.java` and every `Kv` implementation; the visibility of
  `pubimp` (7); `overview-pub.html`, `pub/package.html`,
  `pubimp/package.html`; the repo's `README.md`; `docs/levels.md` (a
  section for the non-Core part, as 020-01, section 14, asks).
* **B3**: `pubimp/DbObject.java` to `pub/DbObject.java`, with the classes
  of section 7's last point, and every import of them.

Files that two steps own are owned in turn, never at once: I1, I2 and I3
share `RwEnvironmentImp`, `IndexManager`, `UseIndexBuilderImp` and the
index testers, and run one after another.

`releases/next.md` gets one line per step, by the coordinator at commit.

### 10.2. Each step, what it must show

* **I0**: every encoding's order against Java's comparison for 100,000
  random pairs per type and for the edges (MIN, MAX, −0.0, ±∞, `00`, `01`,
  `ff`, empty, prefixes); E's prefix rule; every definition field's
  refusal (one test per row of 4.2); the function's table (3.3) by kind,
  with absent fields, paths through non-objects and the 4,096-byte limit.
  Nothing uses the classes yet.
* **I1**: 9.2's races and `testStringOverObject`, failing on the code
  before; the existing index tests pass unchanged (today's layout).
* **P1**: H4; S2-F17, S2-F25 tests; the old `PubTesterPrimary` tests that
  stay valid unchanged; `IndexManager.initFromDatabase` still works
  through `dirInternal`.
* **I2**: the new API (`createFast` gone: its 36 calls in the testers and
  one in `PayDemo` become `start().join()`), the layout (4), the start (4.5), the jobs (6), H3,
  the rows of section 8 marked I2; 020-08 step 3's refusal of `/#i/dii/`
  kept. 020-09's case K16 names `Data.Index`, which goes: if 020-08's step
  8 tests it, that test takes another class of the same shape (tell the
  coordinator). `level2.sh` once (BryanRepro: scans through restarts).
* **I3**: the grammar test (every call in every state), the rows marked
  I3, the scans of the rewritten testers.
* **H2**: 9.1, with its three planted faults found.
* **B2**: `javadoc-pub.sh` ("JAVADOC PUB OK"), the release jar check, no
  reference to ICU left (`grep -ri icu` over `java/src`, `src-dev`).
* **B3**: the gate and `javadoc-pub.sh`.

No step touches the Core, the stream's format below `/#i/`, the Lean
model or the C clone. `night.sh` is the coordinator's, when the machine
has room (no `night.sh large` tonight, Frans 22:12).


## 11. Decided under Frans's delegation (22:17)

For his information; each with its reason in the section named.

1. The definition is a format-2 object read and written field by field,
   not its own bytes: one spec and codec for all stored structures (4.2).
2. The generation G is the latest transaction's time at the creation, 8
   bytes in the entries' key; unique per name by the lock rule (4.3).
3. The keys: `/#i/didef/-<name>`, `/#i/dient/d<name>/` ‖ G, the marker
   `/#i/didel/d<name>/-<G16>`; a start refuses `/#i/dii/` (4.1).
4. An entry is prefix ‖ levels ‖ K, no separator and no directory number;
   its value is empty (4.1, 4.4).
5. `string` and `bytes` share one escaped encoding, which replaces
   today's +2 one for strings (4.4).
6. −0.0 is indexed as 0.0; NaN gives no entry (3.3).
7. Each type takes exactly its stored kind; no kind is converted (3.3).
8. Limits: 8 levels, 16 path parts, names of 255 bytes, 4,096 bytes of
   levels per entry (else no entry) (3.1, 3.3).
9. Every put and delete at an object key, of any value, keeps the indexes,
   so a `w()` of `String`s at such keys may run again (5.1).
10. Writers read the index set under the manager's lock after R; they no
    longer read the definition's key (5.1, 5.2).
11. `JobStatus` is state, count, reason, note; `progress()` goes;
    `Database.indexJob(name)` replaces `getStartupJobs()`; `deleteIndex`
    returns nothing; a deletion during a build makes it FAILED "deleted";
    a failure is kept in memory only (3.2).
12. A deleted generation's cleanup is resumed from a marker key (6.2).
13. A build step reads at most 25 values of any kind (6.1).
14. `UseIndexBuilder`'s grammar: `eq`, then `from`/`to` or `prefix`,
    `backward`; from above to is an empty scan (3.4).
15. Scans fix a frozen lookup time as a get does and leave
    `transactionInfo()` alone (3.6).
16. `UsePrimaryBuilder` keeps its method names; `dir()` is required and
    first; its types list by kind (3.5).
17. `Database.PRIMARY` goes (3.2).
18. `build.sh` makes a separate release jar; `build/bergdb.jar` stays the
    jar of the tests and scripts (7).
19. `DbObject` moves with the classes its public methods name, last (7).
20. A long build is redone from the start at each restart (6.1).
21. `LookupTimeNotAvailableException` from a scan is promised (3.6).
22. N11, new: key replace reached into an entry's level bytes; it is
    limited to K (5.3).


## 12. Log

2026-11-08. Written at the coordinator's request after Frans's decisions
of 22:08 to 22:12 (020-01, section 14.1), from the code at `acac9d2`; the
gaps decided under his delegation of 22:17 (section 11). No code changed.

2026-11-09. Section 3.2: `join()` of a FAILED build throws
`IndexBuildException` (Frans, 08:29: "Do as you propose"); the code, its
tests and the Javadoc changed with it.

2026-11-09. Section 5.3: key replace in an object key's directory refused,
and no previous value for a replaced name (the Codex review's X1, 020-14);
the code, its tests and the Javadoc changed with it.
