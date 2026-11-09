# 020-22 Core writes and the Pub layer's integrity

Created 2026-11-09 by Frans Lundberg. Status: open.

A study and a draft spec: what the Pub layer (objects and user indexes, `bergdb.pubimp`)
keeps in the Core, the invariants it relies on, and the rules for writes through the Core
API (`bergdb.core.Db`) in a database that the Pub API uses: which writes are free, which
are allowed with care, which are forbidden, and for each what the Pub layer does today when
it is broken. Options for the principle and for detection, with a recommendation, draft
text for users, and the code changes that would follow, for Frans's decision. No code
changed. The probe is in `/Users/f/fl/bench/2026-11-09/r22/` (section 10).


## 1. The request

Frans, 2026-11-09, 10:43: "I know that direct writes to Core can corrupt Pub API level
indexes. In general, Core is given "root" access, can do everything, even destroying
consistancy of the upper layer. This is by design, really. Or, well, it is known at least.
We might want to define the rules more exactly. What Core API calls are allowed to do and
not. What they are not supposed to do to maintain integrity of bergdb.pub layer."

At 10:48 he said yes to coord-1109's proposal: a spec in two parts, (1) what the Pub layer
stores in the Core, each reserved key space with the invariant the Pub layer relies on, and
(2) the rules for Core writes as a table, free, allowed with care, or forbidden, and for each
forbidden write what the Pub layer does when it is broken: undefined (like editing a
database file by hand) or detected (refused with `InternalDataException` at a start or a
read, never silently wrong). The coordinator's recommendation: "Core is root" as the
principle, every reserved space and its invariants written down, and detection where a
check is cheap (a start), since silent stale indexes are the worst outcome.

The first cases are 020-16's (the fuzzing hunt of the same morning, in its clone
`/Users/f/fl/bench/2026-11-09/clone-f16`, not yet on `main`): F16-1, a corrupt entry whose
K has no ikey made a scan throw `IllegalArgumentException`; F16-2, a value at exactly
`/#i/didef/` hid every index definition from a start; F16-3, a build failed as for a bug
over a key such as `/dp/-a/b`. Here they are rows W14, W11 and W9 (section 5).


## 2. In short

* **The reserved spaces.** The Pub layer owns two key spaces: the user's data, the bkeys of
  the ikeys that start with `/d` or `/-` (every key of the Pub API maps there), and its part
  of the internal prefix `/#i/`: the index definitions (`/#i/didef/`), entries
  (`/#i/dient/`), deletion markers (`/#i/didel/`), the virtual keys of indexed directories
  (`/#i/div/`, hashes only, nothing stored) and 2026.3's spaces (`/#i/dii/`, which a start
  refuses, and `/#i/di/`, never read). The Core owns `/#i/dreclaim/` (reclaim's table,
  current row and settings) and `/#i/-dummy`. Nothing else under `/#i/`, and nothing under
  another `/#` prefix, is used. Every other key is never read or written by BergDB.
* **What holds whatever the Core writes.** A scan of an index never returns a value that
  does not match its query: it checks each value against its entry (020-10, section 3.4),
  and the Core cannot get around that check. So a stale entry is never a wrong result; the
  worst that a well-formed Core write does to the indexes is to make values **missing**
  from scans, or an index disappear. Reclaim's keys are the one place where a Core write can
  lose data.
* **Silently wrong today** (`main` at `2c248ff`): W6, a Core put at an object key of an
  indexed directory that changes the value's entry (the value is left out of scans until
  the Pub API writes the key again); W12, a well-formed definition that the Pub layer did
  not write (active without a build, another generation, other levels or directory: values
  missing); W16, a delete of an entry; W11 (F16-2) and W21, a value at exactly `/#i/didef/`
  or `/#i/dii/`, which makes a start skip every definition under it; W25, a definition
  written while the database runs, which the index manager's memory never sees. With
  020-16's fixes W11 and W21 become refusals; W6, W12, W16 and W25 stay silent, and no
  cheap check can find them: they are missing entries, and a start reads no entry and no
  user value (bounded startup, 007).
* **A new small fault, R22-1**: a Core transaction that writes a user key and a key with
  no ukey (a free key, or `/dp/-a/b`) makes `Connection.transactionInfo()`'s `Kv.key()`
  throw `IllegalArgumentException` for a get of the user key (probe U5; noted in passing in
  021-06, not registered).
* **Recommendation**: A2, "Core is root, with a detection floor": the rules of section 5
  written down; a promise that malformed internal data is refused with
  `InternalDataException` at a start or at the read that meets it, never another exception
  and never skipped (020-16's three fixes and R22-1's give it); well-formed data that the
  rules forbid is undefined, with the scan's check as the floor; the repair after a Core
  write into an indexed directory is to put the keys again through the Pub API or to make
  the index again. The free space K2: every key that does not start with `/d`, `/-` or
  `/#`. A check tool for the silent rows (B4) is optional, not for the release.
* **For Frans**: Q1 to Q6 in section 9: the principle, the free space, whether W6 is
  allowed with care or forbidden, the detection, R22-1, and where the rules are written.


## 3. How a Core write reaches a database that the Pub layer uses

* **The Pub API never reaches a reserved key.** Every key of the Pub API is a ukey, which
  `PubKeys.u2i` maps to an ikey with `d` after each `/` but the last and `-` after the
  last: `/#i/x` becomes `/d#i/-x`, so no Pub write lands under `/#i/`, and none at an ikey
  that is no ukey's (with a `/` in a name, or a segment without `d` or `-`). A lone
  surrogate is refused, so no ukey gives a bkey without an ikey. The Pub API has no raw
  write: `Kv` and `TransactionInfo` are read-only, and `WBuilder`, `RwEnvironment` and
  `Connection` take ukeys.
* **The release jar holds all of `src`**: `bergdb.core` whole (`Db`, `Trans`, `DbBuilder`,
  `Db.internal()`), `dag` (`Keys`), `storage`, `stream`, `common`, `nanotest`, `pub`,
  `pub.util` and `pubimp`. The API is `bergdb.pub`, `bergdb.pub.util` and the Core's `Db`
  with the types of its signatures (020-10, section 7; `bergdb.pub`'s package page, "The API
  and its jar"). `Db.internal()` and `pubimp`'s public methods are not API.
* **The Core API refuses no key.** `Trans.Builder.put` and `delete` take any bkey;
  `DbConstants.INTERNAL_PREFIX` says of `/#i/`: "Keys with this prefix must not be used by
  an ordinary user. The Pub Layer enforces this; the Core Layer does not."
* **Two routes** to a Pub database's stream:
  * **R1, online**: the `Db` under a running `Database`, from `DatabaseImp.getDb()` or
    `ConnectionImp.getDb()`, public in `pubimp` and marked "internal, not API" (020-10,
    section 7). BergDB's tests and tools use them (`src-dev`: `CreateIndexTester`,
    `DeleteIndexTester`, `BryanIssue`, `Interactive`, `CcDbNightTest`; `stress`:
    `ObjectBench`; the testers and 020-16's fuzzer); a user reaches them by a cast.
  * **R2, offline**: a `Db` started on the database's stream while no `Database` runs on it.
    A directory's lock (`bergdb.lock`, `FileStream`, 005-63; `LOCKED_DIRS` within a JVM)
    refuses a second start while one runs. The next start of a `Database` reads what the
    `Db` wrote.
* **What differs**: the index manager reads the definitions and markers at a start only, and
  keeps them in memory (`IndexManager.byName`, `byIdir`); writers use that memory, while
  `useIndex` reads the definition from the stream. An R1 write under `/#i/didef/` makes the
  two differ until the next start (W25); an R2 write is read, and checked, by the next
  start. In the user's data space the two routes are the same.


## 4. Part 1: what the Pub layer stores in the Core

### 4.1. The key spaces

Keys as ikeys (`core/doc-files/key-encoding.md`); a bkey is each byte + 2, `/` as `01`. So
`/d` is `01 66`, `/-` is `01 2f`, `/#` is `01 25`, `/#i/` is `01 25 6b 01`.

| Space | Keys                                         | Whose           | Read by              |
|---|---|---|---|
| D     | `/d…`, `/-…`: values at the ukeys' ikeys     | Pub             | gets, scans, writers |
| Idef  | `/#i/didef/-NAME`: a definition, format 2    | Pub             | a start; `useIndex`  |
| Ient  | bkey(`/#i/dient/dNAME/`) ‖ G8 ‖ levels ‖ K   | Pub             | scans; cleanups      |
| Idel  | `/#i/didel/dNAME/-G16`: a marker             | Pub             | a start              |
| Idiv  | `/#i/div/IDIR`: a hash only, nothing stored  | Pub             | writers' read sets   |
| Idii  | `/#i/dii/…`: 2026.3's definitions            | Pub (2026.3)    | a start (refuses)    |
| Idi   | `/#i/di/…`: 2026.3's entries                 | Pub (2026.3)    | nothing              |
| Crec  | `/#i/dreclaim/-table.txt`, `-current.txt`, … | Core            | reclaim              |
| Cdum  | `/#i/-dummy`                                 | Core            | nothing              |
| Irest | the rest of `/#i/`                           | none            | nothing              |
| Hrest | `/#…` but `/#i/`                             | none            | nothing              |
| Free  | every other key                              | the Core's user | nothing              |

Reclaim's third key is `/#i/dreclaim/-settings.txt` (015-87). The layouts of Idef, Ient,
Idel and Idiv are 020-10, section 4.1; key-encoding.md says `#` after `/` is for internal
code. A ukey's ikey is the only key of D that the Pub layer takes as a key of a directory
(V1); D holds other keys only through the Core.

### 4.2. The invariants the Pub layer relies on

* **V1, keys of a directory.** Under a directory's file prefix (`IDIR-`), a key the Pub
  layer takes as one of the directory's is the ikey of a ukey: a name without `/`, of
  well-formed UTF-8. Any other key there is no key of the Pub layer: `usePrimary` leaves it
  out (021-06), a build leaves it out (since F16-3's fix; on `main` it can fail over one),
  no get can name it.
* **V2, values.** None that the Pub layer takes on trust: a read checks what it reads. A
  `String` read is well-formed UTF-8 or `DataFormatException`; a value read as an object
  passes 020-07's full check or is not an object (`ObjectCreationException` for a get into
  a class; its bytes for `Object.class`); an object of format 1 is refused by its structure
  (020-08, section 3). By design, a `byte[]` at an object key that passes the full check is
  an object (020-01, N4).
* **V3, the entries** (the one invariant that every write must keep). For an index I of
  directory d and generation G, at every lookup time from the commit of its activation, the
  entries under (name, G) include f_I(v) for every value v at an object key of d (020-10,
  section 3.3); while it builds, those of every value written since its creation and of the
  keys its build has passed. Scans rely on it for completeness. Writers rely on the entries
  of a key being f of its previous value: they delete f(old), which they compute, not what
  is stored; an entry that is not f(old) stays. Harness H2 checks the strong form, the raw
  entries equal to f over the values exactly (020-10, section 9.1).
* **V4, definitions.** Every key under `/#i/didef/` is `/#i/didef/-NAME` with a valid name
  (020-10, section 3.1), and its value passes 020-10, section 4.2.
* **V5, who makes them.** Only the index manager makes, activates and deletes a definition,
  under its lock (020-10, section 5.2): G is the creation's time, unique per name; `active`
  follows a complete build; the manager's memory, read at a start, is the stream's latest
  set of definitions. A creation and a deletion also write the directory's virtual key, so
  that writers that read the old set run again.
* **V6, entries.** Every entry key of a live generation parses (020-10, section 4.4), its K
  the bkey of an ikey's file part (since F16-1's fix); its value is empty and never read.
* **V7, markers.** Every key under `/#i/didel/` is a marker; none names a live definition's
  (name, G); each names a generation whose entries are garbage, and a start resumes its
  cleanup, which deletes them and then the marker.
* **V8, generations.** Every generation under `/#i/dient/` belongs to a live definition or
  to a marker. The Pub layer never makes one that does not: an orphan is never read, and
  never removed.
* **V9, format 1.** `/#i/dii/` is empty (a start refuses a key there); `/#i/di/` is never
  read or written.
* **V10, virtual keys.** Nothing is stored under `/#i/div/`; the hash of `/#i/div/IDIR` is
  written virtually by creations and deletions and read by every writer at an object key of
  the directory (020-10, section 5.1, step 2).
* **V11, the Core's own.** Reclaim's three keys are reclaim's writes: a start parses them,
  and their content decides what reclaim cuts. `/#i/-dummy` is written by
  `Db.setStartupDistance` and never read.

### 4.3. What is checked, and when

| When       | What is checked                                          | Cost               |
|---|---|---|
| a start    | V4 each definition; V7 each marker; V9's `/#i/dii/`; V11 | a prefix scan each |
| `useIndex` | V4, the definition at the lookup time                    | one read           |
| a scan     | V6 for each entry met; each value against its entry      | a read per entry   |
| a build    | V1 (keys skipped); V2 (format 1 fails the build)         | part of the build  |
| never      | V3's completeness; V5; V8                                | (section 6.3)      |

A start reads no entry and no user value, so that its cost does not grow with the data
(020-10, section 4.5; 007). V3's completeness can be checked only by reading every value
and every entry of an index, a cost of the data's size (B4).


## 5. Part 2: the rules for writes through the Core

### 5.1. The classes

* **Free**: BergDB never writes the key or reads it for its meaning, in this release or a
  later one; the Core keeps it as any key (reclaim rewrites it as any live value).
* **Allowed with care**: a key of the user's data. The Pub layer's reads check what they
  read, so any bytes are taken or refused as the Pub API's documents say; but only the Pub
  layer's own writes keep the indexes (V3).
* **Forbidden**: BergDB's internal keys, and the keys of D that are no ukey's (reserved).
  Each row says what happens today when it is broken: **detected** (refused with an
  exception at a start or at the read that meets it), **harmless** (no result changes; at
  most garbage or a write run again), or **silent** (a scan gives fewer values than are
  stored, or an index is lost, with no error).

Abbreviations: IDE `InternalDataException`, VSE `VersioningStreamException`, IAE
`IllegalArgumentException`. "Today" is `main` at `2c248ff`; "F16" adds 020-16's three
fixes (clone-f16 at `b1a659f`: `a3c5e61`, `19cd6a4`, `dfb7df4`). U1 to S1 are the probe's
cases (section 10).

### 5.2. Free

| Row | A write through the Core                             | Today                             |
|---|---|---|
| W1 | a put or delete at a key outside `/d`, `/-` and `/#` | never read (U6); but see W26      |
| W2 | reads; read hashes; virtual writes                   | no data changes                   |
| W3 | lifecycle, settings, sync, status                    | the Pub API's own calls are these |

A virtual write of a directory's hash (W2) makes its writers run again, as W23 does. W3
holds as `Database.stop()`, `close()`, `setRetainDuration()` and the other settings call
the `Db`'s. Not in any row: `Db.internal()`, not API; it can do anything.

### 5.3. Allowed with care: the user's data

An **indexed object key** is an object key (a name without a suffix, or with `.obj`) of a
directory that has an index, building or active, when the write commits; an **unindexed**
one is an object key of a directory that has none. "Care" is W6's rule: allowed with the
repair below, or forbidden (Q3).

| Row | A write through the Core                      | Rule      | Today                           |
|---|---|---|---|
| W4 | a put or delete at a key with a suffix        | allowed   | never indexed; reads check (S1) |
| W5 | a put or delete at an unindexed object key    | allowed   | a later build indexes it        |
| W6 | a put at an indexed object key that changes f | care      | **silent** (U1)                 |
| W7 | a put at an indexed object key that keeps f   | allowed   | no effect on the indexes        |
| W8 | a delete at an indexed object key             | allowed   | harmless: a stale entry (U2)    |
| W9 | a key of `/d`, `/-` that is no ukey's ikey    | forbidden | F16-3; F16: left out (U4)       |

* **W5**: a later build reads every value of the directory, so values written through the
  Core before the index's creation are indexed. A build in progress makes the directory's
  keys indexed: its steps have passed some of them. An object of format 1 there fails that
  build (U3: FAILED with `DataFormatException`), as 020-08's step 3 says; a get refuses
  it, and a Pub delete of it works.
* **W6**: the new value's entry is not written, so every scan leaves the key out (U1: 2
  results of 3 stored; a put of y over x: `eq(y)` 0 results); the old value's entry stays,
  which scans skip. It lasts until the key is written through the Pub API: a writer deletes
  f(Core's value), which is not there, and puts f(new). The repair: put each such key's own
  bytes again through the Pub API (`c.put(k, c.get(k, byte[].class))`, U8: complete again,
  one stale entry left), or delete the index and create it again (U8: complete, no stale
  entry). Rule: allowed only with the repair, or forbidden (Q3).
* **W7**: f_I(new) = f_I(old) for every index of the directory: a value that is not an
  object over one that is not (or with no entry), or an object whose indexed fields are
  unchanged.
* **W8**: no value is wrong or missing; the entry is garbage until the index is deleted
  (U2: 3 entries for 2 values after a later Pub put).
* **W9**: `/dp/-a/b`, `/dp/x`, a bkey without an ikey under `/dp/-`. Today `usePrimary`
  leaves them out, no get names them, and a build over the directory FAILED with IAE, "Not
  the ikey of a value in a directory", at every start, for `/dp/-a/b` with an object of the
  index's kind (U4, F16-3); with F16 the build skips them. Reserved rather than free, as a
  later release may give such keys a meaning (key-encoding.md's "Want 3", directory entries
  such as `/da/ndir1`).

### 5.4. Forbidden: BergDB's internal keys

| Row | A write through the Core                     | Today                       | F16        |
|---|---|---|---|
| W10 | a definition that does not parse             | IDE: start, `useIndex` (D2) | same       |
| W11 | a value at exactly `/#i/didef/`              | **silent**: no index (D1)   | IDE, start |
| W12 | a well-formed definition not the manager's   | **silent** (D3, D4, D7)     | same       |
| W13 | a delete of a definition                     | index gone; orphans (D6)    | same       |
| W14 | an entry key that does not parse             | IDE at a scan; K: IAE (E2)  | IDE        |
| W15 | a well-formed entry                          | harmless: checked (E2)      | same       |
| W16 | a delete of an entry                         | **silent** (E1)             | same       |
| W17 | a marker of a live generation, or a bad one  | IDE at a start (M1, M2)     | same       |
| W18 | a marker of a dead generation                | harmless: cleaned (M4)      | same       |
| W19 | a delete of a marker, or `/#i/didel/` itself | harmless: garbage           | 2nd: IDE   |
| W20 | a key under `/#i/dii/`                       | VSE at a start (M3)         | same       |
| W21 | a value at exactly `/#i/dii/`                | **silent** with format 1    | VSE, start |
| W22 | `/#i/di/…`, `/#i/-dummy`, the rest of `/#`   | harmless: never read (U6)   | same       |
| W23 | a key under `/#i/div/`                       | harmless: reruns (U7)       | same       |
| W24 | reclaim's keys                               | IDE (C1); else undefined    | same       |

* **W10**: `useIndex` of the name throws IDE while the database runs, and the next start
  refuses with IDE naming the key and the rule (D2). The same for a key under
  `/#i/didef/` that is not `/#i/didef/-NAME` with a valid name (020-16's area starts).
* **W11** (F16-2): the start's scan stopped at the prefix's own key, so the database
  started with no index: writes were not indexed, `useIndex` (which reads the definition
  itself) gave 2 results of 3 stored (D1), and a second index of the name could be made.
  With F16 the start refuses with IDE.
* **W12**: a definition that parses but is not the manager's. A new name in state active
  over a directory with values: scans give none of the values written before (D3: 0 of 2,
  also after a restart; only later Pub writes are indexed, D3: 1 of 4). The live index's
  definition with another G: scans read an empty generation (D4: 0 of 2). Other levels:
  entries that still parse are checked against the new function and skipped (D7, `bytes`
  for `string`: 0 of 2); entries that do not parse throw IDE at a scan (D7, `long`).
  Another directory: the old entries name keys of the new one, which match or not (D7: 1
  of 1, by chance). State `building` for an active index is harmless: the next start builds
  it again, which also restores missing entries (D5: 2 of 2 after one entry was deleted).
* **W13**: offline, a `deleteIndex` without its marker: the index is gone and its
  generation's entries are orphans, never read and never removed (V8). Online, see W25.
* **W14**: a scan that meets it throws IDE naming the key (E2: levels not ended by `00`);
  one whose K has no ikey threw IAE from `Keys.bkey2ikey` (E2; F16-1), IDE with F16. A
  scan whose range does not reach the key does not meet it (E2: `eq(x)` gave 2 results).
* **W15**: a scan reads the value at its K and skips the entry unless f(value) is its
  levels (E2: an entry of no value, an entry of y at a key holding x: skipped); an entry
  that the value does have is a correct entry, so a well-formed Core entry is never a wrong
  result. Its value is not read.
* **W16**: the value is left out of every scan (E1: 1 of 2) until the Pub API writes its
  key, or the index is made again.
* **W17**: a marker that names a live definition's generation (M1), or a key under
  `/#i/didel/` that is no marker's (M2): the start refuses with IDE naming it.
* **W18**: a marker of a generation that no live definition names: the start's cleanup
  deletes the generation's entries, then the marker (M4); this is the end of a
  `deleteIndex` done by hand.
* **W19**: the F16 column is the second case's. Without its marker a generation's cleanup
  is not resumed at a start: its entries stay, orphans (V8); an online delete during a
  cleanup is undone by its last step, which deletes the marker anyway. A value at exactly
  `/#i/didel/` hid every marker from the start on `main` (020-16, F16-2's family): no
  cleanup resumed; with F16 the start refuses it. F16 also makes a cleanup delete a key at
  exactly its generation's prefix, which on `main` ended the cleanup at once, its entries
  left.
* **W20**: the start refuses with VSE, whose message names format 1 (M3): right for a
  2026.3 database, misleading for a Core write, but a refusal.
* **W21**: the start's check of `/#i/dii/` stopped at the prefix's own key, so a database
  with 2026.3's definitions and a value at exactly `/#i/dii/` started without them instead
  of being refused (020-16, F16-2). From the code, not probed here.
* **W22**: never read. `/#i/-dummy` is the Core's and rewritten by
  `setStartupDistance`; the rest is reserved for later releases.
* **W23**: a put at `/#i/div/IDIR` writes the hash that index creations and deletions write
  virtually, so a writer of the directory that read it before the put's commit runs again;
  the value is never read (U7).
* **W24**: reclaim's table, current row and settings are parsed at a start; a value that
  does not parse refuses the start with IDE (C1). A well-formed value that reclaim did not
  write is undefined: a table that says a range is reclaimed can make reclaim cut live
  values, a loss of data. Also `transactionInfo()` takes a transaction with a key under
  `/#i/dreclaim/` for reclaim's, and throws `LookupTimeNotAvailableException`.

### 5.5. While the database runs, and transactions with keys of two spaces

| Row | A write through the Core                           | Today                         |
|---|---|---|
| W25 | a write under `/#i/didef/` while a `Database` runs | **silent** until a restart    |
| W26 | one transaction: a user key, a key with no ukey    | `transactionInfo()`: IAE (U5) |

* **W25**: the manager's memory is read at a start only (section 3). A new definition: the
  writers do not keep it, while `useIndex` reads it (D3 online: 0 of 2, and 0 of 3 after a
  Pub put). A deleted definition: `useIndex` throws `NoSuchIndexException`, the writers
  still keep its entries, and `indexBuilder(name).start()` throws
  `IndexAlreadyExistsException` until a restart, after which the index is gone and its
  entries are orphans (D6). A creation through the Pub API over a definition the Core wrote
  for a name the manager does not hold overwrites it (D3b). Another G, online: the writers
  write the old generation, `useIndex` reads the new one (D4: 0 of 2).
* **W26** (R22-1): `ConnectionImp.transactionInfo()` leaves out the keys under `/#i/`
  (005-42) and converts every other key with `PubKeys.i2u(Keys.bkey2ikey(bkey))`, which
  throws IAE for a key with no ukey: a free key (`{05 06}`, `/x`) or a W9 key (`/dp/-a/b`).
  So after a get of the user key, `kvs()`'s `key()` throws (U5). Only a Core transaction
  makes such a mix; the Pub layer's transactions write user keys and keys under `/#i/`.
  A 2016 note in the method asked it ("we cannot in general convert keys to ukey", 006-05's
  T12); 005-42 left out the internal keys, and 021-06 noted in passing that a key without
  an ikey still throws. Not registered until here.

### 5.6. What holds whatever the Core writes

* **A scan never returns a value that does not match its query.** It reads the definition
  from the stream at its lookup time, and for each entry in its range reads the value at
  the entry's key and returns it only if f(value), by that definition, is the entry's
  levels (020-10, section 3.4; `UseIndexBuilderImp.Scan.hasNext`). No write through the
  Core changes that: a stale entry, a well-formed Core entry, another definition, all give
  values that match the definition the scan read. What a Core write can do to an index is
  leave values out, make the index disappear (W11 on `main`, W13), or make the scan throw
  (W14).
* **A get returns what is stored**, checked as V2 says; a Core write there is the user's
  data, not a fault.
* **Data loss** through a Core write is only the Core's own: reclaim's keys (W24), or a
  delete of the user's data, which is the Core's root power.


## 6. Options

### 6.1. The principle

* **A1, "Core is root", undefined.** The rules of section 5 are written down; any write
  that they forbid breaks the Pub layer's promises in a way left undefined, as an edit of
  the database's files does. No promise of detection. Checked: nothing new. When and by
  whom: no one. Cost: the text (section 7). Tested: no new test; the tests that write
  through the Core today (`testScanSkipsAStaleEntry`, 020-16's area starts) stay as tests
  of robustness, not of a promise. Effect: W11 and W21 may stay silent, F16-1's and R22-1's
  IAE stay.
* **A2, "Core is root, with a detection floor".** As A1, and the Pub layer promises two
  things. (1) The scan's check: a scan never returns a value that does not match its query
  (section 5.6), whatever was written through the Core; it holds today. (2) Malformed
  internal data is never used: a key or value under the Pub layer's internal spaces that
  breaks 020-10, section 4 makes a start refuse the database with IDE (VSE under
  `/#i/dii/`) when the start reads it (definitions, markers, the prefixes' own keys), and a
  read that meets it throw IDE (an entry at a scan, a definition at `useIndex`); never
  another exception, never skipped. A key of D that is no ukey's is no key of the Pub
  layer: every reader leaves it out. Well-formed data that the rules forbid (W6, W12, W13,
  W16, W25) stays undefined, with (1) as its floor, and its repair is written down. What
  is checked and when: section 4.3's table, with 020-16's fixes and R22-1. By whom: the
  index manager at a start, `UseIndexBuilderImp` at a scan and `useIndex`, the build, and
  `transactionInfo()`. Cost: no new reads; the fixes exist (F16) or are a few lines
  (R22-1). Tested: 020-16's tests (`testStartRefusesBadIndexData`, `testCorruptEntryKey`,
  `testBuildSkipsKeysWithASlashInTheName`), the fuzzer's area starts (in `before-commit.sh`
  at 200 starts), and one new test class with a case per row of section 5 that is
  detected or harmless, and one per silent row checking that every result of a scan
  matches (the floor).
* **A3, a guarded Core.** The Core refuses a write under a protected prefix unless the
  transaction carries the owner's token: a new general mechanism, such as
  `Db.protect(byte[] prefix)` returning a token and `Trans.Builder.token(t)`; the Core
  protects `/#i/dreclaim/`, the Pub layer `/#i/` at its start (and could protect each
  indexed directory's file prefix at a creation, releasing it at a deletion). Checked: each
  key of a transaction against the protected prefixes, in `execute`, before the go point,
  refused with IAE before anything is written. Cost: a prefix compare per key; a wider Core
  API (010-01, P12: Frans's decision); every internal writer must carry its token (the
  manager, builds, cleanups, `RwEnvironmentImp`, reclaim, `setStartupDistance`); the C
  clone (012) would differ. Tested: a Core write into each protected prefix refused, every
  Pub path and reclaim unchanged. It is the only option that stops W10 to W24 when they
  are made by accident, and, with directories protected, W6; it ends "Core is root", which
  Frans calls by design.

### 6.2. The free space

* **K1**: free is every key whose first byte is not `01`, the bkey of `/`. Simplest to
  state, and leaves every `/…` ikey to BergDB. But the Core's own style of key,
  `Trans.Builder.put("/k1", …)` (the Core's tests: `/key10`), would be BergDB's space,
  though nothing reads it.
* **K2**: free is every key that does not start with `/d`, `/-` or `/#` (the bytes `01 66`,
  `01 2f`, `01 25`): any first byte but `01`, and `/` followed by any other character.
  Matches what BergDB reads today, and the Core's style of key. A later use of a new
  prefix at the root, such as key-encoding.md's directory entries (`/na` for `/a/`), would
  need one under `/#` instead.

### 6.3. Detection

* **B1, the floor's fixes.** 020-16's three fixes (F16-1: `parseEntry` refuses a K with no
  ikey; F16-2: the start's and the cleanup's scans take the prefix's own key; F16-3: a build
  skips a name with `/`), and R22-1's: `transactionInfo()` leaves out a KV whose key has no
  ukey (`Keys.bkey2ikeyOrNull`, then a check that the ikey is a ukey's), as it leaves out
  internal keys (005-42) and as `usePrimary` leaves out such keys (021-06). When: at a
  start, a scan, a build, `transactionInfo()`. Cost: none at run time. Tested: 020-16's
  tests, and for R22-1 the three keys of U5 in a Core transaction with a user key, the
  KVs being the user key only (fails today).
* **B2, orphans at a start.** A start lists the generations under `/#i/dient/` by a
  skip-scan (one read of the first key under bkey(`/#i/dient/`), then a read at the
  successor of its (name, G) prefix, and so on): one read per generation. A generation
  that no live definition and no marker names (W13, W19, V8) gets a cleanup, as a marker
  would. Cost: a read per generation at each start, small and not growing with the data
  (007's bound holds). Tested: an orphan written through the Core is gone after a restart.
  Benefit: garbage only; no result changes.
* **B3, definitions at a change.** Under the manager's lock, a creation reads the
  definition key at the latest time and refuses with IDE if the stream holds a definition
  that memory does not (D3b); a deletion and an activation refuse with IDE if the stream's
  definition is not memory's (D6, D4 online). Cost: one read per creation, activation and
  deletion. Tested: D3b and D6 as cases. Benefit: W25 is detected at the next change of a
  definition, not at a write or a scan (a writer's check would cost a read per write).
* **B4, a check of an index's content.** An operation that reads, at one lookup time, every
  value of an index's directory and every entry of its generation, and reports the entries
  that are missing (W6, W12, W16), stale (W8, W6), or do not parse (W14), and the orphan
  generations; with a repair that puts the missing entries and deletes the stale ones in
  steps, as a build does. By whom: a tool, `bergdb.dev.CheckIndexes` in `src-dev` (not
  API), or a method of the Pub API (wider API: Frans's). Cost: a read of every value and
  entry, a build's cost; run by hand or in night tests, never at a start. Tested: each
  silent row planted through the Core (U1, E1, D3, D4) is reported, a clean database
  reports nothing, and H2 (020-10, section 9.1) can use it as a second oracle. The only
  option that finds the silent rows.
* **Not proposed**: a check at each get or write that f(v)'s entry exists (a read per get
  or write per index: the cost of every user's reads, to find a fault of a Core user);
  a count or digest per index kept by writers (one key that every writer of the directory
  writes: they would all conflict).

### 6.4. Recommendation

A2 with K2 and B1, for release 2026.4; B4 later, as a `src-dev` tool, if Frans wants a way
to find the silent rows (Q4); not B2 or B3 (garbage, and a case that A2 leaves out of the
contract: R1 is not API); not A3.

Reasons: "Core is root" is Frans's principle and P12's (the Core knows nothing of indexes);
A2 adds no reads and no API, only the fixes that 020-16 found and R22-1, and turns every
failure that a check can see into one exception; the scan's check already makes a missing
result the worst outcome for the indexes, never a wrong one. The coordinator's worry, silent stale
indexes, is the missing entries, which no check at a start can see (a start reads no entry
and no value, 007); they are left to the rules, the repair, and B4. K2 because it is what
BergDB reads and what Core users write. W6 allowed with care, not forbidden (Q3): writing
values through the Core and building the index after is a natural bulk load, and the rule
(no index while writing, or a repair after) is short.


## 7. Where the rules are stated: draft text

### 7.1. `Db`'s Javadoc

A paragraph of the class Javadoc, after "The Core Data API":

> **Keys and the layers above** (bergdb 020-22). The Core takes any key and reads no value
> for its meaning (bergdb 010-01, P12). A database of the Pub API (`bergdb.pub`) keeps its
> data in the Core under keys of its own, and the Core does not stop another writer there:
> a write through `Db` can break the Pub layer's data as an edit of the database's files
> can. In a database that the Pub API uses:
>
> * **Your keys**: every key that does not start with the bytes `01 66`, `01 2f` or
>   `01 25`, the bkeys of `/d`, `/-` and `/#` (`doc-files/key-encoding.md`): a key whose
>   first byte is not `01`, or a String key such as `"/k1"`. BergDB never reads or writes
>   them, in this release or a later one.
> * **The Pub API's keys**: the bkey of the ikey of a Pub key, such as `/da/-b` for `/a/b`.
>   A put or delete there is allowed: the Pub API's reads check what they read. But only
>   the Pub API's own writes keep its indexes: a put at an object key (no suffix, or
>   `.obj`) of a directory that has an index, building or active, leaves the value out of
>   the index's scans until the Pub API writes the key again, or the index is deleted and
>   created again. Write such keys before the index is created, or make it again after. A
>   delete there leaves an entry that scans skip. Any other key that starts with `/d` or
>   `/-` is reserved.
> * **BergDB's keys**: every key that starts with `/#`, among them the internal prefix
>   `/#i/` (`DbConstants.INTERNAL_PREFIX`): reclaim's state and the Pub layer's index
>   definitions, entries and markers. Do not write them. Data there that does not parse is
>   refused with `InternalDataException`, at a start or at the read that meets it; data
>   that parses but that BergDB did not write makes values missing from an index's scans,
>   or an index disappear, and in reclaim's keys can lose data.
>
> A scan of an index never returns a value that does not match its query, whatever was
> written through `Db`: it checks each value against the index (bergdb 020-10, section
> 3.4). Write through `Db` while no `Database` runs on the stream: the `Db` under a running
> `Database` is not API, and its writes of BergDB's keys are not seen until the next start.

And `DbConstants.INTERNAL_PREFIX`'s Javadoc: "The Pub Layer enforces this; the Core Layer
does not" gains "(the rules: `Db`'s Javadoc, bergdb 020-22)".

### 7.2. `bergdb.pub`'s package page

In "The API and its jar", after its first sentence: "The Core's `Db` reaches every key, the
Pub API's own too; its Javadoc says which keys a `Db` may write in a database that the Pub
API uses (bergdb 020-22)."

### 7.3. `core/doc-files/key-encoding.md`

The paragraph "The Core Layer's own internal keys are those of Reclaim…" in "IKP" becomes:

> The key spaces of a database (bergdb 020-22): the Pub API's, the bkeys of ikeys that start
> with `/d` or `/-` (a ukey's ikey, and keys reserved for it); BergDB's internal ones, every
> ikey that starts with `/#`: the IKP `/#i/`, holding the Core Layer's own keys
> (`/#i/dreclaim/` of Reclaim, `/#i/-dummy` of Db) and the Pub API's (`/#i/didef/`,
> `/#i/dient/` and `/#i/didel/` for user indexes, `/#i/div/` hashed only; `/#i/dii/` and
> `/#i/di/`, 2026.3's, refused and unread; bergdb 020-10, section 4.1), the rest reserved;
> and the Core user's, every other key. What a Core user may write in each: `Db`'s Javadoc.

### 7.4. `docs/levels.md`, section 11

A paragraph after "**The API.**":

> **Writes through the Core.** The Core is root: `Db` writes any key, the Pub layer's
> too, and the Core refuses none (010-01, P12). The rules
> ([020-22](../items/020-release-2026-4/22-core-writes-and-pub-integrity.md), section 5;
> `Db`'s Javadoc): keys outside `/d`, `/-` and `/#` are the Core user's; the Pub API's keys
> may be written, but only the Pub API's writes keep its indexes, so a Core put at an
> object key of an indexed directory is left out of its scans until the key is written
> through the Pub API or the index is made again; keys under `/#` are BergDB's. Malformed
> internal data is refused with `InternalDataException` at a start or at the read that
> meets it; a scan never returns a value that does not match its query, whatever was
> written; a well-formed Core write of BergDB's keys is undefined.

### 7.5. 020-10

A section 4.6, "Writes through the Core", of three points: the invariants V3 to V10 by
name, with 020-22, section 4.2 as their statement; the start's and the scan's checks of
section 4.3 as the promise (A2); and 020-16's O16-2 words: in 4.4, K "is the bkey of an
ikey's file part"; in 4.5, "the prefix's own key included" (refused); in 6.1, "a step skips
a key whose name holds a `/`".


## 8. The code changes that would follow (not made)

* **A1**: none; the text of section 7.
* **A2**: section 7's text, and:
  * 020-16's three commits (`a3c5e61`, `19cd6a4`, `dfb7df4`, with their tests), which
    apply to `main` at `2c248ff` without a conflict (020-16's log);
  * R22-1 in `ConnectionImp.transactionInfo()`: leave out a KV whose key has no ukey
    (`Keys.bkey2ikeyOrNull`, then the ukey's rule as `UsePrimaryBuilderImp` applies it),
    with `Connection.transactionInfo()`'s Javadoc saying so, and a test with U5's three
    keys (fails today);
  * a test class, `PubTesterCoreWrites` (about 300 lines): one case per row of section 5
    that is detected or harmless, asserting its exception or its unchanged results, and
    one per silent row (W6, W12, W16, W25) asserting the floor, every scan result matching
    its query; it can reuse the probe's cases;
  * `releases/next.md`: R22-1 and the rules' place.
* **A3**: in the Core, the protected prefixes (`Db`, `Trans.Builder`, `execute`'s check,
  before the go point) and a token for reclaim's and `setStartupDistance`'s writes; in the
  Pub layer, the token in every internal writer (`IndexManager`, `IndexBuilderImp`,
  `RwEnvironmentImp`, the cleanup), and optionally a directory's file prefix protected at
  a creation; P12's record in 010-01 (a widening); tests in the Core and the Pub layer;
  about a day, and the C clone's difference noted.
* **K1 or K2**: text only; with K2, `Db`'s Javadoc names the three prefixes.
* **B1**: as A2's first two points.
* **B2**: `IndexManager.start`: a skip-scan of `/#i/dient/` and a cleanup per orphan; a
  test; about an hour.
* **B3**: `IndexManager.createInner`, `activateInner`, `deleteInner`: a read of the
  definition key under the lock and the refusals; tests for D3b and D6; about an hour.
* **B4**: `IndexManager.check(name, t)` (package-private: the raw entries of
  `entries(name, gen, t)` against f over `getMany` of the directory) and a tool in
  `src-dev`, `bergdb.dev.CheckIndexes DIR`, on a stopped database, with an optional repair
  in steps; tests by planting U1, E1, D3 and D4; about three hours.


## 9. Decisions for Frans

Frans, 2026-11-09, 11:13, to the six questions: "Yes", all as recommended.

* **Q1, the principle**: A1, A2 or A3 (section 6.1). Recommended: A2. **Decided (Frans,
  2026-11-09, 11:13)**: A2, "Core is root, with a detection floor".
* **Q2, the free space**: K1 or K2 (section 6.2). Recommended: K2. **Decided (Frans,
  2026-11-09, 11:13)**: K2, every key that does not start with `/d`, `/-` or `/#`.
* **Q3, W6**: a Core put at an object key of an indexed directory, allowed with care (the
  rule "no index while writing, or a repair after") or forbidden. Recommended: allowed
  with care. **Decided (Frans, 2026-11-09, 11:13)**: allowed with care.
* **Q4, detection**: B1 for 2026.4 (recommended); B4 as a `src-dev` tool, now, after the
  release, or not (recommended: after the release, if wanted); B2 and B3 (not
  recommended). **Decided (Frans, 2026-11-09, 11:13)**: B1 for 2026.4 (020-16's three
  fixes and R22-1's); B4, a `src-dev` check of an index's content, after the release if
  wanted; not B2 or B3.
* **Q5, R22-1**: `transactionInfo()` leaves out a key with no ukey (recommended), or
  throws IDE for it. **Decided (Frans, 2026-11-09, 11:13)**: it leaves out a key with no
  ukey.
* **Q6, where**: section 7's five places (recommended: all, the Javadoc first, as users
  read it), and whether the drafts' words are his. **Decided (Frans, 2026-11-09,
  11:13)**: the rules in all five places of section 7, the Javadoc first.


## 10. The probe

`/Users/f/fl/bench/2026-11-09/r22/probe/bergdb/pubimp/R22Probe.java`, compiled with `main`'s
`java/src` at `2c248ff` (`git archive` into `r22/java/src`, classes in `r22/cls`) and with
clone-f16's at `b1a659f` (`r22/f16src`, `r22/f16cls`); outputs `r22/run-main.txt` and
`r22/run-f16.txt`, one JVM each, a few seconds. Each case starts a memory database with
`/p/1` and `/p/2` holding `{s: "x"}` and the active index `a` on `/p/`, field `s`, writes
through `DatabaseImp.getDb()`, and restarts on a copy of the stream where it says so.

| Case | What the Core writes                                    | Row      |
|---|---|---|
| U1  | an object at `/p/3`; one over `/p/1`; then Pub puts     | W6       |
| U2  | a delete of `/p/1`                                      | W8       |
| U3  | a format-1 object at `/p/9`; a new index over `/p/`     | W5       |
| U4  | `/dp/-a/b` and a bkey without an ikey under `/dp/-`     | W9       |
| U5  | a user key and a free or W9 key in one transaction      | W26      |
| U6  | `{05 06}`, `/x/y`, `/#j/y`, `/#i/dfoo/-y`; a restart    | W1, W22  |
| U7  | a value at `/#i/div//dp/`                               | W23      |
| U8  | U1, repaired by Pub puts of the same bytes, then remade | W6       |
| E1  | a delete of `/p/1`'s entry                              | W16      |
| E2  | entries: K with `0x31`; levels cut; of no value; of y   | W14, W15 |
| D1  | a value at exactly `/#i/didef/`; a restart              | W11      |
| D2  | junk bytes at `/#i/didef/-b`; a restart                 | W10      |
| D3  | a definition `c`, active, on `/p/`; online, a restart   | W12, W25 |
| D3b | as D3, then `indexBuilder("c")` online                  | W25      |
| D4  | `a`'s definition with another G                         | W12, W25 |
| D5  | `a`'s definition in state building, an entry deleted    | W12      |
| D6  | a delete of `a`'s definition, online; a restart         | W13, W25 |
| D7  | `a`'s definition as `bytes`, as `long`, on `/q/`        | W12      |
| M1  | a marker of `a`'s generation; a restart                 | W17      |
| M2  | a marker key `/#i/didel/da/-zz`; a restart              | W17      |
| M3  | a key `/#i/dii/-x`; a restart                           | W20      |
| M4  | entries and a marker of (`z`, 77); a restart            | W18      |
| C1  | `retain=x` at reclaim's settings; a restart             | W24      |
| S1  | `a C0 80` at `/dq/-t.txt`; a get as `String`            | W4       |

On clone-f16 every case gives the same lines but U4 (the build active, one result), E2's
first (IDE naming the key) and D1 (the start refused with IDE).


## Log

2026-11-09. Written at Frans's request (10:43, the coordinator's proposal accepted at
10:48), by coord-1109's agent r22, from `main` at `2c248ff` and 020-16's clone at
`b1a659f`, with the probe of section 10: the inventory, the rules W1 to W26, R22-1 (new),
options A1 to A3, K1 and K2, B1 to B4, recommended A2, K2 and B1; the drafts of section 7;
questions Q1 to Q6 for Frans. No code changed.

2026-11-09, 11:13. Frans decided Q1 to Q6 as recommended (section 9): A2, K2, W6 allowed
with care, B1 for 2026.4 (B4 after the release if wanted), R22-1's KVs left out, the rules
in section 7's five places. Status stays open until the release. coord-1109's agent r22b
makes R22-1's fix and the five places' text, in its clone
`/Users/f/fl/bench/2026-11-09/clone-r22b`; 020-16's three fixes come to `main` through the
integrator, not redone here.

2026-11-09, 11:42. R22-1 fixed as Q5 decided, in the clone
`/Users/f/fl/bench/2026-11-09/clone-r22b`, commit `ff3d5f6` (on `main` at `1691676`):
`ConnectionImp.transactionInfo()` leaves out a KV whose key has no ukey, by the new
`PubKeys.i2uOrNull` (the ukey only when its ikey is the key: `u2i(i2u(ikey))` equal to the
ikey). Found while writing the test: `i2u` is lenient, so a key such as `/-q/-t` or `/dq/-`
did not throw but gave a String that is not its ukey (`/q/t`, whose key is `/dq/-t`; `/q/`,
no key); the round trip leaves these out too. Test
`PubTester.testTransactionInfoLeavesOutKeysWithNoUkey`, seven keys (U5's three, a bkey
without an ikey, `/dq/x`, `/-q/-t`, `/dq/-`), which failed before. Javadoc of
`Connection.transactionInfo()` and `TransactionInfo.kvs()`; `releases/next.md`. BEFORE
COMMIT OK (143 s).

2026-11-09, 11:50. An observation, not fixed (not asked; forbidden writes only): the index
scan's `next()` (`UseIndexBuilderImp`, line 413) takes `key()` from the lenient
`PubKeys.i2u` too, null when it throws. A well-formed entry written through the Core (W15)
whose K names a W9 key holding a matching value, such as `/dp/-a/-b`, gives the ukey
`/p/a/b`, another key's (`/dp/da/-b`); the value matches its query, so the floor of 6.1's
A2 holds, but the key is wrong. It takes two forbidden writes (W15 and W9; the Pub layer's
own entries, and builds since 020-16's F16-3, never name such a key). `i2uOrNull` there
would give null, as for a key with no ukey; for Frans or a later item.

2026-11-09, 11:56. The rules in section 7's five places, from its drafts, as Q6 decided
(clone-r22b, commit `6ef4e33`, after `ff3d5f6`): `Db`'s class Javadoc, "Keys and the
layers above" (7.1), and `DbConstants.INTERNAL_PREFIX` pointing to it; `bergdb.pub`'s
"The API and its jar" (7.2); `key-encoding.md`'s IKP section, the three spaces by a key's
first bytes (7.3); docs/levels.md, section 11, "Writes through the Core" (7.4); 020-10's
new section 4.6 and 020-16's O16-2 words in its sections 4.4, 4.5 and 6.1, citing 020-16
for F16-1 to F16-3 (7.5); `releases/next.md`, Documentation. JAVADOC PUB OK; BEFORE
COMMIT OK (149 s). Left for the release: 020-16's three fixes through the integrator (B1's
other part); B4 after the release if wanted. Status stays open until the release.

2026-11-09, 12:05. `main` had moved to `770d88b`, with 020-16's three fixes (`87a1f83`,
`2fcc546`, `d2f86f4`). The two commits rebased onto it in clone-r22b's `main`: R22-1 as
`119f927`, the rules as `d0a5f6a` (only `releases/next.md` met other entries, both kept;
the commits on `1691676` are kept on the branch `r22b-on-1691676`); after them `3883740`,
020-15's KR-O1 (at Frans's word, 11:56). The tip gated: JAVADOC PUB OK; BEFORE COMMIT OK
(144 s, unit 1497, f 86, demos).

2026-11-09, 12:20. The observation of 11:50, corrected and fixed at the coordinator's
request (a key that is not the value's is a wrong result, against A2's floor). The case of
11:50 does not happen: a K with a `/`, such as `-a/-b`, has the byte 1 and
`IndexKeys.parseEntry` refuses it with `InternalDataException` ("K has a byte below 2"). The
gap is the empty name: an entry with K `-` (it parses) and a matching value at the
directory's own file prefix, `/dr/-`, both written through the Core, made a scan give the
value under `/r/`, no key (test `PubTesterIndex.testScanLeavesOutAKeyWithNoUkey`, which
failed: `/r/ /r/a1`). Now the scan leaves out an entry whose key has no ukey
(`PubKeys.i2uOrNull`, before the value is read), as `transactionInfo()` does; nothing there
needs a refusal. The primary scan already left it out (a page holds the keys that the prefix
is a proper prefix of, `Keys.isPrefix`; its filter was exact) and now uses the same rule,
with a test as a guard (`PubTesterPrimary.testScanLeavesOutTheEmptyName`, which passed
before); the messages of `KvToObjectImp` and `IndexDefinition` name a key by `i2uOrNull`
too. No other place gives a stored key to the user: a get and `RwEnvironment` take the
user's key, and a build gives none. Commit `f61e4e8` in clone-r22b, after
`3883740`; BEFORE COMMIT OK (161 s, unit 1499, f 86, demos).
