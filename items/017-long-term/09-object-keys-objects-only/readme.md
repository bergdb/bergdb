017-09. Object keys hold objects only
=====================================

Created 2026-11-09 by Frans Lundberg. Status: open.

Open (a study; notes only). For a release after 2026.4, not 2026.4.

What this topic holds: the idea of refusing a `String` or a `byte[]`
value at an object key, so that text and bytes live at keys with a suffix
(such as `.txt`) and only object puts and deletes reach the index layer.
Today's suffix rules, what the idea removes, its price, the variants, a
recommendation and the questions for Frans. Nothing decided; no code
changed. Code is cited by path and line at `6d9b0fb` (main, 2026-11-09),
release 2026.3 at its tag (`929fa33`); a path is under `java/src/bergdb/`
unless it starts with `java/`.


## 1. What it is about

Since 020-10's step I1 (`249b684`), every put and delete at an object key
(a key without a suffix, or with `.obj`), whatever its value and whether
its directory has an index, follows 020-10, section 5.1's rule:

1. its read time R is fixed first (the latest transaction's time, if it
   has read nothing);
2. the hash of the directory's virtual key, `/#i/div/<dir>`, goes into
   its read set;
3. the directory's index set is read from the index manager, under its
   lock, after R;
4. if the set is not empty, the previous value is read at R, and the
   entries of the old value are deleted and those of the new one put; a
   value that is not a stored object has none.

A `w()` with such a write goes through `RwTransaction.executeRw` and may
run again after a conflict. That a `String` or a `byte[]` at an object
key follows the rule too is 020-10, section 11, decision 9, taken under
Frans's delegation of 2026-11-08, 22:17. The rule fixes 015-28 (a write
racing an index's creation), 015-43 (index work before the read time) and
015-46 (a `String` or `byte[]` put over an indexed object left its
entries; an object put over a `String` threw). Its cost is 020-11's C-M8
(020-12, M8): a `w()` of one `String` put at an object key takes 2.6 µs
against 2.3, 13 %.

Frans accepted C-M8 for 2026.4 (2026-11-09, 07:18; 006-15, section 6.3,
point 2; 020-11, section 1): "I am not currently concerned with the cost
in time. I am more concerned with layers and complexity." The Core Layer
knows nothing of indexes (010-01, P12); his concern is the coupling of the
index layer to the Pub layer's writes: the index layer must see every
write at an object key, even of a `String` or a `byte[]`, values it never
indexes. Less of that coupling is this topic, for a later release.

The idea: a put of a `String` or a `byte[]` at an object key is refused,
as a put of an object at a key with a suffix is refused today. Steps 1
and 2 stay for objects and deletes (015-28 needs them: an object put or a
delete racing a creation must be ordered with it), so the question is how
much coupling and complexity goes, and at what price.


## 2. Why it matters

Three couplings of text and bytes to the index layer exist today, all
from the rule's scope:

* **The lock.** A `String` or `byte[]` put at an object key, in any
  directory, reads the index set under the one lock of the database's
  index manager (`pubimp/IndexManager.java`, line 63; one object per
  database, line 32), also in a database that never had an index:
  `RwEnvironmentImp.indexEntries` asks for every such write
  (`pubimp/RwEnvironmentImp.java`, lines 401 to 403).
  A definition change holds that lock across its Core transaction
  (`IndexManager.createInner`, lines 232 to 257; `activateInner`, 285 to
  310), and a build step that met three conflicts retries under it until
  it commits (`pubimp/IndexBuilderImp.java`, lines 390 to 403,
  `LOCKED_AFTER` = 3). So a write of text in `/notes/` can wait for an
  index of `/payments/`.
* **Reruns.** A `w()` of a `String` at an object key is no longer a blind
  write: it has a read time and a read set, and runs again, after a
  sleep of 10 ms, then 20, 40 and more, when an index of its directory is
  created or deleted between its read time and its commit, or, in an
  indexed directory, when its key is written meanwhile (020-10, section
  5.1, "Which writes").
* **A put's legality depends on the index set.** A `byte[]` put whose
  bytes are an object of format 1 (2026.3's) is stored at an object key
  of a directory without an index, and refused with `DataFormatException`
  in one with an index (`RwEnvironmentImp.indexEntries`' Javadoc, lines
  381 to 386; `pubimp/IndexDefinition.java`, lines 413 to 428); in a race
  with a creation, the timing decides.

And one that the rule does not cause but the idea touches: the kind of a
value is not stored, so at an object key every reader guesses whether the
bytes are an object, a `String` or bytes (`pub/Connection.java`, lines
166 to 175; `pub/UsePrimaryBuilder.java`, lines 27 to 35).

**The idea is old.** Until 2013-11-05 BergDB had this rule in the form of
its time: an object was put only at a `.obj` key, and a `String` or a
`byte[]` put at a `.obj` key was refused ("Bad key for set of
String.class, should not end with .obj"). Frans's commit `ce0c574` of
2013-11-05 ("Now, we do not need the ".obj" suffix for object storage")
made a key without a suffix an object key and dropped both refusals,
leaving in `RwEnvironmentImp.put` the note "TODO, A. Consider forcing
special suffix, or at least not EMPTY or ".obj". Or rather:
!Entries.isObjectKey(ikey)" for a `String`, and "NOTE, No check here, but
we could force suffix != EMPTY" for a `byte[]`. The TODO went at release
2013.3 (`e0faeb0`, 2013-11-29) without the check; the note for `byte[]`
is still at `RwEnvironmentImp.java`, line 325. (The 2013 to 2017 history:
F1-007's bundle, `a/007-bergdb-261012/bergdb-git.bundle` in the f1 repo;
the backlog line "DONE! Remove need for ".obj" suffix. That should be
default." in its `bergdb/doc/2013/2013-backlog.txt`, line 36.) Frans's
notes of March 2013 already name values by suffix, as files:
`load("images/im1.jpeg", byte[].class)`, `load("help/0123.txt",
String.class)`, `load("dir/data1.obj", DataClass.class)`
(`2013-03-notes.txt`, lines 304 to 306).

**And it was on the table for 2026.4.** 016-06's review S1, S1-F7 (015-46)
named the design choice: "whether a String or byte[] at an object key is
allowed at all (refused, as an object at a key with a suffix is), or
allowed and kept out of the indexes". 020-01 asked it (section 4.5,
question 4; section 7.5, question 4; N4 in section 12; section 14,
decision 6: "the kind of a value (N4: stored, or an indexed directory
holds objects only)"); 020-02, section 4.5 listed it as option (iii) for
telling an object from other bytes, and 020-05, section 7 noted that (iii)
"makes 015-46's case (a String put over an object in an indexed
directory) a refused put". Frans took the header byte 0x82, option (i)
(2026-11-08, 16:22), and left the `byte[]` case with the API; 020-10 then
kept non-objects allowed, with no entries (decision 9).


## 3. Today's suffix rules

### 3.1. The suffix and the object key

One definition, in `pubimp/Entries.java`: `suffix` (lines 49 to 60) is
what follows the last '.' of the key's last part, after its last '/'; a
name that starts with '.' has one (".h" has "h"); a '.' in a directory's
name gives none (021-10). `isObjectKey` (lines 74 to 79): no suffix, or
the suffix `obj`, which its Javadoc calls obsolete (lines 66 to 70). So
`/a`, `/a.obj`, `/d/x.` and `/v1.2/k` are object keys; `/a.txt`, `/a.bin`
and `/d/.h` are not. The harnesses' references copy it apart
(`IndexReference.isObjectKey`, line 379; `PrimaryHarness.isObjectKey`,
line 172).

2026.3's rule differed: `Entries.suffix` at `929fa33` (lines 42 to 52)
took the whole key's last '.', so no key under `/v1.2/` was an object key
(it had the suffix `2/k`), and a ukey `/d/.h` had none
(`releases/next.md`, lines 180 to 185; 020-11, R3-N2).

The only other suffix with a meaning is `.txt`, and only to a reader: a
get as `Object.class` gives a `String` there (3.4).

### 3.2. What each kind of key allows

The writers, `RwEnvironmentImp.put` (lines 312 to 340), the same for
`Connection.put`, `WBuilder.put` (through `WBuilderImp`, lines 27 to 30)
and `RwEnvironment.put`:

* **An object** (neither a `String` nor a `byte[]`; a `DbObject`, a Data
  Object, a wrapper, an array): only at an object key; at another key
  `IllegalArgumentException` ("Bad key, expected no suffix (or possibly
  the obsolete '.obj' suffix)", lines 332 to 336), before anything is
  written.
* **A `String`** (well-formed UTF-8, lines 237 to 255) or **a `byte[]`**
  (copied, line 328): at any key. The Javadoc says so in one place only:
  "a String or a byte[] may be put at any key" (`pub/package.html`, lines
  61 and 62).
* **A delete**: at any key.

### 3.3. What a put and a delete do, in 2026.3 and 2026.4

| Put or delete | 2026.3 (`929fa33`) | 2026.4 (`6d9b0fb`) |
|---|---|---|
| object, object key   | object op; `executeRw`; R not fixed | object op; rule; `executeRw`        |
| object, other key    | refused ("Bad key")                 | the same                            |
| `String`, object key | KV op; no index work                | object op; rule; no entry           |
| `byte[]`, object key | KV op; no index work                | object op; rule; entry if an object |
| text or bytes, other | KV op                               | the same                            |
| delete, object key   | object op; `executeRw`              | object op; rule; `executeRw`        |
| delete, other key    | KV op                               | the same                            |

"Rule" is section 1's rule (020-10, section 5.1); "object op" is
`RwEnvironmentImp`'s map `objectOps`; "KV op" its map
`kvOps`, written to the Core as it is. A `w()` with an object op goes
through `RwTransaction.executeRw` (`pubimp/WTransaction.java`, lines 30
and 31; `pubimp/RwTransaction.java`, lines 107 to 162); one without it is
executed once, and a conflict is a `Bug` (`WTransaction`, lines 33 to 40).

* **2026.3**: `setBytes` (lines 230 to 242) put a `String` or a `byte[]`
  in `kvOps` at any key, with no index work, so one over an indexed
  object left its entries (015-46, S1-F7 (a)). `indexEntries` (from line
  361) read the index set before R (015-28, 015-43), and in an indexed
  directory parsed the previous value as a `DbObject`, which threw
  `DataFormatException` for a `String` there (lines 396 to 405; S1-F7
  (b)): an object could not be put over a `String` while the index
  existed.
* **2026.4**: `setBytes` (lines 259 to 275) puts a `String` or `byte[]`
  at an object key in `objectOps`, as `ObjectInfo.ofBytes` (lines 646 to
  653) with the flag `string` (line 601), elsewhere in `kvOps`; `delete`
  (lines 296 to 307) the same split. `indexEntries` (lines 388 to 437)
  applies the rule: `fixReadTime` (lines 444 to 449), the directories'
  hashes (397 to 399), the set under the lock (401 to 403,
  `IndexManager.getActiveIndexesForDir`, lines 198 to 202), the previous
  value at R (418), an object of format 1 there taken as no entry (419
  to 421), a `String` put's new value never looked at (422), every other
  new value through `IndexDefinition.entryLevels` (lines 419 to 432): a
  `byte[]` that passes 020-07's full check is an object (020-10, section
  3.3, rule 1), one of format 1 is refused in an indexed directory.

### 3.4. What a read does with a value at each kind of key

| Read as | Object key | Key with a suffix |
|---|---|---|
| `Object.class`      | `DbObject` if 0x82, full check; else bytes | `.txt`: `String`; else bytes |
| `String.class`      | UTF-8 decoded, else `DataFormatException`  | the same                     |
| `byte[].class`      | the stored bytes                           | the same                     |
| a class, `DbObject` | full check, else `ObjectCreationException` | the same                     |
| scan, a class       | the objects only                           | none                         |
| scan, `String`      | every value that is not an object          | every value                  |
| build's entry       | f(v) for a stored object; none else        | none                         |

From `pubimp/KvToObjectImp.java` (`createObject`, lines 27 to 90;
`entryToMixedTypeObject`, lines 114 to 132, the `.txt` rule at line 126),
`pubimp/UsePrimaryBuilderImp.java` (`isObject`, lines 208 to 221) and
`IndexDefinition.entryLevels`. An object of format 1 at an object key is
refused by every read that takes it for an object, and fails a build.
So a `String` put at `/text` and read as `Object.class` comes back as a
`byte[]`, not a `String`; only `.txt` gives a `String`. The index scans
check each entry against its value at the scan's time and skip a stale
one (`pubimp/UseIndexBuilderImp.java`, lines 318 to 350), so an entry
left behind gives no wrong answer; it stays in the index's keys, which
020-10's harnesses check against the index function.

### 3.5. Where it is decided

* **`bergdb.pub`**: no code decides a suffix; the Javadoc states the
  rules: the package's "Objects" (`pub/package.html`, lines 44 to 63),
  `Connection.put` (`pub/Connection.java`, lines 246 to 254),
  `WBuilder.put` (`pub/WBuilder.java`, lines 28 to 32),
  `RwEnvironment.put` (`pub/RwEnvironment.java`, lines 61 to 64), the
  guesses of `Connection.get` (lines 166 to 175) and of
  `UsePrimaryBuilder` (lines 27 to 35).
* **`bergdb.pubimp`**: `Entries` (the definition); `RwEnvironmentImp`'s
  `put`, `setBytes` and `delete` (which map a write takes) and
  `indexEntries` (the rule); `KvToObjectImp` and `UsePrimaryBuilderImp`
  (the reads); `IndexDefinition.entryLevels` (the index function's rule
  1).
* **The Core**: nothing. It stores keys and bytes (010-01, P12), and the
  Core's `Db`, which is API (`pub/package.html`, lines 9 to 11), writes
  any bytes at any key.


## 4. What the idea removes, and what stays

### 4.1. Code

With the idea (option (a1) of section 6: a `String` and a `byte[]`
refused at every object key), in `pubimp/RwEnvironmentImp.java`:

* `put` (lines 324 to 330) refuses a `String` or a `byte[]` at an object
  key with `IllegalArgumentException` before anything is written, the
  mirror of lines 332 to 336.
* `setBytes` (lines 259 to 275) loses its `objectOps` branch: text and
  bytes always go to `kvOps`.
* `ObjectInfo.ofBytes` (lines 646 to 653) and the flag `string` (line
  601) go, and with them `info.string ? null :` in `indexEntries` (line
  422): a new value in `objectOps` is always an object that `ObjectInfo`
  made (`DbObject.toDbObject`, or a user's `DbObject` after the full
  check, lines 623 to 641), so always of format 2.
* `indexEntries` can no longer throw `DataFormatException`: its only
  source was a new value of format 1, which only a `byte[]` put could
  give: the Javadoc's `@throws` (lines 381 to 386) goes, and its list's
  item 4 (lines 370 to 376) loses its `String` and `byte[]` cases. The
  map's comment (lines 42 to 48) and `WTransaction`'s (lines 27 to 29)
  say "object puts and deletes" again; the map's name `objectOps` is true
  again.

Small in lines: about 15 lines of code and 25 of comments go, about 5
come. The gain is in the rule's scope and in what the API promises.

### 4.2. Behaviour

* A write of text or bytes never reaches the index layer: it takes no
  lock, fixes no read time, adds no hash, and is executed once (a blind
  write, `WTransaction`, lines 33 to 40); `rw()`'s `indexEntries` returns
  at once when it has no object ops (line 392).
* No put is refused by an index: whether a put is stored depends on its
  key and value only, never on the index set or on a race with a
  definition change (section 2, the third coupling).
* The index layer's input is the writes that can make or remove an entry:
  object puts, and deletes at object keys.
* 015-46's fix is halved: "a `String` or `byte[]` over an object deletes
  its entries" cannot happen through the Pub API; "an object over a
  `String` puts its own and does not throw" stays, for old data (4.5).

### 4.3. Tests that become moot or change

* `pubimp/PubTesterIndexRaces.java`: the write `STRING` (lines 66, 242 to
  244) is a third of the 36 races of `testRacesCreate`, `testRacesActivate`
  and `testRacesDelete` (3 changes, 4 points, 3 writes): 12 races go, or
  become one test that a `String` put takes no lock (a hook that fails if
  called). `testStringOverObject` (lines 258 to 311): its `String` and
  `byte[]` puts at `KEY`, in `w()` and `rw()`, and the "last call wins"
  mixes become refusals; the `byte[]` that is a stored object (lines 286 to
  289) a refusal under (a1), an object put under (a2); the keys with a
  suffix (305 to 307) stay. `testFormat1InIndexedDirectory` (lines 321 to
  353): the `byte[]` puts of format 1 (328, 333) are refused by key, in
  any directory, with `IllegalArgumentException`, not `DataFormatException`;
  the `String` put over a Core-written format-1 value (343) is refused;
  the Core writes stay, as the way to make old data.
  `testWriteWithoutIndexRunsAgainAfterCreation` (355 to 381) stays: it
  puts an object (its Javadoc says "a w() of a String", which goes).
* `PubTester.testStringThatStartsAsFormat1` (`pubimp/PubTester.java`,
  line 3993; 020-11, R3-F1): its puts at an object key become Core writes,
  or move to a suffix.
* `PubTesterIndex`: `testNonObjects2`'s `byte[]` at `/payments/22`;
  `testStaleLastEntries`' `String` at `/r/a4` (line 2228).
* Harness H2 (`pubimp/IndexHarness.java`, `keyValue`, lines 330 to 349:
  at an object key 10 % `String`s, 10 % `byte[]`s, 5 % bytes that start
  as an object but are not) and its reference `IndexReference`; harness H4
  (`pubimp/PrimaryHarness.java`, `value`, lines 407 to 427: at an object
  key more `String`s and `byte[]`s than objects). Their generators put
  objects only at object keys; the readers' tolerance is then covered by
  Core writes of old data, as `testNonObjects2` and
  `testFormat1InIndexedDirectory` make it already.
* Incidental uses: about 120 puts of a literal `String` or `byte[]` at an
  object key in the Pub testers (`PubTester` 79, `PubTesterPrimary` 19,
  `PubTesterOutput` 10, `Utf8ReadTester` 5, `DataObjectsTester` 5,
  `DbObjectFormatTester` 2, `PubTesterIndex` 2), and puts at computed keys
  that a grep does not find, such as the night test `CcDbNightTest`'s
  `byte[100]` at `/cards/<hex>`
  (`java/src-dev/bergdb/test/night/CcDbNightTest.java`, line 122).
  Most move to `.txt` or `.bin` with no other change.

### 4.4. C-M8

C-M8 is the rule's cost on a `w()` of one `String` put at an object key:
0.3 µs, 2.6 against 2.3 (020-12, M8, quiet; 100 puts a `w()` hide it,
0.98). With the idea, that write does not exist: the same text at a key
with a suffix takes the plain path, so the rule's 0.3 µs goes for it, all
of it.

But ObjectBench's M8 (`java/stress/ObjectBench.java`, lines 476 to 512)
puts `/s1/k<n>` against `/t1/k<n>.txt`, 4 bytes longer, and there the
`.txt` key took 3.0 µs a `w()` in both builds, against 2.3 at the shorter
key in format 1, where neither paid the rule (100 puts: 253 and 260 µs
against 241 and 235). So in that bench a user who moves a `String` from
`/s/k` to `/s/k.txt` gains nothing; the bench does not separate the
suffix from the key's length and directory. To measure: keys of the same
length (section 7, first steps).

What stays: object puts and deletes pay the rule (an object put not
indexed, M5: 2.3 µs, already 0.77 of format 1's). A cut of that is
independent of the idea (option (c'), section 6).

### 4.5. What stays

* Steps 1 to 4 for every object put and every delete at an object key,
  in every directory, the lock and the reruns included (015-28, 015-43).
* The readers' tolerance, unchanged: `KvToObjectImp`,
  `UsePrimaryBuilderImp`, `IndexDefinition.entryLevels`, the build's skip
  of non-objects (`IndexBuilderImp`, lines 457 to 460), the previous
  value's format-1 case (`RwEnvironmentImp`, lines 418 to 421), the
  guesses in the Javadoc.
  Non-objects at object keys still come from old databases, from the
  Core's `Db` (API) on the same files, and from other writers (012's C
  clone writes Core bytes). So "an object key holds an object" becomes a
  promise of the Pub API's writers, not an invariant a reader may rely
  on.
* The index scans' check of each entry against its value.


## 5. The price

### 5.1. The API

The rule's text changes in: `pub/package.html`, "Objects" (lines 57 to
63: "a String or a byte[] may be put at any key" becomes "only at a key
with a suffix", and the `byte[]` of format 1 in lines 52 and 53);
`Connection.put` (lines 246 to 254, and its `@throws`, 262 to 267);
`WBuilder.put` (lines 17 to 32, 34 to 47); `RwEnvironment.put` (lines 54
to 73); `Connection.get` (lines 166 to 175: the guess stays, for data
written before the release or not through the Pub API);
`UsePrimaryBuilder` (lines 27 to 35, the same); the `Database` class's
example, `put("/key", "value")` (`pub/Database.java`, line 60). A draft
of the rule: "A String or a byte[] is put only at a key with a suffix,
such as "/notes/a.txt"; at an object key the put throws
IllegalArgumentException ("Bad key"), before anything is written, as an
object at a key with a suffix does. To put an object given as its stored
bytes, put new DbObject(bytes)."

**A get of a `String` at an object key.** Three ways:

* (g1) Unchanged (recommended): the bytes decoded as UTF-8, so an old
  `String` reads as before, and an object's bytes throw
  `DataFormatException` (0x82 is never the first byte of UTF-8). Its
  message could name the case ("an object; read it as a DbObject").
* (g2) Refused by key, as the put: an old `String` at an object key is
  then readable only as a `byte[]`.
* (g3) As (g1) for `String.class`, but `Object.class` at an object key
  gives a `String` for a non-object that is well-formed UTF-8: a new
  guess; not advised.

**Deletes**: unchanged; a delete at an object key follows the rule, as it
must remove whatever is there.

**Scans of mixed types**: unchanged. `usePrimary(Object.class)` over a
directory gives `DbObject`s at object keys, `String`s at `.txt` and
`byte[]`s elsewhere, as `PubTesterPrimary.testNonObjects2` shows (lines
349 to 378); for data put after the change no value at an object key is
anything but an object, so `usePrimary(String.class)` lists only keys
with a suffix, but the scan cannot tell new data from old and still
parses each candidate.

**The first example.** `c.put("/key", "value")` is BergDB's hello-world
(the website's snippets, `java/src-dev/frans/WebsiteCode.java`, lines
61 to 65; the `Database` Javadoc; `java/src-dev/bergdb/demo/Demo.java`,
line 12; `GetStarted5`, lines 14 and 17). It becomes
`c.put("/key.txt", "value")`.
A first-time user meets the rule at the first line.

**A runtime refusal.** An upgraded application that puts text at a key
without a suffix compiles and fails at its first such put, loudly, with
nothing written. The release notes must lead with it.

### 5.2. Users in the repo

* `java/src-dev/frans/PayDemo.java`: objects only, at object keys
  (accounts at `/acc/<8 digits>`, line 66; payments at
  `/payments/${transactionTime}`, line 128); its index on `/payments/`
  (lines 76 to 78). Unaffected.
* `java/src-dev/frans/WebsiteCode.java` (the website's snippets): `m1`
  puts an object (unaffected); `m2` a `byte[]` at `/data` and a `String` at
  `/text` (lines 45 to 48), `m3` `String`s at `/key` (lines 61 to 65): all
  refused; they become `/data.bin`, `/text.txt`, `/key.txt`, and the
  website's page with them.
* `java/stress/release-jar/ReleaseDemo.java`, which `build.sh` runs on the
  release jar (lines 123 and 124): `String`s at `/fruit/apple` and
  `/fruit/banana`, a `byte[]` at `/bytes/b` (lines 48, 49 and 58). Its
  Core part (line 72) is unaffected.
* Demos and manual tools in `src-dev`: `Demo`, `GetStarted5`,
  `test/manual/StorageOverhead` (line 16), `test/manual/MultipleWriters`
  (line 27, a computed key); the night test `CcDbNightTest` (4.3).
* Core-level code (`java/stress/core-build/CoreDemo.java`,
  `java/stress/DeleteRepro.java`, `ScenarioTester`'s `/direct/` keys, the
  Core's testers): the Core API, unaffected.
* `docs/levels.md`, section 11, "Maintenance" (lines 798 to 801: "every
  put and delete at an object key of an indexed directory, of any value");
  the next release's notes get an entry beside 2026.4's "Every write keeps
  the user indexes" (`releases/next.md`, lines 193 to 204).
* The Lean model (the Core's levels) and the C clone (012, the Core of
  2026.2): unaffected.

### 5.3. Old databases

A 2026.3 database opens in 2026.4 unless it holds index definitions of
format 1 (`IndexManager.start`, lines 149 to 154); its objects of format 1
are refused at a read, and its `String`s and `byte[]`s read as before
(`pub/package.html`, lines 52 to 55). A 2026.3 or 2026.4 database that
holds a `String` at an object key, under the idea:

* **A reader**: as today. `String.class` gives the text, `byte[].class`
  the bytes, `Object.class` a `byte[]`, a class or `DbObject`
  `ObjectCreationException`; the primary scan lists it as `String` and
  `byte[]`, not as an object.
* **A put over it**: of an object, works; the previous value has no entry
  (`IndexDefinition.entryLevels` gives none, `RwEnvironmentImp` lines 418
  to 421). Of a `String` or a `byte[]`, refused: the application moves the
  value, a delete of `k` and a put at `k.txt` in one `w()`.
* **A delete**: works.
* **An index build**: skips it, no entry, as today; but a `String` whose
  bytes are a whole object of format 1 still fails a build (020-11, R4-2).
* **2026.3's keys with a '.' in a directory's name**, such as `/v1.2/k`:
  not object keys in 2026.3 (3.1), so an application may hold `String`s
  there by design; object keys since 2026.4 (021-10); a `String` put there
  is refused.
* **A migration**: none needed for reads, deletes or puts of objects.
  BergDB cannot rename a user's keys, so an application that updates such
  text renames it; it finds it with `usePrimary(byte[].class)` over a
  directory, the keys without a suffix whose `get(Object.class)` is not a
  `DbObject`. A copy of an old database through the Pub API cannot keep
  such a value at its key; the Core API can. A switch in
  `DatabaseBuilder` that allows the old puts for one release would keep
  both paths, and the coupling where it is set: not advised.


## 6. The options

Every option keeps the Core untouched: none changes the stream or the
Core's code; the Pub API's rules and `bergdb.pubimp` change. None changes
the stored format, so 018-01's rule on format changes is not touched.

### (a) Refuse a `String` and a `byte[]` at every object key

* **What**: the put of a `String` or a `byte[]` at an object key throws
  `IllegalArgumentException` ("Bad key"), before anything is written, in
  `Connection.put`, `WBuilder.put` and `RwEnvironment.put`; reads,
  deletes, scans and builds unchanged ((g1), 5.1). The rule before
  2013-11-05 (section 2), with today's object keys. Two forms for bytes:
  * **(a1)** a `byte[]` refused at every object key; an object given as
    its stored bytes is put as `new DbObject(bytes)` (`pub/DbObject.java`,
    line 156), which checks it;
  * **(a2)** a `byte[]` that passes 020-07's full check is taken as an
    object put (as a `DbObject` is, `RwEnvironmentImp`, lines 629 to 637),
    any other refused.
* **How**: section 4.1; the Javadoc, 5.1; the tests, 4.3; the users, 5.2;
  the release notes.
* **Cost**: the code, an hour; the tests and harness generators, half a
  day to a day; the Javadoc, the docs and the website's snippets, a few
  hours. A prototype first (section 7).
* **Risk**: low in BergDB, a small change on a path the races already
  test; for users, a runtime refusal at their first text put at an object
  key (5.1), and old text at object keys that can no longer be updated as
  text in place (5.3).
* **The index layer sees**: object puts and deletes at object keys.
* **C-M8**: its case is gone (4.4).

### (b) Refuse them only in a directory that has, or had, an index

* **What**: as (a), but only where the directory has an index, building
  or active, at the write's R; "had" also after the index's deletion.
* **How**: the write still goes to `objectOps` and follows steps 1 to 3;
  after step 3, a non-empty set refuses it. "Had" needs a stored mark per
  directory, written by a creation and never removed, read at a start.
* **Cost**: small for "has", more for "had" (the mark, its start read,
  its tests).
* **Risk**: the refusal comes from the index layer, the coupling the idea
  is meant to remove; a put's legality depends on a racing definition
  change, so a `w()` racing a creation is stored, or refused after a
  rerun, by timing; "has" alone lets a directory hold text again after a
  deletion. (c) already handles the case with no refusal.
* **The index layer sees**: every write at an object key (to decide).
* **C-M8**: stays.

### (c) Keep today's rule (the baseline)

* **What**: 2026.4 as it ships: a `String` or a `byte[]` at an object key
  is a value with no entries, kept by the rule (020-10, sections 3.3 and
  5.1).
* **How**: nothing. Optionally **(c')**, the cut that 020-11 names for
  C-M8: the index set read without the lock, as an immutable snapshot
  under a sequence counter or a volatile count of live indexes, which
  020-10, section 5.2 allows if it keeps the invariant (a write whose R is
  at or after a definition change sees the change) with a test that
  forces each order (section 9.2's races). It cuts part of the cost for
  every write at an object key, objects too; steps 1 and 2, `executeRw`
  and the reruns stay. Unmeasured.
* **Cost**: none; (c') small to medium.
* **Risk**: none new; (c') the invariant, a known kind of risk with
  tests in place.
* **The index layer sees**: every write at an object key.
* **C-M8**: stays; smaller with (c').

### (d) The key's suffix decides the value's type

* **What**: (a), and the table that `get(Object.class)` already reads by
  (3.4) made the writers' rule: an object key holds an object, a `.txt`
  key a `String`, any other suffix a `byte[]`; each refused elsewhere.
* **How**: (a)'s change, plus a check of the suffix for each put of a
  `String` or a `byte[]` in `RwEnvironmentImp.put`. The readers keep their
  guesses for old data.
* **Gain beyond (a)**: for data the Pub API writes, a value's type is a
  function of its key: `Object.class` reads and scans by kind are exact,
  and a binding in another language reads the type from the key. Nothing
  more for the index layer.
* **Cost**: (a)'s, and more refusals of reasonable code: text at
  `/pages/a.html` or `/conf/app.json` must be `.txt` or bytes; bytes
  never at `.txt`; `PubTesterPrimary`'s mixes change.
* **Risk**: the strictest API, for a gain that old data keeps from being
  a promise.
* **The index layer sees**: as (a).
* **C-M8**: as (a).

### (e) Declared object directories

* **What**: a directory is declared to hold objects only; in it a `String`
  or a `byte[]` at an object key is refused; an index is made only on a
  declared directory. Two forms:
  * **(e1)** declared while the database runs, by a call such as
    `Database.objectDirectory(dir)`, or by its first index. A write must
    then know whether its directory is declared at its R, so it reads the
    declarations as it reads the index set today: steps 1 to 3 for every
    write at an object key, with a declaration set in place of the index
    set. Nothing gained over (c).
  * **(e2)** declared when the database is created (`DatabaseBuilder`),
    stored in an internal key, read at a start, not changed while it
    runs. A write outside the declared directories can never meet an
    index, and needs no step at all, objects too; inside them, (a)'s rule.
* **Cost**: (e2) a new API, a stored list and its start read, tests;
  changing the list needs a stop and a start, or an online design, which
  brings back (e1)'s coupling.
* **Risk**: (e2) is a schema: an application names its indexed
  directories at creation. Text at object keys stays allowed elsewhere,
  and with it the guesses.
* **The index layer sees**: (e1) every write at an object key; (e2) the
  writes at object keys of the declared directories, the fewest of all.
* **C-M8**: (e1) stays; (e2) gone outside the declared directories, for
  objects too.

### (f) Objects only at `.obj` keys (the rule until 2013-11-05)

* **What**: the reverse of (a): the object key is `.obj` only; a key
  without a suffix holds a `String` or a `byte[]`, never an object.
* **Cost**: every object key changes, in the repo (PayDemo's accounts and
  payments, every object test and harness) and in users' databases, whose
  objects at keys without a suffix can no longer be written there; it
  undoes Frans's 2013 decision ("Remove need for ".obj" suffix. That
  should be default.").
* **Risk**: high; it keeps the hello-world and moves the price to every
  object.
* **The index layer sees**: object puts and deletes at `.obj` keys, as
  (a).

Set aside: the kind in the Core's entry (020-02, section 4.5, option
(ii)), a change of the stream and the Core; a `String` put at an object
key stored as an object with one field, as a wrapper is today
(`pub/package.html`, lines 81 to 83): it is then an object put, so the
index layer still sees it, and a get as `byte[]` returns the wrapper's
bytes.

### Summary

| Option | Writes the index layer sees | API change | C-M8's case |
|---|---|---|---|
| (a)  | object puts, deletes          | text, bytes refused at object keys | gone              |
| (b)  | all at object keys            | refused in indexed dirs, by timing | stays             |
| (c)  | all at object keys            | none                               | stays; (c') less  |
| (d)  | as (a)                        | (a), and a type per suffix         | gone              |
| (e1) | all at object keys            | declarations                       | stays             |
| (e2) | those in declared dirs        | a list at creation                 | gone outside them |
| (f)  | object puts, deletes (`.obj`) | every object key                   | gone              |

All keep the Core untouched. The fewest writes reach the index layer
under (e2); then (a), (d) and (f); the most under (b), (c) and (e1).


## 7. The recommendation

**(a1), with reads unchanged ((g1)), in a release after 2026.4**, if
Frans accepts its price (5.1): the hello-world at a `.txt` key and a
runtime refusal for upgraded applications. Reasons:

1. It is the only option whose rule depends on the key alone, so the
   layering holds by construction: a write of text or bytes never reaches
   the index code, takes no lock, never runs again, and is never refused
   by an index. The index layer's input becomes the writes that can make
   or remove an entry.
2. It completes a rule that is half there: an object has been refused at
   a key with a suffix since 2013, and the reverse refusal existed until
   2013-11-05, when it was left as Frans's TODO A (section 2).
3. It removes, for a few lines of new code, the index-dependent refusal
   of a `byte[]` of format 1, a third of the 36 races and most of
   `testStringOverObject`, and 020-10's decision 9.
4. It needs no migration: old values stay readable, deletable and
   replaceable by objects (5.3).
5. (a1) over (a2): a `byte[]` means bytes, and an object given as bytes
   has its own call, `put(key, new DbObject(bytes))`, which checks it;
   (a2) keeps a second way to put an object and a full check per `byte[]`
   put at an object key.

Against the others: (d) adds refusals with no gain for the index layer;
(e2) sends the fewest writes to the index layer but is a schema and keeps
text at object keys elsewhere; (b) and (e1) keep the coupling; (c) keeps
it and is the safe default if the price is not wanted; (f) undoes 2013.
(c') is independent of all of them and could cut the rule's cost for
objects after (a).

**What it does not do**: steps 1 to 4 stay for every object put and
delete at an object key, and the readers keep their tolerance of
non-objects there, which come from old databases, the Core API and other
writers.

**First steps**, when Frans takes it up: in a clone, the refusal in
`RwEnvironmentImp.put` alone, then `before-commit.sh`, to list every test
and tool that puts text or bytes at an object key (the greps of 4.3 find
only literal keys); ObjectBench's M8 again with keys of the same length
(such as `/s1/k12345` against `/t1/k1.txt`), to know what a user gains;
the Javadoc of 5.1 drafted.


## 8. Open questions

1. Take the idea, (a), or keep today's rule, (c)?
2. Bytes: (a1), a `byte[]` refused at every object key, or (a2), taken
   as an object put when it passes 020-07's full check?
3. Reads: a get of a `String` at an object key unchanged ((g1),
   recommended), or refused as the put is ((g2))?
4. Which release? 2026.4 was the release where "No need for any
   backwards-compatibility. API can change." (Frans, 2026-11-06, 12:05);
   the idea after it is a second break of the most basic put.
5. `.obj`: keep it as an object key, or drop it (an object key is a key
   without a suffix only)? `Entries`' Javadoc calls it obsolete.
6. The advice for text: `.txt` in the docs and examples, or any suffix,
   with `.txt` only what `Object.class` reads as a `String`?
7. (c'), the rule's cost for object puts and deletes: wanted, after (a)
   or instead of it?


## 9. Log

2026-11-09. Created at Frans's request: the study of refusing a `String`
or a `byte[]` at an object key, from the code at `6d9b0fb`, the items
(015, 016-06, 020) and the 2013 history; options (a) to (f), (a1)
recommended; no code changed.
