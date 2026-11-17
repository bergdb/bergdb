# 022-02 Study: the C clone brought to release 2026.4

Created 2026-11-09 by Frans Lundberg. Status: open.

Frans, 2026-11-09, 11:45: "Should we plan to port to 2026.4. This Java
release is not final yet, but it seems very promising and quite stable
already. So, perhaps some work can start. Detailed planning for 2026.3 to
2026.4 could likely be made."

A study from reading alone, as 012-18 was for 2026.3: what changed in
Java's Core between the tag `release-2026.3` and 2026.4's candidate, what
of it the C clone (`c/`, 022) needs, how C is tested against the candidate
before the tag exists and what shows a match once it does, what may still
move, the steps, the decisions and a recommendation. Nothing was built or
run. Where this file says that C has a fault, it cites the C code that
shows it; none was reproduced.

C as read: `022` at `714d52b` (the 2026.3 port's steps 0 to 3, and its
step 4's first part, 015-68's admission at a start and 015-70's test,
landed at about 12:00; 022-01), and the rest of that step 4, the corrupt
set (`test/cross/java/CorruptSet.java`), as it stood in its clone `s4b`,
not landed.


# 1. In short

* **Small: about a quarter of the 2026.3 port.** About 3 to 4.5 hours of
  an agent's coding, 650 to 1,100 lines of C and harness (more than half
  of them tests), and about 1.5 hours of a quiet F53 for the long runs;
  steps 1 to 3 in parallel take about 1 to 1.5 hours of wall time. At the
  tag, half an hour and a short confirming run. The 2026.3 port's steps 0
  to 3 were 3,219 lines added where 012-18 had estimated 1,210; these
  figures allow for that.
* **No byte changes.** No format change, no record change, StreamDigest's
  digests unchanged (`releases/next.md`, Format), and 021-11 reads valid
  streams as before. So the cross harness shows no difference before the
  port or after it, by design: what C must change is shown by Java's own
  tests, ported, and by Java's vectors of the new functions; the cross runs
  show that nothing else moved.
* **What C needs** (section 3): the keys of 021-05 and 021-06
  (`bergdb_ikey_to_bkey` refuses bytes that are not well-formed UTF-8;
  `bergdb_bkey_to_ikey` says when a bkey has no ikey, where today it gives
  one whose bkey is another key, the fault 021-06 fixed in Java); 019-47
  (a start keeps a large value of its section's first transaction, a fault
  C has since the 2026.3 port's step 4 brought 015-68's admission);
  and 021-11 (a damaged pointer that names a node of another type, refused
  where the start or the writer links it; C refuses it later, at its
  cast). Optional: 020-20's text for a directory that cannot be listed,
  019-46's writer line (no change in C), 020-22's rules for keys in
  `bergdb.h`. Not for C: 019-46's race, `BufferedStream`'s close, the key
  printers, and the Pub layer's changes.
* **The candidate read**: `main` at `12dd8f7` (2026-11-09, 11:57:26),
  with 021-11 as `36e003f`. 20 commits since 2026.3 touch the Core
  layer's packages, 14 of them the five Core packages, where 1,083 lines
  were added: about 600 tests and documents, 240 comments and Javadoc,
  210 code, of which about 80 lines have a C counterpart.
* **Stable** (section 5): all that C needs is on `main` (021-05, 021-06,
  019-47, 021-11, and 020-20's T1), with its tests; all but 021-11, which
  landed at 11:57, also reviewed. **May move**: 020-22's Javadoc, and
  whatever tonight's checks of the release candidate find; the tag comes at
  Frans's word after them. The port starts on the stable parts against a
  pinned candidate and takes the rest as the diff from that candidate to the
  tag.
* **Recommended** (section 8): start now, in clones: steps 1, 2 and 3 at
  once, step 0 and step 2's corrupt set when the 2026.3 port's corrupt set
  lands; land after the 2026.3 port is closed; the long runs in the next
  quiet block after tonight's; at the tag, the diff and a confirming run.
  Five decisions for Frans, each with a default that goes ahead (section
  7).


# 2. What changed in Java's Core

## 2.1 The candidate and the size

The candidate is `main` at `12dd8f755f5d4e4c02922882a4bdcff6d4f47262`
(2026-11-09 11:57:26), fetched read-only into this study's clone as
`refs/remotes/repo/main`. Earlier fetches gave `dfb0c50` (11:43) and
`43f71af` (11:47), whose Core layer is this one without 021-11
(`36e003f`, 11:57). No commit is named the release candidate yet: the
candidate comes after the day's bug hunts, its checks run tonight, and the
tag comes at Frans's word (006-17, sections 2 and 3).

"The Core layer" is what C's harness compiles (`test/cross/java-build.sh`):
the packages of `deps.py --layer core`, `common`, `core`, `dag`,
`nanotest`, `pub.util`, `storage` and `stream` (the same list at both
ends), and `java/stress/StreamDigest.java`; and
`java/stress/core-build/CoreDemo.java`, which `examples/compare.sh` takes.
`StreamDigest.java`, `CoreDemo.java`, `deps.py` and `nanotest` are
unchanged.

| Part (`git diff --numstat release-2026.3 12dd8f7`) | Files | Added | Deleted |
|---|---|---|---|
| `java/`                                               | 175 | 40,488 | 10,255 |
| the Core layer's seven packages                       | 25  | 1,211  | 108    |
| of them, `pub.util` (the Pub API's exceptions, `Job`) | 8   | 128    | 43     |
| of them, the five Core packages                       | 17  | 1,083  | 65     |
| of these, tests (`@Nano`, testers), `key-encoding.md` |     | 600    |        |
| of these, comments and Javadoc                        |     | 243    |        |
| of these, code                                        |     | 213    |        |

The last three rows count the added lines by kind with a script's rule (a
`@Nano` method to its end is a test), so they are close, not exact. Of the
213 lines of code, those with a C counterpart are about 80:
`Keys.bkey2ikeyOrNull` and `toBytes`' check (021-05, 021-06),
`StringUtil.isWellFormedUtf8` (021-06), one line of `Db`'s start (019-47),
the three checks of 021-11 in `NodeCollection`, and `FileStream.listFiles`
(020-20). `main` has 199 commits since the tag, 107 of them in `java/`.


## 2.2 The commits

Every commit from `release-2026.3` to `12dd8f7` that touches the Core
layer, oldest first:

| Commit | Date | Entry | What | Class |
|---|---|---|---|---|
| `22cbcc9` | 11-07 | -      | `BuildInfo` says 2026.4-dev                          | none         |
| `15c234a` | 11-07 | 021-01 | Javadoc of `pub.util`'s exceptions and `SyncLevel`   | Pub, Javadoc |
| `b7fc20a` | 11-07 | 021-05 | a String key or value with a lone surrogate refused  | API          |
| `a1b505c` | 11-08 | 021-06 | a bkey that is not well-formed UTF-8 has no ikey     | API          |
| `fecfb10` | 11-09 | 021-06 | `KeyNode`'s printer shows a key without an ikey      | messages     |
| `9ac976d` | 11-09 | 019-46 | a reader's drop no longer evicts the writer's object | threads      |
| `4f8210f` | 11-09 | 020-10 | `Job`, `JobStatus` of the user indexes (`pub.util`)  | Pub API      |
| `db496dc` | 11-09 | 019-47 | the start admits the large values of every key node  | algorithm    |
| `02995d9` | 11-09 | 020-08 | `StringUtil.utf8Size`, for the Pub's String values   | Pub          |
| `a182faa` | 11-09 | 019-46 | the writer installs every index node it reaches      | threads      |
| `4ff57b6` | 11-09 | 020-08 | `StringUtil.toBytes(String, int)`, for the Pub       | Pub          |
| `4eaa97a` | 11-09 | 019-46 | the writer's assert before step 6; a test hook       | threads      |
| `b4dea15` | 11-09 | -      | `key-encoding.md`: the Core's own internal keys      | documents    |
| `412c739` | 11-09 | 020-10 | `IndexBuildException`; `Job.join()` throws it        | Pub API      |
| `4bba305` | 11-09 | 020-20 | T1: an unlistable directory, an `IOException`        | API, storage |
| `103328d` | 11-09 | 020-19 | F1: `JobStatus`'s Javadoc                            | Pub, Javadoc |
| `50bf8ff` | 11-09 | 020-19 | J4: `DbException`'s Javadoc                          | Pub, Javadoc |
| `12092e0` | 11-09 | 020-13 | bug 4: `BufferedStream.close()` waited for its timer | threads      |
| `285d031` | 11-09 | 020-21 | `Job.join(millis)` refuses a negative time           | Pub API      |
| `36e003f` | 11-09 | 021-11 | a pointer linked by node id: its node's type checked | refusals     |

The entries: 021-01, 021-04 to 021-06 and 021-11 in `items/021-todo/`,
019-46 and 019-47 in `items/019-todo/`, the rest in
`items/020-release-2026-4/`. `36e003f` is `1035b64` of its clone
(`/Users/f/fl/bench/2026-11-09/clone-p11`, 11:52, "BEFORE COMMIT OK;
level1.sh OK"), brought to `main` at 11:57 with its entry (`12dd8f7`).


## 2.3 Bytes on disk

None. `releases/next.md`, Format: "The Core's records and the stream's
format are unchanged. StreamDigest's digests are unchanged: its workloads
use the Core API and put no object." The format changes of 2026.4 are the
Pub layer's: objects in format 2 (020-07, 020-08) and the user indexes'
internal keys (020-10), values and keys like any other to the Core. The
Core's entries in `next.md` (021-05, 021-06, 019-46, 019-47 and 021-11)
refuse input that 2026.3 took, refuse damaged streams,
or change memory and threads; none writes another byte. The release notes'
Verification section is written at the release; by these entries it
should give 2026.3's 36 digests again (12 configurations in 3 modes),
which C's cross harness exports and compares (012-18, section 4).


## 2.4 Algorithms

* **019-47, the start's admission** (`db496dc`). A start reruns every
  transaction of its startup section but the first, whose values
  `DbStarter.createMemoryPointers` links into the section's node versions.
  015-68's admission at the end of the start (`Eviction.recordWritten`
  with no written nodes) took only the large values that the rerun's
  pointer listener reported, so a value over 1 MiB of the first
  transaction stayed in its leaf for as long as the database ran, unless a
  budget forced its eviction. Now `Db.startInner` passes the resident key
  nodes as the written nodes, `eviction.recordWritten(this,
  cache.nodes().iterator())`: each of their pointers to a value over 1 MiB
  in the stream becomes a stream pointer. Memory only.
* **019-46, a reader's drop and the writer's load** (`9ac976d`, `a182faa`,
  `4eaa97a`). A reader whose cache policy keeps no index node
  (`Dag.CACHE_NOTHING`) removed its empty handle (`Cache3.dropIfEmpty`,
  without the write lock) while the writer could load the node into that
  handle and make it canonical; the drop then evicted the writer's object
  in the middle of its transaction. The drop now decides after its
  compare-and-set and makes the handle LIVE again if an object came; the
  writer installs and swizzles every index node it reaches, whatever its
  op's policy (`isWriter || op.cachePolicy.shouldCache(node)`), which
  changes nothing for BergDB's writer, whose policy caches every index
  node; an assert before step 6 says that the writer's handle holds an
  object. Threads only.
* **021-11, the links by node id** (`36e003f`). 019-32's check that a
  pointer names a
  node of the type it expects (`NodeCollection.checkPointeeType`) was made
  where a pointer is followed, not where the Core gives a pointer the
  handle of the node that its position names: the start's rule 4
  (`linkToCanonical`, by the section's ids and, for a top node's pointer,
  by the node's header), its check of 005-57 (`checkLinkById`, with `-ea`)
  and the writer's `resolvePointers` (the pinned rule, before a node is
  written). A damaged pointer, its node's checksum right, that named a
  version of a node of another type got that node's handle, and a read
  threw a `ClassCastException` (with `-ea` an `AssertionError`). Now each
  of the three checks the type first, with `StreamFormatException`
  ("Pointer i of node N names a node of type T at P, not E."): the start
  refuses the stream, the writer's check fails the database. Found by
  reading in C's port (022-01, step 2). Tests:
  `NodeCollection.testResolvePointersChecksTheType`, and
  `CorruptStreamTester.testFound021_11` with a new configuration `LONG`
  (keys of three segments, so that key nodes point to key nodes, which the
  tester's keys of one segment never made).
* **020-13, bug 4** (`12092e0`): `BufferedStream`'s consumer thread no
  longer waits for its timer while a close waits for buffered bytes.
  Threads only.


## 2.5 The API

* **021-05** (`b7fc20a`): `Keys.toBytes(String)`, and so every Core call
  that takes a String key, and `Trans.Builder.put(String, String)` throw
  `IllegalArgumentException` for a lone surrogate, which the encoder wrote
  as '?'. The rule (021-04, Frans's option 1): every string BergDB stores
  is well-formed UTF-8, in every language; "in C and Go bytes that are not
  well-formed UTF-8" are the counterpart of a lone surrogate.
* **021-06** (`a1b505c`, `fecfb10`): `Keys.bkey2ikey` and
  `Keys.toString(long[])` throw `IllegalArgumentException` for a bkey
  without an ikey: one with the byte 0 or 0x31 ('/' + 2, which no ikey
  gives, '/' being 1), or whose bytes, each 1 as '/' and every other less
  2, are not well-formed UTF-8 (the new `StringUtil.isWellFormedUtf8`, RFC
  3629). The new `Keys.bkey2ikeyOrNull` returns null for it. So two bkeys
  never give one ikey, and the ikey's bkey is the bkey. The Core API still
  takes any bkey. The debug printers (`Klong.getKeyString`,
  `KeyNode.getKeyString`) show bytes with `Keys.toDisplayString`.
* **020-20, T1** (`4bba305`): `new FileStream(dir)` of a directory that
  cannot be listed throws an `IOException` ("Cannot list the directory
  DIR: an I/O error, or no permission to read it.") and releases the lock,
  where it threw a `NullPointerException`; `FileStream.hasStreamBytes`
  declares `IOException` (the Pub layer's).
* `Db` and `DbBuilder`: no public method added, removed or changed.
  `pub.util`: the Pub API's (`IndexBuildException`, `Job`, `JobStatus`,
  Javadoc). `StringUtil.utf8Size` and `toBytes(String, int)`: the Pub
  layer's String values (020-08).


## 2.6 Documents and refactors

`core/doc-files/key-encoding.md`: the bkey to ikey rule (021-05, 021-06)
and the Core's own internal keys, Reclaim's `/#i/dreclaim/` and
`/#i/-dummy` (`b4dea15`). Javadoc in `Handle` (DEAD, 019-46), `Db`'s start
and `Eviction.recordWritten` (019-47), `pub.util`. `BuildInfo`.


## 2.7 The tests

The tests a port takes over: `Keys.testLoneSurrogate` (in C, as bytes:
021-04's CK1 to CK5), `Keys.testBkeyWithoutIkey`,
`Keys.testBkeyIkeyRoundTrip`, `StringUtil.testIsWellFormedUtf8`,
`Eviction.testStartAdmitsLargeValuesOfTheSectionsFirstTransaction`; with
021-11, `NodeCollection.testResolvePointersChecksTheType` and
`CorruptStreamTester.testFound021_11`; optionally
`FileStream.testUnlistableDirectory`. Not: 019-46's three
`NodeCollection` tests (forced schedules by hooks and threads) and
`EvictionAccountingTester`'s night tests, `BufferedStream`'s,
`KeyNodeTester.testPrintKeysWithoutIkey`, `Trans.testLoneSurrogateRefused`
(C has no String put).


# 3. What the C clone needs

C as read (`714d52b`, and step 4's corrupt set in its clone), checked
against each change. "Fault" means that C's code does what Java's did
before the fix.

| ID | Java's change | C today | For C |
|---|---|---|---|
| 021-06  | a bkey without an ikey has none   | fault: `keys.c` 41 maps any bkey   | needed   |
| 021-05  | a lone surrogate refused in a key | fault: `keys.c` 18, any but FE, FF | needed   |
| 019-47  | the start admits every key node's | fault: `db.c` 657 admits none      | needed   |
| 021-11  | a link checks the node's type     | unchecked: `ncoll.c` 513, 599      | needed   |
| harness | `CorruptStreamTester.Config`      | `CorruptSet.java` 404 (4b's clone) | needed   |
| 020-20  | an unlistable directory refused   | refused: `plat.c` 27, another text | optional |
| 019-46  | the writer installs index nodes   | same in effect: `ncoll.c` 348, 373 | optional |
| 020-22  | the rules for Core writes         | no such note in `bergdb.h`         | optional |
| 019-46  | a reader's drop raced the writer  | one caller; no op keeps nothing    | no       |
| 020-13  | `BufferedStream.close()`'s wait   | no thread                          | no       |
| 021-06  | `getKeyString` of the printers    | no printer of nodes                | no       |
| Pub     | `pub.util`, `StringUtil`'s sizes  | no Pub API, no String values       | no       |


## 3.1 Needed

Needed because C must refuse what the release refuses, with its texts, and
follow its rules (`c/readme.md`, "Which Java"). The cross tests show none
of 1 to 3 (the vectors' new kinds show 1 and 2); the corrupt set shows 4.

1. **021-06, a bkey without an ikey.** `keys_bkey_to_ikey` (`keys.c` 41)
   maps every byte, 1 to '/' and any other b to b − 2, and
   `bergdb_bkey_to_ikey` (`api.c` 233) returns nothing; `bergdb.h` (476
   to 479) calls it "Java's Keys.bkey2ikey before the UTF-8 decoding",
   which 2026.4's Java no longer is. A bkey with 0x31 gives '/', whose
   bkey is 0x01: another key's ikey, the fault that 021-06 fixed ("two
   bkeys never give one ikey"); a bkey with the byte 0 gives 0xFE, which
   no UTF-8 has. The port, line for line with `bkey2ikeyOrNull`: false
   for the byte 0 or 0x31, the map, then the well-formedness check of 2;
   `bergdb_bkey_to_ikey` returns `int`, `BERGDB_ARG` for such a bkey (D3).
   Nothing in C calls it but `api.c`.
2. **021-05, ikeys that are not well-formed UTF-8.** `keys_ikey_to_bkey`
   (`keys.c` 18) takes any bytes but 0xFE and 0xFF, and `bergdb.h` (466
   to 474) says "The bytes are not checked to be UTF-8": it takes
   `ED A0 80` (a surrogate) and `C0 80` (an overlong NUL), 021-04's CK1
   and CK4, keys that no Java String gives and that 2026.4's rule says a
   writer refuses. 021-04 (option 1) names this change: "A later port
   checks ikeys in `bergdb_ikey_to_bkey`"; 021-06, answer 2: "The C
   clone's writer (`bergdb_ikey_to_bkey`) refuses such keys at a later
   port". The port: `StringUtil.isWellFormedUtf8` line for line in a
   module of its own (`strutil`, one function: a cut sequence, an overlong
   form, a surrogate, a value above U+10FFFF, and the bytes C0, C1 and F5
   to FF are not well-formed), called by `keys_ikey_to_bkey` before its
   loop, `BERGDB_ARG` as for the empty key. Every call that takes a bkey
   takes any bkey, as Java's Core API does. `tools/run.c`'s `valid_utf8`
   (243) keeps checking the workloads' keys (the runner uses `bergdb.h`
   only, and its check is Java's decoder with REPORT, the same set).
   Tests for 1 and 2: 021-04's CK1 to CK5 (`ED A0 80` and `C0 80` now
   refused, `EF BF BD` and '?' taken, 0xFF refused), the cases of
   `StringUtil.testIsWellFormedUtf8` and the nine bkeys of
   `Keys.testBkeyWithoutIkey`, and `testBkeyIkeyRoundTrip` (100,000
   random bkeys of bytes near UTF-8's edges, with `test_random`: no ikey,
   or the ikey's bkey is the bkey). And two new kinds of Java's vectors,
   written by `Vectors.java` from the candidate and read by `t_vectors.c`,
   so that Java's own code gives the answers, as for every other
   conversion: `utf8 BYTES RESULT` (`StringUtil.isWellFormedUtf8`) and
   `bkey2ikey BKEY IKEY` or `none` (`Keys.bkey2ikeyOrNull`).
3. **019-47, the start's admission.** The 2026.3 port's step 4 (`714d52b`)
   ports 015-68 as 2026.3 has it: the rerun's pointer-created listener puts
   the rerun's large values on eviction's admission list, and `db_open`
   drains it with `ev_record_written(&db->ev, NULL)`, no written nodes,
   before its first `db_evict` (`db.c` 657). `create_memory_pointers`
   (`starter.c` 536) links the values of the section's first transaction,
   which is not rerun, into the section's node versions, and
   `ev_record_written`'s loop over the written key nodes (`evict.c` 261)
   does not see them: a value over 1 MiB of that transaction stays in its
   leaf after the start. C counts it in its resident bytes, so eviction
   takes it when the budget presses; under a larger budget (200 MB by
   default) it stays, against the release's rule that such a value is
   reached by a stream pointer, as in 2026.3's Java. The port: the open
   passes the node table's resident key nodes (Java's `cache.nodes()`): a
   walk of `nt_slot`, each live handle's key node through the loop's body,
   made a function. Test:
   `Eviction.testStartAdmitsLargeValuesOfTheSectionsFirstTransaction` in
   `t_evict.c` (a startup distance of 200 bytes, values of 1,200 KiB, a
   second large value or not, no large resident pointer after the start and
   after the reads, by `t_evict.c`'s `large_resident`, 430, which
   `evict_start_admits_large_values`, 459, uses for 015-68).
4. **021-11, the links by node id** (`36e003f`). C links as
   2026.3's Java does: `nc_resolve_pointers`' pinned rule (`ncoll.c` 513)
   and `nc_link_to_canonical` (`ncoll.c` 555 to 603, the link at 599) take
   the handle without `nc_check_pointee_type` (`ncoll.c` 134, 022-01's
   step 2), and `check_link_by_id` (534 to 553) gives 005-57's
   `AssertionError` before any type check. C refuses such a pointer later,
   where it casts the node it follows (`dag.c`, `topds.c`: a
   `ClassCastException` with the JVM's text, 022-01's step 2), and
   `t_ncoll.c` 607 to 636 (`ncoll_link_to_canonical_another_type`)
   records that the link is made, as Java's was. The port: the check at
   the three places, before the link, as `36e003f` puts it; the test
   inverted to expect the refusal; `testResolvePointersChecksTheType`
   ported to `t_ncoll.c`; and the corrupt set's bases `found-021_11`
   (`CorruptStreamTester.write(LONG, 1)` and the three rows of
   `testFound021_11`, in step 4b's exporter), started by both dumpers:
   Java and C refuse each at the start with the same text. Without the
   port, those three copies differ (C starts them and refuses at the first
   read that meets the pointer).
5. **The harness** (step 0). The pinned candidate (section 4.1). Step 4b's
   `CorruptSet.java` (line 404 in its clone) calls
   `new CorruptStreamTester.Config(name, 1000000, 0, 0, 0, 0)`; with
   021-11 the constructor takes a seventh argument, the keys, so it does
   not compile: `CorruptStreamTester.KEYS`, 2026.3's keys. Java's vectors
   written again from the candidate: equal, all twelve files (the
   vectors' ikeys are well-formed and hold no '?'; `Reclaim`,
   `StoredTrans`, the codecs and `Keys`' other functions are unchanged).
   Nothing else of the harness uses what changed: `Dump.java` and
   `StreamScan.java` print bkeys (`Keys.toBytes(long[])`), not ikeys, and
   `Workload.key` decodes with REPORT, so no workload has a key that
   021-05 refuses.


## 3.2 Optional

* **020-20, T1's text.** C refuses a directory that cannot be listed
  already: `plat_list_dir` (`plat.c` 27) gives "IOException: Cannot read
  directory DIR: " and `strerror`'s text, and `open_dir` closes the stream
  and releases the lock (`stream.c` 337 to 343). Java's text is now
  "Cannot list the directory DIR: an I/O error, or no permission to read
  it." No harness compares it. Port the text and
  `FileStream.testUnlistableDirectory` (a directory with mode 0; skipped
  where that does not stop the listing, as for root). A few lines.
* **019-46's writer line.** In `follow_stream_pointer`, the install and
  the swizzle take `isWriter || should_cache` (`ncoll.c` 348, 373), and
  an assert before step 6 (385) that the writer's handle holds an object.
  In C nothing changes: both ops' policy is `cache_all_except_large`
  (`dag.c` 156, 232), which keeps every index node, and this path follows
  index nodes only. It keeps `ncoll.c` line for line with Java. A few
  lines.
* **020-22's rules for Core writes**, in `bergdb.h`, section E: in a
  database that Java's Pub API also uses, a key that starts with `/d`,
  `/-` or `/#` (the bkeys `01 66`, `01 2F`, `01 25`) is BergDB's, any
  other the Core user's; C itself writes only reclaim's `/#i/dreclaim/`
  and `/#i/-dummy`. The Javadoc's text is in flight (020-22's agent r22b,
  Frans's Q6: the rules in `Db`'s Javadoc first); take its words when it
  lands. A paragraph.


## 3.3 Not for C

* **019-46** (`9ac976d`, `a182faa`, `4eaa97a`): a race between a reader's
  drop, without the write lock, and the writer's load. C has one caller
  and no thread (`c/readme.md`, section 8), and no op that keeps nothing
  (3.2), so `nt_drop_if_empty` (`ntable.c` 172) runs only after a reader
  read a cut-back version, never with the writer between its test and its
  kill.
* **020-13, bug 4**: `BufferedStream`'s thread; C writes its buffer in the
  calls (`c/readme.md`, section 9, point 1).
* **The printers** (`fecfb10`, `Klong.getKeyString`): C ports no printer
  of nodes, and its texts of the start's refusals print no node.
* **`Trans.Builder.put(String, String)`** (021-05): C has no String put;
  its counterpart is 3.1, point 2.
* **020-08's `StringUtil` additions and `pub.util`'s six commits**: the
  Pub layer. `BuildInfo`: no counterpart in C (`created.txt` is the Pub
  layer's).


# 4. How C is tested against the candidate

## 4.1 Before the tag: the candidate pinned

`test/cross/java-build.sh` takes `JAVA_REF=2026.3` by default (the
release's source zip, checked against its `SHA256SUMS`), and
`JAVA_REF=tree` or `JAVA_REF=DIR` for another `java/` (022-01, step 0).
For the candidate:

* **The commit in every clone.** `main` at the candidate is merged into
  `022` (022-01, section 5 allows it for 2026.4's files), so that each
  clone of `int.git` has it.
* **`JAVA_REF=git:HASH`**, a new choice of `java-build.sh` (about 20
  lines): `git archive HASH java/src java/stress java/deps.py` of the
  clone, extracted once into `build/java-src/git-HASH/` with its
  `.complete` marker, as a release's zip is; `java-ref.txt` says
  `git:HASH`, so every report names the Java it ran. A release's source
  zip is the `git archive` of its commit (2026.3's notes, Files), so this
  tree is what the zip will hold, `BuildInfo` aside. The default becomes
  `git:` and the pinned hash until the tag. `JAVA_REF=DIR` with the same
  archive made by hand also works, without a change of the script, but
  then no report names the hash.
* **Which hash**: the commit that the coordinator names the release
  candidate; until then `main`'s head with 021-11, written in step 0's
  log. A later pin is a step of its own: the diff, ported, then the gate.

**The negative control** (step 0): C at the 2026.3 port's end against the
candidate. Expected: no difference in `unit` (the vectors equal), `func`,
`cross quick`, `writecheck`, `allocfail`, `examples` and `corrupt.sh`; in
the corrupt set none either, until step 2 adds the `found-021_11` bases.
That the cross runs show nothing is the check that 2026.4's Core changed
no byte, scan, dump, recovery or refusal of the sets that C sees; a
difference there is a change that this study missed. The port's own
changes are shown by the ported tests, each failing with its fix taken
out (as 022-01's steps did), and by the new vector kinds.


## 4.2 Once 2026.4 is tagged

1. `main` at the release commit merged into `022` (`releases/2026.4/`:
   the source zip, `SHA256SUMS`, `baseline.zip`); `java-build.sh`'s
   default `JAVA_REF=2026.4`.
2. The diff from the pinned candidate to the tag, over the Core layer
   (the seven packages, `StreamDigest.java`, `core-build/`, `deps.py`):
   `git diff HASH release-2026.4 -- ...`. `BuildInfo` alone: nothing to
   port. Anything else: each change classed as in section 3, ported and
   tested as the steps were.
3. `C BEFORE COMMIT OK` at `JAVA_REF=2026.4`, Java's vectors written
   again from 2026.4 and equal to the committed ones.
4. StreamDigest: the digests in 2026.4's `baseline.zip`
   (`f53/digests.txt`) equal 2026.3's (section 2.3), and `cross.sh full`'s
   exports give them.
5. `cross.sh full` and `scale`, the corrupt set and `corrupt.sh` at
   `JAVA_REF=2026.4`: no difference. By D5's default, when point 2's diff
   is `BuildInfo` alone, the candidate's long runs stand, and the gate
   (with `cross quick`) and the corrupt set are run again at 2026.4.
6. `c/readme.md`'s "Which Java" says release 2026.4 (its tag, commit and
   date), and records the 2026.3 state's commit.


# 5. What is stable, and what may still move

**Stable**, on `main` with their tests and in `releases/next.md`, and
reviewed but for 021-11:

* 021-05 (`b7fc20a`) and 021-06 (`a1b505c`, `fecfb10`): Frans's rule
  (021-04, 2026-11-07, 09:33: "Yes, option 1, absolutely.") and 021-06's
  answers under his delegation; 020-11, section 5: fixed.
* 019-47 (`db496dc`): the night's independent review ("both fixes
  correct", 020-11, section 6), the Codex review (020-14: "no defect found
  in these fixes"), `level4.sh` OK.
* 021-11 (`36e003f`), on `main` since 11:57: its gate and `level1.sh`;
  no independent review recorded yet. Should a review change it before the
  tag, the change reaches C as 4.2's diff.
* 019-46 (`9ac976d`, `a182faa`, `4eaa97a`), 020-20's T1 (`4bba305`),
  020-13's bug 4 (`12092e0`), `b4dea15`.
* The format: unchanged (2.3). And no Core API change comes from 020-22:
  Frans chose A2, "Core is root, with a detection floor" (11:13), not A3,
  a guarded Core, which would have widened the Core's API and made C
  differ (020-22, section 6.1).

**May still move:**

* **020-22's text** in the Core's Javadoc and `key-encoding.md` (agent
  r22b): documents only; R22-1's fix is the Pub layer's.
* **The release candidate's checks**, tonight after 22:00: `night.sh large`
  (about 5 hours), the jar tests on s1, jcstress, StreamDigest and the
  axioms (006-17, sections 2 and 3); and the day's hunts whose items are
  still open (020-16's fuzzing, 020-17's long runs on s1 until 18:00). A
  Core fault found there comes as a commit before the tag, and to C as 4.2's
  diff. 006-17: "Nothing new into 2026.4 after the release candidate."
* **The release commit** (`BuildInfo`, `releases/2026.4/`) and the tag,
  at Frans's word after the checks: 10 November at the earliest.

So steps 1 to 3 rest on Java that is on `main`, and the pinned hash is
the line from which the tag's diff is taken.


# 6. The steps

| Step | What | Size, agent hours | Lines | Waits for |
|---|---|---|---|---|
| 0 | the candidate pinned; the harness; the control | S, 0.5        | 50         | 4b          |
| 1 | the keys (021-05, 021-06, D3); the vectors     | S-M, 1 to 1.5 | 300 to 500 | nothing     |
| 2 | 021-11 in `ncoll.c`; `found-021_11`            | S, 0.5 to 1   | 150 to 250 | 4b, in part |
| 3 | 019-47: the open's admission                   | S, 0.5 to 1   | 100 to 200 | nothing     |
| 4 | the runs on a quiet F53                        | M, 1.5 of F53 | 0          | 0 to 3      |
| 5 | "Which Java"; the record                       | S, 0.5        | 60         | 4           |
| T | at the tag: the diff, 2026.4, the runs (D5)    | S, 0.5; runs  | 20         | the tag     |

"4b" is the corrupt set of the 2026.3 port's step 4 (022-01), in its
clone `s4b`; the step's first part landed as `714d52b`.

* **Step 0.** The merge of `main` at the candidate; `JAVA_REF=git:HASH`
  and its default; `CorruptSet.java`'s seventh argument; Java's vectors
  written again; the negative control (4.1), with every difference listed
  by class and the step that removes it, as 022-01's step 0 did.
* **Step 1.** 3.1, points 1 and 2, with their tests and the vectors' two
  kinds; `bergdb.h`'s section E and the two declarations, `c/readme.md`'s
  module table (`strutil`). D4's note on the key spaces goes here, in the
  same file.
* **Step 2.** 3.1, point 4. D4's 019-46 line goes here, in the same file.
  The `ncoll.c` part can start now; the `found-021_11` bases wait for
  4b's `CorruptSet.java`.
* **Step 3.** 3.1, point 3, on `714d52b`'s admission. D4's text for T1
  (`plat.c`, alone) goes here or in any step.
* **Step 4.** On a quiet F53: `cross.sh full` about 40 minutes, `scale` 4,
  the corrupt set and `corrupt.sh` about 10, `random.sh` over 300 seeds
  about 15. `power.sh` is not needed: nothing of the stream, its files or
  its forces changes. C builds only on macOS, so s1 cannot take them.
* **Step 5.** "Which Java" names the pinned candidate until the tag; the
  record of each step in this file's log, as 022-01 holds 2026.3's.
* **Step T.** Section 4.2.

**In parallel.** Steps 1, 2 and 3 touch separate modules, one worker each
in a clone of its own, as 022-01's steps 1 to 3: step 1 `keys.c`,
`api.c`, `bergdb.h`, a new `strutil.c`, `t_keys.c`, `Vectors.java`,
`t_vectors.c`; step 2 `ncoll.c`, `t_ncoll.c`, `CorruptSet.java`; step 3
`evict.c`, `db.c`, `t_evict.c`. All three can start at once from `022`'s
head.

**What waits for the 2026.3 port.** Step 2's corrupt set and step 0's fix
of `CorruptSet.java` wait for 4b; step 3 builds on `714d52b`, landed. And
every landing on `022`, by D2's
default, waits for the 2026.3 port to close: its step 5 (tonight's long
runs) passed and its step 6 recorded at a commit, so that the 2026.3
state is one commit gated against 2026.3. The coding of steps 1 to 3 does
not wait.

**Gate and landing** as 022-01, section 5, against the pinned candidate
from step 0 on. Since the cross runs show no difference before or after
(4.1), every landing passes the whole gate; each ported test is shown to
fail with its fix taken out.

**F53.** Builds and gates (about 5 minutes each) run at any time. Tonight's
quiet time goes to the release candidate's `night.sh large` and the 2026.3
port's step 5, so step 4 takes the next quiet block, or comes after the
tag in place of 4.2's runs.

**In all**: about 3 to 4.5 hours of an agent's coding, 650 to 1,100
lines, more than half of them tests, and about 1.5 hours of F53; with
steps 1 to 3 in parallel, about 2 hours from step 0 to the last landing.


# 7. Decisions for Frans

Each has a default that goes ahead if Frans does not answer; D6 and D7
came later. As taken (step 5): D1 (a), D2 (a) on a branch of its own, D3
(a) and D6 (a) by Frans, D4 all in, D7 (a) by default; D5 waits for the
tag.

* **D1. Start now, or at the tag.** (a) Now: the steps of section 6 on a
  pinned candidate, the coding today in clones; at the tag, the diff from
  the pinned commit (4.2), ported if not empty, and a confirming run. It
  costs a pin to keep and a second, short run at the tag, and gives a C
  at 2026.4 within hours of the tag. (b) At the tag: one port from
  `release-2026.3` to `release-2026.4`, as the 2026.3 port was made;
  nothing done twice; nothing starts before the tag, 10 November at the
  earliest. **Default (a)**, as Frans's words of 11:45 suggest. **Taken:
  (a)**, the default: steps 0 to 3 landed from 12:36 to 13:15 on the
  pinned `main`, which was pinned again three times until 15:22 (this
  file's log); the candidate's diff is taken at about 20:00 and the tag's
  at step T (022-04, sections 8 and 9).
* **D2. Landing after the 2026.3 port closes.** (a) The coding in clones
  at once; landings on `022` only after the 2026.3 port's step 5 has
  passed and its step 6 has recorded its state (a tag such as
  `022-c-2026.3` in `int.git`, and the commit in `c/readme.md`), so that
  one commit is the port of 2026.3, gated against 2026.3, and the harness
  moves to the candidate in one landing (step 0). (b) Each part lands
  when ready; the 2026.3 runs take a commit before the first 2026.4
  landing; `022`'s head is between two releases meanwhile (a gate against
  2026.3 fails on 021-11's copies, one against the candidate on what is
  not yet ported). **Default (a).** **Taken: (a)**, the default, on a
  branch of its own: the landings went to `int.git`'s new branch
  `2026.4`, not to `022`, which stays the port of 2026.3 (at `342dcb2`,
  `main`'s `142dabc`; 022-01's long runs tonight) and was merged into
  `2026.4` for the 2026.3 port's corrupt set (`0110bc7`) and step 6
  (`007285a`). The gate on `2026.4` is against the pin from step 0 on. No
  tag of the 2026.3 state was made; `c/readme.md`'s "Which Java" names its
  commit.
* **D3. C's keys and 021-04's rule.** (a) `bergdb_ikey_to_bkey` refuses an
  ikey whose bytes are not well-formed UTF-8 (`BERGDB_ARG`), as
  `Keys.toBytes(String)` refuses a lone surrogate; `bergdb_bkey_to_ikey`
  returns `int`, `BERGDB_ARG` for a bkey without an ikey (the byte 0 or
  0x31, or bytes less 2 that are not well-formed), as `bkey2ikeyOrNull`
  returns null; every call that takes a bkey takes any bkey, as Java's
  Core does. The API changes in one return type, and a caller that gave
  ill-formed bytes to `bergdb_ikey_to_bkey` now gets `BERGDB_ARG`. (b) The
  writer only: `bergdb_ikey_to_bkey` refuses; `bergdb_bkey_to_ikey` stays
  a byte map, its comment saying that a bkey without an ikey gives
  another key's. (c) Neither: the comments only, C apart from 021-04's
  rule. **Default (a)**: 021-04's rule is for every language, 021-04 and
  021-06 name this change for C's next port, and (b) and (c) keep a
  conversion that makes two keys one. **Decided (Frans, 2026-11-09,
  12:14)**: "D3 as recommended.", (a); step 1 made it.
* **D4. The optional parts** (3.2). **Default**: all in, each a few lines
  in a step that changes its file anyway: T1's text and test, 019-46's
  writer line, 020-22's note in `bergdb.h` (with r22b's words once they
  land). Section 3.3 stays out. **Taken: all in**, the default: T1 in step
  3, 019-46's line in step 2, 020-22's note in step 1 from r22b's draft,
  with `Db`'s Javadoc as landed at the pin of 13:04 and 020-27's K1 and K2
  at the pin of 15:22.
* **D5. The runs at the tag.** (a) If the diff from the pinned candidate
  to the tag is `BuildInfo` alone: the gate with `cross quick`, the
  corrupt set, and the digests compared, at `JAVA_REF=2026.4`; the
  candidate's long runs stand. (b) Step 4's runs again at 2026.4, about
  1.5 hours of a quiet F53. **Default (a)**, and (b) when the diff holds
  Core code. **Not taken yet**: it is for the tag (step T); the long runs
  of step 4 run on the candidate (022-04, section 9).
* **D6. `StreamIoException`'s text** (012-14, section 6.4, a choice left
  open; 022-03, section 10, point 5). **Decided**: Frans, 2026-11-09,
  12:25: "Yes, (a)." A failed read of the stream is named
  `StreamIoException` in C, as Java's `RecoverableStream` names it
  (012-14, section 7.4), but its text began with the inner exception's
  name and went on in C's words ("EOFException: Cannot read at spos P,
  past the end of a file at S."), where Java's message is the inner
  exception's message ("Cannot read 32 bytes at position P, stream size
  is S.", `BufferedStream`'s); the corrupt-stream set counted these as
  known (10 of 2026.3's 6,247 copies, 022-01, step 4). (a) C gives Java's
  message, byte for byte: the text is the inner message, the inner
  exception's name kept apart as the error's cause, and a database's
  stream read as Java's `Db` reads it, through `BufferedStream`, so that
  the inner message is Java's too; `tools/reappend.c`, which told a torn
  last record by the text's prefix, reads the cause; `t_rstream.c`'s
  checks change with it; `corruptset.sh` compares these messages as any
  other and fails on a difference. (b) Keep C's text, a departure
  counted as known, as 022-03, section 7, point 5 records it: the name
  compared, the message not. Made in the landing "022-02, D6" (this
  file's log), and for `corrupt.sh`'s messages in "022-02, D6,
  `corrupt.sh`".
* **D7. A new stream file and the directory forced when the file is made,
  or at the next sync, close or cut** (put to Frans by the session at
  12:43; 022-01's log, step 3, and the departure that was `c/readme.md`'s
  section 11, point 3). C forced a new file and the directory only at the
  next sync, close or cut, so one write of its 10 MB buffer could make
  several files with no force of the directory between them; a file system
  that made a later name durable before an earlier one would then leave a
  gap in the files, which both opens refuse (`BadDirStateException`).
  Java's `FileStream.newFile`, with per-append forcing on or off, forces
  the old last file (SWITCH, which finds nothing unforced with forcing
  on), makes the new file, and forces it (OPEN) and then the directory
  before the file takes a byte (`openForRw`). (a) Force each new file and
  the directory as Java does: `new_file` forces the new file
  (`PLAT_FORCE_OPEN`) and then the directory after it makes the file and
  before its first byte, and the forces of the directory at a sync and
  before a cut's deletes are dropped, as no new name is then left
  unforced. It costs an `F_FULLFSYNC` of the empty file and one of the
  directory per new file, about 1.4 ms on F53 by 022-01's figures for the
  open's forces; files grow from 200 kB to 200 GB
  (`FileStream.FILE_SIZES`), so a stream that grows to 1 GB makes about 70
  files, and one of 100 GB about 115. (b) Keep C's way, as a departure
  (`c/readme.md`, section 11): no force more; APFS keeps namespace
  operations in order, as 014-01's consequence (c) relies on for the bytes
  of a file, so on F53 the case is a theoretical one, but not on every
  file system that C may be ported to. **(a), the default, went ahead;
  Frans did not answer before leaving at 12:55; he may change it.** Done
  by worker t5 (this file's log); the stream's bytes do not change.


# 8. Recommendation

**Start now** (D1 (a)): steps 1, 2 and 3 at once, each in a clone; step
0 and step 2's corrupt set when the 2026.3 port's corrupt set (4b) has
landed; landings after the 2026.3 port is closed (D2); step 4's runs in
the next quiet block of F53 after tonight's; at the tag, the diff and a
confirming run (D5).

Why:

* It is small and well bounded: no byte changes, four needed changes of
  about 80 lines of Java between them (021-11's included), each with
  Java's tests to port.
* Two are faults of C's today: `bergdb_bkey_to_ikey` gives one ikey for
  two bkeys, the fault 021-06 fixed; and 019-47's large value, which the
  2026.3 port's 015-68 (`714d52b`) leaves in C as 2026.3 left it in
  Java. 021-11 makes C refuse a damaged stream where Java does, with
  its text, and it was C's reading that found it.
* The Java side is stable where C needs it: every change C needs is on
  `main` and in `releases/next.md`, all but 021-11 reviewed; 2026.4's
  changes are the Pub layer's.
* It keeps the clone at the current release with little work, and its
  second reading of the Core goes on (the 2026.3 port found 021-11).

Against: the release may still move tonight; the cross harness sees none
of 2026.4's Core changes but 021-11's, so the ported tests carry the
weight, and a change of a refusal or of memory that this study missed
would show nowhere (section 2.2's list of every commit and the diff at the
tag are the guard; a change of bytes would show in the negative control);
and F53's quiet time is short tonight. If the tag is near and the 2026.3
port has not closed, **at the tag** (D1 (b)) costs little more: the same
steps, in one go.


# Log

2026-11-09. Written by worker s6 of the session `022-bergdb-c`, at
Frans's request of 11:45, from `main` at `12dd8f7` (fetched read-only into
a clone of `int.git`'s `022`; first read at `43f71af`, then 021-11 landed),
`int.git`'s `022` at `714d52b` (the 2026.3 port's step 4a landed while
this was written), and step 4's corrupt set in its clone `s4b` as it
stood at about 12:00; nothing built or run. The study and a line
in 022's readme; no other file changed.

2026-11-09, step 3 (worker t3). Section 3.1, point 3, and D4's T1 (3.2);
the stream's bytes do not change. (a) 019-47: the open's admission passes
the resident key nodes as the written nodes, as `Db.startInner`'s
`eviction.recordWritten(this, cache.nodes().iterator())` since `db496dc`.
`db_open` calls the new `ev_record_written_start` (`evict.c`), which
drains the admission list as before (015-68: the rerun's large values)
and then puts the key node of each live handle of the node table
(`nt_slot`) through the record's loop body, made a function
(`admit_written`): a value over 1 MiB of the startup section's first
transaction, which `create_memory_pointers` links and the rerun's
listener never reports, becomes a stream pointer. It allocates nothing
and changes no slot. Before, C, as 2026.3's Java, kept such a value in
its leaf, counted, until a budget's sweep took it. Test: `t_evict.c`'s
`evict_start_admits_first_transactions_large_values`
(`Eviction.testStartAdmitsLargeValuesOfTheSectionsFirstTransaction`: a
startup distance of 200 bytes; "a" of 1,200 KiB and a small "b" in one
transaction, and with extra "c" of 1,200 KiB in a later one; the restart
with a budget of 100 MB: no resident pointer to a value over 1 MiB after
the start and after the reads, the values read back, the recount 0; then
the allocation failures in turn in that start, 50 and 51 starts, each
refused with nothing left or opened with no large value resident). With
the fix taken out it fails with extra: 1 such pointer after the start and
after the reads, the resident bytes over 1,200 KiB. Without extra the
section begins with the creation and the start reruns "a", so the list
has it (015-68's case), and the test passes either way, in Java too: a
probe on the candidate's Java gives the sections that C's start gives
(startPos 0 and 264, two transactions each), and with `db496dc`'s line
reverted 1 large resident pointer with extra, 0 without, as C. (b) T1
(020-20): `plat_list_dir` refuses a directory that cannot be listed with
Java's `IOException` text, "Cannot list the directory DIR: an I/O error,
or no permission to read it.", where it gave "Cannot read directory DIR:
" and `strerror`'s; an error of `readdir` refuses too, where it ended the
listing as if complete. Test: `t_append.c`'s `append_dir_unlistable`
(`FileStream.testUnlistableDirectory`: a directory without read
permission refused at the open for writing and at a read-only open,
nothing left; once readable, the byte read back; skipped where the
permission does not stop the listing), which failed before on the text.
No harness compares the text.

The gate against 2026.3 (`JAVA_REF`'s default: step 0 had not landed),
on `2026.4` at `2929db5`: `C BEFORE COMMIT OK (477 s)`, F53 under a load
of about 12 to 25; `unit` 383 tests (382 in the release build); `cross
quick` 0 differences (23 workloads, 69 crash cuts, 85 corrupt variants,
2 in turns, 46 budget runs); `writecheck` 0; `allocfail` 628 runs. No
difference remains; neither change shows in the cross runs, as section
4.1 expects.

2026-11-09, step 2 (worker t2). Section 3.1, point 4, and D4's 019-46
writer line (3.2), in `ncoll.c`; the stream's bytes do not change. (a)
021-11, as `36e003f`: `nc_check_pointee_type` (019-32's check, Java's
`StreamFormatException` and text, "Pointer I of node N names a node of
type T at P, not E.") where a pointer gets a handle by node id, before the
link: `nc_resolve_pointers`' pinned rule (the writer's; the error fails
the database), `nc_link_to_canonical` (the start's rule 4: by posToId, by
position, and for a top node's pointer by the header) and
`check_link_by_id` (005-57's check, `-check`, Java's under `-ea`), before
its comparison, so that such a pointer gives no `AssertionError`. That
`AssertionError`'s text is now Java's (C's said "no canonical object -1"
and left out the object's position). Before, C linked such a pointer, as
2026.3's Java did, and refused it later, where the Dag cast the node (the
JVM's `ClassCastException`, 022-01, step 2). (b) 019-46: the writer
installs and swizzles every index node it reaches (`isWriter ||` the
policy), and an assert before step 6 that its handle holds an object; no
change for C's writer, whose policy caches every index node. Tests, each
failing with the fix taken out: `t_ncoll.c`'s
`ncoll_link_to_canonical_another_type` (it recorded the link; now
`testFound021_11`'s three ways on nodes: by posToId to a top node, a top
node's skip pointer by the header to a key node, and with the check a
pointer in neither map, which without the check links nothing),
`ncoll_resolve_pointers_checks_the_type`
(`testResolvePointersChecksTheType`),
`ncoll_writer_keeps_the_node_whatever_its_policy` (019-46's
`testWriterKeepsTheNodeWhateverItsPolicy`: a writer whose policy cached
nothing dropped its own empty handle and made the version canonical in
it, out of the table) and `ncoll_link_to_canonical_check`'s text;
`t_sdb.c`'s `sdb_found_021_11`, `testFound021_11` on the vectors' stream:
the last record's top node's skip pointer set to a key node version from
before the startup section (before: started, and a read at time 2030
threw the `ClassCastException`; now refused at the start, with the check
and without) and its root key node's pointer 4 set to an older top node
version (with the check: the `AssertionError` before, the refusal now;
without it, started, and a read refuses, as Java's without `-ea`). In that
stream the rerun's follows refuse first (019-32) a key node's pointer set
to the newest top node; the corrupt set's `LONG` copies have that case.
(c) The corrupt set's `found-021_11` bases: not in this landing, since
step 0 (the candidate, `CorruptSet.java`'s `Config` call) and step 4b's
merge are not on `2026.4` yet; made and checked in a scratch tree, `022`
at `3e3b704` with this step and the candidate's Java (`JAVA_REF=DIR`, the
`git archive` of `12dd8f7`): `CorruptSet.java`'s `found021_11`, the three
rows on `LONG`'s original of seed 1, base `found-long-1`, in `quick` too;
and `corruptset.sh` runs C's `bergdb-dump` with `-check`, the counterpart
of Java's `Dump` under `-ea`. `quick`: 60 copies, `CORRUPTSET OK`, the
three refused by both with the same text; C at `3e3b704` differs in all
three (two started and a read failed, one gave the `AssertionError`); C's
dumps without `-check` differ in the third (Java refuses at the start, C
starts and a read fails). The whole set with `-check`, seed 1: 6,250
copies (`3e3b704`'s 6,247 and these 3), `CORRUPTSET OK` (262 s). They
land in a later commit, after step 0.

The gate against 2026.3 (`JAVA_REF`'s default: step 0 had not landed), on
step 3's landing (`8e088a7`): `C BEFORE COMMIT OK (349 s)`, F53 under a
load of about 13 to 27; `unit` 386 tests (385 in the release build);
`cross quick` 0 differences (23 workloads, 69 crash cuts, 85 corrupt
variants, 2 in turns, 46 budget runs); `writecheck` 0; `allocfail` 628
runs. No difference remains; 021-11 does not show in the cross runs (the
quick set's corrupt variants are bit flips), as section 4.1 expects.

2026-11-09, step 0 (worker t0), on `int.git`'s branch `2026.4` (D2
(a): `022` stays the 2026.3 port until it closes). The candidate pinned
(section 2.1): `main` at `12dd8f755f5d4e4c02922882a4bdcff6d4f47262`
(11:57:26). `test/cross/java-build.sh` takes `JAVA_REF=git:HASH`: the
commit's `java/src`, `java/stress` and `java/deps.py` by `git archive`
from the clone's Git, not from its working tree, extracted once into
`build/java-src/git-HASH/` (a `.complete` marker, the full hash in
`commit.txt`): the commit's 339 files of those paths. `java-ref.txt`
says `git:HASH`, so every report names it. The default on `2026.4` is the
pinned hash until the tag. `main` is not merged: the harness needs no file
of it but the commit's `java/`, read from the commit itself; a clone of
`int.git` has the commit after `git fetch /Users/f/fl/repos/bergdb
main:refs/remotes/repo/main`, which the script names when it is missing
(section 4.1 had a merge for that). The 2026.3 port's step 4b
(`3e3b704`, on `022` at 12:15) merged into `2026.4`, after step 3's
landing, and `CorruptSet.java`'s `Config` given its seventh argument,
`CorruptStreamTester.KEYS` (section 3.1, point 5); the cases' originals
are walked and patched, which use no key. So on this branch the harness
compiles against the candidate and no longer against 2026.3 (whose
`Config` has six arguments; the script's header says so). It compiles
against the candidate: 191 files, and `StatsProbe`, `PowerImages` and
`JBench` too. Java's vectors written again from the candidate: all
twelve files equal to the committed ones. Their two new kinds (`utf8`,
`bkey2ikey`) are step 1's (section 6), as `t_vectors.c` fails on a kind
it does not know. StatsProbe's lines from the candidate equal C's, so
`f_settings.c`'s stand.

The negative control (section 4.1), C at the 2026.3 port's end
(`3e3b704`'s `c/`, unchanged) against the candidate: `C BEFORE COMMIT OK
(550 s)`, F53 under a load of about 17 to 21 with other gates and the
2026.3 port's `cross.sh full`; `unit` 382 tests, `func` 27, `cross quick`
0 differences (23 workloads, 69 crash cuts, 85 corrupt variants, 2 in
turns, 46 budget runs), `writecheck` 0, `corruptset` quick 57 copies,
`allocfail` 628 runs, `examples` OK. Before 4b's merge, on `2929db5`'s
C, `C BEFORE COMMIT OK (300 s)`, the same. The whole corrupt set (seed 1,
303 s): `CORRUPTSET OK`, 6,247 copies, 2,622 refused by both with the same
exception and message, 3,560 started, 65 with a later read failing alike,
22 of 014-01's case and 10 I/O texts, the counts of 4b's run against
2026.3; the candidate's tester failed none. `corrupt.sh` (166 s): `CORRUPT
OK`, 144 variants, 82 refused by both, 40 started, 22 with a read failing
later (step 2's run had 84 and 38: four variants append `/dev/urandom`
bytes, and `last-longer`'s start refuses or recovers as they fall). No
difference: 2026.4's Core changed no byte, scan, dump, recovery or
refusal that these sets see, and none remains for a later step. What steps
1 to 3 change shows in their ported tests, step 1's new vector kinds and
step 2's `found-021_11` bases. Left for step 5: `c/readme.md`'s "Which
Java" and its vectors paragraph still name a release as the default.

The gate against the candidate on step 2's landing (`fb9f33b`), with 4b
merged (`0110bc7`), steps 2, 3 and 0 together: `C BEFORE COMMIT OK (346
s)`, F53 under a load of about 12 to 16; `unit` 387 tests (386 in the
release build); `cross quick` 0 differences (23 workloads, 69 crash cuts,
85 corrupt variants, 2 in turns, 46 budget runs); `writecheck` 0;
`corruptset` 57 copies; `allocfail` 628 runs; `examples` OK. On step 3's
landing with 4b merged, before step 2 landed: `C BEFORE COMMIT OK (359
s)`. No difference remains. Not merged: the 2026.3 port's step 6
(`ecc5319`, on `022` at about 12:40), for the session with D2.

2026-11-09, step 1 (worker t1). Section 3.1, points 1 and 2, by D3 (a),
which Frans took at 12:14 ("D3 as recommended."), and D4's note on the key
spaces (3.2); the stream's bytes do not change. (a) A new module,
`strutil` (`su_`): `StringUtil.isWellFormedUtf8` line for line (RFC 3629;
a cut sequence, an overlong form, a surrogate, a value above U+10FFFF and
the bytes C0, C1 and F5 to FF are not well-formed). (b) 021-05:
`keys_ikey_to_bkey`, and so `bergdb_ikey_to_bkey`, refuses an ikey that is
not well-formed UTF-8, before its loop and with nothing written
(`BERGDB_ARG`, as for the empty key), as `Keys.toBytes(String)` refuses a
lone surrogate; the loop's test of 0xfe and 0xff, which no longer meets
them, is Java's "Should not happen" Error as an assert. Before, C took any
bytes but 0xfe and 0xff, 021-04's CK1 (`ED A0 80`) and CK4 (`C0 80`)
among them. (c) 021-06: `keys_bkey_to_ikey` is `bkey2ikeyOrNull` (false
for a bkey with the byte 0 or 0x31, or whose bytes, mapped, are not
well-formed), and `bergdb_bkey_to_ikey` returns `int`, `BERGDB_ARG` for
such a bkey, a NULL pointer or a length over `INT32_MAX`; it was `void`, a
byte map that gave CK1's bkey its bytes and 0x31 the ikey "/", whose bkey
is 1. The empty bkey gives the empty ikey, as Java's "". Every call that
takes a key takes any bkey, as before: `f_api.c`'s `api_any_bkey` (the
byte 0, CK1's bkey, CK2's, 0x31 and FF FF put and read by getOne, by
getMany in byte order and by a prefix that is no ikey's, also after a
restart; CK1 and CK2 two keys, `Utf8ReadTester.testCk1AndCk2StayTwoKeys`
on the Core) passed before too. (d) The callers: `t_keys.c`, `t_klong.c`,
`t_vectors.c`, `f_settings.c`, and the examples, which now check
`bergdb_bkey_to_ikey`'s result (`core_demo.c`, `get_many_prefix.c`; their
output unchanged, `EXAMPLES OK`); in `src/`, `tools/` and `bench/` every
call of the ikey conversion gives ASCII constants, digits or a workload's
key that `tools/run.c`'s `valid_utf8` has checked (Java's decoder with
REPORT: the same set), and none calls the bkey conversion. (e)
`bergdb.h`: section E (any bkey; an ikey well-formed; a bkey without an
ikey), the two declarations, and D4's paragraph "Keys and the layers
above" (020-22): the user's keys, the Pub API's (`/d`, `/-`) and BergDB's
(`/#`), and C's own (`/#i/dreclaim/`, `/#i/-dummy`), from the words of
`Db`'s Javadoc in r22b's commit `d0a5f6a` (clone-r22b), which is not on
`main` yet, so step T's diff shows any change of them; `readme.md`'s
module table. Tests ported, each failing before its fix (shown on copies
of `c/`): `t_strutil.c`'s `strutil_is_well_formed_utf8`
(`StringUtil.testIsWellFormedUtf8`: every sequence of 1 and 2 bytes, and
here of 3 bytes from C0, the edges and 50,000 random sequences, against a
decoder of the test's own, as Java's against the JDK's); `t_keys.c`'s
`keys_lone_surrogate` (`Keys.testLoneSurrogate` in WTF-8 bytes, and
021-04's CK1 to CK5 after "/dd/-a"), `keys_bkey_without_ikey`
(`testBkeyWithoutIkey`'s nine bkeys and CK2, also through the segments)
and `keys_bkey_ikey_round_trip` (`testBkeyIkeyRoundTrip`: 100,000 random
bkeys near UTF-8's edges, none or the ikey's bkey the bkey); changed:
`keys_refused` and `keys_bkey_bytes` (0xfd and a lone 0x80 are no ikey's
bytes, the byte 0 has no ikey) and `f_settings.c`'s keys. Java's vectors
of two new kinds, written by `Vectors.java` from the candidate and read by
`t_vectors.c`: `strutil.txt`, new, `utf8 BYTES RESULT` (2,203 lines: the
256 bytes, the edges, 625 pairs, 1,000 random sequences and 300 of whole
characters; as an ikey, each refused unless well-formed) and `keys.txt`'s
`bkey2ikey BKEY IKEY` or `none` (1,077 lines: the ikeys' bkeys, the empty
bkey, CK2, `testBkeyWithoutIkey`'s, each single byte, 600 random bkeys
near the edges and 200 of whole characters); the other twelve files
written again are equal. Negative controls: the old `keys_ikey_to_bkey`
fails 3 unit tests (`keys_refused`, `keys_lone_surrogate`,
`vectors_strutil`) and 2 functional ones; the old `keys_bkey_to_ikey` 4
(`keys_bkey_bytes`, `keys_bkey_without_ikey`,
`keys_bkey_ikey_round_trip`, `vectors_keys`) and 2; `strutil` without the
surrogates' limit (ED's second byte up to BF) 5 and 2.

The gate against the candidate (`git:12dd8f7`, step 0's default), on
`2026.4` at `fd7f9e0` (steps 0, 2 and 3 landed): `C BEFORE COMMIT OK (531
s)`, F53 under a load of about 19 to 31; `unit` 392 tests (391 in the
release build); `func` 28; `cross quick` 0 differences (23 workloads, 69
crash cuts, 85 corrupt variants, 2 in turns, 46 budget runs);
`writecheck` 0; `corruptset` 57 copies; `allocfail` 628 runs; `examples`
OK. Java's vectors written again by step 0's harness from the candidate:
all thirteen files equal to the committed ones. No difference remains;
the keys' change does not show in the cross runs, whose workloads' keys
are well-formed (section 4.1).

2026-11-09, step 2's corrupt-set bases (worker t2), on step 0 with 4b
merged (`fd7f9e0`): `CorruptSet.java`'s `found021_11`, the three rows of
`testFound021_11` on `LONG`'s original of seed 1, as the test makes them
(base `found-long-1`, in `quick` too); `corruptset.sh` runs C's
`bergdb-dump` with `-check`, the start's check by node id (005-57), which
Java's `Dump` runs under `-ea`: without it the third copy, the pointer
set to an older top node version, differs (Java refuses at the start, C
starts and a read fails), as step 2's paragraph records from its scratch
tree. `c/readme.md`, section 10, and `before-commit.sh`'s header say so.
The gate against the candidate (`git:12dd8f7`), on step 1's landing
(`b23d24e`): `C BEFORE COMMIT OK (468 s)`, F53 under a load of about 20
to 26; `unit` 392 tests (391 in the release build); `cross quick` 0
differences (23 workloads, 69 crash cuts, 85 corrupt variants, 2 in
turns, 46 budget runs); `writecheck` 0; `corruptset` 60 copies, the three
of `found-long-1` refused by both with the same exception and text;
`allocfail` 628 runs; `examples` OK. Before, on `fd7f9e0`: `C BEFORE
COMMIT OK (567 s)`. No difference remains.

2026-11-09, D7 (worker t5). Section 7's D7, (a), the default, which went
ahead: C forces a new stream file and the directory when it makes the
file, as Java's `FileStream.newFile` does with per-append forcing on or
off (`openForRw`: OPEN, then the directory); the stream's bytes do not
change. `new_file` (`stream.c`), after the old last file's SWITCH force
and the open of the new file, and before its first byte: `plat_force` of
the new file (`PLAT_FORCE_OPEN`, whose comment in `plat.h` says so) and
`plat_force_dir`, then the check that the file is empty, in Java's order.
So every name is durable before its file takes a byte, and no file system
can keep a later name without an earlier one. The forces of the directory
that C made after a new file at a sync (`stream_sync`) and before a cut's
deletes (`stream_pretruncate`) are gone, with `struct stream`'s
`dir_unforced`, as no new name is then unforced (Java forces none before a
cut's deletes or at a close either); a new file counts as forced (Java's
`forcedLength`). The cost: one `F_FULLFSYNC` of the empty file and one of
the directory per new file. Tests, each failing before the change (in a
copy of `c/` with `2026.4`'s `stream.c` and `stream.h`): `t_stream.c`'s
`stream_new_file_forces` (one write of 1,000,100 bytes, six files: for
each "open N OPEN N dir write N", after the old one's SWITCH; 6 OPEN and 6
directory forces; the sync after forces "SYNC 10" only; before, no OPEN
and no directory force, then "SYNC 10 dir"; Java's
`testForcingOffWritesAppends` and the six files of
`testForcingOffForcesBeforeACutDeletes`), `stream_forces` (its seam logs
the writes too: each open followed by OPEN and the directory before the
write, a cut and a sync that force no directory) and `stream_seam`'s count
(4 file forces, 2 before). `stream.h`, `bergdb.h`'s `bergdb_sync` and
`reclaim.c`'s `cut_if_durable`: no directory at a sync.

The power model: `bergdb-power -names reorder`, `power.sh`'s new default
`NAMES=reorder`: as `now` (a new name durable at its creation), and at
each event at which two or more names exist that no force of the directory
has made durable, the image with the newest of them and none of the others
(`reordered_names`); an image that leaves out a name has a gap and counts
as short (`power SHORT`, exit 4). The existing modes cannot show the case:
`now` makes the names durable in the order of their creation, and
`dirforce` all at once at a force of the directory. `-omit newfile`
(`OMIT=newfile`, which sets `reorder`) leaves out a new file's OPEN force
and the force of the directory after it, the negative control. On
`power.sh`'s six workloads, and 1101 with a sync after 2 % of the
transactions in place of 15 %, C without D7 (the copy) has short images
under `reorder` in 1101, 1103, 1105 and the 2 % run (2, 14, 12 and 28;
1102, 1104 and 1106 make no two files between forces of the directory),
and none under `now`; with D7 none in either mode, and no reordered image
at all, as no two names are ever unforced at once. Two of the copy's short
images (1103), started by both dumpers: refused by both with
`BadDirStateException` ("not in a correct state"), the same dump.
`power.sh` with D7, `JOBS=2`, under `nice`: C's images, `NAMES=reorder`,
1101 and 1102: 890 images started and run on by C and Java alike, no
failure (the run stopped at 10 minutes, after these two of its six
workloads, with F53 under a load of 25 to 40; 1101's last comparisons,
from its 537th image, finished by hand with the script's own lines);
Java's images (`JAVAIMG=1`, seeds 17, 19 and 23): `POWER OK`, 147 images
(36 s); `OMIT=newfile`: `POWER CONTROL CAUGHT` in all six workloads (3 to
236 images each, 52 s). `c/readme.md`: section 9, points 3, 9 and 11 (a
new file's OPEN; one difference from Java left), section 10's `power.sh`,
and section 11 without the departure (its points 4 and 5 now 3 and 4).

The gate against the candidate (`git:12dd8f7`), on `2026.4` at `0e4e27f`
(022 merged): `C BEFORE COMMIT OK (376 s)`, F53 under a load of about 15
to 27; `unit` 394 tests (393 in the release build); `func` 28; `cross
quick` 0 differences (23 workloads, 69 crash cuts, 85 corrupt variants, 2
in turns, 46 budget runs); `writecheck` 0; `corruptset` 60 copies;
`allocfail` 628 runs; `examples` OK. No difference remains; D7 does not
show in the cross runs, which compare bytes and files, not forces.

2026-11-09, D6 (worker t4). Frans's decision of 12:25 ("Yes, (a).";
section 7, D6): C's `StreamIoException` carries Java's message, byte for
byte, and the corrupt-stream set fails on any difference of it. (a) The
wrap: `rs_stream_read` (`rstream.c`) keeps the read's text and code and
names the inner exception as the error's cause, a new field of `struct
err` (`err.h`, "" for every other error), as Java's `StreamIoException(e)`
takes `e.getMessage()` and `initCause(e)`; the text began with the inner
name (012-14, section 7.4). `tools/reappend.c` tells a torn last record
by the cause, `EOFException`, where it read the text's prefix; and
`bergdb-scan`'s reason names a failed record read once (it said
`StreamIoException` twice). (b) The inner message: Java's `Db` reads its
stream through `StorageManager` and a `BufferedStream`, whose read
refuses first, whatever the position, a read whose last byte is at or
past the end, "Cannot read N bytes at position P, stream size is S.";
there C gave the text of `FileStream`'s `DbFile` ("Cannot read at spos P,
past the end of a file at S.", where Java's names the file's path). The
new `stream_as_storage` (`stream.h`), called by `db_open`, `sdb_open` and
`replay_open`, makes `stream_read` refuse such a read first, with that
text; a read of 0 bytes before it reads nothing, as Java's; a position
within n of `Long.MAX_VALUE`, where Java's sum wraps and its read goes
on into the ring buffer's bytes, is refused as past the end. The stream
alone keeps `FileStream`'s and `MemoryStream`'s texts, which their ported
tests check. Tests, each failing with its fix taken out: `t_rstream.c`'s
`rs_read_across` (the texts and causes of `MemoryStream`'s
`EOFException` and `ReadBelowFirstPosException`, and `BufferedStream`'s
through a database's stream; 6 checks fail with the old wrap) and
`t_stream.c`'s new `stream_storage` (`BufferedStream.testReadOneBytePastEnd`'s
reads on a memory stream, and a directory with the corrupt set's read of
32 bytes at 2147483808; 10 checks fail without the check). (c)
`corruptset.sh`: the known class gone, a `StreamIoException`'s message
compared as any other; `iotexts.txt` no longer written. `corrupt.sh` and
`cross.sh` count no such class and are unchanged: `corrupt.sh` compares
the exception's name, the status and a failed read's position, and
`cross.sh` the names, and the scans with their error lines' texts set
aside. `c/readme.md`: section 10's corrupt set, and section 11's point
on it (from the 2026.3 port's step 6, merged as `0e4e27f`; point 4 since
D7): no longer a departure; 022-03, section 10, point 5: decided.

The whole corrupt set against the candidate, seed 1, on this tree (on
step 2's bases, `6f91efe`; 248 s, F53 loaded): `CORRUPTSET OK`, 6,250
copies, 2,625 refused by both with the same exception and message, the
10 `StreamIoException` refusals among them (4 flips, 3 headers, 3 nodes:
a top position or a node's pointer far past the end, read as 32 bytes),
3,560 started, 65 with a later read failing alike, 22 of 014-01's case,
the one class still counted as known. Before step 2's bases, on step 0
(`fd7f9e0`) with this change (327 s): `CORRUPTSET OK`, 6,247 copies; and
on `022` at `ecc5319` merged with it, against 2026.3 (166 s): the same.
The merge of the 2026.3 port's step 6 (`0e4e27f`) changes no part that
the set runs. Negative control: the new script with C before D6 (`022`
at `ecc5319`, against 2026.3): `CORRUPTSET FAILED`, 10 differences,
those 10 copies, each a
`StreamIoException`'s text ("EOFException: Cannot read at spos ..."
against Java's "Cannot read 32 bytes at position ..."). `corrupt.sh`
with this change (98 s): `CORRUPT OK`, 144 variants; its first-missing
copy is refused by both with `StreamIoException`, C's text now
`FileStream`'s, "Cannot read at spos 143928, below the first position,
200000.".

The gate against the candidate (`JAVA_REF=git:12dd8f7`), on D7's
landing (`82ff694`), with the 2026.3 port's step 6 merged: `C BEFORE
COMMIT OK (420 s)`, F53 under a load of about 11 to 22; `unit` 395 tests
(394 in the release build), `func` 28; `cross quick` 0 differences (23
workloads, 69 crash cuts, 85 corrupt variants, 2 in turns, 46 budget
runs); `writecheck` 0; `corruptset` quick 60 copies; `allocfail` 628
runs; `examples` OK. The same on the landings that came meanwhile (step
1, step 2's bases, the merge of step 6), 365 to 506 s. No difference
remains.

2026-11-09, the re-pin (worker t6). The candidate pinned again, `main`
at `38a9492b11a1b6fe29b30596ca66a469abbfd611` (13:04, `int.git`'s
`repo-main`): `java-build.sh`'s default. The Core layer's commits since
`12dd8f7`: `ff5fbfa` (020-22, `Db`'s Javadoc), `b8503a3` (021-11:
harness 6.1's full set runs `LONG` too; the sample's configurations, and
so the corrupt set's copies, unchanged), `4ff84fb` (021-12), `f744b7d`
(020-23 V2-1, a test), `e1f9676` (020-23 V2-2, `BufferedStream.append`'s
check after its wait for room: no counterpart, as C has no buffer thread
and one caller, so no append waits while a close begins). Java's vectors
written again from it: all thirteen files equal. The negative control, C
before this entry (the library of `b23d24e`, as at `0e4e27f`) against
the new pin: `C BEFORE COMMIT OK (437 s)` (`unit` 392 tests, `cross
quick` 0 differences, `writecheck` 0, `corruptset` 57 copies,
`allocfail` 628 runs); the whole corrupt set `CORRUPTSET OK` (6,247
copies, step 0's counts); `corrupt.sh` `CORRUPT OK` (144 variants, 83
refused by both, 39 started, 22 with a later read failing): no
difference, as harness 6.1's sample never met 021-12 (its full set on
`LONG` did). (a) 021-12, as `4ff84fb`: `nc_validate_key_node`
(`ncoll.c`, `DbStarter.validateKeyNode`): `kn_validate_stream_node` and,
for a version from before the startup section, no time after the startup
time, with Java's `StreamFormatException` and text ("Key node N at P,
before the startup section, has the time T, after the startup time S.");
called by `validate_node` (the section's nodes, as before), by
`read_version` for each key node version a follow reads during the
reconstruction, and by `canonical_node`, each before the cut back.
Before, C took such a version: the times not increasing gave the
`AssertionError` of the start's check of its nodes (`post_startup_check`,
Java's `Db.checkNodes`), or an abort on an assert of the rerun's put
(`kn_add_klong`, Java's `KeyNode.addKlong`; `dag.c`'s
`append_delete_klong` and `append_klongs`); a time after the startup time
that kept them increasing was started; a time klong made a key klong
whose pointer is `Spos.NULL` gave the check's `AssertionError`. Tests,
each failing before the fix (an `AssertionError`, then an abort):
`t_sdb.c`'s `sdb_found_021_12`, `testFound021_12` on the vectors' stream,
ten copies of versions from before the section, checksums right, refused
with Java's texts or, unchanged, started: those the rerun's follows read
(1357 at 1760, 2595 at 2848, 1359 at 3496) and, the last record's
got-dirty entry of 2595 set to a version the rerun does not reach (as a
touch's entry names one), those `canonical_node` reads (733 at 1008, 735
at 2376); with `read_version`'s call taken out it fails at its first
copy, with `canonical_node`'s at those two. The corrupt set's base
`found-long-3971358` (`CorruptSet.java`'s `found021_12`, the test's three
copies on `LONG`'s original of its seed, in `quick` too): refused by
both; C before differs in all three (`CONTROL=0e4e27f`: the
`AssertionError`, an abort in `kn_add_klong`, the `AssertionError`; no
other base). The third's Java text, `KeyNode.validateStreamNode`'s "Bad
spos of pointer 0 of node K/3a 22807:36536 L" and the node's print, holds
`Object.toString`'s identity hash ("K/d9" in the next run), so no program
gives it; C's text of that check is its own since the port of 2026.2
("Bad spos of pointer, at or before the startup time"), and
`corruptset.sh` counts the pair (`node_text`; `knode.h`, `c/readme.md`,
section 10). (b) V2-1: `t_ncoll.c`'s
`ncoll_link_to_canonical_checks_the_type`
(`testLinkToCanonicalChecksTheType`); C has the check since step 2, so it
passed before, and fails with `nc_link_to_canonical`'s
`nc_check_pointee_type` taken out. (c) 020-22: `bergdb.h`'s "Keys and the
layers above", step 1's from r22b's draft, now follows `Db`'s Javadoc as
landed (a write through the Core can break the Pub API's data; your keys
never read or written by BergDB; an object key's put left out of an
index's scans until written again through the Pub API or the index made
again, a delete an entry that scans skip; well-formed data that BergDB
did not write in its keys; a scan of an index returns only matching
values; Java's rule to write while no `Database` runs, which C's lock
gives).

The gate against the new pin (`git:38a9492`), on `2026.4` at `9b5c244`
(D7 and D6 landed): `C BEFORE COMMIT OK (331 s)`, F53 under a load of
about 28 to 48; `unit` 397 tests (396 in the release build); `func` 28;
`cross quick` 0 differences (23 workloads, 69 crash cuts, 85 corrupt
variants, 2 in turns, 46 budget runs); `writecheck` 0; `corruptset` 63
copies, `found-long-3971358`'s three refused by both, the third's text
counted by `node_text`; `allocfail` 628 runs; `examples` OK. On
`0e4e27f` with this entry, before the rebases: the whole corrupt set
`CORRUPTSET OK` (6,253 copies, the control's counts and these six, 198
s) and `corrupt.sh` `CORRUPT OK` (144 variants). No difference remains.

2026-11-09, D6, `corrupt.sh` (worker t7). Frans's decision of 12:25
(section 7, D6) for the second harness that compares exceptions:
`corrupt.sh` compared a refused start's exception name, the statuses
and a failed read's position, not the messages. It now compares, as
`corruptset.sh` does, the name and message of a refused start (status
1), of a refused directory (status 3: `FileStream`'s exception leaves
Java's `Dump`, and `bergdb-dump` prints "the directory DIR: NAME,
MESSAGE"; not compared at all before) and of a read that failed after
the start (Java's from its stack trace, a `DbFailedException` with its
cause's message), byte for byte, C's cut at its 239 bytes. Java's dumps
run through `CorruptSet -dump`, one at a time, each with its own
standard error (`Batch`'s `Dump` wrote to the JVM's). Both dumpers run
in `OUT` with paths from there, so that `FileStream`'s texts, which name
the directory or a file, are short (with absolute paths C's cut fell
within the first path), and a path names the dumper's own copy,
`v/SEED/VARIANT/a` or `.../b`, the one difference allowed. The first run
(absolute paths, before the rule for the copies' paths): 44 differences,
all directory refusals; 36 the paths alone, and 8 C's own texts, a
directory in place of `bergdb.lock` or of the last file (`lock-dir` and
`last-as-dir` in each base): Java's `new RandomAccessFile(file, "rw")`
(`lockDir`; `FileStreamIo.open`, by `openForRw`) throws
`FileNotFoundException`, "PATH (Is a directory)", where C gave
`IOException`, "Could not lock PATH: Is a directory" and "Cannot open
PATH for writing: Is a directory". Fixed: `plat.c`'s `real_open_rw` and
`plat_lock`'s open give Java's name and text (`plat.h`); test
`t_append.c`'s `append_dir_open_is_a_directory` (both cases, nothing
left open, then the stream opened again), 4 checks failing before the
fix. No
class of messages is counted as known: every message is Java's, C's cut
at 239 bytes where Java's is longer ("Existing files in dir ...", whose
positions at the end are past the cut). And 014-01's zero fill is
counted as known as `corruptset.sh` counts it (both refused with the
same status, the two directories alike after the starts), where the
script failed on it: `HEADERS`'s flip of a record size's low byte, as
022-01's step 2 found it on bases 501 and 503 ("a matter for both"). The
variants of random bytes differ from run to run: `last-longer`'s record
size is random, refused when negative, zero-filled (up to 2 GB a copy)
and started when positive, so the four bases split between refused and
started anew each run; each outcome is compared as it comes, and no
class is counted by variant.

The runs, F53 under a load of about 25 to 31, `nice -n 10`, against the
pin (`git:38a9492`) on `e4be144` with this change: the four bases
`CORRUPT OK`, 144 variants (84 refused by both, 38 started, 22 with a
read failing later; 106 messages compared: 40 refused starts, 44
refused directories, 22 failed reads; 0 differ; 110 s); `HEADERS=2` on
501 and 503, `CORRUPT OK`, 200 variants, 121 messages, 0 differ, 2 of
014-01's case (96 s); `HEADERS=2` on 502 and 504, `CORRUPT OK`, 200
variants, 127 messages, 0 differ, 3 of 014-01's case (285 s). Negative
control, the new script with C at `e4be144` (`CBUILD=`): `CORRUPT
FAILED`, 8 differences, the 8 `FileNotFoundException` refusals.
Against this pin no other text differed, the start's and node
validation's among them (`DbStarter`'s "startup error, node ... not
found", checksums, "Bad lastByte"), which Java's 021-15 changes and
worker t8 ports. `c/readme.md`, section 10's `corrupt.sh`.

The gate against the pin (`git:38a9492`) on `e4be144` with this change:
`C BEFORE COMMIT OK (455 s)`, F53 under a load of about 25; `unit` 398
tests (397 in the release build); `func` 28; `cross quick` 0
differences (23 workloads, 69 crash cuts, 85 corrupt variants, 2 in
turns, 46 budget runs); `writecheck` 0; `corruptset` 63 copies;
`allocfail` 628 runs; `examples` OK. No difference remains.

2026-11-09, 021-15 and 021-14 (worker t8). The candidate pinned again,
`main` at `629e1c6d79d937b487b7a955143dda145c4b380a` (14:40), the head
when both of Java's commits had landed: `6b58e8c` (021-15) and `78c6718`
(021-14); `java-build.sh`'s default and `c/readme.md`'s "Which Java".
Java's vectors written again from it: all thirteen files equal. The
stream's bytes do not change. (a) 021-15, as `6b58e8c`: the texts of a
start's refusals and of the key nodes' checks name a node as Java's new
`Node.name` does, by its kind, id and position, "key node 22807 at
36536" (`node_kind`, `node.h`), where Java's printed `KeyNode.toString`,
with `Object.toString`'s identity hash, or the whole node, and C's were
its own. `kn_validate_stream_node`: "Key node I at P with size 0.", "Bad
spos of pointer N of key node I at P: S." and "..., at or before the
startup time T.". `kn_check` and `kn_check_max` take a buffer
(`KN_TEXT`, now 200 bytes) for Java's `AssertionError` texts ("Bad spos
of pointer ...", "Bad reference of pointer N of key node I at P: R.",
"Overfull node, size=Z, maxNodeSize=M, key node I at P.", and "Time not
increasing, ..." with its numbers), `NULL` for the asserts' short texts;
the start's check of its nodes (`post_startup_check`) and the put's
`assertOk` (`dag.c`'s `assert_ok`, which added ", key node I" to C's
short text) give them. `starter.c`'s checks, made functions of
`starter.h` as Java's `DbStarter` has them: `sr_validate_node` ("Bad
spos of KIND I at P."), `sr_check_primordial_transaction` ("Expected
TopNode, got KIND I at P.", "Expected KeyNode, got ..."; C named the
type's number), `sr_check_stream_pointers` ("Unexpected stream pointer
S, index N of KIND I at P."; C named the id) and
`sr_check_value_nodes_have_spos` ("value node got no spos during
startup, value node I at P."), which `post_startup_check` now runs over
every key node before their checks, in Java's order
(`checkThatValueNodesHaveSpos`, then `Db.checkNodes`). (b)
`corruptset.sh`'s known class `node_text` is gone with its notes (the
script's header, `knode.h`, `c/readme.md`, section 10): these texts are
compared as any other. Section 11 had no departure for them. (c) 021-14,
as `78c6718`: C refused a read near `Long.MAX_VALUE` already (D6's
`stream_as_storage`; the memory stream's check without the sum; a
directory's read past its last file). The storage's check is now
Java's, `pos > length - n`, and a read of 0 bytes returns after it: the
one change of outcome, a read of 0 bytes at `Long.MIN_VALUE`, which the
wrapped sum refused, reads nothing, as Java's now. The write buffer's
check without its sum (it wrapped, `-fwrapv`, and the read was refused
by the files, "the stream is empty"; now past the buffer's end).
`ns_bad_read_size` (`nstream.h`, `NodeStream.checkReadSize(pos, size,
length)`) refuses a position at or past the length first:
`rs_get_spos` wrapped near `Long.MAX_VALUE` and the check passed,
unreached, as the read of the size field refuses such a position first,
in C as in Java.

Tests, each failing with its fix taken out (a copy of `c/` with the old
texts and checks, 8 tests and 30 checks failing in it): `t_knode.c`'s
`knode_node_texts_same_in_every_run`
(`KeyNodeTester.testNodeTextsSameInEveryRun`, and the bad reference's,
the overfull node's and `Node.name`'s texts) and
`knode_validate_time_text` (`check`'s text with a buffer); `t_sdb.c`'s
`sdb_found_021_12` (the third copy's text, as `testFound021_12` checks
it), `sdb_starter_node_texts` (`DbStarter.testCheckStreamPointersOfKeyNode`
and a top node's pointer, `validateNode`, `checkPrimordialTransaction`,
`checkThatValueNodesHaveSpos`) and `sdb_section_pointer_to_a_vpos` (a
section's key node pointing to 2001, its checksum right, on the
vectors' stream: refused at the start; written as a directory and
started by Java's `Dump` and C's `bergdb-dump`, both refuse it alike,
"Unexpected stream pointer 2001, index 1 of key node 2599 at 4064.");
`t_dag.c`'s `dag_assert_ok_text`; `t_stream.c`'s `stream_storage` (the
read of 0 bytes at `Long.MIN_VALUE`); `t_rstream.c`'s
`ns_read_size_near_max_value` (`NodeStreamTester.testReadSizeNearMaxValue`).
`t_stream.c`'s `stream_read_past_end_near_max_value`
(`BufferedStream.testReadPastEndNearMaxValue` and `StreamContract`'s two
new reads, on a memory stream and on directories, each alone and as
storage) passes before too. C has no `StrictStream` or `DummyStream`.

The whole corrupt set against the new pin, seed 1, `nice -n 10`, F53
under a load of about 17 to 29: `CORRUPTSET OK`, 6,253 copies (183 s),
2,628 refused by both with the same exception and message, 3,560
started, 65 with a later read failing alike, 22 of 014-01's case, now
the only class counted as known. Negative control, the quick set with C
before this entry (`CONTROL=3aa9671`): only `found-long-3971358/2`
differs, C's "Bad spos of pointer, at or before the startup time"
against Java's "Bad spos of pointer 0 of key node 22807 at 36536: -1, at
or before the startup time 470.". `corrupt.sh`: `CORRUPT OK`, 144
variants, 105 messages compared, 0 differ (85 s). Its first run failed on
one variant, 503's `last-longer`, whose random record size made a zero
fill to a stream of 2,146,064,565 bytes: C started it, Java's dumper
(`-Xmx2g`) threw `OutOfMemoryError` reading that record at the start; a
limit of the harness's heap, not of either Core.

The gate against the new pin (`git:629e1c6`), on `2026.4` at `3aa9671`
(corrupt.sh's messages landed) with this entry: `C BEFORE COMMIT OK (285
s)`, F53 under a load of about 21 to 23; `unit` 404 tests (403 in the
release build); `func` 28; `cross quick` 0 differences (23 workloads, 69
crash cuts, 85 corrupt variants, 2 in turns, 46 budget runs);
`writecheck` 0; `corruptset` 63 copies, `found-long-3971358`'s three
compared as any other; `allocfail` 628 runs; `examples` OK. No
difference remains. The pin also brings the Core's other changes since
`38a9492`, which no harness run here showed and which this entry does
not port or check in C:
020-27's C1 (`GetMany.GetN` and `PrefixN` of a count of 0, `3849076`),
C2 (`eod()` also before the first transaction, `61fbcc2`) and C3
(`DbBuilder.cacheSizeIndicator()` below 1 refused, `984b254`); 021-13
(`Db.getTrans` waits for the writer, `1ad85d3`; C has no writer
thread); 020-24's U1-12 (`LookupTimeNotAvailableException`'s text,
`5df48be`; C has no such text). After the pin, `main` took 020-23's Z1
(`7ad5019`, `DbClock.currentTime()` with a clock that goes back).

2026-11-09, `main` at 345fdba (worker t9). The candidate pinned again,
`main` at `345fdba81a7bcd3075c660a91906068b57eb01b5` (15:22), the head
when the pin was moved: `java-build.sh`'s default and `c/readme.md`'s
"Which Java". Java's vectors written again from it: all thirteen files
equal. The stream's bytes do not change. Every Core commit that C had
not checked, in the last pin and after it, with C's outcome. (a)
020-27's C1 (`3849076`): `getmany.c`'s `get_n_handle` and
`prefix_n_handle` stop at their count, none for 0 (`GM_STOP`), where
`GetN(0)` gave every pair. `bergdb_range.max_count` 0 stays the field's
"no count", as before, so the API's reads do not change (`bergdb.h`: a
read of no pair needs no call). `PrefixN`'s copy of its prefix:
`gm_prefix_n` keeps the caller's array during the read, as `gm_endpoint`
does, and `bergdb_get_many` makes the segments at the call. Test
`t_getmany.c`'s `gm_at_most_n` (`DbTesterJavadoc.testGetManyAtMostN`: 0,
1, 3, 5 and 7 of 5 keys, and `GetOne`). (b) C2 (`61fbcc2`):
`dag_get_many` calls `eod` for a lookup time with no state, before the
first transaction, as `Dag.getMany` now does; `bergdb_many.eod` is true
there. Tests `gm_eod_once_at_the_end` (`testEodOnceAtTheEnd`) and
`f_api.c`'s `api_create_and_read`, a read at 999 before the creation at
1000. (c) C3 (`984b254`): `db_open` refuses a cache size indicator below
1 with `DbBuilder.cacheSizeIndicator`'s `IllegalArgumentException`, "Bad
cacheSizeIndicator: N.", where C gave `Cache3`'s `AssertionError`
(`BERGDB_ARG` both). Test `f_settings.c`'s `settings_open_checks`
(`testBuilderCacheSizeIndicatorBelowOneRefused`: 0, -1 and `INT64_MIN`
refused with the texts, 1 taken and the database working). (d) 021-13
(`1ad85d3`): nothing for C. Java's writer thread sets a record's
positions before it appends the record, and a reader's `getTrans` could
meet it in part; C appends a record whole within `bergdb_execute`,
before any other call, and `bergdb_get_trans` from a callback is
`BERGDB_STATE` (one caller, no thread: `c/readme.md`, section 8). (e)
020-24's U1-12 (`5df48be`): C's text of a lookup time before the first
available one was its own since 2026.2's port, "Cannot lookup at time T,
the first time available for lookup is F.", without Java's times in UTC;
now Java's, with its parenthesis closed, "Cannot lookup at time T (UTC):
the first time available for lookup is F (UTC).", in `db.c`'s
`lookup_refused` for `getOne` and `getMany`, with `DbUtil.dbTimeToUtc`
ported as `clk_time_to_utc` (`clock.c`: Java's division toward zero, the
proleptic Gregorian calendar, the year of the era, a '+' above 9999).
Tests `t_clock.c`'s `clock_time_to_utc` (`DbUtil.testDbTimeToUtc`'s
three times and twenty edges, with the strings Java's `DbUtil` gave for
them, from `Long.MIN_VALUE` to `Long.MAX_VALUE`) and `t_reclaim.c`'s
check of both texts behind a cut (10 checks in 2 tests failing with the
old text). No harness compares the text (the dumps print "unavailable").
(f) 020-23's Z1 (`7ad5019`): `dbclock_current_time` takes the clock's
time at most as `DBCLOCK_LAST_USER_TIME` and never below the last time
it gave. Tests `t_clock.c`'s `clock_dbclock_clock_goes_back`
(`testClockGoesBack`) and `clock_dbclock_current_time_leaves_the_margin`
(`testCurrentTimeLeavesTheMargin`), and `f_settings.c`'s
`settings_current_time_with_a_clock_that_goes_back`
(`PubTesterJavadocRest.testCurrentTimeWithAClockThatGoesBack` through
the API). Z3 (`15bd3ec`, Javadoc): `bergdb.h`, section F, says that only
an open that creates a database reads the clock; `f_settings.c`'s
`settings_open_with_the_clock_out_of_range`
(`testStartWithTheClockOutOfRange`) passes before too, as Java's. (g)
021-16 (`e5b552c`): nothing to change. Java's walks of a long key's
levels were recursions; C's have none: the start's check walks the node
table, `dag_dirty_node_bound` keeps its work in an array,
`bergdb_debug_check` has a stack of its own, and the reads are loops;
`Dag.visitMemoryNodes` and `DagNodeIterator` have no counterpart.
`f_api.c`'s `api_long_keys` (`DbTesterLongKeys`' two tests through the
API, under the sanitizers: a key of 200,000 bytes, a restart, reads,
both scans, the check and a longer put; a key of 1,000,000 bytes after
one of 100,000) passes before and after. Its Q2 (`0dc79be`): the rerun's
`node_created` (`starter.c`) scanned the record for each node it made,
as `StoredTrans.findNode` did; now `sr_find_node` (`starter.h`), a scan
up to 64 nodes, above it a map (`lmap`) from id to the first node, made
at the first call of a record's rerun. Test `t_sdb.c`'s `sdb_find_node`
(`StoredTrans.testFindNode`: 200,000 lookups among 100,001 nodes under 2
s, the first of two, none, another record, 2, 64 and 65 nodes alike),
failing with a scan only (23.6 s in the release build). (h) The rest:
020-27's Javadoc of the Core API (`5c6a716`, `50e3c5b`): `bergdb.h` says
each already; K1 and K2 (`2c00faf`): `bergdb.h`'s "Keys and the layers
above" takes their words (K3's sentence is C's own: the lock); 020-25's
J4 to J7 (`09ad69c`, `801f602`, `fb6f33a`), 020-23's Z2 (`e85e021`),
021-17 (`7eb2852`, a comment in `Reclaim.java`) and 020-24's U6
(`2ab9b7d`): the Pub layer's, nothing for C. Each test above fails
before its fix but where said (shown on a copy of `c/` with the old
`getmany.c`, `db.c` and `clock.c`, and with the scan only). (i)
`corrupt.sh`: Java's dumper runs with `-Xmx4g`. `last-longer`'s random
record size made a zero fill to 2,146,064,565 bytes on 503 in worker
t8's run, and a start reads the zero-filled record whole, one array of
up to `StoredTrans.MAX_RECORD_SIZE`, 2^31 - 9 bytes; with `-Xmx2g`
Java's `Dump` threw `OutOfMemoryError` (`NodeStream.TransIterator.next`,
reproduced on base 503 with that size), where C started it. With
`-Xmx3g` that copy starts, a resident size of 2.3 GB, and with `-Xmx4g`
one of 2^31 - 9 bytes; both dumps equal C's. The script's header says
so.

The gate against the new pin (`git:345fdba`), on `2026.4` at `38e8b4e`
with this entry: `C BEFORE COMMIT OK (310 s)`, F53 under a load of about
15; `unit` 410 tests (409 in the release build); `func` 31; `cross
quick` 0 differences (23 workloads, 69 crash cuts, 85 corrupt variants,
2 in turns, 46 budget runs); `writecheck` 0; `corruptset` 63 copies;
`allocfail` 628 runs; `examples` OK. The whole corrupt set, seed 1,
`nice -n 10`: `CORRUPTSET OK`, 6,253 copies (120 s), 2,628 refused by
both with the same exception and message, 3,560 started, 65 with a later
read failing alike, 22 of 014-01's case. `corrupt.sh`, `nice -n 10`:
`CORRUPT OK`, 144 variants, 105 messages compared, 0 differ (85 s;
`last-longer` refused on 503 and 504, its sizes negative this run,
started on 501 and 502). No difference remains. After the pin, `main`
took `0d85f28` (021-17's R17-1) and `dc3ca71` (its item), the Pub
layer's alone, which the harness does not compile (15:27 to 15:31).

2026-11-09, step 5 (worker t10). The documents, written before the
release candidate, so that at about 20:00 only its hash and its last
changes remain. `c/readme.md`: "Which Java" says that C is a port of
release 2026.4 and that until the tag it follows the release candidate,
pinned as `java-build.sh`'s default `JAVA_REF=git:HASH`; the pin is one
indented line of that paragraph, today `main` at `345fdba` (15:22), and
its hash is in no other place of the file, so that the session's re-pin
to the candidate changes that one line (and `java-build.sh`'s default);
once tagged, `JAVA_REF=2026.4` and the release's source zip; the 2026.3
port's state, `c/` at `main`'s `142dabc` (`int.git`'s `022` at
`342dcb2`); the interim sentence "On the way to 2026.4" gone. The vectors
paragraph: the pin's thirteen files, the new kinds `utf8` (`strutil.txt`)
and `bkey2ikey` (`keys.txt`). Section 1: the gate about 5 to 9 minutes
under load (285 to 567 s at this item's landings). Section 8: a count of
0 is none. Section 9, point 11: Java's `FileStream`'s forces, 2026.3's,
which the candidate keeps (no force changed in `FileStream` since
2026.3). Section 10: 022-04 named; `corrupt.sh`'s `-Xmx4g` and counts; the
corrupt-stream set's copies from the pinned Java, `quick`'s 63 copies and
the whole set's 6,253, 014-01's zero fill its one known class. Section 11:
the Java that C follows; a new point 4, a count of 0 is no count
(020-27's C1: C's API cannot say Java's `GetN(0)`); D7's and D6's former
departures in a closing paragraph. Sections 9 and 11 were otherwise as D7
and D6 left them, and consistent. The report, 022-04
(`04-report-2026-4.md`), in 022-03's form, with section 8 (the candidate)
and section 9 (the long runs, `runs-2026-4.sh`) left to fill, and the
open points for Frans. Section 7 here: D1 to D7 as taken. 022's readme:
022-04 in `Files`, and 022-02's decisions D1 to D7. No file of `c/` but
`readme.md` changed, so the gate was not run (022-01, section 5); the
gate of the pin of 15:22, on `ddd75cc`, stands.

2026-11-09, 021-18, `main` at e875a34 (worker t11). The candidate pinned
again, `main` at `e875a34496aa50a2b1f2193c1fe3bddfdb6fc6a9` (17:18), the
head when the pin was moved, the first `main` with 021-18 (`dff9a6a`,
`1ccc242` before its rebase) and 021-19 (`977b599`, `f134914`):
`java-build.sh`'s default and `c/readme.md`'s "Which Java". C had to
follow 021-18 in the same landing: with C's fix, `cross.sh quick`
against the pin of 15:22 gave 4 differences, `coresame-n1500`'s and
`coresame-plain-n1500`'s dumps, each by both dumpers, at `range
at=latest start=/k/1 incl=1 fwd=1 stop=prefix10` (Java 0 pairs, C 10:
the dumper's prefix of half a sampled key, `/k/1`, is itself a key), and
against Java with 021-18 (a tree of `main` at `e3a4734` with `1ccc242`
and `f134914` applied) 0 differences. Java's vectors written again from
the new pin: all thirteen files equal. The stream's bytes do not change.
Every Core commit since `345fdba`, eleven, with C's outcome. (a) 021-18
(`dff9a6a`): `GetMany.Prefix` and `PrefixN` add the prefix's own key,
where they stopped at it (`Keys.isPrefix` is a strict prefix), so that a
read from the prefix, inclusive, gave no pair when the prefix was a key,
and a backward one left it out. `getmany.c`'s `has_prefix` (Java's
`GetMany.hasPrefix`: `keys_is_prefix` or `keys_are_equal`) decides in
`prefix_handle` and `prefix_n_handle`, so also `bergdb_range.prefix`
(`api.c` gives it to `gm_prefix`) and the dumper's `prefix10`
(`gm_prefix_n`). `bergdb.h`'s point 1 of the stop conditions says it,
where it said that a key equal to the prefix stops the read;
`examples/get_many_prefix.c`'s comments too (its output is unchanged:
`/user/1/` is no key; a prefix `/user/1` from `/user/1` inclusive now
gives 5 pairs, exclusive 4, checked with a program of the API).
`Keys.isPrefix` stays strict, and so does `keys_is_prefix` (the vectors'
`isprefix`). Tests: `t_getmany.c`'s `gm_prefix_has_the_prefix_key`
(`DbTesterGetMany.testPrefixHasThePrefixKey` on `mdb`: nine keys around
a segment of 7 bytes and the empty key, twelve prefixes, `Prefix`,
`PrefixN` of 100 and 1, exclusive, backward, at node sizes 30 and 8),
`f_api.c`'s `api_prefix_has_the_prefix_key` (the same through
`bergdb_range`'s prefix and `max_count`), and `mdb_model`, whose
prefixes are now also a key's own (the start's) and whose model takes
the prefix's own key; each failing before the fix (90 checks, 45 and
1,449). (b) 021-19 (`977b599`): Javadoc of `Kvt.time`, `GetData.kvTime`
and `tpos`, the time of a key node entry, not of the write: `bergdb.h`'s
`bergdb_one.time` and `tpos`, `bergdb_kvt.time` and `bergdb_many.kvts`
take its words; `tpos`'s follow back at the step's time less one "while
that time can be read". Test `f_api.c`'s
`api_kv_time_is_the_entrys_time`
(`DbTesterJavadoc.testKvTimeIsTheEntrysTime`: 27 keys of one byte, then
a 28th, all 28 read the second's time, 27 not their write's; the write's
time by `bergdb_get_trans`), passing before, as Java's. (c) 020-24's
U8-11 (`7e790c2`): `FileStream` refuses a path that exists and is not a
directory before the lock, IOException "Directory P could not be opened:
it exists and is not a directory."; `plat_mkdirs` gives that text, where
C's own was "Not a directory: P". Test `t_append.c`'s
`append_dir_mkdirs`, its text and the file unchanged, failing before.
(d) U8-9 (`8ba0692`): `DbFile.append`'s text of a file that someone else
changed, "File F is not of expected length (N), but M bytes. Was it
modified by someone else?" (it had "(N),but" and "Was is"); C gives
Java's text, naming the file, where C's own named the directory. Test
`append_dir_refusals`, its whole text, failing before. Its other parts,
Javadoc and `pub.util`'s `Job`: nothing for C. (e) 020-24's U9
(`2b1300a`): the Core API's Javadoc as an embedded key-value store, no
change of behaviour. `bergdb.h` takes U9-4 (section E: every key that
starts with 01 25 is BergDB's in every database, and the library writes
some itself; a range returns them, the counters count them, a stop
function can skip them), U9-9 (`bergdb_stored.values`: a delete of a key
without a value is not listed, a reclaim step lists what it copied) and
U9-10 (`bergdb_stats`' `transaction_count` and `kv_count`); its other
parts `bergdb.h` says already (U9-12: a delete does not replace a put;
U9-5's keys, section E) or are Java's (threads, `GetMany`'s one call).
Four of its five tests ported through the API, each passing before, as
Java's: `api_keys_and_values` (`testKeysAndValues`: nineteen keys in the
unsigned order of their bytes, both ways, the empty key, a key of 3,000
bytes, the empty value, a NULL value refused),
`api_core_writes_bergdbs_keys` (`testCoreWritesBergDbsKeys`:
`/#i/-dummy` of 200 kB and reclaim's settings, 3 transactions, a stop
function that skips 01 25), `api_counters_and_listed_deletes`
(`testCountersAndListedDeletes`, the restart through a directory) and
`api_optimistic_transactions` (`testOptimisticTransactions` without its
virtual write hash: C's API has no `addReadHash` or
`addVirtualWriteHash`); `testGetManyDefaultsAndOneCall` has no
counterpart (`bergdb_range_init`'s defaults are checked by
`f_settings.c`; a read context serves one call at a time). (f) 020-28
(`50caeb0`): the encryption out of 2026.4's API, and `Db.startInner`'s
refusal of bad magic bytes a `StreamFormatException` with the
`BadMagicBytes` as its cause, where it was the Pub API's `BadCryptoKey`,
with a new text: "Invalid magic bytes in stream: the stream is not a
BergDB stream, or it is damaged; or an earlier release of BergDB, 2026.3
or before, encrypted it, and this release cannot read it: it has no
encryption (bergdb 020-28). The start has written nothing." The corrupt
set and `corrupt.sh` compare it, so C had to follow in this landing:
`starter.c`'s `sr_bad_magic_bytes` (`starter.h`) gives that name, text
(250 bytes, cut at C's 239) and cause, for the start and for the
replay's start (`replay.c`, which gave the name `BadCryptoKey` to the
storage's text); `bergdb.h`'s `BERGDB_FORMAT` says it. Tests `t_sdb.c`'s
`sdb_refusals` (the name, the cause, the text cut at 239 bytes),
`t_replay.c`'s `replay_refusals` and `f_start.c`'s `start_refusals`,
each failing before (3, 3 and 1 checks). The rest of 020-28
(`DbBuilder.createdTxt`, `SalsaStream`'s key line, the Pub API's refusal
of a database that an earlier release encrypted): nothing for C, which
has no encryption and writes no `created.txt`. (g) Nothing for C:
006-18-03 (`aef43ff`: `BufferedStream`'s wait statistics without
`java.lang.management`; C has no write buffer thread and no such
statistics), 020-24's U9-13 (`fdebb8a`: test methods made
package-private, Javadoc escapes), U7-2 (`869d2e3`: `SalsaStream`'s
appends) and U7-7 (`9ebffa5`: `BadCryptoKey`'s text with a crypto key; C
has no encryption), U4 (`e0ca4c2`, `pub.util`'s `JobStatus` Javadoc).

The gate against the new pin (`git:e875a34`), on `2026.4` at `391c3cf`
with this entry: `C BEFORE COMMIT OK (276 s)`, F53 under a load of about
19; `unit` 411 tests (410 in the release build); `func` 37; `cross
quick` 0 differences (23 workloads, 69 crash cuts, 85 corrupt variants,
2 in turns, 46 budget runs); `writecheck` 0; `corruptset` 63 copies;
`allocfail` 628 runs; `examples` OK. The whole corrupt set, seed 1,
`nice -n 10`: `CORRUPTSET OK`, 6,253 copies (156 s), 2,628 refused by
both with the same exception and message, 3,560 started, 65 with a later
read failing alike, 22 of 014-01's case. `corrupt.sh`, `nice -n 10`:
`CORRUPT OK`, 144 variants (83 refused by both, 39 started, 22 started
with a read failing later), 105 messages compared, 0 differ (127 s),
among them the 8 refusals of bad magic bytes (`meta-last-garbage` and
`meta-last-zero` on the four bases) with 020-28's name and text. No
difference remains. Java's build at the pin has 192 source files, one
fewer (020-28's `BadCryptoKey`); the harness's Java compiles against it
unchanged.

2026-11-09, 022-06, u1, eviction (worker f4). Two faults of C's own
eviction that the black-box user u1 found (022-06-1, U1-3 and U1-4),
fixed in `evict.c`, `db.c` and `api.c`; the record is
`06-user-apps/u1-eviction.md`. Eviction never writes, so the stream's
bytes do not change; what is pinned or detachable, and the meaning of
`bergdb_stats`' resident and pinned bytes, do not change either. U1-3: a
transaction refused before its go point (`BERGDB_LIMIT`, `BERGDB_RERUN`,
`BERGDB_NOMEM`) left what its warmup had loaded resident until a later
call evicted it: every put key's path and present value, 10.2 MB over a
budget of 100 kB in u1's `budget_after_refusal.c`, still there after a
sync. `db_execute` now evicts at each refusal's exit (`refused()`), as at
the end of a commit. Java's warmup loads wake its eviction thread
(`Eviction.afterLoad`, not paced), which evicts to the trigger however
the transaction ends. The reads had the same gap: `bergdb_get_one` and
`bergdb_get_many` now evict at their end when refused too (NOMEM, a stop
function's answer out of range). U1-4: under a budget below what must
stay, the trigger was the floor plus the gap between the watermarks.
That gap is one byte at a budget of one byte, so each pair that a getMany
loaded swept the whole node table, which grows with D, and a full scan
was quadratic in its keys. Now the margin over the floor is the gap or
the node table's own bytes, whichever is more (`sweep`'s `ev->trigger`
and `call_trigger`), so the sweeps' work is linear in the bytes loaded.
Java's trigger has the same one-byte gap, but each batch is bounded
instead (015-67: 4,096 handles, 65,536 under pressure, 2 ms) and runs on
its own thread; this is read from the code, not run. Tests in
`t_evict.c`, each failing before its fix:

* `evict_after_refused_transaction`: 876,896 resident bytes after each
  refusal against a trigger of 100,000; now 60,104.
* `evict_after_refused_read`: 500,738 after a refused getMany, and
  getOnes refused by NOMEM over the trigger; now 648.
* `evict_alloc_failures`: a new check after each NOMEM refusal; before,
  465 of 953 refusals failed it.
* `evict_scan_is_linear`, using a new counter, `ev.examined`, of the
  slots the hand looked at, at a budget of one byte: 512,000 slots in
  1,000 sweeps for 1,000 keys and 8,192,000 in 4,000 sweeps for 4,000
  keys; now 26,624 in 52 and 110,592 in 54.

`evict_twins`' and `evict_accounting`'s bound on the resident bytes over
the pinned ones is now the budget or the table's bytes, whichever is
more. u1's `evict_scan` with 8,000 keys: 0.214 s before, 0.015 s now, at
a budget of one byte; 16,000 keys 0.032 s.

The gate on `2026.4` at `d51d65d` with this change: `C BEFORE COMMIT OK
(533 s)`, F53 under a load of about 9 to 12; `unit` 519 tests (518 in
the release build); `func` 44; `cross quick` OK (23 workloads, 69 crash
cuts, 85 corrupt variants, 2 in turns, 46 budget runs); `writecheck` 0
errors; `corruptset` 63 copies; `allocfail` 628 runs; `examples` OK.

2026-11-09, 022-06, docs (worker f3). The new users' findings that are
C's own words or small faults (06-user-apps/fixes.md, section 1). Four
changes of behaviour, each with a test that fails before it: U2-10,
`bergdb_open` gives `BERGDB_IO` for a read below the stream's first
position (a front file deleted by hand), Java's `StreamIoException`,
where it gave `BERGDB_NOT_AVAILABLE` (`f_start.c`'s
`start_files_of_the_directory`, which also checks U2-11's words); U2-14,
the test clock with `clock_ctx` NULL refused with `BERGDB_ARG` at the
open, where the creation dereferenced NULL (`f_settings.c`'s
`settings_open_checks`); U2-13 and U1-5, `bergdb_stats.pinned_bytes`
counts each object once (a pinned node's handle that its pinned parent
holds was counted twice: 6,552 pinned against 6,032 resident) and leaves
out the written values that pinned key nodes hold, which a sweep lets go
(10.2 MB pinned after a refused transaction's warm-up, 156 KB after the
next read): `evict.c`'s `pinned_of` (`f_budget.c`'s
`budget_pinned_within_resident`). Words, each checked against Java's
Core, which does the same: `bergdb.h` for U2-5, U2-7, U2-9, U2-11,
U2-12, U2-16, U3-3 to U3-7, U1-6, U1-7, U1-9 and U1-10; `readme.md`,
section 9, point 6 for U2-15 (a torn record is zero-filled, not cut
off), points 1 and 10 and section 8; `cache_size_indicator` names the
pinned bytes as what must stay, with f4's margin over them (above). A departure kept, by the session's
default (worker t12's finding): `bergdb_close` gives `BERGDB_IO` also
after a call has reported the storage's failure, where Java's `close()`
returns normally since 019-09; `bergdb.h`'s "Java's close() does not
report it" was older than 005-73 and 019-09 (`readme.md`, section 11,
point 5). Proposed to Frans, not made: a read-only open, a buffer size
setting, a close with an error text (fixes.md, section 1.3). The gate
against `git:e875a34`, on the tree of this entry rebased on `448ca60`:
`C BEFORE COMMIT OK (459 s)`, `unit` 521 tests, `func` 46, `cross quick`
OK (23 workloads, 69 crash cuts, 85 corrupt variants), `writecheck` 0
errors, `corruptset` 63 copies, `allocfail` 628 runs, `examples` OK. No
difference remains.

2026-11-09, the candidate, part 1 (worker t17). The Core commits on
`main` after the pin (`e875a34`) at 17:40, five, each with C's outcome;
the pin stays at `e875a34` until the candidate, as no harness compares
what they change. (a) 021-20 (`225d936`, 020-24-10's U10-1): Java's
`FileStream.checkDirectory()`, before each new file, each delete of a
cut and each reopen of a file after an interrupt, fails the stream if
the directory at its path is no longer the one that it locked, by its
file key, with IOException "Directory P is no longer the database's
directory: it was deleted, moved or replaced while the database had it
open. Nothing more is written there."; and the JVM's set of locked
directories holds each one's real path too, so that a start at the path
is refused while the old stream is open. C had the fault, across
processes and within one: it makes and deletes its files by name in the
directory's path, so a database whose directory was deleted made its
next file in a new database's directory at the path, and broke it, or
deleted that database's files at a cut. Now `stream.c`'s
`check_directory`, Java's, before `new_file` (after its "Illegal state"
check and before the switch force, as Java's `newFile`) and before each
unlink of `stream_pretruncate` (as `DbFile.delete`), with Java's text;
the identity is `plat_dir_key` (`plat.c`: stat's device and inode,
following a link as `Files.readAttributes`), taken at the open for
writing before the lock, as `lockDir` takes `lockKey(dir)` (a stat that
fails there: Java's `NoSuchFileException`, the path). C reopens no file.
Java's set of paths is the JVM's, and C has no global state (P9;
`readme.md`, section 9, point 10), so an open at the path is not refused
within the process, as neither refuses one of another process;
`bergdb.h`, section G, `readme.md`, section 9, point 10, and section
11's opening say so. Tests, each failing before (on a copy of `c/` with
the old `stream.c`): `t_append.c`'s `append_dir_replaced_no_new_file`
(`FileStream.testNoNewFileInAReplacedDirectory` without its refusal in
the JVM: the text, nothing made in the new directory, the stream failed,
the path open again after the close) and `append_dir_replaced_no_delete`
(`testNoDeleteInAReplacedDirectory`: the new directory's file of the
same name kept), and `f_durable.c`'s `durable_directory_replaced`
(`PubTesterJavadocNewUsers.testDirectoryDeletedWhileTheDatabaseRuns`,
the new database opened in the process: the old one's sync
`BERGDB_FAILED` with the cause's text, as far as C's 240 bytes leave
it, its close `BERGDB_IO`, the new one's transaction whole at a restart
and none of the old's; before, that restart was refused, "Bad size of
file .../00000000000000.bergdb, should have been a multiple of 100000,
but was 520."; then `testNewDatabaseWhereAStoppedOneWasDeleted`'s case,
closed, deleted and created again, which passes before too: C has no
`stop()`, and its close returns after its last write). (b) U10-3
(`d10bcce`): nothing for C. Java's `BufferedStream` kept its ring buffer
of 10 MB in a closed `Database` that the application still referenced;
C's write buffer is freed by `bergdb_close` with the handle
(`stream_close`), and no closed handle is left (012-13, Q2). (c) U10-5
(`49c2db9`): Java's `createDirIfNeeded` threw "Directory P could not be
created." when `mkdirs()` returned false because another thread had
just made the directory; now only if it is then not a directory, and
the lock refuses the others. C's `plat_mkdirs` took `EEXIST` at each
level already, so several processes' opens of a new directory were
refused by the lock only; now it takes Java's rule whole: after its
`mkdir`s, whatever they met, it refuses only if the path is then not a
directory, with Java's text, where C's own added `strerror`'s reason and
took `EEXIST` also for a file made at the path. Tests: `t_append.c`'s
`append_dir_mkdirs_refused` (a directory under a regular file, Java's
text; failing before, with C's) and `f_durable.c`'s
`durable_concurrent_opens_of_a_new_directory`
(`FileStream.testConcurrentOpensOfANewDirectory` with eight processes
for its threads, the child mode `openat` waiting for a common time, ten
rounds, the directory two levels below an existing one: each open taken
or refused with `BERGDB_IN_USE`, at least one taken a round; 17 to 22 of
80 taken), passing before, as C took `EEXIST`. A copy that refuses
`EEXIST` passed it too, three runs of ten rounds (also with eleven
missing levels and a spinning wait): on F53 under a load of about 37 the
processes did not meet between a stat and a `mkdir`, so the test guards
the rule and does not show the race. (d) U10-6 (`41eb7cf`): nothing for
C. Java's `sync()` after `close()` threw, though the close had made
every transaction durable; `bergdb_close` writes and forces everything
before it returns, and frees the handle, so no `bergdb_sync` follows it
(`bergdb.h`: after the close, db is not valid). (e) 020-24's U10-2,
U10-4, U10-7 and U10-9 (`e5765ab`): the Pub API's Javadoc, nothing for
C. 020-27's Q2 was not on `main` yet.

2026-11-09, the candidate, part 2 (worker t17). The Core commits that
reached `main` after part 1, up to `ef5b52f` (18:03), each with C's
outcome; the pin stays at `e875a34`. (a) 020-27's Q2, the null arguments
(`a848c62`): Java's Core API refuses every null argument with
IllegalArgumentException "PARAM == null not allowed", before anything
else (`Db.start`, `getOne`'s key and `GetData`, `getMany`'s `GetMany`
and its stop condition, `execute`, `printDag`; `DbBuilder`'s setters;
`Trans.Builder`'s keys, values, read keys and read hashes; `GetMany`'s
`Endpoint`, `Prefix` and `PrefixN`), where it threw
NullPointerException, an AssertionError with `-ea`, or took the null.
C's API refused each NULL that it has with `BERGDB_ARG`
(IllegalArgumentException) already, before the state, since 012-03:
`bergdb_open`'s database pointer, `bergdb_get_one`'s key, read context
and result, `bergdb_get_many`'s range, read context and result,
`bergdb_execute`'s transaction, `bergdb_debug_print`'s stream,
`bergdb_trans_put`'s, `_put_transformed`'s, `_delete`'s and
`_key_read`'s key (a NULL key also with a length of 0), the puts' value,
and the level of `bergdb_sync` (Java's null `SyncLevel`). What C takes
as "none" when NULL is its design and stays: the options (the defaults),
their clock (the system's) and directory (memory), the range's start key
(Java's `startKey` null), prefix, end key and stop function
(`DontStop`); C has no `DbBuilder` setters, `addReadHashes` or
`createdTxt`. The texts are C's own, as before (Java's name the
parameter, C's API names its own: no harness compares them). (b) Its
range checks (`f490cfa`): a key of no segments (Java's `long[0]`) in
`Trans.Builder` and `getOne`, and `getMany`'s start key of none: C's API
takes bytes, and a bkey of any length, the empty one too, has a segment
at least, so nothing for C; a `GetMany` used again with a non-empty
result: C has no such object, as `bergdb_get_many` fills `*out` anew at
each call and resets the read context's pairs (nothing for C); a stop
condition's answer that is none of the four, which ended Java's read
with an assert (with `-ea` failing the database) and now with
IllegalArgumentException, the database going on: `api.c`'s `many_handle`
refused it already (`BERGDB_ARG`, "a stop function's answer out of
range", the read ended, the database active); `GetN` and `PrefixN` with
a negative count: `bergdb_range.max_count` below 0 is refused already
(`gm_get_n`'s assert is the library's own invariant behind it);
`addReadHashes()`'s length: C has none. `bergdb.h`: `BERGDB_ARG` and
`bergdb_get_many`'s errors say it, the latter no longer "GetN asserts
it". Test `f_api.c`'s `api_null_and_range_arguments`
(`DbTesterJavadoc`'s `testDbNullArguments`,
`testTransBuilderNullArguments` and `testRangeArguments`, each case that
C's API has: 24 calls, each `BERGDB_ARG` with "IllegalArgumentException:
" where there is a database; nothing written, nothing added to the
transaction, the database going on; the stop function's bad answer had
no test), passing before, as C's checks were there. (c) 020-27's Q1
(`c4ce24a`): the Core API named in `Db`'s class Javadoc, Javadoc only;
nothing for C, whose API is `bergdb.h` (its first paragraph: the
counterpart of `Db`'s public methods, as 012-03 maps them; "Keys and the
layers above" has 020-27's K1 and K2). (d) 006-18-03 (`58f2092`): the
unit tests on Android (`bergdb.nanotest.Platform`, `DbTesterFailure`'s
and `Eviction`'s and `StreamContractTester`'s tests): Java's tests only,
nothing for C; 021-14's `OneFileStream` (`4957737`, a stream for tests),
which C does not have: nothing for C. (e) A fault of C's, found by part
1's test of the cut and by 022-05 (`d694a0d`) at once: a failed
stream's sync and close (`stream_finish`) gave `ERR_OK` when its buffer
was empty, as `stream_flush` returned before it looked at the failure;
so after a failed cut, or a force that failed at a sync, `bergdb_close`
gave `BERGDB_OK`, where `bergdb.h` says `BERGDB_IO`, and Java's
`FileStream.close()` throws the failure; 021-20's check makes a failed
cut one of a replaced directory. 022-05 landed the same fix first
(`stream_flush` refuses a failed stream first, with its tests), so part
2's own fix and its test of a failed force went at the rebase;
`append_dir_replaced_no_delete` checks the sync and the close after the
cut in a replaced directory, failing before (on a copy with the old
`stream_flush`).

2026-11-09, the candidate, part 3 (worker t17). 021-24 (`41b9b155`,
18:08, a review of 021-20, W1, high), on `main` after part 2's look;
the pin stays at `e875a34`. Java's `newFile()` checked the directory
before its force of the last file (SWITCH, with per-append forcing off),
which can take seconds, so a directory replaced during that force got
the new file, and the stream went on; a cut's delete checked before the
file's close. Now `openForRw()` checks right before the open and again
after the file's and the directory's forces, `DbFile.delete()` right
before the delete and again after it, and a start's last file goes
through `openForRw()` too; what is left is said: a replacement between
the check and the step leaves an empty stream file in the replacement
(an open there refuses it until it is removed), or deletes the
replacement's file of that name at a cut, and the check after fails the
stream before a byte is written there. C had part 1's port with the
same order as 021-20's Java (the check before the switch force), so the
same fault. Now `stream.c`'s `new_file` checks right before
`plat_open_rw`, after the switch force, and again after the OPEN and
directory forces; `stream_pretruncate` right before each unlink, after
the file's close, and again after it; `open_dir` before and after the
open of the last file for writing; `check_directory`'s comment says what
is left and the invariant it relies on (bergdb.lock open until
`stream_close`, which closes it after the files: 020-23's V5-1).
`bergdb.h`, section G, and `stream.h` say it. Tests, by the test build's
I/O seam (Java's `FileStreamIo`), each failing before (on a copy with
part 1's order): `t_append.c`'s `append_dir_replaced_during_the_switch`
(`FileStream.testNoNewFileWhenReplacedDuringTheSwitch`: the directory
moved away and a stream's of 1,000 bytes moved to the path in the
switch force; the sync fails with Java's text, no file made in the
replacement, which opens with its 1,000 bytes; before, the sync
returned and file 02 was in the replacement),
`append_dir_replaced_right_before_the_open`
(`testReplacedRightBeforeTheOpen`: the replacement in the seam's open of
file 02; the sync and the close fail, the empty file is in the
replacement, an open refuses it, `BadDirStateException`, and opens
without it) and `append_dir_replaced_right_before_a_delete` (C's own,
for `DbFile.delete`'s check after: a cut of one file whose delete met
the replacement fails with Java's text, the replacement's file of that
name deleted; before, the cut returned `ERR_OK`).

2026-11-09, the candidate, part 4 (worker t17). 021-26 and 021-27, at
the session's word (18:40): `main`'s `007140d` and `f1a5456` (18:31),
taken from coord-1109's clone `clone-h31` (`e7a3b02`, `57cb00a`)
before they reached `main`; the pin stays at `e875a34`. (a) 021-26: `DbClock.currentTime()` took the clock's
time at most as `LAST_USER_TIME` (020-23's Z1) and kept it as the time
that the next transaction must pass, so one call while the clock was
out of range, or in the 1024 units kept for reclaim, gave
`LAST_USER_TIME`, and every later user transaction was refused until a
restart, also with the clock back in the range; found by a black-box
user of this port, 022's U2-1 (`apps/u2/repro_clock_poison.c`). Now a
clock's time after `LAST_USER_TIME` is not taken: the time is the last
time given or the last transaction's. C's `dbclock_current_time` had
Z1's cap, ported at the pin of 15:22, and follows: `clock.c`, its
comment and `clock.h`'s; `bergdb.h`'s `bergdb_current_time` and section
F. Tests, each failing before (on a copy with the cap): `t_clock.c`'s
`clock_dbclock_current_time_with_the_clock_past_the_end`
(`DbClock.testCurrentTimeWithTheClockPastTheEnd`: the clock past
`MAX_TIME`, then past `LAST_USER_TIME`, each time the last transaction's
time and the user transaction refused with its text; the clock at 2000,
a transaction at 2000), `clock_dbclock_current_time_leaves_the_margin`
as Java's now (the last transaction's time with the clock after
`LAST_USER_TIME`; at it, `LAST_USER_TIME`; the margin's internal
transactions as before), and `f_settings.c`'s
`settings_current_time_with_the_clock_out_of_range`
(`PubTesterJavadocRest.testCurrentTimeWithTheClockOutOfRange` through
the API: `bergdb_current_time` gives the put's time while the clock is
past `BERGDB_MAX_TIME`, the put is refused with `BERGDB_LIMIT`, "outside
the range", and with the clock at 2000 the put takes 2000; before, the
current time was 2^56 - 1025 and the put at 2000 was refused). (b)
021-27 (U2-4, open, kept for 2026.4): `bergdb_get_trans` at a multiple
of 8 inside a committed transaction's record reads the bytes there as a
record and fails the database, as Java's; no Javadoc word changed, and
`bergdb.h` says it already ("the bytes at tpos are not a committed
transaction"). Test `f_api.c`'s `api_get_trans_inside_a_record`
(`DbTester.testGetTransInsideARecord`: a put of 1,000 bytes, offsets 8,
16, 24 and 512, each `BERGDB_FAILED` and a read after it too), passing
before, as Java's.

2026-11-09, the candidate (worker t17). The release candidate pinned:
`main` at `d00096e4d4a423dd36622617d32d0dc5ee00bf6a` (18:42), named by
coord-1109 at 18:58 (also `int.git`'s branch `candidate-2026.4`):
`java-build.sh`'s default and `c/readme.md`'s "Which Java", which now
calls it the candidate. Java's vectors written again from it: all
thirteen files equal. The stream's bytes do not change. Every Core
commit from `e875a34` to it, nineteen, was read; parts 1 to 4 above
took those up to 021-27, and this landing the rest. (a) 021-25, fix (c)
(`e8cbf9d`): `KeyAccessPath.clear()` nulls only the entries that `add()`
set since the last `clear()`, below a high-water mark, not the whole
array, whose length is that of the longest path ever followed (a
reclaim step's touch records every key node it follows, and every later
transaction nulled them all: the main cost of 020-24-14's put slowdown).
C's `pd_clear` nulled the whole capacity at every transaction too: now
`struct kap`'s `used`, raised by `kap_add` and set to 0 by `pd_clear`,
which nulls below it; `kap_enlarge` zeroes the new nodes' array, as a
Java array is, so that no entry above the mark holds a pointer (before,
`pd_clear`'s whole-array loop zeroed what the allocation left). Test
`t_dag.c`'s `dag_kap_clear_nulls_what_was_used` (`KeyAccessPath`'s
`testClearNullsTheNodes`, `testClearAfterClearFast` and
`testClearAfterEnlargement`: no entry holds a node after `pd_clear`,
also after `pd_clear_fast` and later shorter adds, and after
enlargements to 25, 40 and 64 entries; and C's own check that an entry
above the mark is not touched, which fails with the old loop). (b)
021-24's wording (`d00096e`): the window between the check and the step
is usually microseconds, not a bound, and the empty file it can leave is
refused with an exception that depends on what else is in the
directory: `check_directory`'s comment and `bergdb.h`, section G. (c)
Nothing for C: 020-24-15's U15-11 (`301c4f4`, FileStream's three tests
made package-private) and U15's Javadoc (`1025955`, `DbException`'s
words on `InternalDataException`, which `bergdb.h`, section E, says
already), 006-18-03's `testOneFileStream` on Android again (`933ee8c`).
Java's build at the candidate has 193 source files (the pin's 192 and
`nanotest.Platform`); the harness's Java compiles against it unchanged.

The gate against the candidate (`git:d00096e`), on `2026.4` at
`e17528d` with parts 1 to 4 and this: `C BEFORE COMMIT OK (326 s)`, F53
under a load of about 6; `unit` 529 tests (528 in the release build);
`func` 51; `cross quick` 0 differences (23 workloads, 69 crash cuts, 85
corrupt variants, 2 in turns, 46 budget runs); `writecheck` 0;
`corruptset` 63 copies; `allocfail` 628 runs; `examples` OK. Before the
rebase onto `448ca60` and `e17528d` (022-06's), on `a125133`: `C BEFORE
COMMIT OK (370 s)`, `unit` 527, `func` 49; and on that tree the whole
corrupt set, seed 1, `nice -n 10`: `CORRUPTSET OK`, 6,253 copies (237
s), 2,628 refused by both with the same exception and message, 3,560
started, 65 with a later read failing alike, 22 of 014-01's case; and
`corrupt.sh`, `nice -n 10`: `CORRUPT OK`, 144 variants (84 refused by
both, 38 started, 22 started with a read failing later), 106 messages
compared, 0 differ (195 s). No difference remains. 022-04, section 8.2,
filled. Landed as `8772b93` (19:21), on `453ad16`, 022-06's index, which
changed no file of `c/`. Both again on the landed tree, `nice -n 10`:
`CORRUPTSET OK`, 6,253 copies (213 s), every count the same;
`CORRUPT OK`, 144 variants, 106 messages compared, 0 differ (210 s).
