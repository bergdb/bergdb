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
* **The candidate read**: `main` at `94a1520` (2026-11-09, 11:57:26),
  with 021-11 as `da6c5b0`. 20 commits since 2026.3 touch the Core
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

The candidate is `main` at `94a1520f21ac81fb7620b1aefba11e41b38a1b18`
(2026-11-09 11:57:26), fetched read-only into this study's clone as
`refs/remotes/repo/main`. Earlier fetches gave `10a2c79` (11:43) and
`770d88b` (11:47), whose Core layer is this one without 021-11
(`da6c5b0`, 11:57). No commit is named the release candidate yet: the
candidate comes after the day's bug hunts, its checks run tonight, and the
tag comes at Frans's word (006-17, sections 2 and 3).

"The Core layer" is what C's harness compiles (`test/cross/java-build.sh`):
the packages of `deps.py --layer core`, `common`, `core`, `dag`,
`nanotest`, `pub.util`, `storage` and `stream` (the same list at both
ends), and `java/stress/StreamDigest.java`; and
`java/stress/core-build/CoreDemo.java`, which `examples/compare.sh` takes.
`StreamDigest.java`, `CoreDemo.java`, `deps.py` and `nanotest` are
unchanged.

| Part (`git diff --numstat release-2026.3 94a1520`) | Files | Added | Deleted |
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

Every commit from `release-2026.3` to `94a1520` that touches the Core
layer, oldest first:

| Commit | Date | Entry | What | Class |
|---|---|---|---|---|
| `0bf0dfd` | 11-07 | -      | `BuildInfo` says 2026.4-dev                          | none         |
| `1132b1d` | 11-07 | 021-01 | Javadoc of `pub.util`'s exceptions and `SyncLevel`   | Pub, Javadoc |
| `c00e621` | 11-07 | 021-05 | a String key or value with a lone surrogate refused  | API          |
| `d65f5b5` | 11-08 | 021-06 | a bkey that is not well-formed UTF-8 has no ikey     | API          |
| `39fb346` | 11-09 | 021-06 | `KeyNode`'s printer shows a key without an ikey      | messages     |
| `68830b8` | 11-09 | 019-46 | a reader's drop no longer evicts the writer's object | threads      |
| `5b08db5` | 11-09 | 020-10 | `Job`, `JobStatus` of the user indexes (`pub.util`)  | Pub API      |
| `c126d7d` | 11-09 | 019-47 | the start admits the large values of every key node  | algorithm    |
| `e92a95a` | 11-09 | 020-08 | `StringUtil.utf8Size`, for the Pub's String values   | Pub          |
| `25978bc` | 11-09 | 019-46 | the writer installs every index node it reaches      | threads      |
| `c9e6975` | 11-09 | 020-08 | `StringUtil.toBytes(String, int)`, for the Pub       | Pub          |
| `dee3e48` | 11-09 | 019-46 | the writer's assert before step 6; a test hook       | threads      |
| `626a6bc` | 11-09 | -      | `key-encoding.md`: the Core's own internal keys      | documents    |
| `4dc245a` | 11-09 | 020-10 | `IndexBuildException`; `Job.join()` throws it        | Pub API      |
| `6db1ac3` | 11-09 | 020-20 | T1: an unlistable directory, an `IOException`        | API, storage |
| `55da329` | 11-09 | 020-19 | F1: `JobStatus`'s Javadoc                            | Pub, Javadoc |
| `b41e116` | 11-09 | 020-19 | J4: `DbException`'s Javadoc                          | Pub, Javadoc |
| `4b520f9` | 11-09 | 020-13 | bug 4: `BufferedStream.close()` waited for its timer | threads      |
| `656decb` | 11-09 | 020-21 | `Job.join(millis)` refuses a negative time           | Pub API      |
| `da6c5b0` | 11-09 | 021-11 | a pointer linked by node id: its node's type checked | refusals     |

The entries: 021-01, 021-04 to 021-06 and 021-11 in `items/021-todo/`,
019-46 and 019-47 in `items/019-todo/`, the rest in
`items/020-release-2026-4/`. `da6c5b0` is `1035b64` of its clone
(`/Users/f/fl/bench/2026-11-09/clone-p11`, 11:52, "BEFORE COMMIT OK;
level1.sh OK"), brought to `main` at 11:57 with its entry (`94a1520`).


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

* **019-47, the start's admission** (`c126d7d`). A start reruns every
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
* **019-46, a reader's drop and the writer's load** (`68830b8`, `25978bc`,
  `dee3e48`). A reader whose cache policy keeps no index node
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
* **021-11, the links by node id** (`da6c5b0`). 019-32's check that a
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
* **020-13, bug 4** (`4b520f9`): `BufferedStream`'s consumer thread no
  longer waits for its timer while a close waits for buffered bytes.
  Threads only.


## 2.5 The API

* **021-05** (`c00e621`): `Keys.toBytes(String)`, and so every Core call
  that takes a String key, and `Trans.Builder.put(String, String)` throw
  `IllegalArgumentException` for a lone surrogate, which the encoder wrote
  as '?'. The rule (021-04, Frans's option 1): every string BergDB stores
  is well-formed UTF-8, in every language; "in C and Go bytes that are not
  well-formed UTF-8" are the counterpart of a lone surrogate.
* **021-06** (`d65f5b5`, `39fb346`): `Keys.bkey2ikey` and
  `Keys.toString(long[])` throw `IllegalArgumentException` for a bkey
  without an ikey: one with the byte 0 or 0x31 ('/' + 2, which no ikey
  gives, '/' being 1), or whose bytes, each 1 as '/' and every other less
  2, are not well-formed UTF-8 (the new `StringUtil.isWellFormedUtf8`, RFC
  3629). The new `Keys.bkey2ikeyOrNull` returns null for it. So two bkeys
  never give one ikey, and the ikey's bkey is the bkey. The Core API still
  takes any bkey. The debug printers (`Klong.getKeyString`,
  `KeyNode.getKeyString`) show bytes with `Keys.toDisplayString`.
* **020-20, T1** (`6db1ac3`): `new FileStream(dir)` of a directory that
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
`/#i/-dummy` (`626a6bc`). Javadoc in `Handle` (DEAD, 019-46), `Db`'s start
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
4. **021-11, the links by node id** (`da6c5b0`). C links as
   2026.3's Java does: `nc_resolve_pointers`' pinned rule (`ncoll.c` 513)
   and `nc_link_to_canonical` (`ncoll.c` 555 to 603, the link at 599) take
   the handle without `nc_check_pointee_type` (`ncoll.c` 134, 022-01's
   step 2), and `check_link_by_id` (534 to 553) gives 005-57's
   `AssertionError` before any type check. C refuses such a pointer later,
   where it casts the node it follows (`dag.c`, `topds.c`: a
   `ClassCastException` with the JVM's text, 022-01's step 2), and
   `t_ncoll.c` 607 to 636 (`ncoll_link_to_canonical_another_type`)
   records that the link is made, as Java's was. The port: the check at
   the three places, before the link, as `da6c5b0` puts it; the test
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

* **019-46** (`68830b8`, `25978bc`, `dee3e48`): a race between a reader's
  drop, without the write lock, and the writer's load. C has one caller
  and no thread (`c/readme.md`, section 8), and no op that keeps nothing
  (3.2), so `nt_drop_if_empty` (`ntable.c` 172) runs only after a reader
  read a cut-back version, never with the writer between its test and its
  kill.
* **020-13, bug 4**: `BufferedStream`'s thread; C writes its buffer in the
  calls (`c/readme.md`, section 9, point 1).
* **The printers** (`39fb346`, `Klong.getKeyString`): C ports no printer
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

* 021-05 (`c00e621`) and 021-06 (`d65f5b5`, `39fb346`): Frans's rule
  (021-04, 2026-11-07, 09:33: "Yes, option 1, absolutely.") and 021-06's
  answers under his delegation; 020-11, section 5: fixed.
* 019-47 (`c126d7d`): the night's independent review ("both fixes
  correct", 020-11, section 6), the Codex review (020-14: "no defect found
  in these fixes"), `level4.sh` OK.
* 021-11 (`da6c5b0`), on `main` since 11:57: its gate and `level1.sh`;
  no independent review recorded yet. Should a review change it before the
  tag, the change reaches C as 4.2's diff.
* 019-46 (`68830b8`, `25978bc`, `dee3e48`), 020-20's T1 (`6db1ac3`),
  020-13's bug 4 (`4b520f9`), `626a6bc`.
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

Each has a default that goes ahead if Frans does not answer.

* **D1. Start now, or at the tag.** (a) Now: the steps of section 6 on a
  pinned candidate, the coding today in clones; at the tag, the diff from
  the pinned commit (4.2), ported if not empty, and a confirming run. It
  costs a pin to keep and a second, short run at the tag, and gives a C
  at 2026.4 within hours of the tag. (b) At the tag: one port from
  `release-2026.3` to `release-2026.4`, as the 2026.3 port was made;
  nothing done twice; nothing starts before the tag, 10 November at the
  earliest. **Default (a)**, as Frans's words of 11:45 suggest.
* **D2. Landing after the 2026.3 port closes.** (a) The coding in clones
  at once; landings on `022` only after the 2026.3 port's step 5 has
  passed and its step 6 has recorded its state (a tag such as
  `022-c-2026.3` in `int.git`, and the commit in `c/readme.md`), so that
  one commit is the port of 2026.3, gated against 2026.3, and the harness
  moves to the candidate in one landing (step 0). (b) Each part lands
  when ready; the 2026.3 runs take a commit before the first 2026.4
  landing; `022`'s head is between two releases meanwhile (a gate against
  2026.3 fails on 021-11's copies, one against the candidate on what is
  not yet ported). **Default (a).**
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
  land). Section 3.3 stays out.
* **D5. The runs at the tag.** (a) If the diff from the pinned candidate
  to the tag is `BuildInfo` alone: the gate with `cross quick`, the
  corrupt set, and the digests compared, at `JAVA_REF=2026.4`; the
  candidate's long runs stand. (b) Step 4's runs again at 2026.4, about
  1.5 hours of a quiet F53. **Default (a)**, and (b) when the diff holds
  Core code.


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
Frans's request of 11:45, from `main` at `94a1520` (fetched read-only into
a clone of `int.git`'s `022`; first read at `770d88b`, then 021-11 landed),
`int.git`'s `022` at `714d52b` (the 2026.3 port's step 4a landed while
this was written), and step 4's corrupt set in its clone `s4b` as it
stood at about 12:00; nothing built or run. The study and a line
in 022's readme; no other file changed.

2026-11-09, step 3 (worker t3). Section 3.1, point 3, and D4's T1 (3.2);
the stream's bytes do not change. (a) 019-47: the open's admission passes
the resident key nodes as the written nodes, as `Db.startInner`'s
`eviction.recordWritten(this, cache.nodes().iterator())` since `c126d7d`.
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
(startPos 0 and 264, two transactions each), and with `c126d7d`'s line
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
021-11, as `da6c5b0`: `nc_check_pointee_type` (019-32's check, Java's
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
`git archive` of `94a1520`): `CorruptSet.java`'s `found021_11`, the three
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
(section 2.1): `main` at `94a1520f21ac81fb7620b1aefba11e41b38a1b18`
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

The gate against the candidate (`git:94a1520`, step 0's default), on
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
The gate against the candidate (`git:94a1520`), on step 1's landing
(`b23d24e`): `C BEFORE COMMIT OK (468 s)`, F53 under a load of about 20
to 26; `unit` 392 tests (391 in the release build); `cross quick` 0
differences (23 workloads, 69 crash cuts, 85 corrupt variants, 2 in
turns, 46 budget runs); `writecheck` 0; `corruptset` 60 copies, the three
of `found-long-1` refused by both with the same exception and text;
`allocfail` 628 runs; `examples` OK. Before, on `fd7f9e0`: `C BEFORE
COMMIT OK (567 s)`. No difference remains.
