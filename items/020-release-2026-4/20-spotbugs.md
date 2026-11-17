# 020-20 SpotBugs over 2026.4

Created 2026-11-09 by Frans Lundberg. Status: open.

A bug hunt for release 2026.4 (020): one run of SpotBugs, a static
analyser of Java bytecode, over the code of `main` at `f8046f3`, its
warnings triaged by reading the code, and each true defect turned into a
failing test and a fix. One of the hunts of 2026-11-09 (coord-1109), each
done apart from the others.


## 1. The request

coord-1109, 2026-11-09, at Frans's word (09:27: "Yes" to a one-off
SpotBugs run): run SpotBugs once over 2026.4's code, effort max,
threshold low; keep the warnings in the files that 2026.4 changed
(`git diff --name-only release-2026.3..HEAD -- java/src`, production
classes before testers and harnesses), and every concurrency,
arithmetic-overflow and null-dereference warning anywhere in
`bergdb.core`, `bergdb.pub` and `bergdb.pubimp`; give each kept warning a
verdict, a true defect, harmless or a false positive, with one line of
reason; for a true defect, a failing test, a fix, the gate and a commit
in the hunt's clone. SpotBugs is not added to the build.


## 2. The method

* **SpotBugs 4.10.5**, the latest release (2026-10-12), the `.tgz` of
  its GitHub release, in `/Users/f/fl/bench/2026-11-09/spotbugs/`, not
  in the repo. Checked: the archive's SHA-256 (`cce32449...6007e`) is
  the digest GitHub publishes for the asset, and `lib/spotbugs.jar`'s
  (`8d0af71a...665f`) is the release notes' and Maven Central's
  `spotbugs-4.10.5.jar.sha256`.
* **The code**: a clone of `main` at `f8046f3`
  (`/Users/f/fl/bench/2026-11-09/clone-t20`), built with `java/build.sh`
  (JDK 27, `--release 17`): `java/build/classes`, 1,106 classes of `src`
  and `src-dev`. BergDB has no dependency outside the JDK (build.sh's
  jdeps check), so the aux class path is empty.
* **The run**, one JVM, 23 s:
  `java -Xmx4g -XX:+UseSerialGC -jar lib/spotbugs.jar -textui
  -effort:max -low -sourcepath src:src-dev
  -xml:withMessages=out/spotbugs.xml -sortByClass=out/spotbugs.txt
  build/classes`. 1,718 warnings (priority 1: 135, 2: 622, 3: 961); one
  analysis error, in a JDK probe of `src-dev`
  (`bergdb.test.java.CloneArray`, an array class name the
  `MethodReturnCheck` detector cannot parse). The outputs:
  `/Users/f/fl/bench/2026-11-09/spotbugs/out/`.
* **The kept set**: 655 warnings, 298 in production classes and 357 in
  testers and harnesses: those in the 122 files that 2026.4 changed, and
  those of `MT_CORRECTNESS`, of an arithmetic pattern (`ICAST_*`, `IM_*`,
  `INT_*`, `BSHIFT_*`, `RV_ABSOLUTE_*`) or of a null pattern (`NP_*`,
  `RCN_*`) anywhere in `bergdb.core`, `bergdb.pub`, `bergdb.pub.util` and
  `bergdb.pubimp`. Each read in the code at its line; a pattern with many
  sites read site by site where the reasons could differ. The kept list,
  one entry per warning with its pattern, class, line and message:
  `out/kept.json` beside the outputs.
* **A glance outside it**: the 1,063 other warnings, by rank and by
  pattern, for anything as plain as a null dereference in a production
  path of the Core Layer's other packages (`bergdb.stream`,
  `bergdb.storage`, `bergdb.dag`, `bergdb.common`). It found finding T1,
  section 3.


## 3. The findings

| ID | Severity | File and line | Tests | Fix (clone) |
|----|----------|---------------|-------|-------------|
| T1 | low | FileStream.java:997 | FileStream and PubTester's testUnlistableDirectory | `4bba305` (clone `9244d57`) |

T1's other sites: `FileStream.hasStreamBytes` (FileStream.java:685) and
its caller `DatabaseBuilderImp.refuseMissingStream` (line 333). The
commit `4bba305 (9244d57 in clone-t20)` is in the clone, gated: BEFORE COMMIT OK (unit 1419, f
86, demos OK, 131 s), JAVADOC PUB OK.

**T1. A directory that cannot be listed.** SpotBugs:
`NP_NULL_ON_SOME_PATH_FROM_RETURN_VALUE` in
`FileStream.getSortedDbFiles()` (`bergdb.stream`, outside the kept set,
found by the glance): `File.listFiles()` returns null when the directory
cannot be listed, an I/O error or no permission to read it, and
`Arrays.sort` dereferenced it. Shown by a probe on F53 (a database
directory made unreadable with `setReadable(false)`):

* the Core's `new FileStream(dir)` threw a `NullPointerException` (the
  lock released since 015-32);
* the Pub API's `start()` of `create(dir)` or `open(dir)` of a directory
  with `created.txt` threw a `DatabaseMissingException`: "its stream is
  missing ... Restore the *.bergdb files from a backup ...; or ... remove
  created.txt and the *.bergdb files and start again", though the files
  were there, as `FileStream.hasStreamBytes` took the null for "no stream
  file". Its advice, to remove the database's files, is the harm;
* of a directory without `created.txt` (a new database), a
  `NullPointerException`.

The fix: `FileStream`'s new `listFiles(dir, filter)` throws an
`IOException` ("Cannot list the directory ...") for the null;
`getSortedDbFiles` and `hasStreamBytes` use it (`hasStreamBytes` still
gives false for a missing directory, and declares `IOException`);
`DatabaseBuilderImp` turns its `IOException` into a `StreamIoException`,
as `openDir` does. So `start()` throws a `StreamIoException` whose cause
is the `IOException`, as `DatabaseBuilder.start()`'s Javadoc says for a
directory that cannot be opened (now "opened or listed"). Tests, each
failed before the fix: `FileStream.testUnlistableDirectory` (the
constructor's and `hasStreamBytes`' `IOException`, the lock released, the
stream opens with its byte once readable) and
`PubTester.testUnlistableDirectory` (`create()` and `open()` of a
database's directory and `create()` of an empty one: `StreamIoException`
with an `IOException` cause; the files unchanged; the data there once
readable). Both skip where the permission does not stop the listing
(root, as on s1). `releases/next.md` has an entry under Pub API. Severity
low: a permission or I/O fault of the user's, but the message's advice
could cost the data.

**Notes, not defects** (for Frans where marked):

* **N1 (for Frans).** `CryptoKey.getKeyData()` returns the key's own
  array (`EI_EXPOSE_REP`): a caller can change a key, and with it its
  `serialize()`, `equals()` and `hashCode()`. No promise is broken
  (`CryptoKey`'s Javadoc does not say immutable; a started database
  copies the nonce and the key), but `DbByteArray` and `DbObject` give
  copies since 020-10's B3. Options: a copy (one line, and a test), or
  a sentence in the Javadoc. Not changed.
* **N2.** `KeyNode.getInfo` counts `uniqueKeyCount` wrong (it compares a
  compare value with the whole last klong), but nothing reads
  `NodeInfo.uniqueKeyCount` (`URF_UNREAD_PUBLIC_OR_PROTECTED_FIELD`).
  Debug output only.
* **N3.** `KeyNode.firstAndSecond`'s `assert insert.length >= 0` is
  vacuous; its Javadoc says a non-zero length
  (`INT_BAD_COMPARISON_WITH_NONNEGATIVE_VALUE`). An assert weaker than
  meant, nothing more.
* **N4.** `Util.today()`, which `Db` calls for `created.txt` at a
  creation, formats with a static `SimpleDateFormat`, which is not
  thread-safe (`STCAL_INVOKE_ON_STATIC_DATE_FORMAT_INSTANCE`, outside the
  kept set; 015-63 replaced the same in `Time`). A probe of 8 threads ×
  20,000 calls gave no wrong string: every call formats the same date,
  and `SimpleDateFormat`'s fast path for 2- and 4-digit fields skips the
  shared `DecimalFormat`. Two creations that straddle midnight could mix
  their dates in `created.txt`, a text no code reads. Harmless.


## 4. Verdicts: production classes

298 warnings. "Harmless": SpotBugs reads the code right, and no fault
follows; "false positive": it reads the code wrong. No true defect.

Concurrency:

* `AT_NONATOMIC_64BIT_PRIMITIVE` (7) harmless: Eviction 830, 832 and
  Reclaim 872, 873 are written by the writer under the write lock;
  NodeCollection 325, the maintenance follower's count, by the writer
  only; KeyNode 179 (`spos`) is published by the volatile `size`
  (`setSpos`), and KeyNode 1356 (`id`) is set before the node is
  published.
* `AT_NONATOMIC_OPERATIONS_ON_SHARED_VARIABLE` (5): Eviction 653
  (`batches`, the eviction thread's only), NodeCollection 324 (one
  thread) and Reclaim 718 (the writer, under the write lock) harmless;
  KeyNode 1739, an iterator's own `offset`, and IndexBuilderImp 469, the
  build's `count`, used by the build's thread only (the lambda of
  `runStep` runs in it), false positives.
* `AT_STALE_THREAD_WRITE_OF_PRIMITIVE` (8): KeyNode 196, 870, 1001,
  1036, 1380 (`isDirty`, `lastTimeIndex`, `isInTransNodes`) harmless,
  the writer's only, under `Db.writeLock` (their synch notes); KeyNode
  1372 (`isCanonical`) harmless, written by the writer or under the node
  table's lock (Node's synch note); IndexBuilderImp 438, 479 (`count`,
  `ended`) false positives, the build thread's only.
* `IS2_INCONSISTENT_SYNC` (2) false positives: Eviction 719
  (`pinnedOfLastRound`) is written and read under the write lock, the
  monitor besides in `sweep()`'s block; Eviction 1145 (`released`): the
  unlocked read is a test accessor, after the work.
* `VO_VOLATILE_INCREMENT` (3) harmless: Eviction 215 (`budgetSets`)
  under the monitor; Eviction 653 one writer (the eviction thread);
  Reclaim 718 one writer (the writer).
* `VO_VOLATILE_REFERENCE_TO_ARRAY` (3, KeyNode's `klongs`, `pointers`,
  `pos`) harmless: elements published by the volatile `size` or by
  release stores (the synch notes; 015-12, 015-14).
* `ESync_EMPTY_SYNC` (12: Cache3 83; Db 319, 320, 530, 535, 1470, 1540,
  1836, 2047, 2180, 2209; Reclaim 240) harmless: memory barriers on
  purpose, each with its synch note (publication to readers, or "a
  transaction that runs has ended").
* `ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD` (5) harmless: Eviction 391,
  392, 971, 972, the process totals, under `Eviction.class`'s lock, which
  `totals()` takes; NodeCollection 1043, a test's hook.
* `SWL_SLEEP_WITH_LOCK_HELD` (1, Eviction 2422) harmless: a test holds
  the lock on purpose, so that a writer waits.
* `USO_UNSAFE_*_SYNCHRONIZATION` (5: Db 2821, KeyNode 1101, DatabaseImp
  166, Eviction 589, 297) harmless: internal locks; BergDB has no
  untrusted code in its JVM to take them.
* `RV_RETURN_VALUE_IGNORED` (2: Eviction 2071, NodeCollection 1132)
  harmless: tests' `await` with a time-out as a safety; a time-out only
  shortens a hold.

Arithmetic:

* `ICAST_INTEGER_MULTIPLY_CAST_TO_LONG` (6) harmless: TransNodes 117,
  `key.length * 8`, a key's segments, far below 2^28; TransSeq 667, 740,
  771, 853, 1015, test helpers with small constants.
* `INT_BAD_COMPARISON_WITH_NONNEGATIVE_VALUE` (1, KeyNode 1279)
  harmless: N3.

Null:

* `NP_NULL_PARAM_DEREF_ALL_TARGETS_DANGEROUS` (2, DbObject 840, 841)
  harmless: `testNamePartsCheckedFirst` passes null on purpose, and
  checks the refusal.
* `UWF_FIELD_NOT_INITIALIZED_IN_CONSTRUCTOR` (6) false positives:
  RwTransaction 77, 185 and WTransaction 54, 69, 79 (`trans`) are set by
  `execute()`, before `ConnectionImp.rw()` and `WBuilderImp` return the
  object; UsePrimaryBuilderImp 361 (`Kvt.key`), set by the Core's
  `GetMany` before `handleKvt`.
* `PZLA_PREFER_ZERO_LENGTH_ARRAYS` (6) harmless, null meaning absent:
  DbObject 528 (`getByteArray`, as its Javadoc says), DbObject 311
  (private: no such name), IndexDefinition 421 (no entry), IndexKeys 480
  (`succ`: none; the scans' bases are never all ff), StringUtil 516 (a
  null argument only), Eviction 1430 (a test's helper).

Switches and stores:

* `SA_FIELD_SELF_ASSIGNMENT` (1, KeyNode 180) harmless: `size = size`
  is a volatile write that publishes `spos`, on purpose (its comment).
* `SF_DEAD_STORE_DUE_TO_SWITCH_FALLTHROUGH_TO_THROW` and
  `SF_SWITCH_FALLTHROUGH` (ObjectFormat 329, 324) false positives:
  `checkValue`'s `ARRAY_START` case is a `while (true)` that only
  returns or throws.
* `SF_SWITCH_NO_DEFAULT` (1, KeyNode 1512) harmless: `getInfo` counts
  the three types it names (N2).
* `DLS_DEAD_LOCAL_STORE` (11) harmless: KeyNode 171, a volatile read on
  purpose (a synch action); KeyNode 484, 559, 633, 707, 773, 1123, an
  initializer overwritten before use; Eviction 1410, 2357, a test and a
  test's helper; DatabaseImp 80 (`startInfo`, unused); TimeResolver
  449, an initializer.
* `EC_BAD_ARRAY_COMPARE` (1, KvToObjectImp 185) harmless:
  `testByteArray` checks identity on purpose: a get as `byte[]` gives the
  database's own array (015-47).
* `REC_CATCH_EXCEPTION` (1, Eviction 1624) harmless: a test's reader
  thread ends on a broken or timed-out barrier, as its comment says.
* `DMI_RANDOM_USED_ONLY_ONCE` (8) harmless: KeyFactory 89 to 129, a
  test-key generator with fixed seeds; CryptoKey 173, 183, a
  `SecureRandom` seeded from another's bytes and more entropy, on
  purpose.
* `DM_DEFAULT_ENCODING` (4: Eviction 1463, 1616, 2256; KeyNode 1397)
  harmless: tests' ASCII keys and a debug print.

API shape and style:

* `UPM_UNCALLED_PRIVATE_METHOD` (83) false positives: Nano tests in
  production classes (NodeCollection, CryptoKey, the value classes,
  DbObject, Time, DatabaseBuilderImp, Entries, RwTransaction,
  TimeResolver), run by reflection (`TestRunner` sets them accessible).
  All 325 of the run's `UPM` warnings were checked to be `static void`
  with no parameter or a `TestEnvironment` and `@Nano` or named `test*`,
  so Nano runs them (`CryptoKey`'s
  `checksThatParsingBadStringGeneratesFormatException` and
  `TimeResolver.tSpecial1` by their `@Nano`), but for five dead helpers
  in `src-dev` (`MyLongMap`, `RefQ`, `Issue150420`, `frans/DagExamples`).
* `EI_EXPOSE_REP` (15) and `EI_EXPOSE_REP2` (9) harmless: the Core's
  internals (`Db.Internal`'s accessors, `Cache3.residents()`,
  `NodeCollection`'s parts), `Pack.getClasses()`, `ConnectionImp`'s list
  made for each call; CryptoKey 64, N1.
* `AA_ASSERTION_OF_ARGUMENTS` (28: Cache3, Db.getOne, NodeCollection,
  Trans.Builder.addReadHashes, KeyNode, Keys, Klong) harmless: internal
  methods; without `-ea` a bad argument fails as soon (a
  `NullPointerException` or an index out of bounds); the API checks its
  arguments with exceptions.
* `CT_CONSTRUCTOR_THROW` (13) harmless: a finalizer attack needs
  untrusted code in the JVM; most of the classes are final or
  package-private.
* `MC_OVERRIDABLE_METHOD_CALL_IN_CONSTRUCTOR` (1, DbFailedException 29)
  harmless: `initCause` in a constructor, as `StreamIoException` does.
* `MS_PKGPROTECT` (1, Klong 88), `PA_PUBLIC_ARRAY_ATTRIBUTE` (1) and
  `PA_PUBLIC_PRIMITIVE_ATTRIBUTE` (6, KeyNode) harmless: the dag's public
  fields, by design; nothing outside writes them.
* `URF_UNREAD_FIELD` (4) harmless, dead fields: Db 2987
  (`PrintStartListener.p`; `StartListener` is empty), DataObjects 101
  (`ClassInfo.c`), RwEnvironmentImp 611 (`ObjectInfo.name`),
  WTransaction 13 (`runCount`).
* `URF_UNREAD_PUBLIC_OR_PROTECTED_FIELD` (7) harmless: `StartInfo`'s
  fields (Db 748 to 752), `Trans.nodeCount`, `NodeInfo.uniqueKeyCount`
  (N2), a test class's field (KvToObjectImp 156).
* `SIC_INNER_SHOULD_BE_STATIC_ANON` (13), `THROWS_METHOD_THROWS_*` (14)
  harmless: style.


## 5. Verdicts: testers and harnesses

357 warnings. No true defect.

* `UPM_UNCALLED_PRIVATE_METHOD` (48, KeyNodeTester, PubTester) false
  positives: Nano tests, checked as in section 4.
* `URF_UNREAD_PUBLIC_OR_PROTECTED_FIELD` (106), `UUF_UNUSED_*` (60),
  `UWF_UNWRITTEN_PUBLIC_OR_PROTECTED_FIELD` (3),
  `NP_UNWRITTEN_PUBLIC_OR_PROTECTED_FIELD` (2, DataObjectsTester 818),
  `UWF_FIELD_NOT_INITIALIZED_IN_CONSTRUCTOR` (4), `UWF_NULL_FIELD` (2),
  `SS_SHOULD_BE_STATIC` (1), `MS_PKGPROTECT` (3),
  `ST_WRITE_TO_STATIC_FROM_INSTANCE_METHOD` (6), `CT_CONSTRUCTOR_THROW`
  (4) false positives or harmless: the tests' Data Objects and their
  fields, which the conversion reads and writes by reflection; null and
  final fields, static counters of constructions and a throwing
  constructor on purpose (DataObjectsTester, DbObjectTester,
  DbObjectFormatTester, PubTester, PubTesterIndex); static fields that an
  `rw()` action fills for the test to read (PubTester 689 to 718).
* `AT_*` (22): LimitsTester's (13) false positives, one driving thread;
  IndexJobsHarness 777, 801, 825, 831, 1877, 1879 false positives, the
  harness's main thread; DbTesterFailure 1666, 1702, 1720 (`faults`)
  harmless, see `VO_VOLATILE_INCREMENT`.
* `VO_VOLATILE_INCREMENT` (9, DbTesterFailure's `faults` and `damaged`)
  harmless: the tests check `> 0`, which a lost increment cannot break,
  and the one `>= 2` counts increments made one after the other.
* `IS2_INCONSISTENT_SYNC` (5, FileStreamPowerLossTester's model flags)
  harmless: set by the test thread before the call that hands work to
  the stream's threads through locks or a queue.
* `USO_UNSAFE_OBJECT_SYNCHRONIZATION` (8, IndexJobsHarness),
  `SWL_SLEEP_WITH_LOCK_HELD` (2), `VO_VOLATILE_REFERENCE_TO_ARRAY` (1)
  harmless: the harness's own locks; sleeps that hold a lock on purpose.
* `CWO_CLOSED_WITHOUT_OPENED` (1, EvictionAccountingTester 168) false
  positive: the `continue` inside `try` goes through the `finally` that
  unlocks the lock taken in that round.
* `NP_NULL_ON_SOME_PATH_FROM_RETURN_VALUE` (4, PubTester 670, 3305,
  3607, 3630) harmless: `listFiles()` of the test's own temporary
  directories.
* `ICAST_INTEGER_MULTIPLY_CAST_TO_LONG` (8) and `IM_BAD_CHECK_FOR_ODD`
  (2) harmless: small constants; non-negative loop indices.
* `ES_COMPARING_STRINGS_WITH_EQ` (1, PubTester 4118) harmless: identity
  on purpose, a `DbString` keeps its `String`.
* `DLS_DEAD_LOCAL_STORE` (5) and `DLS_DEAD_LOCAL_STORE_OF_NULL` (5)
  harmless: loop variables that only count, and nulls that free a
  database or a 1 GiB array before the next step.
* `RV_RETURN_VALUE_IGNORED` (2) harmless: DataObjectsTester 2948, a
  `hasNext()` called for its refusal; PubTester 407, a bounded `await`.
* `BC_UNCONFIRMED_CAST_OF_RETURN_VALUE` (1, IndexJobsHarness 586)
  harmless: the fault is an `Error` or a `RuntimeException`, the `Error`
  thrown first.
* `BC_VACUOUS_INSTANCEOF` (1, IndexDefinitionTester 679) harmless: true
  in the loop's first round only.
* `DB_DUPLICATE_SWITCH_CLAUSES` (1, IndexDefinitionTester 719) harmless:
  two cases give a long, a weighting.
* `SF_SWITCH_FALLTHROUGH` (1, ObjectFormatTester 1117) false positive,
  as ObjectFormat's: a `while (true)` that returns or throws.
* `UC_USELESS_OBJECT` (1, ObjectFormatTester 255) false positive: the
  chain of objects is used through `deep`.
* `DMI_RANDOM_USED_ONLY_ONCE` (9) harmless: seeded streams, one per
  purpose.
* `DM_DEFAULT_ENCODING` (4), `AA_ASSERTION_OF_ARGUMENTS` (4),
  `PZLA_PREFER_ZERO_LENGTH_ARRAYS` (3), `PA_PUBLIC_PRIMITIVE_ATTRIBUTE`
  (1), `SIC_INNER_SHOULD_BE_STATIC_ANON` (2), `THROWS_METHOD_THROWS_*`
  (13), `URF_UNREAD_FIELD` (2) harmless: ASCII, tests' asserts, style,
  dead fields.


## 6. State

2026-11-09, by t20 for coord-1109. Every kept warning has a verdict: no
true defect among the 655. One true defect outside the kept set, T1,
fixed with its tests in the clone
`/Users/f/fl/bench/2026-11-09/clone-t20`, commit `4bba305 (9244d57 in clone-t20)` on
`f8046f3`, gated (BEFORE COMMIT OK). Not on `main`: the coordinator
takes the commit. Left: N1, for Frans; the other 1,063 warnings were
glanced at, not triaged.


Log
===

2026-11-09. Created by t20 (coord-1109's hunt 020-20). SpotBugs 4.10.5
downloaded and checked; one run over `f8046f3`, 1,718 warnings; 655 kept
and triaged, none a true defect; T1 found outside the kept set, with a
failing test for each symptom, then the fix: commit `4bba305 (9244d57 in clone-t20)` in the
clone, BEFORE COMMIT OK (131 s), JAVADOC PUB OK.

2026-11-09. N1 decided by Frans (09:47: "N1, as recommended. I see no
reason for not making a copy"): `CryptoKey.getKeyData()` returns a
copy, by coord-1109's agent n20: b70ea77 in clone-n20, with
`CryptoKey.testGetKeyDataGivesACopy` failing before the fix; BEFORE
COMMIT OK (140 s), JAVADOC PUB OK; into `main` by the integrator.
