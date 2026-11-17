005-10. The proposal: unused code to remove
============================================

Written 2026-10-19 by Claude (Opus 5.5, Claude Code), at Frans's request
("Do the 005-10 todo item"). Made on commit `1f4b637`, the code as
committed; the uncommitted changes of the main tree then were documents
and items only (005-04).

Nothing is removed. This is the proposal: Frans approves all, part or none
of it, by ID, and only what he approves is removed (see "How to answer").

Frans decided on 2026-10-20; the decision and the removal are in
[../10-unused-code.md](../10-unused-code.md), and the removal's plan, lists
and checks in [applied/](applied/). This file is the proposal as it was,
but for a correction in G1.


In short
--------

* About 11,700 lines can go: 85 files deleted, 97 files edited, plus a
  120 kB jar. Measured with a patch that makes every removal recommended
  here: the build, the unit tests, the f-tests, the four gates and
  `lake build` pass with it ("Checks").
* The large parts are old tests and tools that nothing runs: benchmarks of
  Java itself (D1, 3,951 lines), manual tests (C1, 2,410), perf tests (D2,
  777), development tools (C2, 650); and the 2012 to 2017 cache, `Cache2`,
  which only its own tests use (B1, 787). Then 168 unused methods, fields
  and nested classes in files that stay (A2 and A3, about 1,200 lines), the
  2017 Ant build (E1), and 20 unused Lean lemmas (F1, 124 lines).
* Not in the patch: `frans/` (C3) and the figure and example printers
  (C5), for Frans to decide; the night tests (D3), proposed to be kept and
  run in a gate; the demos (C4), kept.
* Found on the way: eight unit tests and one f-test that never ran, as
  their classes are in no test pack (B3, and `NextMap`'s in A1); one of
  them fails on today's code. And 25 methods and two exceptions of the
  public API that nothing in the repository uses (G1), a question rather
  than a removal. The night tests, which nothing runs either, pass (D3).


How to answer
-------------

By ID, for example: "Remove all that is recommended", or "Remove A1, A2,
B1 to B3, C1, C2, D1, D2, E1, F1; keep A3; C3: remove; D3: keep". For A3,
strike single members if wanted ("keep `StorageManager.setD1`"). Then
the removal is made as in "After the decision".


The IDs
-------

| ID | What | Files | Members | Lines | Proposed |
|---|---|---|---|---|---|
| A1 | Files that nothing reaches | 7 | | 278 | remove |
| A2 | Unused members in files that stay: leftovers | | 97 | 643 | remove |
| A3 | Unused public methods of public classes in `java/src` | | 71 | 554 | remove, or strike some |
| B1 | `Cache2`, the old cache; only its own tests use it | 1 | | 787 | remove |
| B2 | `DagChecksum`; only its own tests use it | 1 | | 170 | remove |
| B3 | Tests that never ran (not in a pack) | 1 | 5 | 456 | remove; register `DbDouble`'s |
| C1 | Manual tests, `bergdb.test.manual` | 16 | | 2,410 | remove |
| C2 | Development tools that nothing runs | 8 | | 650 | remove |
| C3 | Frans's experiments, `java/src-dev/frans/` | 9 | | 901 | Frans decides |
| C4 | The demos, `bergdb.demo` | 7 | | 243 | keep |
| C5 | Figures and printed examples of the Dag | 4 | | 546 | Frans decides |
| D1 | Tests and benchmarks of Java itself | 39 | | 3,951 | remove |
| D2 | The perf tests (group "perf") | 7 | 9 | 777 | remove |
| D3 | The night tests (group "night") | 9 | | 1,790 | keep, and run them in a gate |
| E1 | The 2017 Ant build | 5 | | 834 | remove |
| F1 | Unused Lean lemmas | | 20 | 124 | remove |
| G1 | Public API members that nothing here uses | | 25 + 2 | | a question |

Lines are those of the removed code, with its comments; the edits that
follow from a removal (a pack's list, an import, a help text) are about 60
lines more. The recommended IDs together: A1 to A3, B1 to B3, C1, C2, D1,
D2, E1 and F1. The lists of files and members are in
[tables/](tables/).


How the code was searched
-------------------------

Code is used if an entry point reaches it. The entry points, as 005-10
defines them:

* the public API: the public and protected members of the public classes
  in `bergdb.pub` and `bergdb.pub.util`;
* the 24 classes that the scripts in `java/stress/` start (the level
  scripts, `conformance.sh`, `performance.sh`, `soak.sh`, `flush-order.sh`,
  `reclaimgrid.sh`, `reclaimtraces.sh`), and the unit and f-test suites
  (`bergdb.dev.Unit`, `bergdb.dev.F`) with the test methods of the classes
  their packs list;
* in a wider set, every class with a main method (106), `bergdb.dev.Run`,
  and the perf and night tests too: so that code only those reach can be
  told apart from code nothing reaches;
* reflection: the test runner finds test methods by annotation or name;
  `OptionalIcuCollatorFactory` loads `bergdb.pubimpicu.IcuCollatorFactory`
  by name; JMX reads the MBean interfaces;
* the documents: a tool or a test that `docs/` cites as the source of its
  evidence, and every Lean name that `docs/`, `README.md` or
  `lean/README.md` cite.

The tools, all in [tools/](tools/), run on a clone:

* ProGuard 7.10.0 (`-printusage`, shrinking only) for what the entry points
  reach, member by member, with the class hierarchy (an override of a used
  method is used); five sets of entry points (`pg.py`).
* A source index made with javac's tree API (`Index.java`): every
  declaration with its position, and every reference. It catches what the
  class files hide: compile-time constants (javac copies their values) and
  types in generic arguments. An unused declaration that used code refers
  to in the source is taken back (`combine.py`).
* For Lean, the constants that each compiled declaration uses
  (`LeanDeps.lean`), and the references in the source that `lake build`
  records in the `.ilean` files, including those of `#guard`, `example`
  and the executables (`lean_unused.py`).
* `members.py` selects the members to remove and says why the others stay;
  `remove.py` and `lean_remove.py` remove them by their positions, with
  their Javadoc or doc comment; `make-patch.sh` makes the whole patch on a
  fresh clone, and repeats the member pass until nothing more is unused (it
  took two rounds: the second found nothing); `gates.sh` runs the checks.

What the tools cannot see, and how it was handled:

* Objects stored through the Pub API: their fields are read and written by
  reflection (`DbObject`). So no field that is not static and final is
  removed, except five checked by hand.
* Names in strings: members that the sources look up by name
  (`getDeclaredMethod("t3")`) stay, and the nanotest fixtures, which exist
  to be found or not found by the runner.
* Lean lemmas tagged `@[simp]` and proved by `rfl`: `simp` can use them
  without naming them in the proof. A first patch removed one and a proof
  failed; all nine such lemmas stay.
* Features: code may be unused here and still be wanted by a user. Where
  the documents name one, it stays (JMX, below). The others are in A3, for
  Frans to strike.


The groups
==========


A1. Files that nothing reaches
------------------------------

No entry point reaches them, not even a main method that no script runs.

* `java/src/bergdb/common/NullPrintStream.java` (15 lines): a copy of
  `bergdb.nanotest.NullPrintStream`, which is the one used.
* `java/src/bergdb/common/Triplet.java` (31): a 3-tuple. `Pair`'s Javadoc,
  which names it, is edited.
* `java/src/bergdb/core/NextMap.java` (110): position-to-next-position
  mappings that `DbStarter` used in the 2017 source; the 2026 repairs
  removed that use (`0eb07c8`). Its three unit tests never
  ran (not in the core pack). `java/stress/restart-experiments.diff`
  names it in context lines; that diff applies to the source it was made
  for, as docs/startup-invariants.md says, and stays.
* `java/src/bergdb/core/NoReclaim.java` (21): a `Reclaim` that does
  nothing, "for testing only".
* `java/src/bergdb/pubimp/JavaCollator.java` (21): a `KCollator` from a
  Java `Collator`; the ICU and Unicode collators are the ones used.
* `java/src-dev/bergdb/dev/DummyForJavadoc.java` (55): a dummy class and
  2013 notes on Javadoc tags for a beta API.
* `java/src-dev/bergdb/dev/DummyForNotes.java` (25): a class that holds
  three 2017 notes. They are, in full: "TODO LATER. Consider if we could
  make rw-transactions composable? How to make two payments and a log
  entry in one transaction using the single-payment + new log entry code?
  Key is RwEnvironment and WBuilder. Should we have WriteInterface as
  common interface?"; "TODO LATER Consider how bergdb.storage could be made
  independent of bergdb.pub. bergdb.shared? bergdb.pub.shared? [...] Would
  be tedious to replace every exception thrown from core in pubimp."; and
  "TODO LATER. study: should we have prevPos field in StoredTopNode like
  for StoredKeyNode." If one of them should be kept, it can become a 005
  entry.


A2. Unused members in files that stay: leftovers
------------------------------------------------

97 methods, fields and nested classes or interfaces that nothing reaches,
in files that stay: private and package-private members, members of
nested classes, debugging printers and assertions, and the methods of
internal interfaces. All of them are in
[tables/members.tsv](tables/members.tsv) with the group A2. The larger
ones:

* The `Cache` interface's ten methods: only `Cache2` implemented them;
  `Cache3` does not implement `Cache`. What stays of `Cache` is its nested
  `DbInfo`. With them, `DbInfo.getStartupPosForEvict` and its three
  implementations, and `StartupPos.getForEvict` (A3).
* `Db.StartListener`'s methods and `DO_NOTHING`, and those of
  `Db.PrintStartListener`: a listener of startup that nothing calls.
  `Db.Internal`'s `executeInner`, `aux` and `handleStillDirtyNodes`.
* Debugging printers and checks that nothing calls:
  `NodeStream.checkEqualBytes`, `printDiff`, `printTransGivenBuffer`,
  `printGotDirtyLine`; `TransNodes.assertNoDuplicates` and `print`;
  `TransSeq.print` (two); `Trans.print`; `KeyNode.assertOk`;
  `Klong.assertNoDeleteBitsBeondSize`; `RecoverableStream.assertAllowedPos`;
  `DbObject.print`; `DagTester.printMap`.
* `IDirtyNodes`'s four methods: no class implements `IDirtyNodes`; only
  its nested `TransNodesForMe` is used (`TransNodes` implements it).
* Nested types nothing uses: `Cache3.AlreadyHasNode`,
  `Dag.NodeAccessListener`, `GetMany.DagForMe` and `GetMany.Link`,
  `DbObjectTester.FloatClass`.
* nanotest: `ConsoleUI`'s eight getters, `Assert.arrayEquals`.
* Fields: `Trans.splitCount` (never written, its use in `Set.java`
  commented out), `BryanIssue.prevTransSeq`, and in the 2026 harness
  `PerfTool.Alert.detail` and `PerfUtil.GcLog.collectorLine`; constants
  `Klong.MAX_VERSION`, `DbConstants.MIN_CACHE_MEMORY_VALUE`,
  `RecoverableStream.TRANS_HEADER_SIZE`, `PubKeys.INTERNAL_DIR_PREFIX`,
  `DbObject.ZERO`.
* Methods of nested classes: `DbObject.Builder`'s `addBoolean`,
  `addDouble` and `addByteArray` (the other typed adders are used) and
  `DbObject.DbField.getName`; `Trans.Builder.keyRead`; three getters of
  `NodeStream.TransIterator`; `RecoverableStream.Iterator.getSSPos`;
  `GetMany`'s `Endpoint.getEod` and three `gotEod`; and
  `IndexFunction.getTypes`, with which `FieldIndexFunction.getTypes` (A3)
  goes.
* In `java/stress/`, `Perf.isLong`; in `java/src-dev/`,
  `TestClasses.getClasses`.


A3. Unused public methods of public classes
-------------------------------------------

71 public methods and constructors of public classes in `java/src` that
nothing calls. They are leftovers too, but each could be a capability that
someone might call later; strike any that should stay. By class:

* `common.Util`: `getMemoryUse`, `getComputerName`, `identity(long)`,
  `identity(long[])`, `identity(byte[])`, `time`, `todayCompact`,
  `memoryUsed`, `sleep`. Also `HashUtil.mHash`, `MyLongSet.isEmpty`,
  `StringUtil.toPrintableAscii`.
* `core.Db`: `getNodesWritten`, `getOrdinaryNodesWritten`,
  `getPosOfLastValidMetaBlock`. `Cache3`: `getSizeIndicator`, `totalSize`,
  `pointerDestroyed`. `DbClock.getBaseClock`; `DbScan.includeInternal` and
  `lookupTime` (options of a scan); `Eviction.schedule`;
  `Kv.hasKeyTransformation`, `hasValueTransformation`; `NodeStream`:
  `getPosOfLastValidMetaBlock`, `getLastTransSpos`,
  `getPosOfLastCompletedTrans`; `StartupPos.getForEvict`; `StoredTrans`:
  `isPrimordial`, `hasNewStartupPos`, `isIndexTransaction`;
  `SyncLevel.getValue`; `TransNodes`: `contains`, `sumMemSize`.
* `dag`: `Dag.visitMemoryPointers`; `KeyAccessPath.getSize`;
  `Keys.compare`; `Klong.getShiftedCompareValue`; `Pointer.getAccessData`;
  `TopNode.getTopNodeId`, `setIsInTransNodes`;
  `ValueNode.setIsInTransNodes`.
* `pubimp` (the implementation, not the API): `ConnectionImp.getDatabase`;
  `DatabaseBuilderImp.database`, `noReclaim`; `DatabaseImp.close`;
  `DbArray.getBytes`, `toStringArray`; `DbObject.getBoolean`,
  `getByteArray`, `getArray`; `DbString.write`;
  `FieldIndexFunction.getTypes`;
  `FieldRef.isNested`; `IndexBuilderImp.getIndex`;
  `RwEnvironmentImp.vkeyRead` and `vkeyWrite` (two each);
  `RwTransaction.getOutputStream`; `WBuilderImp.vkeyRead`;
  `WTransaction.getActionRunCount`.
* `storage` and `stream`: `StorageManager.setD1`, `setErrorRule` and
  `setListener` (without the first two, D1 and the error rule stay the
  defaults that the constructor sets, `MainConfirmedRule` and
  `MainErrorRule`; `setListener` only throws
  `UnsupportedOperationException`); a constructor of
  `BufferedStream` and one of `StreamIoException`; `MetaBlock.setPos`;
  `RecoverableStream.getPosOfLastValidMetaBlock`;
  `FileStream.setRenameAsDelete`; `MemoryStream.copyShallow`.

The candidates to keep, if any: `StorageManager.setD1` and
`setErrorRule`, which change D1 and the error rule of a running database.
`DatabaseImp.close` (it calls `Db.close`) is not in the API, whose
`Database` has `stop` only.


B1. `Cache2`, the old cache
---------------------------

`java/src/bergdb/core/Cache2.java` (787 lines): the node cache of 2012 to
2017, with weak references and an outgoing-pointer sweep. `Db` uses
`Cache3` only; nothing but `Cache2`'s own six tests (five unit, one f)
uses it. docs/level4-plan.md links to it ("not a validated substitute for
the new design"); the link becomes a `git show 0597329:...` command.
Comments that name it stay where they are history (`props/Mem.java`'s
2015 results, `CcDbNightTest`).


B2. `DagChecksum`
-----------------

`java/src/bergdb/dag/DagChecksum.java` (170 lines): a checksum of a Dag's
state. Only its own three unit tests use it.


B3. Tests that never ran
------------------------

The test runner runs the test methods of the classes that the packs list.
Classes with test methods in no pack: their tests never ran. `NextMap`'s
three go with it (A1); the others:

* `bergdb.pubimp.DbDouble`: two unit tests of the double value's
  serialization. They pass. Proposed: add `DbDouble` to the pubimp pack
  (one line; the only addition of the patch).
* `bergdb.dag.DagNodeIterator`: two unit tests. One fails on today's code
  (`OpData.pointerFollower is null, not allowed`: it predates the pointer
  follower that `DagTester`'s tests set). Proposed: remove both, and
  `addToList`, which only they use. The class stays: `DagComparison` uses
  it.
* `bergdb.core.KeyFactory`: `testGettingCrazy`, with `crazyStringKey`,
  which only it uses.

And one class whose f-test never ran:
`java/src-dev/bergdb/test/Concurrency.java` (339 lines), with a main
method and JMX beans; `Concurrency2`, in the f-tests, is "a simpler
version" of it. Proposed: remove it.


C1. Manual tests
----------------

`java/src-dev/bergdb/test/manual/`, all 16 files (2,410 lines): programs
of 2013 to 2016 that a person ran by hand. No script, document or item
runs them or names them. Two of them have perf tests (D2).

`CcDbTest` (up to a million cards: lookup speed, disk size),
`DiskReadSpeed`, `DiskWriteSpeed`, `Huge` (a huge database, read
performance), `Interactive`, `LoadA` (100k entries, gets and sets),
`MultipleWriters` (processes sharing a directory), `NetworkRoundTrip`
(TCP), `RefQ` (Java's reference queues), `Shrink` (1M entries, most
deleted), `StorageOverhead`, `StreamSizeFourCases`,
`StreamSizeVsStartupDistance`, `TransThroughput`, `ValueNodeTotalMem`.


C2. Development tools
---------------------

Main methods that no script, document or item runs (650 lines):
`bergdb.Help` (points at `Run`), `dev.Dev` ("dummy test code"),
`dev.GoogleQueen` (a demo), `dev.Info` (prints the environment),
`dev.MemPerf` (memory of a million small KVs, as Props's MEM measures it
in `level1.sh` now; it is also in the test pack, without tests),
`dev.MyInstrumentation` and `dev.ObjectSize` (object sizes through an
instrumentation agent, `inst.jar`, which only the Ant build made), and
`dev.Swing` (a window with "Hello world!"). `Run`'s help text names
`Info`, `Swing` and `dev.Perf` (D2); those three lines go.


C3. Frans's experiments, `frans/` (for Frans)
---------------------------------------------

`java/src-dev/frans/`, 9 files (901 lines): `DagExamples` (Dag examples
for documentation), `FastMap` (a map from long to node, performance),
`MemoryAccess` (cache and RAM latency), `PayDemo` (a million accounts,
with replication), `WebsiteCode` (the code snippets of www.bergdb.com),
and `bryan/` (the bug that Bryan reported in November 2015, which
`java/stress/BryanRepro.java` reproduces in `level2.sh` and
`bergdb.test.BryanIssue` tests). Nothing runs them. Not in the patch;
removing them is safe (nothing else uses them).


C4. The demos (kept)
--------------------

`bergdb.demo` (7 files, 243 lines): `Demo` and `GetStarted1` to
`GetStarted5`, examples of the Pub API; `java/src/overview-pub.html`
shows `Demo`. Nothing runs them, but every build compiles them, and a
published BergDB would want them (005-05). Proposed: keep.


C5. Figures and printed examples (for Frans)
--------------------------------------------

`bergdb.dev.VizFigure` and `VizFigureSet` (GraphViz figures of a
database's graph), `DagExamples` and `PrintableDagExamples` (printed Dag
examples "for a document"): 4 files, 546 lines. Nothing runs them; they
may be of use for figures in a publication (005-06). Not in the patch.


D1. Tests and benchmarks of Java itself
---------------------------------------

`java/src-dev/bergdb/test/java/`, all 37 files (3,869 lines): they use no
BergDB code at all. 35 classes measure Java (hashing, byte buffers, zip,
ciphers, method calls, maps, clocks...); their tests are perf tests, which
nothing runs (D2). `JudyNode` (451 lines) is a 256-ary prefix tree with
nine unit tests that test only itself. With them,
`bergdb.dev.StringTester` (four unit tests of how Java's strings behave on
IKVM and GCJ) and `bergdb.dev.Pack`, which lists only `StringTester`. The
test-java and dev packs leave `TestClasses`.

With B1 to B3, the unit tests go from 948 to 929: 21 go (`Cache2` 5,
`DagChecksum` 3, `StringTester` 4, `JudyNode` 9) and 2 come (`DbDouble`);
the f-tests go from 37 to 36 (`Cache2`'s).


D2. The perf tests
------------------

The test group "perf" runs only through `bergdb.dev.Perf`, which no
script runs; the performance harness of 2026 (`performance.sh`) and Props
(`level1.sh`, step 6) measure performance now. Removed: `dev/Perf.java`,
the six classes whose only tests are perf tests (`FileSynchPerformance`,
`GetScalability`, `GetManyScalability`, `OneByteToFile`, `OneGig`,
`StreamSize`), and the perf test methods of `Get`, `GetThreaded`,
`PerfGetMany`, `Set`, `BigDb` and `BigDbWithDeletes` with what only they
use. `Get`, `GetThreaded`, `PerfGetMany` and `Set` stay, but leave the
test pack: Props's CORE (`props/Core.java`) uses their `corePerfMethod`.
Tests in two groups, such as "f perf", stay.


D3. The night tests (for Frans)
-------------------------------

The group "night" runs only through `bergdb.dev.Night`, which no script
runs: `java/src-dev/bergdb/test/night/` (`BryanIssueNight`,
`CcDbNightTest`, `Issue150420` with its data file, `PayTest`, the pack),
`dev/Night.java`, and `core/KvComparison.java`, which only `Issue150420`
uses: 9 files, 1,790 lines. They are long-running tests of BergDB, from
2015: cards in a database, payments, the issue of 2015-04-20 and Bryan's
issue at a larger scale. They pass today: 7 of 7, in 255 s, on the code
with the patch. Not in the patch. Frans decides: keep them as they are,
run them in a gate (`bergdb.dev.Night`, about four minutes, for example
in `level3.sh`'s full run), or remove them. Proposed: keep them and run
them in a gate; tests that nothing runs rot, as B3 shows.


E1. The 2017 Ant build
----------------------

`java/build.sh` replaced it in 2026. Removed:

* `java/build.xml` (248 lines; its paths and JDK are those of 2017),
* `java/readme.txt` (it describes `ant jar`, Java 5 and `out/`;
  README.md describes the build now),
* `java/in/jarjar-1.4.jar` (120 kB; the Ant build's versioned jar),
* `java/in/BuildInfoTemplate.txt` (the Ant build generated `BuildInfo.java`
  from it; `build.sh` compiles `BuildInfo.java` as it is),
* `java/in/style.css` (the Ant build's Javadoc style).

Edited: `java/in/readme.txt` (its paragraph on jarjar), the comment of
`BuildInfo.java`, and a comment in `build.sh` that names `build.xml`.
After this no script makes Javadoc; the overview pages and the
`package.html` files stay, as documentation. If the ICU jar is ever made
again, jarjar can be fetched again (`in/readme.txt` says how the jar was
made, not how it was renamed).


F1. Unused Lean lemmas
----------------------

20 lemmas that no theorem, test, executable or document uses (124 lines,
14 files in `lean/SIS/Proof/`): `Grow.mono`, `Grow.sameNodes`,
`view_grow`, `SameNodes.trans`, `SExt.refl`, `versionAt_cons_zero`,
`parts_i`, `stillOK_of`, `stub_node`, `lastFa_cut`, `reachOnPath_congr`,
`Mem.KeepCore.keepPos`, `Mem.KeepRead.refl`, `Mem.KeepRead.trans`,
`Mem.linkD_table`, `RootPerm.cacheOp`, `applyChange4_canonicalOf`,
`follow4_root_ne`, `frame_refl`, `withRoot_withRoot`. Of 2,048
declarations, these are all that nothing uses, but for nine `@[simp]`
lemmas, which stay (see the method). The proofs have little unused code;
this group is small.


G1. Public API members that nothing here uses (a question)
-----------------------------------------------------------

No test or tool in the repository calls these 25 methods of the public
API, or makes the two exceptions. They are the API, so they are
not proposed for removal; the question is whether each should stay as it
is, get a test, or go.

Correction, 2026-10-20: this looked at the declarations in the API only.
For eight of the methods, the code behind the declaration is used
(`cacheSizeInMb` and `startupDistanceInMb` by `DatabaseBuilderImp`'s
tests, for example); see ../10-unused-code.md, "G1".

* `Connection`: `getEnableKeyReplace()`, `put(Object)`.
* `Database`: `getFirstAvailableLookupTime()` (docs/levels.md documents
  it as the expiry contract), `addReplica`, `removeReplica`,
  `getStorageInfos()`.
* `DatabaseBuilder`: `replica`, `startupDistanceInMb` (docs/levels.md),
  `cacheSizeInMb` (docs/level4-alignment.md, M45).
* `Duration`: `add`, `days`, `hours`, `minutes`. `Time`: `substract`,
  `getDate`.
* `ReadInterface`: `exists`, `get(String, Class)`. `RwEnvironment`:
  `exists`, `setOutput`. `Transaction.getOutput`. `UseIndexBuilder`:
  `prefix`, `kvs`. `util.Job.join(int)`.
* `Factory.printHello()`, `CryptoKey.main`.
* The exceptions `NoFieldsSetException` and `NoSuchObjectException`.

Replication (`addReplica`, `replica`) is implemented in `pubimp`, but no
test exercises it.


What stays, and why
===================

Looked at and kept, so that the same ground is not searched again:

* `bergdb.dev.Run`: the jar's main class (`build.sh`'s manifest).
* `bergdb.dev.props`: `level1.sh` runs `Mem`, `SS` and `Core`; item
  006-02's `run.sh` runs `Props`.
* Stress tools that no script runs but the documents cite: `StreamDigest`
  (docs/level3-alignment.md and others), `A2A3Check`
  (docs/level2-alignment.md), `DbJunk` (the same), `ReclaimHitRate`
  (docs/level4-alignment.md). `BryanRepro`'s data class, as Bryan wrote
  it.
* `java/stress/restart-experiments.diff`, `native/trace-flush-macos.c`,
  `validate-flush-trace.py`, the `.suite` files: cited or used by scripts.
* ICU: `in/icu-for-bergdb.jar`, `in/ICU-LICENSE.html`, `src-icu/`: the
  Pub API's ICU collators, loaded by name.
* JMX, `core/Jmx.java` whole: docs/level4-alignment.md names
  `Jmx.DbMonitor` as the way to read and set the budget, and `register()`
  is how it gets into JMX; `Jmx.Speed` with it.
* The Javadoc pages (`overview-*.html`, `package.html`) and
  `core/doc-files/`.
* `lean/References/` (outside `lake build`; docs/reference-theory.md and
  its `check.sh`, which passes on the patch), `lean/test-traces/`
  (lean/README.md).
* Members: 6 empty private constructors (classes of static members only),
  3 nanotest fixtures, 4 fields of classes stored by reflection, 7
  abstract methods with a used implementation and 2 overrides of them,
  the main methods of classes that stay, and 3 members that kept code
  needs. Unused code in the files of C3, C5 and D3 is left with them.


Checks
======

On a clone of `1f4b637` with the patch (`tools/gates.sh`, 2026-10-19,
20:35 to 21:16 on F53, nothing else running; the output is in
[runs/](runs/)):

| Check | Before | With the patch |
|---|---|---|
| `java/build.sh` | builds | builds |
| Unit tests (`bergdb.dev.Unit`) | 948 pass | 929 pass (B1 to B3, D1) |
| f-tests (`bergdb.dev.F`) | 37 pass | 36 pass (B1) |
| `level1.sh` | | `LEVEL 1 OK` (169 s) |
| `level2.sh` | | `LEVEL 2 OK` (769 s) |
| `level3.sh` | | `LEVEL 3 OK` (506 s) |
| `level4.sh` | | `LEVEL 4 OK` (871 s) |
| `lake build` | | completes (136 jobs) |
| Props MEM, three runs | 192, 191, 191 | 191, 191, 191 |
| `lean/References/check.sh` | | passes |

The gates were not run here without the patch; 005-02 and 005-08 record
them passing with their changes (docs/log.md, 2026-10-19). Level 1's
Props: MEM 192 at its run, SS 1.50 (1.10, 1.19, 1.62, 2.37), within the
limits. Level 4's conformance: 30 traces, `TRACECHECK OK` 30. The items'
Java tools compile against the patched build as before (two of them,
`M46Bound` and `IndirectionBench`, fail to compile before and after, for
reasons of their own). The night tests: see D3.


After the decision
==================

1. Frans's decision is recorded in 10-unused-code.md, with the IDs.
2. The plan files follow it: `plan/delete-files.txt` loses the groups that
   stay; files whose unused members stay go into `members.py`'s
   `SKIP_FILES`, and single members that stay (struck from A3, or all of
   A2 or A3) into its `KEEP`; `plan/lean-remove.txt` loses what stays. A
   group that is approved later (C3, C5, D3) gets its files added to
   `delete-files.txt`, with the edits that follow (its pack, `Run`'s help,
   `TestClasses`).
3. `tools/make-patch.sh` makes the patch on a fresh clone of what is then
   committed (the line numbers of the members are found again, so later
   commits do not matter), and `tools/gates.sh` runs the checks there.
4. The change is copied into the main tree (`git diff` of the clone,
   applied with `git apply`), the four gates run once more on the combined
   tree, and the documents that name removed code are checked again. Frans
   commits.

Best done when no other change to `java/` is under way: the patch touches
182 files.


Files
=====

* [tables/files.tsv](tables/files.tsv): the files the patch deletes, with
  their group and lines.
* [tables/members.tsv](tables/members.tsv): the members it removes, with
  their group, file, lines and kind.
* [tables/kept.tsv](tables/kept.tsv): the unused members that stay, with
  the reason.
* [tables/api-unused.tsv](tables/api-unused.tsv): G1.
* [tables/lean.tsv](tables/lean.tsv): the unused Lean declarations, those
  removed and the `@[simp]` ones kept.
* [plan/](plan/): what the patch removes and edits (`delete-files.txt`,
  `edits-*.py`, `lean-remove.txt`).
* [tools/](tools/): the tools, with `README.md`.
* [runs/](runs/): the checks' output.
* [edits.patch](edits.patch): the patch's changes to the files that stay
  (the deleted files are listed, not copied).
