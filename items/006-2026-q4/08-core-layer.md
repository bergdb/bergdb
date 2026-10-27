006-08 The Core Layer, built alone
==================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: done.

Frans: "Check BergDB Core Layer independence. Can a version be build from
the bergdb.core package with dependencies. The user of the database would
call the methods of Db directly. Ensure there are not dependencies on
classes in packages beyond what is allowed according to the package.html
documentation."

2026-10-27, "The Core without its tests" added by Claude (Opus 5.5, Claude
Code), from a session of 2026-10-26 on Frans's question: "Is The Core
independent from the test of the code. How large would a build of only the
Core be compared to the full database. Assume users would call the methods
of Db directly instead. How large would the core be. How many lines of
code? Do not cound test code. This question is relevant for the
possibility of using the database or some type of clone to C or rust for an
embedded target where code size matters."

The Core Layer here is `bergdb.core` and the packages it may use, directly
or not, by the `package.html` files: `common`, `dag`, `nanotest`,
`pub.util`, `storage` and `stream` (010-P12). The tools and their output
are in [08-core-layer/](08-core-layer/).


Answer
------

Yes. The seven packages compile alone, from `java/src` with an empty class
path: 175 source files, 415 classes, a jar of 680 kB (`build/bergdb.jar`,
with `pub`, `pubimp`, `src-dev` and the ICU classes, is 3.3 MB). Of the
JDK, the classes need `java.base` and `java.management` (the JMX bean), no
more. A program outside the `bergdb` packages, with that jar alone on its
class path, writes to a database in a directory and reads from it with
`execute`, `getOne`, `getMany` and `getTrans`, and reads the same after a
restart. The Core Layer's own tests pass on that jar alone: 648 of the
1,023 unit tests and 52 of the 71 f-tests.

The seven compiled alone before this change too: none of them uses `pub`
or `pubimp`. But two of them used packages that their `package.html` does
not allow. Now each of the seven uses only what its `package.html`
allows.

Without its test code, what `Db` needs is 14,677 code lines and a jar of
335 kB, two thirds of BergDB's production code; but the tests are in the
production files, and a script must remove them first ("The Core without
its tests").


What did not follow package.html
--------------------------------

At `cc8effb`, by `deps.py` (imports, and qualified names in the code;
`jdeps -verbose:package` on the compiled classes gives the same pairs):

| Package | Uses, not in its `package.html` | Where | Now |
|---|---|---|---|
| `stream` | `core`, `storage` | `FileStreamPowerLossTester`, a tester | moved to `core` |
| `stream` | `nanotest` | Nano tests in 6 classes, and `Pack`; the list said "nano" | the list says `nanotest` |
| `dag` | `nanotest` | Nano tests in 11 classes, and `Pack` | `nanotest` added to the list |

`core`'s list left out `dag` until Frans's `cc8effb`, the same day. Every
other package of the Core Layer may use `nanotest`, and so may every
package in Frans's design of 2015 (F1-007, `bergdb/doc/2015/2015-q4-notes.txt`,
"All packages can depend on nanotest"; 005-56).


The change
----------

1. `FileStreamPowerLossTester` moved from `bergdb.stream` to `bergdb.core`.
   It runs `StorageManager` and `Db` over its model of the file system, so
   only a package that may use `storage` and `core` can hold it. In the
   file: the package line, the imports, `protected` on the 11 methods that
   override `FileStreamIo`'s, and two lines of Javadoc on why it is in
   `core`. Its tests and its output are the same (Checks).
2. `FileStreamIo`, the persistence boundary that the tester replaces, was
   package-private. It is public now, with protected methods, and
   `FileStream`'s constructor that takes one is public. This is the only
   change to production code: `stream`'s public API grows by this class
   and this constructor, a seam for fault tests.
3. `java/stress/PowerLossTest.java`, step 7 of `level3.sh`, followed the
   tester to `bergdb.core`; `level3.sh` runs `bergdb.core.PowerLossTest`.
4. The `Pack` lists: the tester left `stream`'s and joined `core`'s.
5. `package.html`: `dag`'s list has `nanotest`; `stream`'s "nano" is
   `nanotest`.
6. `storage/Constants.java`: a comment named `bergdb.core.Spos.NULL`; `Spos`
   is in `dag`. A comment only, no dependency.

The other way, `stream`'s list allowing `core` and `storage` for its
testers, would have kept a cycle: `stream` to `core` to `stream`.


Checks
------

In a clone, with the change:

* `java/before-commit.sh`: `BEFORE COMMIT OK` (142 s), 1,023 unit tests
  and 71 f-tests, as before. The tester runs as
  `bergdb.core.FileStreamPowerLossTester`; its f-test prints the same
  `POWER TRACE` line as in earlier runs (seed 17, 19 checkpoints, 6
  physical deletes, the same stages).
* Step 7 of `level3.sh`, the command as the script runs it: quick (1 seed,
  600 transactions) `POWERLOSS OK` with 19 cold recoveries, in 4 s; full
  (8 seeds, 1,500 transactions) `POWERLOSS OK` with 440, as in the 16
  earlier runs in `items/`, in 40 s.
* `core-build.sh` with the unit and f-tests: `CORE BUILD OK`.
* `deps.py` on all nine packages of `java/src`: 11 uses not in a
  `package.html` before, 7 after, all in `pub` and `pubimp`.


Outside the Core Layer
----------------------

Not changed; they are 005-56's:

* `pub` uses `core` (`SyncLevel`, in the `sync` methods of `Database`,
  `Connection` and `Transaction`), `pubimp` (in `Database`, `Factory`,
  `TestClock` and `Time`), `common` and `nanotest` (in `CryptoKey` and
  `Time`); its list allows `pub.util` only. `pubimp`'s list allows the
  cycle `pubimp` to `pub` to `pubimp`; `pub`'s does not.
* `pubimp` uses `dag`, `storage` and `pub.util`, which its list leaves
  out.
* `java/stress/BryanRepro.java` is in package `bergdb.core` and uses only
  the Pub API. It is not in `java/src`, so not in the Core Layer's build,
  but its package line says `core`.
* Two comments in `core` name classes of other packages, without a
  dependency: `TestClock` ("Copy of class: bergdb.pub.TestClock") and
  `DbTester` (`bergdb.test.StreamSize`).


The Core without its tests
--------------------------

The Core Layer's production code does not depend on its test code, except
for one line. But the tests are in the same files, so the Core cannot be
built without them as the code stands; a script must remove them first.
Without its tests, and with only what `Db` and `DbBuilder` need, the Core
is 14,677 code lines, two thirds of BergDB's production code, in a jar of
335 kB.

Much of the test code is in the production classes: 342 `@Nano` methods in
the Core Layer's production files (and 304 in its tester files), and also
`test*` and `main()` methods, nested `Tester` classes
(`RecoverableStream.Tester`) and the private helpers that only tests use
(`Eviction`'s twins). 52 of the Core Layer's production files use
`nanotest`. A few also import a tester (`DbHelper` uses `KeyNodeTester`,
`StoredTopNode` uses `TopTester`). `strip.py` removes all of this from a
copy. After that, one line of production code still uses `nanotest`:
`KeyNode.checkLastTimeIndex()` calls `Assert.assertEquals`; it could throw
`AssertionError` itself. Test-only code that `Db` still reaches stays in
the counts below: `Audit` and `TestClock` (304 code lines), `Db.TestHooks`
and `DbBuilder`'s test settings (`evictionSchedule`, `auditEvery`,
`secondTopOrdinal`).

By `core-size.sh`, at `3c807f1` (`runs/core-size.txt`):

| Build | Source files | Classes | Jar |
|---|---|---|---|
| The Core Layer, with its tests (`core-build.sh`) | 175 | 415 | 680 kB |
| The Core Layer, without its tests | 137 | 262 | 365 kB |
| What `Db` and `DbBuilder` need, without tests | 121 | 234 | 335 kB; 293 kB with `-g:none` |
| All of `java/src` and `src-icu`, without tests | 207 | 377 | 520 kB, and the ICU jar, 2,021 kB |
| `build/bergdb.jar`, with tests, `src-dev` and ICU | | | 3,263 kB |

| Code | Lines | Code lines |
|---|---|---|
| All of `java/src`, with its tests | 66,810 | 43,984 |
| All of `java/src` and `src-icu`, without tests | 38,348 | 22,017 |
| The Core Layer, with its tests | 47,770 | 31,445 |
| The Core Layer, without its tests | 27,346 | 15,773 |
| What `Db` and `DbBuilder` need, without tests | 25,649 | 14,677 |

A code line has code on it: not blank, not only a comment. What `Db` needs
is found by `javac` on `Db.java` and `DbBuilder.java` with the stripped
copy as source path: it compiles what they use, directly or not, and
nothing more. `CoreDemo` runs on that jar alone, and `jdeps` finds that it
needs `java.base` only. Of the Core Layer, `Db` does not need `Jmx` (the
reason for `java.management`), `DbScan`, `KeyFactory`,
`DagComparison`, `KvComparison`, `DagNodeIterator`, `StatsNodeVisitor`,
`OneFileStream`, `ReadOnlyStream` and a few small classes of `common`. The
upper layers, `pub` and `pubimp`, add 6,099 code lines; the ICU jar is most
of the full build's bytes.

The 14,677 code lines by part (`runs/closure-lines.txt`):

| Part | Code lines | Classes |
|---|---|---|
| `dag`: key, top and value nodes, `Klong`, `GetMany`, `Dag` | 3,617 | 25 |
| `core`: `Db` (1,320), `StoredTrans`, `DbStarter`, `NodeCollection`, `NodeStream`, `Trans`, the rest | 5,021 | 37 |
| `storage`: `RecoverableStream`, `MetaBlock`, the exceptions | 592 | 8 |
| `common`: `Bytes`, `MyChecksum`, `Util`, `StringUtil` and others | 908 | 12 |
| The replicas and the write buffer: `StorageManager`, `BufferedStream`, the rules | 1,261 | 9 |
| The streams: `FileStream`, `FileStreamIo`, `MemoryStream`, `AppendOnlyStream` | 941 | 6 |
| Memory: `Cache3`, `Eviction`, `Residents`, `Handle` | 930 | 6 |
| Reclaim: `Reclaim`, `CutStream` | 782 | 2 |
| Encryption: `Salsa`, `SalsaStream` | 243 | 2 |
| Test-only: `Audit`, `TestClock` | 304 | 2 |
| `pub.util`: exceptions, `Clock`, `Job`, `StorageInfo` | 78 | 12 |

For a port to C or Rust for an embedded target, where code size matters, an
estimate, not measured: without the test-only code, the replicas, the
encryption and `MemoryStream`, and with a simple buffered append and a
file or flash layer of the target's own, the Core is about 10,000 Java
code lines with reclaim, 9,000 without. Ported one to one, the line count
would be about the same in Rust or C. LMDB, about 7,000 code lines of C, is
about 100 kB of machine code, so a Core of this kind would be 60 to 150 kB.
The jar sizes do not predict this; bytecode is not machine code. The larger
question for a port is memory, not size: the node table, handles and
eviction are shaped by Java's objects and collector, and `BufferedStream`
and `Eviction` have threads of their own.


Tools
-----

In [08-core-layer/](08-core-layer/):

* `deps.py`: each package's uses of other `bergdb` packages against its
  `package.html`. `python3 -I deps.py java/src core` checks the Core Layer;
  without `core`, all nine packages. Exit status 1 for a use that a list
  does not allow. It reads the four forms of the lists ("Depends on:",
  "Dependencies:", "Package dependencies:", "Allowed dependency:").
* `core-build.sh`: `deps.py` on the Core Layer, `javac` on its sources
  alone with an empty class path, `jdeps`, `CoreDemo`, and the Core
  Layer's tests on its jar alone. `sh core-build.sh REPO [unit] [f]`:
  about 15 s with the unit tests, 85 s with both.
* `CoreDemo.java`: the user's program that calls `Db` directly.
* `CoreUnit.java`: runs the Nano tests of the given packages, as
  `bergdb.dev.Unit` does for all of them.
* `core-size.sh`: the Core Layer without its tests, what `Db` needs, and
  all of `java/src` without tests: each compiled, its jar, its lines, and
  `CoreDemo` on what `Db` needs. `sh core-size.sh REPO`: about 15 s.
* `strip.py`: removes the test code from a copy of the sources.
* `lines.py`: lines and code lines of Java files.
* `runs/`: the output of the checks above.

P12 has no measure yet (010-01). `deps.py` and `core-build.sh` could be
one, as a step in `java/before-commit.sh` (about 15 s with the unit tests);
not added, as the commit gate is Frans's call.
