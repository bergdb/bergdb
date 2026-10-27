006-08 The Core Layer, built alone
==================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: done.

Frans: "Check BergDB Core Layer independence. Can a version be build from
the bergdb.core package with dependencies. The user of the database would
call the methods of Db directly. Ensure there are not dependencies on
classes in packages beyond what is allowed according to the package.html
documentation."

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
* `runs/`: the output of the checks above.

P12 has no measure yet (010-01). `deps.py` and `core-build.sh` could be
one, as a step in `java/before-commit.sh` (about 15 s with the unit tests);
not added, as the commit gate is Frans's call.
