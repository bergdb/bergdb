005-56. Investigate the package dependencies
============================================

Status: done (2026-10-28; see Outcome). Kind: investigate. Created 2026-10-26.

Registered at Frans's request (2026-10-26: "Add a todo item to 005 to
investigate package dependencies. How do packages depend on each other?
Does this follow the documentation in package.html files?"). The same day,
010-01's P12, a small Core Layer, checked the Core Layer's imports against
the `package.html` files: five mismatches, none from the core upward.


The issue
---------

Each package's `package.html` says which packages it may use ("Depends
on: ..."). Nothing checks it: `java/build.sh` compiles `src`, `src-dev`
and `src-icu` in one `javac` run, so any class can use any other. Two
older texts say what was intended, in the f1 repository's F1-007:

* The layers of 2012 (`bergdb/doc/2012/2012-08-layers.txt`): "A layer is
  only allowed to use the functionality provided by the layer immediately
  below it" (Public, DB, RecoverableStream, AppendOnlyStream); of a
  package that would use the layer above it: "Not something I like".
* The package dependencies of 2015 (`bergdb/doc/2015/2015-q4-notes.txt`,
  "Package dependencies"; "Similar to now, few changes."): every package
  may use `nanotest`, and every package but `nanotest` may use `common`.
  Besides those, `storage` uses `pub.util` and `stream`; `core` uses
  `pub.util`, `stream`, `storage` and `dag`; `pubimp` uses `pub.util`,
  `stream`, `storage` and `core`; `pub` uses `pub.util` and `pubimp`;
  `src-dev` uses any package; `stream`, `dag` and `pub.util` use nothing
  more.

A first look, 2026-10-26, at `4e0a849`: the import lines and `jdeps
-verbose:package` on the compiled classes give the same graph for
`java/src`. Four of its nine packages use packages that their
`package.html` does not list:

| Package | Its `package.html` | Also uses | Where |
|---|---|---|---|
| `stream` | common, nano, pub.util | `core`, `storage` | `FileStreamPowerLossTester` only |
| `dag` | common, pub.util | `nanotest` | `Assert`, `@Nano` and `IPack`, in 12 classes |
| `pubimp` | pub, core, stream, common, nanotest | `dag`, `storage`, `pub.util` | `dag`: `GetData`, `GetMany`, `Keys`, `Klong`, `Kvt` and `Spos`, in 8 classes; `storage`: `StorageManager`, its exceptions, and its streams in `PubTester` |
| `pub` | pub.util | `core`, `pubimp`, `common`, `nanotest` | `core.SyncLevel` in the `sync` methods of `Database`, `Connection` and `Transaction`; `pubimp` in `Database`, `Factory`, `TestClock` and `Time`; `common` and `nanotest` in `CryptoKey` and `Time` |

Beyond 010-01's five: `pub` also uses `pubimp`, `common` and `nanotest`,
and `pubimp` uses `pub.util`. The other five packages agree with their
lists: `nanotest`, `common`, `pub.util`, `storage`, and `core` since
`4e0a849` added `dag` to its list. `pubimpicu` (`src-icu`) has no list;
nothing names it but by reflection, as its `package.html` asks.

By the 2015 rule, which lets every package use `nanotest` and `common`,
the `dag` row and half of the `pub` row are stale lists, not code to
change. `dag` uses `pub.util`, which its list allows and the 2015 design
does not.

Cycles: `stream` with `core`, and `stream` with `storage`, both through
the tester; `pub` with `pubimp`, which `pubimp`'s list allows ("we allow
the circular package dependency: pubimp -> pub -> pubimp"). And
`pub/Factory.java` says that `new DatabaseBuilderImp()` "is the *only*
reference to the implementation package bergdb.pubimp"; `Database`,
`TestClock` and `Time` have three more.


After 006-08
------------

[006-08](../006-2026-q4/08-core-layer.md), 2026-10-26, checked that the
Core Layer (`core` and what its list allows: `common`, `dag`, `nanotest`,
`pub.util`, `storage`, `stream`) builds alone, and fixed its two
packages that broke their lists:

* `stream`: `FileStreamPowerLossTester` moved to `core`, and
  `stress/PowerLossTest` with it. `FileStreamIo` became public with
  protected methods, and `FileStream(File, FileStreamIo)` public, so that
  the tester can override them from `core`; Frans, 2026-10-27: "It is
  good as is." The cycles `stream` with `core` and with `storage` are
  gone.
* `dag`: its list has `nanotest`. `stream`'s list says `nanotest`, not
  "nano".

The Core Layer compiled alone before that too: none of its packages uses
`pub` or `pubimp`. Now each of the seven uses only what its list allows,
and they compile alone, with an empty class path (`core-build.sh`).

`deps.py` (006-08; imports and qualified names in code, without comments
and strings) on `java/src`, 2026-10-27: 7 uses not in a list, all in
`pub` and `pubimp`:

| Package | Its `package.html` | Also uses | Where |
|---|---|---|---|
| `pub` | pub.util | `common`, `nanotest` | `CryptoKey`; `nanotest` also in `Time` |
| `pub` | | `core` | `SyncLevel`, in `Connection`, `Database` and `Transaction` |
| `pub` | | `pubimp` | `Database`, `Factory`, `TestClock` and `Time` |
| `pubimp` | pub, core, stream, common, nanotest | `dag` | 8 classes, among them `ConnectionImp`, `IndexManager` and `RwEnvironmentImp` |
| `pubimp` | | `storage` | `DatabaseBuilderImp`, `DatabaseImp`, `IndexBuilderImp`, `PubTester` and `RwTransaction` |
| `pubimp` | | `pub.util` | 16 classes |

The only cycle left in `java/src` is `pub` with `pubimp`. Also found by
006-08, outside `java/src` or without a dependency:

* `java/stress/BryanRepro.java` is in package `bergdb.core` but uses only
  the Pub API (question 1).
* Two comments in `core` name classes of other packages: `TestClock`
  ("Copy of class: bergdb.pub.TestClock") and `DbTester`
  (`bergdb.test.StreamSize`). A comment in `storage/Constants.java` named
  `bergdb.core.Spos`; it says `bergdb.dag.Spos` since 006-08.

`deps.py` scans `java/src` only; question 1's `src-dev`, `src-icu` and
`stress` are still to do.


The check, with test code apart (2026-10-27)
--------------------------------------------

By Claude (Opus 5.5, Claude Code), 2026-10-27 (006-09, W6.3).
[56-package-dependencies/check-deps.py](56-package-dependencies/check-deps.py)
(`python3 -I check-deps.py [java/src]`, under a second) builds on 006-08's
`deps.py`: the same uses (imports and qualified names, without comments and
strings) and the same reading of the four forms of list, but each use is
production code or test code. Test code: a file whose name contains
`Tester`, or whose class implements `IPack` (each package's `Pack`); a
nested class whose name contains `Tester`; a method annotated `@Nano`; a
static `void test...` method; and, repeated until nothing changes, a method
or nested class whose name is used in the file only by test code (the
tests' helpers). An import counts as test code when every use of its
simple name is. Limits: a helper whose name is also used for something
else (`Eviction.values`, beside `Map.values`) counts as production, and so
does a helper in a production file that only another file's tests call.
Exit status 1 when a use is not in the list.

On HEAD `e747323`, `java/src`: the same 7 uses not in a list as 006-08
found, all in `pub` and `pubimp`; 6 are production code.

| Package | Uses, not in its list | Code | Where | Which looks wrong |
|---|---|---|---|---|
| `pub` | `common` | production | `CryptoKey`: `StringUtil`, `SeedGenerator`, `Util` | The list: the 2015 design lets every package use `common` |
| `pub` | `core` | production | `SyncLevel` in the `sync` methods of `Connection`, `Database` and `Transaction` | The code: a Core type in the Pub API's signatures (010-01); `SyncLevel` belongs in `pub.util` or the Pub API. An API change, for Frans |
| `pub` | `nanotest` | test only | the `@Nano` methods of `CryptoKey` and `Time` | The list, if test code may use `nanotest` (question 2; the 2015 design allows it for every package) |
| `pub` | `pubimp` | production | `Factory` (`new DatabaseBuilderImp()`); `Database.PRIMARY = IndexManager.PRIMARY`; `TestClock` (`ClockConstants.MIN_TIME`, `MAX_TIME`); `Time` (`TimeResolver`) | `Factory`: the list (the designed cycle, which `pubimp`'s list allows and the 2015 design lists). The other three: the code, small; `Factory`'s comment says it is the only reference. The constants can live in `pub`; `TimeResolver` is a larger move |
| `pubimp` | `dag` | production (also `PubTesterIndex`) | `GetData`, `GetMany`, `GetMany.StopCondition`, `Kvt`, `Keys`, `Klong`, `Spos`, in 7 production classes | The list: `GetData`, `GetMany` and `Kvt` are in `Db`'s public signatures (`newGetData`, `getOne(..., GetData)`, `newGetMany`, `getMany(GetMany)`, the `Kvt` handler), and `Keys` and `Klong` make the `long[]` key segments that `getOne` takes, so the Core API needs them. `Spos` is one `Spos.NULL` in `ConnectionImp`, and `ClockConstants` only copies `Klong.MIN_TIME` and `MAX_TIME`. 010-P12's "dag, storage and stream are under them" should then name these types as part of the Core API |
| `pubimp` | `pub.util` | production (also 4 testers, `DbBoolean`, `DbByteArray`) | 12 production classes | The list: `pub.util` is the package shared with lower layers, and the 2015 design lists it for `pubimp` |
| `pubimp` | `storage` | production (also `PubTester`) | `StreamIoException`, `StreamFormatException` (thrown through `Db`), in `DatabaseBuilderImp`, `DatabaseImp`, `IndexBuilderImp`, `RwTransaction`; `StorageManager`'s buffer constants in `DatabaseBuilderImp` and `DatabaseImp` | The list for the exceptions, which come through the Core API (the 2015 design lists `storage` for `pubimp`); the constants could come from `DbBuilder`'s defaults |

What test code adds: only `pub` → `nanotest`. In `common`, `storage`,
`stream`, `pub` and `pubimp`, `nanotest` is used by test code only; in
`core` and `dag` also by production code, which their lists allow:
`KeyNode.checkLastTimeIndex` (an invariant check) and `Eviction`'s `Twin`
(the check under the test schedule `EVERY`) call `Assert`. So the rule "the
lists cover production code; test code may also use `nanotest`" leaves
6 mismatches: 4 the lists' (`pub` → `common`, `pubimp` → `dag`,
`pub.util`, `storage`), 1 the code's (`pub` → `core`), and `pub` →
`pubimp` both (`Factory` by design, three small uses not).


Questions
---------

1. The graph, in full: `java/src`, `java/src-icu`, `java/src-dev` and
   `java/stress`, from the class files (`jdeps`) and from the source (a
   constant that `javac` inlines leaves no trace in the class file);
   which edges come only from test code (the testers and the Nanotest
   methods in `java/src`); the cycles.
2. The rule: the `package.html` lists, the 2015 design (`nanotest` and
   `common` for every package), or a new one? May test code in
   `java/src` use more than its package's production code?
3. Each difference: is the code wrong (a dependency to remove) or the list
   (a line to change)? Above all:
   * `pubimp` uses `dag` and `storage`. 010-P12: "The API is Db's public
     methods; dag, storage and stream are under them." Which of these
     types are in `Db`'s public signatures, and which uses go around the
     Core API?
   * `pub` has `core.SyncLevel` in the Pub API (010-01).
   * `stream`'s tester uses `core` and `storage`, two layers above it.
     Done in 006-08: the tester moved to `core`.
   * `pub` and `pubimp` use each other, by design.
4. A check that keeps the lists true: a unit test, or a step in
   `java/before-commit.sh`, that compares each package's dependencies with
   its `package.html`; 010-01 names it as a candidate measure for P12. The
   lists then need one form; today they say "Depends on:",
   "Dependencies:", "Package dependencies:" and "Allowed dependency:".
   Two such tools exist since 2026-10-26, in
   [006-08](../006-2026-q4/08-core-layer.md): `deps.py` compares each
   package's uses with its `package.html` (it reads all four forms), and
   `core-build.sh` builds the Core Layer alone and runs `CoreDemo` and the
   Core Layer's unit tests on it (about 15 s). Should both become a step
   in `java/before-commit.sh`? Frans, 2026-10-27: decided when this entry
   is worked on.
5. The rest of the `package.html` files: stale titles (`pub.util`'s
   "Package bergdb.pub", `pubimp`'s "Package com.bergdb.pubimp",
   `pubimpicu`'s "Package dev"), `stream`'s "nano" (fixed in 006-08),
   and three packages in `src-dev` without one (`bergdb`,
   `bergdb.dev.props`, `frans.bryan`).


Done when
---------

* A report, here or in `56-package-dependencies/`: the graph, each
  difference with the rule it breaks and a proposal (change the code or
  the list), and a proposal for the check.
* Frans has decided; what he decides is done, or registered as Fix
  entries.


First step
----------

`jdeps -verbose:class` on `java/build/classes` (without the ICU classes),
grouped by package pair, beside each package's list and the 2015 design;
then question 3's cases, from the code.


Size and order
--------------

S for questions 1, 2, 4 and 5. Question 3 may grow it: `SyncLevel` is in
the Pub API's signatures, and `pubimp`'s uses of `dag` touch P12. Question
4's check would be P12's measure (010-01).


Decision
--------

Frans, 2026-10-28 (006-09, section 8, decision 6): "005-56, as the
entry's table proposes: change the lists for pub→common, pub→nanotest
(test code only), pubimp→dag, pubimp→pub.util and pubimp→storage; change
the code for SyncLevel (move to pub.util, which core already uses; an API
change against 2026.1, note it for the release notes) and pub→pubimp's
three small uses (Database.PRIMARY, TestClock's constants into pub;
TimeResolver may wait), Factory stays (the designed cycle); one form for
the package.html lists; deps.py as a step in java/before-commit.sh."


Outcome
-------

2026-10-28, by Claude (Opus 5.5, Claude Code), as decided; in a clone on
`1ad7cdc`.

* **The lists, in one form.** Every `package.html` in `java/src` says
  `Depends on: a, b, c.`, the packages in alphabetical order, or `Depends
  on: nothing.` (`nanotest`); more text may follow the period. This is the
  form that `bergdb.dev`'s `package.html` already asked for ("a statement
  like: Depends on: list-of-packages", checked by a `jdepend.sh` that is
  gone); its paragraph now names `java/deps.py`.
  `common`'s "Package dependencies: nanotest (only)", `dag`'s
  "Dependencies: ...", `pub`'s "Dependencies: ..." and `pub.util`'s
  "Allowed dependency: ..." are in the form now, and `core`'s and
  `storage`'s lists are sorted. Changed lists: `pub` gets `common`,
  `nanotest` (its text says only test code, the `@Nano` methods, uses it)
  and `pubimp` (`Factory`, the circular dependency by design, and
  `TimeResolver`); `pubimp` gets `dag`, `pub.util` and `storage`.
* **`SyncLevel`** moved from `bergdb.core` to `bergdb.pub.util` (`git
  mv`, the package line its only change), so `pub` no longer uses `core`.
  55 files: the class, its 20 imports changed (`pub`'s `Connection`,
  `Database` and `Transaction`, 5 in `pubimp`, 12 in `src-dev`) and 34
  imports added (17 files of `core`, among them `Db`, `Eviction`,
  `Reclaim` and the testers, which used it without an import; `BigDb`
  and `BigDbWithDeletes` in `src-dev`, which import `bergdb.core.*`; 15
  stress programs, among them `Perf`, `Soak`, `TraceExport` and
  `RestartStress`). An API change against 2026.1: a line in
  `releases/next.md`. Tools in `items/` that import `bergdb.core.SyncLevel`
  are left as they are; they were run against the code of their day.
* **`Database.PRIMARY`** is defined in `pub` (`Util.identity("primary")`,
  so that it is not inlined, as `pubimp`'s dev notes ask), and
  `IndexManager.PRIMARY` is `Database.PRIMARY`.
* **`TestClock`** checks against `Time`'s own range, `MIN_IN_UNITS` and
  `MAX_IN_UNITS`, now package-private, instead of `pubimp`'s
  `ClockConstants`, which only copied `Klong.MIN_TIME` and `MAX_TIME` for
  it and is deleted. `PubTester.testTimeRangeIsTheCores` checks that
  `Time`'s range is `Klong`'s.
* **`TimeResolver` waits**, as Frans allowed: 646 lines with its own
  Nanotest tests in `pubimp`'s `Pack`, and it uses `core.SystemClock`;
  moving it into `pub` is not small. So `pub` uses `pubimp` in `Factory`
  and `Time`, and `Factory`'s comment that its `new DatabaseBuilderImp()`
  is "the *only* reference" to `pubimp` is still not quite true.
* **The check**, `java/deps.py` (`python3 -I java/deps.py [JAVA_SRC]`,
  under a second), is `check-deps.py` made a tool of the build: it reads
  only the one form, and a package in `java/src` without a list, with a
  list in another form, out of order or naming a package that does not
  exist is a failure ("BAD LIST"), as is a use that the list leaves out
  ("NOT ALLOWED", now with the two packages). The list covers production
  and test code alike; the split is still printed. `java/before-commit.sh`
  runs it after the build, logs to `build/before-commit/deps.txt`, prints
  `Deps: 9 packages, all as package.html allows`, and on a failure prints
  the failing lines and `BEFORE COMMIT FAILED: package dependencies: ...;
  change the code or the list`. Tried on a copy of `java/src` with
  `pub`'s old list, `common`'s old form and `storage`'s old order: 5
  failures, exit status 1. `check-deps.py` stays here as the
  investigation's tool.

The check on the result, `java/src`:

| Package | Production code uses | Only test code uses | `package.html` |
|---|---|---|---|
| `common` | nothing | nanotest | nanotest |
| `core` | common, dag, nanotest, pub.util, storage, stream | nothing | the same |
| `dag` | common, nanotest, pub.util | nothing | the same |
| `nanotest` | nothing | nothing | nothing |
| `pub` | common, pub.util, pubimp | nanotest | common, nanotest, pub.util, pubimp |
| `pub.util` | nothing | nothing | common |
| `pubimp` | common, core, dag, pub, pub.util, storage, stream | nanotest | common, core, dag, nanotest, pub, pub.util, storage, stream |
| `storage` | common, pub.util, stream | nanotest | common, nanotest, pub.util, stream |
| `stream` | common, pub.util | nanotest | common, nanotest, pub.util |

"9 packages, all as package.html allows". The only cycle is `pub` with
`pubimp`.

* Gates, in the clone, on the final tree: `java/before-commit.sh` (`Deps: 9
  packages, all as package.html allows`; unit 1056 tests, f 74; `BEFORE
  COMMIT OK (89 s)`) and `java/stress/level2.sh quick` (`LEVEL 2 OK`).
  `build.sh` compiles every stress program, so all 15 that use
  `SyncLevel` compiled.

Not done, as the decision did not ask: question 1's graph of `src-dev`,
`src-icu` and `stress` (`deps.py` scans `java/src`), and question 5's
stale titles (`pub.util`'s "Package bergdb.pub", `pubimp`'s "Package
com.bergdb.pubimp", `pubimpicu`'s "Package dev") and the three `src-dev`
packages without a `package.html`. 010-01's P12 says "No measure today";
`deps.py` in `before-commit.sh` is one now.

Files: [56-package-dependencies/](56-package-dependencies/):
`check-deps.py` (the check of 2026-10-27; `java/deps.py` since),
`deps.txt` (`java/deps.py`'s output on the result) and `gates.txt` (the
gates' output).


Follow-ups, 2026-10-28
----------------------

Frans, 2026-10-28, on the five points left over above: "as proposed", and
"Do not add core-build.sh to before-commit.sh. Ensure it runs nightly.
From night.sh somehow." Done by Claude (Opus 5.5, Claude Code), in a clone
on `a45467c`:

1. `src-dev`, `src-icu` and `stress` are not checked by `deps.py`: no
   action; it scans `java/src`, as before.
2. The stale titles are corrected: `pub.util`'s is "Package
   bergdb.pub.util", `pubimp`'s "Package bergdb.pubimp", `pubimpicu`'s
   "Package bergdb.pubimpicu".
3. `src-dev`'s `bergdb` (only `Help`), `bergdb.dev.props` (the properties
   of 2014 to 2017, MEM, CORE and SS) and `frans.bryan` (Bryan Wisdom's
   program of 2015-11) have a short `package.html` in the form of the other
   `src-dev` packages. `bergdb.dev.props` and `frans.bryan` also have a
   `package-info.java`, which Javadoc prefers; the two say the same.
4. `Factory`'s comment names both of `pub`'s references to `pubimp`: its
   `new DatabaseBuilderImp()` and `Time`'s use of `TimeResolver`.
5. 010-01's P12 names its measures: `java/deps.py` in `before-commit.sh`,
   and the Core Layer built alone, nightly. The number of Db's public
   methods stays a candidate.
6. 006-08's `core-build.sh` is a tool of the build: `java/stress/core-build.sh`
   (`java/stress/core-build.sh [GROUP...]`, unit by default), with
   `CoreDemo.java` and `CoreUnit.java` in `java/stress/core-build/`
   (`CoreDemo` imports `SyncLevel` from `pub.util` now). It runs from
   `java/`, on `src/`, writes `build/core-build/`, and uses `java/deps.py`,
   which got `--layer PKG [--list]` for it: only the package and the ones
   it may use, directly or not (for `core`, the Core Layer's seven). It is
   step 2 of `java/night.sh`, `core-build`, with the unit and f groups,
   about 50 s: its last line in the report, and a failure makes the night
   FAILED. Not in `before-commit.sh`. `README.md` and `docs/levels.md`
   name it among the night's steps. The copy in
   [006-08's directory](../006-2026-q4/08-core-layer/) stays, as history.

Tested: `java/stress/core-build.sh unit f` on the clone, `CORE BUILD OK`
(177 source files, 430 classes, a jar of 714,723 bytes; unit 674 tests,
f 54), about 50 s. One earlier run failed in
`StorageManagerTester.testAddReplica2`, the known race (about one run in
twelve, 001-05), which the night now runs twice. Not the full
night run: `sh -n night.sh`, and night.sh's `step` function, cut from the
script by `sed`, run on the clone (`core-build ok 48 s CORE BUILD OK`)
and on a copy with a `core` class using `pub` (`core-build-bad FAILED 1 s
CORE BUILD FAILED: deps.py`, in the failed steps). The gate, on the
rebased tree: `java/before-commit.sh` (`Deps: 9 packages, all as
package.html allows`; unit 1058 tests, f 74; `BEFORE COMMIT OK (93 s)`).
