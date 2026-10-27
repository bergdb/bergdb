005-56. Investigate the package dependencies
============================================

Status: open. Kind: investigate. Created 2026-10-26.

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

A first look, 2026-10-26, at `cc8effb`: the import lines and `jdeps
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
`cc8effb` added `dag` to its list. `pubimpicu` (`src-icu`) has no list;
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

On HEAD `a6cd234`, `java/src`: the same 7 uses not in a list as 006-08
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
