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
   * `pub` and `pubimp` use each other, by design.
4. A check that keeps the lists true: a unit test, or a step in
   `java/before-commit.sh`, that compares each package's dependencies with
   its `package.html`; 010-01 names it as a candidate measure for P12. The
   lists then need one form; today they say "Depends on:",
   "Dependencies:", "Package dependencies:" and "Allowed dependency:".
5. The rest of the `package.html` files: stale titles (`pub.util`'s
   "Package bergdb.pub", `pubimp`'s "Package com.bergdb.pubimp",
   `pubimpicu`'s "Package dev"), `stream`'s "nano", and three packages in
   `src-dev` without one (`bergdb`, `bergdb.dev.props`, `frans.bryan`).


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
