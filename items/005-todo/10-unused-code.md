005-10. Find unused code and propose what to remove
===================================================

Status: in progress (removed as Frans decided, but for part of G1, which
waits for his answer). Kind: investigate. Created 2026-10-19.


The task
--------

In Frans's words: go through the BergDB code, search for unused code, and
make a proposal for removal. The work is for an AI to do: find the code,
check it, and write the proposal. Only remove files if approved by Frans.

So nothing is removed without his approval: no file, and no class, method
or other part of one. Frans approves all, part or none of the proposal, and
only what he approves is removed.

The code: BergDB continues from the 2017 source, about 63,000 lines in
`java/src` and 16,000 in `java/src-dev`. The 2026 work added stress tests,
a performance harness and the Lean model (about 45,000 lines in
`lean/SIS`) beside it. Code that nothing uses costs reading time, for Frans
and for AI, and makes changes and reviews larger.


Scope
-----

The tracked files (`git ls-files`) in:

* `java/`: `src/`, `src-dev/`, `src-icu/`, `stress/`, `in/`, and the build
  files (`build.sh`, `build.xml`, `readme.txt`).
* `lean/`: `SIS/`, `Check/`, `References/`, `test-traces/` and the files at
  its top.

Not in scope: `items/` (history; an item's code is for that item only),
`frans/` (kept as it is), `java/bench/` (the performance harness's
reference results) and `docs/`, except that a removal updates the documents
that name what is removed.


What counts as used
-------------------

Code is used if one of these reaches it:

* The public API, `bergdb.pub`. A library's API is used by its users even
  where nothing in this repository calls it. Parts of it that nothing here
  uses are listed apart, as a question for Frans, not as dead code.
* The entry points that are run: the jar's main class (`bergdb.dev.Run`),
  the unit tests (`bergdb.dev.Unit`, `F`, `Night`), the classes that the
  scripts in `java/stress/` start (the level scripts, `performance.sh`,
  `conformance.sh`, `soak.sh` and the others), and the targets in
  `lean/lakefile.toml`.
* What is reached without a direct call: reflection (the `bergdb.nanotest`
  test runner), class names in strings and in the scripts' arguments, the
  resources that `build.sh` copies into the jar, and the Javadoc files.
* The documents: a tool or a test that `docs/` names as the source of its
  evidence is used in that sense, even if no script runs it today, since
  removing it makes the evidence impossible to repeat. The same holds for a
  theorem or an example that `docs/` cites.

Code that only an item uses (a probe in `items/`) is not used in this
sense, but the proposal says when a removal would break one. Code that an
open item or a plan in `docs/` names for later use is marked as such.


What to look for
----------------

1. Files, classes and packages that nothing used reaches.
2. Methods, fields and constructors that nothing calls, in classes that are
   used.
3. Code that only its own tests use: is the feature needed?
4. Old variants beside the current one, commented-out code, disabled tests.
5. Files of retired tools: build files, jars and templates that nothing
   reads, scripts and diffs that nobody runs.
6. In Lean: definitions and lemmas that no theorem, test or executable
   uses.


Leads
-----

Seen when this entry was written, not checked:

* The 2017 Ant build: `java/build.xml`, and `java/readme.txt`, which
  describes `ant jar`, Java 5 and an `out/` directory; `java/build.sh`
  replaced that build. Some of the files in `java/in/` may be read only by
  `build.xml`.
* `java/src-dev/frans/` (`DagExamples`, `FastMap`, `PayDemo`,
  `WebsiteCode`, `bryan/`), the demos in `bergdb.demo` and the manual tests
  in `bergdb.test.manual`.
* Tools in `java/stress/` that no script runs; some of them are named in
  `docs/` as evidence (`A2A3Check2`, `DbJunk`).


How
---

Suggestions, not rules:

* Java: a class-level graph of `java/build/classes` from
  `jdeps -verbose:class`, walked from the entry points. For members, a
  shrinker's list of what it would remove (ProGuard's `-printusage`, with
  the entry points as keep rules), or the unused warnings of Eclipse's
  compiler. `git grep` for each candidate's name, to catch reflection,
  scripts and documents.
* Coverage (JaCoCo) over the unit tests and the level scripts is a second
  signal: code that no test runs. That is not the same as unused, but it
  helps to find and rank candidates.
* Lean: a small program over the environment (`Expr.getUsedConstants`) that
  walks from the main theorems and the executables. The repo has no
  Mathlib.
* Work in a scratch clone, not in the main tree: several sessions share the
  main tree and `java/build/`.


The proposal
------------

A report in this subitem, or in a directory `10-unused-code/` beside it
with the tools' output:

* The commit it was made on.
* A table of candidates, each with an ID (U1, U2, ...) so that Frans can
  approve by ID or by group: the path or the symbol, its size in lines, the
  kind (as in "What to look for"), the evidence that it is unused, the
  documents and items that name it, the risk, and a recommendation: remove,
  keep, or ask.
* Groups that go together (a class and its tests, a tool and its script).
* The total: files and lines that would go, per directory.
* What was looked at and kept, and why, in short, so that the same ground
  is not searched again.
* A patch that removes the candidates recommended for removal, checked in a
  scratch clone: the build and the unit tests pass.


After Frans's decision
----------------------

* His decision is recorded here, with the IDs he approved.
* Only the approved candidates are removed: in a scratch clone first, then
  copied into the main tree. The four gates print `LEVEL n OK`,
  `lake build` passes if Lean changed, and the documents that name removed
  code are updated. The change is left for Frans to commit.
* Removed code stays in git history (the 2017 source also in Frans's
  earlier repositories, F1-007), so a removal can be undone.


Done when
---------

The proposal is written and checked, Frans has decided, and what he
approved is removed as above (or nothing, if he approved nothing).


First step
----------

List the entry points: the `java` and `lake` commands in the scripts, the
main classes, the test runner's reflection, the resources, and the tools
that `docs/` names. Then build the class-level graph and list the classes
that no entry point reaches.


Size and order
--------------

M: tools and reading, and machine time for the checks. The proposal can be
made any time, since it changes nothing. A removal touches many files: best
made when no other change to `java/` is under way or waiting to be
committed (such as 005-01's and 005-09's fixes), or made on top of them.


The proposal
------------

Made 2026-10-19 by Claude (Opus 5.5, Claude Code), at Frans's request ("Do
the 005-10 todo item"), on commit `0597329`:
[10-unused-code/proposal.md](10-unused-code/proposal.md), with its tables,
plan, tools and runs in [10-unused-code/](10-unused-code/). Nothing is
removed.

* About 11,700 lines can go (85 files deleted, 97 edited, and a 120 kB
  jar). A patch with every recommended removal passes the build, the unit
  tests (929, from 948), the f-tests (36, from 37), the four gates and
  `lake build`, on a clone.
* The groups, by ID: A1 files nothing reaches; A2 and A3 unused members
  (168); B1 `Cache2`, B2 `DagChecksum`, which only their own tests use; B3
  tests that never ran (one fails today); C1 manual tests, C2 development
  tools; D1 tests and benchmarks of Java itself, D2 the perf tests; E1 the
  2017 Ant build; F1 20 unused Lean lemmas. Not in the patch: C3 `frans/`
  and C5 the figure printers (for Frans), D3 the night tests (they pass;
  proposed to be kept and run in a gate), C4 the demos (kept). G1: 25
  methods and two exceptions of the public API that nothing here uses, a
  question.


Frans's decision
----------------

2026-10-20, in his words: "remove all recommended; C1 keep; C2 keep; C3
keep; D1 keep; D2 keep; D3 keep; E1 keep; G1 remove. D3: add script
night.sh to run these tests."

So to remove: A1, A2, A3, B1, B2, B3, F1 and G1. Kept as they are: C1,
C2, C3, C4, C5, D1, D2, D3 and E1.


The removal
-----------

Made 2026-10-20 by Claude (Opus 5.5, Claude Code), on `0597329`, but for
part of G1 (next section). The plan, the lists and the checks are in
[10-unused-code/applied/](10-unused-code/applied/).

* Deleted: the seven files of A1, `Cache2` (B1), `DagChecksum` (B2) and
  `java/src-dev/bergdb/test/Concurrency.java` (B3).
* Removed: 165 unused members (A2 97, A3 68), the five members of B3, the
  20 Lean lemmas of F1, and eight class methods of the API (G1a). Three of
  the proposal's A3 stay, as code of the kept groups uses them:
  `Cache3.getSizeIndicator` and `totalSize`, and a constructor of
  `BufferedStream`.
* Added: `DbDouble` to the pubimp pack (B3; its two tests pass), and
  `java/stress/night.sh` (D3), which builds, runs the night tests and
  prints `NIGHT OK`; README.md lists it.
* In all: 103 files, 3,071 lines removed and 49 added; docs/log.md has
  the entry.
* Checks, on a clone with the change: the build; the unit tests, 942 pass
  (948 before: `Cache2`'s 5 and `DagChecksum`'s 3 went, `DbDouble`'s 2
  came); the f-tests, 36 pass (37: `Cache2`'s); `LEVEL 1 OK` (167 s),
  `LEVEL 2 OK` (736 s), `LEVEL 3 OK` (469 s), `LEVEL 4 OK` (859 s);
  `lake build`; `night.sh`, `NIGHT OK` (262 s). The main tree's `java/`,
  `lean/SIS/`, `lean/Check/`, README.md and docs/level4-plan.md were then
  made the same as the clone's (`git apply`, compared file by file).

The change is in the main tree, not committed.


G1: what was removed, and what waits
------------------------------------

The proposal said that nothing in the repository uses G1's 25 methods.
That was true of their declarations in the API, but the proposal looked at
those only: for some of them, the code behind the declaration is used. So
G1 is in three parts, and only the first is removed:

* G1a, removed: eight class methods that nothing calls: `Duration.add`,
  `days`, `hours` and `minutes`; `Time.substract` and `getDate`;
  `Factory.printHello`; `CryptoKey.main`.
* G1b, for Frans: nine methods whose implementations nothing uses either,
  and two exceptions: `Connection.put(Object)`;
  `Database.getFirstAvailableLookupTime`, `addReplica`, `removeReplica`,
  `getStorageInfos`; `DatabaseBuilder.replica`; `RwEnvironment.exists`
  (it repeats `ReadInterface.exists`) and `setOutput`;
  `Transaction.getOutput`; `NoFieldsSetException` and
  `NoSuchObjectException`, which only `getOutput`'s implementations throw.
  Removing them takes out of the API: replication, storing an object
  under its key field, transaction outputs, and the first available lookup
  time. The last belongs to the expiry contract: the Javadoc of
  `Database.setRetainDuration` and `Connection.setLookupTime`, and
  docs/levels.md, refer to it and would be reworded. On transaction
  outputs, `RwEnvironment.java` keeps Frans's note of 2013-05-30: "Added
  setOutput(). It *is* needed." (Found on the way: `Connection.get`'s
  Javadoc says that it throws the two exceptions; for a missing key it
  returns null.)
* G1c, for Frans, proposed to keep: eight methods whose implementations
  are used: `DatabaseBuilder.cacheSizeInMb` and `startupDistanceInMb`
  (Level 4's budget and Level 2's startup distance; `DatabaseBuilderImp`'s
  tests call them), `ReadInterface.exists` and `get` (`Connection`
  declares both again and `RwEnvironment` `get`; the tests and the demos
  call those), `UseIndexBuilder.prefix` and `kvs` (`UsePrimaryBuilderImp`
  calls them), `Connection.getEnableKeyReplace` (`RwEnvironmentImp` calls
  it) and `Job.join(int)` (each job's `join()` calls it). Removing them
  would take features that are used out of the API.

Frans's answer on G1b and G1c comes next; this entry is done then.
