# 026-08. The node size fixed at 30 for users; other sizes for tests only

Created 2026-11-13 by Frans Lundberg. Status: open: done on the branch
`026-08-node-size` (State, below), to land.

For release 2026.6, with the stable stream format (027-03): one node
size, B = 30, for every database a user makes, by the Pub API and the
Core API; the sizes 8, 14 and 62 only for BergDB's own tests.


Decided
=======

Frans, 2026-11-13, 09:17, on 024-19's Q5 (a start reads B from the meta
block): "I was surprised with the node size parameter. Not sure we need
this at all. Fixed at 30 could be fine. We have, so far, found little
reason for other values. This is something that is easy to keep a
constant first, then allow variation in later versions if needed. The
other way around is hard. What do you think?" To the coordinator's
answer (below), 09:21: "Yes".

The coordinator's answer, as agreed:

* **For users and the stable format: 30, fixed.** Every size the stable
  format accepts is a promise each later release must keep. 024-19
  found no case for another: 30 within 10 % of the best in every
  measured workload; 62 cost 16 to 45 % more bytes a put at 10M to 100M
  keys; 8 and 14 serve the tests. The meta block keeps its node-size
  field (`u16` at byte 44, 027-03, section 6), written as 30, and a
  start refuses another value, as `Db.refuseOtherNodeSize` does now; the
  field is the hook for a later release that allows other sizes without
  a format change.
* **For the tests: 8, 14 (and 62) stay, test-only.** About 40 files use
  them (tests, harnesses, fuzzers, the conformance sets, `src-dev`): a
  small B gives deep trees with few keys, so splits, merges and
  collapses at many levels are tested in seconds. They are reached only
  from BergDB's own tests, not through public `DbBuilder` methods; a
  database made at a test size carries no promise that a later release
  reads it.
* **The Lean model: B stays a parameter.** A proof over every B costs no
  more than one at 30 and is more general.

What it revises: 024-19's Q2 (answered "yes, as recommended" at 08:54:
B a property of the database, 8, 14, 30, 62 by the Core API) becomes B =
30 for users, the other sizes internal; Q3's rule (v B / 30) stays, used
by the tests at 8, 14 and 62; Q5 (the start takes B from the meta block)
is dropped: with one size there is nothing to take.


The work
========

* `DbBuilder.maxNodeSize8()`, `maxNodeSize14()` and `maxNodeSize62()`
  leave the public Core API (package-private, or a test hook that the
  tests outside `bergdb.core` reach); `maxNodeSize30()` goes too or stays
  as a no-op, whichever keeps the Core API simplest.
* The Javadoc: `DbBuilder`, `Db` and the Pub API's package say the node
  size is 30.
* 027-03: the node size is 30 in the stable format; the field kept and
  checked; the test sizes named as outside the format's promise.
* releases/next.md: a Core API change (the setters gone).
* Gates: before-commit.sh, level1.sh, and the level scripts whose
  conformance sets run other sizes (they keep running them).


What was made
=============

On the branch `026-08-node-size` (State). No stream change, no test's
expected value changed, the Lean model untouched (B stays a parameter).

* **The setters leave the public Core API.** `DbBuilder.maxNodeSize8()`,
  `maxNodeSize14()`, `maxNodeSize30()` and `maxNodeSize62()` are
  package-private: same names, same bodies. A user's `DbBuilder` has no
  node-size method; `defaultSettings()` sets 30 as before, so every
  database made through `Db.builder()`, the Pub API's among them, has
  30.
* **`maxNodeSize30()` goes from the API too** (Q1, below): a public no-op
  would only invite the question of the other sizes. The tests that
  pick a size from a list (8, 14, 30, 62) still call it, inside the
  package.
* **The test hook: `bergdb.core.TestNodeSize`**, one public static
  method, `builder(int size)`: `Db.builder()` with the size 8, 14, 30 or
  62, an `IllegalArgumentException` for any other. Its Javadoc says it
  is for BergDB's own tests, not part of the Core API, and that a
  database made at a size other than 30 carries no promise. Db's
  Javadoc, "The Core API", names it among the internal classes.
* **Who reaches the sizes, and how.** Every user of the setters keeps
  working, with the change below in 11 files:

  | Where                                         | Files | How                       |
  |---|---|---|
  | `java/src/bergdb/core` (testers, Eviction, ...) | 18  | package-private, unchanged |
  | `java/stress`, package `bergdb.core`            | 10  | package-private, unchanged |
  | `java/stress/RestartStress.java` (no package)   | 1   | `TestNodeSize.builder(n)`  |
  | `java/src/bergdb/pubimp` (PubTester and 3 more) | 4   | `TestNodeSize.builder(8)`  |
  | `java/src-dev` (dev, test, frans)               | 6   | `TestNodeSize.builder(n)`  |

  The stress programs in `bergdb.core` (CrashTest, TraceExport,
  StreamDigest, RestartInvariance and the others that the level scripts
  and the conformance sets run) are compiled against `build/bergdb.jar`
  and run with `build/bergdb.jar:build/stress` on the class path, one
  class loader: package-private access works, as it already does for
  their other package-private uses. `bergdb.core` is not sealed.
  RestartStress keeps its "0 means the default": `Db.builder()` for 0,
  `TestNodeSize.builder(maxNode)` otherwise; a value other than 0, 8,
  14, 30 and 62, which used to fall back to 30 silently, now throws.
* **Why this mechanism** (the brief: the simplest that keeps every user
  working). Package-private methods with their names kept leave 28 of
  the 39 files as they were. The tests outside the package need some
  public door, and a door on `DbBuilder` (one `testNodeSize(int)`, as
  `audit()` and `secondTopOrdinal()` are doors for tests) is what Frans
  ruled out: "not through public `DbBuilder` methods". A class of its
  own, named for tests, keeps the user's `DbBuilder` free of the
  subject, and one static factory fits every call site as a
  replacement of `Db.builder()` (`TestNodeSize.builder(8).testSetup(s)
  ...`), with no other change of the chain. It lives in `java/src`,
  because the Pub layer's testers there use it, so the release jar holds
  it, as it holds `DbTester` and the other testers of `src`; a user can
  call it, as he can call any public class of `bergdb.core`. What keeps
  it out of the API is Db's Javadoc (everything not named there is
  internal) and its own. Hiding it for real would mean moving the
  testers out of `src`, far more than this item. `src-dev` cannot hold
  it: `build.sh` refuses a package of `src-dev` that is also one of
  `src`, and a class of `src-dev` could not reach `DbBuilder`'s
  package-private members from another package.
* **The start's refusal** (`Db.refuseOtherNodeSize`) is unchanged but for
  its message, which named `DbBuilder.maxNodeSize<B>()`. Now: "The
  database's maximum node size is 8, and this start uses 30. BergDB makes
  and starts databases of the node size 30 (bergdb 026-08); the other
  sizes are for BergDB's own tests, and a database made at one starts
  only with it. The start has written nothing (bergdb 005-50)." The two
  tests that read it (`DbTesterRestart`, `PubTester.
  testOtherNodeSizeRefused`) check its first sentence, which stays.
* **The Javadoc.** `DbBuilder` (the class: what a user sets, no node
  size; each setter: for tests, package-private, `TestNodeSize` outside
  the package, no promise), `Db` ("Opening a database": 30 for every
  database, by both APIs; "The Core API": `TestNodeSize` internal; the
  two `start()`s' `@throws StreamFormatException`;
  `refuseOtherNodeSize`: the field kept as a hook), `MetaBlock` (byte
  44: 30 in a user's database, 8, 14 or 62 in some that the tests make),
  and the Pub API's package, "The API and its jar": "Every database has
  the node size 30, the most entries of a node of its index, whether
  this API or the Core API made it: nothing sets another, and the stream
  keeps it (bergdb 026-08)."
* **027-03.** Section 6: the table's row for byte 44 and the paragraph
  "The node size": B is 30 in the format; the field kept, written as 30
  and checked, the hook for a later release; 8, 14 and 62 for the tests,
  outside the format's promise; the rules still given for every B. G19:
  30 at every start but a test's. Q18: the node size 30 among the
  constants. Q19 (the start takes B from the stream): dropped, as this
  item drops 024-19's Q5. 21.3, the corpus: at the node size 30. Its
  Log has the entry.
* **releases/next.md**, under "Core API": the setters gone, the node
  size 30 for every database, what a program that called them does, the
  field kept and checked, the test hook not API.
* **Not changed.** The item probes in `items/` that call
  `Db.builder().maxNodeSize8()` from another package (about 60 files,
  history; code in an item is for that item only) no longer compile
  against this jar; nothing runs them. The C clone's cross tools
  (022's `Dump.java`, `Run.java`, `StatsProbe.java`) build against a
  release (`JAVA_REF`, 2026.4 by default), so they work; a port of C to
  2026.6 changes their calls to `TestNodeSize.builder(n)`. 027-01 and
  `docs/log.md`, snapshots and history, keep the old names.


Questions for Frans
===================

* **Q1. `maxNodeSize30()`: removed from the API, or kept as a public
  no-op?** Recommended and applied: removed (package-private, used only
  by tests that choose from a list of sizes). The Core API then has no
  node-size method at all, which says what the format says; a no-op
  would be a method whose only use is to suggest a choice that does not
  exist. A user who called it drops the call (releases/next.md).
* **Q2. The test hook a public class `bergdb.core.TestNodeSize` in the
  release jar, internal by the Javadoc.** Recommended and applied, for
  the reasons in "What was made": it is the smallest change that keeps
  every test, harness and conformance set working, and keeps the user's
  `DbBuilder` free of the subject. The alternative, hiding it from the
  release jar, means moving the Pub layer's testers out of `src`.


Gates
=====

To run on the branch's head after main is merged (State).


State
=====

2026-11-13, 10:20. Code, Javadoc, 027-03 and releases/next.md done and
committed in the clone `/Users/f/fl/bench/2026-11-13/ns30/clone`, branch
`026-08-node-size`; the gates running. Logs in
`/Users/f/fl/bench/2026-11-13/ns30/`.


Log
===

2026-11-13. Registered by coord-1113 (Frans, 09:17 and 09:21).

2026-11-13, 10:09 to 10:20. Made by agent ns30 of coord-1113 on the
branch `026-08-node-size`: the setters package-private,
`TestNodeSize`, the Javadoc, 027-03, releases/next.md.
