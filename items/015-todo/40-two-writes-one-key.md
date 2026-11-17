015-40. Fix: two writes of one key in a transaction: the later one can lose
===========================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For 2026.2 if it fits (a wrong answer in normal use); in 2026.1 too.

What: review S1's finding S1-F1 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F1: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`0b739f3`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F1, in a tester of the area.


State
-----

2026-11-03, 21:38: the fix, its tests, three mutations and
`before-commit.sh` done in the clone `/Users/f/fl/bench/016/015-40/repo`
(`main` at `dfc3ca7`); handed off for review in
`/Users/f/fl/bench/016/015-40/handoff/`. Open: the review (016-05,
section 5), the combined gate, the commit in `main`.


The cause and the fix
---------------------

**The cause**: `RwEnvironmentImp.MapKey.equals` returned false unless its
argument was a `long[]`, and it is always a `MapKey`; so `kvOps` and
`indexOps`, `HashMap`s of `MapKey`s, never replaced an entry, and held
each call on a key. `createTrans` handed them all to `Trans.Builder`,
whose `build()` keeps the last put of a key that it is given, and a put
over a delete whatever their order. So a put and then a delete of a key
with a suffix committed the put, and of many puts of one key, the
`HashMap`'s iteration order chose the one that won (S1-F1). Since before
2013-06-06: `MapKey.equals`, `deleteIndexEntry` and the comment
"Non-deletes take precedence over deletes" are in the first commit of
the 2013 to 2017 Git history (`1f4d0b6`, release 2013.1.130606).

**Why `Trans.Builder` keeps a put over a delete**: no note or commit
says; the code shows the need. The index maintenance of an object put
(`RwEnvironmentImp.indexEntries`) deletes the index entries of the
object's previous value and puts those of its new value, in one
transaction, as Frans's 2012 note on indexes says ("These index entries
are deleted if they exist. Then the new index entries are added. This is
done in one atomic transaction"; in the f1 repo,
`a/007-bergdb-261012/bergdb/doc/2012/2012-10-notes.txt`, "Modify object,
creating index"). When the
indexed fields are unchanged, the entry deleted and the entry put are one
key, and the entry must stay. With `MapKey.equals` never true, `indexOps`
held both and its iteration order was not the order of the calls; only
the builder's rule kept the entry. The other users of `Trans.Builder`
(`IndexManager`'s index info and its deletion of an index's entries,
`IndexBuilderImp` through `RwEnvironmentImp.set`, `Reclaim`'s steps,
`DbHelper`, the core's tests) never put and delete one key in one
transaction; `Eviction`'s comparison test at line 1224 does (`k0` at
i = 0, `k20` at i = 180), on two databases built alike, so it does not
depend on the rule.

**The fix**, in `java/src/bergdb/pubimp/RwEnvironmentImp.java`, with the
Javadoc of `Trans.Builder.build` (`java/src/bergdb/core/Trans.java`, no
code) and the tests in `java/src/bergdb/pubimp/PubTester.java`:

* `MapKey.equals` compares with a `MapKey` (`key instanceof MapKey`); the
  hash code is as before, of the key only. Two `MapKey`s of one key are
  equal whatever their key transformations.
* `kvOps`: `setBytes`, `set` and `delete` go through `setKv`, new, which
  removes the key and puts the call's `MapKey`: the last call on a key
  wins, and the `MapKey` kept is the last call's, with its key
  transformation (a `HashMap` keeps its first key object when a put
  replaces an entry; a delete's `MapKey` has no transformation, so a
  delete and then a put of a `${transactionTime}` key would store the
  value at the key as written).
* `indexOps`: the old rule is kept where the code relies on it. An index
  entry's put removes the key and puts its `MapKey`, as `setKv`;
  `deleteIndexEntry` uses `putIfAbsent`, which replaces a delete and not
  a put. So an entry deleted for an object's previous value and put for
  its new value stays, whatever the order of the calls (today the delete
  comes first).
* `Trans.Builder.build` is not changed; its Javadoc says its rule and why
  it is kept. The rule is a contract of the core: BergDB's C clone builds
  the same way (`items/012-bergdb-c/c/src/trans.h`, 012-09) and its cross
  tests compare the streams byte for byte, so a change of the rule would
  change the bytes of a core transaction with a put and a delete of one
  key, and C's with it. The Pub API no longer needs the rule for `kvOps`
  and `indexOps`: each map gives the builder one operation a key.
* Not fixed here: a key in `kvOps` and `objectOps` both, a String or a
  `byte[]` put and an object put or a delete of one object key (S1-F2,
  015-41): the two maps are separate, `createTrans` adds `kvOps` first,
  and the builder's rule decides. The fields' comment in
  `RwEnvironmentImp` says so.
* No stream byte of a transaction without two calls on one key, no
  stream format, no Pub API signature or Javadoc changed. A transaction
  with two calls on one key now stores the last call's (or, for index
  entries, the put).

**The tests**, in `PubTester` (the Pub API's general tester; unit, each
about 0.01 s):

* `testRwPutThenDelete`, `testWPutThenDelete` and
  `testRwManyPutsOfOneKey` are the review's three tests of S1-F1
  (`PubTesterS1`), with `testWPutThenDelete` also doing a delete and then
  a put through `WBuilder`.
* `testWDeleteThenPutOfReplacedKey`, new: with key replace, a delete and
  then a put of `/t/${transactionTime}.txt`; the value is at the key
  with the transaction's time, and not at the key as written. It passes
  on `main`'s code too (the builder's rule kept the put's `MapKey`); it
  checks the removal in `setKv`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 21:27 to 21:38, by an agent of 016-05, in
`/Users/f/fl/bench/016/015-40/repo` (a clone of `main` at `dfc3ca7`):

* **Read**: S1-F1 and S1-F2 (016-06, S1), `RwEnvironmentImp`
  (`kvOps`, `objectOps`, `indexOps`, `indexEntries`, `createTrans`,
  `MapKey`), `Trans.Builder`, `WBuilderImp`, `IndexBuilderImp.createStep`,
  `IndexManager`'s transactions, `Reclaim`'s step, `Eviction`'s test
  driver, C's `trans.h` and `trans.c`. `git log -S 'Non-deletes take
  precedence'` in bergdb gives only the 2017 import (`0257e0b`); in the
  2013 to 2017 history (`java/build/props-006-02/orig-git`), the first
  commit (`1f4d0b6`, 2013-06-06), as for `instanceof long[]` and
  `deleteIndexEntry`. Frans's notes (f1 `a/007-bergdb-261012/bergdb/doc/`)
  have no word on the rule; the 2012 note on indexes describes the delete
  and add in one transaction. The findings: "The cause and the fix".
* **The tests first, on `main`'s code**: `testRwPutThenDelete` ("rw: put
  then delete: expected no entry, got 'new'."), `testWPutThenDelete`
  ("w: put then delete: expected no entry, got 'new'.") and
  `testRwManyPutsOfOneKey` ("round 0, expected 'v39', got 'v30'.") fail;
  `testWDeleteThenPutOfReplacedKey` passes. With the fix all four pass;
  `PubTester` (211 tests with the other `PubTester*` classes) and
  `PubTesterIndex` (65) pass. The review's `PubTesterS1`, applied for a
  run and removed: 14 of 20 fail with the fix (17 before): its three
  tests of S1-F1 pass; `testRwStringAndObjectOfOneKey` and
  `testRwObjectThenString` (S1-F2, 015-41) still fail, as expected.
* **Mutations** (each built and run, then the fixed file put back):
  M1, `MapKey.equals` tests for a `long[]` again: the three tests of
  S1-F1 fail, nothing else in `PubTester` and `PubTesterIndex`. M2,
  `setKv` without the removal: `testWDeleteThenPutOfReplacedKey` fails
  ("the replaced key, expected 'v', got 'null'."), only it. M3, an index
  entry's put does not replace a delete of it (the delete wins, as it
  comes first): `PubTesterIndex.testIterHistory` and
  `testWithDeletesAndUpdates` fail; so the index maintenance does need a
  put to stay over a delete of one key, and the existing tests check it.
* **The gate**: `java/before-commit.sh`, 21:36:22 to 21:38:09: `BEFORE
  COMMIT OK (107 s)`, 1,141 unit tests, 79 f-tests. (A first run, 21:34:16
  to 21:36:04, OK in 108 s, was before a comment of a test was reworded.)
  Not run: the level scripts (no level's mechanism changed).

2026-11-03, 21:41, by the coordinator (016-05, H5): reviewed, no fault.
`MapKey.equals` compares the keys' segments, as `hashCode` does already;
`kvOps` keeps the last call on a key, with its key transformation; in
`indexOps` a put stays over a delete, which `indexEntries` needs when an
object's indexed fields are unchanged, as before. 015-41 (S1-F2) stays
open. Committed after the combined gate.
