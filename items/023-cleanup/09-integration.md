# 023-09. The integration branch 023-core

Created 2026-11-10 by Frans Lundberg. Status: open.

The core of 023-08, section 5, with Frans's answers of its section 7, put
together on one branch from the prototypes: no new design. Clone
`/Users/f/fl/bench/2026-11-10/int/clone`, branch `023-core` from `main` at
`40d06eff`, head `f2be6a5b` (section 8). Runs and their outputs:
`/Users/f/fl/bench/2026-11-10/int/runs/`. Gate worktree (detached):
`/Users/f/fl/bench/2026-11-10/int/gate`.


## 1. Summary

* Fourteen commits on `main`: K1 to K3 (P4), the take-back's retarget
  (P5), fault 12's fix, X5 (c), K4, K7 (SE), K6 (the dead hand), K8
  (format 6), Frans's Q4 (the sort), reclaim liveness tests, one commit of
  expected values, one operation a key and X5 (c) unreachable (Frans,
  17:48; section 7), and last Q9's change of `conformance.sh` (Frans
  accepted Q9 at 17:49).
* No textual conflict. `main` has no Java change since the prototypes'
  base `1901394c`; P5's, P6's and fault 12's parts were taken by hand.
* Reclaim is `main`'s. No P8, no merges, no `mergeBound`, no replaced
  queue, no switch.
* Gates: before-commit OK at `8bc7f2a2` (K8) and at `699d2429` (the Java
  head); level1 OK; UnlinkFuzz in the new modes, 0 failures in 20,000
  seeds; T1 at 100,000 passes every row bounded; T3 reach 1 for every shape; T1
  at 1M with a drive of 12,000 fails C9 by 6 (127 objects against 121),
  the top-node window that 023-08 leaves as on `main`; at 1,000, three
  rows miss C6 or C9 by 1 to 7, from the phase that fault 12's fix
  shifts (section 5.1).
* One commit of expected values (two tests of SE): section 4.
* About 2,600 lines in `java/src`, of which about 1,250 production code;
  the rest tests.


## 2. The commits

In order, on `main` at `40d06eff`:

1. `f4c469d3` K1 to K3: P4's head `0e66d1c9` in `java/src` and the stress
   tools (UP, LE-b, RC, the take-back of a split's node,
   `Cache3.dropNode`, `keyNodeTakenBack`, A2A3Check2's count of
   taken-back nodes, UnlinkFuzz). Comments that named P1's relabelling
   now name LE-b. Not taken: CleanupRule (a prototype; see section 6),
   P4's change of `StoredTrans` (moved to K8).
2. `947e866f` The take-back retargets every klong of tt in the parent
   that names the node, deleted ones too (P5's `retarget`, 17 lines of
   `4c6bea65`; 023-07, section 5.14, fault 6).
3. `b879affc` Fault 12's fix in `Dag.spaceSplitInPlace` (the code of
   `92bf4eb5`), UnlinkFuzz's pointer check (P5) and its modes
   `order=shuffle` and `dup=P` (`92bf4eb5`), without P5's merge counts
   and strict mode; two unit tests of the fault.
4. `04f0fd97` X5 (c): the leaf branch kept; its inner branch a `Bug`
   thrown before the climb changes anything. Tests of X5 (c) at the leaf
   and of deletes of every key.
5. `5fffe9bf` K4: `dirtyNodeBound` by node of the paths, two klongs a
   node, no off-path count, no `mergeBound`, one node for an emptied
   space root; and new, the klongs of chained root collapses (reviews B
   and C, 2.5). A test against counted nodes at node sizes 8, 14, 30.
6. `4f1e598b` K7, SE: 021-28's `2bfeb3e3`, `240f2b3e` and `eebeb39d`,
   squashed.
7. `a34f89a9` Expected values of two SE tests (section 4).
8. `9e93a7ba` K6, the dead hand, on by default (P6's `83e1cb86` and its
   tests `411ae3d1`), without the switch, the timing counters and the
   CPU probe; the 2 ms bound of 023-07, section 5.6. `noEvict()`'s
   Javadoc (Z15).
9. `8bc7f2a2` K8: `RECORD_FORMAT` 6; the refusal names release 2026.3.
10. `ed07d17e` Q4: the key transformations first, then a stable sort of
    the KVs by key, then the puts. A test that two transactions with the
    same operations in other orders write the same stream.
11. `699d2429` Reclaim liveness: two unit tests on `main`'s reclaim.
12. `0b1d59f4` One operation a key: of the KVs that key transformations
    make one key, `Db.putKvs` keeps one by the builder's rule (section 7).
13. `abe27089` X5 (c) unreachable: a `Bug` at any level; the Dag tests
    give one operation a key (section 7).
14. `80105ef1` Q9 (Frans, 17:49): `conformance.sh` requires no adoption
    below the old parent in the a6 traces. The same change as `2c67f887`,
    the head before section 7's change (kept as the branch
    `023-core-before-collapse` in the clone), with a new message.

Each commit message says what it holds and where it comes from, in
Frans's name, with no other attribution.


## 3. Sources and conflicts

* **P4** (`0e66d1c9`): it carries all of P1's four commits; P1's relabel
  code is gone at P4's head (no `relabelSmallest`; the counter
  `statRelabelNodes`, never set, removed; `statRelabels` now counts
  LE-b's pointing of the empty key). The diff `99089978..0e66d1c9`
  applied to `main` without a conflict. CleanupRule.java was left out.
* **P5** (`71e386de`): only `retarget` and its call in `takeBack` (hand
  copied), and the count of `429b56d3` and `71e386de` without
  `mergeBound`: for a delete, two klongs in each node of the path and
  `deleteBelow`'s merges gone; the `+1` that `mergeBound` returned with
  merges off is kept, for an emptied space root. `Db.checkDirtyNodes`'
  cheap factor for a delete stays P4's 7 (P5 had 11, for merges).
* **Fault 12** (`92bf4eb5`, on P5): the same lines, on the core; the
  test probes from `v12/probe`.
* **X5 (c)**: the inner branch is a `Bug`, not a Java `assert`, as the
  climb's other impossible states are, so that it holds without -ea.
  Since `abe27089` the leaf branch is a `Bug` too (section 7).
* **K4, chained collapses** (reviews B and C, 2.5): each level that
  `replaceRoot` collapses adds a klong to the segment leaf L above the
  tree, and unlinks a root that existed before the transaction, one level
  lower each time; so over a transaction L gets at most one klong for
  each inner node of that tree on the paths. The count adds that to L
  once (`Walked.collapses`).
* **SE** (`eebeb39d`, base `5f176575`): applied without a conflict.
* **P6** (`83e1cb86`, `411ae3d1`): applied without a conflict on P4's
  base; then the switch `-Dbergdb.p6.dead`, the counters of the steps'
  time and their test-side reads removed; the time bound
  (`BATCH_NANOS`, `main`'s constant) added from `6451d774`, without its
  CPU probe. The replaced queue and `c46d607d` not taken.
* **K8**: hand written. **Q4**: new code in `Db.putKvs` and
  `Db.sortByKey`. **Liveness tests**: review C's probe with the
  assertion turned round, and 023-v8-fix's unit test without its
  Reclaim change and without the line on P8's end key.
* **Q9**: `conformance.sh` only, the last commit; accepted by Frans at
  17:49 ("Q9, as recommended").


## 4. Expected values changed

| Test                                          | Old        | New       | Commit     |
|---|---|---|---|
| DbTesterGetMany.testEndKeyPassesNoDeletedKeys | > 200      | <= 20     | `a34f89a9` |
| DbTesterGetMany.testEndKeyPassesNoDeletedLongKeys | > 2,000 | <= 30    | `a34f89a9` |

* Both are the control scans of SE's tests, ended by the stop condition
  alone: 398 and 2,160 key nodes on 021-28's branch, 11 and 11 now. With
  K1 a delete unlinks the nodes it empties, so neither scan follows the
  deleted keys. The scans with the end key and the results are as
  before. These two tests no longer fail with SE's check turned off;
  `testEndKeyAsEndpoint` and `testEndKeyChainEdges` still test it.

Changed with their mechanism, not as expected values:

* `StoredTrans.testRefusesNewerFormat` takes `RECORD_FORMAT + 1`, not 6,
  as the newer format (K8, `8bc7f2a2`): 6 is the format now.
  `testRefusesOldFormat` refuses 5 too, and checks that the message
  names release 2026.3.
* A2A3Check2 counts a node made and taken back in a transaction as not
  made (Z18; P4's change, `f4c469d3`).

Not changed, though named by the prototypes: `testFound019_32` (P5's
merges moved its row; no merges here), `testOwnThreadsAreDaemons` (only
P6's queue needed it), `testUserTransactionLeavesTimesForReclaim` (P8's).


## 5. Gates

| Gate                                  | Where             | Result                         |
|---|---|---|
| before-commit.sh                      | `8bc7f2a2`        | BEFORE COMMIT OK (264 s)       |
| before-commit.sh                      | `699d2429`        | BEFORE COMMIT OK (254 s)       |
| level1.sh (full)                      | `699d2429`        | LEVEL 1 OK (157 s)             |
| StreamDigest quick, four modes        | `699d2429`        | the modes give the same stream |
| UnlinkFuzz long, shuffle, dup 10      | `5fffe9bf`, 10 min | 6,000 seeds, 0 failures       |
| UnlinkFuzz long, sorted, dup 10       | `5fffe9bf`, 10 min | 5,950 seeds, 0 failures       |
| UnlinkFuzz random, shuffle, dup 20    | `5fffe9bf`, 10 min | 500 seeds, 0 failures         |
| UnlinkFuzz long, shuffle, dup 10, B 4 | `699d2429`, 5 min | 2,350 seeds, 0 failures        |
| the same, B 14 and B 30               | `699d2429`, 5 min | 2,850 seeds each, 0 failures   |
| T1, N = 100,000, 8 rows (judge.py)    | `699d2429`        | bounded: all pass              |
| T3, R forever, 6 shapes               | `699d2429`        | reach 1 for every shape        |
| T1, N = 1M, drive 12,000              | `699d2429`        | bounded: C9 (127 against 121)  |
| T1, N = 1,000, 8 rows and long 1k, 10k | `699d2429`       | bounded: 7 of 10 pass          |
| A2A3Check2, 8 configurations          | `699d2429`        | all rules hold                 |
| The check's probes (section 5.2)      | `699d2429`        | 0 failures                     |

level1: unit 1,641 tests; DagFuzz at 8, 14, 30, 62; DeleteRepro;
RestartStress, every configuration; RestartInvariance: the stream
identical; Props MEM 129 (at most 131), SS 1.51 (at most 1.52; `main`
gives 1.51 too).

UnlinkFuzz runs in the Dag alone; the Dag's code at `5fffe9bf` is the
head's but for SE's six lines in `Dag.getMany`, which its scans without
an end key do not use. Each "long" run: `shape=long ops=40 n=30`.

### 5.1 T1 and T3

T1 at 100,000 (P4's rows and `judge.py`, P4's CleanupRule compiled
against the head): every row passes bounded, as on P4. Strict: after C9,
before C6, around pass, inter C4, hashed C9, desc C6 C9, random C6,
versions=3 C6 C9 (P4: C6 C9 in most rows, random C4 C6 C9).

T3 (R forever, no drive, after the deletes): reach 1 for after, before,
around, inter, long (10,000) and hashed (random), as P4 and the twin.

T1 at 1,000 and long: 7 of 10 rows pass bounded (P4: 9 of 10). After
fails C9 by 3 (114 against 85 + 26), around C6 by 1 and C9 by 7,
versions=3 C9 by 2; desc, which failed on P4 (C9 by 7), passes. The cause
is fault 12's fix alone: the head without it (`runs/nofix`) gives P4's
figures exactly in these four rows (102, 97, 105 and 118 objects). The
fix writes one klong fewer where a segment root of the transaction is
split in place, so the stream is shorter and the drive ends at another
phase of the startup position: C9's sensitivity to that phase that
023-07, sections 3.2 and 6.2, names (P8's Q4), and the top-node window.
Not a fault of the mechanisms; for Frans's revision of the allowances.

T1 at 1M with a drive of 12,000: reach 6/6, maxD 129 against the twin's
94, objects after the probe 127 against 83. Bounded, a_n = 10 + 4 x 7 =
38: C6 passes (129 < 132), C9 fails by 6 (127 > 121). P4 at the same
settings: maxD 178, objects 184. This is the top-node window that 023-08,
section 5, leaves "as on `main`".

A2A3Check2 on level2.sh's three configurations, two of batch deletes and
P4's three draining ones: A2, A3, A5, marking, TREE, A6' and A-COPY hold
in all; nodes taken back 0, 0, 0, 26, 12, 559, 307 and 324 (the last
three as on P4).

### 5.2 The check's probes, on the head

* DbShadowProbe30, `-Dsd=10 -ea`, 4,377 cases: bad 0.
* DbShadowProbe, `-Dsd=10 -ea`, 200 iterations: bad 0.
* X5cProbe: bad 0; X5 (c) at the leaf taken 2,187 times. Since
  `0b1d59f4` this probe no longer applies: its deletes of keys that its
  transformed puts give are dropped by the builder's rule.
* DbReplay of UnlinkFuzz seed 33 (sorted), with and without -ea: OK, 15
  transactions, restart OK.

With Q4's sort, the Db probes now give the Dag their keys in order; the
Dag-level test `DagTester.testNoKlongNamesATakenBackNode` still reaches
fault 12's order and fails without the fix.

### 5.3 The bound of K4

`dirtyNodeBound` against the key nodes made dirty (a probe, 200,000 keys,
random deletes in one transaction):

| Node size, deletes | Head bound | Dirty  | P4 bound  | main bound |
|---|---|---|---|---|
| 8, 1,000           | 36,748     | 4,553  | 92,253    | 4,693      |
| 8, 100,000         | 2,657,812  | 82,709 | 8,257,301 | 279,646    |
| 14, 1,000          | 7,321      | 2,728  | 41,260    | 2,791      |
| 14, 100,000        | 617,317    | 38,597 | 4,017,262 | 48,094     |
| 30, 1,000          | 2,553      | 1,831  | 28,553    | 1,833      |
| 30, 100,000        | 142,243    | 15,422 | 2,742,246 | 15,835     |

At node size 30 a transaction of 100,000 deletes now counts 142,243
nodes, far below the record limit; P4 counted 2.7M.

### 5.4 Reclaim liveness

`testQueueBeforeAKeyEnds` (queue of 1,000 and "/z" after it; bound 37):
22 transactions on `main`, 15 on the head. `testRandomPutsAheadDoNotSlowTheScan`
(bound 30): 7 on both. Measured with a print in a scratch copy.


## 6. Left out, open, and not fitting the scope

* **The stop -1 case is not reached.** An inner space root left with no
  live klong is replaced by an empty segment leaf (`Dag.deleteUpward`,
  `stop == -1`). No test or run reached it (UnlinkFuzz: "new roots 0";
  `statNewRoots` never grew). By reading: root collapse lowers an inner
  root as soon as a climb leaves it one live klong, and a root that the
  transaction made fresh has only fresh nodes below, whose climbs stop at
  the leaf (X5 (c)). So the branch looks unreachable, as P1 (5) found.
  Left as is; for the review of the integrated code.
* **An undercount of K4 not shown.** No transaction exceeded the bound
  also with the collapses' klongs left out, as in review C's probe. The
  new count is safe by the argument in section 3, not by a failing test.
* **The cheap count of a KV with a transformation.** `Db.checkDirtyNodes`
  counts a KV with a key transformation as a put (factor 3), and a KV
  with a value transformation as a put in the walk; a value
  transformation may return null, a delete, which with UP costs two
  klongs a node of its path. As on `main`; not changed (outside the
  scope).
* **The fault in the first fuzz run was mine.** The first 10-minute
  UnlinkFuzz runs used a jar built while I had the fix taken out to show
  that the new tests fail without it; seed 1385 (long, shuffle, dup 10)
  failed there. With the right build it passes, and all runs were redone
  (section 5). It shows that UnlinkFuzz in shuffle mode finds fault 12 on
  the core without merges, which the check had not seen in 300 seeds.
* **Not in the branch:** CleanupRule.java (P4's prototype of 023-03's
  tests; I compiled it apart for T1 and T3); `CleanupTester` and
  `cleanup.sh` (023-07, 6.2); UnlinkFuzz as a level1 or night step; the
  ratchet test; P7's `testRuleBCounterexample` (023-07, 6.1, step 8, not
  in 023-08's section 5).
* **Documents not changed:** docs/levels.md (format 5 at line 281, the
  delete's climb), sis-model.md 3.4 (transient nodes, the empty key
  first), releases/next.md (format 6, the refusal), 018-01's format
  entry. No Lean change.
* **Not run here** (the coordinator's): level2.sh to level4.sh (level3
  and level4 ran on `2c67f887`, before section 7's change),
  conformance.sh (so Q9's commit is not run), night.sh,
  performance.sh, `night.sh large`, the cold start at 50 MB.
* **Item files:** 021-28's item file is on the branch `scan-deleted-keys`
  only; not taken (the branch holds code only).


## 7. One operation a key (Frans, 17:48)

Frans, on KVs that key transformations make one key: "Why keep both.
[...] Either we should silently use the last KV put (or delete), or we
throw." His decision: silently, with the builder's existing rule
(`Trans.Builder.build`, 015-40). `Trans` itself is not changed; a rule of
"the last operation wins" is a later item, with the C clone.

### 7.1 The rule

* In `Db.putKvs`, after the key transformations and the stable sort,
  `Db.sortByKey` keeps one KV of each run of KVs with one key: the last
  put in the order of build's sort (the keys as written), or a delete if
  there is no put; a delete never replaces a put.
* `t.kvs` and `t.writeKeyHashes` become shorter arrays when KVs are
  dropped; the virtual KVs' hashes stay after the KVs'. A dropped KV's
  hash is the kept one's.
* Value transformations run in the put loop, so only for the KVs kept.
* The record holds the value nodes of the KVs put, so the startup's
  rerun, in stored order, does the same.
* `Db.checkDirtyNodes` and `Db.checkSize`, before the go point, still
  count every KV: an over-count.
* A transaction without a key transformation is not sorted and has one
  KV a key already (build), so nothing changes for it: T1, T3,
  StreamDigest and the other runs on `699d2429` hold for it.

### 7.2 X5 (c) and the tests

* X5 (c) is unreachable: a node that the transaction made and no split
  made, and every node below it, holds only puts of the transaction, and
  one operation a key leaves them live. `Dag.deleteUpward` throws `Bug`
  for it at any level above the space root, before it changes anything.
  A space root that is a segment leaf stays, empty, as before
  (`statKeptNew` counts that case now).
* `DbTesterDelete.testOneOperationAKeyAfterTransformations` replaces the
  X5 (c) leaf test: put + put, put + delete, delete + put and two
  transformed puts on keys that existed, and two puts with value
  transformations. The stream is the same, byte for byte, as a
  database's given the kept operations alone; the values are the rule's
  at the latest time and after restarts (startup distances 10 bytes and
  10 MB); the dropped KV's value transformation does not run. It fails
  without the collapse.
* `DbTester.testTransformedKeysSorted` (two orders, one stream) is kept;
  its plain put of a transformed key is the KV kept.
* `DagTester.testNoKlongNamesATakenBackNode` no longer deletes z keys
  that its transaction put (ShadowProbe mode 2); it still fails without
  fault 12's fix. `testDeleteEveryKeyInTheTransactionThatSplitTheRoot`
  became `testDeleteEveryKeyAfterTheRootSplit`: the transaction that
  splits the root puts the new keys and deletes the old ones, the next
  deletes the new ones.
* UnlinkFuzz's `dup` mode keeps one operation a key in the same way, at
  the key's first place, so the Dag gets one operation a key.

### 7.3 Gates

| Gate                                     | Where      | Result                         |
|---|---|---|
| before-commit.sh                         | `abe27089` | BEFORE COMMIT OK (283 s)       |
| level1.sh (full)                         | `abe27089` | LEVEL 1 OK (168 s), MEM 130    |
| UnlinkFuzz long, shuffle, dup 10, 5 min  | `80105ef1` | 2,650 seeds, 0 failures        |
| UnlinkFuzz long, sorted, dup 10, 5 min   | `80105ef1` | 2,650 seeds, 0 failures        |
| UnlinkFuzz long, shuffle, dup 10, B 14   | `80105ef1` | 2,650 seeds, 0 failures        |
| UnlinkFuzz random, shuffle, dup 20       | `80105ef1` | 250 seeds, 0 failures          |
| DbShadowProbe30, `-Dsd=10 -ea`           | `80105ef1` | bad 0 of 4,377                 |
| DbShadowProbe, `-Dsd=10` and default     | `80105ef1` | bad 0 of 200 each              |
| DbReplay seed 33, -ea and without        | `80105ef1` | OK, restart OK                 |
| ShadowProbe modes 1 and 2 (Dag)          | `80105ef1` | 0 found in 3,000 each          |
| A2A3Check2, 8 configurations             | `80105ef1` | all rules hold                 |
| StreamDigest quick, four modes           | `80105ef1` | the modes give the same stream |

The Java of `80105ef1` is that of `abe27089`. No Bug was thrown in any
run. level1: unit 1,641; DagFuzz, DeleteRepro, RestartStress OK;
RestartInvariance: the stream identical; MEM 130 (at most 131; 129 on
`699d2429`, the step of noise that the limit allows), SS 1.51.


## 8. The fixes of the code reviews (023-11)

Two independent reviews of `80105ef1`, 023-11's a.md (A) and b.md (B).
Six commits on top of `80105ef1`; each the smallest change that fixes its
point, none over 40 lines of production code.

| Finding | Commit     | Test                                                     |
|---|---|---|
| A F1    | `11ba2a8f` | DbTesterDelete.testReusedTransKeepsItsKvs                |
| A F2    | `68714892` | Eviction.testDeadHandBoundsItsWork (f)                   |
| A S1, B5 | `e3b23c07` | the existing tests; UnlinkFuzz                          |
| B B1    | `bd5fd203` | DagTester.testDirtyNodeBoundSumsCollapsesOverTrees       |
| B B2    | `154ad247` | none (an over-count)                                     |
| B B3, B4 | `f2be6a5b` | comments and one name                                   |

* **A F1, a fault.** `Db.sortByKey` replaced a reused `Trans`'s `kvs` and
  write hashes with the sorted, compacted arrays, so a KV dropped in one
  run was gone from the next, and a slot-based key transformation saw
  another KV after the sort. Now `sortByKey(Kv[])` returns a new array for
  the put loop; the `Trans` stays as given. The test runs one `Trans`
  twice, with a collision in the first run and with the slots turned
  round by the sort, then checks each key after the second run and a
  restart. It fails on `80105ef1` ("/later/a" held b's value).
* **A F2, a risk.** A step of the dead hand counted only handles, and
  unswizzled every value of every kept node of a part of up to 4,096
  handles. Now it takes parts of 8 handles (`DEAD_PART`), and the handles,
  the pointers of kept nodes examined and the map copy all count toward
  `DEAD_BATCH`. The cursor stays at a part's end, so no value is skipped.
  A step may exceed the budget by one part and one map copy.
  `Eviction.deadBatch` lets a test set less. The test (an f-test, 1.2 s):
  3,000 keys, overwrites while reclaim cuts, work set to 256. Every step
  unswizzles at most 256 + 8 x 31 = 504 values (248 seen); the rounds
  unswizzle about 230,000. With the old loop one step unswizzled 725, and
  the test fails.
* **A S1 and B5, simpler.** An inner space root is never emptied (root
  collapse lowers it first). The climb now throws `Bug` for it before it
  changes anything. Removed: the new empty root, `statNewRoots`, the
  climb's duplicate first branch, `takeBack`'s null parent, and its
  repoint before `retarget` (which repoints that klong too). `takeBack`'s
  `Bug` now also checks the parent's time klong of tt, which `retarget`
  needs. `dirtyNodeBound`'s one node for the empty root is gone with it.
  Not changed: B5's three refusals of an end key with a backward scan.
  They differ in what they cover: Db's comes before the state and time
  checks, Dag's before the root's lookup (also with no root), the Chain's
  for direct drivers. So none is removed.
* **B B1.** The collapses' klongs into a segment leaf are now summed over
  the trees below it: kept at each tree's root, added to its leaf. The test
  (B's probe) has three trees of 1,024 keys at node size 8, thinned to
  chains, one delete each: 15 collapses, and the count gives the space root
  at least 15 + 6 klongs. With the old rule 11, and it fails. A
  package-private overload of `dirtyNodeBound` returns the klongs counted
  for each node, for the test.
* **B B2.** `Db.checkDirtyNodes` walks a KV with a value transformation as
  a put and as a delete, an over-count; the cheap test counts it with a
  delete's factor. No test: the bound only grows.
* **B B3 and B4.** The four node-count tests of SE now say that they test K1
  and SE together; SE's own tests are `testEndKeyAsEndpoint` and
  `testEndKeyChainEdges`. The Pub tests' figures of 146 and 157 are gone.
  `testTakeBackAfterSpaceSplitInPlace` is now
  `testTransformedPutsAndDeletesWithRestarts`. `testDeleteEveryKey` no
  longer names a test that does not exist.

### 8.1 Gates

| Gate                                     | Where      | Result                         |
|---|---|---|
| before-commit.sh                         | `f2be6a5b` | BEFORE COMMIT OK (273 s)       |
| level1.sh (full)                         | `f2be6a5b` | LEVEL 1 OK (151 s), MEM 129    |
| UnlinkFuzz, 4 configurations, 5 min each | `f2be6a5b` | 8,800 seeds, 0 failures        |
| DbShadowProbe30, `-Dsd=10 -ea`           | `f2be6a5b` | bad 0 of 4,377                 |
| DbShadowProbe, `-Dsd=10` and default     | `f2be6a5b` | bad 0 of 200 each              |
| DbReplay seed 33, -ea and without        | `f2be6a5b` | OK, restart OK                 |
| ShadowProbe modes 1 and 2 (Dag)          | `f2be6a5b` | 0 found in 3,000 each          |
| A2A3Check2, 8 configurations             | `f2be6a5b` | all rules hold                 |

UnlinkFuzz: long, shuffle, dup 10; long, sorted, dup 10; random,
shuffle, dup 20; long, shuffle, dup 10 at node size 14 (2,850, 2,800, 250
and 2,900 seeds); no Bug thrown. before-commit: unit 1,643 tests, f 89.
level1: SS 1.51.
