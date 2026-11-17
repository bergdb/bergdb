# 023-11 Review B of 023-core

2026-11-10, 18:04 to 18:32. The branch `023-core` at `80105ef1` against `main` at
`6d5373d6`, `git diff main...023-core`, read against 023-08 (sections 5 and 7), 023-09,
023-07 (section 5) and the take-back check (023-08, checks/take-back.md). Clone
`/Users/f/fl/bench/2026-11-10/rev09/b/clone`. The code was read in full; one probe and one
test run were made (sections 2 and 3). Nothing in the clone is committed; its jar was last
built with SE's check off (B3) and is not the head's.


## 1. Verdict

**Ready to merge, with two small fixes and two comment fixes before the release gates.**

* No correctness fault found: no legal transaction reaches a `Bug`, leaves a pointer to a
  node never written, changes a node a reader at an earlier time can see, or breaks the
  rerun's choices and ids. The take-back's chain of pointers is closed (section 3).
* B1: `Dag.dirtyNodeBound` undercounts the klongs that root collapses give a segment leaf
  above several trees (max over the paths, not the sum over the trees). The node bound
  still held in every probe, by the slack of the unlinked path nodes it keeps counting.
  A four-line fix; the rule's text in the Javadoc is wrong until then.
* B2: a value transformation that returns null is a delete that the bound walks as a put.
  Same class as B1, named in 023-09, section 6, as out of scope; it is in K4's scope now.
* B3, B4: four node-count tests of SE pass with SE's check off, and two comments name
  figures and a test that are not there. Comment fixes.
* The stop rule of 023-08, section 5, is not triggered: no fault in the take-back.


## 2. Findings

| ID | Severity | Where                              | One line                                |
|---|---|---|---|
| B1 | risk    | Dag.dirtyNodeBound                  | collapses' klongs: max, not sum         |
| B2 | risk    | Db.checkDirtyNodes, dirtyNodeBound  | a null value transformation as a put    |
| B3 | test    | DbTesterGetMany, Pub scan tests     | four node counts pass with SE off       |
| B4 | test    | DbTesterDelete                      | fault 12 not reached; a stale test name |
| B5 | simpler | deleteUpward, takeBack, Db.getMany  | a duplicate branch, a repoint, 3 checks |

### 2.1 B1. The collapses' klongs are not summed over the trees below a segment leaf

**What.** `Dag.dirtyNodeBound` adds, for a delete, two klongs to every node of its path and,
for root collapse, `u.collapses = Math.max(u.collapses, inner)` to each segment leaf L
above a tree of the path, where `inner` is the number of inner nodes of that tree on the
path. The Javadoc states the rule as "L gets one klong for each inner node of that tree on
the paths, once for the transaction". A segment leaf whose klongs of full length name
several segment trees gets that many klongs from each of them. The max is right for one
tree (every path of a tree has the same number of inner nodes, as all its leaves are at one
depth); for m trees below L the real number is the sum.

**Scenario.** L is the space root, a segment leaf with m klongs "/pref00" to "/pref0m", each
to a tree of 1,024 keys at node size 8 (five inner nodes a path). An earlier transaction
deletes all keys of each tree but its first and last, so each tree is a root with two chains
of single children. The checked transaction deletes the first key of each tree: in each,
root collapse replaces five roots (`Dag.replaceRoot`), each a klong in L. L gets 5m
klongs; the count gives 2m + 5.

**Evidence.** A probe on the Dag (SiblingCollapseProbe, in the review's scratch space; the
code of UnlinkFuzz's follower), `-Db=8`:

| m | Collapses in the transaction | Klongs the count gives L | Bound | Dirty key nodes |
|---|---|---|---|---|
| 1 | 5                            | 7                        | 48    | 1               |
| 3 | 15                           | 11                       | 128   | 1               |

(At m = 5 the space root is no longer a single leaf.) The node bound holds by a wide
margin: the count keeps every node of the deleted keys' paths, which the climb unlinks, so
the slack is at least the length of each path that a collapse chain needs, and a klong
costs at most a fraction of a node in `overflows`. I found no transaction where
`dirty > bound`, and the test `DagTester.testDirtyNodeBoundOfDeletes` (2b) covers one chain
only. So no failure after the go point is shown; the rule as written is wrong.

**Fix.** Attribute `inner` to the root of the tree (the `Walked` below L on the path:
`max` there, one root a tree), and at the end add each tree root's `collapses` to its
`up.klongs`. Four lines in the delete branch and the `anyDelete` loop; the Javadoc's
sentence becomes "one klong for each inner node of each tree below L on the paths".

### 2.2 B2. A value transformation that returns null is a delete walked as a put

**What.** `Db.checkDirtyNodes` sets `deletes[n] = kv.getValue() == null &&
kv.valueTransformation == null`: a KV with a value transformation is walked as a put (one
klong in its leaf, fresh trees counted). `Db.putKvs` turns a null result of the
transformation into a delete (`Dag.putKv` with null), which since K1 costs two klongs in
every node of its path and the collapses' klongs. 023-09, section 6, names it and leaves it
as on `main`; on `main` a delete cost what a put cost, so it did not matter there.

**Scenario.** As B1 with the deletes given as value transformations returning null: the
count gives L nothing for them, and the trees' roots one klong each.

**Evidence.** By reading: the two lines above. The same slack covers it in practice.

**Fix.** Walk a KV with a value transformation both ways: as a put (fresh trees) and as a
delete (two klongs a node, the collapses). Three lines, no new count.

### 2.3 B3. Four node-count tests pass with SE's check off

**What.** `DbTesterGetMany.testEndKeyPassesNoDeletedKeys` and `testEndKeyPassesNoDeletedLongKeys`
assert that both the scan with `endKey` and the scan by the stop condition alone follow at
most 20 and 30 key nodes; 023-09, section 4, changed the latter from "more than 200 and
2,000" and says the two no longer fail without SE's check. The same holds for
`PubTesterIndex.testScansBeforeDeletedEntries` (`nodes[0] <= 30`, its comment: "6 key nodes
with it, 146 without it") and `PubTesterPrimary.testListingBeforeDeletedKeys` (3 against
157): since K1 unlinks the deleted entries' nodes, the stop condition alone follows few
nodes too, and the comments' figures are from before K1.

**Evidence.** In the clone, with the `isPastEnd` branch of `GetMany.Chain.next` disabled
(`if (false && ...)`), a rebuild and `bergdb.dev.Unit -c DbTesterGetMany -m 'testEndKey.*'`:
`testEndKeyAsEndpoint` and `testEndKeyChainEdges` fail, the two node-count tests pass;
`-c 'PubTesterIndex|PubTesterPrimary'` with the two tests: both pass. So SE's semantics are
tested (the two that fail); what SE saves on the branch is not, and the four tests test K1.

**Fix.** Say so in the four comments (as the two Db tests' Javadoc already does), and drop
the "146" and "157". What SE still saves on the branch is the load of the first live value
after the range and the nodes of a chain of single children (023-07, section 5.3, risks); a
test of that is small but not needed for the release.

### 2.4 B4. A test that no longer reaches fault 12, and a stale test name

**What.** `DbTesterDelete.testTakeBackAfterSpaceSplitInPlace` was DbShadowProbe's case of
fault 12; since Q4's sort its transaction puts the z keys after the deletes, and its Javadoc
says it "no longer reaches that order through Db". It is now a restart test of deletes
through a KeyTransformation, which is worth keeping, under a name that says so.
`DbTesterDelete.testDeleteEveryKey`'s Javadoc ends "An inner space root emptied in one
delete is replaced by an empty segment leaf: DagTester.testEmptiedSpaceRootReplacedByALeaf";
no such test exists (grep of `java/`), and 023-09, section 6, says no run reached that
branch (`stop == -1`, `statNewRoots` never grew). By reading it cannot be reached: root
collapse runs after every climb that stops at an inner node, so a root that loses its
second-last child is lowered before its last child can empty it, and a root the
transaction made fresh holds only its own puts.

**Fix.** Rename the first test; replace the stale sentence by "that branch is not reached:
Dag.deleteUpward, stop == -1" or remove it. The unreachable branch itself can stay: it is
the safe answer if the argument above ever fails.

### 2.5 B5. Simpler, without a change of behaviour

* `Dag.deleteUpward`: the first `if` of the climb (a space root made by the transaction,
  inner: `stop = -1`) is the `top == 0` branch's answer too; it differs only in not counting
  `statKeptNew`. Drop it and count `statKeptNew` for a segment leaf only.
* `Dag.takeBack`: `parent.repointKlong(i, old)` is repeated by `retarget(parent, node,
  old, tt)` right after it, which repoints every klong of tt that names the node, index i
  included. `linkIndex` is then only the `Bug` check.
* The refusal of `endKey` with a backward scan is in `Db.getMany`, `Dag.getMany` and the
  `Chain` constructor. `Dag.getMany` alone serves `Db.getMany`; the Chain's is there for a
  test that drives a Chain directly (`testEndKeyChainEdges`).


## 3. What I checked and found sound

Read in full: the diff of `java/src` (production and tests), `java/stress/UnlinkFuzz.java`,
the changes of `A2A3Check2` and `conformance.sh`, and the callers and helpers around them
on the branch (`Dag.putKv`, `setValue`, `appendDeleteKlong`, `handleFullNode`, the four
splits, `KeyNode.firstAndSecond`, `toPreviousState`, `addKlong`, `TopDs.newSuperRoot`,
`Db.executeInner`, `putKvs`, `endOfTrans`, the node listener, `checkDirtyNodes`,
`DbStarter.rerunTransaction`, `Cache3.clockStep`, `dropIfEmpty`, `Eviction.detachable`,
`GetMany.Chain.next`, `Trans.Builder.build`, `Kv`).

1. **The climb (`Dag.deleteUpward`).** Nothing changes until `stop` is known. A node that
   the transaction made and no split made can only be emptied by a delete of the
   transaction's own put, which one operation a key rules out (section 3, item 5); the
   `Bug` is unreachable from `Db`, and before the climb changes anything. The nodes below
   `stop` are taken back or unlinked bottom up; `unlink` drops the klongs of tt
   (`toPreviousState`) that only readers at tt could see, and an unlinked node dirty from
   an earlier transaction stays in D and is written in its previous state (`Db.endOfTrans`
   takes out of the got-dirty list only nodes that got dirty in this transaction).
2. **The take-back and its retarget.** `PutData.replacedBy` names a node that existed
   before tt in every case (`madeFor` in `handleFullNode`, `spaceSplit`, and in
   `spaceSplitInPlace` the old node of the node split). Every klong of tt that names a
   node of tt is in that node's parent on the path, now that `spaceSplitInPlace` repoints
   the segment leaf's klong in place (fault 12): `appendKlongs`, `emptyKeyNext`'s copy,
   `replaceRoot`'s klong and `takeBackRoot`'s repoint all land in the parent; `retarget`
   repoints them all, deleted ones too. The repointed klong is then deleted by the bitmap
   (every klong of its compare value) or overwritten in place by `emptyKeyNext`
   (`copyPointer`, as the latest klong of the empty key is the one of tt). So no written
   node names a node never written; a deleted klong names at most the old node, which is
   written, in D, or in the stream. The chain of a time split, a split in place, a
   take-back, `emptyKeyNext` and `takeBackRoot` on one segment root was followed by hand
   with the same result. The branch's own runs: UnlinkFuzz's `checkTakenBack` in every mode,
   DbShadowProbe30 with -ea, DbReplay (023-09, sections 5 and 7.3).
3. **Readers at earlier times.** `repointKlong`, `copyPointer` and the bitmap written in
   place assert and sit behind the node's time klong of tt, where every reader stops.
   `addKlongCopyPointer` reads the pair under the node's monitor (A-COPY from a current
   node). `toPreviousState` of an unlinked node is `handleFullNode`'s on `main`.
4. **Root collapse.** The child is followed before the old root is unlinked
   (`replaceRoot`), quietly, so it is not marked (fault 2, C-S). A root the transaction made
   by a split is taken back in the top node of tt or in the segment leaf's klong of tt, in
   place (fault 5). A root made fresh is not collapsed and cannot be emptied. Chained
   collapses: at most the old inner levels of the tree, one klong each (B1 for the count).
   An inner root with one live klong has the empty key as it (LE-b): `Bug` otherwise, as
   `smallestLive` checks at `stop`.
5. **One operation a key.** `Db.sortByKey` runs only after a key transformation; the
   sort is stable (`Arrays.sort` of objects) and the rule matches `Trans.Builder.build`:
   the last put, a delete only after deletes. Hashes move with their KVs; the virtual KVs'
   stay after them, also when KVs are dropped; `stmRecordKeys` runs after `putKvs` on the
   moved array. Value transformations run only for the KVs kept, in sorted order, each
   reading the previous value at tt. The record holds the value nodes created in that
   order, so the rerun, which does not sort, applies the same operations in the same
   order; ids are taken in creation order, taken-back nodes included, in both runs. A
   `Trans` is already mutated by a key transformation on `main`; its `kvs` being shorter
   after `execute` is new, and only a Core caller that reads `t.kvs` afterwards sees it.
   `DbTesterDelete.testOneOperationAKeyAfterTransformations` checks the five cases against
   a plain database, byte for byte, with restarts.
6. **The rerun and crashes.** Every step of the climb is a function of the delete and the
   state at tt (A1). `DbStarter`'s listener drops a taken-back node at once; `Db` at the
   end of the transaction, after `endOfTrans` took it out of the got-dirty list; neither is
   named by a node or a record. A record of format 6 is refused by 2026.3 and earlier, and
   a record of format 5 by this code, with a message that names 2026.3
   (`StoredTrans.testRefusesOldFormat` for 2 and 5). A torn record is handled as before.
7. **`dirtyNodeBound`, besides B1 and B2.** Two klongs a node cover the stop node's
   bitmap and `emptyKeyNext`'s klong of the empty key, with `overflows`' own +1 for the
   time klong (a node gets at most three in one delete and at most one more a later
   delete); a second bitmap of tt after an empty-key klong is handled by `appendDeleteKlong`
   as a new bitmap, within the two. The `+1` for an empty root is once a transaction. The
   cheap factor 7 for a delete stays a margin. The branch's table (023-09, section 5.3)
   shows the bound far above the dirty count and far below the record limit.
8. **The dead hand.** `Cache3.deadStep` is `clockStep`'s protocol without the CLOCK bit:
   under the map's lock, a copy of the map's handles taken in parts, LIVE to DEAD by
   compare-and-set (a loader that holds the handle is skipped), `kill` on the object seen
   after it, the handle out of the map; `dropNode` uses the same map lock. It runs in the
   writer's thread between transactions, before the budget's step, with the decided cut
   position of `Reclaim.getFirstAvailablePos`, which only rises; a round in progress takes
   the new position as its bound and the next round starts when the position has moved
   again. Not taken: the super root, the newest written top node, D's and the record's
   objects (`Eviction.detachable`), as for the capacity controller. A reader admitted
   before the cut keeps the objects it holds and expires if it follows again below the cut
   (`ReclaimReaderTester.testHeldReadersAndTheDeadHand`). Values below the cut in kept key
   nodes are unswizzled under the node's monitor, as the CLOCK does for pinned nodes.
   Bound a step: 4,096 handles and 2 ms, the time checked between parts. `noEvict()` and
   the schedules other than BUDGET and RANDOM run no round; the Javadoc says so (Z15).
9. **SE.** `isPastEnd` compares the segments passed plus the klong's compare value, a
   lower bound of every key under the klong, with the end as `Keys.compareKeys` would,
   the shorter prefix first; with LE-b the first klong of an inner node compares below
   everything, so the check ends the scan only when every key under the klong is past
   the end. The field `linkSize` is cleared (fault 11). Backward scans with an end are
   refused before anything is read. The Pub API's index scan sets the range's `hi`,
   exclusive (`IndexKeys.succ` of an inclusive bound), the listing `after(prefix)`,
   forward only. `testEndKeyAsEndpoint` compares 1,500 random scans with the Endpoint
   stop condition at every time, deletes included.
10. **LE-b at the split.** `KeyNode.firstAndSecond` gives an inner second half the empty
    key as its first klong and the parent the real compare value; a klong inserted with
    that value goes to the second half as the empty key, later in the node, so it shadows
    the copied one (fault 4).
11. **Expected values changed.** Only the two of SE's node counts (023-09, section 4),
    for the reason given; B3 is about what they test now, not about the values.
12. **Tests.** `DagTester.testNoKlongNamesATakenBackNode` reaches fault 12's order at the
    Dag and walks every klong of every node reachable at any time;
    `testDeleteEveryKeyAfterTheRootSplit`
    and `DbTesterDelete.testDeleteEveryKey` end with an empty segment leaf as the root at
    two startup distances; `testDirtyNodeBoundOfDeletes` checks the bound against the
    dirty count at three node sizes and 100,000 deletes; `Eviction.testDeadHand` checks
    the hand's guarantee after each finished round against the twin without eviction,
    byte for byte; the two reclaim liveness tests bound an iteration. UnlinkFuzz's `dup`
    mode keeps one operation a key by Db's rule. `A2A3Check2` counts a node made and taken
    back as not made (Z18). `conformance.sh` requires no adoption below the old parent in
    the a6 traces (Q9); not run here.

Not done: the level scripts, night.sh, performance; a run of UnlinkFuzz beyond the branch's
own 20,000 seeds; a probe of the dead hand under 10M nodes (023-07, section 5.6, risks).
