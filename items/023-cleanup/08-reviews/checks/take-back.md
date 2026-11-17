# Fault 12 of 023-08's review C: a check

2026-11-10, 15:48 to 16:15. A check of one finding of review C of 023-07 (023-08): fault 12
in its section 2.2, a shadowed klong that names a node taken back, and the question of
X5 (c) between reviews B and C. Everything is in `/Users/f/fl/bench/2026-11-10/v12/`: the
clone `clone/`, the worktrees `wt-p5` (023-p5-merge, 71e386de), `wt-p4r` (branch
023-v12-p4r: 023-p4-empty-key, 0e66d1c9, with P5's `retarget` ported, not committed),
`wt-main` (main, 75cfc0f1) and `wt-fix` (branch 023-v12-fix, 92bf4eb5). Probes are in
`probe/`, outputs in `runs/`.

## 1. Summary

* **Fault 12 is real, and it is in the core** as 023-07 defines it (K1: P4's branch with
  P5's `retarget`; 023-07, sections 3 and 5.1). It reproduces on 023-p5-merge unchanged and
  on P4 with only `retarget` ported. With -ea the assertion in `StoredTrans` fails; without
  -ea the next start fails with `StreamFormatException`, so the database cannot be opened
  again. `main` passes the same probes.
* **C's explanation is right, and complete.** The one source is `Dag.spaceSplitInPlace` for
  a segment root made by tt. The segment leaf above gets a second klong of tt, and the first
  one still names the node, which is now a level down. No other place puts a klong of tt that
  names a node of tt anywhere but in that node's parent (section 4).
* **New: sorted keys do not prevent it.** On P5 a plain Core transaction, with no
  `KeyTransformation`, fails in the same way (section 3.2). On P4 with `retarget` it was
  found only with a `KeyTransformation`, but I see no argument that rules out sorted keys.
* **The fix is C's option (2)**: the segment leaf's klong is repointed in place in
  `spaceSplitInPlace`, as `TopDs.newSuperRoot` does for the space root. It is on branch
  023-v12-fix, from 023-p5-merge, in one commit. Every probe passes with it. A fuzz with keys
  out of order, or sorted, finds the fault on P5 and not on the fix. before-commit.sh prints
  BEFORE COMMIT OK.
* **X5 (c) can be reached through the Core API.** A `KeyTransformation` can give one
  transaction a put and a delete of the same key. So C is right, and B's "never" holds only
  without a transformation. Only the branch at the leaf is reached. The branch that stops
  above an inner node is never reached, and cannot be (section 7).
* **Frans's question on ordering** is answered in section 8. Sorting after the
  transformations is small and safe if the order of duplicate keys is fixed. It does not
  replace the fix.

## 2. Builds and probes

| Build   | Code                                                         | Take-back |
|---|---|---|
| wt-main | main, 75cfc0f1                                               | none      |
| wt-p4r  | 023-p4-empty-key + `retarget` (17 lines, from 4c6bea65)      | yes       |
| wt-p5   | 023-p5-merge, 71e386de, unchanged                            | yes       |
| wt-fix  | 023-p5-merge + the fix (section 5) + UnlinkFuzz's options    | yes       |

The probes are review C's, copied to `probe/src`. C's statistics are read by reflection, so
that one source builds on every branch.

* `DbShadowProbe` (Db, node size 8). First a history of keys `/prefix/bNNNN`. Then one
  transaction puts `/prefix/$NNNN` with a `KeyTransformation` to `/prefix/zNNNN`: these keys
  are applied first but sort last. The same transaction deletes every b key. Then come a
  restart, more transactions, and another restart. The probe walks every klong of every node
  that is reachable at any time. It reports a pointer whose vpos is not in the node table
  (a "dead handle").
* `DbShadowProbe30`: the same at node size 30, over a grid of histories (4,377 cases).
* `ShadowProbe` (Dag only). Mode 0 is as above, with some z keys deleted again. Mode 1 is
  one sorted transaction of random puts and deletes. Mode 3 puts and deletes the keys of a
  new prefix in one transaction.
* New: `DbReplay` (Db). It replays an UnlinkFuzz log through the plain Core API: no
  transformation, and `Trans.build` sorts the keys.
* New: `X5cProbe` (Db). One transaction puts the keys of a new prefix through a
  `KeyTransformation` and deletes two thirds of them (section 7).
* New: two UnlinkFuzz options, committed on 023-v12-fix. With `order=shuffle` a
  transaction's keys are applied in random order. With `dup=P`, P percent of the keys get a
  second operation later in the transaction: a delete after a put, or a put after a delete.
* New: `probe/instr`, a copy of the fix's `Dag.java` with counters for the X5 (c) branches.
  It is used only on the class path of the X5 (c) runs.

The startup distance decides how the fault shows. At the default of 50 MB the bad pointer
stays in memory: the walk finds it, but the segment leaf is not written while the probe
runs, and a restart reruns the transaction. With `-Dsd=10` the leaf is written at once.

## 3. Fault 12 reproduced

### 3.1 With a KeyTransformation (C's probes)

| Probe, build                | -ea                                      | without -ea           |
|---|---|---|
| DbShadowProbe, sd=10, p5    | AssertionError at iter 7 and 11          | start fails, 7 and 11 |
| DbShadowProbe, sd=10, p4r   | AssertionError at iter 7 and 11          | start fails, 7 and 11 |
| DbShadowProbe, sd=10, main  | 0 of 200                                 | 0 of 200              |
| DbShadowProbe, default sd   | dead handle: p5 19, p4r 4, main 0 of 200 | the same              |
| DbShadowProbe30, sd=10, p5  | AssertionError at case 36 and 37         | start fails           |
| DbShadowProbe30, sd=10, p4r | AssertionError at case 1134 and 1135     | start fails           |
| DbShadowProbe30, main       | 0 of 4,377                               | 0 of 4,377            |
| ShadowProbe mode 0, p5, p4r | 2 found in 3 cases                       | -                     |

Each probe stops after two failures. The messages are the same as C's:

* With -ea: `AssertionError: spos of index node pointer (2261) is vpos, index: 5, node:
  K/.. 0:3664 L`, from `StoredTrans$Serializer.checkStreamPointers`, in `Db.store`.
* Without -ea, at the next start: `StreamFormatException: Unexpected stream pointer 2261,
  index 5 of key node 0 at 3664`, from `DbStarter.checkStreamPointers`.

P4 with only `retarget` fails just as P5 does, so the fault is in K1 itself and not in P5's
merges. `main` has no take-back. There the shadowed klong names a node that is written, so
it is only a dead klong.

### 3.2 With sorted keys only

| Run                                                 | p5               | p4r      | fix    |
|---|---|---|---|
| UnlinkFuzz long, sorted, ops 40, n 30, 300 rounds   | fails, seed 33   | 0        | 0      |
| UnlinkFuzz long, shuffle, ops 40, n 30              | fails, seed 52   | 0 of 300 | 0      |
| UnlinkFuzz long, shuffle, dup 10                    | fails, seed 16   | 0 of 300 | 0      |
| ShadowProbe mode 1 (sorted), up to 3,000 cases      | 2 in 46 cases    | 0        | 0      |
| DbReplay of seed 33, Db, plain Core API, sd=10, -ea | AssertionError   | passes   | passes |
| the same without -ea, 1 or 2 transactions after     | start fails      | passes   | passes |
| DbSortedProbe (Db, runs of deletes), 400 cases      | 0                | 0        | 0      |

The 15 transactions of UnlinkFuzz seed 33 (`runs/unlinkfuzz-seed33-sorted-log.txt`) are
sorted, with one operation per key. Replayed through `Db` with the plain Core API, they leave
a dead handle after T15 on P5. With -ea, the next transaction that writes the leaf fails
(`spos of index node pointer (49103) is vpos, index: 5, node: K/d2 37493:54968 L`). Without
-ea, a start after one or two more transactions fails with `Unexpected stream pointer
49103`. After three, the bad version has been superseded and the start passes, but the bad
version is still in the stream.

So C's "reached when a KeyTransformation puts a transaction's keys out of order" is too
narrow. On P5, with merges, sorted transactions reach the fault: a merge takes back X, or
the new root collapses, and both repoint in one node only. On P4 with `retarget` (the core,
without merges) no sorted run found it. But a long run of sorted deletes that space-splits
a segment root of tt and then empties its first half looks possible. It was not shown.

With the default ops of 6, shuffled, neither p5 nor the fix failed in 280 s of rounds.

C also says UnlinkFuzz "cannot find it" because the klong is shadowed at every time. That
part is wrong. UnlinkFuzz's `checkTakenBack` walks every klong, shadowed ones too, and it
finds the fault once the transactions are larger (ops 40 with long keys). The default ops of
6 rarely makes a segment root split in place.

## 4. The cause, and other places

C's explanation holds. In `spaceSplitInPlace`, `node` X was made by tt and its parent L is
a segment leaf. X keeps the first half in place, and a new root goes above X and the second
half. L then gets a klong of tt to the new root through `appendKlongs`, which adds a klong.
L's earlier klong of tt, with the same compare value, still names X. That klong is shadowed
at every time: readers before tt stop at L's time klong of tt, and from tt on the new klong
wins. But it is still in L when L is written. If tt then empties X, the climb takes X back
using X's parent on the path, which is the new root. `takeBack` and `retarget` repoint
klongs there only. `takeBackRoot` and P5's merges (`retarget(p, o, m1)`) also repoint in one
node only. So L's shadowed klong names a node that is never written.

I looked for other places where a node of tt gets a klong of tt in a node that is not its
parent on the path. These are all the ways a klong comes to name a node:

| Where                               | The klong lands in                                  |
|---|---|
| `appendKlongs` (every split's link) | the child's parent                                  |
| the new root of a split             | the new parent of both halves                       |
| `firstAndSecond`, in place          | `node` keeps only the first half's klongs           |
| split or time split of an old node  | the old node's klongs of tt go (`toPreviousState`)  |
| `timeSplitInPlace`                  | content from `last`: no shadowed or deleted klong   |
| `emptyKeyNext`                      | the same node, the parent of both children          |
| `replaceRoot`                       | the leaf above, now the parent; old root unlinked   |
| `takeBack`, `takeBackRoot`          | the parent, repointed; the node taken back unwritten |
| merge (`mergeParent`, m1, m2)       | the parent; l and r unlinked or taken back          |
| `TopDs.newSuperRoot` (space root)   | the top node of tt, in place                        |
| `spaceSplitInPlace`, segment root   | **L keeps its klong to X; X moves under a new root** |

Only the last row leaves a klong of tt that names a node of tt in a node other than that
node's parent. Through that row the fault also reaches the merges and root collapse, as
section 3.2 shows. Review B argues (its section 2.2) that "a deleted klong of tt naming S
can exist only in that parent". That misses this row: the klong in L is shadowed, not
deleted, and after the split L is X's grandparent.

Which fix:

* (1), `retarget` in every node of tt on the path above. It would have to go into
  `takeBack`, `takeBackRoot` and the merges, and it leaves the dead klong in L.
* (2), repoint L's klong of tt in place. This removes the one source. After it, every klong
  of tt that names a node of tt is in that node's parent, which is what `takeBack`,
  `retarget`, `takeBackRoot` and the merges assume. `TopDs.newSuperRoot` already does the
  same for the space root in the same split, and `emptyKeyNext`, `mergeParent`'s `link` and
  `takeBackRoot` already repoint a klong of tt in place. L also gets one klong fewer and is
  never split by this link.

So (2). The repointed klong is behind L's time klong of tt, where every reader stops, and
`repointKlong` asserts this. No reader sees the change. The rerun at a start runs the same
code. The trace (docs/trace-format.md, section 2) lists a transaction's entries as they
stand at the end of the transaction, so the model sees one `ADD` in L instead of two, as it
already does for `takeBackRoot`.

## 5. The fix

Branch 023-v12-fix in the clone, from 023-p5-merge (71e386de), commit 92bf4eb5. P5 already
has `retarget`, so it was the simpler base. In `Dag.spaceSplitInPlace`, the branch for a
segment root now reads:

```java
final long klong1 = pd.keyAccessPath.getKlong(depth);
assert klong1 != Klong.NULL : "Missing klong in keyAccessPath, " + depth;
final int i = linkIndex(parent, node, klong1);
if (i < 0 || lastTime(parent) != tt) {
    throw new Bug("Space split at " + tt + ": no klong of tt to segment root "
            + node.getId() + " in its segment leaf.");
}
parent.repointKlong(i, newRoot);
pd.pointerCreatedListener.pointerCreated(parent, i, newRoot);
pd.nodeChangeListener.keyNodeChanged(parent);
```

This replaces `appendKlongs(parent, depth - 1, oneKwi -> newRoot)`. C's sketch falls back
to the append when it finds no klong; here a `Bug` takes its place. X was made by tt, so
L's latest klong with X's compare value names X and is of tt: L got it during tt, behind its
time klong of tt. No run reached the `Bug`. The same commit adds UnlinkFuzz's `order` and
`dup` options. Applying the fix to P4 with `retarget` is the same change; the line numbers
differ.

## 6. Results with the fix

| Run on wt-fix                                 | Result            | On p5               |
|---|---|---|
| DbShadowProbe, sd=10, -ea and without         | 0 of 200 each     | fails at iter 7     |
| DbShadowProbe, default sd                     | 0 dead handles    | 19 of 200           |
| DbShadowProbe30, sd=10, -ea and without       | 0 of 4,377 each   | fails at case 36    |
| ShadowProbe modes 0, 1 and 3                  | 0 of 2,000-3,000  | 2 in 3, 2 in 46, 0  |
| DbReplay seed 33, -ea and without             | passes            | fails               |
| UnlinkFuzz long, sorted, ops 40, 300 rounds   | 0 failures        | fails at seed 33    |
| UnlinkFuzz long, shuffle, ops 40, 100 rounds  | 0 failures        | fails at seed 52    |
| UnlinkFuzz long, shuffle, dup 10, 400 rounds  | 0 failures        | fails at seed 16    |
| UnlinkFuzz long, sorted, dup 10, 200 rounds   | 0 failures        | -                   |
| UnlinkFuzz random, shuffle, dup 20, 200 rounds | 0 failures       | -                   |
| UnlinkFuzz, default settings, 30 rounds       | 0 failures        | -                   |
| before-commit.sh                              | BEFORE COMMIT OK  | -                   |

before-commit.sh, on the commit's tree: Unit 1,625 tests, F 86 tests, the demos 14 runs,
BEFORE COMMIT OK in 257 s. It passed on the first run, with no IndexJobsHarness flake.
Each probe and fuzz run took under 5 minutes. No level script and no performance run.

## 7. X5 (c)

B (023-08 B, sections 2.2 and 2.4) calls the branch unreachable from `Db`. Its reason is
that `Trans.build` keeps one entry per key in a `TreeMap`, so a node that tt made and no
split made holds only puts of tt that are live at the end. C says the branch is reached when
a new segment tree is put and deleted in one transaction, and then always at the leaf.

It is reachable, through the Core API:

* `Trans.build` sorts and deduplicates by the keys as the builder gets them. A put of
  `/newpref/$0001` with a `KeyTransformation` and a delete of `/newpref/z0001` are two
  entries. `Db.executeInner` transforms the put's key just before its `Dag.putKv`, so the
  Dag gets a put of `/newpref/z0001` and then a delete of it.
* `X5cProbe` does this for n = 1 to 80 keys of a new prefix and deletes two thirds of them.
  Run with the instrumented copy of the fix's `Dag`, the branch was taken 2,187 times. Each
  time it was at a node above the space root (top > 0), made fresh (`replacedBy` null), and
  at the leaf (`stop == top`). Gets and the restart were right. Here every delete empties a
  leaf, because keys are cut into segments of 7 bytes (`/newpre`, `f/z1000`, and an empty
  last segment), so each key has a segment leaf of its own.
* UnlinkFuzz with `dup` (the instrumented Dag): 1,652 and 1,237 times fresh at the leaf,
  and 1 and 3 times at a space root that is a segment leaf.
* Without a second operation on one key, the fresh case was never reached. Sorted
  ShadowProbe mode 1 took the branch 105 times, all at a space root that is a segment leaf
  (top == 0). That is the rule that "a space root that is a segment leaf stays, empty", not
  X5 (c). The two cases share the counter `statKeptNew`. B's "kept for A3 0" comes from runs
  without that case.
* The branch that stops above an inner node of tt (`stop > top`) was reached 0 times in
  every run. C's argument holds: an inner node that tt made and no split made belongs to a
  fresh tree, and every node below it is fresh too, so the climb stops at the leaf first.

So C is right that the branch is reached, and B is right for the plain Builder. Each case
leaves an empty segment leaf linked at tt, a node with no live klong, which is what B says
it would cost (I2, R3, R12 (a)). B's proposal to make the branch a `Bug` would turn a Core
transaction that a `KeyTransformation` makes legal into a failed database. Keep the leaf
branch, and make only the inner branch (`stop > top`) an assertion, as C proposes.
Alternatively, settle what two operations on one key in one transaction mean (section 8,
point 2).

## 8. Can the Dag's puts arrive in order? (Frans, 16:07)

**(1) Other sources of disorder.** By reading, there are none besides key transformations.

* `Trans` is made only by `Trans.Builder.build`, which sorts. `new Trans()` is called only
  there.
* `Db.executeInner` is the only caller of `Dag.putKv` apart from the rerun. Only a
  `KeyTransformation` changes a key there. A `ValueTransformation` changes only the value.
* `DbStarter.rerunTransaction` applies the record's value nodes in stored order, which is
  the order the transaction applied them. It repeats the original order and adds no
  disorder of its own.
* Reclaim's step builds its transaction with `Trans.Builder`. Its row is a
  `ValueTransformation`, and `touchRange` makes nodes dirty without a `putKv`.
* Pub index entries are puts in the same Builder. They are out of order only when they carry
  `${transactionTime}` (`RwEnvironmentImp.entryTransformation`).

**(2) Transforming every key first, then sorting.** This is small: one loop over the
`KeyTransformation`s in `Db.executeInner` before the put loop, and a stable sort of `kvs`
with `writeKeyHashes` moved along. The virtual KVs at the end of `writeKeyHashes` stay
where they are. It is safe if these points are settled:

* **Two templates that map to one key.** This happens today: both are applied, in the
  builder's order, and the last one wins. A stable sort keeps that, so both are still
  applied. Better is to decide, at the transformation, either the Builder's rule ("non-deletes
  take precedence over deletes", `Trans.build`) or a refusal. This choice also settles X5 (c)
  for the Core API.
* **Value transformations** read the previous value at tt (`getOne` at the transaction's
  time) and must stay in the put loop, in apply order. Reclaim's row, a value
  transformation, stores `stepTrans.dirtiedBytes`, which depends on what was applied before
  it. Reclaim's step has no key transformation, so its order does not change.
* **The rerun** must keep the stored order and must not sort again. Records written before
  such a change still hold their keys out of order. The node ids, vpos in creation order,
  then match as they do now.
* A `KeyTransformation` is public Core API. Sorting changes only when it runs relative to
  the puts, not what it sees: it gets the `Trans` and an index.

**(3) With sorted input, fault 12 is reachable, not just harder to reach** (section 3.2).
On P5 a plain sorted Core transaction fails. On P4 with `retarget` no sorted run failed, but
nothing rules it out. Sorting would also not remove the dead klong that the shadowing leaves
in L. So the fix in `spaceSplitInPlace` is needed either way. Sorting is a separate
decision about what a key transformation means, and it would make X5 (c) unreachable from
the Builder.

## 9. Left open

* The level scripts were not run on 023-v12-fix: level2 and level3, for the trace
  conformance of the in-place repoint, and level4. They should run before the fix joins the
  integration branch (023-07, section 6.1).
* A unit test: `DbShadowProbe` at `-Dsd=10`, and the DbReplay of seed 33, made into
  `DbTester` cases with -ea as the oracle. UnlinkFuzz with `ops=40 shape=long` and
  `order=shuffle dup=10` as a stress step.
* P4 with `retarget` and sorted keys: a targeted probe (a long sorted run of deletes over a
  segment root that tt copied) would show whether the core without merges can reach the
  fault without a transformation.
* Reach through the Pub API (`${transactionTime}`) was not tried. It would need a Pub event
  log that appends and trims in one transaction.
* `wt-p4r`'s port of `retarget` is not committed. It is the 17 lines of 4c6bea65's
  `retarget` and its call in `takeBack`.
