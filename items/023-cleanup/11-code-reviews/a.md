# 023-11 Review A of 023-core

## 1. Verdict

**Ready with fixes. Do not merge this head unchanged.**

1. F1: preserve a reusable transaction's full input across key collisions.
   A later execution can silently omit a put.
2. F2: make the dead hand yield during its value work. Its advertised
   2 ms budget can become more than 30 ms of CPU under the writer lock.

S1 is an optional simplification. I found no further failure of the
unlink, historical reads or restart choices in the checks below.
Reviewed `6d5373d6...80105ef1`, all 14 commits, against the frozen rules
of 023-08, sections 5 and 7. The design choices are accepted here.

## 2. Findings

| ID | Severity | File and method | One line |
|----|----------|-----------------|----------|
| F1 | fault   | Db.sortByKey      | Reuse loses an operation after a collision.  |
| F2 | risk    | Eviction.deadStep | The time limit excludes a large inner batch. |
| S1 | simpler | Dag.deleteUpward  | The empty inner space-root fallback is dead. |

### 2.1 F1. Collision compaction destroys reusable input

`Trans` explicitly permits reuse by the same thread (class Javadoc,
lines 23 to 25). `Db.sortByKey`, lines 3028 to 3033, replaces its input
arrays with the compacted arrays. Nothing restores the dropped KVs.
`Db.putKvs` therefore never calls their transformations on a later run.

Concrete case: build two puts, with templates `/template/a` and
`/template/b`. Each transformation uses only its own slot and `t.tt`,
as `KeyTransformation.transform` permits. At time 100 both produce
`/shared`. At time 200 they produce `/later/a` and `/later/b` respectively.
Each also sets its slot's hash to `Keys.hash(newKey)`.

The first execution correctly keeps the second put under 023-08,
section 7. Reusing the same `Trans` at 200 must run both transformations.
The first KV has gone, so `/later/a` is silently absent. This is a
missing write, with no exception. Restart preserves the omission.

`ReuseReviewProbe`, compiled against both heads, with assertions on:

```text
main:     T100 KVs=2; T200 a=[1], b=[2]; restart a=[1], b=[2]
023-core: T100 KVs=1; T200 a=null, b=[2]; restart a=null, b=[2]
```

Fix: preserve the full reusable input list. Sort and compact working
arrays for this execution, with their hashes, without losing an input
needed by the next execution. Add this two-execution regression, including
the restart. The frozen one-operation-a-key rule need not change.

### 2.2 F2. The dead hand does not enforce its time budget

K6 promises at most 4,096 handles and 2 ms a step (023-07, section 5.6;
023-09, section 3). `Eviction.deadStep` checks the clock only at its outer
loop, line 480. It then inspects a whole map part and unswizzles every
value of every kept node, lines 485 to 508, without another time check.

Concrete case: after a cut, the next cache map holds 4,096 written key
nodes that stay resident, each with 60 pointers to values below the cut.
One step can unswizzle 245,760 values. Each unswizzle also calls
`Residents.valueOut`, which scans the holder again through
`Residents.bytesWithoutValues`. The next commit waits for all of this
under `Db.writeLock`.

`DeadBoundReviewProbe` uses a direct cache fixture of that shape, with
distinct values and a 1 GiB budget. Seven warmed steps each unswizzled
245,760 values and took 32.7 to 34.0 ms of thread CPU. The first took
47.6 ms. This overrun does not depend on a collector pause or disk I/O.
The 4,096-handle count holds; the time budget does not.

Fix: check the deadline between small units of handle and value work,
and retain a cursor for the unfinished node or map part. Do not advance
past values that have not been visited. Include the map copy in the
bounded work: `Cache3.mapHandles`, lines 420 to 424, currently copies the
whole map before the deadline can be checked again. Add a test with a
populated map and kept value pointers; the current dead-hand tests check
answers and release, but do not check this bound.

### 2.3 S1. Remove the unreachable empty-root fallback

`Dag.deleteUpward`, lines 1094 to 1099 and 1113 to 1119, can choose
`stop == -1`. Lines 1154 to 1161 then create an empty replacement root.
The climb and `takeBack` also carry a null-parent case solely for it.

For a legal transaction, an inner root has at least two live children.
A delete empties one child. When that leaves one, `collapseRoot` lowers
the root immediately. Thus, deleting the last key reaches a segment
leaf root. A fresh tree holds puts of the transaction, which its other
operations cannot delete under the one-operation-a-key rule.

Evidence: 023-09, section 6, already notes the unreachable branch. My
500-seed UnlinkFuzz run made 403 collapses and no replacement empty root.
`DbTesterDelete.testDeleteEveryKey` cites
`DagTester.testEmptiedSpaceRootReplacedByALeaf`, but no such method exists
in this head. There is no separate test of the fallback.

Proposed simplification: assert the root invariant before the climb
changes anything, then remove the empty-inner-root replacement and its
special null-parent path. Keep the empty segment-leaf root case. This
leaves the behaviour of legal transactions unchanged and removes a
second way to finish a complete delete. It is not a merge blocker.

## 3. What I checked and found sound

* **Unlink and old readers.** `Dag.deleteUpward` finds the stopping node
  before mutation. `Dag.unlink` removes only entries of the current
  transaction. `KeyNode.copyPointer` and `KeyNode.repointKlong` change
  slots behind its time marker. Earlier readers do not use those slots.
  `Dag.emptyKeyNext` deletes the next child's compare value, never the
  empty key. `KeyNode.firstAndSecond` also converts an inserted boundary
  klong to the empty key, as K2 requires.

* **Take-back and fault 12.** `Dag.retarget` includes deleted and shadowed
  KEY klongs of the current transaction. `Dag.spaceSplitInPlace` replaces
  the segment leaf's link in place, removing fault 12's extra reference
  outside the current parent. `Db.endOfTrans` removes taken-back nodes
  from the new dirty set and cache. `DbStarter.rerunTransaction` drops
  them during replay while still consuming their creation IDs.

* **Root collapse and X5 (c).** Both old roots and roots made by a split
  collapse. The quiet follows avoid marking an unchanged child. A fresh
  non-split subtree contains only this transaction's puts. Once the Core
  keeps one operation per transformed key, a legal delete cannot empty
  it. No legal `Bug` was reached in the unit, fuzz or replay checks.

* **Model assumptions and dirty state.** A2A3Check2 ran 1,800 transactions
  at node size 8, with long keys, up to 40 operations and 70% deletes.
  Net A2, A3, A5, TREE, A6 and A-COPY had no failures. Its marking set
  equalled the model's in every transaction. These are sampled checks
  of the assumptions in sis-model, sections 3.4 and 15.2, and of the
  marking behind INV-1 to INV-3 in section 8.

* **Dirty-node bound.** Read the new path charges, overflow propagation
  and chained-collapse allowance. `BoundReviewProbe` compared the bound
  with counted dirty key nodes in 24,000 mixed transactions at node sizes
  8, 14, 30 and 62. It found no undercount, also when deletes were counted
  as puts to exercise the value-transformation classification. The
  branch's large-delete bound test passed too. This does not prove the
  bound. Key transformations still have the documented pre-transformation
  size check; this branch does not introduce that limit.

* **Dead-hand safety.** The new hand uses the existing LIVE-to-DEAD
  protocol, skips loaders, protects D, the record and pinned roots, and
  unswizzles values under the holder's monitor. It runs under the writer
  lock. `noEvict()` disables it in the budget schedule, as documented.
  The held-reader test passed: a reader finishes correctly or expires,
  and the database remains usable. F2 concerns the step's work budget.

* **Forward end key.** `GetMany.Chain.isPastEnd` uses a lower bound of
  the subtree. The stop clears the chain's field, so a later `next()`
  also ends. Backward scans with an end key are refused. Besides the
  branch's tests, `EndKeyReviewProbe` passed 4,000 binary-key scans at
  node sizes 8 and 62, with empty keys, both endpoint choices, historical
  times and a cold restart. Pub index and primary scans passed too.

* **Prepared transactions.** For a fresh `Trans`, key transformations
  precede the stable sort; collision selection follows 023-08, section 7;
  only retained value transformations run. The record contains the actual
  value nodes, and replay keeps their order. `HashReviewProbe` checked
  three retained keys, two trailing virtual hashes, five expected STM
  refusals, a value transformation returning a delete, and restart.
  F1 is the reuse exception.

* **Restart and crash checks.** RestartInvariance, seed 2311, ran 2,000
  transactions with node size 8, long keys, deletes, batches up to 60,
  reclaim, random eviction and a restart every 19 transactions. Streams
  were identical. Dirty sets, identity and lookups matched at all 106
  checkpoints. CrashTest passed three seeds with 500 transactions,
  30 tail cuts and eight meta-block cuts per seed, then writes and restart.

* **Format and expected values.** Format 6 refuses formats 2 and 5 and
  newer formats; the old-format message names 2026.3. The parser tests
  passed. The two scan-count changes are caused by UP removing emptied
  nodes. Their old control scans no longer measure SE alone; the endpoint
  and chain-edge tests still test SE. I found no unexplained expected
  value change.

Validation used an export of exactly `80105ef1`, on JDK 27.0.1. The build
passed, including the release-jar check. Core/Dag unit tests: 619 passed.
Affected Pub unit tests: 145 passed. Focused eviction and reclaim f-tests:
19 passed. UnlinkFuzz: seeds 100000 to 100499, long keys, shuffled order,
dup=20, up to 40 operations, 60 transactions, node size 8; no failures,
552 take-backs, including 106 roots. The run took about 6.5 minutes.

No production source was changed. No level, night or performance script
was run. The larger merge gates in 023-08, section 5, remain separate
from this review's evidence.
