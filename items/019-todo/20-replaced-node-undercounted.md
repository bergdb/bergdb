019-20. Fix: a key node that its transaction grew and replaced stays counted below its bytes
============================================================================================

Status: done 2026-11-06, night 006-12. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: the writer adds a klong to a written, clean key node
(`KeyNode.addKlong`, from `Dag.setValue`), which grows its arrays
(`growCapacity`); a later klong of the same transaction finds the node full,
and `Dag.handleFullNode` replaces it (a split that is not in place) and
cuts it back to its written version (`toPreviousState`). `Db.endOfTrans`
then makes it clean again (`setDirty(false)`), with no count: the resident
registry (`Residents`) counted it at its last write, before the arrays
grew. It stays counted below its bytes, by the arrays' growth (192 bytes
in the harness's case), until it is evicted.

Why: the resident bytes are the capacity controller's measure of memory
(`Eviction`, the budget); `Residents`' class comment says they are exact
but for the objects the writer changed since their last count, which are
pinned until their write. A replaced node is neither pinned nor written,
so its difference stays. Small: the arrays' growth of the nodes that a
transaction replaced, while they are resident; the estimate does not drift,
as the release takes away what was counted.

Source: harness 6.5 of 018-01 (018-05, `EvictionAccountingTester`), its
recount, unit seed 3: "the clean object of node 8117 is counted with 973
bytes, its bytes now 1165". Traced: `grown` at its write, then the next
transaction's `addKlong` (size 6 to 8) and `toPreviousState` (back to 6),
then no count.

Frans: none.

Done when: a test that fails before the fix passes after it, and the
harness's recount passes; `before-commit.sh`; `level4.sh` (full).


Log
---

2026-11-06. Found by harness 6.5 (018-05) in night 006-12, registered and
fixed there.

* Fix: `Db.endOfTrans`, where it makes a replaced node clean, counts it
  with its bytes now (`Residents.grown`). Javadoc of `Residents` (the
  class, `grown`).
* Test: `Residents.testReplacedNodeCounted` (unit group): 200 transactions
  of three keys of 50, nodes of at most 8 entries; after each, every clean
  object of a live handle is counted with its bytes now
  (`Residents.misCounted`). Before the fix: "after transaction 10: the
  clean object of node 3347 is counted with 719 bytes, its bytes now 911";
  after it, none.
* P1 to P12 (010-01): one count per replaced node, under the write lock, in
  the transaction that replaced it; no setting, thread or API. The count
  decides only what eviction takes, and eviction does not change the
  stream's bytes (the eviction twins, `level4.sh`'s EvictionInvariance).
