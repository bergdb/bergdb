021-16. Fix: long keys overflow the stack at a start or a put
=============================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: a put at a key of about 90 KB or more of UTF-8 commits, reads back
and closes, but the next start throws `StackOverflowError` and the
database does not open (U5-1, critical; with `-Xss16m` it starts and the
data is there). A put of a key of 1,000,000 chars after one of 100,000
with the same start throws `StackOverflowError` and fails the database
(U5-2, high). Found by a new-user application, 020-24-05; the
reproductions `LongKey6.java`, `LongKey4.java` and `repro.sh` in
`/Users/f/fl/bench/2026-11-09/app-u5/probe/longkey/`.

Why: both calls are legal; nothing limits a key's length, and a limit
would be a change of meaning for Frans. A database fails when its
environment has failed or on a bug (010-01, P7); a start that cannot open
acknowledged data is the worst case of it.

Frans: none.

Done when: every recursion whose depth grows with a key's length or depth
listed with its depth bound (core, dag, storage, pubimp); each unbounded
one a loop with a stack of its own, in the same visiting order and with
the same checks, or bounded; tests with the default stack that fail
before (a key of about 200 KB and one 20,000 directories deep: put, stop,
start, get, scan; the 1,000,000-char key after the 100,000-char one);
`BEFORE COMMIT OK` and `java/stress/level1.sh` under the gate lock; a line
in `releases/next.md`. If the change is not small or touches the Lean
model's rules, stop after the tests and the list, and report.

First step: the call graph's cycles.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-05's U5-1 and U5-2, and
taken by its agent k16 (clone `clone-k16`, on main's a593b17).

2026-11-09. k16: fixed, commits 4f4db2f (the recursions) and 1e01f45
(Q2) in `clone-k16`, on main's a593b17, to land.

* Cause. A key is a tree of key nodes with a level per segment of 7 bytes
  (`Keys.toSegments`, `Klong.MAX_SIZE`), so a key of N bytes has about
  N / 7 levels. U5-1: the start ends with `DbStarter.postStartupCheck`,
  whose `checkThatValueNodesHaveSpos` walks the nodes in memory with
  `Dag.visitMemoryNodes`, a recursion in `visitNodeWithChildren`, a frame
  per level. U5-2: `Db.checkDirtyNodes` (the transaction's size check,
  005-31) calls `Dag.dirtyNodeBound` for a long key, whose
  `freshTreeBound` recursed once per segment of the key's new part
  (128,000 frames for the 1,000,000-byte key).
* How the recursions were found: a call graph of the compiled classes
  (javap of core, dag, storage, stream, common, pub, pubimp; every
  invoke, a virtual or interface call to every method of its name and
  descriptor, a lambda to its enclosing method) and its cycles (Tarjan);
  then probes in the Core and the Pub API with keys of 200 KB to 2 MB and
  20,000 to 40,000 directories deep: puts, gets, scans both ways, a put
  that shares a long start, deletes, eviction of every node, a restart
  from a memory stream with the audit and from a directory, index builds
  on a deep and on a long directory, `useIndex`, `usePrimary` listings,
  `rw()`, `transactionInfo()`, `Db.printDag`. After the fix, no
  `StackOverflowError` in any of them.
* The cycles, with their depth bound:
  1. `Dag.visitNodeWithChildren` (`visitMemoryNodes`; the start's check,
     `Db.checkNodes`): a frame per level of the deepest path in memory,
     unbounded. U5-1. Fixed.
  2. `Dag.freshTreeBound` (`dirtyNodeBound`): a frame per segment of a
     key below the tree in memory, unbounded. U5-2. Fixed.
  3. `Dag.visitMemoryPointersOnceFromNode` (`visitMemoryPointersOnce`;
     `DagTester` and src-dev's `Interactive` only): as 1. Fixed.
  4. `DagNodeIterator.next` (`DagComparison`, tests): a frame per level
     at every call, unbounded, and each call a walk down the chain of
     iterators. Fixed.
  5. The writer's split cascade, `Dag.appendKlongs`, `handleFullNode`,
     `timeSplit`, `spaceSplit`, `spaceSplitInPlace`: three frames per
     level, up the key's access path, but only through nodes that are
     full at once (a node that is not full takes the klong and ends it).
     Bound: the run of full nodes above the node. A segment leaf at
     level i fills with klongs of keys of at least 7(i + 1) bytes (new
     keys, or writes and deletes of its own keys); a replaced child adds
     one klong, so repeated writes of one key fill a level only after
     (M / 2)^k writes (M = 30, the node size). To have k nodes of one path
     full at once takes about M - 3 keys a level, 3.5·M·k² bytes of keys
     in all. An overflow of the default stack needs some thousands of
     levels (estimate: 3,500 to 7,000, so 1 to 5 GB of keys, written for
     the purpose); then the put that reaches it fails the database, before
     its record, so a start works and the same put fails again. Not
     changed: the writer's central code, and not small; a candidate for
     a loop with an explicit stack of pending splits if Frans wants it.
  6. `KeyNode.printInternal` (`Db.printDag`): stops at depth 10.
     `TopNode.printGraph`: the top nodes' tree, not a key's levels.
  7. `Klong.getTime` and `Klong.toString`: depth 2.
  8. The Pub layer's object readers and writers (`ObjectFormat.checkObject`
     and `checkValue`, `valueEnd`, `heightAt`; `DataObjects.make`,
     `convert`, `toArray`; `DataObjects.Put`): an object's nesting,
     bounded by 021-08 (1,001 objects, 2,001 levels); not a key's.
  9. `Util.delete`: a directory tree on disk. The delegations among the
     stream classes (`append`, `read`, `getLength`, `close` and others),
     `Db` and `Jmx`, `Reclaim`'s table serializers, the iterators of
     `usePrimary` and `useIndex`: depth at most 3, cycles only by the
     graph's over-approximation of virtual calls.
  10. Test harnesses and fuzzers (`IndexHarness`, `FormatFuzzer`,
      `IndexReference.show`, `IndexJobsHarness`): not on a database's
      paths.

  No regular expression is applied to a key (a long input can make
  `java.util.regex` recurse).
* Fix, in `bergdb.dag`, the order and the checks kept:
  `visitNodeWithChildren` and `visitMemoryPointersOnceFromNode` are loops
  with a `WalkPath`, the frames of the recursion as arrays: each node's
  size read when the walk comes to it, after its visit, as before, and its
  pointers read one at a time; `freshTreeBound` a loop with a stack of the
  trees still to count (the count is a sum); `DagNodeIterator.next`
  follows its chain of iterators in a loop and keeps it between calls. A
  key's length still has no limit. About 150 lines with comments.
* Tests, with the default stack (2 MB on F53), each failing with
  `StackOverflowError` before the fix: `DbTesterLongKeys` (new):
  `testLongKeyRestart`, a key of 200,000 bytes and a short one, a restart
  from the stream, gets, scans both ways, `checkNodes`, a longer put
  (290 ms); `testLongKeyAfterItsStart`, 1,000,000 bytes after 100,000
  (330 ms). `PubTesterLongKeys` (new): `testLongAndDeepKeysStartAgain`, a
  key of 200,007 chars and one 20,000 directories deep (120,006 chars),
  closed, opened, gets, `usePrimary` listings of both directories, a put
  (440 ms); `testLongKeyAfterItsStart`, `LongKey4` as a test (100 ms).
  `DagTester.testLongKeyWalks`, 400,000 bytes, the three walks reach every
  node (160 ms). And `DagTester.testWalksKeepTheirOrder`: each walk
  against the recursion it replaced, node by node, on a graph of node
  size 8 with replaced nodes and deletes; it passes before and after.
  `repro.sh` on the fixed jar: U5-1 starts again with the value, U5-2
  puts both.
* `releases/next.md`, Core API, a line: in 2026.1 to 2026.3 (the same
  recursions in each release's `Dag.java`).

Two new findings, not recursions: long keys make two loops quadratic in
the key's length. Q2 fixed (coord-1109's answer, 14:50), Q1 reported for
Frans.

* Q1, open, for Frans. `Db.handleStillDirtyNodes` calls
  `DbHelper.handleStillDirtyNodes` until a pass marks no node still
  dirty, a pass over the record's index nodes each. When a commit writes
  the chain of a long key (taken from D) while a node at its bottom is
  dirty, each pass marks one more level, so the passes are as many as the
  chain's nodes: quadratic, under the write lock. Measured: a put of
  1,000,000 bytes after 100,000 with the same start took 2.6 to 5.8 s at
  startup distances of 100 bytes to 50 MB (88 ms at 200 MB, where nothing
  is written); in a Pub probe (keys of 400 KB and 2 MB with the same
  start, cache 4 MB), 3,000 small puts took 79 s. Nothing fails; a key
  of 10 MB after one of 1 MB would hold the write lock for minutes. A fix
  that gives the same nodes in the same order (the record's got-dirty
  list): a node's pass is the least, over its children in memory, of 1
  (a child dirty before the passes), the child's pass (a child before it
  in the list) or the child's pass + 1 (a child after it), a 0-1
  breadth-first search over the parents; then the nodes by pass and
  position. Not done: it is the still-dirty test of Rule A
  (docs/levels.md), which the Lean model covers.
* Q2, fixed. `StoredTrans.findNode(id)`, a scan of the record's nodes,
  is called by the start's rerun for every node it makes
  (`DbStarter.rerunTransaction`, `nodeCreated`): a time in the product of
  the two counts. A Core database with a key of 100,000 bytes and then
  one of 1,000,000 with the same start (startup distance 50 MB) took 4.9
  to 5.9 s to start; in the Pub probe above, 118 s, its stack in
  `findNode` at every sample. Commit 1e01f45 in `clone-k16`: a record of
  at most 64 nodes is still scanned (most are); a larger one is looked up
  in a map from id to node, made once for the array, the first node of an
  id, as the scan gave. The start above now takes 0.5 to 0.6 s. Test
  `StoredTrans.testFindNode`: 200,000 lookups among 100,001 nodes in 47
  to 73 ms, 33 s before (failed at its limit of 2 s); a replaced array;
  the scan and the map agree at 2, 64 and 65 nodes. `releases/next.md`,
  Core API, a line.

Runs, under the gate lock: 4f4db2f, `BEFORE COMMIT OK (157 s)` (unit
1554, f 86, demos) at 14:56, `java/stress/level1.sh`: `LEVEL 1 OK`;
1e01f45, `BEFORE COMMIT OK (161 s)` (unit 1555, f 86, demos) at 15:11,
`LEVEL 1 OK` at 15:17. Logs `k16-gate1.txt`, `k16-gate2.txt`,
`k16-level1.txt` and `k16-level1b.txt` in `/Users/f/fl/bench/2026-11-09/`.

Left: Q1, for the coordinator to register (an entry of its own, or a
known issue of 2026.4), with Frans's decision on Rule A's code; the split
cascade (cycle 5), bounded in practice, if Frans wants it a loop.

Probes and the call graph's script in `/Users/f/fl/bench/2026-11-09/k16/`:
`LongKeyProbe.java` (Core, package bergdb.core), `PubLongKeyProbe.java`
(Pub API), `T2.java` (Q1's timings), `T3.java` (Q2's), `Many.java`,
`cg2.py` (the cycles of a javap listing).
