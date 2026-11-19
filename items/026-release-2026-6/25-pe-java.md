# 026-25. Java's writer as PE, "plan, then emit"

Created 2026-11-19 by Frans Lundberg. Status: open: made and gated on the
branch `026-25-pe-java` (d64e5638), not on `main`; it waits for Frans's
word on the format and the performance (State).

Java's write half replaced by PE, the writer that 030-21 proved to meet
the writer's contract (`Contract.PE.peTx`, lean/contract/Contract/
PeWriter.lean): for each transaction, a plan over the tree from the
transaction's whole batch, then each decided node emitted once; node for
node the trees of the model on the traces. The level scripts' oracle is
then PE too. Frans, 2026-11-18, 21:42: "If you successfully prove it, feel
free to do the Java implementation too." By an agent of
coord-1118, from 02:10 on 2026-11-19, on the branch `026-25-pe-java` in
/Users/f/fl/bench/2026-11-19/pej/clone.


# Result

Java's writer is PE (`PeWriter.java`, `Dag.putKvs`): a transaction's KVs
planned over the tree as one batch, each node decided once and emitted
once, node for node the trees of `Contract.PE.peTx`. The level scripts'
oracle is PE (lean/SIS/Tree/Pe.lean, a copy shown equal to PeWriter.lean
on every transaction of Java's traces by this item's pecmp). Record format
8 (section 4: the rerun of a record makes another tree than the old
writer's, so a database of format 7 is refused with a message, not rerun
into a tree that its stream does not hold). The take-back, its books, the splits in place
and the merges at the delete are gone (section 5). Gated on d64e5638
(section 6: before-commit, core-build, level1 to level4, contract, medium
tree checks, transcheck, kill-restart with two seeds). On s1, PE is about
8 % slower than main a operation in CCBench (0.93 to 1.24), 0.94 to 0.99 of
main's commits a second in Perf's writes, reads unchanged. For Frans:
the performance left (section 6), the reclaim row's bytes (section 2),
the harness's late exit run (section 6).


# 1. The plan

From 026-24's recommendation, step 2, and coord-1118's brief:

1. **Java's write half replaced by PE** (java/src/bergdb/dag/PeWriter.java,
   called by `Dag.putKvs`): the program of PeWriter.lean, rule for rule;
   the record's KVs given to the Dag as one batch (`Db.putKvs`, and the
   start's rerun, `DbStarter.rerunTransaction`). Reads, recovery, startup,
   eviction, reclaim's cut and the stream's layout stay; reclaim's own
   transactions go through the new writer. The cut size a parameter,
   `Dag.cutSize`, M / 2 (026-24, section 2.6), as PeWriter.lean's `cap`.
2. **The oracle**: the tree checker's writer (`treecheck`, the level
   scripts) is PE: lean/SIS/Tree/Pe.lean, a copy of PeWriter.lean on the
   model's P (lean/contract imports lean/SIS, so lean/SIS cannot import
   it), shown to give PeWriter.lean's trees on the traces by a tool of this
   item (`pecmp`, section 3).
3. **The record format**: decided by 027-03, section 21 (section 4).
4. **Simplify**: today's take-back, its books, the in-place splits, the
   merges at the delete, the upward unlink and the splits removed (section
   5).
5. Not touched: the creation path (028-18 waits for Frans), lean/contract.


# 2. Java's writer

`java/src/bergdb/dag/PeWriter.java`, called by `Dag.putKvs(keys,
values, pd)`: the program of PeWriter.lean (`plan`, `planKids`, `route`,
`applyGroups`, `planTree`, `rebalance`, `joinAt`, `settleRoot`, `mkNode`,
`decideNode`, `emit`, `newParts`), each Java method naming the definition
it restates. The differences of form, none of which changes a node:

- A node is named by the pointer that reached it (a node and the index of
  its klong), not by an id: an entry is unchanged in a node if it is the
  node's own live klong of its compare value (`kept`). A node made and a
  value are named by their objects. A node written that names an old node
  copies the pointer that named it, its handle and reference as a coherent
  pair (`KeyNode.addKlongCopyPointer` from another node; the A-COPY of
  030-07).
- Heights come from the planned children (a segment leaf 0, an inner node
  one above its children), not from levels: Java has no level field.
- The walk over the segments is a loop with a stack of frames, not a
  recursion: a key of BergDB's own may have 8,193 segments (024-17's L3;
  `DbTesterLongKeys.testOwnLongKeysSmallStack` runs in a stack of 256 kB).
  Within a segment tree the recursions (rebalance, settle, emit) are bounded
  by its height; a descent of more than 1,000 nodes in one tree is a cycle
  of a damaged stream (`PointerFollower.cycle`).
- A delete that deletes makes a delete node, with an id, for the record
  (`ValueNode.createDelete`, as before); a delete of a key with no value is
  a noop and makes nothing. Java has no level bounds G and H and every key
  of `Keys.toSegments` is one the tree can hold, so nothing is refused.
- The cut size is `Dag.cutSize(B)` = B / 2, PeWriter.lean's `cap` (026-24,
  section 2.6, its recommendation; 030-21 ran the traces with `cap` = h,
  and its theorems hold for any `cap` from 1 to M - 1, `Cfg.Ok`).

**The ways to the same decisions.** PE's program decides a node by its
whole final list; Java decides most nodes by counts, without the lists,
where the counts give the same decision (each way is compared with the
model, node for node, on every traced transaction):

- the short way of a transaction of at most 8 operations whose every
  segment leaf is only appended to (it fits, keeps a live klong, at most
  theta dead klongs, at least m if not a root) and that makes no segment
  tree: the operations found as a get finds a key (one scan an inner
  node), the values made in key order, each leaf's klongs appended, the
  nodes above marked; anything else changes nothing and the plan runs
  (`PeWriter.shortWay`);
- in the plan, a segment leaf kept or appended to is decided by counts over
  its changes (`LeafFrame.leafNode`); an inner node whose children planned
  are all kept is kept without its list (sparse), and one whose children
  are kept or replaced by new nodes, none empty or joined, is appended to
  by counts (`appendedByCounts`); an inner node routes a few operations by
  one scan of its klongs, not by its sorted live list (`routeBySearch`);
- the rest, a node cut, replaced, joined, emptied or collapsed, by its
  lists, as PeWriter.lean.

**The ids.** Db gives a node its id when it is reported made, so the order
of the reports is that of PeWriter.lean's fresh ids: a value or delete node
when its operation is applied at its segment leaf (key order), a segment
tree's new key nodes when that tree is emitted, before the leaf's later
operations, the space root's tree bottom-up and left to right, the top node
last. A node made is filled first, then reported made (its id, and the
resident registry counts it with what it holds, as a time split's last
version was), then its pointers, then changed.

**The listeners and D.** The plan follows pointers without telling pd's
pointer listener, so a node that a plan reads is not marked; the writer
reports what Db's step 3 needs: a node made (`keyNodeCreated`, then
`keyNodeChanged`), a node that gets klongs (`keyNodeChanged`), a node of the
tree before that is not reachable after (`keyNodeReplaced`: replaced by new
nodes, joined, emptied, collapsed), and a node kept as it was with a node
written below it (`keyNodeOnPath`, new), which Db marks: so D is the Lean
model's marked set, the changed nodes and their current ancestors (C-T9 and
A2A3Check2's MARKING: equal at every transaction). The super root and the
space root are marked by the find of the root, as before.

**The batch.** `Db.putKvs` runs an internal transaction's value
transformations first (each reads its key's value at tt, which is the
value before the transaction, as a transaction has one operation a key),
then gives the Dag the KVs as one batch, in key order; the start's rerun
gives it a record's KVs in their stored order and refuses a record whose
KVs are not strictly increasing (an SFE; it was an
IllegalArgumentException of `Dag.putKvs` in `CorruptStreamTester.testSample`).
A reclaim step's row (`Reclaim`'s value transformation) therefore stores
the bytes that the step's touch made dirty (`Trans.dirtiedBytes`), and no
longer also those of the step's puts that sort before the row: **for Frans
to confirm** (the smallest choice; the touch covers the paths of all the
step's keys, the puts' new nodes are left out, which was already true of
the puts that sort after the row).


# 3. The oracle

`lean/SIS/Tree/Pe.lean`: PeWriter.lean's definitions copied, on the
model's P (a key node read from its history, `klongsOf`, with its level),
with Java's ids (a fresh id the next vpos, two on; a delete that deletes
takes one) and Java's bitmaps (bits in increasing order without repeats),
the cut size `cutSize` = M / 2, and a result in the model's writer state
`W`, so that the tree checker's checks run unchanged: `Pe.runOps` replaces
`runOps` in `Check/Tree.lean` (C-T1 to C-T8) and `TreeCheck.lean`
(`--hplus`), `Pe.exec` replaces `Tree.exec` in `Check/TreeRun.lean`
(C-T9). A noop is a delete of a key with no value at i - 1 (`get`). The old
writer of the model, `SIS/Tree/Exec.lean`, stays: `treeSpec` and the
statements of SIS/Tree/Props.lean are about it, and `treetest` runs it.

lean/contract imports lean/SIS (`require sis`), so lean/SIS cannot import
`Contract.PE`. Instead, 25-pe-java/pecmp/ (a Lake package of this item,
which builds PeWriter.lean's closure from lean/contract's sources into its
own .lake, as that closure needs neither Mathlib nor lean/SIS) runs both
writers on Java's structure before every transaction of Java's traces and
walks both trees after it from their space roots: the same old nodes, every
node written by either written by the other, with the same level, kind and
klongs, the nodes made renamed by a bijection, values with the same hash.
`pecmp --cap-h` is its own test: the proved writer with the cut size h
against the copy's M / 2 must, and does, differ on traces of node size 30.

**Results** (Java's traces of this branch, 2026-11-19): the small set (21
traces, 2,151 transactions), the drain set (33, 4,203), the reclaim set
(10, 5,789), the medium set (27 traces, 13,640 transactions,
node sizes 8 to 62): the same trees at every transaction, PECMP OK. Again
on the traces of the gated commit d64e5638: small 14 traces, 1,434
transactions; drain 22, 2,802; reclaim 10, 5,789; medium 27, 13,640; 0
differ, PECMP OK. With
the tree checker's TREE OK on the same traces (section 6), Java's writer
makes the proved writer's trees, node for node.

The tree checker then compares Java with PE node for node, with the ids:
the nodes made (NEW), the entries (ADD), the klongs (KN), the noops, the
reads, the touch, the invariants, the bound and the whole run.


# 4. The record format

Raised to **8** (`StoredTrans.RECORD_FORMAT`). By 027-03, section 21.1,
the record format covers "header, nodes, the rerun's meaning", and PE
changes the rerun's meaning: the same record makes another tree, with
other ids. 2026.6 already refuses 2026.5's streams by the meta version
(155 since 028-15), so a release reader never meets a format 7 record of
2026.5; the number is raised anyway because:

- 21.2: "Each record carries its format byte ... A reader can tell, record
  by record, which rules apply": with format 7 meaning both 2026.5's
  writer and PE, a later release that reads several formats (21.3's V-B or
  V-C) could not tell them apart;
- a database made by a build of 2026.6 before this item (meta 155, format
  7, the old writer's tree) is refused with a message, not rerun into
  another tree than its stream holds (its got-dirty ids would name other
  nodes);
- it costs one constant, one test (`StoredTrans.testRefusesFormat6` now
  refuses 6 and 7) and the message; format 7's meaning had changed twice
  without a new number before 2026.5, but each time within one release's
  development.

027-03 is updated (sections 5, 6, 8.2, 11.2, 21.1 and its log), with
027-08's description and 027-11's rerun.


# 5. What was removed

The old writer of formats 2 to 7 in Java, and its books:

- `Dag.java`: putKv's per-operation walk (setValue, setNode), the upward
  unlink (deleteUpward, unlink, the climb), the take-back (takeBack,
  canTakeBack, retarget, takeBackRoot), LE-b's relabel (emptyKeyNext),
  root collapse by descent (collapseRoot, replaceRoot, descendTo*), the
  merges at the delete (mergeAfterDelete, merge, sibling, mergeParent,
  link), appendDeleteKlong, appendKlongs, handleFullNode and the five
  splits (time splits, space splits, in place and not), isLive, deadFull,
  the SplitListener, `keyNodeTakenBack`; 1,892 code lines (lines that are
  not blank or comments) before, 782 after.
- `KeyNode.java`: firstAndSecond, replaceKlong, addSortedKlong,
  setContentFrom, copyPointer, repointKlong (1,289 code lines, 1,163).
- `PutData.java`: the key access path, madeFor/replacedBy, the split
  counters and listener, fullNodes, newRootsMade, oneKwi, twoKwis (69, 27);
  `KeyAccessPath.java` (117 code lines) gone.
- `Db`: the nodes taken back (takenBackInTrans); DbStarter's take-back;
  TransCheck's take-back (it now fails a node made or changed and replaced
  in one transaction: each node is written once).
- The write half: about 1,395 code lines before (Dag 1,110, KeyNode 126,
  PutData 42, KeyAccessPath 117), about 1,380 after (PeWriter.java 1,338,
  the entry points in Dag 43). The plain PE writer was 846 code lines (36 %
  less, at commit 1befbe22); the shortcuts that brought it to main's
  speed (section 6: the short way, leaves and inner nodes decided by counts,
  routing by one scan, the live lists in work arrays) took about 490 lines
  of that back. With comments, PeWriter.java is 1,713 lines against the
  2,011 lines of Dag.java's old write half. What is gone is not only lines:
  no node is written twice in a transaction, no take-back and no books of
  it, no split in place; the writer is one plan and one emit, each the
  contract's (section 3).

Tests and tools changed with it: the Dag's tests and fuzzers give a
transaction as one batch (DagTester, MergeTester, DeadKlongTester,
UnlinkFuzz, DagFuzz, A2A3Check, A2A3Check2, DagExamples); the take-back's
assertions became the writer's (joins, cuts, collapses: `Dag.stat*`);
TraceExport's noop flags by key, its Dag counters line; conformance.sh and
level2.sh require joins of their draining configurations, where they
required take-backs; CorruptStreamTester's positions found again in the new
streams (six tests, with probes kept in the agent's scratch, not here);
a few thresholds of tests that depend on the tree's shape (sections 6 and
the Log).


# 6. Gates and results

On d64e5638, the last commit that changes code (the later ones change
items and lean/README.md), each gate in its own clone of the branch, on F53
while other sessions ran Lean proofs (load up to 90; no timing there):

- `java/before-commit.sh`: BEFORE COMMIT OK.
- `java/stress/core-build.sh unit f`: CORE BUILD OK (unit, 68 f-tests).
- `level1.sh`: LEVEL 1 OK; MEM 129 (at most 131), MEM10M 128.2, SEG
  228.1, SS 1.53 (at most 1.54).
- `level2.sh`: LEVEL 2 OK; the tree checker (PE, node for node) TREE OK on
  small, drain and reclaim (7,170, 14,010 and 8,685 transactions, 0 nodes
  made and replaced in one transaction); A2A3Check2's MARKING equal at
  every transaction; joins in each draining configuration (1,841 to 8,642).
- `level3.sh`: LEVEL 3 OK (reclaim, C-CUT 0 of 784, power loss).
- `level4.sh`: LEVEL 4 OK (eviction; C-P and C-H 0 of 14,656).
- `lean/contract/check.sh small drain reclaim` on the gate's fresh traces:
  CONTRACT OK (the contract and the bridge, 0 failures).
- The medium traces (`treeconf.sh medium`): TREE OK on m-big-1, m-long-1,
  m-fifo-1, m-d62-1, m-d30-1; pecmp (section 3).
- `transcheck.sh`: TRANSCHECK OK.
- `kill-restart.sh 1000`: KILL RESTART OK with seed 20261120 (1,000 kills,
  52 exits) and with seed 20261119 (1,000 kills, 50 exits). The first run
  of seed 20261119, while the load stood near 90, failed at database 11, run
  13: "the child ended before its kill, with status 0", a run aimed at
  "exit" whose child did not print "P exit" within 8 s of "P running", so
  that the parent counted it late and aimed a kill after a delay, and the
  child had by then stopped and ended by itself, as an exit run should. Not
  a failure of the database (the check of the data never ran); the
  harness's late path (`KillRestartHarness.runChild`) does not allow for an
  exit run. The rerun with the same seed, at a load near 7, passed. **For
  Frans**: a 028 todo for the harness (a late exit run whose child ends with
  status 0 is an exit), not made here (a change of code after the gates).

**Performance, s1** (2 vCPUs, 3.8 GB; nothing else running; main at
62cd36c4 against d64e5638, ABBA order; runner and summary in
25-pe-java/s1/). CCBench (030-20; 1,000,000 keys of 100 bytes, in memory,
the writer's CPU time), the median of 3 runs, PE / main a operation:

- 1 operation a transaction: update 1.11, insert 1.09, delete 0.97,
  mixed 1.00;
- 10: update 1.19, insert 1.11, delete 0.97, mixed 1.24;
- 100: update 1.07, insert 1.24, delete 0.98, mixed 1.08;
- 500: update 1.01, insert 1.17, delete 0.93, mixed 1.03;
- the load (transactions of 500 puts) 0.95 of main's puts a second; the
  stream 1,687 MB against 1,703.

Perf (performance-quick's scenarios, 2 runs each, PE / main):

- w-uni-1k-inf (1 KB values, 1,000,000 puts, history kept): 0.99 of
  main's commits a second (fsync-bound), p99 append 1.05, the load 0.88,
  GC time 1.11, RSS 1.10;
- w-uni-1k-fin (with reclaim, 11 cuts each): 0.94 of main's commits a
  second, append mean 1.12, bytes appended 1.009, reclaim steps 1.04, GC
  time 1.13, RSS 1.09;
- read-1k: gets 0.97 to 1.00 of main's time, scans 0.96 to 1.11 (the
  tree's shapes differ little; the reads did not change).

On the first s1 run PE took about 2 times main's time an operation: it
built every node's live list, each entry an object, and planned whole
lists where the old writer appended a klong to the node it found. The ways
by counts (section 2) brought it to the figures above. What is left, about
8 % on average over CCBench's 16 cases and 6 % of w-uni-1k-fin's commits a
second, is the plan's own cost: a transaction is walked twice (plan, then
emit), and the plan's objects (a VN a node, the changes of a leaf) are
garbage at its end, about 10 % more GC time and RSS. Deletes are faster
(a delete's leaf decided by counts, without the old writer's merge). Not
within a few per cent everywhere: **for Frans to decide** whether that is
the price of the simpler, proved writer (the theme of 2026.6, simpler
algorithms), or whether a later item takes the plan's allocations down
further (the next steps: a leaf's changes in work arrays, VNs reused
between transactions).


# 7. Performance, quiet machines

Frans, 2026-11-19, 07:25: "You can have this machine to yourself until
09:00. For performance testing. You can use s1 too." main at 519880cb
(its Java that of 62cd36c4) against d64e5638, each built in its own clone;
on F53 from 07:33 to 08:46 with nothing else heavy (the CPU 88 to 98 %
idle before each run, noted in each output; Spotlight's indexing of the
new clones, which held the load near 13, was stopped by renaming their
directory perf.noindex, with a link perf), on s1 from
07:29 to 08:52. Scripts and summaries in 25-pe-java/perf2/; the raw
outputs in /Users/f/fl/bench/2026-11-19/perf/ (not kept in Git).

**The result.**

- **CORE's set is about 11 to 18 % slower with PE, not 3 times.** The
  1.19 against main's 0.39 of the gates' level 1 (section 6, at a load
  near 90) was the load. On a quiet F53, 10 runs each in ABBA order: set main 0.33
  to 0.39, PE 0.39 to 0.43 (smaller is faster; pe/main 1.11 in the first
  session, 1.18 in the second, quieter one); the same in a loop of the set
  test alone, 1.94 against 1.75 µs a transaction (1.11). get, get4t and
  getmany are the same (pe/main 0.97 to 1.00).
- **Why** (JFR of the set test, `profile-set-*.txt`): set is transactions
  of one put of a random 4-byte key with an empty value, into a database of
  100,000 keys in memory (inserts, then the same keys updated). The
  writer's part is 1.01 µs a transaction with PE against 0.87 with main
  (`PeWriter.run` 52 % of 1.94 µs, `Dag.putKv` 50 % of 1.74). PE tries the
  short way on every transaction (0.67 µs), and most of that is
  `shortLeaf` (0.45 µs), which builds the leaf's whole live list
  (`PeWriter.live`, 0.22 µs, and an IdentityHashMap a transaction) to
  decide the leaf by counts, where main searches the leaf for the key and
  appends. The transactions that the short way does not take (a full
  leaf, cut; dead klongs over theta) pay for the try and then the plan and
  the emit: 0.34 µs averaged over all transactions, against 0.13 µs for
  main's splits (`handleFullNode`). So the slowdown is real and is the
  writer's own CPU on a small database in memory; the likely remedy is a
  short way that decides a leaf without its live list (a count of its
  live and dead klongs, as main's `isLive` and `deadCount`), and that
  keeps its lists for the plan without a map a transaction.
- **At 10M keys the writers are within a few per cent**, where the cost is
  mostly memory, the stream and GC: CCBench (10M keys of 8-byte values,
  update, insert, delete and mixed in transactions of 1 to 500, history
  kept) pe/main 1.03 on F53 and 1.03 on s1 (geometric means of 16 cases);
  Perf's commits a second 0.96 to 0.98 with history kept and 1.00 to
  1.04 with reclaim. The load (transactions of 100 or 500 puts) is
  slower: 0.90 to 0.97 of main's puts a second on F53, 0.90 to 0.92 on
  s1.
- **With reclaim PE's databases cut sooner and keep less, for about 6 %
  more bytes written.** In the same 6M transactions on F53 PE made 3
  physical cuts against main's 1 and kept at most 9.1 GB against 10.0;
  its user records are 16 % smaller (fewer index nodes a commit), its
  reclaim steps' bytes 22 % larger, in all 1,348 bytes a put against
  1,262. The same on s1 at 5M keys (1,069 against 1,016; kept at most
  0.88 of main's). Not explained here: a difference of reclaim's pace,
  not of the writer's speed; perhaps the reclaim row's bytes (section 2).
  PE's worst commit was also longer: 315 to 336 ms against 228 on F53,
  366 to 414 against 210 to 228 on s1 (the p99 and p99.9 were 22 to 25 %
  shorter); not explained either (no GC log in these runs).
- **Judgment.** At the sizes BergDB is optimized for, PE costs a few per
  cent in the writer's time and up to 10 % in the load, and nothing in
  the commit latencies but the worst one; the set test's 11 to 18 % is a
  small database in memory, the case that comes last. So the
  performance does not stand against the merge; the short way without the
  live list, the load and reclaim's pace (more cuts, more bytes) are for a
  later item.

**F53 (M1 Pro, 10 cores, 32 GB; OpenJDK 27.0.1).**

- CORE (`core-f53.sh`, level 1's `bergdb.dev.props.Core`, one JVM a run,
  ABBA; `summary-f53-core.txt`): session 1 (3 rounds, 6 runs each): get
  0.27 / 0.27, get4t 0.19 / 0.19, getmany 0.25 / 0.25, set 0.37 (0.33 to
  0.39) / 0.41 (0.39 to 0.43), CORE 0.26 / 0.27; session 2 (2 rounds, 4
  each): set 0.33 (0.33 to 0.34) / 0.39 (0.39 to 0.39), CORE 0.24 / 0.25.
  The set test alone (`setloop/SetLoop.java`, 30 runs a JVM, ABBA;
  `summary-f53-setloop.txt`): main 1.77 and 1.73 µs, PE 1.95 and 1.94.
- The other Props, once each (`summary-f53-props.txt`): MEM 129.5 / 129.1,
  SEG 226.9 / 228.3, MEM10M 127.1 / 128.1, SS 1.53 / 1.53 (main / PE).
- CCBench at 10M keys (8 GB heap, 4 runs each, ABBA; `summary-f53-10m.txt`):
  pe/main from 0.91 (delete, 500) to 1.21 (update, 500), the geometric
  mean 1.027; the load 187,690 against 194,269 puts a second (0.966); the
  stream 6,243 MB against 6,363.
- Perf write at 10M keys, history kept (1M transactions of one put, 2 runs
  each): 137,300 against 142,500 commits a second (0.963), append mean
  1.03, p99 1.01, p99.9 1.04 of main's; the load 0.895; bytes appended
  0.983.
- Perf write at 10M keys with reclaim (retention 0.1 updates a key): until
  the first physical cut (2 each), PE's came after 2.99M transactions,
  main's after 3.88M; for a fixed 3M transactions (2 each): 1.036 of
  main's commits a second, append mean 0.965, p99 0.76, p99.9 0.78, the
  load 0.934, bytes a put 1,338 against 1,261, reclaim steps 1.26, the
  worst commit 1.42; for 6M transactions (2 each, ABBA): 1.002 of main's
  commits a second, append mean 0.99, p99 0.77, p99.9 0.75, the load
  0.94, bytes a put 1,348 against 1,262 (1.068), reclaim steps 1.67,
  physical cuts 3 against 1, kept at most 9.08 GB against 10.06, the
  worst commit 1.20.

**s1 (2 vCPUs, 3.8 GB; nothing else running; `summary-s1-10m.txt`).**

- CCBench at 10M keys (2.9 GB heap, as 030-20's set 4; 2 runs each, ABBA):
  pe/main from 0.84 (update, 100) to 1.16 (delete, 10 and 500), the
  geometric mean 1.031; the load 62,350 against 68,487 puts a second
  (0.910). The heap is nearly full at 10M keys (2.45 GB used after the
  load), so the runs are noisy (a case's two runs differ by up to 20 %).
- Perf with reclaim does not fit s1 at 10M keys: both builds ran out of
  the 2.9 GB heap (at 1.6M and 1.7M transactions), and with a cache budget
  of 1 GB (`-Devictbudget`) the load took 322 s and the updates ran at 25
  a second, bound by the disk. So 5M keys (2 runs each; until the first
  cut, PE's at 2.0M transactions, main's at 2.23M): 1.010 of main's
  commits a second, append mean 0.98, p99 0.78, p99.9 0.78, the load
  0.900, bytes a put 1,069 against 1,016 (1.053), GC time 1.01, RSS 1.05,
  kept at most 0.88; the worst commit 366 and 414 ms against 210 and 228,
  and the slowest second 696 and 807 commits against 6,400 and 7,668.
- Perf at 10M keys, history kept (500,000 transactions after the load, 2
  runs each): 0.975 of main's commits a second (49,870 against 51,140;
  PE's two runs 46,640 and 53,100), append mean 1.06, p99 0.96, p99.9
  1.10, the load 0.922, bytes appended 0.985, GC time 1.03, RSS 1.15.
  Perf on s1 ran with keep=1 halt=1, without the check of every key after
  a restart (at 5M keys it read the stream from the disk for more than 10
  minutes).

GC time and RSS on F53 are not compared: with an 8 GB heap a measured
phase has none to ten collections, and the RSS is the heap the JVM
happened to touch.


# State

2026-11-19, 05:05. **GATED d64e5638** (the last code change; the commits
after it change items and lean/README.md only), on the branch
`026-25-pe-java` in /Users/f/fl/bench/2026-11-19/pej/clone, not merged,
not pushed; main has not moved since the merge of 62cd36c4. All gates of
section 6 pass. For Frans: the performance left (section 6: about 8 %
in CCBench, 0.94 to 0.99 of main's commits a second); the reclaim row's
bytes (section 2); the kill-restart harness's late exit run (section 6);
format 8 (section 4). Then the merge into main.

2026-11-19, 09:00. Timed on quiet machines (section 7): CORE's set 11 to
18 % slower with PE (the short way builds a leaf's live list), not 3
times as under load; at 10M keys within a few per cent of main, the load
up to 10 % slower; with reclaim PE's databases cut sooner and keep less
for about 6 % more bytes written. Nothing in the code changed.


# Log

2026-11-19. Created the item; the clone at main b15f4b1b, branch
`026-25-pe-java` (02:10). The oracle, lean/SIS/Tree/Pe.lean (02:20 to
02:45). PeWriter.java and Dag.putKvs, Db's and the start's batch (02:35);
the tests adapted, record format 8, the old write half removed (02:55);
main merged (62cd36c4); pecmp, 0 differences (03:07). Bugs found on the
way and fixed: a node reported made before it was filled (CapacityTester's
counts); a damaged record's KVs out of order reached the Dag
(CorruptStreamTester.testSample, now an SFE); the short way grouped a
leaf's operations by position, not by leaf, when a segment tree came
between them (PubPromiseTester, a leaf of 31 klongs;
`DagTester.testShortWayLeafAroundASegmentTree` fails on it). The first
s1 run: PE about 2 times main's time; the ways by counts, the short way,
routing by one scan and fewer allocations brought it near main's (03:50 to
03:59, section 6). Gates on d64e5638 from 04:00, all passed by 05:03
(kill-restart's seed 20261119 a second time, section 6); s1's runs from
03:45 to 04:27.
Timing on quiet machines (Frans, 07:25, F53 to 09:00 and s1), 07:25 to
09:00, section 7: CORE ABBA, the set test profiled (JFR), the other Props,
CCBench and Perf at 10M keys on F53 and s1 (Perf with reclaim at 5M on
s1: at 10M it did not fit s1's heap); s1 left clean.
