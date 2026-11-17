Node size and BergDB's writes at scale (bergdb 005-38)
=====================================================

2026-10-26, F53. A measurement for item 005-38 ("Investigate writes at
scale", question 2: the node size). All runs in memory on a scratch clone of
bergdb `716778e`; nothing in `~/fl/repos/bergdb` was changed. Directory:
`/private/tmp/claude-502/-Users-f-fl-repos-f1/c2c8b076-1761-487e-ac3a-ea475443b664/scratchpad/nodesize/`
(called `nodesize/` below; the coordinator's tool and outputs are in the
sibling `wb/`).

# 1. Summary

SUMMARY-TEXT


# 2. Stream bytes a put

The update phase's bytes a put, the steady state at a fixed size, whole
phase (`nodesize/assemble.py key`; * an update phase cut short by the heap;
node 30 at 10M and 50M keys from the coordinator's `wb/out/u-sd*-*.txt`):

KEY-TABLE

By level, update phase after its first 20 percent (`nodesize/breakdown.py`):
writes a put × bytes a written node = bytes a put.

BREAKDOWN-TABLES

**The loads**, for reference: bytes a key after the load, and in parentheses
the mean of its last fifth (the marginal cost of an insert near K). At sd 200
MB and more these are transients (writes come in waves; at the end of a load
most of the index is still in D):

LOAD-TABLE

**Other key shapes**, update phase: random 24-byte keys (`rnd24`, 1M keys, sd
50 MB, 3M updates): 627, 632 and 653 bytes a put at 14, 30 and 62: only the
first segment is a real tree, and each key's three one-key segment leaves are
rewritten about 0.9 times a put whatever the node size. Sequential `key24`
(10M keys, sd 50 MB, load only): 99.0, 89.4 and 85.9 bytes a key at 14, 30 and
62 (heap 153, 120 and 109 bytes a key).



# 3. The model

Bytes a put = Σ over levels of node writes a put × (bytes a written node +
16), plus the value node (68 bytes here) and a little for top nodes. The 16 is
the node's entry in the got-dirty list of the record where it got dirty.

* **A put dirties its whole path**, one node a level (a class: segment and
  height). A dirty node is written when its transaction falls a window behind
  the end of the stream; the window W is the startup lag, the startup distance
  most of the time (section 6). A window holds P = W / B puts (B the bytes a
  put: the model is solved for B by iteration). A level of N nodes gets
  x = P / N touches a node a window.
* **Value leaves** are dirty for one window after a touch and then clean until
  the next: w = 1 / (1 + x) writes a put. **Every other node** is also written
  again while a child is dirty at its write (`DbHelper.handleStillDirtyNodes`):
  it stays dirty as long as each window touches it, w = 1 / (x + e^-x).
  Both go from 1 (cold, x << 1: every put writes the node) to 1/x (hot, x >>
  1: the node is written once a window).
* **Dead versions.** A leaf that is dirty when a split replaces it is written
  once more: about r (1 - e^-x) more writes a put, r = 2 / (S - 1 - k) the
  replacements a put (each touch adds a TIME and a KEY klong to a leaf of k
  live keys, max S). Dead inner versions are also kept dirty by hot children
  (section 7); the model leaves that out.
* **Node counts and sizes.** A value leaf holds about 0.45 S live keys, so
  N0 ≈ K / (0.45 S); a written leaf is about 62 percent full, measured 40 +
  9.85 S bytes (178, 338 and 655 at 14, 30 and 62); an inner level has about
  1/(0.4 S) of the nodes of the level below.

**Fit** (`nodesize/model.py`, `model2.py`: N from the tree after the load,
bytes a node from the run; update phase after its first 20 percent):

MODEL-TABLE

The model is within about 10 percent for node 30 at 10M keys, and within about
30 percent everywhere: low for node 14 (its dead inner versions on five levels
are left out), high for node 62 in the hot cases (its dead leaves are fewer
than r says).

**What it says about node size.** Take the leaves alone: their bytes a put
are about (56 + 10 S) / (1 + x0), with x0 = 0.45 S P / K. Their derivative in
S has the sign of 10 - 56 × 0.45 P / K: **smaller leaves are cheaper when a
window holds fewer puts than about 0.4 times the keys (P < 0.4 K), larger
ones when it holds more.** The inner levels shift this towards large nodes: a small
node size has more levels (5 for a segment-3 tree at 14, 3 at 30), each
written up to once a put while it is cold, and more dead inner versions while
it is hot. So:

* **cold** (index far larger than a window, P << K / 100): every level that is
  cold costs a full node a put; 14's nodes are half of 30's but it has one or
  two levels more. 14 wins only when also the levels above the leaves are
  cold: 10M keys at sd 10 MB, 812 against 939 bytes a put (load, -14 percent).
* **hot** (index smaller than a window, P > K): every node is written about
  once a window plus its dead versions; the leaves then cost about the same at
  every size (51, 59 and 67 bytes a put for 62, 30 and 14 at 1M keys and sd 200
  MB: every klong a put appends is written about once, in the version that
  holds it when it dies); fewer and larger inner nodes are cheaper: 62 wins,
  by 7 to 14 percent against 30.
* **between**: 30 is the best or within a few percent of it.

The regimes move with K / sd. At node 30 a window touches each leaf about once
(x0 = 1) where K ≈ 13.6 W / B, with B about 350 bytes a put there: at about 2M
keys for sd 50 MB, 8M for 200 MB and 40M for 1000 MB; the leaves are cold
(x0 < 0.2) from about five times that. (Node 14: 0.45 times those sizes, node
62: about 2 times.) So a database of 10M to 100M keys with a startup
distance of 200 to 1000 MB, as Frans proposes, is in the middle regime.

# 4. Memory

**MEM** (Props' `Mem`: 1M KVs `"0"` to `"999999"` in order, empty values,
100 a transaction, all resident; `nodesize/MemNode.java`, two runs each, the
same both times; `out/mem.txt`):

| node size | 8 | 14 | 30 | 62 |
|---|---|---|---|---|
| MEM, bytes a KV | 253 | 165 | 130 | 120 |
| against 30 | +95% | +27% | | -8% |

**The heap of this workload** (random `key24`, 8-byte values; after four full
GCs; `nodesize/structure.py`):

| | node 8 | node 14 | node 30 | node 62 |
|---|---|---|---|---|
| heap a key after the load, 1M keys | 454 | 250 | 186 | 160 |
| heap a key after the load, 5M keys | 444 | 244 | 179 | 156 |
| heap an update (history kept: retain forever, no eviction), 1M keys | 311 | 188 to 191 | 153 to 154 | 139 to 142 |
| heap an update, 5M keys | - | 208 to 225 | 161 to 173 | 146 to 157 |
| current key nodes a key | 0.442 | 0.200 | 0.081 | 0.037 |
| key nodes reachable through any pointer, a key (old versions included) | 0.97 | 0.41 | 0.16 | 0.07 |
| current index, memory estimate, bytes a key | 118 | 72 | 54 | 47 |
| current index on the stream, bytes a key | 50 | 34 | 26 | 23 |

About half of the key nodes in memory are dead versions that current nodes
still point to (0.16 reachable against 0.08 current at node 30). Node 8's
arrays are 14 slots for at most 8 klongs (the capacity classes), and its
nodes hold 3.3 live keys; it ran out of a 4 GB heap during the update
phases at 1M keys (after 7.9M of 12M updates) and at 5M (after 1.5M of 2M).


# 5. Tree shape

After the load (`out/u-n*-sd50-1M.txt`, `-5M.txt`; the same shape at 1M and
5M keys, as the segment-3 trees are full):

| | node 8 | node 14 | node 30 | node 62 |
|---|---|---|---|---|
| levels of a segment-3 tree (1000 keys) | 7 | 5 | 3 | 3 (2 in most trees) |
| longest path, key nodes, 1M / 5M keys | 17 / 18 | 12 / 13 | 8 / 9 | 8 / 8 |
| value leaves: klongs, live keys, array capacity | 5.0, 3.3, 7.7 | 8.5, 6.2, 11.7 | 18.1, 13.6, 24.4 | 37.4, 28.8, 50.6 |
| live keys a leaf over the maximum | 0.41 | 0.44 | 0.45 | 0.46 |
| nodes above the value leaves: share of nodes, of memory | 32%, 33% | 19%, 19% | 10%, 9% | 4.5%, 4% |

Written value leaves are not half TIME klongs: at 5M keys a written leaf of
node 30 has 19.2 klongs, of which 5.0 TIME, 14.2 live keys, during the load,
and 19.1, 5.1 and 11.4 (2.6 replaced) in the update phase; node 14: 9.1
klongs, 2.7 TIME, 6.5 live (load); node 62: 39.3, 9.8, 29.7. A written leaf
fills 60 to 65 percent of its maximum at every size.


# 6. D and the startup lag

D (`TransSeq`'s got-dirty nodes, the nodes a startup must rebuild and that a
budget cannot evict), over the update phase after its first 20 percent
(`nodesize/dsize.py`; stored bytes are `StoredKeyNode.getByteSize`; memory
is the `KeyNode.getMemSize` estimate, about 2.0 to 2.5 times the stored bytes):

DSIZE-TABLE

D's stored size is about one window: 43 to 79 MB at sd 50 MB, 85 to 241 MB at
200 MB, 678 MB (979 at most) at 1000 MB and 10M keys. In bytes it hardly
depends on the node size; in objects it does (node 14 about twice node 30's
count). So a larger startup distance pins about twice its size in memory. The
startup lag (the stream from the startup position to the end) is the
startup distance most of the time, with peaks of up to 2.6 times it at sd 50
MB (`take` stops after its node limit, 4 a put after two transactions).


# 7. Two findings beside the node size

**Dead versions are written, and kept dirty.** With `-Dwb.replaced=true` the
tool marks the nodes a transaction replaces (`TestHooks.nodeReplaced`) and
counts their writes (`out/r-*.txt`, update phase after its first 20 percent):

| run | value leaves | height 1 | height 2 |
|---|---|---|---|
| 1M keys, sd 50 MB, node 14 | 16% | 32% (21% stay dirty) | 58% (52%) |
| 1M keys, sd 50 MB, node 30 | 28% | 56% (43%) | 66% (63%) |
| 1M keys, sd 50 MB, node 62 | 33% | 63% (49%) | - |
| 1M keys, sd 200 MB, node 30 | 72% | 90% (54%) | 89% (75%) |
| 5M keys, sd 50 MB, node 30 | 4% | 18% (15%) | 0% |

(shares of a level's writes that were of dead versions; in parentheses, of
dead versions left dirty again). A leaf that is dirty when a split replaces it
is written once more, as a dead version; that write is needed, and when the
leaves are hot (a window touches each leaf many times) it is most of the leaf
writes: every put's two klongs end up written once in the version that holds
them when it dies. An inner dead version is also re-dirtied whenever one of
its children (shared with its replacement) is dirty at its write: BergDB's
conservative still-dirty test ("points to a node in D"). docs/sis-model.md,
6.2, describes exactly this ("A hot child ... keeps such a dead node dirty. It
is then written once per section for as long as the child stays hot"), and
the Lean model proves T1 and T2 for the exact test too. Measured: in the hot
regime half or more of the inner writes are dead versions. The writes that
follow a re-dirtied dead version, an upper bound for what the exact test
would save, are at 1M keys and sd 50 MB about 17 of 232 bytes a put at node
30, 39 of 318 at node 14 and 8 of 196 at node 62: more with more inner
levels, and nearly nothing once the leaves are cold (5M keys, sd 50 MB).

**A database starts only with the node size it was written with.**
`nodesize/RestartNodeSize.java` (`out/restart-check.txt`): written with node
size A, synced and closed (D not written, a startup section of about 1 MB),
started with size B. A = B: starts, all 20,000 keys read back. A ≠ B, all 12
pairs of 8, 14, 30 and 62: `StreamFormatException: startup error, node ...
not found, got dirty in trans ...`: the rerun of the startup section splits
differently and the got-dirty ids do not match. The size is not in the
stream. So a new default would make every existing database fail to start
unless its builder sets the old size; and a user who changes the size gets
what looks like a corrupt stream.

# 8. Method and commands

* **Tool.** `nodesize/NodeSizeBench.java` (package `bergdb.core`, run with its
  classes before the jar): the coordinator's `wb/WriteBench.java` (the same
  load, the same report line, the same update phase) plus, for every window of
  puts, the written key nodes by class (segment and height): writes a put,
  bytes, klongs, TIME klongs, live keys, the share left still dirty, and, with
  `-Dwb.replaced=true`, the share that were replaced (dead) versions; after the
  load and after the updates: D (`TransSeq`), the heap after four
  `System.gc()`, the current tree by class, and (`-Dwb.reach=true`) all key
  nodes reachable from the super root through any pointer. Checked against
  `wb/WriteBench.java` (cls3): 1M keys, node 30, sd 50 MB, 3M updates: all 40
  windows and D identical (`nodesize/xcheck.sh`).
* **Database.** In memory: a ring stream that keeps its last 512 MiB (1.3 GB
  for sd 1000 MB), no eviction, retain forever, the test clock (+0.1 ms a
  transaction), bergdb `716778e` (the scratch clone's `bergdb.jar`).
* **Workload.** Load K keys `key24` (`/scale/key/` + 13 digits) in a random
  order, 8-byte values, 1,000 puts a transaction; then U random puts to loaded
  keys, uniform with replacement (`SplittableRandom(2)`), 1,000 a transaction.
* **The figure.** Stream bytes a put over the update phase: the steady state
  at a fixed size. A load alone is dominated by transients at sd 200 MB and
  more (index writes come in waves; at the end most of the tree is still in D).
  U covers at least about five windows of sd bytes where it could (10M + 30M
  updates, 50M + 20M, as the coordinator's run3; 1M + 5M and 12M, 5M + 2M and
  5M). The update phase is bursty too (a cycle of about two windows); its
  whole-phase mean is the figure, the same way for every node size.
* **Heap.** `Runtime` total minus free after four `System.gc()` (ParallelGC),
  after minus before (the ring and the key order allocated before). MEM:
  `nodesize/MemNode.java`, Props' `Mem` (1M KVs `"0"` to `"999999"` in order,
  empty values, 100 a transaction, `DummyStream`, test setup) with a node size;
  default G1; `bergdb.dev.props.Mem` itself gives 130, as `MemNode` at 30.
* **Restart check.** `nodesize/RestartNodeSize.java`: 20,000 random keys at
  startup distance 1 MB, sync, close (D is not written: a startup section of
  about 1 MB stays), start a copy of the stream with each node size, read all
  keys back.
* **Separate leaf and inner sizes.** A scratch `Dag.java`
  (`nodesize/mixed/`, compiled to `nodesize/clsmixed/`, ahead of the jar):
  six lines, a limit for segment leaves from `-Dns.leaf` and for inner nodes
  from the builder's size. Only for this measurement; no bergdb code changed.
* **Machine.** F53 (10 cores, 32 GB), shared with the coordinator's runs; one
  JVM of mine at a time, `nice -n 10`, 4 GB until the coordinator's run3 was
  done, then up to 22 GB. Byte counts and heap are deterministic; no timing.

Commands (all from `nodesize/`; J is `../bergdb/java/build/bergdb.jar`):

    javac --release 17 -cp $J -d cls2 NodeSizeBench.java MemNode.java RestartNodeSize.java
    javac --release 17 -cp $J -d clsmixed mixed/Dag.java
    # one run (the run scripts ns3.sh to ns6.sh hold them all):
    nice -n 10 java -Xms14g -Xmx14g -XX:+UseParallelGC -cp cls2:$J -Dwb.keys=10000000 \
        -Dwb.window=1000000 -Dwb.updates=30000000 -Dwb.ring=1300000000 -Dwb.node=14 \
        -Dwb.sd=200000000 bergdb.core.NodeSizeBench > out/u-n14-sd200-10M.txt
    java -Xmx2g -Dnode=14 -cp cls2:$J bergdb.core.MemNode
    java -Xmx1g -cp cls2:$J bergdb.core.RestartNodeSize
    python3 -I tables.py; python3 -I breakdown.py 10 200; python3 -I model.py out/u-n14-sd200-10M.txt

# 9. What node size is in BergDB

* **The setting.** `DbBuilder.maxNodeSize8()`, `14()`, `30()` (the default)
  and `62()`: the most klongs a key node holds. A klong is 8 bytes: a TIME
  klong, a KEY klong (up to 7 key bytes and a pointer) or a delete bitmap. The
  arrays of a node (klongs, pointers, positions) grow through the capacity
  classes of `KeyNode.ARRAY_SIZES`, 2, 6, 14, 30, 62, 126. So 14, 30 and 62
  fill their largest class, and 8 does not: a node of 7 or 8 klongs has arrays
  of 14 (one reason for node 8's memory, section 4).
* **A node is a log of versions.** A transaction that changes a node appends a
  TIME klong and its KEY klongs. A full node is replaced by its last version: a
  space split into two halves if that version has more than half the maximum,
  else a time split (a compacted copy). The replaced node stays, for lookups at
  earlier times, and its parent gets new klongs for the new node(s). A search
  in a node is a linear scan of all its klongs, TIME and replaced ones included
  (`KeyNode.searchLte`).
* **Stored size** 32 + 16 bytes a klong (`StoredKeyNode.getByteSize`); in
  memory about 80 + 24 bytes a slot of capacity (`KeyNode.getMemSize`), plus
  its handle.
* **Hard limits.** 62 is the largest size the code supports: a delete bitmap
  has 62 bits, one a klong position, and `KeyNode.lastVersionGivenDel` asserts
  at most 62 klongs. 126, the last capacity class, is only reachable by a
  node that exceeds its maximum.
* **Not in the stream.** The node size is a builder setting only (no meta
  block field); a database is started with whatever the builder says. See
  section 7 for what that means at a restart.

The workload's keys shape the trees. A key of 24 bytes is 4 segments of 7, 7,
7 and 3 bytes (`Keys.toSegments`); each segment is a B-tree whose leaves point
to the next segment's roots, the last to the values. The keys
`/scale/key/` + 13 digits (WriteBench's `key24`, ScaleBench's format) give one
segment-0 node, one segment-1 node, one segment-2 tree of K/1000 keys (the
thousands of the key number) and K/1000 segment-3 trees of 1000 keys each.
So a class "s3h0" below is a segment-3 leaf (it points to values), "s3h1" its
parent, "s2h0" a segment-2 leaf (it points to segment-3 roots). At 1M keys and
more, the segment-3 trees are full: more keys means more of the same trees and
a larger segment-2 tree, not deeper segment-3 trees.


# 10. The 2015 investigation

The comment "150103 Frans: keeping maxNodeSize30() after renewed
investigation" points to the end comments of `Db.java` ("CorePerf vs maximum
node size"), the same text as F1-007 `bergdb/log.md` (report of 2015-01,
Frans's Cissi laptop): CorePerf, geometric mean of get, get4t, getmany and
set, each the best time over its 2013 baseline (lower is better):

| max node size | CorePerf | get | get4t | getmany | set |
|---|---|---|---|---|---|
| 8 | 1.00 | 1.25 | 1.65 | 0.73 | 0.66 |
| 14 | 0.73 | 0.82 | 1.06 | 0.61 | 0.55 |
| 30 | 0.77 | 0.79 | 0.98 | 0.86 | 0.54 |
| 62 | 0.89 | 0.86 | 1.06 | 1.22 | 0.60 |

Frans's conclusion then: keep 30; 14 is faster on the mean but 30 is best
for get (one and four threads); 8 is too small; 14 and 62 are reasonable.
"There are other criteria besides CorePerf; stream size, memory usage. Not
investigated now." (Core's tests use 100,000 KVs in memory, so this was a
small-database, CPU-only comparison.)

Older traces, all small: 2012-03 (F1-007 `doc/log-old/2012-log.txt`): 32 longs
"works best for Rose" for gets (256 bytes, four cache lines), after reading
Hankins and Patel on cache-conscious B+-trees. 2014-12 (`doc/2014/2014-q4-notes.txt`,
`bergdb.test.StreamSize.t3`): the average stream bytes of 100 single-put
transactions into a new database, 424, 359, 450 and 721 for 8, 14, 30 and
62 (the `kv2` branch: 56 for all). Nothing measured stream size or memory at
scale until now.


# 11. What node size also affects, not measured here

No timing was done (the machine was shared; byte counts are deterministic).

* **Gets in memory.** A get scans every node on its path linearly, TIME and
  replaced klongs included. Path length at 10M keys: node 8 about 18 key
  nodes, 14 about 13, 30 and 62 about 9 (section 5). Small nodes mean more
  pointer chases (node object, its arrays, its handle: cache misses), large
  ones longer scans (sequential, cheap per klong). 2015's CorePerf found 30
  best for get, 14 and 62 within 4 to 9 percent, 8 far behind; at 10M keys
  and more, with handles (item 009), the misses weigh more, which favours 30
  or 62 over 14. Unmeasured.
* **Device reads for a cold get.** One read a level that is not cached. With
  the inner levels cached, a cold get reads its leaf: one read at every node
  size. What differs is the memory the inner levels need to stay cached: the
  nodes above the value leaves are 33, 19, 9 and 4 percent of the current
  index's memory at node 8, 14, 30 and 62 (section 5), so at a fixed budget
  small nodes leave less room for leaves and values. A read is at most about 1
  KB (node 62), within one 4 KB page, at every size.
* **Sweeps and the collector.** Eviction's sweeps (Level 4) and the GC visit
  objects: node 14 has 2.5 times the key nodes of node 30, node 8 5.5 times,
  node 62 0.45 times (section 5). The sweep cost of item 005-03 scales with
  that.
* **Startup.** D (the dirty nodes, rebuilt at startup) and the rerun of the
  startup section: section 6 has D's size by node size.
* **Reclaim (Level 3).** Reclaim copies what is live forward; the live index
  on the stream is 50, 34, 26 and 23 bytes a key for 8, 14, 30 and 62
  (section 5).
* **Caching precision under a budget.** A cached node holds all its keys:
  with large nodes a hot key keeps more cold keys resident. Not measured.


# 12. Separate sizes for leaves and inner nodes

**How easy.** For a measurement, six lines of `Dag.java`
(`nodesize/mixed/Dag.java` against `Dag.java.orig`): a method
`max(KeyNode n)` that gives segment leaves one limit and inner nodes another,
used where `Dag` compares a node's size with `maxNodeSize` (`setValue`,
`setNode`, `appendDeleteKlong`, `appendKlongs`'s full test, `handleFullNode`'s
space-or-time split). For a real option also: the builder (two sizes), the
record bound of `Db.checkDirtyNodes` (it assumes the largest node),
`Dag.dirtyNodeBound`'s overflow count, the conformance sets of Levels 2 to 4
(today one size a run; they cover 8 to 62), and the restart rule of section
7 (both sizes would have to be the ones the database was written with). The
code ties: leaves at most 62 (the delete bitmap's 62 bits; deletes only occur
in segment leaves); inner nodes at most 62 too, by `lastVersionGivenDel`'s
assertion and its quadratic copy, though they never hold delete bitmaps; the
capacity classes 2, 6, 14, 30, 62 fit 14, 30 and 62 exactly. The Lean model
has no node size. So it would be easy; the question is whether it pays.

**Measured: it does not** (update phase, bytes a put; L = leaves, I = inner):

MIXED-TABLE

Small leaves pay only where the leaves are cold (a window touches few of
them), and there the inner level just above is cold or warm too: a 30- or
62-klong inner node then costs its full size a write, more than the 14-klong
inner nodes it replaces. Where the inner levels are hot enough for large inner
nodes to help, the leaves are warm and large leaves are as good. The model
(section 3) agrees: a mixed size wins only where the leaves are cold and the
level above them is hot, N0 >> P >> N1, which for leaves of 14 and inner nodes
of 62 means puts a window between about K/170 and K/6; at 50M keys and sd
1000 MB it predicts about 300 bytes a put for leaves of 14 and inner nodes of
62 against about 305 for node 30.
