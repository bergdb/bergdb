005-08. Fix the node table's tree bins (`Cache3.mapIndex`)
=========================================================

Status: done (2026-10-19; see Outcome). Kind: fix. Created 2026-10-19.


The issue
---------

A performance fault, not a correctness one, found in
[006-02](../006-2026-q4/02-props-2017-vs-2026.md) (section 4).

Cache3, the node table that Level 4's eviction works on, has an entry for
every node in memory, value nodes too. It keeps them in 256
`HashMap<Long, CacheEntry>` maps and picks the map by the XOR of the node id's
eight bytes (`Cache3.mapIndex`). `HashMap` picks the bin from
`h ^ (h >>> 16)`, where h is the id's hash. Once the map is fixed, the bin
depends only on the XOR of two bytes of the id. That gives at most 256 bins
per map, 65,536 in all, while a map's capacity is at most 2^16 (up to about
12 million entries).

The bins fill up, and `HashMap` turns every bin of 8 or more into a red-black
tree. So every entry is a 56-byte `HashMap$TreeNode` instead of a 24-byte
`HashMap$Node`. Every lookup, insert and removal walks a tree comparing
`Long`s, under the table's one lock: `getLock` returns `bigLock` for every id.

Measured on the 2026 code, Props's MEM database (a million small KVs):

* 1.10 tree nodes per KV, 61 bytes per KV, 27 percent of MEM.
* A simulation of the same ids gives exactly 65,536 bins, up to 37 ids in one,
  and every id in a bin of 8 or more.

The fault came with the split into 256 maps on 2017-07-31 (original commit
`fa338b0`). With one map (`9d9a038`, `87d5faa`) the bins were ordinary.

An experiment: [006-02's maphash.patch](../006-2026-q4/02-props-2017-vs-2026/maphash.patch)
picks the map from the top 8 bits of `id * 0x9E3779B97F4A7C15L` (Fibonacci
hashing). Results:

* MEM 227 to 191 bytes per KV (−16 percent).
* Core's `set` 1.80 to 1.60 us per transaction (−11 percent).
* The other Props tests and the stream unchanged.

It ran only in 006-02's builds; no gates were run.


The task
--------

1. Change `Cache3.mapIndex` so that the map and the bin depend on different
   bits of the id: the patch's multiplicative hash, or a single map. The 256
   maps do nothing for locking today.
2. Find out whether anything depends on the table's iteration order.
   `Cache3.nodes()` feeds `Residents.walk` in the sweeps (`Eviction`: the
   capacity controller and the test schedules) and the audit. If a sweep's
   choice follows that order, the fix changes which objects are evicted, for
   example among objects of the same age, or under the random schedule. The
   stream must not change (EvictionInvariance), but a test with exact counts
   may.
3. Add a test that the bins stay small. Two options:
   * the class histogram of a million-KV database has no
     `HashMap$TreeNode`;
   * a check of `mapIndex`'s spread over consecutive odd ids. Node ids are
     `Spos.nextVpos` numbers, counted from the stream's end in each
     transaction.

Not part of this: a table keyed by primitive longs (no `Long` keys, no bin
objects) might save about another 25 to 35 bytes per KV. Keeping the reference
count in the node instead of a `CacheEntry` might save 17.5 more. Both are
estimates and would change more code.


Done when
---------

* No tree bins: MEM's database on F53 at 191 bytes per KV or less (006-02's
  `Probe006 histo`).
* Props's `set` at least 10 percent faster than 006-02's 2026 numbers, the
  other tests within noise.
* The stream unchanged: StreamDigest identical, Props's SS unchanged.
* The four gates print `LEVEL n OK`.
* `performance.sh`'s quick suite against the reference gives no alerts.


First step
----------

Apply maphash.patch on a branch, run the unit tests and `level4.sh`'s quick
part, and read `Residents.walk` and the sweeps for order dependence.


Size and order
--------------

S. Independent of 005-01 and 005-02, which change other files. Before
005-03, whose sweeps walk this table.
005-03, whose sweeps walk this table.


Outcome
-------

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-19, at
Frans's request ("Fix bergdb 005-08"). Two other sessions worked on bergdb
at the same time (a Props step in `java/stress/level1.sh`, and 005-02), so
the builds, the gates and the measurements ran in a local clone of
`8c5a106` with the change. The change was then copied here, the same lines,
and is left for Frans to commit (he did, in `0597329`).

The criteria of "Done when", point by point:

* **No tree bins: met.** MEM's database (006-02's `Probe006 histo`) takes
  190.7 bytes per KV, against 226.5 before, and has no `HashMap$TreeNode`
  (1,095,639 before, for 1,095,709 table entries).
* **`set` 10 percent faster: met in matched runs.** Props's `set` 0.355 to
  0.32 (−10 percent, six runs each); the probe's `set` 1.85 to 1.61 us per
  transaction (−13 percent), 10.6 percent below 006-02's 1.80. Props's two
  decimals against 006-02's median, 0.34, give only 6 percent: on this day
  the code before the fix gave 0.355, not 0.34. `get`, `get4t` and `getmany`
  within noise.
* **The stream unchanged: met.** StreamDigest identical, 36 of 36 (twelve
  configurations in three modes); Props's SS 1.50 (1.10, 1.19, 1.62, 2.37)
  in all twelve runs, before and after, as in 006-02.
* **The four gates: met.** `LEVEL 1 OK` to `LEVEL 4 OK`, full runs, in the
  clone. A run of the gates on the main tree with 005-02's change too was
  started the same day and not finished; the four gates have passed since
  on trees with both, in 005-10 and in 005-04's follow-up (`c6ca623`).
* **`performance.sh`'s quick suite: no alerts**, against the code before the
  fix, in one matched session.


The change
----------

In [Cache3.java](../../java/src/bergdb/core/Cache3.java):

* `mapIndex(id)` is the top `MAP_BITS` = 8 bits of `id * 0x9E3779B97F4A7C15L`
  (Fibonacci hashing), as in 006-02's patch. They depend on every bit of the
  id, and `HashMap` takes the bin from the low bits, so the map no longer
  fixes the bin. Never negative (an unsigned shift); `testLargeIds` still
  covers ids past 2^31.
* The 256 maps stay; one map was task step 1's other option. A map resizes
  inside a put, under the table's lock, which a reader's load takes too
  (`getNode`): with 256 maps a resize moves a 256th of the table, with one
  map the whole table at once. The maps also keep a lock per map possible;
  `getLock` still returns one lock for every id.
* `nodes()` says what its order is and what follows it (next section).
* A unit test, `testBinsStaySmall` (next sections but one).


The table's order (task step 2)
-------------------------------

`Cache3.nodes()` lists the table by map and by bin, so in an order given by
a hash of the node ids, and the fix changes that order. Three choices of
`Eviction` follow it:

* The capacity controller's sweep (the budget schedule, the default) first
  releases objects that only the table holds, in this order, until it has
  freed enough.
* It then unswizzles memory pointers by age, the oldest first, and pointers
  of the same age by their parent's place in `Residents.walk`, the later
  first (`OLDEST_FIRST` and `seq`; `Eviction` calls a pointer a slot). The
  walk starts from the super root, every object of the table and D's, so a
  canonical object's place in the walk is its place in the table's order.
  The tie is broken by a hash of the parent's id, not by depth as
  `OLDEST_FIRST`'s comment says ("so the deeper"); only snapshots, which the
  table does not hold, come in breadth-first order. A probe on a database of
  4,000 keys (maximum node size 8): of 6,724 pairs of canonical index
  objects, parent and child, the walk puts the child first in 3,469 before
  the fix and 3,486 after. Not new and not changed by the fix: a note for
  005-03.
* The random schedule (tests only) draws for each memory pointer, and for
  each object that only the table holds, in the walk's order.

The values and every schedules, the complete sweep (`takeAll`), the audit,
`Residents.resync` and TraceExport's SLOT lines (sorted) do not depend on the
order. Nothing depends on it for correctness: which detachable objects a
sweep takes does not change the records. Measured with EvictionInvariance in
`level4.sh`'s node8 configuration (2,000 transactions), with both builds:
every schedule's stream identical to the one without eviction; the same
counts for values (20,907 pointers unswizzled, 20,118 objects released) and
every (62,185 and 60,536); other counts for random (30,670 and 45,610
before, 30,693 and 45,746 after) and for the budget (56,765 and 57,200 in
453 sweeps before, 56,161 and 57,057 in 454 after); 2,005 audits each, none
failed. The unit tests and the gates pass with the new order.


The test (task step 3)
----------------------

`Cache3.testBinsStaySmall`, the second option: the test needs no class
histogram and runs in under a second. For three cases of a million node ids,
made as the writer makes them (each transaction's ids are consecutive odd
numbers from the stream's end, `Spos.nextVpos`), it puts the ids into the
maps by `mapIndex` and into bins as `HashMap` does: the low bits of
`h ^ (h >>> 16)`, h the `Long`'s hash, the capacity doubled when the size
passes three quarters of it. A put into a bin that holds 8 makes `HashMap`
turn the bin into a tree. The test fails if more than 10 puts of a million
do that, or if a bin passes 10 ids. The cases: Props's MEM (110 nodes a
transaction, transactions 5,000 bytes apart), single puts on a stream past
4 GB (4 nodes, 150 bytes), and large transactions near 2^40 (1,000 nodes,
30,000 bytes).

| Case | Puts into a bin of 8, before | after | Largest bin, before | after |
|---|---|---|---|---|
| Props's MEM | 478,452 | 0 | 26 | 7 |
| Single puts past 4 GB | 528,827 | 0 | 59 | 7 |
| Large transactions near 2^40 | 475,712 | 1 | 19 | 9 |

"Before" is the old `mapIndex` in the same simulation (`TestCheck.java`);
with the new one, a few puts in a million meet a bin of 8, as with random
hashes at `HashMap`'s load factor of 0.75. A wider check with real
`HashMap`s (`BinSim.java`), 43 patterns of 1.1 million ids (the cases above
and others, starting from 0 to about 2^46, and random ids), found tree nodes
after the fix in one pattern only, 7 of them, against about one per id before
in every pattern.


Measurements
------------

On F53, as in 006-02: JDK 27 with its default flags, one fresh JVM a run,
started when the CPU was at least 90 percent idle, no `-ea`. Two preserved
builds of `performance.sh build`: `pre-0508`, the code before the fix
(`8c5a106`, whose `java/` is 006-02's 2026-10-19 code), and `fix-0508`, with
the fix. Runs alternated (ABBA), medians and ranges:

| Measure | Before | After | Change |
|---|---|---|---|
| MEM's database (`Probe006 histo`), bytes per KV | 226.5 | 190.7 | −16 % |
| Its `HashMap$TreeNode` objects | 1,095,639 | 0 | |
| Its `HashMap$Node` objects | 930 | 1,096,569 | |
| Props: MEM (6 runs each) | 227 (226–227) | 191 (191–192) | −16 % |
| Props: CORE | 0.31 (0.30–0.32) | 0.305 (0.30–0.31) | |
| Props: `get` | 0.265 (0.23–0.28) | 0.27 (0.26–0.28) | within noise |
| Props: `get4t` | 0.38 (0.38–0.39) | 0.40 (0.36–0.41) | within noise (below) |
| Props: `getmany` | 0.255 (0.25–0.27) | 0.25 (0.25–0.26) | within noise |
| Props: `set` | 0.355 (0.35–0.36) | 0.32 (0.32–0.34) | −10 % |
| Props: SS | 1.50 (1.10, 1.19, 1.62, 2.37) | the same | none |
| Core alone (4 runs each): CORE | 0.305 (0.28–0.32) | 0.28 (0.28–0.30) | |
| Core alone: `get4t` | 0.375 (0.33–0.46) | 0.34 (0.34–0.41) | |
| Core alone: `set` | 0.35 (0.35–0.37) | 0.32 (0.32–0.33) | −9 % |
| The probe's `set` (`Probe006 set`, 4 runs each), us per transaction | 1.85 (1.78–1.97) | 1.61 (1.59–1.64) | −13 % |

`get4t`, four threads, is the test that other work on the machine disturbs
(006-02, section 7), and this afternoon gave higher values than 006-02's
(0.31 to 0.39) in both builds; over all ten runs of each build its median
is 0.38 before and 0.39 after, with ranges of 0.33 to 0.46 and 0.34 to 0.41.
The readers' path does not touch the node table once the nodes are in
memory (`NodeCollection.followPointer`), so no direct effect is expected.

`SUITE=quick performance.sh ab pre-0508 fix-0508`, one matched session, 3
runs of each scenario a build, 93.7 percent idle at the start: **no
alerts**. Commits 1.4 percent faster with infinite retention and 3.0 percent
with finite; after a restart, the mixed phase 5.0 percent more commits and
3.5 percent more gets; startup between −1.5 and +3.0 percent; warm gets and
scans within 3.5 percent either way. Flagged to explain, the maxima of
`r-1k-fin`: a GC pause of 78 ms against 25. Four of the six runs, all three
of the fix's, have a third young collection of 78 to 98 ms near the end of
the mixed phase (the heap from 1.3 to 1.5 GB down to 0.56 to 0.61 GB); in
two of the fix's runs it fell inside the measured window. When a collection
comes decides it, as in item 001's J10
([level4-performance.md](../001-lean-model-levels-3-4/11-level4-performance.md)).


Files
-----

In [08-fix-node-table-tree-bins/](08-fix-node-table-tree-bins/):

* [run.sh](08-fix-node-table-tree-bins/run.sh): Props and 006-02's
  `Probe006` on preserved builds of `performance.sh`, one fresh JVM a run,
  waiting for a quiet CPU, ABBA.
* [runs/](08-fix-node-table-tree-bins/runs/): one file per run (the build,
  the machine state before it, the output): `histo`, `props`, `set`, `core`,
  and the tools' runs.
* The tools, run by `run.sh tool`:
  [TreeCount.java](08-fix-node-table-tree-bins/TreeCount.java) (the tree
  nodes of MEM's database),
  [TestCheck.java](08-fix-node-table-tree-bins/TestCheck.java) (the unit
  test's simulation with the old and the new index),
  [BinSim.java](08-fix-node-table-tree-bins/BinSim.java) (43 patterns, real
  `HashMap`s; `JFLAGS="--add-opens java.base/java.util=ALL-UNNAMED"`) and
  [WalkOrder.java](08-fix-node-table-tree-bins/WalkOrder.java) (parents and
  children in the walk's order).
* [ei-node8-pre-0508.txt](08-fix-node-table-tree-bins/ei-node8-pre-0508.txt),
  [ei-node8-fix-0508.txt](08-fix-node-table-tree-bins/ei-node8-fix-0508.txt):
  EvictionInvariance, both builds.
* [digest-pre-0508.txt](08-fix-node-table-tree-bins/digest-pre-0508.txt),
  [digest-fix-0508.txt](08-fix-node-table-tree-bins/digest-fix-0508.txt),
  [digest-compare.txt](08-fix-node-table-tree-bins/digest-compare.txt):
  StreamDigest, run as its comment says (the stress classes of `pre-0508`
  against both jars).
* [perf-quick-ab.txt](08-fix-node-table-tree-bins/perf-quick-ab.txt): the
  output of `performance.sh ab`; its sessions were in the clone and are not
  kept.
* [gates-fix-0508.txt](08-fix-node-table-tree-bins/gates-fix-0508.txt): the
  four gates in the clone.

To repeat, in a tree without the change and then with it:
`java/stress/performance.sh build pre-0508`, then `... build fix-0508`;
`run.sh probe pre-0508 fix-0508`; `run.sh ab props 3 pre-0508 fix-0508`,
`run.sh abclass set 2 pre-0508 fix-0508 Probe006 set 50000000`,
`run.sh abclass core 2 pre-0508 fix-0508 bergdb.dev.props.Core`;
`IDLEMIN=0 run.sh class BUILD histo Probe006 histo 20000000` and
`IDLEMIN=0 run.sh tool BUILD LABEL FILE.java` for each build; and
`SUITE=quick java/stress/performance.sh ab pre-0508 fix-0508`.
