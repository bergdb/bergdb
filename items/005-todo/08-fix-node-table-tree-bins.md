005-08. Fix the node table's tree bins (`Cache3.mapIndex`)
=========================================================

Status: open. Kind: fix. Created 2026-10-19.


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
