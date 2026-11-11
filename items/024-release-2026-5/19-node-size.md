# 024-19. The node size: which, and one fixed constant or not

Created 2026-11-11 by Frans Lundberg. Status: open.

A study with measurements, no product code: what the node size B is
today, what the theory says a larger or smaller B does in BergDB's
append-only tree, what B costs and buys measured at 1M and 10M keys,
whether B should be one fixed constant, and a recommendation for release
2026.5, whose aim is solid algorithms (024-04). Frans, 2026-11-11, 11:24:
"By the way, the node size of 30 is open for discussion. And should it
even be a fixed constant? And should an index node be stored more
compact in the stream? Big questions. But these are important now when
we want to settle the algos. Solid algorithms are the aim." 11:31: "Node
size is worth a separate study. Compact stored format too." The compact
stored form is 024-20's; section 7 says what each study needs from the
other.

It builds on 005-38's node-size measurement (005-38, report, section 6,
and its draft `node-size/draft-report.md`, 2026-10-26: sizes 8 to 62,
stream bytes a put at 1M to 50M keys, MEM, tree shape, a model, separate
leaf and inner sizes), which it does not repeat. What is new here: the
code since then (the paced take, 2026.4's deletes, format 6, the
meta block's node size), sizes above 62 on a measuring build, other key
shapes and orders, batch size 1, the retain duration, gets under the
default cache at 10M, times, and the question of a constant.

Names: B the node size (the most klongs a key node holds); K the keys;
sd the startup distance; m, h, c 024-11's merge thresholds.


## 1. Summary

**Postponed, 2026-11-11, 11:50**: Frans decided to build 024-11's merges
first with B = 30 and to take the node size up after that (the
coordinator's message). Stopped with sections 2, 3, 5, 7 and 9 written,
1M counts of sets A, B and M in section 4.2, and no run at 10M; sections
6 and 8 are not written. The interim reading: at 1M keys the bytes an
overwrite and the heap a KV have a flat optimum at 30 to 62 (30 and 62
within 2 percent of each other in bytes, 62 8 percent below 30 in MEM,
nothing gained above 62), as section 3 predicted; the 62-bit delete
bitmap makes 62 the largest size without a format change.


## 2. The node size today

### 2.1 What it bounds, and in what unit

* **Key nodes only.** B bounds the klongs of every key node: segment
  leaves (they point to values, or with a key klong of length 7 to the
  next segment's root), inner nodes, and so every segment tree's root.
  It does not bound top nodes (the super root and its kind: 40 bytes and
  16 a pointer, up to 64 pointers; `Db.checkDirtyNodes`' `topBytes`) or
  value and delete nodes (one KV each, of any size; 024-02, section 12).
* **The unit is the klong, not the byte, and not the key.** A klong is
  an `i64` of one of three types (024-02, section 11.2): a TIME klong
  (begins the entries of a transaction), a KEY klong (a segment's compare
  value, up to 7 key bytes, with its pointer) or a delete bitmap. A key
  node is a log of versions, a "fat node": a transaction that changes it
  appends a TIME klong and its KEY klongs, and replaced and deleted keys
  stay until the node is full. So B counts history as well as live keys:
  a value leaf at B = 30 written in an update phase holds about 19
  klongs, of which 5 TIME, 11 live keys and 3 replaced (005-38, draft,
  section 5); its live keys are about 0.45 B.
* **Stored**, a key node is 32 + 16 n bytes for n klongs (8 the klong, 8
  its reference; `StoredKeyNode`, 024-02, section 11.1): at most 32 +
  16 (B + 1) = 528 bytes at B = 30 (a node may hold B + 1 for a moment,
  `KeyNode.check`). **In memory**, 80 + 24 bytes for each element of
  its arrays (`KeyNode.getMemSize`), whose lengths are the capacity
  classes 2, 6, 14, 30, 62, 126 (`KeyNode.ARRAY_SIZES`), plus its handle.

### 2.2 Where it is set, and its range

* `DbBuilder.maxNodeSize8()`, `14()`, `30()` (the default) and `62()`;
  the field is package-private, so only these four sizes can be chosen.
  The Pub API always uses 30 (`DatabaseBuilderImp`; 010-01, "the node
  size is not a setting of the Pub API").
* **A property of a database since 005-50**: the primordial transaction
  writes it into the meta block (`u16` at byte 44; 024-02, section 6),
  and a start with another size is refused (`Db.refuseOtherNodeSize`),
  as are databases without it. But it is still *given* by the start and
  compared, not *taken* from the block (024-02, G19 and Q19). So today
  it is a per-database property in the format, settable when a database
  is made by the Core API only, and a start must repeat it.
* **The hard ceiling is 62.** A delete bitmap is one klong with 62 bits,
  one for each klong index of its node (`Klong.DELETE_BITS`, 024-02,
  section 11.2), and every search tests `DELETE_BITS[i]` for each of its
  klongs; `KeyNode.lastVersionGivenDel` asserts at most 62. A node of
  more than 62 klongs needs another delete encoding: a format change.
* **The sizes are 2^k − 2**: 14, 30, 62 (and 8, below its class).
  Two reasons, both plausible, neither written down as the reason: a
  `long[30]` is 16 + 240 = 256 bytes with the JVM's array header, one
  power of two (the 2012 note below: "32 (longs) ... 256 bytes and 4x
  cache line size"); and 62 is the bitmap's limit (2012-06 notes: "If we
  limit a KeyNode to max 62 klongs, this works fine"). The capacity
  classes are the same numbers, so 14, 30 and 62 fill a class and 8
  does not (its arrays are 14 long).
* **Which tests use other sizes.** Most Core unit tests use 8, so that a
  few keys make deep trees (`DbTesterDelete`, `Eviction`,
  `CapacityTester`, `ReclaimRetentionTester`, the Pub layer's
  `PubTester`); `DbTesterRestart` runs 8, 14, 30 and 62 (and checks the
  refusal of another size, pair by pair); `DbTesterGetMany` 8, 14 and the
  default; the level scripts' conformance sets 8 to 62; the C clone
  mirrors 8, 14, 30 and 62 (012-02's format). The Lean SIS model has no
  node size; 024-12's tree model is parametric in M with the hypothesis
  M ≤ 62 (024-12, its table of assumptions), checked exhaustively at
  M = 4, 6 and 8 and against Java's traces at 8, 14 and 30.

### 2.3 What depends on it

| What                                | How it depends on B                                   |
|---|---|
| The split (`Dag.handleFullNode`)    | full at size + new + 1 > B; space split if > B / 2    |
| The time split                      | the last version, at most B / 2 klongs, copied        |
| 024-11's merges (planned)           | m = max(2, B / 4), h = B / 2, c = B / 2 (or m8 8/17/17) |
| `Dag.dirtyNodeBound`, `overflows`   | room B − 2 − size, then a split every B / 2 − 3       |
| `Db.checkDirtyNodes`                | a node at 32 + 16 (B + 1) + 16 bytes                  |
| 024-17's limits                     | nodes a KV dirties: height from m; 544 bytes a node   |
| Reclaim's steps                     | 80 + 48 B pinned bytes a node in the 4 MB reserve     |
| The cache's accounting              | 80 + 24 a capacity element; the class above B         |
| The stream                          | B in the meta block; nodes up to 32 + 16 (B + 1)      |
| The Lean models                     | SIS: none; 024-12's tree: a parameter M ≤ 62          |

* **The split rule.** A node that cannot take a transaction's klongs
  (its size, the new klongs and a TIME klong more than B) is replaced by
  its last version: two halves (a space split) if that version holds
  more than B / 2 klongs, else one compacted copy (a time split). A node
  the same transaction made is split in place. So a node goes through
  cycles: live klongs L ≤ B / 2 after a time split, then appends until
  B, then again.
* **Reclaim's step.** A step counts every index node it pins as 80 + 48
  B bytes (`Reclaim.stepNodeBytes`) against its 4 MB reserve, so the
  steps, and the records they write, depend on B: a larger B, fewer KVs
  a step.
* **The cache** counts a node at its array capacity, not its size, and
  evicts nodes whole: a larger B, fewer and larger units.

### 2.4 Where 30 came from

* **2012-03-12** (F1-007's `doc/log-old/2012-log.txt`): "DB.maxNodeSize
  = 32 (longs) works best for Rose. This is 256 bytes and 4x cache line
  size which is 64 bytes on Rose": a get benchmark on an Atom N450,
  after Frans read Hankins and Patel, "Effect of Node Size on the
  Performance of Cache-Conscious B+-trees" (2012-02-16: about 512 bytes
  rather than one cache line). The 2012-01 tree study: "Node size could
  be 128 bytes to suit cache line sizes ... and possibly larger to suit
  file system block sizes".
* **2012-06** (`doc/2012/2012-06-notes.txt`): the delete bitmap of 62
  bits, "If we limit a KeyNode to max 62 klongs, this works fine".
* **2014-q4** (`doc/2014/2014-q4-notes.txt`): stream bytes of 100
  one-put transactions into a new database, 424, 359, 450 and 721 at 8,
  14, 30 and 62.
* **2015-01** (the end comments of `Db.java`, "CorePerf vs maximum node
  size", Frans's Cissi laptop, 100,000 KVs in memory): geometric mean of
  get, get4t, getmany and set, 1.00, 0.73, 0.77 and 0.89 at 8, 14, 30
  and 62; "30 is best for getOne() performance (one or 4 threads) ...
  There are other criteria besides CorePerf; stream size, memory usage.
  Not investigated now." `DbBuilder`: "150103 Frans: keeping
  maxNodeSize30() after renewed investigation."
* **2026-10-26** (005-38, report, section 6): bytes a put at 10M keys
  for sd 50, 200 and 1000 MB: 679, 483, 219 at 14; 681, 373, 180 at 30;
  771, 330, 167 at 62; MEM 253, 165, 130, 120 at 8, 14, 30, 62. "Node 30
  is within 8 percent of the best at every distance measured ... The
  default stays." Separate sizes for leaves and inner nodes measured and
  not worth it (draft, section 12).
* **Others**: 006-02 (MEM, 2015 against 2026) keeps 30 throughout;
  006-19, section 3.1 (a node at most 512 bytes at 30), and its
  estimate of a compact encoding (35 to 40 percent fewer index bytes).

So 30 was chosen for in-memory gets on 2012 to 2015 laptops with small
databases, kept in 2015 on CPU alone, and checked for stream bytes and
heap at scale in 2026 (005-38). Nobody chose it for a stable format.


## 3. The theory, before measuring

### 3.1 What a put writes

A put makes every key node of its path dirty; a dirty node is written
whole when its transaction falls about sd behind the end (the take), and
puts that reach it meanwhile are absorbed (006-19, section 3.2; 005-38's
model, draft, section 3). Per level, writes a put go from 1 (cold: a
window of P = sd / (bytes a put) puts touches each node of the level at
most once) to N / P (hot: once a window). With f the fanout (live
klongs a node, about 0.45 B in leaves and 0.4 B above) and s(B) the
bytes of a written node (about 40 + 9.85 B, measured, 005-38):

* **Cold** (K much larger than P): bytes a put ≈ s(B) × levels ≈ (40 +
  9.85 B) × ln K / ln(0.45 B). The minimum is where ln(0.45 B) = 1 +
  4.06 / B: **B ≈ 10**. Relative to it, 14 costs 5 percent more, 30
  40 percent, 62 2.1 times, 126 3.5 times (the levels are whole numbers
  in practice, so the steps are coarser). Small nodes win when every
  level is cold, which no database of interest is above its leaves.
* **Hot** (K smaller than P): every klong a put appends is written about
  once, in the version that holds it when it dies; the leaves cost the
  same at every B, and fewer, larger inner nodes are cheaper. **Large B
  wins**, a little.
* **Between**, where 1M to 100M keys at sd 50 to 1000 MB lie: 30 within
  a few percent of the best (005-38). The regime moves with sd / K, so
  a fixed B is right for a ratio, not for a size.

The value node is written once, whatever B; with values of 100 bytes
and more it is a large part of a put.

### 3.2 Reads, memory and the rest

* **A get in memory**: one node a level, a linear scan of each node's
  klongs, history included (a node is a log; `KeyNode.searchLte`). Cost
  ≈ levels × (a + b n), with a the cost of reaching a node (a cache miss
  or two: object, arrays, handle) and n ≈ 0.6 B the klongs scanned. With
  levels ∝ 1 / ln n, the minimum is at n (ln n − 1) = a / b: for a / b
  of 50 to 100 (a miss of 100 ns against 1 to 2 ns a klong), **n about 22
  to 38, B about 35 to 65**. 2015's CorePerf agrees (30 best for gets).
  A binary search is not possible in a log node; that is what makes the
  optimum small.
* **A get under a small cache** (10M keys, 200 MB): loads a get ≈ the
  levels not resident. A larger B has fewer levels and a smaller share
  of inner nodes (about 1 / (0.4 B) of the index), so more of the top
  stays resident: fewer loads a get, each a larger read, but within one
  4 KB page up to B = 254 (4,096 bytes stored). **Large B wins** where
  reads miss, until a node passes a page.
* **Heap a KV** (no eviction): a node's fixed part (about 80 bytes and
  its handle) is shared by its 0.45 B live keys; its arrays cost 24
  bytes an element of capacity, about B / (0.45 B) elements a live key
  whatever B. So MEM ≈ c0 + c1 / B, falling and flattening: 253, 165,
  130, 120 at 8 to 62 (005-38); **predicted about 113 at 126 and 110 at
  254**, if the arrays' class fits B.
* **Dead klongs**: at most B a node (024-11, section 1; 024-18), so the
  dead klongs a live key are bounded by a constant in B / (0.45 B),
  whatever B; but a larger node keeps a hot key's dead versions longer.
* **Splits and merges**: a split copies O(B) klongs and happens once in
  about B / 2 appends to the node: O(1) a put amortized at every B. A
  merge (024-11) the same. The worst case of one operation, which 024-17
  bounds, grows with B: nodes a KV dirties × node bytes.
* **A scan** reads 0.45 B keys a leaf: per key, the cost of reaching a
  node falls as 1 / B; per key, the klongs passed are constant. **Large
  B wins**, flattening.
* **Startup**: D, the dirty nodes a start rebuilds, is about one window
  of stored bytes at every B (005-38, draft, section 6); its node count
  falls with B. The rerun of the startup section splits the same way.
  Little effect expected.
* **The worst case of a record** (024-17): a KV dirties up to about
  three nodes a level of a path; a node is 32 + 16 (B + 1) bytes. At B
  = 254 a path node is 4 KB against 528 bytes at 30: the dirty-node
  bound of a transaction grows 7.7 times while the height falls by a
  factor of about ln(13.5) / ln(114) = 0.55. **Large B costs** in the
  bound.
* **A small device** (024-17, section 6.9: a Pico 2, 520 kB of RAM):
  the memory of one path (levels × node bytes), not the bytes a KV,
  sets the floor: small B.

**Predicted optimum**: bytes a put flat from 14 to 62 with the best
moving from small to large B as sd / K grows; gets in memory best near
30 to 62; gets under a cache, scans and heap better with larger B and
flat after 62; the worst-case bounds better with small B. So a broad,
flat optimum around 30 to 62, nothing to gain above 62 that pays for the
format change of the delete bitmap.


## 4. Measurements

### 4.1 The probe and the build

* **Probe**: `19-node-size/NS.java` (package `bergdb.core`, after
  024-03's PF1), compiled apart and run before the jar. It sets the
  builder's package-private `maxNodeSize` to any value. `run`: a fill of
  n keys (random, ascending or a queue), then overwrites of random keys
  (or, for the queue, puts at the end and deletes of the oldest), the
  tree after each (a scan with CleanupRule's counting follower: key
  nodes, klongs, live keys, stored bytes; the key nodes of 2,000 gets'
  paths). `mem`: MEM's method (`DummyStream`, the test setup, empty
  values, 100 a transaction) with a node size and a key shape.
* **Build**: branch `024-19-nsize` in
  `/Users/f/fl/bench/2026-11-11/nsize/clone`, main at `1076235c` and one
  commit, `a06202be`, for sizes above 62 on workloads without deletes:
  `Klong.DELETE_BITS` 256 long with bits only for 0 to 61, a delete bit
  beyond 61 refused with an exception (so a run that would need one
  stops), and the array classes 254 and 510 added. At B ≤ 62 the build
  behaves as main.
* **Sizes**: 8, 14, 30, 62, 126, 254 (2^k − 2, so that every size but 8
  fills its array class: the brief's "about 15, 60, 120, 250").
* **Database**: a `FileStream` on the internal SSD, the builder's
  defaults (sd 50 MB, cache indicator 200 MB, eviction on), a test clock
  of 1 ms a transaction; retain 1 s (1,000 transactions) unless "forever".
* **Keys**: k13 = `/k/%010d` (13 bytes, 2 segments: 024-03's keys); k24
  = `/scale/key/%013d` (24 bytes, 4 segments of 7, 7, 7 and 3, a shared
  prefix: 005-38's `key24`); mem = `"" + i` (MEM's keys; at 1M, at most
  6 digits, one segment).
* **Counts** at 1M keys run one JVM at a time on one core
  (`-XX:ActiveProcessorCount=1`, SerialGC, 4 GB), with no slot
  (`19-node-size/c1m.sh`); outputs `19-node-size/out/c1m-SET-nB.txt`.

### 4.2 Counts at 1M keys

**Set A**: k13 keys in random order, values of 100 bytes, 100 puts a
transaction, then 1M overwrites of random keys, 100 a transaction,
retain 1 s (`out/c1m-A-nB.txt`). "Bytes a put" is the stream's growth a
put (the overwrites': over their last 80 percent); "path" the key nodes
a get follows; "index" the stored bytes of the current key nodes a key.

| B   | fill B/put | path | key nodes | live/node | index/key | overwrite B/put | nodes after |
|---|---|---|---|---|---|---|---|
| 8   | 564 | 15 | 488,967 | 3.0   | 56.9 | 618 | 673,331 |
| 14  | 408 | 10 | 224,250 | 5.5   | 38.8 | 461 | 287,201 |
| 30  | 329 | 7  | 88,990  | 12.2  | 28.9 | 394 | 111,176 |
| 62  | 309 | 6  | 40,537  | 25.7  | 25.3 | 400 | 49,749  |
| 126 | 301 | 5  | 19,478  | 52.3  | 23.8 | 418 | 23,529  |
| 254 | 299 | 4  | 9,383   | 107.6 | 23.8 | 439 | 11,327  |

* **Comparable with 024-03**: its fill of the same keys and values at B =
  30 wrote 328 bytes a put and left 88,974 key nodes (024-03, section 3);
  here 329 and 88,990.
* The fill falls with B and is flat from 62 (a fill into a growing tree
  is mostly hot leaves at 1M keys and sd 50 MB). The overwrites have
  their minimum at 30, with 62 1.5 percent above and 126 6 percent; 14
  is 17 percent above, 8 57 percent.

**Set B**: as A with k24 keys (24 bytes, a shared prefix, 4 segments)
and values of 0 bytes, where the index is nearly all of a put
(`out/c1m-B-nB.txt`):

| B   | fill B/put | path | key nodes | live/node | index/key | overwrite B/put | nodes after |
|---|---|---|---|---|---|---|---|
| 8   | 436 | 16.7 | 527,779 | 2.9   | 61.3 | 539 | 689,613 |
| 14  | 213 | 11.1 | 218,131 | 5.6   | 37.9 | 374 | 289,195 |
| 30  | 138 | 8.0  | 84,568  | 12.8  | 27.4 | 322 | 110,498 |
| 62  | 114 | 7.4  | 37,718  | 27.5  | 23.4 | 315 | 50,507  |
| 126 | 105 | 6.0  | 17,832  | 57.1  | 22.5 | 319 | 24,451  |
| 254 | 97  | 6.0  | 9,045   | 111.6 | 22.0 | 330 | 12,523  |

* The overwrites' minimum is at 62 (315), with 30, 126 and 254 within 2,
  1 and 5 percent of it; 14 is 19 percent above, 8 71 percent.
* The fill (each key a new path through four segment trees) falls with B
  all the way, 30 to 254 by 30 percent: a fill of new keys into small
  segment trees is the hot regime, where larger inner nodes win.

**Set M, MEM** (bytes of heap a KV, no eviction; MEM's method; one run
each, MEM's noise is a few bytes; `out/c1m-M-nB.txt`):

| B   | MEM's keys `"" + i` | k24 keys |
|---|---|---|
| 8   | 251.4 | 238.5 |
| 14  | 164.4 | 162.1 |
| 30  | 129.1 | 126.0 |
| 62  | 119.4 | 114.9 |
| 126 | 117.8 | 117.0 |
| 254 | 123.3 | 113.4 |

MEM at 30 is 024-03's 129.6. It falls as predicted to 62 (−8 percent)
and is flat after: the arrays' 24 bytes an element of capacity, about
2.2 elements a live key at every B, are most of it.


## 5. One fixed constant, or not

Five options. For each: what it is, what it costs and buys, and its
effect on the Lean model, the format and the C clone, 024-11's merges and
024-18's dead klongs.

**(a) One constant for every database.** B is a literal in one place of
the code (Java and C), the meta block's field is kept only to refuse a
database of another size, and the builder's setters go.

* Buys: one tree shape for every database; one number in every bound
  (024-17's nodes a KV, the record's worst case, reclaim's step); one
  set of merge thresholds (024-14's m8, 8/17/17, as numbers); the
  conformance sets run one size; the C clone has one.
* Costs: the tests lose their small trees. Today most Core tests use B =
  8 so that a few hundred keys make trees of five levels and more, with
  splits, time splits and (with 024-11) merges at every level; at B = 30
  the same coverage needs about 30 times the keys, and some tests that
  aim at a deep tree would take minutes. So in practice (a) keeps a
  test-only size, which is (b) for tests.
* Lean: the model may still be parametric (024-12's tree is, with M ≤
  62); a literal makes the decision procedures (`decide`) usable on the
  thresholds' arithmetic, and the exhaustive checks would still run at
  small M, as a parameter.

**(b) A property of the database, fixed when it is made** (today, since
005-50, in the Core API only).

* What varies with B: the split rule (as today, B and B / 2); 024-11's
  thresholds, which must become formulas in B (for instance m = B / 4 +
  1, h = B / 2 + 2, c = h, which gives m8's 8/17/17 at B = 30, 4/9/9 at
  14, 16/33/33 at 62; to be checked against 024-14's thrash rules for
  every B allowed: at B = 8 the formula gives c = h = 2m, the shape with
  a split-merge cycle on paper, 024-14, section 6); 024-17's height
  bound (H ≤ 1 + log_m(2^60): 22 at m = 7, 31 at m = 4, so the
  dirty-node bound grows for small B); the
  record's worst case (node bytes 32 + 16 (B + 1)); reclaim's step
  (80 + 48 B).
* Buys: the tests keep 8; a later class (option e) costs nothing more in
  the format; a database outlives a change of the default.
* Costs: every bound and threshold is a function, and the tests' matrix
  has a size axis (the conformance sets today run 8 to 62). The start
  must read B from the meta block (024-02, Q19; today it is given and
  compared, so a Pub API user cannot open a Core database of 14).
* Lean: B a parameter with hypotheses (4 ≤ B ≤ 62, B even or not),
  which 024-12's tree already has; proofs over all B allowed cost
  little more than at one B when they never compute with it.
* Format and C: the field exists (`u16` at 44); C reads it.

**(c) Different sizes for leaves and for inner nodes.** Measured in
005-38 (draft, section 12): it does not pay; a mixed size wins only where
the leaves are cold and the level above hot (N0 ≫ P ≫ N1), by a few
percent. It doubles the parameters of (b). Not recommended.

**(d) A node bounded in bytes (a page).** Today the stored bytes of a key
node are 32 + 16 n exactly, so a byte bound is a klong bound under
another name. It differs only with a variable-length encoding (024-20):
then a node of P bytes holds a varying number of klongs, the split rule
and the merge thresholds are in bytes, and the delete bitmap's 62
indexes still bound the klongs, so two bounds hold at once.

* Costs: the tree's shape depends on the encoder: a change of encoding
  would change where nodes split, so a start's rerun of the startup
  section would need the encoder of the database's format, and the Lean
  model would need the encoder's size function inside the split rule.
  That couples the algorithm to the format, the opposite of 024-04's
  "algorithms first, then not changed".
* Buys: a node fills a disk page or a cache line exactly; useful for a
  B-tree that reads pages in place, which BergDB does not: it reads
  whole nodes from a log, at any offset.
* Not recommended: bound the klongs; let the encoding make them small.

**(e) Database classes S, M and L** (024-17, section 6.9; Frans's thought,
"certainly not for 2026.5"). B would be one value of a class's set of
limits, in the meta block beside the others.

* If B is per database (b), a class adds nothing for B; if B is one
  constant (a), a class brings (b) back for S only.
* Which B a class would take: L (100M keys and more, several GB) is
  where large B helps gets under a cache and heap, by up to about 10
  percent (sections 3 and 4); M as today; S (a Pico 2, 520 kB of RAM) a
  small B, as the memory of one path is what counts there. The
  measurements of section 4 say how much L would gain.


## 6. Recommendation

Not written: postponed (State).


## 7. With 024-20, the compact stored form

The two interact through one function: the stored bytes of a key node
of n klongs, s(n) = H + C n today with H = 32 and C = 16 (the klong and
its reference).

**What the compact form does to the best B.** In the cold regime the
best B solves ln(0.45 B) = 1 + (H' / C') / B, with H' and C' the header
and the per-klong bytes as a written node fills (section 3.1: today H' ≈
40, C' ≈ 9.85, H' / C' ≈ 4). Only the ratio counts. An encoding that
cuts both (say a 16-byte header and 6 bytes a klong) moves the optimum
from about 10 to about 11; in the hot and middle regimes every klong is
written about once whatever B, so a compact klong cuts the bytes a put
at every B alike. **So the compact form scales the curve and hardly
moves its minimum**, with two exceptions that 024-20 should report:

* **Prefix sharing inside a node.** If neighbouring klongs share their
  leading bytes (024-20, section 2.3: keys `...0000123` and `...0000124`
  share 6 of 7), a larger node has closer neighbours and more sharing:
  the bytes a klong then fall with B, which moves the optimum up.
* **Free time klongs and dead klongs.** If a time klong or a dead klong
  costs less than a live one, a fat node's history costs less, which
  favours larger B a little (a node keeps its history until it is full).

**What 024-19 needs from 024-20**: its bytes of a written key node as a
function of n and of the klongs' kinds (live, dead, time), on the
streams of section 4, at two or three B (30 and 62 at least), so that
section 3.1's model can be rerun with them; and whether its delete
encoding still has a fixed number of indexes (the 62 limit).

**What 024-20 needs from 024-19**: the range of B (whether a node may
hold more than 62 klongs, which needs a new delete encoding, and how
wide n's field must be: a `u8` holds 254); that B is a property of the
database in the meta block (so the encoding needs no field of its own
for it); and that the split rule stays in klongs, not bytes (option d,
section 5), so that the encoding never changes the tree's shape and can
be designed after the algorithms are settled.


## 8. Questions for Frans

Not written: postponed (State). Open so far, from section 5: whether B
stays a property of the database read from the meta block (option b,
024-02's Q19), and whether 024-11's thresholds become formulas in B.


## 9. Not measured

* **Sizes above 62 with deletes**: the measuring build refuses a delete
  bit beyond 61, so the queue (set D) and every delete ran at B ≤ 62
  only; 024-11's merges were not in any run (main's code).
* **A cold OS cache**: no `purge` (it needs root); "cold" is a new JVM
  over files the OS holds, as in 024-03.
* **Gets with several threads**, 2015's get4t: not measured.
* **100M keys**: stood in for by 1M keys at sd 0.5 MB (set H), on the
  rule that the bytes a put depend on sd / K (006-19, section 1); the
  heap, the cache's loads and times do not follow that rule.
* **The worst case of one transaction** (024-17's record bound) was
  computed, not measured.
* **A small device** (a Pico, option e): not measured; the C clone was
  not run.


## State

2026-11-11, 11:51. **Stopped at the coordinator's message of 11:50**
(Frans: merges first at B = 30, the node size after that; this study
postponed, not dropped). Every run was stopped, no slot was taken or is
held, the data directory `/Users/f/fl/bench/2026-11-11/nsize/data` was
removed. Done: sections 2 (point 1), 3 (point 2), 5 (point 4, a draft),
7 (with 024-20) and 9; section 4.2 has the 1M counts of sets A (k13,
values 100), B (k24, values 0) and M (MEM). One run of set G (B = 8 at
sd 5 MB) is in `out/c1m-G-n8.txt`; the rest of G was stopped. Not done:
sets C to I at 1M, every 10M run, the times, sections 6 and 8.

**Interim**: at 1M keys (sd 50 MB, retain 1 s) the overwrites' bytes a
put are lowest at 30 (k13, 394) or 62 (k24, 315), the other within 2
percent; 126 and 254 1 to 11 percent above, 14 17 to 19 percent, 8 57
to 71 percent. MEM falls to 62 (119 against 129 at 30) and is flat
after. A flat optimum at 30 to 62, as predicted.

**What a later agent should do first**:

1. Read 024-11, 024-14 and the merges as built (their thresholds at B =
   30), and recheck that the measuring build below still applies on the
   new main (merge it or rebase the one commit: `Klong.DELETE_BITS` and
   `KeyNode.ARRAY_SIZES` only).
2. Run the 1M sets left (`c1m2.sh G`, `H`, `E`, `F`, `C`, `I`, and `D`
   at 8, 14, 30 and 62 only: it deletes), one core each, no slot; then
   `c10m.sh A "30 126" "14 62 254"` in one slot (about 25 minutes); then
   the timing hold `t1m.sh` (both slots, about 6 minutes) last.
3. With the merges in, measure their thresholds as formulas in B at 14
   and 62 (section 5, option b), then write sections 6 and 8.

* **Build**: branch `024-19-nsize` (head `a06202be`, one commit over main
  `1076235c`) in `/Users/f/fl/bench/2026-11-11/nsize/clone`, built
  (`java/build/bergdb.jar`). Probe source here (`19-node-size/NS.java`,
  a copy of `/Users/f/fl/bench/2026-11-11/nsize/NS.java`), compiled to
  `/Users/f/fl/bench/2026-11-11/nsize/cls2` (`cls` is an older
  compile without gets, scans and restarts, used by `c1m.sh`).
* **Scripts** (`19-node-size/`): `c1m.sh` (sets A, B, M), `c1m2.sh`
  (C ascending, D queue, E one overwrite a transaction, F retain
  forever, G and H sd 5 and 0.5 MB as stand-ins for 10M and 100M keys,
  I k13 with values 0), `c10m.sh` (10M in one slot, two JVMs), `t1m.sh`
  (times, a timing hold), `table.py` (`python3 -I table.py c1m` or
  `c10m`). The scripts that take a slot do it through `slot.sh`, which
  belongs to 2026-11-11's coordinator: check it still exists.
