# 024-19. The node size: which, and one fixed constant or not

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-12): Q1, Q4
and Q6 decided (Frans, 2026-11-12), made in 024-27; Q2 and Q3 decided
as built (Frans, 2026-11-13); Q5 proposed for 2026.6 (026's readme).

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

Postponed on 2026-11-11 at 11:50 until the merges were in; resumed
2026-11-12, 00:40, on format 7 (024-21's merges with 8/17/17 at B = 30,
024-23's option 2 with theta 7 at 30, both scaled v B / 30 at other
sizes; 024-25's CRC32C). Measured at B = 8, 14, 30, 62, 126 and 254
(above 62 only without deletes, on a measuring build).

* **Bytes a put** (sections 4.2, 4.3): two regimes. With few keys
  against a window of puts (1M keys, sd 50 MB) 62 to 254 are best, 30
  4 to 9 percent above them; with many (10M keys at sd 50 MB, and 1M at
  sd 5 and 0.5 MB, the ratio of 10M and 100M keys), 14 is best, 30 7
  to 10 percent above, 62 29 to 45 percent, 126 two times and more. 30
  is the only size within 10 percent of the best everywhere.
* **Heap** (MEM): 129 bytes a KV at 30, 119 at 62 (−8 percent), flat
  above, 164 at 14.
* **Times** (1M keys): puts fastest at 30 (62 9 to 10 percent slower);
  gets equal at 30 and 62; scans 18 percent and a restart 22 percent
  faster at 62. At 10M under the 200 MB cache 62 needs one index load
  in five fewer than 30.
* **Above 62** costs a new delete encoding and smaller limits (the
  release limits' worst transaction would not fit a record at 126) for
  at most 4 percent in the hot regime and two to four times the bytes
  in the cold one: no.
* **Theta at B = 8** (option 2's floor of 1) costs 25 percent of the
  bytes a put for nothing; 2 costs 1 to 2 percent (section 4.5).

**Recommendation** (section 6): keep B = 30 for 2026.5, the Pub API's
only size; keep B a property of the database (option b: 8, 14, 30, 62
by the Core API, in the meta block, the thresholds and theta functions
of B as built), with theta at least 2; 62 the hard maximum. Questions
Q1 to Q6 in section 8.


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
| The split (`Dag.handleFullNode`)    | full at size + new + 1 > B; space split if > h        |
| The time split                      | the last version, at most h klongs, copied            |
| 024-21's merges, 024-23's theta     | 8/17/17 and 7 at 30, v B / 30 elsewhere (4.1)         |
| `Dag.dirtyNodeBound`, `overflows`   | room B − 2 − size, then an overflow every q (4.1)     |
| `Db.checkDirtyNodes`                | a node at 32 + 16 (B + 1) + 16 bytes                  |
| 024-17's, 024-24's limits           | height from m, nodesALevel from q; 32 + 16 (B + 2)    |
| Reclaim's steps                     | 80 + 48 B pinned bytes a node in the 4 MB reserve     |
| The cache's accounting              | 80 + 24 a capacity element; the class above B         |
| The stream                          | B in the meta block; nodes up to 32 + 16 (B + 1)      |
| The Lean models                     | SIS: none; 024-12's tree: a parameter M ≤ 62          |

* **The split rule.** A node that cannot take a transaction's klongs
  (its size, the new klongs and a TIME klong more than B) is replaced by
  its last version: two halves (a space split) if that version holds
  more than h klongs (B / 2 until format 7; 17 at 30 since 024-21), else
  one compacted copy (a time split). A node the same transaction made is
  split in place. So a node goes through cycles: live klongs L ≤ h after
  a time split, then appends until B (or until theta dead klongs, a
  compaction, since 024-23), then again.
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
* **Build** (from 2026-11-12, 00:41): branch `024-19-nsize` in
  `/Users/f/fl/bench/2026-11-11/nsize/clone`, rebased onto main
  `40aa66cb` (record format 7: 024-21's merges at the delete with
  8/17/17 at B = 30, 024-23's option 2 with theta 7 at 30, 024-25's
  CRC32C, 024-24's limits), one commit for sizes above 62 on workloads
  without deletes: `Klong.DELETE_BITS` 256 long with bits only for 0 to
  61, a delete bit beyond 61 refused with an exception (so a run that
  would need one stops: checked, set D at 126 stops at its first delete
  into a node of more than 62 klongs), and the array classes 254 and
  510 added; a second commit adds `-Dnsize.theta=T` (theta forced to T
  at every size, section 4.5). Without the property and at B ≤ 62 the
  build behaves as main. The runs of 2026-11-11 (main `1076235c`, no
  merges, no option 2, Fletcher-16) are kept in `out/pre-merges/`.
* **The thresholds at each size**, as format 7 scales them (`Dag`:
  v B / 30 by integer division; m at least 2; theta at least 1 from B =
  8; q, the room after a replacement, max(2, min(B / 2, B − h, B − c) −
  3); `Dag.roomAfterReplacement`):

  | B   | m  | h   | c   | theta | q   |
  |---|---|---|---|---|---|
  | 8   | 2  | 4   | 4   | 1     | 2   |
  | 14  | 3  | 7   | 7   | 3     | 4   |
  | 30  | 8  | 17  | 17  | 7     | 10  |
  | 62  | 16 | 35  | 35  | 14    | 24  |
  | 126 | 33 | 71  | 71  | 29    | 52  |
  | 254 | 67 | 143 | 143 | 59    | 108 |

  The merges run only at a delete, so at 126 and 254 (no deletes
  allowed) they never run, but option 2 does: an overwrite leaves a dead
  klong, so the compactions at theta 29 and 59 are in every run.
* **Sizes**: 8, 14, 30, 62, 126, 254 (2^k − 2, so that every size but 8
  fills its array class: the brief's "about 15, 60, 120, 250").
* **Database**: a `FileStream` on the internal SSD, the builder's
  defaults (sd 50 MB, cache indicator 200 MB, eviction on), a test clock
  of 1 ms a transaction; retain 1 s (1,000 transactions) unless "forever".
* **Keys**: k13 = `/k/%010d` (13 bytes, 2 segments: 024-03's keys); k24
  = `/scale/key/%013d` (24 bytes, 4 segments of 7, 7, 7 and 3, a shared
  prefix: 005-38's `key24`); mem = `"" + i` (MEM's keys; at 1M, at most
  6 digits, one segment).
* **Counts** at 1M keys: each JVM on one core
  (`-XX:ActiveProcessorCount=1`, SerialGC, 4 GB); a series of sizes one
  JVM after the other (`19-node-size/c1m.sh`, `c1m2.sh`), three series
  at a time in one slot (`c1m-all.sh 1`, `2`, `3`); outputs
  `19-node-size/out/c1m-SET-nB.txt`, tables by `python3 -I table.py
  c1m`. The probe's `DAG` line counts merges and option 2's
  compactions over the whole run (fill and updates).

### 4.2 Counts at 1M keys (format 7)

Run 2026-11-12, 00:42 to 00:54, on the rebased build (section 4.1). The
sets: k13 keys in random order and values of 100 bytes, 100 puts a
transaction, then 1M overwrites of random keys, 100 a transaction,
retain 1 s, unless the row says otherwise. "Bytes a put" is the stream's
growth a put of the second phase, over its last 80 percent (C has no
second phase: its fill). Sizes above 62 only where the set has no
deletes.

| Set | What differs                    | 8     | 14    | 30    | 62    | 126   | 254   |
|---|---|---|---|---|---|---|---|
| A   | (as above)                      | 772   | 476   | 400   | 386   | 384   | 390   |
| B   | k24 keys, values 0              | 720   | 369   | 309   | 303   | 294   | 292   |
| I   | values 0                        | 725   | 361   | 305   | 288   | 280   | 280   |
| F   | retain forever                  | 758   | 476   | 395   | 376   | 376   | 382   |
| E   | 1 overwrite a transaction, 200k | 1,558 | 504   | 550   | 586   | 632   | 626   |
| G   | sd 5 MB (10M keys' ratio)       | 1,139 | 895   | 976   | 1,165 | 1,752 | 2,852 |
| H   | sd 0.5 MB (100M keys' ratio)    | 1,450 | 1,184 | 1,307 | 1,715 | 2,624 | 4,308 |
| D   | queue: put at end, delete first | 354   | 277   | 259   | 259   | -     | -     |
| C   | fill in key order (the fill)    | 205   | 180   | 172   | 170   | 174   | 182   |

**How far each size is above the best of its row** (percent; MEM from
set M below, the mean of its two key shapes):

| Size | A  | B  | I  | F  | E   | G   | H   | D | C | MEM | worst |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 14   | 24 | 26 | 29 | 27 | 0   | 0   | 0   | 7 | 6 | 39  | 39    |
| 30   | 4  | 6  | 9  | 5  | 9   | 9   | 10  | 0 | 1 | 9   | 10    |
| 62   | 1  | 4  | 3  | 0  | 16  | 30  | 45  | 0 | 0 | 0   | 45    |
| 126  | 0  | 1  | 0  | 0  | 25  | 96  | 122 | - | 2 | 0   | 122   |
| 254  | 2  | 0  | 0  | 2  | 24  | 219 | 264 | - | 7 | 1   | 264   |

* **Two regimes, as section 3.1 predicted.** Where the keys are few
  against a window of puts (A, B, I, F at 1M keys and sd 50 MB: P = 50
  MB / about 400 bytes = 125,000 puts a window, every leaf touched
  about once a window) larger nodes win a little: 62 is within 4
  percent of the best, 30 within 4 to 9. Where they are many (G and H,
  1M keys at sd 5 and 0.5 MB, the ratio of 10M and 100M keys at 50 MB;
  E, one put a transaction, where a window holds fewer puts to absorb)
  small nodes win, and by more: 30 is 9 to 10 percent above 14, 62 is
  16 to 45 percent above it, 126 and 254 two to four times.
* **30 has the least worst case**: at most 10 percent above the best in
  every row and in MEM; 14 is up to 39 percent above (MEM, and 24 to
  29 in the hot rows), 62 up to 45 (H). That is the minimax, and the
  rows where 62 loses are the large databases that BergDB optimizes
  for first.
* **126 and 254** buy at most 1 to 4 percent in the hot rows and cost
  two to four times in the cold ones; with section 6's other reasons
  they are out.
* **8** is the worst everywhere, 1.1 to 2.8 times 30, worse than on
  2026-11-11 because of option 2's theta of 1 (section 4.5).
* **The deletes (D)**: 30 and 62 the same (259), with merges at every
  size (D's `DAG` line: 156,747 merges at 30, 103,955 at 62; 532,478 at
  8, one a delete).

**Set A in detail** ("path" the key nodes a get follows, "index" the
stored bytes of the current key nodes a key, after the fill and after
the overwrites; the bytes of 2026-11-11, before format 7, in brackets):

| B   | fill B/put | path | nodes   | index | overwrite B/put | nodes after | compactions |
|---|---|---|---|---|---|---|---|
| 8   | 603 (564)  | 16   | 486,827 | 53.8  | 772 (618)       | 716,615     | 1,102,899   |
| 14  | 415 (408)  | 10   | 226,683 | 37.9  | 476 (461)       | 290,420     | 243,840     |
| 30  | 340 (329)  | 7    | 81,336  | 27.3  | 400 (394)       | 96,741      | 113,822     |
| 62  | 319 (309)  | 6    | 37,369  | 24.0  | 386 (400)       | 43,933      | 69,344      |
| 126 | 310 (301)  | 5    | 17,952  | 22.7  | 384 (418)       | 20,972      | 34,617      |
| 254 | 309 (299)  | 4    | 8,757   | 22.2  | 390 (439)       | 9,980       | 17,179      |

* **What format 7 changed**: the fill costs 7 to 11 bytes a put more at
  every size (024-25's 4 bytes a value node, h = 17 B / 30 instead of B
  / 2); the overwrites cost more at 8 to 30 (+25, +3, +1.5 percent) and
  less from 62 (−3.5, −8, −11 percent): option 2's compaction keeps a
  large node's history short, so a large node written whole carries
  fewer dead klongs. The minimum moved from 30 to 62 to 126 in A; it is
  flat (386 to 400) from 30 to 254.
* Key nodes after the fill 9 percent fewer at 30 than on 2026-11-11
  (81,336 for 88,990): h = 17 leaves fuller nodes after a split.

**Set B** (k24, values 0) in detail, the same columns:

| B   | fill B/put | path | nodes   | index | overwrite B/put | nodes after | compactions |
|---|---|---|---|---|---|---|---|
| 8   | 487 (436)  | 16.9 | 526,715 | 56.3  | 720 (539)       | 727,133     | 1,327,075   |
| 14  | 229 (213)  | 11.2 | 219,484 | 35.8  | 369 (374)       | 290,447     | 337,196     |
| 30  | 153 (138)  | 8.0  | 81,911  | 26.0  | 309 (322)       | 97,275      | 163,232     |
| 62  | 128 (114)  | 7.0  | 36,671  | 22.8  | 303 (315)       | 44,857      | 88,984      |
| 126 | 120 (105)  | 6.0  | 17,718  | 22.4  | 294 (319)       | 20,484      | 42,115      |
| 254 | 118 (97)   | 6.0  | 9,043   | 21.7  | 292 (330)       | 9,736       | 19,688      |

**Set M, MEM** (bytes of heap a KV, no eviction; MEM's method; one run
each, MEM's noise is a few bytes; `out/c1m-M-nB.txt`; a fill only, so
format 7 changes nothing: within 1 byte of 2026-11-11):

| B   | MEM's keys `"" + i` | k24 keys |
|---|---|---|
| 8   | 252.6 | 239.5 |
| 14  | 164.3 | 162.2 |
| 30  | 129.1 | 126.0 |
| 62  | 119.4 | 114.8 |
| 126 | 117.7 | 117.0 |
| 254 | 123.3 | 113.3 |

MEM at 30 is 024-03's 129.6. It falls as predicted to 62 (−8 percent)
and is flat after: the arrays' 24 bytes an element of capacity, about
2.2 elements a live key at every B, are most of it.


### 4.3 Counts at 10M keys

Set A at 10M keys (k13, values 100, 100 puts a transaction, sd 50 MB,
the default cache of 200 MB with eviction, retain 1 s), then 2M
overwrites, then 200,000 warm gets, a restart, 200,000 cold gets and a
scan (`c10m.sh A "30 126" "14 62 254"`, one slot, 2026-11-12, 00:54 to
01:16; 30 and 14 rerun 01:10 to 01:27 by `c10m-r.sh`, their first runs
having lost their directory to another script's cleanup;
`out/c10m-A-nB.txt`). 254 was stopped in its overwrites at 01:16: its
stream had reached 16 GB with 15 GB left on the disk. "Loads" are the
cache's node loads a get, the value node's included (one a get).

| B   | fill B/put | path | nodes after fill | overwrite B/put | loads/get | index loads/get |
|---|---|---|---|---|---|---|
| 14  | 746        | 11   | 2,186,328        | 895             | 2.72      | 1.72            |
| 30  | 734        | 7    | 835,732          | 958             | 1.93      | 0.93            |
| 62  | 860        | 6    | 391,502          | 1,156           | 1.75      | 0.75            |
| 126 | 1,116      | 5    | 189,425          | 1,731           | 1.70      | 0.70            |
| 254 | 1,635      | 4    | 91,364           | (stopped)       | -         | -               |

* **Section 4.2's stand-in holds**: set G (1M keys at sd 5 MB) gave
  895, 976, 1,165, 1,752 at 14, 30, 62, 126; here 895, 958, 1,156,
  1,731, within 2 percent.
* **The fill is best at 30** (734); 62 costs 17 percent more, 126 52,
  254 2.2 times. **The overwrites are best at 14** (895), 30 7 percent
  above it, 62 29 percent (21 percent above 30), 126 93 percent.
* **Gets under the 200 MB cache**: the index loads a get fall with B,
  1.72, 0.93, 0.75 and 0.70 (cold, after the restart, the same within
  0.03): 62 saves one load in five against 30, 14 needs 85 percent
  more. Each load is one read of one node (at most 528 bytes at 30,
  1,040 at 62), so 62 reads about as many index bytes a get as 30.
* The times of these runs (µs a get, puts a second, the restart) are
  not comparable: two to three JVMs ran at a time, at 18 GB of heap on
  a 32 GB machine; section 4.4 has times.


### 4.4 Times at 1M keys

`t1m.sh` in a timing hold (both slots, 2026-11-12, 01:27:54 to
01:31:41): per size one JVM (G1, 4 GB heap) after the other, set A at
1M keys with 500,000 overwrites, then 1M gets of random keys twice, a
scan twice, a restart (close and start), 1M gets and a scan
(`out/t1m-nB.txt`, `uptime` before and after each). One run each. The
machine was not quiet: load 3.0 to 3.7 before each run from processes
outside the slots (`mediaanalysisd` at one core, a node gateway at half
of one), no Lean or lake process at the start; two `lean --run`
processes started at 01:30:31 (another session's), so **126 and 254
are possibly disturbed** (126 in its last seconds, 254 throughout).
µs a get and ns a key from the second pass; loads a get include the
value node.

| B | fill puts/s | overwrite puts/s | µs/get | loads/get | scan ns/key | restart ms | cold µs/get |
|---|---|---|---|---|---|---|---|
| 8   | 94,370  | 59,075  | 4.95 | 1.71 | 2,452 | 2,653 | 4.94 |
| 14  | 146,454 | 101,725 | 2.79 | 0.83 | 1,720 | 1,976 | 2.70 |
| 30  | 180,416 | 114,339 | 1.88 | 0.47 | 1,133 | 1,363 | 1.85 |
| 62  | 162,858 | 104,502 | 1.92 | 0.42 | 926   | 1,069 | 1.83 |
| 126 | 107,700 | 76,939  | 2.12 | 0.40 | 877   | 1,308 | 1.89 |
| 254 | 46,101  | 38,931  | 2.31 | 0.41 | 943   | 2,520 | 2.11 |

* **Puts are fastest at 30**: 62 is 10 percent slower to fill and 9 to
  overwrite, 14 19 and 11 percent; 126 and 254 lose 30 to 75 percent
  (a split or a compaction copies O(B) klongs, and a put scans its
  nodes' klongs, history included: section 3.2).
* **Gets are the same at 30 and 62** (1.88 and 1.92 µs warm, 1.85 and
  1.83 cold), as section 3.2 predicted (n (ln n − 1) = a / b gives B
  about 35 to 65); 14 is 48 percent slower, 8 2.6 times.
* **Scans and the restart favour 62**: 18 percent faster a key (fewer
  nodes a key), the restart 22 percent shorter (1.07 against 1.36 s:
  fewer, larger nodes rebuilt).
* At 10M keys only the loads were comparable (section 4.3): 62 one
  index load in five fewer than 30 under the 200 MB cache.


### 4.5 Option 2's theta at other sizes

Format 7 scales theta as the thresholds, 7 B / 30 by integer division,
at least 1 (024-23, OD2; open as its QO2): 1 at 8, 3 at 14, 14 at 62.
The measuring build's `-Dnsize.theta=T` forces it (0: option 2 off);
sets A and E at 1M (`c1m-theta.sh`, 2026-11-12, 00:54 to 00:58,
`out/c1m-SET-nB-thT.txt`). Bytes a put of the overwrites, and option
2's compactions in the run:

| B  | theta | A: B/put | A: compactions | E: B/put | E: compactions |
|---|---|---|---|---|---|
| 8  | 0     | 619      | 0              | 1,291    | 0              |
| 8  | 1 (*) | 772      | 1,102,899      | 1,558    | 704,338        |
| 8  | 2     | 628      | 83,279         | 1,317    | 50,697         |
| 8  | 3     | 619      | 0              | 1,291    | 0              |
| 14 | 0     | 466      | 0              | 508      | 0              |
| 14 | 3 (*) | 476      | 243,840        | 504      | 92,054         |
| 14 | 7     | 466      | 0              | 508      | 0              |
| 30 | 0     | 407      | 0              | 536      | 0              |
| 30 | 7 (*) | 400      | 113,822        | 550      | 44,869         |
| 62 | 0     | 396      | 0              | 594      | 0              |
| 62 | 7     | 430      | 191,828        | 593      | 80,363         |
| 62 | 14 (*)| 386      | 69,344         | 586      | 26,726         |

(*) format 7's value.

* **theta 1 at 8 costs 25 percent** (A) and 21 percent (E) for nothing:
  a compaction every second dead klong, a node rewritten about as often
  as it is written. theta 2 costs 1.4 to 2 percent; 3 never compacts at
  8 (a node of at most 8 klongs is full by its size first).
* **At 14, 30 and 62 format 7's theta is within 2 percent of off** in
  both sets, and at 30 and 62 it saves 1.7 and 2.5 percent in A; at 62
  theta 7 would cost 8 percent: theta must scale with B, as built.
* So the scaling is right from 14 up; at 8 the "at least 1" is too low.
  Rounding 7 B / 30 to the nearest (2 at 8, 3 at 14, 7 at 30, 14 at 62)
  or "at least 2" gives 2 at 8 and changes nothing else. B = 8 is a
  test size (the Core tests' small trees), so the cost is the tests'
  run time and the fidelity of their trees, not a user's; but every
  conformance set and the fuzz run at 8 (section 8, Q4).


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
  thresholds, which are formulas in B since 024-21 (v B / 30 by integer
  division from 8/17/17 and theta 7, m at least 2, theta at least 1:
  section 4.1's table; 024-14's alternative m = B / 4 + 1, h = c = 2m +
  1 gives 3/7/7 at 8, where a time split would keep 7 of 8 klongs);
  024-14's QT2 and 024-23's QO2 leave them open for B other than 30; 024-17's height
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

**B = 30 stays the default, and the only size of the Pub API, in
2026.5.** It is not the best size for any one workload, but it is
never far from the best, and the sizes that beat it in one regime lose
by more in the other:

* **Bytes a put, every set** (section 4.2): 30 is at most 10 percent
  above the best size of each set at 1M keys, including the stand-ins
  for 10M and 100M keys (G, H) and one put a transaction (E). 62 is at
  most 4 percent above the best where a window of puts covers the keys
  (A, B, I, F), and 30 to 45 percent above where it does not (G, H;
  at 10M keys, section 4.3: 29 percent above 14, 21 above 30). 14 is
  the best in G, H and E by 9 to 10 percent and 24 to 29 percent worse
  in A, B, I, F. 024-04's aim
  and BergDB's rule "large databases and worst cases first" weigh the
  cold rows (G, H, 10M) first: there 30 against 62 saves 16 to 24
  percent, and 14 against 30 saves 9 to 10.
* **Heap (MEM)**: 62 saves 8 percent (119 against 129 bytes a KV; 115
  against 126 with k24), 14 costs 27 percent. MEM is tracked, and 8
  percent is the one clear gain of 62; it does not pay for 16 to 45
  percent more bytes a put at scale.
* **Times** (section 4.4, 1M keys, one run each): puts are fastest at
  30 (62 9 to 10 percent slower, 14 11 to 19); gets the same at 30 and
  62 (1.9 µs), 48 percent slower at 14; scans 18 percent faster and the
  restart 22 percent shorter at 62. At 10M keys under the 200 MB cache
  62 needs one index load in five fewer than 30 (section 4.3).
* **Bounds** (024-17, 024-24): the release limits' worst transaction
  (`ReleaseFits`, `Bound.lean`) takes 0.43 of the record limit at 30,
  0.66 at 62 (section 2.3: a node of 32 + 16 (B + 2) bytes, H 21 or
  16); at 126 and 254 it would not fit (1.08 and 1.87 of it, by the
  same formula), so sizes above 62 need smaller limits as well as a
  new delete encoding (section 2.2). The memory of one path, which a
  small device pays (option e), is about 7 × 528 bytes at 30 and 6 ×
  1,040 at 62 (stored, at most B + 1 klongs).
* **What is settled at 30**: the merge thresholds 8/17/17 (024-14,
  measured and thrash-checked at 30), theta 7 (024-18, 024-23), the
  Lean model's checks against Java's traces (024-12, 024-22) and the
  tests' sizes all have 30 as their reference point. A change of the
  default would reopen 024-14's measurements at the new size for a gain
  that is a few percent in one regime and a loss in the other.
* **Above 62: no.** Up to 4 percent in the hot rows, two to four times
  the bytes a put in the cold rows, a format change for the delete
  bitmap and the limits; 024-20's compact form scales the curve and
  hardly moves its minimum (section 7). 62 stays the hard maximum.

**B stays a property of the database (option b), as it is**: set when a
database is made, by the Core API only, from the four sizes 8, 14, 30
and 62, held in the meta block (`u16` at 44), with format 7's thresholds
and theta as functions of B (v B / 30, section 4.1). Not one constant
(option a), because the tests need their small trees (B = 8: five levels
and more from a few hundred keys) and the cost of (b) is already paid:
the field, the formulas, the conformance sets at the four sizes, the
Lean tree model's parameter M ≤ 62, `ReleaseFits` at the four sizes.
Two changes to (b), both small, both Frans's (section 8):

* **theta at 8 at least 2**, not 1 (section 4.5: theta 1 costs 25
  percent at 8 for nothing; 2 costs 1 to 2). The tests' size, not a
  user's; but it is a rule of format 7, so it is settled now or never.
* **The start takes B from the meta block** (024-02, Q19) instead of
  being told it and refusing another: a database describes itself, and
  a Pub API user can open a database that the Core API made at 14 or
  62. An API change, no byte change; it may wait for 2026.6.

No database classes (option e) in 2026.5; if they come, the data here
says what each would take: 30 for M, 14 or 30 for L (100M keys and more
at a fixed sd: section 4.2's H and 4.3), a small B for S.


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

**Decided, Q1: the node size of 2026.5 is 30** (Frans, 2026-11-12,
07:26, to the coordinator's summary "keep 30, theta at least 2, 62 the
maximum": "OK, good. Let's keep 30. Document this."). B = 30 stays the
default and the Pub API's size, on this study's numbers (section 6): the
only size within 10 % of the best in every set and in MEM. **Decided, Q4 and Q6** (Frans, 2026-11-12,
07:36, "Yes I confirm", to the coordinator's question "theta at least 2,
and 62 the maximum?"): the floor of theta is 2 (2 at B = 8), and 62 is
the largest node size; made in 024-27. Q2, Q3 and Q5 are open, each with
its recommendation below.

**Decided, Q2 and Q3** (Frans, 2026-11-13, 08:54: "Q2. Yes as
recommended." and "Q3, as built."): B stays a property of the database
(option b: 8, 14, 30, 62 by the Core API, in the meta block, the
thresholds and theta functions of B), and format 7's thresholds at the
other sizes are v B / 30 by integer division, m at least 2 (2/4/4 at 8,
3/7/7 at 14, 16/35/35 at 62). Frans asked whether B can change while a
database runs; the coordinator's answer: no, it is set once, when the
database is made; a start with another size is refused
(`Db.refuseOtherNodeSize`), and another size means copying the KVs into
a new database. Q5 (2026.6) lets a start take B from the meta block
instead of repeating it.

Cite as "024-19, Q1". Each with a recommendation; none blocks other
work, as main already behaves as recommended except in Q4 and Q5.

* **Q1. The node size of 2026.5.** Keep B = 30 as the default and the
  Pub API's only size? Recommended: **yes** (section 6: within 10
  percent of the best in every measured workload; 62 saves 8 percent
  heap and up to 4 percent bytes on small or hot databases but costs 16
  to 45 percent bytes a put at 10M to 100M keys' ratio).
* **Q2. One constant or a property of the database.** Keep B a property
  of the database (option b): 8, 14, 30, 62 by the Core API, held in
  the meta block, the thresholds and theta functions of B? Recommended:
  **yes**, as built; option a would need a test-only size anyway.
* **Q3. The thresholds at other sizes (024-14's QT2).** Make "v B / 30
  by integer division, m at least 2" format 7's rule for 8, 14 and 62
  (2/4/4, 3/7/7, 16/35/35), as built? Recommended: **yes**. Set D (put
  and delete, merges at every size) costs the same bytes at 30 and 62
  (259), and the fuzz ran 8 and 14 (024-21).
* **Q4. theta at 8 (024-23's QO2).** Raise the floor from 1 to 2 (2 at
  8; 3, 7 and 14 unchanged at 14, 30, 62)? Recommended: **yes**, in
  2026.5, while format 7 is unreleased: theta 1 costs 25 percent of the
  bytes a put at 8 (21 with one put a transaction) and makes a
  compaction every second dead klong; theta 2 costs 1 to 2 percent
  (section 4.5). It changes a rule of format 7 at B = 8 only (`Dag.theta`,
  the Lean model's `Params.theta`) and one expected value of a test
  (`DeadKlongTester.testTheta`: 1 becomes 2 at 8).
* **Q5. The node size read from the meta block (024-02's Q19).** Let a
  start take B from the meta block, with the builder's setters only for
  a new database? Recommended: **yes, but in 2026.6** with the stable
  stream format: no byte changes, and 2026.5's aim is the algorithms.
* **Q6. Sizes above 62.** Close them for good: 62 the maximum, written
  into the specification (024-02), and 024-20's encoding free to keep a
  62-index delete bitmap and an n field of 6 bits? Recommended: **yes**
  (section 6: no gain in the hot regime worth a delete encoding and
  smaller limits, and two to four times the bytes in the cold one).


## 9. Not measured

* **Sizes above 62 with deletes**: the measuring build refuses a delete
  bit beyond 61, so the queue (set D) and every delete ran at B ≤ 62
  only; so 024-21's merges ran at 8 to 62 (set D) and never above 62.
* **The thresholds at 62 under thrash**: 024-14's thrash rules and
  UnlinkFuzz were run at 8, 14 and 30 (024-14, 024-21), not at 62;
  set D at 62 is the only workload with merges at 62 here.
* **10M keys**: set A only (section 4.3), not B; MEM at 10M not rerun
  (024-08 has 30).
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

2026-11-12, 01:34, by the agent "nsize2" of coord-1111 (resumed at
00:40). **Done**: every point of the brief. No run is running, no slot
is held, the data directory `/Users/f/fl/bench/2026-11-11/nsize/data`
is empty. Nothing committed in the main tree; the coordinator commits
this file and `19-node-size/`.

* **Ran**: the build rebased onto main `40aa66cb` and checked (the
  probe on format 7; set D at 126 refused at its first delete bit
  beyond 61; at ≤ 62 deletes, merges and option 2 run); 1M sets A to I
  and M (section 4.2), theta at 8, 14, 30, 62 (section 4.5), set A at
  10M (section 4.3; 254 stopped in its overwrites for disk space, 15 GB
  left), the timing hold (section 4.4; 126 and 254 possibly disturbed
  by another session's `lean --run`, started 01:30:31). Sections 1, 6
  and 8 written; 2.3, 5 and 9 updated for format 7.
* **Recommendation**: B = 30 for 2026.5; B a property of the database
  as built; theta at least 2 (B = 8); 62 the maximum. **Questions**:
  Q1 to Q6 (section 8); Q4 needs a changed expected value
  (`DeadKlongTester.testTheta`, 1 to 2 at 8) and Lean's `Params.theta`.
* **Build**: branch `024-19-nsize` in
  `/Users/f/fl/bench/2026-11-11/nsize/clone`, head `db0685a2`, two
  commits over main `40aa66cb`: `5d25dba7` (delete bits, array classes
  254 and 510) and `db0685a2` (`-Dnsize.theta=T`); a measuring build,
  not for main. Built (`java/build/bergdb.jar`); the probe
  (`19-node-size/NS.java`, now with a `DAG` line of merges and
  compactions) compiled to `/Users/f/fl/bench/2026-11-11/nsize/cls2`
  (`cls`, the older compile, removed; `c1m.sh` uses `cls2`).
* **Scripts** (`19-node-size/`): `c1m.sh`, `c1m2.sh` (one series, one
  core), `c1m-all.sh 1|2|3` (three series in one slot), `c1m-theta.sh`
  (section 4.5, one slot), `c10m.sh` and `c10m-r.sh` (10M, one slot;
  `-r` uses its own directories, to run beside it), `t1m.sh` (timing
  hold), `table.py` (`python3 -I table.py c1m|c10m [SETS]`). Outputs in
  `out/`; the runs of 2026-11-11 (before format 7) in
  `out/pre-merges/`. A script removes only its own data directories
  (`c1m-theta.sh`'s first version removed all of `data/` and took two
  10M runs with it; fixed, both rerun).
* **To continue**, if Frans wants more: set B at 10M (`c10m.sh B "30"
  "62"`, about 15 minutes, 10 GB of disk each); 126 and 254 retimed on
  a quiet machine; the thresholds at 62 under 024-14's thrash rules and
  UnlinkFuzz (section 9); and, after 024-20, section 3.1's model rerun
  with the compact form's bytes (section 7).

2026-11-13. Status set after the release (coord-1113).
