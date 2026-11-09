# 006-19 Write amplification at large sizes

Created 2026-11-09 by Frans Lundberg. Status: open.

Where the bytes of a put go at 1M to 100M keys, how the cost grows with
the number of keys and the startup distance, how it compares with LSM
trees, B-trees and LMDB, the levers and their costs, and what to measure
next. A design study: no code of `java/` changed; two short checks on F53.


## 1. The answer in short

* **The index is most of it.** At 10M keys with uniform random updates of
  24-byte keys and 8-byte values, today's code writes 867 bytes of stream a
  put at the default startup distance of 50 MB: the value node is 68 of
  them, the index nodes and their got-dirty entries the rest. The value is
  written once. Checksums take no bytes of their own, meta blocks 0.06
  percent, a record's header 37 bytes a transaction.
* **The cost is a function of sd/K.** The index writes a put depend on the
  keys K and the startup distance sd only through sd/K, the window per key
  (section 4.1). Checked today: 1M keys at 5 MB wrote 854 bytes a put,
  against 867 at 10M keys and 50 MB. So 100M keys at 500 MB cost what 10M
  cost at 50 MB. At a fixed sd, a tenfold growth of K adds up to one and
  a half node writes (400 to 650 bytes) a put, a logarithmic growth like
  an LSM tree's.
* **Against others.** Over the user's bytes, BergDB writes 6 to 43 times
  for 32-byte KVs (10M to 100M keys, 1000 to 50 MB), 2.5 to 12 times for
  100-byte values and 1.3 to 2.4 times for 1 KB values; reclaim adds at
  most a third. A leveled LSM tree writes 10 to 33 times whatever the
  value size; a B-tree writes a page of 8 to 16 KB for a cold row; LMDB a
  path of 4 KB pages a commit. BergDB is in the LSM's range for tiny
  values and far below it for medium and large ones, as its values are
  separate from the index (section 5).
* **The levers.** Without a format change: the startup distance (it buys
  bytes with startup time and pinned memory, one for one), and the take's
  pacing (up to about 20 percent at the same sd). Batching does not help.
  With a format change, for Frans: a compact key node encoding (about 35
  to 40 percent fewer index bytes, estimated, no change to reads) and
  delta writes of key nodes (2 to 3 times fewer, estimated, with chains to
  read). Section 6.
* **Measure first** (section 7): M1, a probe that prices the compact and
  the delta encodings on the nodes a run really writes; then M2, the
  scale law at 10M keys standing for 100M. **The lever that looks best**:
  the compact encoding, as the one that cuts bytes at the same startup
  time without a new read path (section 8).

A correction: 006-18-01, section 3, cites 681, 373 and 180 bytes a put
at 50, 200 and 1000 MB (from 006-08, section 6.4, and 005-38). Those are
the take before 2026-10-28.
Today's paced take (007-03, step 3) writes 867, 524 and 190 in the same
runs (007-07, section 10).


## 2. Sources and terms

* A put: one key and its value in a transaction of 1,000 puts, uniform
  random updates of loaded keys, steady state, unless said otherwise.
  Bytes a put: the stream's growth over the puts. WA: bytes a put over
  the user's key and value bytes (32 for 24-byte keys and 8-byte values).
* sd: the startup distance; K: the number of keys; the take: `TransSeq.take`,
  which writes the dirty index nodes (levels.md, section 5).
* The keys of the measurements: WriteBench's `key24`, 24 bytes, cut into 4
  segments of 7, 7, 7 and 3 bytes; segment-3 trees of 1,000 keys each, a
  segment-2 tree above them (005-38, node-size draft, section 9).
* Measurements used: 005-38 (WriteBench; its report, sections 2 to 7;
  the node-size draft and its model, sections 3 and 5 to 7); 007-06,
  sections 1 and 4; 007-07, sections 10 to 12 (the paced take at 10M and
  50M keys); 011-04, "Level 3 cost" and "Where the bytes go (W4)"; 007-05,
  the startup time against sd; 006-16 (SS); 006-08, section 6.4.
* SS (006-16) is 1.51 for Props's four scenarios: 100 MB of new KVs of
  100 or 1,000 bytes into a small database. It is a load at a small size,
  not updates at a large one, and says little about this question.


## 3. Where the bytes of a put go

### 3.1 The formats

From the code (`StoredValueNode`, `StoredKeyNode`, `StoredTopNode`,
`StoredTrans`; doc-files/stream-format.txt):

* **Value node**: 28 bytes, the value, and 8 bytes for each segment of up
  to 7 key bytes, padded to 4. The 28: a header word (size 4, type 1,
  version 1, checksum 2), the node id (8), the offset in the record (4),
  the value's size (4) and the key's size (4). A 24-byte key with an
  8-byte value is 68 bytes; with 100 bytes, 160; with 1,000 bytes, 1,060.
  It is written once per put. A delete writes a value node without a
  value (56 bytes here).
* **Key node**: 32 bytes and 16 for each klong. The 32: the header word
  (with the checksum), the previous version's position (8), the leaf flag
  and count (8) and the id (8); then each klong (8) and its reference (8).
  At node size 30 a node is at most 512 bytes. A key node is a fat node:
  it keeps its history (TIME klongs, replaced keys) until it is full and
  is replaced, and every write writes the whole node. A TIME or
  delete-bitmap klong has a reference too, `Spos.NULL`: 8 bytes that name
  nothing.
* **Top node**: 40 bytes and 16 a pointer; nearly never written in these
  runs (0.000 a put).
* **Record**: a 32-byte header (size and format, time, startup pos, top
  pos), the nodes, the got-dirty list (4 bytes, then 16 for each node that
  got dirty in the transaction: its id and position) and a last byte.
* **Meta block**: 128 bytes each 200,000 bytes of stream, 0.064 percent.
* **Checksums**: each node's Fletcher-16 is in its header word: no bytes
  of their own.

A written value leaf has about 19.1 klongs (node-size draft, section 5,
5M keys, updates): 5.1 TIME, 11.4 live keys, 2.6 replaced. Its 338 bytes
are the header (32), the TIME klongs (82, of which 41 are empty
references), the live keys (182) and the history (42).

### 3.2 The index: path copying a window, not a transaction

A put makes every node on its path dirty: in `key24`, a value leaf, the
two inner nodes of its segment-3 tree (its root among them), and the
nodes above in segments 2 to 0. A dirty node is not written by its
transaction. It stays in D until its transaction is about sd behind the
end of the stream, and the take then writes it whole; puts that reach it
in between are absorbed. A written node whose child is still dirty
stays dirty and is written again later (the still-dirty test), and a
node the take moves makes its parent dirty in the writing record's own
transaction (007-06, section 1). So a put costs about one node write on
each level whose nodes are more than the puts in a window, and a
fraction on the levels above: the path is copied once a window, not once
a transaction.

The startup section itself is never rewritten: its cost is this
deferral, which ends when the take writes D's nodes. The section's other
bytes (meta blocks, `setStartupDistance`'s records) are noise.

### 3.3 The parts, measured

The last window of three runs (bytes a put; a node write × its bytes):

| Part             | 50M keys, 200 MB, 8 B | 1M keys, 5 MB, 8 B | 1M keys, 50 MB, 100 B |
|------------------|-----------------------|--------------------|-----------------------|
| Value node       | 68                    | 68                 | 160                   |
| Value leaves     | 0.99 × 342            | 0.95 × 360         | 0.52 × 376            |
| Inner, height 1  | 0.87 × 357            | 0.84 × 364         | 0.18 × 439            |
| Inner, height 2  | 0.22 × 436            | 0.26 × 392         | 0.03 × 468            |
| Segment-2 leaves | 0.04 × 416            | 0.05 × 440         | 0.00                  |
| Got-dirty list   | 34                    | 34                 | 12                    |
| Rest of record   | 1                     | 1                  | 0                     |
| Total            | 865                   | 872                | 458                   |

The first is 006-10's run for 007-07, section 11 (`m50-upd-sd200.txt` in
`/Users/f/fl/bench/006-10/r50/out/`); the other two are today's checks
(section 7.1). In the first two, 92 percent of the stream is index.

### 3.4 Reclaim

With a finite retention R, reclaim moves live data forward before it cuts
the front (levels.md, section 6). An iteration starts when the stream has
grown by 2 sd and R/4 has passed. Its steps scan the keys in order and
rewrite each live value stored before the cut point pCut, making the
index nodes of the range dirty. A step runs only while the bytes charged
(values rewritten and index nodes made dirty) are below f = 0.25 of the
stream's growth since the iteration began.

* So reclaim's share of the stream is held near f, at most about f/(1-f)
  = a third more than the user's records. Measured at small sizes: 26 to
  38 percent of all writes (011-04, W4, 10 MB of live data, 2 MB sd).
* An iteration rewrites at most the live data once: K × (V + about 30
  bytes), V the value node, the 30 the share of a leaf write in a
  sequential scan (a written leaf of 360 bytes holds about 13 live keys).
  Only keys not updated since pCut are rewritten.
* Extra bytes a put: about min(B × f/(1-f), r × K × (V + 30) / U), with B
  the user's bytes a put, r the share of keys not updated since pCut and U
  the puts between iterations (at least 2 sd of growth, and R/4).
* At large K an iteration is long: 100M keys of 100-byte values are about
  19 GB to rewrite, so an iteration needs about 76 GB of growth at f =
  0.25. Unless R/4 holds that much, reclaim runs at its cap. It is a
  bounded third in writes; its larger cost at large sizes is space: the
  kept stream is R's stream plus one or two iterations (011-04, "Level 3
  cost"). The default retention is forever, without reclaim.
* Reclaim cuts the front only, so it moves cold data forward every
  iteration, also data that never changes. A log-structured store whose
  cleaner picks segments by their live share and age (LFS's cost-benefit
  cleaning, Rosenblum and Ousterhout, SOSP 1991) cleans cold, well-filled
  segments seldom.

Not measured at large K; M4 in section 7.

### 3.5 Bytes a put at 1M to 100M keys

8-byte values (WA over 32 user bytes in parentheses). Measured with
today's take where there is a measurement (007-07, sections 10 and 11),
else the model of section 4 (at 1M keys the take before 2026-10-28
measured 230 and 147 at 50 and 200 MB, its model 221 and 138):

| Keys | sd 50 MB    | sd 200 MB   | sd 1000 MB | Source                       |
|------|-------------|-------------|------------|------------------------------|
| 1M   | 268 (8.4×)  | 148 (4.6×)  | 123 (3.8×) | model                        |
| 10M  | 867 (27×)   | 524 (16×)   | 190 (5.9×) | measured, 007-07, section 10 |
| 50M  | 1,244 (39×) | 851 (27×)   | 460 (14×)  | measured, 007-07, section 11 |
| 100M | 1,383 (43×) | 1,106 (35×) | 658 (21×)  | model                        |

100-byte and 1,000-byte values, the model (WA over 124 and 1,024 user
bytes); measured today: 431 at 1M keys, 100 bytes, 50 MB (model 401):

| Value  | Keys | sd 50 MB     | sd 200 MB    | sd 1000 MB   |
|--------|------|--------------|--------------|--------------|
| 100 B  | 1M   | 401 (3.2×)   | 261 (2.1×)   | 219 (1.8×)   |
| 100 B  | 10M  | 987 (8.0×)   | 581 (4.7×)   | 314 (2.5×)   |
| 100 B  | 100M | 1,489 (12×)  | 1,218 (9.8×) | 792 (6.4×)   |
| 1 KB   | 1M   | 1,485 (1.5×) | 1,277 (1.2×) | 1,155 (1.1×) |
| 1 KB   | 10M  | 2,035 (2.0×) | 1,709 (1.7×) | 1,365 (1.3×) |
| 1 KB   | 100M | 2,494 (2.4×) | 2,226 (2.2×) | 1,876 (1.8×) |

Reclaim, when R is finite, adds up to a third to each (section 3.4).


## 4. How it grows

### 4.1 The model

005-38's model (node-size draft, section 3), with a window of 0.7 sd for
today's take:

    B   = V + 1 + Σ over node classes c of (b_c + 16) × w_c
    P   = 0.7 × sd / B                  puts in a window
    x_c = P / (n_c × K)                 touches of a node of class c a window
    w   = 1/(1 + x) + 0.13 (1 - e^-x)   value leaves (the 0.13: dead versions)
    w   = 1/(x + e^-x)                  nodes above them (the still-dirty test)

V is the value node, b_c the bytes of a written node of the class (360,
366, 380 and 420 from the leaves up), 16 its got-dirty entry, n_c the
nodes a key of the class (0.0733 for value leaves, then 0.0067, 0.001,
9.2e-5 and about a tenth for each level up, from 005-38's tree of 1M
keys). B is solved by iteration. The script is
`/Users/f/fl/bench/2026-11-09/a19/wamodel.py`.

The 0.7 is a fit: with a window of sd the model matches the take before
2026-10-28 (005-38's runs, within about 25 percent), and with 0.7 sd it
matches today's paced take within 15 percent at 10M and 50M keys (1.00,
0.85, 0.99 at 10M and 1.01, 1.09, 0.96 at 50M, model over measured). Why
the paced take acts as a shorter window is not known. One sign: at 50M
keys and 200 MB its inner nodes of height 1 are written 0.87 times a put,
against 0.55 with the old take, which also held a longer section (mean
1.24 sd, up to 2.3 sd).

### 4.2 What it says

1. **The scale law.** K and sd enter only as P / (n_c K), and P is sd/B,
   so B depends on sd/K alone (for a key shape, a value size and a node
   size). Checked: 854 bytes a put at 1M keys and 5 MB, 867 at 10M keys
   and 50 MB. The sd a key for a cost, 8-byte values: about 5 bytes a key
   for 870 bytes a put, 20 for 450, 100 for 190. At 100M keys: 500 MB, 2
   GB and 10 GB.
2. **Growth with K at a fixed sd**: one node write (about 380 bytes) a put
   for each level whose node count exceeds P, a fraction for the next
   level up. Each tenfold growth of K/sd turns about one more level cold,
   400 to 650 bytes more a put in the model's middle range and less at
   its ends, until every level of the segment-3 trees is cold (three at
   node size 30).
   From 1M to 10M to 100M keys: 268, 869 and 1,383 at 50 MB; 123, 187 and
   658 at 1000 MB. The shape is an LSM tree's, log(K / window), but each
   step costs a node, not a rewrite of the data.
3. **Growth with sd**: the same law read the other way, with diminishing
   returns. As sd/K grows past about 100 bytes a key, only the value
   leaves remain, and B falls towards V plus the dead leaf versions, about
   120 bytes for 8-byte values.
4. **The value size**: the index costs about the same bytes for the same
   P; at a fixed sd larger values mean fewer puts in a window, so more
   index bytes a put (1M keys, 50 MB: 199, 240 and 424 bytes of index for
   8, 100 and 1,000-byte values in the model; about 270 measured for 100
   bytes), but a lower WA.
5. **The transaction size does not matter**: 755, 754 and 753 bytes a key
   with 100, 1,000 and 10,000 puts a transaction (005-38, section 2); 873
   against 867 for single puts (007-07, section 11.1). The deferral is per
   window. A transaction's own overhead is its header, about 37 bytes.
6. **Key shape and skew**: sequential keys cost 90 bytes a put (005-38,
   section 2); random 24-byte keys add about 480 bytes a put whatever the
   sd, three one-key segment leaves a key (005-38, section 7); a hot set
   costs about half of uniform updates (011-04, W4: 312 against 662 bytes
   at a small size). Uniform updates of `key24` are the usual worst case,
   keys like `rnd24` a worse one.
7. **The prices of sd**: a warm start costs 62 to 104 ms a MB of section
   with small values at 10M to 50M keys (007-05, finding 1, measured with
   the take before 2026-10-28). Today's take holds the section at 1.0 to
   1.1 sd (007-07), so about 3 to 5 s at 50 MB, 12 to 21 s at 200 MB and
   a minute or more at 1000 MB. D, which eviction cannot touch, is about
   sd in stream bytes and 2 to 2.5 times that in the heap (node-size
   draft, section 6). To halve the bytes a put at 10M keys (867 to 524)
   takes 4 times the sd: a warm start of 12 to 21 s instead of 3 to 5,
   and D's nodes at most 448k (about 160 MB of stream) instead of 137k
   (about 50 MB). 007-05 put a 10 s warm start at up to about 75 MB at
   10M keys, counting a section of twice sd (the deadline's bound); with
   a section of about sd, as today's take holds it, about 140 MB.

So at 10M keys and more, with small values, bounded startup and few
bytes a put pull against each other, and sd only moves along that line.
A format lever moves the line: at the same P, the same startup work, it
cuts the bytes of each node write.


## 5. Against other engines

| Engine                 | Written for a small put                 | WA, small KVs | WA, 1 KB   |
|------------------------|-----------------------------------------|---------------|------------|
| BergDB, today          | value node, 0.3 to 3 node writes        | 6 to 43       | 1.3 to 2.4 |
| LSM, leveled (RocksDB) | WAL, then about 10 at each level        | 10 to 33      | 10 to 33   |
| B-tree, WAL (InnoDB)   | WAL record, a page of 8 to 16 KB, twice | 100s          | 10s        |
| LMDB, copy-on-write    | a path of 4 KB pages, free-page tree    | 100s          | 10s        |

* **LSM trees.** RocksDB's tuning guide, "Level Style Compaction",
  estimates the total write amplification of a leveled tree as about
  1 + 2 + 10 + 10 + 10 = 33 ([RocksDB Tuning Guide](https://github.com/facebook/rocksdb/wiki/RocksDB-Tuning-Guide));
  the size multiplier between levels is 10 in most of Facebook's
  deployments, and a larger one means more write amplification (Dong et
  al., "Optimizing Space Amplification in RocksDB", CIDR 2017, section
  3.1). WiscKey measured LevelDB at 3.1 for a 1 GB and 14 for a 100 GB
  database (16-byte keys, 1 KB values), and notes it can be over 50 (Lu et
  al., FAST 2016, section 2.3 and Figure 2). An LSM tree's WA is per byte,
  so the same for large values as for small ones, unless values are kept
  apart (WiscKey, RocksDB's BlobDB). BergDB keeps them apart by design: a
  value is written once, and only reclaim moves it, as WiscKey's value
  log is cleaned. Its index cost is per put and grows with log(K/window),
  as an LSM's grows with log(K/memtable).
* **B-tree with a WAL.** A row change is written to the log and later as
  a whole page; Facebook's InnoDB wrote a whole 8 KB page for a single row
  change, and twice with the double-write buffer, and the move to MyRocks
  cut the bytes written to flash by 75 percent (Matsunobu, Dong and Lee,
  "MyRocks", PVLDB 13(12), 2020, sections 2.1 and 2.2). The redo log's
  size plays the part of BergDB's sd: it bounds the recovery and lets
  writes to a hot page be absorbed. BergDB's unit of write is a node of
  about 360 bytes, not a page of 16 KB, so a cold write costs about 45
  times less.
* **LMDB.** Copy-on-write: each commit writes new copies of every page
  from the leaf to the root, about the tree's depth in pages, plus its
  free-page tree (H. Chu,
  ["Is LMDB a LevelDB killer?"](https://www.symas.com/post/is-lmdb-a-leveldb-killer),
  2013). "The minimum write amplification may be on the order of 8 pages
  for a trivial write", and that is also about the maximum (H. Chu on the
  openldap-technical list, 2015-05-05,
  [msg00033](https://openldap.org/lists/openldap-technical/201505/msg00033.html)).
  The copy is per commit, so batching helps LMDB much. BergDB copies the
  path once a window, so batching does not help it, and needs none.
* **Closest designs.** Berkeley DB Java Edition is a log-structured B+tree
  with a cleaner; it writes BIN-deltas, a bottom node's dirty entries only,
  instead of the whole node (its change logs, for example 6.4.x,
  [JE change log](https://docs.oracle.com/cd/E17277_02/html/changelog.html)).
  The Bw-tree prepends delta records to a page and consolidates them later
  (Levandoski, Lomet and Sengupta, ICDE 2013). Both are lever 6.6.

The table's ranges are orders of magnitude, from the sources' own
setups; no engine was run here.


## 6. The levers

Each with its gain, its cost and risk, and whether it changes the stream
format (Frans approves any change of it, 018-01's rule).

### 6.1 The startup distance (no format change)

* Gain: large and measured: 867, 524, 190 bytes a put at 50, 200, 1000 MB
  (10M keys). By the scale law, a default sd that grows with the database
  (for example 20 bytes a key, capped by a memory budget) keeps the cost
  from growing with K.
* Cost: startup time and pinned memory grow with sd one for one (section
  4.2, point 7); a 10 s warm start holds only up to about 75 to 140 MB at
  10M keys. Larger bursts after a decrease (007-07, section 11.2).
* Risk: low; sd is already stored in the stream and changeable at run
  time (005-53). A default that follows K is a policy: what it does at a
  start and on a shrinking database needs a design.

### 6.2 The take's pacing (no format change)

* Gain: the model says up to 10 to 20 percent at the same sd, if the
  paced take wrote as a window of sd instead of 0.7 sd (at 10M keys and
  200 MB: 443 against 364 in the model; 524 against 373 measured with the
  old take). Not known how much is recoverable.
* Cost: work on the take, whose bound is proved (T3_take holds for any
  share) and measured (007-06, 007-07); 007-07's evidence would be redone.
* Risk: medium; the take's bursts and the deadline were hard to get right.
* First: find why (M1's records give the still-dirty writes by level).

### 6.3 Larger transactions and batching (no format change)

* Gain: none for the index (section 4.2, point 5); a transaction's own
  overhead is about 37 bytes. Key locality within the database helps:
  sequential keys cost 90 bytes a put. Guidance for applications, not a
  change: keys that cluster what is written together.

### 6.4 Node fan-out (no format change)

* Gain: small. At 10M keys node 62 writes 771, 330 and 167 bytes a put
  at 50, 200 and 1000 MB against node 30's 681, 373 and 180: 7 to 12
  percent less at 200 and 1000 MB, 13 percent more at 50 MB (005-38,
  section 6, the take before 2026-10-28). Node 30 is within 8 percent of
  the best everywhere measured.
* Cost and risk: the node size is in the meta block since 005-50, so a
  database keeps its own; a new default changes MEM and the gets.
  Not worth it alone.

### 6.5 A compact key node encoding (format change)

* What: a key node format that drops the reference of TIME and
  delete-bitmap klongs (41 of a leaf's 338 bytes, 12 percent), writes
  references as variable-length offsets back from the record, and key
  klongs with their used bytes only. The node in memory stays as it is.
* Gain: estimated 35 to 40 percent fewer bytes a node; at the same P,
  that is the same share of the index bytes, about a third of the bytes a
  put at 10M keys and 50 MB. With the same sd instead, the model gives 487
  instead of 869 at 10M keys and 50 MB, and 638 instead of 1,106 at 100M
  keys and 200 MB (with nodes at 0.6 of their size). Also fewer bytes for
  a cold start and an evicted node's reload to read.
* Cost: encoding and decoding on every node write and read; key node
  format version 3; the C port (022) and the corrupt-stream set
  (022-01, step 4) follow. The Lean model is not touched (bytes as a
  function of the stream are argued, M10 of 011-11).
* Risk: medium. No new read path, no new invariant.

### 6.6 Delta writes of key nodes (format change)

* What: write only what changed since the node's last written version:
  the klongs added since and the references raised. A key node already
  names its previous version (prevPos), and its klongs are append-only
  until it is replaced, so a delta is natural here. A full version every
  k-th write, or when the delta passes a share of the node, bounds the
  chain (as Berkeley DB JE's BIN-deltas).
* Gain: estimated 2 to 3 times fewer index bytes in the cold regime: a
  leaf delta after one put is about 64 bytes against 360. With k = 4, the
  model gives 296 instead of 869 at 10M keys and 50 MB, 399 instead of
  1,106 at 100M keys and 200 MB; with 6.5 too, 191 and 259.
* Cost: a node read from the stream reads its chain: cold reads, an
  evicted node's reload, a cold start (already 46 s at 10M keys on s1,
  most of it reads). Rule R by node id and rule 4 by position must see a
  node's base; reclaim must not cut a base that a live delta needs; the
  Lean model's physical layer (lemma M, T1-L, CC) changes; the C port.
* Risk: high. A larger change of the design than any since handles (009).

### 6.7 Keeping hot paths in memory longer (no format change)

* D is that memory already, and the startup section bounds it: startup
  reruns the section to rebuild D, so a node cannot stay dirty longer than
  the section without being written. Longer means a larger sd (6.1).
* The exact still-dirty test (sis-model.md, section 11) would skip dead
  versions kept dirty by a hot child: at most 17 of 232 bytes a put at 1M
  keys and 50 MB, nearly nothing once the leaves are cold (node-size
  draft, section 7). It changes the records, not the format. Not worth it
  at large sizes.

### 6.8 Reclaim's policy (no format change, except the last)

* f: a lower f makes iterations longer; fewer bytes a put, more stream
  kept. The cap of a third holds whatever f's effect on space.
* Iterations no closer than R/4 already save writes for long retentions.
* A cleaner that leaves cold data in place (generations, or a cut that
  skips well-filled files) would stop the moves of data that never
  changes; it changes the stream's FIFO shape, Level 3's model and the
  format. A 017 topic, for space more than for writes.


## 7. Measurements

### 7.1 Today's checks

On F53, one JVM at a time, nice 19, bytes only (deterministic; the
machine was busy with other sessions' gates). WriteBench of 007-06 with a
value size option (`-Dwb.val`), in
`/Users/f/fl/bench/2026-11-09/a19/wb/`, on a copy of the main tree's
`java/build/bergdb.jar` of 08:45 (main at 1d1b6f3, today's paced take),
1,000 puts a transaction, 3M updates after the load:

| Run                      | Bytes a put | Model | Checks                                | Time |
|--------------------------|-------------|-------|---------------------------------------|------|
| 1M keys, 100 B, sd 50 MB | 431         | 401   | the value size in the model           | 30 s |
| 1M keys, 8 B, sd 5 MB    | 854         | 869   | the scale law: 10M at 50 MB wrote 867 | 67 s |

Outputs: `out/v100-sd50-1M.txt` and `out/v8-sd5-1M.txt`; `out/runs.txt`.

### 7.2 To run on a quiet F53, or any time (bytes only)

None needs a quiet machine, as only bytes are counted, but each takes a
core and 12 to 16 GB of memory for minutes and would disturb another
session's timings: run them when the coordinator gives F53 room, one at a
time. In order:

* **M1. Price the format levers** (a new probe, not written today, about
  150 lines in `/Users/f/fl/bench/2026-11-09/a19/`). A copy of WriteBench
  whose `transExecuted` hook computes, for each key node written, (a) its
  size in the compact encoding of 6.5 and (b) its size as a delta against
  its last written version (klongs added, references raised), keeping
  each node's klong count and references at its last write, and the
  still-dirty writes by level for 6.2. Runs at 10M keys, sd 50 and 200
  MB, 30M updates, about 8 minutes each. Gives 6.5's and 6.6's gains on
  real nodes before Frans is asked about a format change.
* **M2. The scale law for 100M keys**, 10M keys at 5, 20 and 100 MB for
  100M at 50, 200 and 1000 MB (about 8 to 12 minutes each):

      cd /Users/f/fl/bench/2026-11-09/a19/wb
      for sd in 5000000 20000000 100000000; do
        nice -n 10 java -Xms12g -Xmx12g -XX:+UseParallelGC -cp cls:bergdb.jar \
          -Dwb.keys=10000000 -Dwb.sd=$sd -Dwb.updates=30000000 \
          -Dwb.window=1000000 -Dwb.ring=1300000000 \
          bergdb.core.WriteBench > out/u-sd$((sd / 1000000))-10M.txt 2>&1
      done

  The model says 1,383, 1,106 and 658 bytes a put.
* **M3. Value sizes at 10M keys**, the same with `-Dwb.val=100` at sd
  50000000 and 200000000 (model 987 and 581), and with `-Dwb.val=1000
  -Dwb.keys=1000000 -Dwb.sd=5000000`, which by the scale law stands for
  1 KB values at 10M keys and 50 MB (model 2,035 for both).
* **M4. Reclaim at 10M keys, on disk**, with Perf (4-byte keys, 100-byte
  values) in a clone, as other sessions use the main tree. The suite is
  `/Users/f/fl/bench/2026-11-09/a19/wa.suite` (infinite and finite
  retention at 50 and 200 MB); its parameters are untried, so run it
  first with n=1000000:

      git clone -q /Users/f/fl/repos/bergdb /Users/f/fl/bench/2026-11-09/a19/clone
      cd /Users/f/fl/bench/2026-11-09/a19/clone
      JAVA_HOME=/opt/homebrew/opt/openjdk SUITE=/Users/f/fl/bench/2026-11-09/a19/wa.suite \
        RUNS=1 FORCE=1 java/stress/performance.sh reference a19-wa

  It reports `bytes_appended_per_put`, `rec.user_index_bytes_per_put`,
  `rec.step_bytes_per_put`, `se` and `kept_mb_max` (the timings of a
  FORCE=1 run are not a reference). It answers section 3.4 at a size
  where an iteration is long.
* **Later: 100M keys itself.** Not possible in memory on F53 (50M keys
  needed a 22 GB heap); it needs eviction on a FileStream and hours. The
  scale law (M2) stands in for it until a machine with more memory, or s1
  over a night.


## 8. Recommendation

1. Measure M1 first, then M2. M1 decides whether a format change is worth
   asking Frans for; M2 makes the 100M rows of section 3.5 measurements.
2. Now, without a format change: give sd as a function of K in the
   documentation (about 5 bytes a key keeps today's 870 bytes a put at
   any size, 20 bytes a key 450), with its price in startup time and D's
   memory; and find why today's take writes as a 0.7 sd window (6.2).
3. The lever that looks best: the compact key node encoding (6.5). It
   cuts the bytes of every index write at the same startup work, has no
   chain to read and no new invariant, and also makes cold starts and
   reloads read fewer bytes. Delta writes (6.6) give more, but with a new
   read path through the parts that were hardest to get right (Rule R,
   rule 4, reclaim's cuts); keep them for later, if 100M keys must run at
   a small sd.


## Log

2026-11-09. Created by the agent a19 for the coordinator coord-1109, at
Frans's word (12:40): the study from the code, the formats and the
measurements of 005-38, 007-05 to 007-07 and 011-04; the model of 005-38
fitted to today's take (`wamodel.py`); two short WriteBench checks on F53
(section 7.1); the measurements to make (section 7.2).
