# 026-01. A compact stored form of the index nodes: measured

Moved from 024-20 on 2026-11-12 (Frans, 07:39): the compact stored form
is for release 2026.6 (QC1).

Created 2026-11-11 by Frans Lundberg. Status: moved to release 2026.8
(032) on 2026-11-20 (Frans), its ID and file kept here; open there. The
measurements done 2026-11-12 (State); QC2 to QC5 are part of 026-12.
Postponed 2026-11-11, 11:50 (Frans: the merges at the delete first, the
stored form after that); resumed 2026-11-12, 01:34, on record format 7
(main `a8c3589a`).

Should an index node be stored more compactly in the stream, and how? A
study with measurements: the stored form today, byte for byte; where a
stream's bytes go, measured on streams of `main`; each candidate encoding
priced by re-encoding those streams offline; a recommendation. No product
code; the probe is in `01-compact-nodes/probe/`.

Frans, 2026-11-11, 11:24: "By the way, the node size of 30 is open for
discussion. And should it even be a fixed constant? And should an index
node be stored more compact in the stream? Big questions. But these are
important now when we want to settle the algos. Solid algorithms are the
aim." 11:31: "Node size is worth a separate study. Compact stored format
too." Why now: release 2026.5's aim is solid algorithms (024-04), the
stream format is to be stable in 2026.6 (026), a record format change is
allowed in 2026.5, and 2026.5 may refuse 2026.4's databases (Frans,
2026-11-11). The node size is 024-19's study; the dead klongs 024-18's;
section 7 says what each needs from the other. Asked by the day's
coordinator (coord-1111) at 11:32. Cite as "026-01, section 4" and the
questions as "026-01, QC1" (024-20 before the move).


## 1. In short

Resumed 2026-11-12, 01:34, on record format 7 (main `a8c3589a`: merges
at the delete, option 2 at theta 7, CRC32C, the limits); measured 01:36
to 02:45. Sections 3 to 8; State at the end.

* **Where the bytes go** (section 3): the index nodes are 11 percent of
  the stream in a sequential fill, 36 in a random fill and 57 in random
  overwrites at 1M keys, 72 to 78 percent in a random fill and the
  overwrites at 10M keys, 88 percent in the deletes. Today an overwrite at 10M keys (24-byte key,
  100-byte value, sd 50 MB) writes 896 bytes, 698 of them index.
* **Encoding C** (section 4): a key node's body as a tag byte a klong,
  key bytes not shared with the klong before, references relative to
  the record as varints, a compact header: 38 to 47 percent of today's
  index bytes in every workload (a round trip exact on 200,000 nodes).
  **Index bytes a put, today and in C**: sequential fill 20.9 and 8.8
  at 1M (28.2 and 11.9 at 10M); random fill 95.0 and 39.8 (479.0 and
  224.6); overwrites 233.4 and 101.9 (698.0 and 328.4); deletes 149.9
  and 61.2 (665.4 and 303.9); one put a transaction, overwrites, 257.3 and 114.4 (702.0
  and 329.2).
* **With a compact value node, record frame and top node** (V1, R1, T1)
  the stream is 19 to 20 percent smaller in a sequential fill, 29 to 43
  in a random one, 37 to 47 in the overwrites, 47 to 52 in the deletes.
* **Through the startup distance it is more** (5.2): sd counts stream
  bytes, so a compact section holds more transactions; measured, a
  compact stream at 50 MB writes 48 percent less than today's in the 1M
  overwrites and 53 percent less at 10M (section 4's offline figures:
  39 and 45), and a start reruns about 1.6 to 1.8 times the
  transactions.
* **It changes no algorithm** if the take, the limits and the Lean
  bounds keep counting a node at its nominal size, which encoding C
  never exceeds (a node that would not be shorter is written in format
  3): 5.1. Reclaim's charge is the exception to adjust.
* **Node size** (section 7, for 024-19): in C a written node is about 23
  bytes and 5 a time klong, 7.2 a key klong; no prefix sharing grows
  with B; 30 stays the minimax size and comes within about 4 percent of
  the best in every row (10 today).
* **CPU** (section 4, a timing hold): C writes a node in about 220 ns
  and reads it in 215, format 3 in 90 and 105 (CRC32C made the sum
  cheap, so the varints show); 1 to 3 percent of a put's time.
* **Recommendation** (section 6): encoding C with V1, R1 and T1 in
  release 2026.6 with the stable stream format, designed now; in 2026.5
  only the decisions that touch the algorithms (QC2: nominal accounting;
  B at most 62). Questions QC1 to QC5 (section 8).


## 2. The stored form today

From 024-02 (sections 8 to 13, the field tables) and the code of `main`
at `2105baa7` (`StoredTrans`, `StoredKeyNode`, `StoredTopNode`,
`StoredValueNode`, `NodeStream`, `KeyNode`); 012-02, sections 5, 6 and
8, for the writer's rules. Updated 2026-11-12 to record format 7 at
`a8c3589a`: 024-25's 12-byte node header with a CRC32C sum (node formats
3, 3 and 5); the merges (024-21) and option 2 (024-23) change what a run
writes, not the layout. Integers little-endian; a *pointer* is an
`i64` stream position, −1 for none (024-02, section 14.1).

### 2.1 The record

024-02, section 8.1. A record is a transaction's bytes, at a multiple of
8 in the stream, its size a multiple of 8:

| Part              | Bytes        | What                                          |
|---|---|---|
| header            | 32           | size `i32`, format `u8` + 3 zero, time, startupPos, topPos (`i64` each) |
| top nodes         | 48 + 16·h    | each (section 2.2)                            |
| key nodes         | 32 + 16·n    | each (section 2.3)                            |
| value nodes       | 32 + L + 8·k | each, padded to 4 (section 2.4)               |
| delete nodes      | 28 + 8·k     | each (section 2.4)                            |
| end marker        | 4            | an `i32` 0 where the next node's size would be |
| got-dirty count   | 4            | N                                             |
| got-dirty pairs   | 16·N         | (id `i64`, position `i64`) of each node that got dirty |
| padding           | 0 to 7       | zeros, so that the size is a multiple of 8    |
| last byte         | 1            | 10                                            |

The stream adds a 128-byte meta block at every multiple of 200,000 bytes
(0.064 %; 024-02, section 6), inside or between records. The startup
pos is the header's `startupPos`, 8 bytes in every record. There is no
checksum over the header or the got-dirty list (024-02, G12); each node
has its own (section 2.2). An empty record is 48 bytes.

### 2.2 The node header and the checksum

Every node begins with 12 bytes (024-02, section 9; 024-25, CD1): its
size (`i32`), its type (`u8`: 10 top, 20 key, 30 value, 40 delete), its
format (`u8`: 3, 3, 5), two zero bytes, and a CRC32C sum (`u32`) of the
node's other bytes. (Format 6 of 2026.4 had 8: a Fletcher-16 sum in
bytes 6 and 7.)

**The top node** (024-02, section 10): 48 + 16·h bytes: the header, 4
zero bytes, h (`u8`), a zero byte, the ordinal (48 bits), the id, the
root time, the root pointer, and h skip pointers each with its time (16
bytes a pair).
One is written with each new super root; in the runs of section 3 they
are below 0.1 byte a put.

### 2.3 The key node and its klongs

024-02, section 11.1. 32 + 16·n bytes, n the klongs:

| Off      | Bytes | Field                                                 |
|---|---|---|
| 0        | 12    | node header (size, type 20, format 3, 2 zero, CRC32C) |
| 12       | 4     | leaf flag (1 byte), n (2 bytes), 1 zero byte          |
| 16       | 8     | prevPos: the position of the version this one replaces |
| 24       | 8     | id (an odd number: the vpos the node got when made)   |
| 32 + 8i  | 8·n   | klong i                                               |
| 32+8n+8i | 8·n   | ref i: klong i's pointer; −1 for a time klong or a bitmap |

**A klong** is 8 bytes (024-02, section 11.2): a *time klong* (a 56-bit
time), a *key klong* (up to 7 bytes of one key segment and the segment's
length), or a *delete bitmap* (62 bits, one a klong index). Each has a
ref of 8 bytes: the child's or the value's position for a key klong; −1,
which names nothing, for the other two.

**A key's bytes** in the index: a key of len bytes is k = len / 7 + 1
segments of 7 bytes (the last 0 to 6; 024-02, section 13). Each segment
is one level of the tree of trees: the segment leaf of segment j holds a
key klong whose 7 bytes are the key's bytes 7j to 7j + 6 and whose ref
is the root of segment j + 1's tree (a klong of length 7), or the value
(length 0 to 6). So a 24-byte key is 4 segment trees deep, and keys that
share a 7-byte segment share the klong of it: the tree already shares
whole 7-byte segments between keys, once, at the level above. What is
left to share is within a node: the bytes of neighbouring klongs of the
same segment (keys `...0000123` and `...0000124` share 6 of 7 bytes).

**A pointer** is 8 bytes everywhere: a key klong's ref, prevPos, the id
(a vpos, not a pointer, but the same 8 bytes), the top node's root and
skip pointers, the record's startupPos and topPos, a got-dirty pair's
id and position, the meta block's lastTrans.

**What a write of a node writes: the whole node.** `StoredKeyNode.toLongs`
writes the header and every klong and ref of the node's array,
`node.klongs[0 .. n)`: the node's whole history since it was made or last
replaced, not what is new since its last stored version. In memory a
node is a history (012-02, section 6.3.1): a writer only appends klongs
(a put adds a key klong, preceded by a time klong if the node has none of
the transaction's time; a delete sets bits in the transaction's bitmap);
when the node is full (n reaches the node size), its last version (one
time klong and the live key klongs) replaces it, or splits in two (012-02,
section 8.5). Between two replacements a node is written each time the
take writes it (a dirty node is written once a startup window, about sd
behind the end; 006-19, section 3.2), and each write repeats every klong
that the earlier writes held. prevPos names the version replaced, but no
reader needs it to read the node: a stored version is complete. So a
node's stored versions are snapshots, and a version with only the new
klongs (a delta) would be a new kind of node with a new read path
(006-19, section 6.6).

**Dead klongs** (024-18, section 2): a key klong shadowed by a later one
of the same compare value, or deleted by the last bitmap, is written
again with its node until the node is replaced. So are the node's older
time klongs and bitmaps.

### 2.4 The value node and the delete node

024-02, section 12. A put's value node: the header (12), the id (8), its
offset in the record (4), the value's length L (4), the value, the key's
size (4) and its k segments as 8 bytes each (8 per 7 key bytes, so a
24-byte key takes 32 and a 4-byte key 8), padded to 4. 32 + L + 8·k
bytes; written once, in its transaction's record. A delete node is the
same without the length and the value: 28 + 8·k. The value and delete
nodes repeat the whole key; the index holds it once more, a segment a
level.

### 2.5 What the reader does with it

* **A node is always read and parsed whole.** `NodeStream.readNode` reads
  the size, then the node, checks the CRC32C sum, and parses it
  (`StoredKeyNode.parse` copies every klong and ref into the in-memory
  `KeyNode`'s arrays). No reader reads one entry of a stored node at its
  offset; lookups run on the parsed arrays (`KeyNode.searchEq`). The only
  partial read is `NodeStream.readNodeHeader`, 32 bytes for the type and
  the id at a fixed offset (24 for a key or top node, 12 for a value
  node, in format 7), used by Rule R and the audit.
* **A start reads whole records**: the startup section from startupPos,
  every node parsed and validated (024-02, section 14.2), and the nodes
  that rule 4 by position does not cover read one by one.
* **Reclaim** reads value nodes (a step rewrites live values) and the
  key nodes on its scan; it sizes its steps in bytes of the stream.

So a variable-length encoding of a node's body changes no reader's
access pattern: what is read is a whole node, then parsed. It changes
the parsers, the serializers and every place that computes a node's size
from its count (`StoredKeyNode.getByteSize`, the take's byte test
`TransSeq.recordBytes`, `Dag.dirtyNodeBound`, the record limit's
arithmetic: 024-17, section 5.3).


## 3. Where the bytes go

Measured 2026-11-12, 01:36 to 02:30, on main `a8c3589a` (record format
7). `probe/CN.java`: the Core API, a FileStream, the builder's defaults
(sd 50 MB, node size 30, retain forever), a test clock of 1 ms a
transaction, keys `/app/users/k` + 12 digits (24 bytes, 4 segments)
unless `-s` (4-byte binary keys, one segment), random values of 100
bytes unless `-v0` or `-v8`, 100 operations a transaction (`-b100`) or
one (`-b1`). Workloads: `seq` and `rand` fill 1M (or 10M) keys in key
order or at random, and the window is the fill; `over` fills at random,
then overwrites 1M random keys (200,000 with `-b1` at 10M; 2M with
`-b100` at 10M), the window the overwrites; `del` deletes every key in
random order after a random fill; `fifo` is a queue (a put at the end
and a delete of the oldest, alternately, 3M operations, reclaim on with
retain 4 s at `-b100` and 400 s at `-b1`), the window the stream kept.
`Scan` reads the window's records, read only, and counts each byte by
kind (the categories sum to the window: checked, diff 0, in every run).
Runs are deterministic: `over-b100` made again (with a dump) gave the
same bytes. Outputs in `/Users/f/fl/bench/2026-11-11/compact/out/1m/`
and `out/10m/`; tables by `python3 probe/summary.py OUT`.

**Bytes a put** (an operation: a put or a delete), 1M keys; "value node
rest" is a value node's bytes besides the value (header 32, key 32 for
k24; a delete node 28 and the key); "frame" the record header, end
marker, got-dirty pairs, padding, meta blocks:

| Run            | total | value | value node rest | index | of it dead | frame |
|---|---|---|---|---|---|---|
| seq-b100       | 187.1 | 100.0 | 64.0 | 20.9  | 0.2   | 2.1  |
| seq-b1         | 288.1 | 100.0 | 64.0 | 76.0  | 2.8   | 48.1 |
| rand-b100      | 264.5 | 100.0 | 64.0 | 95.0  | 3.2   | 5.5  |
| rand-b1        | 322.0 | 100.0 | 64.0 | 108.3 | 3.8   | 49.6 |
| over-b100      | 408.1 | 100.0 | 64.0 | 233.4 | 37.4  | 10.7 |
| over-b1        | 476.6 | 100.0 | 64.0 | 257.3 | 40.8  | 55.3 |
| del-b100       | 217.0 | 0.0   | 60.0 | 149.9 | 22.7  | 7.1  |
| del-b1         | 291.2 | 0.0   | 60.0 | 179.5 | 27.1  | 51.7 |
| fifo-b100      | 187.4 | 71.5  | 75.1 | 37.8  | 3.7   | 3.0  |
| fifo-b1        | 385.4 | 101.8 | 94.1 | 138.0 | 17.5  | 51.5 |
| rand-b100-s-v0 | 89.0  | 0.0   | 40.0 | 45.5  | 1.1   | 3.5  |
| over-b100-s-v0 | 192.7 | 0.0   | 40.0 | 146.1 | 24.0  | 6.5  |
| over-b100-v8   | 255.8 | 8.0   | 64.0 | 175.8 | 28.5  | 7.9  |
| over-b100-sd5  | 908.2 | 100.0 | 64.0 | 709.8 | 111.3 | 34.4 |
| over-b1-sd5    | 961.5 | 100.0 | 64.0 | 719.2 | 112.8 | 78.4 |

`fifo`'s value columns include reclaim's rewrites of live values (its
records are in the window). At 10M keys (one run each, its own slot;
`del-b100` deletes 2M random keys):

| Run (10M)         | total  | value | value node rest | index | of it dead | frame |
|---|---|---|---|---|---|---|
| seq-b100          | 194.4  | 100.0 | 64.0 | 28.2  | 0.4  | 2.2  |
| rand-b100         | 666.3  | 100.0 | 64.0 | 479.0 | 32.1 | 23.3 |
| over-b100         | 896.5  | 100.0 | 64.0 | 698.0 | 81.3 | 34.5 |
| over-b1           | 943.0  | 100.0 | 64.0 | 702.0 | 66.1 | 76.9 |
| del-b100          | 758.1  | 0.0   | 60.0 | 665.4 | 76.9 | 32.6 |
| over-b100, B = 62 | 1083.4 | 100.0 | 64.0 | 897.5 | 87.0 | 21.9 |

* **The index is most of a put wherever the keys are many against the
  window**: 11 percent of the stream in a sequential fill, 36 in a random
  one, 57 in random overwrites at 1M keys; 72 to 78 percent at 10M keys
  in the random fill and the overwrites (and at 1M with sd 5 MB,
  024-19's stand-in for 10M: 709.8 against 10M's 698.0). BergDB
  optimizes for that case first.
* **The value node's own overhead** (64 bytes for a 24-byte key) is a
  constant a put, the largest part after the value in a sequential fill.
* **The frame** is 2 to 11 bytes a put in batches of 100 and about 50 in
  transactions of one put (an empty record is 48 bytes).
* **Dead klongs** with option 2 (theta 7) are 16 percent of the index
  in the overwrites at 1M keys and 12 percent at 10M; a node written
  holds 3.8 and 2.4 of them on average (section 7).
* Of the index of `over-b100` at 1M: headers 19.7 bytes a put, time
  klongs 27.4 and their unused refs 27.4, key klongs 79.5 and their refs
  79.5 (the got-dirty pairs, 10.0, are in the frame). At 10M: 66.7,
  73.1, 73.1, 242.6, 242.6.


## 4. The candidates

Each measured by `probe/Scan.java` re-encoding the window's records
offline, node by node: the bytes a put it saves.

* **K1**: no reference for time klongs and bitmaps (always −1 today).
* **K2**: K1 and a compact header: leaf and n in the header's byte 6,
  the node's offset in its record, the id relative to the record's tpos
  and prevPos as references (below).
* **K2f**: K2 with key klongs' references in 6 bytes.
* **K3**: K2 with references relative to tpos as varints (K3a: absolute
  varints, worse).
* **K4 = encoding C**: K3 with compact klongs (below).
* **K4b**: K3 with klongs as zigzag deltas of the one before (worse than
  K4).
* **K5**: K4 without the dead key klongs (an algorithm, 5.6).
* **V1**: a compact value or delete node: the 12-byte header, the id
  relative to tpos, the offset, L and the key's length as varints, the
  key's bytes without segment padding.
* **R1**: the record frame with the got-dirty pairs as varints relative
  to tpos (kept 8-aligned: 3.5 bytes of padding a record counted).
* **T1**: a compact top node (below 0.1 byte a put in every run).
* **D0, D1**: a delta version (only the klongs after its previous
  version, when that version is in the window) in format 3 and in C:
  counted, not a candidate (5.6).

Saved, bytes a put, 1M keys, and C's share of the index ("all" is K4,
V1, R1 and T1 together; "all %" of the total of section 3):

| Run            | K1   | K2   | K3    | C (K4) | K5    | V1   | R1   | all   | all % | C of index |
|---|---|---|---|---|---|---|---|---|---|---|
| seq-b100       | 0.7  | 1.4  | 5.8   | 12.1   | 12.2  | 22.2 | 1.3  | 35.6  | 19.0 | 58 % |
| seq-b1         | 9.0  | 11.1 | 24.2  | 46.6   | 47.5  | 23.9 | 8.9  | 79.4  | 27.6 | 61 % |
| rand-b100      | 12.5 | 14.8 | 29.7  | 55.2   | 56.6  | 21.7 | 3.3  | 80.3  | 30.3 | 58 % |
| rand-b1        | 14.0 | 16.9 | 33.6  | 61.0   | 62.7  | 23.8 | 9.3  | 94.1  | 29.2 | 56 % |
| over-b100      | 27.4 | 33.0 | 66.8  | 131.5  | 147.9 | 21.3 | 5.6  | 158.4 | 38.8 | 56 % |
| over-b1        | 29.9 | 36.7 | 73.9  | 142.9  | 160.9 | 23.5 | 11.8 | 178.2 | 37.4 | 56 % |
| del-b100       | 23.9 | 27.7 | 46.6  | 88.7   | 98.7  | 18.6 | 4.5  | 111.8 | 51.5 | 59 % |
| del-b1         | 27.9 | 32.8 | 55.6  | 104.5  | 116.6 | 20.7 | 10.9 | 136.1 | 46.8 | 58 % |
| fifo-b100      | 2.0  | 3.2  | 10.1  | 21.4   | 23.0  | 25.4 | 1.6  | 48.4  | 25.8 | 57 % |
| fifo-b1        | 16.6 | 20.7 | 42.9  | 83.8   | 90.6  | 33.7 | 10.8 | 128.3 | 33.3 | 61 % |
| rand-b100-s-v0 | 6.8  | 7.7  | 15.0  | 28.2   | 28.6  | 18.3 | 2.3  | 48.7  | 54.8 | 62 % |
| over-b100-s-v0 | 18.3 | 21.8 | 44.6  | 87.1   | 96.7  | 17.8 | 3.7  | 108.7 | 56.4 | 60 % |
| over-b100-v8   | 21.5 | 25.8 | 52.1  | 100.9  | 113.1 | 21.5 | 4.4  | 126.8 | 49.6 | 57 % |
| over-b100-sd5  | 76.3 | 93.8 | 200.2 | 391.5  | 441.8 | 21.3 | 16.6 | 429.5 | 47.3 | 55 % |
| over-b1-sd5    | 77.3 | 97.5 | 205.0 | 391.9  | 442.9 | 23.2 | 23.2 | 438.3 | 45.6 | 54 % |

At 10M keys:

| Run (10M)         | K1   | K2    | K3    | C (K4) | K5    | V1   | R1   | all   | all % | C of index |
|---|---|---|---|---|---|---|---|---|---|---|
| seq-b100          | 1.0  | 1.9   | 7.8   | 16.3   | 16.4  | 22.1 | 1.3  | 39.7  | 20.4 | 58 % |
| rand-b100         | 52.2 | 63.5  | 130.0 | 254.4  | 269.7 | 21.4 | 11.0 | 286.8 | 43.1 | 53 % |
| over-b100         | 73.1 | 89.6  | 185.8 | 369.6  | 407.1 | 21.3 | 15.7 | 406.6 | 45.4 | 53 % |
| over-b1           | 73.9 | 91.5  | 188.2 | 372.8  | 403.8 | 23.5 | 21.3 | 417.7 | 44.3 | 53 % |
| del-b100          | 82.5 | 98.2  | 184.3 | 361.5  | 397.4 | 18.4 | 15.2 | 395.1 | 52.1 | 54 % |
| over-b100, B = 62 | 95.9 | 105.9 | 235.2 | 489.9  | 530.8 | 21.4 | 9.3  | 520.6 | 48.1 | 55 % |

* **Encoding C stores 38 to 47 percent of today's index bytes** in every
  workload, key shape and size (it saves 53 to 62 percent of them).
  About half of the saving is the klongs (a tag byte and the key bytes
  not shared with the klong before), the rest the references (relative
  to the record, varints) and the header. The fixed-width steps save
  much less: K1 3 to 16 percent of the index, K2 7 to 19, K2f (6-byte
  references) 17 to 26.
* **With V1, R1 and T1** the stream is 19 to 20 percent smaller in a
  sequential fill (the value node's overhead is most of it), 29 to 43
  percent in a random fill, 37 to 47 percent in the overwrites (48 at B
  = 62), 47 to 52 in the deletes, and 50 to 56 percent with short keys
  or small values.
* **K5** (dead klongs left out as well) adds 1 to 5 percent of the
  total: option 2 has already bounded them.
* **Delta writes** (D0 in format 3, D1 in C) save 131.5 and 186.7 bytes
  a put in `over-b100` at 1M (C alone 131.5), 469.9 and 579.5 at 10M (C
  alone 369.6): in the overwrites about half of a node's written
  versions follow its own previous one in the window, which they repeat
  in full (5.6 for why it is not a candidate here).
* **Deflate** (the JDK's, level 6, a yardstick): a whole record to 0.30
  to 0.76 of its bytes (values included; random values do not
  compress), the index nodes of a record together to 0.28 to 0.52, one
  node alone to 0.43 to 0.57. Encoding C (0.39 to 0.47 a node, with no
  shared dictionary) does as well as deflate on a record's index and
  better than deflate a node, and a node read alone is what a reader
  needs.

**Encoding C** (`probe/Codec.java`; its class comment is the exact
definition): in today's 12-byte node header, the leaf flag and n in byte
6 (zero today; n at most 127, 62 with 024-19's Q6); then the node's
offset in its record (varint; a node read alone finds its record's start
tpos by it, as a value node does today); the id as a zigzag varint
relative to tpos; prevPos as a reference; then each klong as a tag byte
(its type; for a key klong its length and the bytes it shares with the
key klong before it) and its fields: a time as a delta from the node's
time before it (the first whole), a key klong's unshared bytes and its
reference, a bitmap's new bit indexes. A reference is relative to tpos:
varint 0 for none, a varint for a position before the record, and a
fixed 5 bytes for one in the record itself, so that every node's size is
known before positions in the record are given (a varint of a forward
position would make sizes and positions depend on each other). A node
that does not fit the rules, or would not be shorter, is written in
format 3, so no node is larger than today's (5.1). Round trip on
200,000 key nodes of `over-b100` (format 7, 2026-11-12): exact, 0.435
of format 3's bytes, no fallback.

**CPU** (`Codec` on the 200,000 nodes of `out/dump-over7.bin`, 371
bytes a node in format 3; a timing hold, both slots, 2026-11-12, 02:27:53
to 02:28:01; no Lean or lake process; `mediaanalysisd` at one core and
load 2.3, as in 024-19's hold; two JVMs, SerialGC, the last 4 of 20
rounds each; ns a node):

| Step | format 3 | C |
|---|---|---|
| write (encode, CRC32C set)  | 89 to 96   | 219 to 234 |
| read (CRC32C check, decode) | 105 to 111 | 212 to 226 |
| decode alone                | 75 to 78   | 192 to 200 |

With CRC32C (0.12 ms a MB, 024-25) the sum is no longer most of the
cost, so C's varints and tags show: about 130 ns more a node written and
110 more a node read, in a probe not tuned (`Codec` decodes a byte at a
time). For scale: `StoredKeyNode.parse`, which allocates the node's
arrays, takes 500 to 515 ns a node (one cold pass); a put of
`over-b100` writes 0.61 key nodes at 1M keys and 2.1 at 10M, so C would
add 80 to 270 ns to a put of 9 to 10 µs (024-19, section 4.4: 114,000
overwrites a second at 1M), 1 to 3 percent, against 45 percent fewer
bytes to write and read. (On 2026-11-11, with Fletcher-16 at about 6 ns
a byte, C was faster than format 2; that no longer holds.)


## 5. What a compact form changes besides the bytes

Each point: what changes, who does it, and how it would be checked.
Encoding C here means section 4's K4 for key nodes with V1, R1 and T1
for the value nodes, the record frame and the top nodes; "nominal" is a
node's size in format 7 (32 + 16 n for a key node).

### 5.1 The accounting: keep the nominal sizes as bounds

Who counts a node's bytes today, and from what:

* **The take's pace** (`TransSeq.take`, `shareFp`) counts nodes, not
  bytes: its share is D o S / (O sd), D the got-dirty nodes of the
  section, o and O own bytes (value nodes and 48 a record), S the
  section's length in stream bytes. A key node's size enters only
  through S, the real stream.
* **The record limit** (`TransSeq.recordBytes`, the `maxBytes` of a
  take; `Db.dirtyNodeBound`; 024-17, section 5.3; 024-24's L1 to L6) and
  **the Lean bound** (`SIS/Tree/Bound.lean`, `nodeBytes M = 32 + 16 (M +
  1) + 16`; `ReleaseFits`) count each key node at its nominal size.
* **Reclaim's charge** (`Reclaim`, a step's `rewritten`) counts the value
  nodes it rewrites (key and value bytes and `VALUE_NODE_BYTES`) and
  the index nodes it makes dirty at their nominal size
  (`Trans.dirtiedBytes`, `Db`'s got-dirty path), against a quarter of
  the real stream's growth.

**The rule that keeps the algorithms out of it**: encoding C writes a
node in format 3 whenever its encoding would not be shorter (section 4),
so a node's written size is at most its nominal size. If the record
limit, `dirtyNodeBound`, 024-24's limits and the Lean bounds keep the
nominal size, every bound proved or measured on format 7 holds as it
is, with room to spare: no algorithm, no limit and no Lean definition
changes. The serializer computes the real sizes when it lays out the
record (section 4: a reference into the record itself has a fixed 5
bytes, so every node's size is known before positions are given), and
the record header's size is the real one. Checked by an assertion in
the serializer (written size at most nominal) and by the existing
`ReleaseFits` and limit tests, unchanged.

**Reclaim's charge is the exception**: it compares nominal index bytes
with real stream growth, so with encoding C a step would count its index
nodes at about 2.4 times what they cost and rewrite fewer values a byte
of growth than the fraction says: iterations span more stream, and the
stream kept grows. The charge should count what the step's record
really adds, or both sides nominal; a design point for the change, not a
bound. (Aside, found here: `Reclaim.VALUE_NODE_BYTES` is still 28, the
value node's overhead before 024-25, which made it 32; it only paces
reclaim, by 4 bytes a rewritten value; reported to the coordinator.)

### 5.2 The startup distance: the same bytes hold more transactions

The startup distance sd is in stream bytes, and the take keeps the
startup section near sd (levels.md, section 5). A compact stream writes
r times the bytes of today's for the same records (r 0.44 to 0.81 by
workload, section 4), so a section of sd bytes holds about 1 / r times
the transactions:

* **The take's decisions at sd are today's at sd / r.** The share D o S
  / (O sd) and the deadline 2 sd compare stream bytes with sd, and the
  encoding scales the stream's bytes (to first order: r differs a little
  between records, and a varint reference is shorter where distances
  shrink). So a compact stream at sd is today's stream at sd / r,
  re-encoded; the offline figures of section 4 are those of a compact
  stream at sd r.
* **Measured**: `over-b100` at 1M keys has r = 0.61 at 50 MB. Today's
  stream at sd 81.7 MB (50 / 0.61) writes 321.9 bytes a put, re-encoded
  210.8. So a compact stream at sd 50 MB writes about 211 bytes a put
  against today's 408.1: 48 percent less, not section 4's 39. The extra
  is the hot regime's absorption (024-19, section 3.1): a window of more
  puts writes each dirty node fewer times. At 10M keys (r = 0.55):
  today's stream at sd 91.6 MB writes 757.9 bytes a put, re-encoded
  422.9, against today's 896.5 at 50 MB: 53 percent less, not 45.
  (The re-encoded runs' own ratios, 0.65 and 0.56, would put the
  equivalent sd at 77 and 90 MB: first order, as said.)
* **A start reruns about 1 / r times the transactions** for the same sd
  (1.5 to 1.8 times in `over-b100`), reads the same bytes, and parses
  about 1 / r times the nodes, each smaller. 007-05's warm start at 10M
  keys stays within 10 s only up to sd about 75 MB: a user who keeps sd
  = 50 MB gets about the rerun work of today's 80 MB. D, the dirty set
  in memory, grows with the section's transactions too, by less than
  1 / r (more of them hit the same nodes).
* So the compact form lets the user take the gain in two ways: the same
  sd, for about half the bytes a put and a longer start, or sd r, for
  section 4's saving and today's start. The default sd (50 MB) would be
  set again by measurement with the change (QC3); nothing else depends
  on sd's unit.

### 5.3 Reads and CPU

A node is read whole and parsed whole today (section 2.5), so a
variable-length body changes no access pattern: `NodeStream.readNode`
reads the size, the node, checks the sum and parses into the same
`KeyNode` arrays. Memory (MEM) is the same: the in-memory node does not
change. `readNodeHeader` (Rule R, the audit) reads the first 32 bytes
and would decode the offset and the id from varints. With CRC32C (024-25)
the checksum is no longer most of a node's cost, so the encoding's own
CPU shows: about 130 ns more a node written, 110 more a node read
(section 4). A start parses about 1 / r times the nodes at the same sd
(5.2), each a little slower to decode and faster to read.

### 5.4 Damage detection and CorruptStreamTester

CRC32C covers the encoded bytes as it covers format 3's: a flipped byte
or a cut is caught before the parse, as now. What changes is the parse
of a node whose sum is right but whose bytes are wrong (CST's "a node's
field changed with its checksum made right", 018-01, section 6.1): with
fixed fields a changed byte changes one field; with varints and tags it
can shift every field after it. The parser must refuse, with a
`StreamFormatException`, a varint that runs past the node's end or past
10 bytes, a tag of no kind, a shared-byte count above the previous key
klong's length, a bitmap index above 61, a reference before tpos that
names a position before the stream's first, an in-record reference at
or past the record's end, n other than the tags read, and trailing bytes. CST's
node-field table (fixed offsets, `nodeFields`) would become a list of
the parsed fields' byte ranges, and its pinned copies would be made
again. The best-effort promise (KNOWN) does not change.

### 5.5 The C clone, the specification, the Lean model

* **The C clone** (012; item 022's) is at format 6, before 024-21's
  merges and 024-25's CRC32C: format 7 is work for it in any case. The
  encoding adds a varint reader and writer and the parse checks of 5.4,
  about 300 lines of C by the Java probe's size (`Codec`, 120 lines for
  the key node's encoder and decoder).
* **The specification** (024-02): sections 9 to 12 (the node header,
  the top node, the key node, the value node) and 14.1 (references)
  are rewritten; the klong's meaning (section 11.2) and the keys
  (section 13) do not change. Format numbers: key node 4, value and
  delete nodes 6, top node 4, the record format 8 (or 7 again, if it
  lands before 2026.5 is released, as 024-25 did).
* **The Lean model** has no node bytes (024-25, section 2): with the
  nominal accounting of 5.1 nothing in `lean/` changes. A model of the
  encoding itself (a round-trip theorem: decode of encode is the node)
  is possible and small, but no other proof needs it.

### 5.6 What it is not: delta writes and dropping dead klongs

* **A delta** (a version holding only the klongs new since its previous
  one, 006-19, section 6.6; D0 and D1 in Scan) saves about as much as
  encoding C in the overwrites (section 4), but it is an algorithm, not
  an encoding: a cold read would follow prevPos through up to B
  versions, Rule R and the cut would have to keep every version a delta
  needs, and a start would read chains. Not studied further here.
* **Writing a node without its dead klongs** (K5) is option 2 with
  theta 0: it removes history that `searchLte` reads at older times. It
  is 024-18's and 024-23's question, decided at theta 7, not an
  encoding.


## 6. Recommendation

**Encoding C, with V1, R1 and T1, in release 2026.6 with the stable
stream format (026), not in 2026.5.** Designed now, its decisions that
touch the algorithms taken in 2026.5 (QC2, QC4), the bytes changed once,
in the release that promises to read them.

* **The gain is real and largest where BergDB cares most**: at 10M keys
  an overwrite writes 896 bytes today and about 490 with C, V1 and R1
  offline (45 percent less), about 423 at the same sd (53 percent, 5.2);
  a random fill 666 and 380. The index, the part that grows with the
  database's size, is cut to 38 to 47 percent in every workload, and
  the node size matters less (section 7). A sequential fill gains 19
  percent, most of it the value node's overhead (V1).
* **It is not an algorithm.** With the nominal sizes kept as the
  accounting (5.1), it changes no tree rule, no take decision, no limit,
  no Lean definition: a serializer, a parser and their checks. 2026.5's
  aim is solid algorithms (024-04); 2026.6's is the stable stream
  format, and the stored form of a node is the format's largest single
  part. Changing the bytes in 2026.5 and again in 2026.6 would pay twice
  for the specification, CST's pinned copies, the C clone and the
  conformance digests.
* **Option 2 already bounds the dead klongs** (theta 7 at 30): they are
  12 to 16 percent of today's index bytes in the overwrites (section
  3), and K5 (writing without them) saves only a few percent beyond C.
  Nothing in 2026.5's algorithms waits for the encoding.
* **What would argue for 2026.5**: format 7 is unreleased, so 2026.5's
  format change could carry it at no compatibility cost, and a user of
  2026.5 at 10M keys writes 1.8 times the bytes a put that C would
  write (sections 4 and 5.2). Against it: a format change of its own, about a week of
  work with the parse checks and CST, and its review, in a release
  whose remaining work is algorithms and proofs.
* **In 2026.5, cheaply**: keep the accounting nominal (QC2) and B at
  most 62 (024-19, Q6), so that n fits the header's byte 6 and the
  bitmap stays 62 bits; fix reclaim's `VALUE_NODE_BYTES` (5.1, aside).

**Not recommended**: K1 or K2 alone (fixed-width, simpler, but 3 to 19
percent of the index where C saves 53 to 62); deflate (no better on a
record than C and worse a node, section 4, and a node read alone cannot
use a record's dictionary); delta writes and K5 (algorithms, 5.6).


## 7. With 024-19 (the node size) and 024-18 (dead klongs)

**024-19's request** (024-19, section 7): a written key node's bytes in
encoding C by kind of klong, at B = 30 and 62 (and 14). From Scan's
"C part", "C kind" and "count" lines, leaves and inner nodes together,
per written node (the counts of nodes are in the outputs); "B/time" is
a time klong's bytes in C, "B/live" and "B/dead" a key klong's with its
reference; "C hdr" the header with offset, id and prevPos; "today" and
"C" the whole node:

| Run | B | n | time | live | dead | C hdr | B/time | B/live | B/dead | today | C |
|---|---|---|---|---|---|---|---|---|---|---|---|
| over-b100 | 14 | 9.80  | 2.74  | 5.29  | 1.77 | 23.2 | 4.98 | 6.98 | 7.31 | 188.7 | 86.7  |
| over-b100 | 30 | 21.75 | 5.58  | 12.36 | 3.81 | 22.9 | 4.90 | 7.11 | 7.30 | 380.0 | 165.9 |
| over-b100 | 62 | 43.10 | 10.66 | 24.95 | 7.49 | 22.8 | 4.78 | 7.12 | 7.27 | 721.6 | 305.9 |
| over sd5  | 14 | 8.93  | 2.38  | 5.01  | 1.54 | 23.5 | 5.00 | 7.03 | 7.46 | 174.9 | 82.1  |
| over sd5  | 30 | 19.33 | 4.58  | 11.40 | 3.34 | 23.6 | 4.91 | 7.19 | 7.48 | 341.2 | 153.0 |
| over sd5  | 62 | 35.61 | 7.76  | 22.12 | 5.72 | 23.7 | 4.78 | 7.23 | 7.45 | 601.7 | 263.4 |
| rand-b100 | 14 | 10.80 | 3.17  | 6.79  | 0.84 | 22.4 | 4.86 | 6.98 | 7.08 | 204.8 | 91.1  |
| rand-b100 | 30 | 23.31 | 6.67  | 15.78 | 0.86 | 22.1 | 4.70 | 6.97 | 7.25 | 405.0 | 169.7 |
| rand-b100 | 62 | 47.35 | 13.74 | 32.63 | 0.97 | 22.1 | 4.52 | 6.94 | 7.34 | 789.6 | 317.7 |
| over 10M  | 30 | 18.93 | 4.38  | 12.11 | 2.44 | 24.1 | 5.32 | 7.56 | 7.63 | 334.8 | 157.5 |
| over 10M  | 62 | 41.51 | 9.30  | 27.99 | 4.22 | 24.3 | 5.08 | 7.57 | 7.74 | 696.2 | 316.2 |

Bitmaps (the deletes): 2.0 bytes each in C (`del-b100`, 2.40 a node),
against 16 today. "n" counts every klong; the rows' kinds add to it.

* **A written node in C is about H = 23 bytes and 4.8 to 5.3 a time
  klong, 7.0 to 7.6 a key klong, live or dead**: s(n) ≈ 23 + 5 t + 7.2
  k, against today's 32 + 16 n. Fitted over B as 024-19's section 3.1
  does (the cold rows, sd 5 MB): today about 50 + 8.9 B, C about 29 +
  3.8 B. The ratio H' / C' rises from 5.7 to 7.7, which moves the cold
  regime's optimum from about B = 10.4 to 11.6: as 024-19 predicted, the
  compact form scales the curve and hardly moves its minimum.
* **No prefix sharing that grows with B**: a key klong costs the same at
  14, 30 and 62 (6.9 to 7.2 bytes at 1M). The tree of trees already
  shares whole 7-byte segments at the level above (section 2.3); what
  neighbours in one node share is a byte or two, whatever B. 024-19's
  first exception does not occur.
* **Time klongs become cheap** (5 bytes, not 16), which 024-19's second
  exception expected to favour larger B a little: it does, and dead key
  klongs cost as much as live ones, so it is only the time klongs.
* **Bytes a put in C by B** (section 4's "all" taken off; offline, at
  each run's sd):

  | Run             | today 14 | today 30 | today 62 | C 14  | C 30  | C 62  |
  |---|---|---|---|---|---|---|
  | over-b100       | 491.0    | 408.1    | 393.1    | 292.9 | 249.7 | 240.2 |
  | over-b1         | 550.5    | 476.6    | 464.9    | 336.9 | 298.4 | 290.4 |
  | rand-b100       | 312.2    | 264.5    | 249.8    | 207.3 | 184.2 | 176.8 |
  | over-b100-sd5   | 833.5    | 908.2    | 1133.7   | 458.9 | 478.7 | 569.6 |
  | over-b100, 10M  | -        | 896.5    | 1083.4   | -     | 489.9 | 562.8 |

  With C, 62 is 3 to 4 percent below 30 where the window covers the keys
  (today 2 to 6) and 15 to 19 percent above it in the cold rows (today
  21 to 25); 14 is 4 percent below 30 in the cold row (today 8) and 13
  to 17 percent above in the hot ones. **30 stays the minimax size, and
  is within about 4 percent of the best size in every row with C** (within 10
  today, 024-19, section 6). The compact form makes the node size matter
  less; it does not argue for another one.
* **The delete bitmap and n**: encoding C writes a bitmap as its new bit
  indexes (one byte each, 0 to 61) and n in 7 bits of byte 6; both hold
  with 024-19's Q6 (62 the maximum). A larger B would need a wider n
  and a delete encoding with more indexes: possible in C (an index byte
  holds 0 to 255), not in format 3's 62-bit bitmap.
* **Dead klongs** (024-18, 024-23): with option 2 at theta 7 a written
  node holds 3.8 dead key klongs at 1M (2.4 at 10M); they are 16 and 12
  percent of today's index bytes and 17 and 12 percent of C's. Writing
  without them (K5) saves 1 to 5 percent of the stream beyond C: no
  reason to revisit theta for the encoding's sake.


## 8. Questions for Frans

**Decided, QC1: the compact stored form is for release 2026.6** (Frans,
2026-11-12, 07:26: "QC1. For 2026.6 as recommended. QC2,3,4,5 should
wait since it is for 2026.6."). QC2 to QC5 wait for 2026.6's work on the
stream format (026).

Cite as "026-01, QC1". Each with a recommendation; none blocks other
work.

* **QC1. When.** The compact stored form (encoding C for key nodes, V1
  for value and delete nodes, R1 for the record frame, T1 for top
  nodes) in release 2026.6 with the stable stream format, not in 2026.5?
  Recommended: **2026.6** (section 6: not an algorithm; the bytes
  changed once, in the release that promises to read them).
* **QC2. The accounting.** Keep the take, the record limit,
  `dirtyNodeBound`, 024-24's limits and the Lean bounds counting a key
  node at its nominal size (32 + 16 n), with the rule that a node whose
  encoding is not shorter is written in the fixed format, so that the
  written size is never above the nominal? Recommended: **yes**, decided
  now (5.1: every bound of format 7 then holds unchanged, and the Lean
  model needs nothing).
* **QC3. The startup distance's unit.** Keep sd in stream bytes, so that
  a compact stream at the same sd keeps 1 / r times the transactions (a
  longer start, fewer bytes a put), and set the default again by
  measurement with the change? Recommended: **yes** (5.2); the
  alternative, sd in nominal bytes, would keep today's start and need a
  second count of the stream.
* **QC4. Reclaim's charge.** With a compact form, count a step's index
  nodes at what the step's record really adds (or both sides nominal),
  not nominal against real growth? Recommended: **real bytes**, with the
  change (5.1). Separately, now: `Reclaim.VALUE_NODE_BYTES` is 28, the
  value node's overhead before 024-25 made it 32; correct it in 2026.5
  (a pacing constant; a test, `Reclaim`'s charge check, uses the same
  constant)?
* **QC5. Delta writes.** Leave a version that holds only its new klongs
  (006-19, section 6.6) unstudied for now? It saves as much as encoding
  C in the overwrites and more at 10M keys (section 3), but it changes
  reads, Rule R and the cut. Recommended: **yes, leave it**; a study of
  its own after 2026.6 if the stream's bytes still matter then.


## 9. Log

* 2026-11-11, 11:32: asked by coord-1111. Clone, probe (`Scan`, `CN`),
  first 1M runs from 11:40; encoding C with record-relative refs and its
  round trip (`Codec`) at 11:47.
* 2026-11-11, 11:51: postponed by Frans (the coordinator, 11:50): runs
  stopped, State written.
* 2026-11-12, 01:34: resumed by compact2 for coord-1111 on main
  `a8c3589a` (record format 7). Clone reset and built; `Scan` and
  `Codec` changed for the 12-byte node header (checked at 50,000 keys).
* 2026-11-12, 01:36 to 02:16: the 1M matrix, two scripts, one slot each.
  01:38: a 10M run and a 1M run of the same name shared a directory; the
  10M run failed and was rerun (01:39), `run10m.sh` uses its own
  directories since. 01:39 to 02:12: the 10M runs, each its own slot.
* 2026-11-12, 02:16: the feedback runs had been set at sd r instead of
  sd / r (5.2); the 10M one stopped and rerun at sd 91.6 MB, the 1M one
  made at 81.7 MB. Sections 1 to 8 written from 02:00 to 02:25.
* 2026-11-12, 02:27: the 10M deletes done; `Codec` timed (02:27:53 to
  02:28:01, after the Lean processes of another session had ended; the
  two slots released at 02:28:53, late by a quoting slip). 02:30: done,
  State written.
* 2026-11-12, 07:41: moved from 024-20 to 026-01 (Frans, 07:39: "go
  through the current work and move things for 2026.6 to 026. In
  particular this 024-20 should move there."); a stub left at 024-20.
  QC4's separate point, `Reclaim.VALUE_NODE_BYTES`, was already fixed in
  2026.5 (`682a4f53`, 024-25).


## State

2026-11-12, 02:30. **Done**, by compact2 (coord-1111's agent), resumed
at 01:34. No run is running, no slot held; the test databases removed
(`/Users/f/fl/bench/2026-11-11/compact/data/` is empty).

* **Done**: sections 1 to 8 on record format 7. The 1M matrix
  (`run1m.sh`, `run1m-b.sh`: 37 runs, and `over-b100-sd82` by hand), the
  10M runs (seq, rand, over, over-b1, over at B = 62, over at sd 91.6
  MB, del; one slot each), the round trip of encoding C on 200,000
  format 7 nodes, `Codec` in a timing hold (02:27:53 to 02:28:01).
* **Not done**: the C encoder in Java (product code; with the change
  itself if Frans takes QC1); fifo, short keys and batches of 1 at 10M
  (the 1M rows and sd 5 MB stand in); a feedback run (5.2) for other
  workloads than `over-b100`.
* **Clone**: `/Users/f/fl/bench/2026-11-11/compact/clone`, branch
  `024-20-compact` reset to main `a8c3589a` (nothing committed, no
  product code), built. Probe classes in
  `/Users/f/fl/bench/2026-11-11/compact/classes` (`javac -d classes -cp
  clone/java/build/bergdb.jar probe/*.java`).
* **Probe changed for format 7** (01:40): `Scan` and `Codec` read the
  12-byte node header of 024-25 (node formats 3, 3, 5); encoding C keeps
  that header and puts leaf and n in its byte 6. `Scan` adds encoding
  C's bytes by kind of klong ("C kind" lines); `summary.py` prints them;
  `run10m.sh` uses `data/10m-NAME`.
* **Outputs**: `/Users/f/fl/bench/2026-11-11/compact/out/1m/` and
  `out/10m/` (one `.txt` a run, `runs.log`), `out/codec-timing-1.txt`
  and `-2.txt`, `out/dump-over7.bin` (200,000 key nodes of `over-b100`,
  format 7); `out/old1m/` and `out/dump-over.bin` are format 6
  (2026-11-11), superseded.
* **To continue**: Frans's answers to QC1 to QC5. If QC1 is 2026.6, the
  work starts there from section 4's definition (`Codec`'s class
  comment) and 5.1 to 5.5's list; QC4's constant can be fixed in 2026.5
  on its own.

2026-11-24. Status set after the release (lead-1124).
