# 024-20. A compact stored form of the index nodes: measured

Created 2026-11-11 by Frans Lundberg. Status: postponed 2026-11-11,
11:50 (Frans: the merges at the delete first, the stored form after
that); not dropped. State says where it stopped.

Should an index node be stored more compactly in the stream, and how? A
study with measurements: the stored form today, byte for byte; where a
stream's bytes go, measured on streams of `main`; each candidate encoding
priced by re-encoding those streams offline; a recommendation. No product
code; the probe is in `20-compact-nodes/probe/`.

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
coordinator (coord-1111) at 11:32. Cite as "024-20, section 4" and the
questions as "024-20, QC1".


## 1. In short

**Stopped at 11:51** (postponed). Section 2 written; section 3 has
interim numbers from three 1M runs. Interim, not conclusions:

* At 1M keys, sd 50 MB, 24-byte keys, 100-byte values, 100 puts a
  transaction, the index nodes are 11 % of the stream in a sequential
  fill, 36 % in a random fill, 57 % in random overwrites (393 bytes a
  put, 223 of them index).
* An encoding of the key node's body (encoding C, section 4) stores
  41 to 43 % of today's index bytes (round trip checked on 200,000 real
  nodes); about half of the saving is the klongs (a tag byte and the
  used key bytes), the rest the refs and the header.
* The value node's own overhead (header 28, key 8 bytes a 7) is 60 bytes
  a put and can be about 38 (V1): 22 bytes a put in every workload,
  which is most of the saving in a sequential fill.
* Deflate (the JDK's, a yardstick only) does no better on the index
  bytes of a record (0.29 to 0.41 of them) than encoding C (0.41 to
  0.43), and worse per node (0.44 to 0.52).
* The Fletcher-16 checksum, not the encoding, is most of a node's write
  and read time (about 2.3 µs for a 364-byte node); encoding C halves
  it with the bytes (section 4; not yet in a timing hold).


## 2. The stored form today

From 024-02 (sections 8 to 13, the field tables) and the code of `main`
at `1076235c` (`StoredTrans`, `StoredKeyNode`, `StoredTopNode`,
`StoredValueNode`, `NodeStream`, `KeyNode`); 012-02, sections 5, 6 and
8, for the writer's rules. Integers little-endian; a *pointer* is an
`i64` stream position, −1 for none (024-02, section 14.1).

### 2.1 The record

024-02, section 8.1. A record is a transaction's bytes, at a multiple of
8 in the stream, its size a multiple of 8:

| Part              | Bytes        | What                                          |
|---|---|---|
| header            | 32           | size `i32`, format `u8` + 3 zero, time, startupPos, topPos (`i64` each) |
| top nodes         | 40 + 16·h    | each (section 2.2)                            |
| key nodes         | 32 + 16·n    | each (section 2.3)                            |
| value nodes       | 28 + L + 8·k | each, padded to 4 (section 2.4)               |
| delete nodes      | 24 + 8·k     | each (section 2.4)                            |
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

Every node begins with 8 bytes (024-02, section 9): its size (`i32`), its
type (`u8`: 10 top, 20 key, 30 value, 40 delete), its format (`u8`) and a
Fletcher-16 checksum (`u16`) over the node's bytes. The checksum takes
no bytes of its own beyond these 2.

**The top node** (024-02, section 10): 40 + 16·h bytes: the header, h
(`u8`), a zero byte, the ordinal (48 bits), the id, the root time, the
root pointer, and h skip pointers each with its time (16 bytes a pair).
One is written with each new super root; in the runs of section 3 they
are below 0.1 byte a put.

### 2.3 The key node and its klongs

024-02, section 11.1. 32 + 16·n bytes, n the klongs:

| Off      | Bytes | Field                                                 |
|---|---|---|
| 0        | 8     | node header (size, type 20, format 2, checksum)       |
| 8        | 8     | prevPos: the position of the version this one replaces |
| 16       | 8     | leaf flag (1 byte), n (2 bytes), 5 zero bytes         |
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

024-02, section 12. A put's value node: the header (8), the id (8), its
offset in the record (4), the value's length L (4), the value, the key's
size (4) and its k segments as 8 bytes each (8 per 7 key bytes, so a
24-byte key takes 32 and a 4-byte key 8), padded to 4. 28 + L + 8·k
bytes; written once, in its transaction's record. A delete node is the
same without the length and the value: 24 + 8·k. The value and delete
nodes repeat the whole key; the index holds it once more, a segment a
level.

### 2.5 What the reader does with it

* **A node is always read and parsed whole.** `NodeStream.readNode` reads
  the size, then the node, checks the checksum, and parses it
  (`StoredKeyNode.parse` copies every klong and ref into the in-memory
  `KeyNode`'s arrays). No reader reads one entry of a stored node at its
  offset; lookups run on the parsed arrays (`KeyNode.searchEq`). The only
  partial read is `NodeStream.readNodeHeader`, 32 bytes for the type and
  the id at a fixed offset (24 for a key node, 16 for a top node, 8 for a
  value node), used by Rule R and the audit.
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

Interim: three 1M runs only (`probe/CN.java`: the Core API, a
FileStream, the builder's defaults, sd 50 MB, a test clock of 1 ms a
transaction, keys `/app/users/k` + 12 digits, random 100-byte values,
100 puts a transaction; `over` = a random fill, then 1M random
overwrites, the window the overwrites only). Bytes a put:

| Run       | total | value | value node rest | index | frame |
|---|---|---|---|---|---|
| seq-b100  | 182.8 | 100.0 | 60.0            | 20.7  | 2.1   |
| rand-b100 | 258.0 | 100.0 | 60.0            | 92.6  | 5.5   |
| over-b100 | 393.0 | 100.0 | 60.0            | 222.7 | 10.3  |

The index of `over-b100`, by part (bytes a put): headers 19.0, time
klongs 27.8 and their −1 refs 27.8, key klongs 74.0 and their refs
74.0 (of the key klongs and refs, dead ones 39.5); the got-dirty pairs
9.6 (in the frame). Leaves hold 20.9 klongs on average in `over`
(scan of 20,000 keys) and 14.9 in a sequential fill.

Not measured: the batch of 1, short keys, values of 0, deletes, the
queue, 10M keys (all scripted, none run; State).


## 4. The candidates

Each measured by `probe/Scan.java` re-encoding the stream offline; the
saving in bytes a put, and of the index:

| Candidate                                     | seq  | rand | over  | of index |
|---|---|---|---|---|
| K1 no ref for time klongs and bitmaps         | 0.7  | 12.5 | 27.8  | 3 to 14 % |
| K2 K1 + compact header                        | 1.6  | 15.5 | 35.0  | 8 to 17 % |
| K2f K2 + 6-byte refs                          | 3.7  | 23.0 | 53.5  | 18 to 25 % |
| K3 K2 + refs relative to the record (varint)  | 5.9  | 29.8 | 66.4  | 29 to 32 % |
| K4 = encoding C: K3 + compact klongs          | 12.2 | 54.6 | 127.8 | 57 to 59 % |
| K4b K3 + klongs as zigzag deltas              | 6.9  | 35.6 | 81.7  | worse than K4 |
| K5 K4 without dead klongs (024-18)            | 12.2 | 56.1 | 145.2 | 59 to 65 % |
| V1 compact value node                         | 22.2 | 21.8 | 21.3  | (value nodes) |
| R1 got-dirty pairs as varints                 | 1.3  | 3.3  | 5.2   | (frame) |
| all of K4, V1, R1                             | 35.7 | 79.7 | 154.4 | 20 / 31 / 39 % of total |

**Encoding C** (`probe/Codec.java`, its class comment is the exact
definition): after today's 8-byte node header word, one byte for the
leaf flag and n; the node's offset in its record (varint; a node read
alone finds its record's start tpos by it, as a value node does today);
the id as a zigzag varint relative to tpos; then each klong as a tag
byte (type; for a key klong its length and the bytes it shares with the
key klong before it) and its fields: a time as a delta from the node's
time before it (the first whole), a key klong's unshared bytes and its
ref, a bitmap's new bit indexes. A ref is relative to tpos: a varint for
a position before the record, a fixed 5 bytes for one in the record
itself, so that every node's size is known before positions are given
(a varint of a forward position would make sizes and positions depend
on each other). A node that does not fit the rules, or would be longer,
is written in today's format 2, so no node is ever larger than today
and every byte bound of 024-17 still holds. Round trip on 200,000 nodes
of `over`: exact, 0.425 of format 2's bytes, no fallback.

**CPU** (interim, not in a timing hold, `Codec` on those nodes, ns a
node): write today 2,270, C 1,150; read today 2,280, C 1,470; without
the checksum, decode today 90, C 265. Fletcher-16 is about 6 ns a byte
(as 024-17, F6), so fewer bytes pay for the varints.

**Delta writes** (a version with only the klongs new since the last
one, 006-19, section 6.6): the probe counts them (D0, D1) but no run
had finished with that code.

**Not yet written**: the effects on CST and damage detection, the
startup distance (a fixed sd in bytes holds more transactions with
smaller records: more rerun work and dirty nodes for the same sd), the
take's and reclaim's byte accounting (keep today's nominal sizes, so
that the take and the Lean model are unchanged?), the C clone, the
specification and the Lean models.


## 5. What matters less than it seems, or more

(to be written)


## 6. Recommendation

(to be written)


## 7. With 024-19 (the node size) and 024-18 (dead klongs)

(to be written)


## 8. Questions for Frans

(to be written)


## 9. Log

* 2026-11-11, 11:32: asked by coord-1111. Clone, probe (`Scan`, `CN`),
  first 1M runs from 11:40; encoding C with record-relative refs and its
  round trip (`Codec`) at 11:47.
* 2026-11-11, 11:51: postponed by Frans (the coordinator, 11:50): runs
  stopped, State written.


## State

2026-11-11, 11:51. **Postponed by Frans** (the coordinator, 11:50):
stopped; no run is running, no slot held, the test databases removed.

* **Done**: section 2 (the stored form today, point 1 of the brief);
  the probe, in `20-compact-nodes/probe/`: `Scan.java` (reads a stream
  directory read only, bytes by kind, and every candidate's bytes),
  `CN.java` (makes a database by a workload, then runs Scan on the
  window), `Codec.java` (encoding C, round trip and micro-benchmark on a
  dump of key nodes), `summary.py` (the tables), `run1m.sh` and
  `run1m-b.sh` (the 1M runs: workloads seq, rand, over, del, fifo;
  batches 100 and 1; short keys and values 0; sd 5 MB; node sizes 14
  and 62 for 024-19), `run10m.sh` (one 10M run in a slot).
  Interim numbers: sections 1, 3 and 4 (three 1M runs).
* **Outputs**: `/Users/f/fl/bench/2026-11-11/compact/out/1m/` (three
  runs; `over-b100` before the K3a, D0, D1 and C-part lines were added),
  `out/old1m/` (an earlier encoding, superseded), `out/dump-over.bin`
  (200,000 key nodes, 75 MB, for `Codec`).
* **Not done**: the rest of the 1M matrix and the 10M runs; the timing
  hold for `Codec`; sections 5 to 8 (the effects on CST, the startup
  distance, reclaim, the take, C, the specification, Lean; what matters
  by workload; the recommendation; the questions; 024-19's request: a
  node's bytes in encoding C by kind of klong at B 30 and 62, which the
  "C part" and "count" lines of Scan give).
* **Clone**: `/Users/f/fl/bench/2026-11-11/compact/clone`, branch
  `024-20-compact` at `1076235c` (main; nothing committed, no product
  code), built (`java/build/bergdb.jar`). Classes:
  `javac -d /Users/f/fl/bench/2026-11-11/compact/classes -cp
  clone/java/build/bergdb.jar probe/*.java`.
* **To continue, first**: rebuild the clone from the main of that day
  (the merges at the delete change the index nodes a run writes, so the
  numbers above are main's of 2026-11-11, before them); remove
  `out/1m/*`; run `sh probe/run1m.sh OUT` then `run1m-b.sh OUT` (each
  1M run takes 10 to 60 s, one JVM, no slot); `python3 probe/summary.py
  OUT`; then the 10M runs with `run10m.sh` (takes a slot itself), and
  `Codec` in a timing hold (`slot.sh take-timing`, about a minute).
* **Clone**: `/Users/f/fl/bench/2026-11-11/compact/clone`, branch
  `024-20-compact` at `1076235c` (main; nothing committed: no product
  code). Probe classes in `/Users/f/fl/bench/2026-11-11/compact/classes`,
  compiled with `javac -d classes -cp clone/java/build/bergdb.jar
  probe/*.java`.
* **To continue**: `python3 probe/summary.py
  /Users/f/fl/bench/2026-11-11/compact/out/1m` gives the tables.
