# 024-08. MEM at 10M KVs: why 327 heap bytes a KV

Created 2026-11-11. Status: done (2026-11-11), a study: Q1 answered
(Frans, 07:30; 024-04, section 7); Q2 as recommended in 024-15; Q3's
correction in 024-03's head.

A study of the known case against aim 3 of release 2026.5 (024-04,
section 4): release 2026.4 holds 327 heap bytes a KV at 10M KVs where it
holds 129.6 at 1M by the same method (024-03, section 3: "Not explained
here"). Asked by the day's coordinator (coord-1111) at 07:10; 024-05's
ST1 gave an explanation by reading, to be tested here (its GM1). The
probe, the scripts and every output are in `08-mem-at-10m/`. No code of
BergDB is changed.


## 1. In short

* **The cause is the keys' shape, not their number.** MEM's keys are
  `"" + i`. Keys "1000000" to "9999999", 9M of the 10M, are 7 bytes
  long, and a key of exactly 7 bytes is two segments
  (`Keys.toSegments`): each of them gets a segment tree of its own, a
  key node that holds one key. At 1M every key is at most 6 bytes and
  none does. Measured: 9,000,000 key nodes with one key at 10M, none at
  1M.
* **Separated by runs.** The same number of KVs with another shape: 1M
  keys of 7 bytes give 356.0 bytes a KV; 10M keys of 13 bytes that
  share their first segment (`/k/%010d`, 024-03's keys) give 127.0. So
  MEM does not grow with the number of KVs: 130.3 at 1M and 127.0 at
  10M for the same shape.
* **A segment tree of one key costs 223 to 226 heap bytes**: six
  objects of 216 bytes (the key node 56, its three arrays 88, its
  handle 32, its entry in the node table 24 and the entry's `Long` 16)
  and 7 to 8 bytes of the table's bins, where a key's place in a
  shared node is 20 bytes. The 9M trees are 200.5 of the 197.5 bytes
  of difference; everything else is 3.0 less at 10M (section 4).
* **It is not a fault of MEM at 10M, but it shows a real cost.** A key
  pays 226 heap bytes (no eviction) and 75 to 160 stream bytes a put
  for each 7-byte prefix that it shares with no other key. Keys of 36
  random characters, such as UUIDs: 1,305 bytes a KV and 712 stream
  bytes a put, against 181 and 82 for random keys of 6. One byte more
  of a prefix can move a fixed-width key across the boundary:
  `/k/%010d` 130, `/kk/%010d` 356 (section 5).
* **With eviction, the default, the heap is the budget for any key
  shape** (173 and 213 MB at 3M KVs, budget 200 MB); the one-key trees
  then cost reads and stream instead: 5.6 nodes read a get, 3.6 times
  the stream (section 8).
* **Against aim 3:** the cost is proportional to the count and to the
  key's size, so the aim's words hold; what is out of proportion is the
  constant, up to 32 heap bytes for a byte of key, and its jumps with
  the key's length. A decision for Frans (section 10, Q1).
* **Proposed bound** for 024-05 (section 7): heap, no eviction, at most
  131 K + 230 T + the values' bytes, K the KVs and T the segment trees
  beyond each first segment's; checked with three runs of `Mem` (keys
  of 6 bytes and of 7 bytes at 1M, a fixed shape at 10M).
* **No fix of a few lines exists.** Options in section 9: name the cost
  (recommended now), a node table without boxed keys (39 bytes a node
  less), one-key tails kept in the parent leaf (the real fix, a format
  change and a change of the model).


## 2. What the two numbers measure

Both are `bergdb.dev.props.Mem`'s method (006-02, section 1), run by
024-03's probe (`PF1.mem`) with `n` as an argument:

* **The database.** `Db.builder().testSetup().mainStream(new
  DummyStream())`: a test clock, **no eviction**, the retain duration
  forever (no reclaim), a stream that counts the bytes appended and
  keeps none of them. Every node ever made stays in memory, the ended
  versions of nodes too (levels.md, section 7: with `noEvict()` "the
  memory of ended versions is released only at a restart").
* **The workload.** n KVs, keys `"" + i` for i from 0 to n - 1 in that
  order, values of 0 bytes, 100 KVs a transaction.
* **The number.** The heap in use (`totalMemory() - freeMemory()`)
  after four `System.gc()`, after the fill minus before it, divided by
  n. The database is running and holds everything.
* **The JVM.** OpenJDK 27.0.1, G1, `-Xms8g -Xmx8g`, compact object
  headers and compressed oops (the defaults).

So MEM is the heap that a database costs when it holds every KV and
its whole index in memory, a KV: not the heap of a database at its
defaults, which evicts (section 8). `level1.sh` runs it at 1M KVs and
fails above 131.

What differs between the two runs, beside n: **the keys' lengths.**
`"" + i` has 1 to 6 bytes below 1,000,000 and 7 bytes from 1,000,000 to
9,999,999. The other candidates, each ruled out:

* **The cache budget against the data's size:** there is none; `Mem`
  evicts nothing at either size (0 objects evicted, 0 loads).
* **The moment, garbage not yet collected:** the class histogram of
  live objects, taken after a full collection, sums to MEM's figure
  within 0.1 byte a KV (section 4).
* **Reclaim's state:** no reclaim; the retain duration is forever
  (reclaim iterations 0).
* **The index's top nodes:** 11 at 1M and 14 at 10M, under 0.01 byte a
  KV.
* **Underfilled nodes:** the key nodes with several keys are filled
  alike at both sizes (0.96 and 0.58 of 14 and 30 places) and cost 72.1
  and 69.7 bytes a KV. The one-key nodes are full: 2 klongs in 2
  places.
* **The stream's buffers:** 10.9 MB of `byte[]` at any size, in the
  empty database too, so not in MEM.


## 3. Reproduced

A clone at `release-2026.4` (`76f66f89`), built with `java/build.sh`;
the probe `MemProbe` (package `bergdb.core`, compiled apart, classes
before the jar): `Mem`'s method with the keys' shape, the order, the
value size and n as arguments, a walk of the node table's objects, and
`jcmd <pid> GC.class_histogram` (live objects) before and after the
fill.

| Keys `"" + i`, key order | MEM, bytes a KV | key nodes   | of them with one key |
|---|---|---|---|
| 1M KVs                   | 129.6           | 95,700      | 0                    |
| 3M KVs                   | 276.8           | 2,287,236   | 2,000,000            |
| 10M KVs                  | 327.1           | 9,957,378   | 9,000,000            |

129.6 and 327.1 are 024-03's figures to the decimal. The curve is not
one of the count: it is the share of 7-byte keys, 0, 2/3 and 9/10. With
129.6 for a key of at most 6 bytes and 355.9 for a key of 7 (section
5), the mix gives 280.5 at 3M and 333.3 at 10M; measured 276.8 and
327.1: the node table's bins, the nodes with several keys and the rest
are each 2 to 4 bytes a KV less at 10M than in the 1M run of 7-byte
keys (section 4's first table).


## 4. The breakdown

**By class**, bytes a KV (objects a KV): the class histogram after the
fill minus that of the empty database, divided by n. The totals are
MEM's to 0.1.

| Class                | 1M `"" + i`    | 10M `"" + i`   | 1M, 7 bytes    | 10M `/k/%010d` |
|---|---|---|---|---|
| `long[]`             | 47.11 (0.192)  | 102.50 (1.992) | 111.80 (2.192) | 45.57 (0.192)  |
| `KeyNode`            | 5.36 (0.096)   | 55.76 (0.996)  | 61.38 (1.096)  | 5.38 (0.096)   |
| `ValueNode`          | 40.00 (1.000)  | 40.00 (1.000)  | 40.00 (1.000)  | 40.00 (1.000)  |
| `Pointee[]`          | 11.92 (0.096)  | 33.52 (0.996)  | 36.09 (1.096)  | 12.09 (0.096)  |
| `Handle`             | 3.06 (0.096)   | 31.86 (0.996)  | 35.07 (1.096)  | 3.07 (0.096)   |
| `HashMap$Node`       | 2.30 (0.096)   | 23.90 (0.996)  | 26.30 (1.096)  | 2.30 (0.096)   |
| `byte[]`             | 16.03 (1.001)  | 16.00 (1.000)  | 16.03 (1.001)  | 16.00 (1.000)  |
| `Long`               | 1.53 (0.096)   | 15.93 (0.996)  | 17.54 (1.096)  | 1.54 (0.096)   |
| `HashMap$Node[]`     | 0.80           | 6.72           | 8.45           | 0.84           |
| the rest             | 1.54           | 0.96           | 3.30           | 0.22           |
| **Total**            | **129.65**     | **327.15**     | **355.96**     | **127.01**     |

At 10M there is one key node, one handle and one table entry a KV
(0.996); at 1M one for every 10 KVs (0.096).

**By structure**, bytes a KV:

| Structure                                   | 1M     | 10M    | 10M - 1M |
|---|---|---|---|
| The values: `ValueNode` 40, `byte[0]` 16    | 56.0   | 56.0   | 0.0      |
| Key nodes with several keys, see below      | 72.1   | 69.7   | -2.4     |
| Segment trees of one key: 0 and 0.9 a KV    | 0.0    | 200.5  | +200.5   |
| The rest (G1's fillers, `TransSeq`, lists)  | 1.5    | 1.0    | -0.6     |
| **MEM**                                     | 129.6  | 327.1  | +197.5   |

* **A key node with several keys** (0.0957 a KV at both sizes, about
  10.4 KVs a node; arrays of 14 and 30 places, filled to 0.96 and 0.58):
  the object 56 bytes, its arrays `klongs` and `pos` 492 together and
  `pointers` 125, its handle 32, its table entry 24 + 16 + 8: 753
  bytes a node at 1M. The nodes hold 1.26 (1M) and 1.18 (10M) pointers
  to values a KV: more than one, because a split keeps the old node as
  history and copies its live klongs (`KeyNode.lastVersion`), and
  `Mem` keeps the history for ever. By the code; not checked by a walk
  from the root.
* **A segment tree of one key** is one key node with arrays of 2 places
  (a time klong and the key's last segment), and what every index node
  has:

  | Object                                  | Bytes |
  |---|---|
  | `KeyNode` (header 8, fields 44)         | 56    |
  | `klongs`, `long[2]`                     | 32    |
  | `pos`, `long[2]`                        | 32    |
  | `pointers`, `Pointee[2]`                | 24    |
  | `Handle`                                | 32    |
  | `HashMap$Node`, the node table's entry  | 24    |
  | `Long`, the entry's key (the node id)   | 16    |
  | the table's bins, `HashMap$Node[]`      | 7 to 8     |
  | **Sum**                                 | 223 to 224 |

  Each row is the histogram's difference between 1M keys of 7 bytes
  and 1M keys of 6 (`%07d` and `%06d`), which is 225.9 in all (2 bytes
  are G1's fillers and `Object[]`); the walk counts the 88 bytes of
  arrays. The key's klong in the node above it
  (8 + 8 + 4 bytes and the arrays' free places) is there for a 6-byte
  key too.
* **The shares of the 197.5 bytes of difference:** the 9M one-key trees
  +200.5 (194.4 for their objects, 6.1 for their part of the table's
  bins): 101.5 %. The key nodes with several keys -2.4 and the rest
  -0.6: -1.5 %. Nothing else: the values, the top nodes (14 of them),
  reclaim's structures (none: retain forever), the stream's buffers
  (not counted) and the tables beside the bins do not differ.


## 5. The cause, and the rule behind it

**The rule** (`Keys.toSegments`, `Dag`): a key is cut into segments of
7 bytes; a key of L bytes has floor(L / 7) + 1 segments, the last one
of 0 to 6 bytes, so a key of exactly 7, 14, 21 bytes ends with an
empty segment (the code's comment: it keeps a klong of 7 bytes, which
points to a tree, apart from a shorter one, which points to a value).
The keys that share their first j segments are in one tree, the
**segment tree** of that prefix of 7j bytes; the tree's root is a key
node. So the index holds one tree for each distinct prefix of 7j
bytes, j from 1, that a key of 7j bytes or more has. A prefix that
only one key has makes a tree of one key: 223 to 226 bytes of heap to
hold one klong of 8 bytes and its pointer.

**The key's shape separated from the count**, MEM's method at 1M KVs
unless said, keys in key order:

| Keys                          | Bytes | MEM   | One-key trees a KV | Stream bytes a put |
|---|---|---|---|---|
| `"" + i` (MEM's)              | 1-6   | 129.6 | 0                  | 48.5               |
| `%06d`                        | 6     | 130.1 | 0                  | 48.1               |
| `%07d`                        | 7     | 356.0 | 1                  | 122.7              |
| `"" + (i + 1000000)`          | 7     | 355.9 | 1                  | 122.7              |
| `%08d`                        | 8     | 117.4 | 0 (trees of 10)    | 57.4               |
| `%013d`                       | 13    | 130.1 | 0                  | 57.7               |
| `%014d`                       | 14    | 355.7 | 1                  | 133.4              |
| `/k/%010d` (024-03's)         | 13    | 130.3 | 0                  | 57.7               |
| `/kk/%010d`                   | 14    | 355.7 | 1                  | 133.4              |
| `/key/%010d`                  | 15    | 117.3 | 0 (trees of 10)    | 66.5               |
| `/keys/%010d`                 | 16    | 120.7 | 0 (trees of 100)   | 63.3               |
| `/k/%010d`, 10M KVs           | 13    | 127.0 | 0                  | 74.9               |
| `"" + i`, 10M KVs             | 1-7   | 327.1 | 0.9                | 147.0              |

* **The same count, another shape:** 1M keys of 7 bytes cost what the
  10M run's 7-byte keys cost. **The same shape, another count:**
  `/k/%010d` costs 130.3 at 1M and 127.0 at 10M. This is 024-05's GM1,
  with the outcome it named ("about 350 and about 130").
* **One byte moves it.** `%06d` to `%07d`, `%013d` to `%014d`, `/k/` to
  `/kk/` before ten digits: 130 to 356. A byte more (`%08d`, `/key/`)
  and the trees hold 10 keys each: 117, less than 130, since their
  small nodes are full.

**Keys that share no prefix**, 1M KVs, random characters (so the puts
come in random key order):

| Keys                          | Segments | MEM     | One-key trees a KV | Stream bytes a put |
|---|---|---|---|---|
| 6 random characters           | 1        | 181.0   | 0                  | 82.4               |
| 8 random characters           | 2        | 407.8   | 1                  | 243.9              |
| 13 random characters          | 2        | 408.3   | 1                  | 244.1              |
| 16 random characters          | 3        | 633.7   | 2                  | 372.9              |
| 32 random hex digits          | 5        | 1,088.0 | 4                  | 603.0              |
| 36 random characters          | 6        | 1,305.3 | 5                  | 711.5              |
| `"" + i` in random order      | 1        | 177.6   | 0                  | 82.3               |
| `/k/%010d` in random order    | 2        | 174.6   | 0                  | 95.9               |

* **Each further segment costs 225 to 227 heap bytes** a key: 181.0 +
  226.8, + 2 x 226.4, + 4 x 226.8, + 5 x 224.9. In the stream it costs
  75 bytes a put in key order and 108 to 162 in random order (the
  stream written in the fill, index nodes included; a `DummyStream`
  with the default startup distance). 006-19, section 4.2, point 6 has
  the same for the stream: "three one-key segment leaves a key".
* **A second effect, not the 10M question:** puts in random key order
  cost 175 to 181 where key order costs 130, for any shape: 1.7 times
  the key nodes (163,500 against 95,700), the ended versions that
  splits leave, kept because MEM keeps the history for ever and evicts
  nothing. MEM's figure is for key order.
* **Values:** with values of 100 bytes MEM is 225.1 for `"" + i` at 1M
  and 451.2 for 7-byte keys: 95.5 more, a `byte[100]` of 112 bytes for
  a `byte[0]` of 16.


## 6. Fault or not

* **"MEM at 10M KVs is 2.5 times MEM at 1M" is a property of the
  measurement.** `Mem`'s keys change their shape at 1,000,000. With a
  shape that does not change, the heap a KV is the same at 1M and 10M
  (130.3 and 127.0). The KVs stored cost memory in proportion to their
  count. As a known case of the count, ST1's first form, it can be
  struck.
* **It is not a configuration effect.** No cache budget, no startup
  distance and no moment of the collection is in it: the histogram of
  live objects gives the same bytes, and the walk finds every object
  in the node table.
* **What it shows is a real cost of the key's shape**, old (the
  segments are from 2013; 2026.3 gives the same 327.0): a segment tree
  for one key costs a whole index node, 223 bytes where a key's place
  in a shared node is 20 and a KV's whole share of the shared index 72,
  in the heap, in the stream and, when the node is not in memory, one
  more node to read for a get. In aim 3's words the cost is still "in
  proportion to count and size": at most K x (131 + 226 x floor(L / 7))
  for K keys of L bytes. Out of proportion are the constant (226 bytes
  for 7 bytes of key, 32 a byte, where a klong is 8) and the jump with
  one byte of length or of prefix.
* **So: a fault only if aim 3 is read with a constant.** My reading: a
  user who picks UUIDs or hashes as keys pays, with empty values and no
  eviction, 6 to 7 times the memory and 7 to 9 times the stream written
  of a user with random 6-byte keys (section 5), and with eviction 5.6
  node reads a get (section 8).
* **The documentation says it in words, with stream figures.**
  `Connection`, "Keys" and `Db`, "Keys and values": "a level for each
  7 bytes of the key, so that a key costs stream bytes, memory and time
  in proportion to its length, many times what a value of that length
  costs", about 1,200 to 1,400 stream bytes for a key of 114 bytes
  whose first 100 differ, about 190 when 109 of 120 are shared; "Keep
  keys short ... let keys that are written together share their start"
  (020-24-13, U13-1). Not said there: the heap's figure (226 a level),
  and that a key of exactly 7, 14 or 21 bytes pays a level more than a
  key one byte shorter or longer.
* **For 024-05:** the case stays in its list in ST1's second form ("a
  key whose segment no other key shares costs a key node of its own"),
  with a bound that names it (section 7) and a decision whether to fix
  it (section 10, Q1).


## 7. The bound and the test proposed for 024-05

In place of 024-05's BD12 ("at most 131 ... and a stated cost for each
segment tree of one key (about 220, to be measured)"):

**BD12. The heap without eviction, retain forever, keys put in key
order:**

    heap <= fixed + 131 K + 230 T + V

K the KVs; T the segment trees beyond the first segment's, that is the
distinct prefixes of 7j bytes (j from 1) among the keys of 7j bytes or
more; V the values' bytes in memory, each value a `byte[]` (its length
and 16, rounded up to 8). Measured: 127 to 130 for K's term, 223 to 226
for T's. In random key order K's term is 181 (the history of splits).

How it is checked, three runs of `Mem` with the key's format and n as
arguments (its defaults unchanged, so 1M with `"" + i` stays the figure
of 2015 to 2026):

1. **K's constant:** `Mem` as today, 1M KVs: at most 131 (`level1.sh`
   has it).
2. **T's constant:** `Mem` with keys `%07d`, 1M KVs, minus run 1: at
   most 230 (today 226.4). `level1.sh`, 2.5 s more.
3. **No term that grows with the count:** `Mem` with keys `/k/%010d`
   at 10M KVs: at most 131 (today 127.0). 19 s and a heap of 1.3 GB,
   so a step of `night.sh`, not of `level1.sh`.

And, since `Mem` at 10M with `"" + i` measures a mix of shapes, **no
document should quote 327 as MEM at 10M**; 024-03's line "MEM, bytes a
KV (10M KVs)" should say "(9M of them 7-byte keys)" or be replaced by
127.0.

BD11 (the heap with eviction: the budget, D and a fixed part, no term
in the keys) is 024-05's own; section 8 adds what was measured here.


## 8. What memory a user needs

* **Everything in memory** (`noEvict()`, or a budget above the data):
  section 7's formula. For values of 100 bytes (112 each), computed
  from it; rows 1 and 3 were measured at 1M (225.1 and 451.2). Nothing
  is measured above 10M: the law is linear in the three runs of section
  3 and the two of `/k/%010d`.

  | Keys                              | Heap a KV | 10M KVs  | 100M KVs |
  |---|---|---|---|
  | shared prefixes, as `/k/%010d`    | 225       | 2.3 GB   | 23 GB    |
  | the same, random order            | 270       | 2.7 GB   | 27 GB    |
  | 7 bytes, or 14 as `/kk/%010d`     | 451       | 4.5 GB   | 45 GB    |
  | 36 random characters (a UUID)     | 1,400     | 14 GB    | 140 GB   |

* **With eviction, the default:** the heap follows the budget (200 MB
  by default), not the keys and not their shape: 024-03 measured 195 MB
  after a random fill of 10M `/k/%010d` keys. Here, 3M KVs with empty
  values put in random key order, the builder's defaults on a
  `FileStream` (eviction on, cache 200 MB, startup distance 50 MB,
  retain forever), then 100,000 gets, twice:

  | 3M KVs, eviction on               | `/k/%010d` | 32 random hex digits |
  |---|---|---|
  | heap above the empty database     | 173 MB     | 213 MB               |
  | resident bytes, as counted        | 199 MB     | 199 MB               |
  | fill, µs a put                    | 4.9        | 22.6                 |
  | stream written, bytes a put       | 226        | 819                  |
  | get, µs, rounds 1 and 2           | 3.6, 1.2   | 15.8, 15.9           |
  | nodes read from the stream a get  | 1.2, 0.1   | 5.6, 5.6             |

  So a user with a budget needs the budget, the pinned part and a
  fixed part, as 024-05's BD11 says, for any key shape; with one-key
  trees the heap was 7 % above the budget (`Residents` counts such a
  node as 207 bytes, 128 and 79, where it is 223; whether that is the
  whole 7 % was not checked). What the one-key trees cost then is not
  memory but work: 3.6 times the stream, 4.6 times the time of a put,
  and a get that reads 5.6 nodes from the stream: the paths of the
  100,000 keys read fit the budget for `/k/%010d` (round 2 reads 0.1)
  and not for the hex keys. The OS cache was warm; from a disk each
  node read is a read. The gets differ too in which keys they take
  (keys spread over the range; the first 100,000 put). Times are one
  run each on a machine in use: for the ratio only. Not run at 10M
  with the hex keys.


## 9. Options, if the cost is to be fixed

No fix of a few obvious lines exists: the one-key tree's node is
already the smallest the code makes (arrays of 2 places).

* **(a) Name the cost; fix the measurement.** Section 7's bound and
  its three runs; in `Connection`'s and `Db`'s paragraphs on keys the
  heap's figure and the rule in one sentence ("each prefix of 7, 14, 21
  bytes that a key shares with no other key costs an index node, about
  226 bytes when in memory; a key of exactly 7, 14 or 21 bytes has one
  more"). Size: `Mem` takes two arguments, two lines in
  `level1.sh`, one step in `night.sh`. No change of the algorithm.
* **(b) The node table without boxed keys.** Each index node has a
  `HashMap$Node` (24), a `Long` (16) and 7 to 8 bytes of bins: 47 to 48
  bytes, 21 % of a one-key tree and 4.6 bytes a KV in shared nodes. A
  table of handles by open addressing on the handle's own id (the
  `Handle` holds it) costs about 8 bytes a node: 39 less, so 226 to
  187 a one-key tree and 130 to 126 a KV. Size: `Cache3`'s 4,096
  `HashMap`s replaced by a class of about 200 lines with its tests;
  eviction's CLOCK walks the maps (`mapHandles`) and must follow. No
  format change, no change of the model. Helps every database held in
  memory a little; does not remove the case.
* **(c) A key node of one key without arrays** (the klong, the
  reference and the pointer as fields): 88 to about 24 bytes, 64 less.
  `KeyNode`'s arrays are public fields read all over `dag` and `core`
  (2,030 lines, lock-free readers): a large and risky change for 28 %.
  Not recommended.
* **(d) Keep a one-key tail in the parent leaf**: while a prefix has
  one key, the key's further segments are klongs in the leaf of the
  tree above, and a tree is made when a second key shares the prefix.
  A segment then costs about 24 bytes (a klong, a reference, a
  pointer's place): by arithmetic, 36 random characters would cost
  about 300 instead of 1,305; the stream a put would fall likewise,
  and a get would read one node where it reads up to six. Size: the node format (a new kind of
  klong: a format change, allowed in 2026.5), `Dag`'s put, get,
  delete and split paths, `GetMany`, reclaim's scan, the Lean model's
  tree, the C clone. Weeks, and exactly the kind of change that
  "solid algorithms" wants decided before the format is frozen
  (024-04, section 3).
* **(e) Only the empty last segment** of keys of exactly 7j bytes
  (another way to tell a klong to a value from a klong to a tree): a
  format change that helps fixed-width keys of 7, 14, 21 bytes only;
  random long keys keep their trees. Not recommended alone; (d) covers
  it.

**Recommended:** (a) in 2026.5 whatever else is decided; (d) as a
study with a design and its size before Frans decides (Q1): it is the
only option that makes the cost follow the key's bytes; (b) on its own
merits, later, measured with `Mem`.


## 10. Questions for Frans

* **Q1. Is the cost of a one-key segment tree within aim 3?** (226 heap
  bytes and 75 to 160 stream bytes a put for each 7-byte prefix of a
  key that no other key shares.) (i) Yes: documented and bounded,
  option (a); (ii) no: a study of option (d) in 2026.5, since it is a
  format change. Default until answered: (a), and 024-05 keeps the
  case open as ST1.
* **Q2. `Mem`'s keys.** Keep `"" + i` at 1M as the historical figure
  and add the two runs of section 7 (recommended), or change `Mem`?
* **Q3. Should 024-03's 327 be corrected** in 024-03 and 024-04
  (section 4's table: "MEM ... 327 ... not explained") to say what it
  is? Recommended: yes, a line in each that cites this item; the
  coordinator's edit, not made here.


## 11. Files

In `08-mem-at-10m/`:

* `probe/MemProbe.java`: the probe (package `bergdb.core`).
* `run.sh`, `shapes1m.sh`, `shapes1m-b.sh`, `ev3m.sh`: the runners.
* `histdiff.py`: class histograms minus the empty database's, a KV.
* `out/`: each run's output (`NAME.txt`) and class histogram
  (`NAME.hist.txt`, its first 100 classes and the total; in full in
  `/Users/f/fl/bench/2026-11-11/mem/out/`); `histdiff.txt`, section 4's
  table; `empty.hist0.txt`, the empty database's histogram.


## 12. Log

2026-11-11, 07:10 to 07:24. The clone and the probe; 129.6 and 327.1
reproduced; the shapes at 1M; 3M and 10M under the heavy-run lock
(07:15 to 07:16); the histograms. The coordinator's message with
024-05's hypothesis came while the probe was written; the runs of
section 5 test it. The two runs with eviction at 3M under the lock
(07:19 to 07:21). Nothing in the main tree changed but this file and
`08-mem-at-10m/`; nothing committed; the data directories deleted.


## State

Written 2026-11-11, 07:24.

* **Done:** every section: both figures reproduced, the breakdown by
  class and by structure, the cause separated from the count by runs,
  the cost with eviction, the bound proposed, the options.
* **Not done:** nothing measured at 100M KVs (section 8's 100M column
  is the linear law); no run with eviction at 10M for long random keys
  (3M only); no run on s1; the stream kept (not written) for one-key
  trees; no design of option (d). No run is in progress and
  the heavy-run lock is not held by this work.
* **For Frans:** Q1 to Q3 of section 10. Until answered: option (a),
  and nothing built.
* **Clone:** `/Users/f/fl/bench/2026-11-11/mem/clone`, detached at
  `release-2026.4` (`76f66f89`), no branch, no change, no commit; the
  probe is outside it, in `/Users/f/fl/bench/2026-11-11/mem/probe`,
  its classes in `mem/classes`, outputs in `mem/out` (copied to
  `08-mem-at-10m/`).
* **To continue:** `mem/run.sh NAME n=... keys=...` (the probe's
  header has the arguments; `setup=default dir=DIR` for eviction); a
  run at 10M KVs or with a `FileStream` needs the lock of the common
  brief.

2026-11-13. Status set after the release (coord-1113).
