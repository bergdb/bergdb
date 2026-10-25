004-03. Summary and future direction
====================================

By Frans Lundberg and Claude (Opus 5.5, Claude Code), 2026-10-24. Created at Frans's
request: "In this new subitem, together we will summarize the work so far and conclude
on the future direction for this."

Status: open.



# 1. Future direction

Frans 24 Oct.

The current cache eviction has unacceptable stop-the-world that can reach 
10s of seconds and more.
Indirect swizzling is the path forward to avoid stop-the-world. 

The performance cost of slower gets than with direct swizzling is 
low and acceptable. In general it is within 20 percent of existing lookup time  
when all nodes are cached.

The development cost is a major change. To code and to Lean.

Note about performance. For larger databases, disk is used, and lookups of values not
cached take in the order of 100 times longer than if all nodes are in memory. 
So, I think if it like this: it takes more like 100 us then 1 us. 
So, the slowdown of lookups for a large database going from direct to indirect swizzling
can typically be from 100.0 us to 100.2 us. 

BergDB is about stability and a well-rounded performance tradeoffs with 
good worst-case behavior. Typically, BergDB aim to be within a factor of 2.0 from
optimal. This is rule-of-thumb only.




# 2. Work so far, summary by AI

Written by Claude from [01-report.md](01-report.md) (004-01, 2026-10-18) and
[02-scale-tests.md](02-scale-tests.md) (004-02, 2026-10-23 and 24). The section numbers
below point into those documents. F53 is Frans's MacBook (Apple M1 Pro), s1 his VPS (AMD
EPYC, two virtual CPUs, a virtual disk at about 0.45 ms a read).

## 2.1 The question

BergDB swizzles directly: a memory pointer goes straight to the object. To evict an object,
Level 4 must know that no resident object points to it, and it finds that out by a sweep
that walks every resident object, twice. Indirect swizzling puts a small per-node handle
between the pointer and the object, so that evicting an object changes only its handle.
004 asked what that would cost, what it would give, and what else could do the same.

## 2.2 004-01: the literature, BergDB today, a design, a microbenchmark

* **The idea is old and well studied:** LOOM (1983), ORION (1988), Kemper and Kossmann's
  classification and measurements (1993, 1995), the Bw-tree's mapping table (2013), the
  logical pointers of MVCC databases. Against it: HotSpot left handles for direct pointers,
  and the Bw-tree's indirection costs it 18 percent on reads. No system was found that
  combines handles with retained history (004-01, section 2).
* **BergDB's memory is a DAG.** 63 to 72 percent of the resident objects have more than
  one incoming memory pointer, because a time split's old node and its replacement point to
  the same children. So LeanStore's cheap eviction, which relies on one parent per page,
  does not apply as it is (3.3).
* **Handles fit the DAG:** one handle per index node, shared by all pointers to it from any
  version. Eviction becomes local and bounded, with any policy (CLOCK, cooling); one object
  per node, no snapshots; exact accounting; records unchanged. Values keep direct pointers
  and go with their leaf. Startup is unchanged (4).
* **The hop is cheap:** on one thread a handle costs 9 to 13 percent over a direct pointer,
  no more than today's pointer lock and access stamp; with 8 threads handles keep about 90
  percent of direct's throughput. A scattered handle is much dearer (874 against 583 ns out
  of cache) (5.1).
* **Today's read path does not scale:** the pointer lock and the stamp, and the `readSync`
  monitor and shared counter of every get, cap readers; today's gets do fewer with 8
  threads than with 4 (3.4).
* **Memory:** 24 bytes a handle, 3 to 4 percent of the index for compact keys, 12 to 18
  percent for random 16-byte keys (5.4).
* **The cost of the change is large:** the Java pointer and eviction code, and the Lean
  physical layer's eviction proofs (about 11,400 lines) (4.10).
* **Alternatives** (7): an incremental sweep (A), reverse reference lists (B), a forest of
  single-owner memory pointers with history reached by id (C, LeanStore's way), weak
  references and the collector (E), a hash lookup per edge (F). C and D (handles) are the
  real candidates.
* **Recommendation** (8): first take the lock, the stamp and `readSync` off the read path,
  whatever comes next; then prototype handles for index nodes on a branch; C if the hop is
  too dear; model the chosen state in Lean before the physical proofs are redone.

## 2.3 004-02: the same on a second machine, and BergDB at 0.1M to 100M keys

* **004-01 holds on x86 Linux.** The follow variants rank the same on s1; s1 is about twice
  as slow out of cache. s1's one-thread figures vary by up to 14 percent between sessions
  (10.2, 10.8).
* **A handle's placement takes care of itself under G1.** After one G1 evacuation,
  handles allocated in random order cost what handles allocated next to their objects
  cost; ZGC keeps the scattered order. At 64M keys a handle still costs 13 percent over a
  direct pointer (10.3).
* **In memory, a get grows slowly:** 0.38 µs at 0.1M keys to 1.92 µs at 50M on F53, about
  half a microsecond per tenfold. Today's read path stops at about 2 million gets a second
  at any size; without the lock and the stamp 3.5 to 4.9 million (10.5.1).
* **Beyond memory, loads and the device set the cost:** 4 to 10 µs a get from the OS
  cache, 0.11 ms from F53's SSD at 100M keys, 0.37 to 0.88 ms from s1's disk. A handle's
  0.05 to 0.15 µs is nothing beside that. Random 24-byte keys need 4.5 loads a get instead
  of 2 (10.5.2, 10.5.6).
* **The worst case is the sweep**, and it grows faster than the budget: 0.5 s at 66 MB,
  6 s at 665 MB, 13.8 s at 2.66 GB, 266 s during the 100M load (8 GB budget), with G1's
  full collections around it. Readers wait for it: from the OS cache, 34 to 44 percent of
  the readers' samples were blocked on the write lock, and 8 readers did fewer gets than 4
  (10.5.3, 10.5.4).
* **Other problems found on the way, not about pointers:** loads into an index larger than
  the budget slow to under 100 puts a second on s1's disk; the stream grows to about 1.1 KB
  per key at 100M keys loaded in random order; a cold-cache startup takes minutes on a slow
  disk, one header read per pointer of D (`DbStarter.linkD`); reads hold a pointer lock and
  FileStream's per-file monitor while they read the device (10.5.3, 10.5.5, 10.5.8).

## 2.4 Where that leaves 004

1. The reason to change eviction is to make it incremental: no stop-the-world. Today the
   sweep is what limits BergDB's worst case (half a second to minutes, readers and the
   writer waiting), and that is not acceptable. Any local eviction with bounded work and
   no walk of the resident set, handles (D) or a forest (C), removes it.
2. The hop's cost is measured and small: about a tenth of a lookup in memory, nothing beside
   a load. The concern of 004-01 that handles might be too dear for latest-time reads is
   mostly answered, which weakens the case for C over D.
3. 004-01's first recommendation is confirmed by 004-02 and independent of the choice: the
   pointer lock, the stamp and the per-get `readSync` are the ceiling in memory, and the
   pointer lock also serializes reads from the device.
4. The other problems of 2.3 (writes beyond the budget, the stream's growth, the cold
   startup, serialized device reads, long random keys) need their own work, whatever
   pointers BergDB has. The writes, the most serious of them, are registered as
   [005-38](../005-todo/38-writes-at-scale.md), to be investigated after incremental
   eviction is under way but before the Lean physical layer is redone for it: the sweep
   is part of the slow loads, and a fix of the write path may change what is pinned or
   written.
5. Not yet done: a prototype of handles (or of the forest) in BergDB itself, and a decision
   on whether and when to redo the Lean physical layer around it.



# 3. Open: the handle table

Noted 2026-10-24 by Claude, from a discussion with Frans; to be studied a bit more before
deciding. Frans: "Just having 4096 HashMaps to start with is not such a bad idea either.
It is simple, and I understand it."

The id-to-handle table is needed in any case, not only for eviction: when a stream pointer
is first followed, it must find the node's live handle if another parent already has the
node resident (the DAG), or there would be two handles and two objects for one node. Today's
node table (`Cache3`, 256 `HashMap`s, `MAP_BITS = 8`) is that table; in D the handle takes
`CacheEntry`'s place. The same table can serve eviction: CLOCK walks it a slice at a time,
or samples it into a cooling FIFO. Dead handles leave the table; only parents hold them.

The requirement: no stop-the-world when the table grows. A resize must be bounded, not
proportional to the number of resident nodes. The options:

* **Many HashMaps, as today but more (for example 4,096).** Simple and known. A resize
  rehashes one map: at 100M resident nodes about 24,000 entries, a short pause, but still
  growing with the database. About 60 bytes an entry (map node, boxed `Long`, the entry;
  an estimate, not measured).
* **Linear hashing (Litwin 1980).** Grows one bucket at a time: an insert splits at most one
  bucket, never a global rehash. Buckets chained through a `next` field in the handle (no
  entry object: about 8 to 10 bytes an entry), the bucket array in fixed-size chunks so
  growth never copies a large array. Bounded, compact, more code.
* **Incremental rehashing (as Redis).** Old and new table side by side during a resize, a
  few buckets moved per operation, lookups in both. Bounded, well tried; two tables during
  the move.
* **Sized from the budget.** Live handles are bounded by about the budget over the
  smallest resident node, so the table can start at that size and seldom grow. Not enough
  alone: no bound without eviction, and many small nodes with long random keys.
* Not `ConcurrentHashMap`: a lone inserting thread does the whole transfer, and it keeps the
  boxed key and the entry object.

The table is used only on the slow path (resolve, install, evict), so one monitor or a few
stripes may do at first: at 004-02's highest load rate, about 10^5 loads a second, one lock
is busy about 1 percent of the time.

To study: the pause of a resize at realistic sizes with many HashMaps (is it small enough
to accept?), the memory per entry of each option measured, and how
the eviction policy walks or samples each.

Frans's prototype of 2017, for reference: `java/src-dev/bergdb/test/java/MyLongMap.java`, a
map from id to node, its bins chained through a `next` field in the node and fixed at 2^21
(48 ns a get at 1M entries, on cissi, 2017-07-31), and `java/src-dev/frans/FastMap.java`.
Noted 2026-10-25 from a TODO marker on its fixed size (006-05, T3).
