004-01. Report: indirect swizzling for BergDB
=============================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-18, at Frans's request:
"Add an item in bergdb/items/ about indirect swizzling. Include the references. Include
the possibility of using this in BergDB, the pros and the cons. Study this deep, more
than we have in this session. Lookup references." It follows a discussion the same
morning about Level 4's caching: the sweeps, the multiple parents of the DAG, and a
pointer that goes through "a middle element" that always points to a node's latest
object. Code at bergdb `651ed45` (`java/build/bergdb.jar` of 06:59; `java/src` has not
changed since). Nothing outside this item was changed. The measurements were first made
on a machine shared with item 001's long trace checks, then repeated the same afternoon on
the quiet machine at Frans's request; the report's figures are the quiet ones (section
5.5). The tools and the raw outputs are in [01-report/](01-report/) (section 11).

Terms: "pointer" as in the Java code, a memory pointer or a stream pointer; "pointer i of
x" for the place (the Lean model and the Level 4 documents call it a slot).


## Summary

1. **What it is.** To swizzle a pointer is to replace a stored reference (in BergDB a
   stream position) by a memory address when the target is in memory. Direct swizzling
   puts the target's address in the pointer; to evict the target, every swizzled pointer
   to it must be found and turned back. Indirect swizzling puts the address of a small
   per-object descriptor (here: a handle) in the pointer, and the handle points to the
   object; to evict the object, only the handle changes. The idea is as old as
   persistent object stores (LOOM 1983, ORION 1988), was classified and measured by
   Kemper and Kossmann (1993, 1995), and lives on as the Bw-tree's mapping table (2013)
   and as the logical pointers of MVCC databases (section 2).

2. **BergDB swizzles directly, and evicts after a walk of all memory.** Its memory
   pointers are direct (the mixed pointers of the 2012 design). Level 4 releases an
   object only when no memory pointer of a resident object points to it, and it finds
   that out by walking every resident object, twice a sweep. Of the ways Kemper and
   Kossmann list for evicting with direct swizzling (reverse reference lists, a bounded
   table of swizzled pointers, or an inspection of all memory like a garbage
   collector's), this is the third. P4 measured its cost: 3.2 s per sweep at 1.6 GB,
   35 percent of the soak's time, throughput down to 62 percent (section 3).

3. **BergDB's memory is a DAG, so the modern fix for direct swizzling does not apply as
   it is.** LeanStore and Graefe et al. evict cheaply because every page has exactly one
   incoming pointer, which a parent pointer finds. In BergDB, 69 to 72 percent of the
   resident index objects, and 63 to 71 percent of the values, have more than one
   incoming memory pointer (1 million keys, after a load and after as many updates): a
   time split's old node and its replacement point to the same children, and the old
   node stays resident for older times (section 3.3).

4. **Indirection removes the multiple-parent problem from eviction.** With one handle per
   node, shared by every pointer to the node from any version, evicting a node is a
   change of its handle: no walk, no counts, no parent pointers, any replacement policy
   (CLOCK, or LeanStore's random choice with a cooling stage), bounded work per
   eviction. It also gives one object per node (no snapshots), exact accounting, and a
   clean split between the reference a record must contain (kept in the pointer, as
   today) and the object that serves reads (in the handle) (sections 4 and 6).

5. **On one thread, the extra hop costs no more than today's pointer lock and access
   stamp.** In a B-tree of Java objects shaped like BergDB's (IndirectionBench, Apple M1
   Pro, JDK 27, quiet machine): in cache, 64 ns a lookup with direct pointers, 71 to 72
   through handles, 83 with today's lock and stamp; out of cache (8 million keys), 517,
   564 to 583 and 586 ns. Where the handle lies matters: next to its object as above,
   scattered 874 ns. A hash lookup per edge costs 85 and 982 ns (section 5.1).

6. **With several readers, today's lock and stamp are the cost, and handles keep
   scaling.** Eight reader threads: in cache, 114 million lookups a second direct, 104
   through handles, 6.5 with lock and stamp; out of cache 13.7, 12.1 and 5.6 (four
   threads: 60, 53, 19 and 6.9, 6.1, 5.0). In BergDB itself, the lock and the stamp cost
   5 to 7 percent of a get on one thread; without them four threads do 25 to 64 percent
   more gets. With eight threads, today's gets do 2.4 million a second, fewer than with
   four; without the lock and the stamp 4.1, and without `readSync` too 8.7 (sections
   5.1 and 5.3).

7. **Memory: 24 bytes per handle** (measured, JDK 27's compact object headers). For
   4-byte keys and 16-byte keys with a shared prefix, one handle per index node is 3.9 to
   6.7 bytes per key with all history resident, 3 percent of the index's memory; under
   eviction, only resident nodes and their recently used children have handles. Values
   should not get handles (24 bytes on a 64-byte value): they are immutable and can stay
   behind direct pointers, dropped with their leaf. Random 16-byte keys are the
   exception: BergDB makes two single-entry key nodes per key for them, and handles cost
   52 bytes per key, 12 to 14 percent of the index (sections 4.6, 5.4 and 9).

8. **The change is large.** In Java: the pointer arrays, both followers, the node table,
   the writer's pointer creation and resolution, startup's linking, eviction, the
   registry and the audit. In Lean: the physical layer's eviction model and its proofs
   (about 11,400 lines in `lean/SIS/Evict.lean` and `lean/SIS/Proof/Evict*.lean`),
   around a simpler state. Records need not change, which StreamDigest can check. The
   literature warns as well: the JVM itself left handles for direct pointers (HotSpot),
   and the Bw-tree's mapping table costs it 18 percent on reads (sections 2.3, 2.5 and
   4.10).

9. **The alternatives** (section 7): an incremental sweep (direct pointers, the walk
   spread out); reverse reference lists or counts (Kemper and Kossmann measured direct
   swizzling with them as the slowest on updates); a forest of single-owner memory
   pointers with parent pointers, edges into history resolved by node id (LeanStore's
   way; context-specific swizzling in Kemper and Kossmann's terms); direct pointers with
   the garbage collector deciding when an object is free (BergDB's own 2017 `Cache2`);
   a hash lookup per edge.

10. **Recommendation** (section 8): first two changes that pay whatever comes next: no
    pointer lock and no write into a shared parent on the read path (recency kept in the
    child object or in a handle), and no `readSync` monitor and shared counter per get.
    Then a prototype of handles for index nodes on a branch, values with their leaves,
    records unchanged, measured on J10's gets, gets from 4 and 8 threads, P4's soak with
    eviction and LargerThanMemory; beside it, if the hop proves too dear for latest-time lookups,
    a prototype of the forest. Decide before the Lean model is redone.


## 1. Terms

From the literature (Moss 1992; Kemper and Kossmann 1995, section 3):

* **Swizzle, unswizzle.** Replace a persistent reference (an object identifier, a page
  id, a stream position) by a memory address, and back.
* **Eager or lazy.** Swizzle every reference of an object when it is loaded, or each
  reference when it is first used ("upon discovery" or "upon dereference", White and
  DeWitt 1992).
* **Direct or indirect.** The swizzled reference holds the target's address, or the
  address of a descriptor that holds the target's address while it is in memory.
  **Optimistic** swizzling is direct swizzling without eviction.
* **In place or copy.** The reference is rewritten in the object itself, or in a separate
  in-memory copy.
* **Reverse reference list (RRL).** For direct swizzling with eviction: per object, the
  swizzled references to it, so that they can be turned back when it is evicted.
* **Fan-in.** The number of swizzled references to an object.
* **Descriptor, handle, mapping-table entry.** The middle element of indirect swizzling.
  A mapping table is an array or a map of them, indexed by logical id.
* **Single owner.** A structure in which every object has exactly one incoming pointer
  (a tree, a forest), so that a parent pointer replaces an RRL.

BergDB's terms, as in [docs/levels.md](../011-docs-archive/04-levels.md) and
[docs/level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md): a **node** (node id) has
**versions** in the stream (positions); lv(y) is node y's latest version. An **object** is
a Java `Node` in memory. A **canonical object** is the one object of a node that the
writer reads and changes; it holds the node's whole history (CC) and, for a clean written
node, exactly lv(y) (INV-CAN). A **snapshot** is any other resident index object, exactly
the version at its position (INV-SNAP); a snapshot is not necessarily an old version. An
object is **resident** when memory pointers reach it from the super root, the node table
or D. **Pinned** objects (D's canonical objects, the record being written, the super root,
the newest written top node) are never evicted. **TREE**: every node reachable at a time,
the root aside, is the live child at that time of exactly one node reachable then
(level4-alignment.md, section 4).


## 2. The literature

### 2.1 Object stores, 1983 to 1995

Pointer swizzling comes from persistent programming languages and object databases.
Objects are named by object identifiers (OIDs); a resident object table maps an OID to
the object's address, and every access by OID pays that lookup. Swizzling stores the
address in place of the OID so that later accesses are a memory reference. PS-algol
(Atkinson et al. 1983) and LOOM, the large object-oriented memory of Smalltalk-80
(Kaehler and Krasner 1983), pioneered it (Kemper and Kossmann 1995, section 3.2). LOOM
and ORION swizzled eagerly and indirectly; PS-algol and the E language's EPVM 2.0 lazily
and optimistically (Kemper and Kossmann 1995, table 2).

Moss (1992) made the first systematic classification, for sessions without eviction; he
found lazy swizzling up to 10 percent slower than eager swizzling for pure lookups (as
reported by Kemper and Kossmann). White and DeWitt (1992) distinguished swizzling upon
discovery from swizzling upon dereference. The "hardware" school swizzled whole pages at
page-fault time with virtual memory protection: Wilson's Texas persistent store (Wilson
1991; Wilson and Kakkad 1992), ObjectStore and QuickStore (White and DeWitt 1994).
Kemper and Kossmann chose software swizzling over that, for logical OIDs, explicit buffer
management and cheaper faults (section 3.3 of their paper); Crotty, Leis and Pavlo (2022)
give today's version of the argument against leaving eviction to the operating system.

### 2.2 Kemper and Kossmann: direct or indirect

Kemper and Kossmann ("Adaptable pointer swizzling strategies in object bases", ICDE 1993;
the long version in the VLDB Journal 4(3), 1995, read in full for this report) are the
reference for swizzling with eviction. Their classification asks two questions: when is a
reference swizzled (eager, lazy), and what precaution is taken for replacement (direct
with RRLs, indirect with descriptors, none). That gives EDS, EIS, EOS, LDS, LIS, LOS and
NOS (no swizzling).

* **Direct swizzling needs reverse references.** "If an object is displaced from the
  system buffer (i.e., is no longer resident), all the directly swizzled references that
  refer to the displaced object need to be unswizzled." They record them in an RRL per
  object. Eager direct swizzling also has a "snowball effect": loading an object loads
  what it points to, evicting one evicts its referrers.
* **Two ways around RRLs, both for direct swizzling.** A routine that "works like a
  compacting garbage collector inspects all the main-memory buffers and reclaims the main
  memory space that is occupied by unreachable objects", finding the swizzled references
  to objects not used for a long time on the way. And McAuliffe and Solomon's swizzle
  table (1995), a bounded hash table of directly swizzled references, which they found not
  very attractive.
* **Indirect swizzling.** "Indirect swizzling totally avoids the overhead of recording
  reverse references by permitting the swizzling of references that refer to non-resident
  objects." A swizzled reference points to a descriptor; the descriptor holds the
  object's address when it is resident and is marked invalid when not; evicting the object
  invalidates the descriptor only. Descriptors are reclaimed by a counter of the
  references to them, "much cheaper than maintaining an RRL". The price: "an additional
  indirection, due to the descriptor, and ... a residency check" on every lookup.

Their measurements (a SPARCstation 1, the GOM object manager on EXODUS; the ratios are
what carries over):

| Operation | Direct | Indirect | No swizzling |
|---|---|---|---|
| Read a reference field, µs (table 5; transient C: 0.9) | 6.7 eager, 7.1 lazy | 7.4 eager, 7.8 lazy | 26.4 |
| Swizzle and unswizzle a reference, µs, fan-in 1 to 8 (table 6) | 59.2 to 85.0, growing with fan-in | 33.6, constant | — |
| The Update operation, hot, µs (table 9) | 299 eager, 289 lazy (worse than none by 33 and 28 percent) | 96 eager, 113 lazy (better by 57 and 50 percent) | 225 |
| Memory | 12 bytes per RRL entry | 24 bytes per descriptor | — |

In the OO1 benchmark's small objects, descriptors or RRLs took 43 percent of the memory
under eager swizzling (their worst case). Hot traversals saved up to 70 percent against no
swizzling with eager indirect swizzling. Their conclusion: "there is no one superior
pointer swizzling strategy for all application profiles". So they built an adaptable
object manager that chooses per application, per type, or per **context**, the place where
the reference is stored. Context-specific swizzling was best in their mixed workloads (16
percent better than the best uniform strategy on traversals with lookups, 23 percent on
updates). Section 7 comes back to this: BergDB has two natural contexts, pointers of the
current tree and pointers into history.

### 2.3 The JVM made the same choice

Sun's Classic VM represented object references as handles: a reference pointed to a
handle that pointed to the object, so that the garbage collector could move objects by
changing one word. The HotSpot VM replaced them with direct pointers for faster access to
instance variables (Oracle, "The Java HotSpot Performance Engine Architecture"; seen only
as a search summary, the page refused the fetch). HotSpot could, because its collector
finds and updates every reference while it moves objects: the same trade as here, with
the collector in the role of BergDB's sweep. Java 27 makes compact object headers the
default (JEP 534: 64 instead of 96 bits), so a handle with a reference, a long and a byte
takes 24 bytes (measured, section 5.4).

### 2.4 Swizzling in buffer managers, 2014 to 2023

**Graefe, Volos, Kimura, Kuno, Tucek, Lillibridge and Veitch, "In-Memory Performance for
Big Data", PVLDB 8(1), 2014** (read). A traditional buffer pool translates a page id
through a hash table on every page access; with the working set in memory that is a
large share of the cycles. They swizzle parent-to-child pointers in B-tree pages (the
pointer becomes the buffer frame's number), lazily, one at a time, and keep page
identifiers for everything else. Un-swizzling must find the parent, so they use Foster
B-trees, in which "every node in the B-tree has at most a single incoming pointer at all
times (which simplified book-keeping for unswizzling)", and they propose child-to-parent
pointers in the frame descriptors. Eviction uses a generalized clock; a depth-first sweep
un-swizzles pages without recent use, never a parent of swizzled children. Result:
read-only lookups within 1 to 3 percent of an in-memory database while the working set
fits, graceful degradation beyond it. They note that Kemper and Kossmann's indirect
swizzling serves "to permit evicting an object from memory without un-swizzling all
pointers to this object".

**Leis, Haubenschild, Kemper and Neumann, "LeanStore: In-Memory Data Management Beyond
Main Memory", ICDE 2018** (read). A "swip" is an 8-byte reference that holds either a
pointer or a page id, told apart by one bit, so a hit costs "one conditional statement".
"In LeanStore, each page has a single owning swip, which avoids consistency issues when it
is (un)swizzled. Consequently, each buffer-managed data structure becomes tree-like and
the buffer pool in its entirety a forest of pages." Parent pointers in the buffer frames
find the owner; a page with swizzled children is never unswizzled. Replacement does no
work on a hit: random pages are speculatively unswizzled into a cooling stage (a FIFO
queue with a hash table, about 10 percent of the pool); a page touched while cooling is
swizzled again, one that reaches the end is evicted. Epochs protect readers, optimistic
latches replace page latches. TPC-C in memory, one thread: 67,000 transactions a second
against 69,000 for an in-memory B-tree, 10,000 for BerkeleyDB and 16,000 for WiredTiger.
Turned on one at a time, from a traditional design: 30,000 (hash table, LRU, latches),
48,000 with swizzling, 62,000 with the cheap replacement, 67,000 with optimistic latches;
on 10 threads 18,000, 23,000, 109,000 and 597,000. A trace with a 1 GB pool over 5 GB
(Zipf 1.0) gave hit rates of 92.5 percent (random, FIFO), 92.7 to 93.0 (LeanStore),
93.1 (LRU), 93.8 (2Q) and 96.3 (optimal). Multiple incoming pointers "would also be
possible", by several parent pointers per frame or by "fat" swips holding both a page id
and a pointer.

**Neumann and Freitag, "Umbra", CIDR 2020** builds variable-size pages on LeanStore's
swizzling. **Leis, Alhomssi, Ziegler, Loeck and Dietrich, "Virtual-Memory Assisted Buffer
Management" (vmcache), SIGMOD 2023** (introduction and comparison read) sums up the state
of the art: swizzling "requires adaptations for every buffer-managed data structure";
"to unswizzle a page, one needs to find and lock its parent, and storing a parent pointer
on each node presents synchronization challenges during node splits"; and "pointer
swizzling-based systems generally do not support more than one incoming reference to any
particular page. In other words, only tree data structures are directly supported. Graph
data, next pointers in B+tree leaf pages, and multiple incoming tuple references ...
require inelegant and sometimes inefficient workarounds." vmcache translates page ids by
the processor's page tables instead (anonymous memory, `MADV_DONTNEED`, an `exmap` kernel
module for scalability): a hardware indirection that supports graphs. It works on pages of
raw memory, not on Java objects.

### 2.5 Indirection as a design: the Bw-tree's mapping table

**Levandoski, Lomet and Sengupta, "The Bw-Tree: A B-tree for New Hardware Platforms",
ICDE 2013** (read in part), with LLAMA (PVLDB 6(10), 2013). The cache layer keeps a
mapping table "that maps logical pages to physical pages, logical pages being identified by
a logical "page identifier" or PID"; it "translates a PID into either (1) a flash offset
... or (2) a memory pointer". All links between nodes are PIDs. Changes are delta records
installed by a compare-and-swap on the page's mapping-table entry, "the only physical
pointer change necessary to install a page update"; a page can move, be consolidated or be
swapped out to flash without touching its parents; epochs reclaim memory. SQL Server's
Hekaton uses it for range indexes. In memory it ran 18.7 times BerkeleyDB on an Xbox
workload.

**Wang, Pavlo, Lim, Leis, Zhang, Kaminsky and Andersen, "Building a Bw-Tree Takes More
Than Just Buzz Words", SIGMOD 2018** (read in part) is the independent evaluation: the
mapping table is a large preallocated array indexed by node id; "the overhead of the
Bw-Tree's indirection layer and delta records causes it to under-perform the lock-based
indexes by 1.5–4.5×". Taking the mapping table out (direct pointers inside inner nodes):
"Read performance increases by 18% due to fewer cache misses for load instructions (L1:
32% lower; L3: 52% lower)." With every lock-free feature taken out it was still 15 to 19
percent slower than a B+tree with optimistic lock coupling. The indirection is not free,
and the lock-free machinery around it costs more.

### 2.6 Logical pointers to versions: MVCC

**Wu, Arulraj, Lin, Xian and Pavlo, "An Empirical Evaluation of In-Memory Multi-Version
Concurrency Control", PVLDB 10(7), 2017** (sections 6 and 7.5 read). A secondary index of
an MVCC database points either to a fixed tuple id, which an indirection layer maps to the
head of the tuple's version chain ("logical pointers"), or to an exact version ("physical
pointers", as in Hekaton and MemSQL). With physical pointers every new version must be
entered in every index; with logical pointers only the mapping changes. Logical pointers
won on update-intensive work: 25 percent more throughput under high contention, 40 percent
with 20 secondary indexes, 45 percent with eight secondary indexes under high contention;
reads are somewhat slower. This is Frans's "middle element that always points to the latest
version", in a database: the indirection redirects every referrer at once.

### 2.7 Multiversion structures have multiple parents

[docs/prior-art.md](../011-docs-archive/02-prior-art.md) reviews the structures BergDB descends from.
What matters here:

* **Driscoll, Sarnak, Sleator and Tarjan (1989).** Node copying keeps, in each node, a
  pointer back for each incoming pointer, so that a copy can be linked in; it assumes a
  bounded in-degree (MIT 6.854 notes). With copying and multiple parents, a structure
  needs reverse pointers or an indirection.
* **The Write-Once B-tree, the TSB-tree (Lomet and Salzberg 1989) and the MVBT (Becker
  et al. 1996)** are DAGs: old and new nodes point to the same children. In the
  TSB-tree, "only historical nodes have more than one parent". BergDB is the same: TREE
  holds for the live pointers of current nodes, and history adds the other parents.
* **Immortal DB** (Lomet et al. 2005) keeps such history inside SQL Server.

### 2.8 Replacement policies cheap enough for in-memory speed

Classic LRU writes on every hit. CLOCK (second chance) sets one bit on a hit; 2Q (Johnson
and Shasha 1994) adds a probationary queue against scans; LeanStore does nothing on a hit
and finds cold pages by random speculative unswizzling with a cooling stage, with hit
rates within a point of LRU and 2Q in its trace (2.4). TinyLFU (Einziger, Friedman and
Manes 2017; Java's Caffeine cache) decides admission from approximate frequencies, which
keeps scans and one-off reads out. All of these need, per cached object, a place to keep a
bit or a state that the reader can reach without a lookup and without writing into a
shared parent: a handle is such a place, and so is the object itself.

### 2.9 What the literature says, in short

* Direct swizzling is the fastest on hits. With eviction it needs to find the pointers to
  a victim: reverse references (expensive on updates, and with fan-in), a whole-memory
  inspection (a stop-the-world pass), or a single owner per object (a tree or forest, with
  a parent pointer). The successful modern systems all chose the single owner.
* Indirect swizzling makes eviction and relocation local and works for graphs, for one
  more dependent memory access per hop and a descriptor per object. Measured costs: about
  10 percent on lookups in 1995's object stores, 18 percent on the Bw-tree's reads in
  2018. It wins where objects move, are replaced or are evicted often, and where many
  references point to one object.
* No strategy is best everywhere; choosing by context is better than one uniform rule.


## 3. BergDB today, in these terms

### 3.1 Lazy, direct, in-place swizzling since 2012

BergDB's mixed pointers (self-indexed streams v5, January 2012; prior-art.md, 5.1) are
lazy, direct and in place: a pointer of a key node or a top node is either a memory
pointer to an object or a stream pointer, the pair `pointers[i]` and `pos[i]`, and the
first follow of a stream pointer loads the target and makes the pointer a memory pointer
(`NodeCollection.followStreamPointer`). The loader takes the node's canonical object from
the node table if it has one, else exactly the version the pointer names after Rule R, as
a snapshot that the table does not get.

Every follow, also of a memory pointer, takes one of 128 striped monitors
(`PointerLocks`: `node.hashCode() + 13 * i`) and writes the operation's access stamp into
`pos[i]` of the parent (`KeyNode.setPointerAccessData`). Every get also enters and leaves
the global `readSync` monitor and increments a shared counter (`aux.getOpCount`).

### 3.2 Eviction: direct swizzling without reverse references

Level 4 (item 001, J1 to J10; [Eviction.java](../../java/src/bergdb/core/Eviction.java))
unswizzles a memory pointer to a detachable object (clean, written, not pinned) by writing
the object's position into it, and releases the object when no memory pointer of a
resident object points to it any more (node table entry, canonical flag, registry). To
know that, a sweep walks every resident object from the super root, the node table and D
(`Residents.walk`), counts the memory pointers to each object, sorts the candidate
pointers by age, unswizzles the oldest, counts what leaves with each released object
(`drop`), and walks everything again to make the byte count exact; a complete sweep
follows under pressure. It is Kemper and Kossmann's garbage-collector-like inspection,
done under the write lock.

Its cost grows with the resident memory, not with what it frees: 1.5 s on average and
2.2 s at most at a 500 MB budget (J8), 3.2 s on average at 1.6 GB in P4's soak, every 9
seconds or so, 35 percent of the time, which brought the paced writer down to 62 percent
([level4-evidence.md](../001-lean-model-levels-3-4/10-level4-evidence.md)). Item 001 lists the options for K5
as an incremental sweep or incoming-reference lists, the RRLs of 2.2
([level4-plan.md](../011-docs-archive/05-level4-plan.md), sections 1 and 4.3).

### 3.3 Most resident objects have more than one parent

IndexCensus (section 5.2) counts, in a database of 1 million keys held in memory with
infinite retention, the memory pointers of resident objects to each object:

| Keys, phase | Resident index objects | Not current | In-degree above 1: index objects | In-degree above 1: values |
|---|---|---|---|---|
| 4-byte, after the load | 162,499 | 51 percent | 69.2 percent | 71.2 percent |
| 4-byte, after 1 million updates | 278,789 | 60 percent | 72.2 percent | 62.8 percent |
| 16-byte, shared prefix, after the load | 162,794 | 51 percent | 68.9 percent | 71.3 percent |
| 16-byte, shared prefix, after the updates | 278,767 | 60 percent | 71.8 percent | 62.9 percent |
| 16-byte, random, after the load or the updates | 2,162,535 | 4 percent | 38.1 percent | 0 |

The reason is the time split and the space split (`Dag.handleFullNode`): the replacement
gets copies of the replaced node's live pointers, and the replaced node, no longer
current, stays reachable for older times with its own pointers to the same children and
values. New super roots copy the skip pointers of the old one, and readers put canonical
objects into the pointers of snapshots. So the in-memory graph is a DAG even right after
a load, and an object's in-degree is mostly 2 to 4 (the histograms are in
[01-report/out/](01-report/out/)). This is why release needs global knowledge in BergDB,
and why the single-owner designs of 2.4 do not fit without a change of which pointers may
be memory pointers (section 7, option C).

### 3.4 The read path's cost today

IndexCensus also times random gets at the latest time on BergDB's own code, with the
readers' follower as it is and with one that takes a memory pointer without the lock and
without the stamp (safe in that measurement only: no eviction, one thread or readers
only):

| Keys, phase | ns a get, as it is | without lock and stamp | 4 threads, million gets a second: as it is | without lock and stamp | and without `readSync` |
|---|---|---|---|---|---|
| 4-byte, load | 709 | 671 | 3.63 | 4.63 | 5.10 |
| 4-byte, updates | 823 | 769 | 3.34 | 4.19 | 4.51 |
| 16-byte prefixed, load | 783 | 733 | 2.99 | 4.47 | 4.78 |
| 16-byte prefixed, updates | 900 | 836 | 2.39 | 3.91 | 4.13 |
| 16-byte random, load | 929 | 884 | 2.71 | 3.65 | 3.80 |
| 16-byte random, updates | 1,128 | 1,060 | 2.14 | 3.10 | 3.36 |

And with 2 and 8 threads (4-byte keys, after the load, two repeated measurements each):

| Threads | As it is | Without lock and stamp | And without `readSync` |
|---|---|---|---|
| 2 | 1.59, 1.69 | 2.50, 2.33 | 2.58, 2.46 |
| 8 | 2.37, 2.44 | 4.09, 3.80 | 8.74, 8.85 |

On one thread the lock and the stamp are 5 to 7 percent of a get. Without them, four
threads do 25 to 64 percent more gets, and without the per-get `readSync` another 4 to 10
percent more. With eight threads, today's gets scale backwards: 2.4 million a second against
3.6 with four. Without the lock and the stamp they reach about 4, and without `readSync`
too 8.7 to 8.9, more than six times one thread; the global monitor of every get is then
the larger cost. J10 measured 1.30 million gets a second on one thread and 3.5 million on
four, with another data set ([level4-performance.md](../001-lean-model-levels-3-4/11-level4-performance.md)).
Masstree's design rule is the opposite of today's read path: its readers "acquire no
locks whatsoever, and in fact never write to globally-accessible shared memory" (Mao,
Kohler and Morris 2012, section 4.4).

### 3.5 Handles BergDB already has, and had

* **Cache3's entries.** The node table maps a node id to a `CacheEntry` holding the node's
  canonical object and a `refCount`. That entry is a handle in all but use: one per node,
  always pointing to the node's canonical object. The parents point past it, to the
  object. `refCount` is incremented by `pointerCreated` and never decremented: nothing
  calls `pointerDestroyed`, in the 2017 code or now. It is Kemper and Kossmann's
  descriptor fan-in counter, unfinished.
* **Cache2** (in the 2017 code, never wired in;
  [Cache2.java](../../java/src/bergdb/core/Cache2.java)). A canonicalizing map of weak
  references from node id to node, split in 100 maps, and an evictor that, a few maps at a
  time, unswizzles the outgoing memory pointers of clean nodes whose access stamp is old;
  the JVM's garbage collector then decides when a node has no incoming memory pointer
  left, and reference queues clean the maps. That is the garbage-collector approach of
  2.2 done incrementally, with the collector doing the in-degree count. level4-plan.md
  (4.3) notes that its eligibility and synchronization rules are not a validated
  substitute.


## 4. Indirect swizzling in BergDB: a design sketch

A sketch, to make the pros and cons concrete and to find the obligations. It is not a
plan of work, and nothing of it is implemented.

### 4.1 The handle and the pointer

```java
// One per index node that has a resident object, or a pointer of a resident object to it.
final class Handle {
    final long id;              // the node id
    volatile Node obj;          // the node's one object: canonical, or the newest version loaded
    long writtenPos;            // the position this process last wrote the node at, or none
    byte state;                 // CLOCK bit, cooling, dead
}
```

Pointer i of a key node or a top node keeps both halves, with new meanings:
`pointers[i]` holds the target's handle, or null until the pointer is first followed;
`pos[i]` always holds a serialized reference, the stream position (or vpos) the pointer
named when it was made, loaded or last written. Today `pos[i]` holds the access stamp
while the pointer is a memory pointer; the stamp moves to the handle. The node table maps
a node id to its one live handle; `Cache3.CacheEntry` becomes the handle. Values get no
handle (4.6).

32 bytes per handle with the id, 24 without (section 5.4). The id is needed to
re-resolve a pointer whose handle has died (4.5) without reading the target's header.

### 4.2 Reading

* **Fast path, no lock and no shared write:** `h = pointers[i]`; `o = h.obj` (an acquire
  read); if `o` is canonical, or `o.spos` is at least the pointer's reference, use `o`;
  set the handle's CLOCK bit if it is clear.
* **Slow path:** if the pointer has no live handle, find the node id (a vpos is the id;
  else the header at the position, as today, or the dead handle's id), get or make the
  table's handle, and set it in the pointer by a compare-and-swap. Then, if the handle's
  object is missing or older than the pointer's reference after Rule R, read a version:
  the pointer's own, or the newest this process wrote (`writtenPos`) if that is newer.
  Install it in the handle under the handle's monitor, unless a canonical or newer object
  got there first.

Correctness rests on lemma M, which is proved for the model (`LM_newer`, `LM_ruleR` in
`lean/SIS/PhysTheorems.lean`): a version at a later position serves every lookup time an
earlier version serves; and on CC: a canonical object serves every time. So a handle may
hold the newest version seen, and every pointer to the node can use it. There are no
snapshots any more, only "the node's object", canonical or not, never older than what was
installed before.

### 4.3 The writer

The writer follows like a reader and then needs the canonical object: if the handle's
object is not canonical, it must be lv(y), which the writer's pointer names (a pointer of
a current node names lv(y), INV-SLOT; or y is pinned and has its canonical object). The
writer loads lv(y) if the handle holds an older version, and marks it canonical under the
handle's monitor. One canonical object per node then holds by construction: there is one
live handle per id. A node the writer makes gets its handle at once. Splits copy pointers
as pairs (handle, position), as they copy (object, position) pairs today. When the writer
writes a node, it sets the handle's `writtenPos`.

### 4.4 Records stay the same

The serialized reference of pointer i of x would be: the canonical object's position if
the pointer's handle holds a canonical object (what a memory pointer to a canonical object
serializes today), else the larger of the pointer's position after Rule R and the handle's
`writtenPos` (a vpos handled as Rule R does).

The obligation is an INV-SLOT for this representation: for x current or in D, this is
lv(y) or y is pinned. The argument: by today's INV-SLOT, a pointer of such an x names
lv(y) unless y is pinned (level4-alignment.md, 5.4); a pinned y has its canonical object
in its handle; `writtenPos` is the position of the writer's last write of y, which is
lv(y) once y is written, and never more than lv(y). Readers never change a pointer's
position or `writtenPos`, so the record does not depend on what reads left in memory: the
requirement of level4-plan.md (4.4), and the class of M21 and M27, by construction. To
be proved, and checked with StreamDigest (every record the same as today's) and
EvictionInvariance.

### 4.5 Eviction

An object is evictable when it is not pinned and written; nothing is asked about incoming
pointers. To evict it, under the handle's monitor: set `writtenPos` from a canonical
object's position, mark the handle dead, clear `obj`, remove the table's entry, and
subtract the bytes. Readers holding the object finish with it (the garbage collector keeps
it). Parents keep the dead handle until they are followed (a re-resolution: one table
lookup by the dead handle's id and a compare-and-swap of the pointer) or evicted
themselves. A dead handle never gets an object again, so there is never more than one live
handle, and one object, per node.

The policy can be anything with a bit or a state per handle: CLOCK over the table's
array, or LeanStore's random choice into a cooling FIFO, which here needs no parent:
cooling and reheating change the handle's state only. The work per eviction is bounded,
and nothing walks the resident set. The simplest placement is today's: bounded batches
under the write lock at transaction boundaries and after loads, without the walks. A
background evictor needs a pin check made atomic with the writer's marking, a later step.

The handles themselves: live handles for resident objects; dead handles until their
parents re-resolve or go. Under eviction their number is bounded by the resident nodes
and the children their pointers have been followed to; for index nodes, about as many as
the node table's entries today.

### 4.6 Values

A value has one version and never changes. It needs no handle, and a handle per value
would cost 24 bytes on a value object of 64 (an 8-byte value; section 5.4). A leaf's
pointer to a value stays direct. Values go with their leaf: when the leaf's object is
evicted and no reader holds it, the garbage collector frees it and every value no other
resident leaf points to. Unswizzling a single value pointer in a leaf is also safe at any
time once the value's record is written (its position is then in `pos[i]`); only the
accounting does not know whether the value is freed, so value bytes are charged to the
leaf that loaded them, a shared value more than once (conservative). Values leave the
node table, which they are in today only because `pointerCreated` enters them. Large
values (over 1 MiB) stay uncached, as today.

### 4.7 Startup

Startup reads what it reads today: Rule R from the startup section, D's canonical objects,
the super root. Rule 4 (`DbStarter.linkD`) becomes "D's pointers resolved to handles by
id". No directory of every node's latest position is needed: a pointer's own position
after Rule R is always good for the lookups that use it (lemma M), the pointers of current
nodes name lv(y) (INV-SLOT), and the handle keeps the newest version seen. So startup is
as fast as today, and level4-plan.md's advice against "a permanent latest-position
directory" holds.

### 4.8 Concurrency

The fast path takes no lock and writes nothing shared but a CLOCK bit when it is clear.
`pointers[i]` is published by the writer as today (the node's volatile size) or by a
compare-and-swap; `obj` by an acquire read. The slow paths (resolve, install, promote,
evict) take the handle's monitor; they are rare, and a load holds no lock while it reads
the stream if the monitor is only taken to install. `PointerLocks` leaves the read path.
Java's garbage collector does what epochs do in LeanStore and the Bw-tree: an evicted
object stays valid for a reader that holds it. The writer's appends to a canonical object
work as today (append-only arrays published by `size`).

### 4.9 The Lean model

The physical state would become: a table from node id to a handle (an object or none,
`writtenPos`, dead or not), and per object, per pointee, a reference and whether it is
resolved. A pointer names a node, not an object, so there are no dangling pointers and no
eligibility condition on incoming pointers: eviction is "not pinned and written". The
invariants: one object per live handle and one live handle per node (by construction);
the object is canonical with its node's whole history (CC, INV-CAN) or an exact version
(INV-SNAP); the serialization invariant of 4.4 in place of INV-SLOT's two halves. T-CACHE
(any cache schedule gives the model's records and D) and T-READ (reads give P) would be
restated over that state, reusing lemma M and the Level 2 and 3 theorems. The statements
get simpler; the proofs of the physical layer would be redone.

### 4.10 What the change touches

Java: `KeyNode` and `TopNode` (pointer arrays, `pos` without access data), `NodeCollection`
(both followers, maintenance reads), `Cache3` (handles), `Dag` (new pointers to a new or
existing node take its handle), `resolvePointers` (the rule of 4.4), `DbStarter` (rule 4),
`Eviction` (replaced: no walks), `Residents` (exact accounting), `Audit`, `PointerLocks`,
and their tests; all four level scripts. Lean: `Phys.lean`, `Evict.lean` and the
`Proof/Evict*.lean` files, and the checker's C-P. Documents: level4-alignment.md and
levels.md. The stream format and the records do not change.


## 5. Measurements

### 5.1 The pointer follow: IndirectionBench

[IndirectionBench.java](01-report/IndirectionBench.java) builds a B-tree of Java objects
shaped like BergDB's key nodes (arrays of 30 slots, 16 used, a linear search in each node,
a value object under each leaf entry) and does random lookups. Only the way an edge is
followed differs: `direct` (a Java reference); `lockstamp` (BergDB's pattern: the striped
monitor, the reference read and the stamp written into the parent's `pos[i]` under it);
`lock` and `stamp` (each half alone); `handle` (through a handle, plain read), `handleacq`
(an acquire read of the handle's object), `handleclock` (and a CLOCK bit set when clear);
`hash` (the child found by id in an open-addressing map of primitive longs) and `chm`
(`ConcurrentHashMap<Long, Object>`). 20,000 keys (1,250 leaves, 5 edges a lookup, in the
processor's caches) and 8 million keys (7 edges, about 550 MB). Each variant in a JVM of
its own (`-Xms4g -Xmx4g`, G1, JDK 27 with compact headers), 7 rounds of 2 or 4 million
lookups, the median of the last 5. Apple M1 Pro (8 performance and 2 efficiency cores).

Nanoseconds per lookup on one thread, and million lookups a second for 2, 4 and 8
threads (handles allocated just before their objects, layout `before`; quiet machine):

| Variant | 20,000 keys: 1 thread, ns | 2 threads, M/s | 4 threads, M/s | 8 threads, M/s |
|---|---|---|---|---|
| direct | 63.8 | 30.8 | 59.8 | 113.9 |
| lockstamp (today) | 83.2 | 14.3 | 18.8 | 6.5 |
| lock | 78.9 | 17.6 | 27.7 | 12.5 |
| stamp | 66.1 | 20.6 | 37.6 | 29.2 |
| handle | 70.7 | 27.4 | 53.2 | 103.6 |
| handleacq | 72.1 | 27.2 | 52.8 | 103.5 |
| handleclock | 72.4 | 26.9 | 52.1 | 101.5 |
| hash | 85.2 | 22.9 | 44.9 | 85.4 |
| chm | 102.5 | 19.1 | 37.1 | 72.2 |

| Variant | 8 million keys: 1 thread, ns | 2 threads, M/s | 4 threads, M/s | 8 threads, M/s |
|---|---|---|---|---|
| direct | 517 | 3.72 | 6.91 | 13.71 |
| lockstamp (today) | 586 | 3.05 | 5.04 | 5.64 |
| lock | 549 | 3.26 | 5.87 | 9.46 |
| stamp | 532 | 3.38 | 6.27 | 11.03 |
| handle | 564 | 3.25 | 6.12 | 12.23 |
| handleacq | 583 | 3.20 | 6.14 | 12.05 |
| handleclock | 566 | 3.24 | 6.24 | 12.24 |
| hash | 982 | 1.95 | 3.71 | 7.35 |
| chm | 1,104 | 1.71 | 3.26 | 6.11 |

Where the handle lies (`handleacq`, one thread, ns): next to its object's header and
first array (`before`) 72 and 583; after the object and its arrays (`child`) 74 and 710;
with the parent's other handles (`parent`) 72 and 647; in random order (`scattered`) 76
and 874.

What it shows:

* **Per edge, one thread:** in cache, today's lock and stamp cost about 4 ns, a handle
  1.4 to 1.7 ns, a hash lookup 4 ns. Out of cache, the lock and stamp about 10 ns, a
  handle next to its object 7 to 9 ns, a scattered handle 51 ns (a cache miss on most
  hops), a hash lookup 66 ns. A handle is never dearer than today's lock and stamp.
* **Placement is most of the cost out of cache.** A handle allocated just before its
  object shares or neighbours its cache lines; a loader that makes the handle first and
  then reads the node gets that placement. A scattered handle is a second miss per hop.
* **With several readers, the monitor and the stamp are the problem.** Each lookup takes
  the same few monitors near the root, and the stamp writes into the root's arrays. In
  cache, today's pattern does fewer lookups with 8 threads (6.5 million a second) than
  with one (12.0); direct pointers do 114 million. Out of cache it reaches 2.4 times
  less than direct with 8 threads. Handles keep 87 to 91 percent of direct's throughput
  at 4 and 8 threads, and scale like it.
* **A hash lookup per edge** (the KISS design) is the slowest that is reasonable: 1.3 to
  1.9 times direct on one thread.

### 5.2 BergDB's index: IndexCensus

[IndexCensus.java](01-report/IndexCensus.java) runs BergDB as it is (`bergdb.jar`), in
memory, with infinite retention and no eviction: 1 million keys loaded in random order,
1,000 a transaction, then 1 million uniform updates, 10 a transaction; 8-byte values, node
size 30. Key types: `int4` (4-byte big-endian), `pre16` ("account:" and an 8-byte id),
`rnd16` (8 bytes of a hash of the id, then the id).

| | int4, load | int4, updates | pre16, load | pre16, updates | rnd16, load | rnd16, updates |
|---|---|---|---|---|---|---|
| Index nodes of the latest tree | 80,183 | 110,727 | 80,363 | 110,428 | 2,080,196 | 2,080,196 |
| Keys per such node | 12.47 | 9.03 | 12.44 | 9.06 | 0.48 | 0.48 |
| Resident index objects (every node so far) | 162,499 | 278,789 | 162,794 | 278,767 | 2,162,535 | 2,162,535 |
| Per key | 0.162 | 0.279 | 0.163 | 0.279 | 2.163 | 2.163 |
| Their memory (`getMemSize`), MB | 119.3 | 220.7 | 119.4 | 220.7 | 375.3 | 451.4 |
| Values, MB | 64.0 | 128.0 | 64.0 | 128.0 | 64.0 | 128.0 |
| Index objects with in-degree above 1 | 69.2 % | 72.2 % | 68.9 % | 71.8 % | 38.1 % | 38.1 % |
| Values with in-degree above 1 | 71.2 % | 62.8 % | 71.3 % | 62.9 % | 0 | 0 |

The node density agrees with J8 (12.4 keys per index node at 20 million keys). The latest
tree alone is 53 bytes of index memory per key after the load and 86 after the updates.

### 5.3 BergDB's read path

The tables of section 3.4. One thread: lock and stamp 5 to 7 percent of a get; the rest
is the search in the nodes, the top-node skip list, the segments and the value. Four
threads: 25 to 64 percent more gets without the lock and the stamp, 4 to 10 percent more
again without `readSync`. Eight threads: today's gets do fewer than four; leaving out the
lock and the stamp gives 1.7 times as many, and leaving out `readSync` too another 2.1
times. The shared counter
`aux.getOpCount` could not be left out without changing the code; it is one more shared
write per get, and may be part of what keeps eight threads at 6.2 times one.

### 5.4 The memory of handles

Measured by allocation (IndirectionBench `sizes`, JDK 27, compressed references and
compact headers): a handle with an object reference, a long and a byte, 24 bytes (one
more long, the id, makes 32); a value object with two longs, 24 bytes; a 30-slot node with
its three arrays, 689 bytes (BergDB's estimate for a key node of that size: 800).

| Keys | Index objects per key | Handles, bytes per key (24 / 32 bytes each) | Index memory per key | Handles' share |
|---|---|---|---|---|
| int4 and pre16, after the load | 0.162 | 3.9 / 5.2 | 119 | 3 to 4 % |
| int4 and pre16, after the updates | 0.279 | 6.7 / 8.9 | 221 | 3 to 4 % |
| rnd16 | 2.163 | 51.9 / 69.2 | 375 to 451 | 12 to 18 % |

These are for every node in memory, history included. Under eviction only resident nodes
and the children their pointers have touched have handles, so the absolute cost follows
the budget, not the database. A handle per value would add 24 bytes to every 64-byte value
object (8-byte values), 37 percent: hence 4.6.

### 5.5 Caveats

* **The machine.** The figures are from the quiet machine (16:30 to 16:53): a script
  waited until no trace check or other JVM ran and the load had stayed below 1.5 for five
  minutes, then ran everything; the load during the runs rose only with their own threads
  (`out/quiet-log.txt`). The first measurements (11:57 to 12:43, `out/busy-*.txt`) shared
  the machine with six of item 001's trace checks and macOS's media analysis (load 8 to
  18 on ten cores). Their one-thread figures were 15 to 40 percent slower but led to the
  same comparisons. Their four-thread figures, on an oversubscribed machine, exaggerated
  the monitor's collapse at four threads (5.8 million lookups a second against 18.8 quiet,
  in cache); the quiet runs with eight threads show the same collapse.
* **One machine.** An Apple M1 Pro. A run on x86 Linux would show whether the costs of
  acquire reads, monitors and contention between cores are the same there.
* **A microbenchmark is not BergDB.** IndirectionBench has no time klongs, segments, top
  nodes or listeners, and its objects are allocated in one go; BergDB's objects are
  loaded, promoted and moved by the collector over time. Its value is the comparison of
  edge-following ways in one shape.
* **IndexCensus** measures BergDB with everything in memory; it says nothing about loads,
  and its followers without the lock are not safe beside eviction.


## 6. Pros and cons

For BergDB, against today's direct swizzling with whole-memory sweeps:

| | Pros | Cons |
|---|---|---|
| Eviction | Local, bounded work per eviction; no walks, counts or parent pointers; works for the DAG (history, splits, skip pointers) as it is; any policy, including LeanStore's cooling | A handle lifecycle to get right: dead handles, re-resolution, one live handle per id |
| Read path | No pointer lock and no write into a shared parent (also possible without handles); scales with readers | One more dependent load per hop: on one thread no more than today's lock and stamp, 9 to 13 percent over a direct pointer without them; much more if handles are scattered |
| Objects | One object per node: no snapshots, no duplicate versions, no snapshot accounting; a newer version serves older pointers (lemma M) | A reader's load can replace a version that other pointers use (harmless by lemma M, but a load more) |
| Records | The reference in the pointer decides the record; reads cannot change records (the M21 and M27 class) | A new serialization invariant to prove (4.4) |
| Memory | Exact accounting; handles cost 3 to 4 percent of the index for 4-byte and prefixed keys | 24 to 32 bytes per handle; 12 to 18 percent for random 16-byte keys; values must stay without handles |
| Concurrency | Compare-and-swap on handles; Java's collector instead of epochs; `PointerLocks` off the read path | Slow paths need care (install, promote, evict racing) |
| Startup | Unchanged; no directory of latest positions | — |
| Model and proofs | A simpler physical state: pointers name nodes, eviction asks nothing of incoming pointers | The physical layer's proofs (about 11,400 lines) redone; the Java Level 4 work partly redone |
| Evidence | The Bw-tree, MVCC's logical pointers and Kemper and Kossmann's indirect swizzling work; LeanStore shows what a cheap policy gives | HotSpot dropped handles for speed; the Bw-tree's indirection costs it 18 percent on reads; no system found combines handles with retained history |

Not solved by handles: P4's second finding, that G1 needs full collections because evicted
objects are old when they die. That depends on the collector (generational ZGC, JEP 439)
or on keeping node contents out of the Java heap, whatever the pointers look like.


## 7. The alternatives

What else could make release local or cheap, for item 001's K5 or later:

| | What | Read path | Eviction | Fits the DAG | Cost of the change |
|---|---|---|---|---|---|
| A | Incremental sweep: today's pointers, the walk spread over transactions | as today | still proportional to the resident set over a cycle; in-degree known only at the end of a cycle, so concurrent changes need a barrier or a re-check | yes | moderate; the subtle part is a walk that the writer and readers change while it runs |
| B | Reverse reference lists, or exact in-degree counts per object | as today | local: unswizzle the victim's pointers | yes | per pointer made or dropped, at splits (copies of 10 to 30 pointers) and loads; 12 bytes per entry in Kemper and Kossmann; they measured it as the slowest on updates |
| C | A forest: memory pointers only on TREE's live pointers of current nodes, other pointers resolved by id (a table lookup) each time; parent pointers | latest-time reads as fast as direct; reads into history pay a lookup per edge | local and bottom-up, LeanStore's way | by construction: history is reached by id | a forest invariant kept at every split (the replaced node's pointers to shared children become stream pointers), parent pointers; context-specific swizzling |
| D | Indirect swizzling, this report | one more hop everywhere | local, any policy | yes | section 4.10 |
| E | Direct pointers, unswizzled locally by age, the garbage collector deciding when an object is free (weak references; Cache2) | as today | incremental; memory and accounting known only after collections | yes | weak references (an object each), reference queues, accounting that lags the collector, old-generation garbage |
| F | A hash lookup per edge (the KISS design) | 1.3 to 1.9 times direct | trivial | yes | small in code, large on reads |

C and D are the real candidates. C keeps the fastest latest-time reads and pays on
history; D pays a little everywhere and gets the simplest eviction and model. Kemper and
Kossmann's result suggests a combination: direct pointers in the hot, single-owner context
(the current tree's upper levels), indirect elsewhere.


## 8. Recommendation

1. **Now, independent of the choice:** take the pointer lock and the stamp off the read
   path, and the `readSync` monitor and the shared counter off each get. The census shows
   that with eight readers they cut the throughput to a quarter, and that today's gets
   scale backwards from four threads to eight. Recency can move into the child
   object (a bit written only when it is clear) or into a handle; never a write into a
   parent's array. This needs its own check of the reader protocol of Q8 (an unswizzle
   may race a lock-free read; today's lock keeps a reader from seeing half a pointer).
2. **For K5 or the next item:** prototype D on a branch, for index nodes only, values with
   their leaves, records unchanged, and measure J10's gets, gets from 4 and 8 threads,
   P4's soak with eviction and LargerThanMemory. The acceptance targets could be
   Q13's: warm gets within 10 percent of today, and P4's commits near P2's.
3. If the hop proves too dear for latest-time lookups, prototype C, or a combination
   (direct pointers in the current tree's top levels, handles below them and into
   history).
4. Then model the chosen state in Lean, before the physical layer's proofs are redone.

Not recommended: B (its costs fall on the writer's splits, which copy many pointers, and
the literature measured it as the slowest), F (too slow), E alone (the accounting the
capacity controller needs comes too late).


## 9. Found on the way

* **Keys longer than 7 bytes with distinct prefixes cost two key nodes each.** With
  `rnd16` keys, BergDB keeps 2.16 index nodes per key: each key gets a segment tree of
  one entry for each further 7-byte segment, so the index takes 375 bytes of memory per
  key against 119 for 4-byte keys. Masstree avoids such layers: a border node keeps a
  key's suffix, and a new layer is made only when two keys share a slice (Mao, Kohler and
  Morris 2012, section 4.1). Worth an item of its own.
* **Every get writes shared memory twice:** the `readSync` monitor and `aux.getOpCount`.
* **`Cache3.CacheEntry.refCount` is never decremented** (`pointerDestroyed` has no
  caller): dead, harmless.
* **[docs/levels.md](../011-docs-archive/04-levels.md) gives the default startup distance as 20 MB;**
  `DbBuilder` sets 50 MB, as level4-evidence.md says.


## 10. References

What was read for this report is marked: **read** (the relevant sections of the paper),
**part** (introduction and the sections cited), **abstract** (the abstract, from the
publisher or a search), **via** (as described by a paper that was read; the bibliographic
record checked), **summary** (a search summary of a page that could not be opened).

Swizzling in object stores:

* M. P. Atkinson, K. J. Chisholm, W. P. Cockshott and R. Marshall. Algorithms for a
  persistent heap. Software: Practice and Experience 13:259–271, 1983. (PS-algol; via
  Kemper and Kossmann.)
* T. Kaehler and G. Krasner. LOOM: Large Object-Oriented Memory for Smalltalk-80 Systems.
  In Smalltalk-80: Bits of History, Words of Advice, 1983; reprinted in Readings in
  Object-Oriented Database Systems, 1990, 298–307. (Via Kemper and Kossmann, and Graefe et
  al.)
* J. E. B. Moss. Working with persistent objects: to swizzle or not to swizzle. IEEE
  Transactions on Software Engineering 18(8):657–673, 1992. doi:10.1109/32.153378. (Via
  Kemper and Kossmann.)
* S. J. White and D. J. DeWitt. A performance study of alternative object faulting and
  pointer swizzling strategies. VLDB 1992, 419–431. (Via Kemper and Kossmann.)
* P. R. Wilson. Pointer swizzling at page fault time: efficiently supporting huge address
  spaces on standard hardware. ACM SIGARCH Computer Architecture News 19(4):6–13, 1991;
  with S. V. Kakkad, IWOOOS 1992, 364–377. (Via Kemper and Kossmann.)
* S. J. White and D. J. DeWitt. QuickStore: a high performance mapped object store.
  SIGMOD 1994. (Via Kemper and Kossmann.)
* A. Kemper and D. Kossmann. Adaptable pointer swizzling strategies in object bases. ICDE
  1993, 155–162; and Adaptable pointer swizzling strategies in object bases: design,
  realization, and quantitative analysis. The VLDB Journal 4(3):519–566, 1995.
  https://www.vldb.org/journal/VLDBJ4/P519.pdf (Read.)
* M. L. McAuliffe and M. H. Solomon. A trace-based simulation of pointer swizzling
  techniques. ICDE 1995, 52–61. (Via Kemper and Kossmann.)

Java:

* Oracle. The Java HotSpot Performance Engine Architecture (white paper).
  https://www.oracle.com/java/technologies/whitepaper.html (Summary.)
* JEP 534: Compact Object Headers by Default (JDK 27). https://openjdk.org/jeps/534
  (Read.) JEP 439: Generational ZGC (JDK 21). https://openjdk.org/jeps/439 (Read.)
* G. Einziger, R. Friedman and B. Manes. TinyLFU: a highly efficient cache admission
  policy. ACM Transactions on Storage 13(4), 2017. arXiv:1512.00727. (Abstract.)

Buffer managers:

* G. Graefe, H. Volos, H. Kimura, H. Kuno, J. Tucek, M. Lillibridge and A. Veitch.
  In-Memory Performance for Big Data. PVLDB 8(1):37–48, 2014.
  doi:10.14778/2735461.2735465.
  https://15721.courses.cs.cmu.edu/spring2016/papers/p37-graefe.pdf (Read.)
* G. Graefe, H. Kimura and H. Kuno. Foster B-trees. ACM TODS 37(3), 2012. (Via Graefe et
  al. 2014.)
* V. Leis, M. Haubenschild, A. Kemper and T. Neumann. LeanStore: In-Memory Data Management
  Beyond Main Memory. ICDE 2018, 185–196. doi:10.1109/ICDE.2018.00026.
  https://db.in.tum.de/~leis/papers/leanstore.pdf (Read.)
* T. Neumann and M. Freitag. Umbra: A Disk-Based System with In-Memory Performance. CIDR
  2020. (Abstract; its translation by swizzling as summarized in vmcache's table 1.)
* V. Leis, A. Alhomssi, T. Ziegler, Y. Loeck and C. Dietrich. Virtual-Memory Assisted
  Buffer Management. SIGMOD 2023.
  https://www.cs.cit.tum.de/fileadmin/w00cfj/dis/_my_direct_uploads/vmcache.pdf (Part.)
* A. Crotty, V. Leis and A. Pavlo. Are You Sure You Want to Use MMAP in Your Database
  Management System? CIDR 2022. (Abstract.)
* T. Johnson and D. Shasha. 2Q: a low overhead high performance buffer management
  replacement algorithm. VLDB 1994. (From memory; cited for the policy only.)
* Y. Mao, E. Kohler and R. Morris. Cache Craftiness for Fast Multicore Key-Value Storage
  (Masstree). EuroSys 2012, 183–196.
  https://read.seas.harvard.edu/~kohler/pubs/mao12cache.pdf (Part: sections 4.1 to 4.4.)

Indirection layers:

* J. J. Levandoski, D. B. Lomet and S. Sengupta. The Bw-Tree: A B-tree for New Hardware
  Platforms. ICDE 2013, 302–313.
  https://faculty.cc.gatech.edu/~jarulraj/courses/4420-s19/papers/08-oltpindexes1/bwtree-icde2013.pdf
  (Part: sections 1 to 3, 5 and 6.)
* J. J. Levandoski, D. B. Lomet and S. Sengupta. LLAMA: A Cache/Storage Subsystem for
  Modern Hardware. PVLDB 6(10):877–888, 2013. (Via Wang et al.)
* Z. Wang, A. Pavlo, H. Lim, V. Leis, H. Zhang, M. Kaminsky and D. G. Andersen. Building a
  Bw-Tree Takes More Than Just Buzz Words. SIGMOD 2018. doi:10.1145/3183713.3196895.
  https://15721.courses.cs.cmu.edu/spring2019/papers/07-oltpindexes1/mod342-wangA.pdf
  (Part: sections 1 to 3, 6 and 8.)
* Y. Wu, J. Arulraj, J. Lin, R. Xian and A. Pavlo. An Empirical Evaluation of In-Memory
  Multi-Version Concurrency Control. PVLDB 10(7):781–792, 2017.
  https://www.vldb.org/pvldb/vol10/p781-Wu.pdf (Part: sections 6, 7.5 and 8.)

Multiversion structures (see also [docs/prior-art.md](../011-docs-archive/02-prior-art.md), whose
reading records these follow):

* J. R. Driscoll, N. Sarnak, D. D. Sleator and R. E. Tarjan. Making data structures
  persistent. JCSS 38(1):86–124, 1989. (Via MIT 6.854 lecture notes,
  https://courses.csail.mit.edu/6.854/20/Notes/n02-persistent.html.)
* D. Lomet and B. Salzberg. Access methods for multiversion data. SIGMOD 1989, 315–324.
  doi:10.1145/67544.66956. (Via prior-art.md, which read it in full.)
* B. Becker, S. Gschwind, T. Ohler, B. Seeger and P. Widmayer. An asymptotically optimal
  multiversion B-tree. The VLDB Journal 5(4):264–275, 1996. doi:10.1007/s007780050028.
  (Via prior-art.md, which read it in full.)
* D. Lomet, R. Barga, M. F. Mokbel, G. Shegalov, R. Wang and Y. Zhu. Immortal DB:
  transaction time support for SQL Server. SIGMOD 2005. doi:10.1145/1066157.1066295.
  (Abstract.)

BergDB: [docs/level4-alignment.md](../001-lean-model-levels-3-4/08-level4-alignment.md) (sections 4, 5 and 7),
[docs/level4-plan.md](../011-docs-archive/05-level4-plan.md) (sections 1 and 4),
[docs/level4-evidence.md](../001-lean-model-levels-3-4/10-level4-evidence.md) (J8, P4),
[docs/level4-performance.md](../001-lean-model-levels-3-4/11-level4-performance.md) (J10),
[docs/levels.md](../011-docs-archive/04-levels.md), [docs/prior-art.md](../011-docs-archive/02-prior-art.md);
[Eviction.java](../../java/src/bergdb/core/Eviction.java),
[Residents.java](../../java/src/bergdb/core/Residents.java),
[NodeCollection.java](../../java/src/bergdb/core/NodeCollection.java),
[Cache3.java](../../java/src/bergdb/core/Cache3.java),
[Cache2.java](../../java/src/bergdb/core/Cache2.java),
[PointerLocks.java](../../java/src/bergdb/core/PointerLocks.java),
[KeyNode.java](../../java/src/bergdb/dag/KeyNode.java),
[Dag.java](../../java/src/bergdb/dag/Dag.java);
`lean/SIS/Phys.lean`, `lean/SIS/Evict.lean`, `lean/SIS/PhysTheorems.lean`.


## 11. Evidence and how to rerun

In [01-report/](01-report/):

* `IndirectionBench.java`, the microbenchmark (no dependencies), and `run-bench.sh`, which
  runs its matrix for a number of threads.
* `IndexCensus.java`, the census and read-path timing against `bergdb.jar` (package
  `bergdb.core`, compiled outside the repository), and `run-census.sh`.
* `run-when-quiet.sh`, the script that waited for the quiet machine and ran everything
  (with this session's scratch paths; kept as the record of what ran).
* `out/`, the quiet runs: `bench-t1.txt`, `bench-t2.txt`, `bench-t4.txt`, `bench-t8.txt`
  (the tables of 5.1); `census-int4.txt`, `census-pre16.txt`, `census-rnd16.txt` (gets
  from 4 threads), `census-int4-t2.txt` and `census-int4-t8.txt` (2 and 8 threads, no
  updates: the second census repeats the first); `quiet-log.txt` (times and loads). The
  first runs on the busy machine are kept as `busy-*.txt`
  (`busy-bench-t1-first.txt` and `busy-bench-t1-second.txt` name the handle layouts
  differently, see their headers).

To rerun, with JDK 27 (`JAVA_HOME=/opt/homebrew/opt/openjdk` on this machine), on a quiet
machine, with a scratch directory outside the repository:

    for t in 1 2 4 8; do sh items/004-indirect-swizzling/01-report/run-bench.sh SCRATCH/bench $t; done
    java -Xms2g -Xmx2g -cp SCRATCH/bench/classes IndirectionBench sizes
    sh items/004-indirect-swizzling/01-report/run-census.sh SCRATCH/census

and the census with `-Dthreads=2` and `-Dthreads=8` (`-Dupdates=0`, 4-byte keys) as in
`run-when-quiet.sh`. `run-census.sh` needs `java/build/bergdb.jar` (`java/build.sh`). The
benchmark takes 3 to 5 minutes per thread count, the census about 6.
