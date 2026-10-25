009-02. Implementation plan: handles in BergDB
==============================================

Created 2026-10-25 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request ("Go ahead and adjust 01 and then write 02."), from
[009-01](01-overview-plan.md), the overview plan, whose phases Frans
approved ("Phases are good."). This is phase 0's output: the design, the
study of the Java Memory Model that Frans asked for, the measurements of
the table, and the steps of phases 1 to 6. The tool and the outputs of the
measurements are in [02-implementation-plan/](02-implementation-plan/).

**Status: decided.** Frans, 2026-10-25: T1a, T2a, T4b, T5a, T7a, and T6b,
which section 3.4 argues safe (19:10); T3a, and the name `Pointee` (19:34:
"I decide T3a. T4b, Pointee is a good name."). Nothing is implemented.

Terms, as in BergDB: a memory pointer, a stream pointer, pointer i of x.
"Slot" is the Lean model's word only. A *handle* is 009's per-node handle.
The Lean model already uses "handle" for an object's number in memory
(`Slot.mem h`, `Mem.objs` in `lean/SIS/Phys.lean`); the new Lean files call
that an address (section 5, phase 2).


# 1. In short

* **The handle** (4.1): one object per index node that is resident or that
  a resident pointer names, 32 bytes: the node id, the node's one object
  (or none), the position this process last wrote the node at, a state,
  and a CLOCK bit. A dead handle is never live again; one live handle per
  node, in the table.
* **Pointers** (4.2): pointer i of a key node or a top node holds a handle,
  or nothing until it is first followed, and always its serialized
  reference in `pos[i]`. The access stamp leaves `pos[i]`. Values keep
  direct pointers and go with their leaf.
* **The table** (4.3, T1): 4,096 HashMaps from node id to live handle,
  each with its own lock; Cache3's 256 maps under one lock go. Measured
  today (section 8): with 4,096 maps a resize stops one map for 0.23 ms
  (median, ZGC) at 30M entries, against 11.6 ms with today's 256 maps.
* **Reads** (4.4): a lock-free fast path when the node's object is in its
  handle and new enough: a plain read of the pointer (T6b, argued safe in
  3.4), an acquire read of the handle's object, a test. Everything else
  (resolve, load, install, re-resolve) is the slow path, and locks: a
  load costs microseconds to a millisecond, a lock tens of nanoseconds.
* **Eviction** (4.7, T2): CLOCK over the table, one map at a time, in
  bounded batches under the write lock, at transaction boundaries and
  from an eviction thread when a reader's load passes the budget (T5).
  Evicting an object is local: its handle dies; no walks, no in-degree.
  The accounting is exact without walks.
* **Records do not change**: the serialization rule of 004-01 (4.4), and
  StreamDigest after every step.
* **Memory** (4.11): handles take the values out of the table (today 1.10
  table entries per KV, values included). Estimated MEM: from about 191
  bytes per KV today to about 135 for compact keys.
* **The Java Memory Model** (section 3): every field of the fast path has
  its barrier, in a table; jcstress tests on F53, which is AArch64 and
  weakly ordered, and on s1 (x86).
* **The steps** (section 5): phase 1 in four commits on `main`, phase 2's
  model in four steps, phase 3 in five steps on the branch, each of which
  passes the gates alone.


# 2. BergDB today, where 009 changes it

## 2.1 Pointers

* `KeyNode` ([KeyNode.java](../../java/src/bergdb/dag/KeyNode.java)):
  `Node[] pointers` and `long[] pos`. Pointer i is a memory pointer when
  `pointers[i]` is set, and then `pos[i]` holds the access data (the
  stamp); else a stream pointer, and `pos[i]` holds its position or vpos.
  The pair is written under the node's own monitor (`setPointer`), and read
  without it when the node is set (`getPointer`). `volatile short size`
  publishes the arrays: the writer appends past `size`, then raises it.
* `TopNode` ([TopNode.java](../../java/src/bergdb/dag/TopNode.java)): the
  skip pointers `TopNode[] pointers` with `long[] pointersPos`, and the root
  pointer `KeyNode rootPointer` with `rootPointerPos`; the same rules.
* The serialized reference (`Pointer.getSposForStream`): a memory pointer's
  object's position, else `pos[i]`.

## 2.2 Following

[NodeCollection.java](../../java/src/bergdb/core/NodeCollection.java):

* **The readers' follower** (`followPointer`) takes one of 128 striped
  monitors ([PointerLocks](../../java/src/bergdb/core/PointerLocks.java),
  `node.hashCode() + 13 * i`) for the whole follow, a read from the stream
  included, writes the stamp into a memory pointer, or loads
  (`followStreamPointer`).
* **The load** (`followStreamPointer`): (1) the id, from a vpos or the
  header at the position (`idOf`, with a small cache `idByPos`); (2) Rule R,
  the newest version in the startup section; (3) the node table's canonical
  object, else exactly that version read; (4) the pointer made a memory
  pointer, and the table told (`pointerCreated`).
* **The writer's follower** makes the object canonical (`makeCanonical`).
  **The maintenance follower** (reclaim's) counts what it reads.
* **The writer before a record** (`resolvePointers`): a pinned pointee by
  id, its canonical object; a stream pointer to its Rule R reference.
* **Startup's rule 4** (`linkToCanonical`, from `DbStarter.linkD`): D's
  stream pointers to nodes with a canonical object become memory pointers.

## 2.3 The node table

[Cache3.java](../../java/src/bergdb/core/Cache3.java): 256 `HashMap<Long,
CacheEntry>`, the map by Fibonacci hashing of the id (`mapIndex`), and one
lock for all of them: `getLock(id)` returns `bigLock`. A `CacheEntry` holds
the canonical object and a `refCount` that nothing decrements (004-01,
section 9). Values are entries too (they count as canonical): 1.10 entries
per KV, about 70 bytes per KV of MEM's 191 (006-02, section 4, with
005-08's fix).

## 2.4 Eviction

[Eviction.java](../../java/src/bergdb/core/Eviction.java) and
[Residents.java](../../java/src/bergdb/core/Residents.java):

* **Schedules:** `NONE`, `VALUES`, `EVERY`, `RANDOM` (tests; the system
  property `evict`) and `BUDGET`, the capacity controller, the default.
* **When:** under the write lock, at a transaction boundary
  (`afterTransaction`), or after a reader's load over the budget
  (`afterLoad`): the reader itself takes the write lock, and waits for any
  transaction in progress.
* **How:** the sweep walks every resident object (`Residents.walk`, from
  the super root, the node table and D), counts the memory pointers to
  each, unswizzles the oldest pointers to detachable objects, releases the
  objects no memory pointer names, and walks again to make the byte count
  exact (`resync`).
* **Pins** (`Residents.isPinned`): the canonical objects of D and of the
  record being written, the super root, the newest written top node.

## 2.5 Publication to readers

[Db.java](../../java/src/bergdb/core/Db.java), and Frans's notes at its end
("A writer published its writes ... by an empty synchronized block"):

* The writer runs `synchronized (readSync) {}` after its in-memory changes
  and before `dbClock.transactionEnd()` makes the transaction's time a
  lookup time, and again after eviction and the audit.
* Every get begins with `synchronized (readSync) {}` (`getOne`, `getMany`,
  `getTrans`): an acquire, but also a write to the monitor's word, shared
  by all readers.
* `DbClock.lastTransactionTime` and `TopDs.superRoot` are volatile; reclaim's
  first available position is published by `readSync` (Reclaim's comment).
* Every get increments one `AtomicLong` (`aux.getOpCount`).

## 2.6 Tests and gates that cover this

`before-commit.sh`; `level4.sh` (the eviction unit and f-tests,
EvictionInvariance with every schedule, restarts, crashes and reclaim with
forced schedules, readers under eviction, conformance with the Lean model
with eviction, LargerThanMemory); StreamDigest against 2026.1;
EvictionReaderTester; the audit (`audit=N`).

## 2.7 The Lean model

* `lean/SIS/Phys.lean` (stage 1): `Slot` (`mem h` or `stream r`), `Obj`
  (node, level, history, canonical, position, slots), `Mem` (objects by
  number, the node table, Rule R's startup pos, the root).
* `lean/SIS/Evict.lean` (stage 2): `Mem.pinned`, `detachable`,
  `unswizzle`, `release`, `promote`, `follow4` (the Level 4 loader),
  `refOf` (a pointer's reference when written), `writeNode`, `linkD`,
  `CacheOp` (reads, unswizzles, releases between transactions),
  `runEvict`.
* The theorems, in `lean/SIS/PhysTheorems.lean`: `TC_records` (T-CACHE),
  `TR_view` (T-READ), `T2_cache` (T2-C, restarts), `TR_view_restarts`,
  `TP_pins` (T-PIN); lemma M (`LM_newer`, `LM_ruleR`). The proofs:
  `Proof/Evict*.lean`, 11,695 lines with Evict*.lean; `Phys*`, 8,798.
* The checker's C-P (`Check/Steps.lean`): INV-SLOT on Java's exported
  physical states.


# 3. The Java Memory Model, and BergDB

Frans: "Lock-free reads. This is hard. Ensure writes are published to
readers somehow. A barrier is needed. Study the Java Memory Model."

## 3.1 The rules that matter here

From the JLS, chapter 17 (17.4, the memory model; 17.5, final fields;
17.7, long and double), and the sources of 3.6:

* **Happens-before is the only guarantee.** A read sees a write that
  happens-before it (and no later write between), or, in a data race, any
  write: a stale value, or a newer one, in any order. Without an edge, a
  reader can see a reference to an object before it sees the object's
  fields as its constructor or loader wrote them.
* **The edges:** program order in one thread; the unlock of a monitor and
  every later lock of the same monitor; a volatile write and every read of
  that variable that sees it; `Thread.start` and `join`; and transitivity.
  So: the writer writes plain fields, then a volatile field (release); a
  reader reads that volatile field (acquire) and sees the new value; then
  everything the writer wrote before the volatile write is visible to it.
* **The VarHandle access modes** (JDK 9; BergDB compiles with
  `--release 17` since step 1-0, before that with 8, which had none of
  them): plain; opaque (no tearing, no
  reordering of accesses to the same variable, no edges); release and
  acquire (the edge above, without the total order of volatile); volatile.
  `compareAndSet` has volatile semantics. `arrayElementVarHandle` gives these
  modes on array elements, which a Java field declaration cannot.
* **Final fields:** an object's final fields, as its constructor set them,
  are seen by every thread that sees a reference to the object, even through
  a race, if `this` does not escape the constructor.
* **`long` without volatile may tear** (JLS 17.7): a plain read of a `long`
  written in a race may see half of each write. HotSpot on 64-bit machines
  does not tear; the JLS allows it. Opaque mode forbids it.
* **The hardware:** x86 (s1) reorders only a store with a later load
  (TSO), so a missing release or acquire rarely shows there. AArch64 (F53,
  Apple M1) reorders much more: stores with stores, loads with loads. A
  missing barrier is far more likely to show on F53. An acquire read is a
  load-acquire instruction on AArch64, a plain load on x86.
* **What the fast path must not do** (Masstree's rule, 004-01, 3.4): take
  a lock, or write shared memory. A monitor, even an empty block, writes
  the monitor's word; every reader on the same monitor then contends.

## 3.2 What BergDB relies on today

* **The node's `size`:** the writer appends to a node's arrays past `size`
  and then writes `size` (volatile, release); a reader reads `size` first
  (acquire). Frans's notes in Db.java. Correct, and kept.
* **The clock:** the writer's changes happen before
  `dbClock.transactionEnd()` writes `lastTransactionTime` (volatile). A
  reader whose lookup time comes from that read sees every change of the
  transactions before it. Correct, and enough for the changes, without the
  reader's `synchronized (readSync) {}`.
* **The empty `readSync` blocks:** the writer's block publishes the
  transaction; the readers' blocks give each get an acquire for whatever is
  not published otherwise: the database state (`DbState`), reclaim's first
  available position, startup's writes. These need volatile fields of their
  own if the readers' blocks go (step 1c).
* **The pointer locks:** every follow takes one, and every change of a
  pointer pair is made under one (`setPointer` also under the node's own
  monitor), so a reader never sees half a pair. They are also what makes
  the swizzling visible: a loader's object reaches other readers through
  the pointer lock's edge.
* **The stamp:** a plain write into the parent's `pos[i]`, under the
  pointer lock.
* Not reviewed as a whole: 005-07.

## 3.3 What handles need, field by field

The protocol, first version. The proofs of these claims are the argument
in the right-hand column; phase 2's model and step 3c's jcstress tests
check them.

| Field | Written by, how | Read by, how | Why a reader is safe |
|---|---|---|---|
| node `size` | writer, volatile, after the arrays | everyone, first, volatile | as today |
| node arrays (`klongs`, `pos`, `pointers` at creation) | writer, plain, before `size` | after `size` | published by `size` |
| `pointers[i]` (a handle, a value, or null) | writer: at creation, before `size`; in place (`resolvePointers`, rule 4, a value's unswizzle): under the node's monitor; a resolver: `compareAndSet` | fast path: plain for a handle (T6b), acquire for a value | section 3.4 |
| `pos[i]` | writer only (a new pointer; Rule R in `resolvePointers`) | slow path; the fast path's test | opaque: no tearing; a stale value only sends the reader to the slow path, or names an older version that lemma M covers (to check in the model: section 7, point 2) |
| handle `id` | constructor | anyone | final |
| handle `obj` | an install, a replace, the writer's promote: under the handle's monitor, release; an eviction: release (null) | fast path: acquire | the loader's writes to the object happen before the reader's use; null sends the reader to the slow path |
| handle `state` | loader, writer, evictor: `compareAndSet` | slow path, evictor | one state machine (4.4); the evictor never waits on a lock a loader holds |
| handle `writtenPos` | writer, plain | writer (records), evictor | both hold the write lock |
| handle CLOCK bit | fast path: plain, and only when clear; evictor: clears | evictor | a lost bit changes only which object goes |
| object `isCanonical`, `spos` | writer, under the handle's monitor; an eviction clears the flag | the fast path's test, plain | a canonical object holds its node's whole history (CC); a snapshot's `spos` never changes; a stale "not canonical" sends the reader to the slow path; a stale "canonical" on an evicted object is still the version at its position (M31) |
| database state, reclaim's first position | writer, volatile | each get, first, volatile | replaces the readers' `readSync` blocks (1c) |

What the fast path then costs per hop: a plain read of the pointer, an
acquire read of the handle's object, the test, and a read of the CLOCK
bit. This is 004-01's `handleacq` variant (5.1): on F53 72.1 ns a lookup
in cache against 70.7 with a plain read of the object, and 583 against
564 out of cache.

## 3.4 Why a plain read of the pointer is safe (T6b)

Frans: "T6. Use T6b if you argue it is safe." The fast path reads
`pointers[i]` with a plain read, and then the handle's object with an
acquire read. The argument, from the rules of 3.1:

1. **What the read can return.** A read of a reference is atomic (JLS
   17.7), and it returns a value that some write stored there, never one
   out of thin air (17.4.8): null, a handle, or a value node. In a race it
   may be an older value than the newest.
2. **A pointer's pointee never changes** (C1). Pointer i of a node names
   the same node, or the same value, for as long as a reader can read it:
   a node's arrays only grow, and the two exceptions are behind the
   transaction's time klong, where every reader stops (KeyNode's class
   comment). What changes in place is only how the pointer holds its
   pointee: nothing, a dead handle, or the live handle; a value node or
   nothing. So whatever the read returns belongs to the right node or
   value, however old it is.
3. **Null** sends the reader to the slow path (C2). The slow path reads the
   pair, `pointers[i]` and `pos[i]`, under the node's monitor, as
   `KeyNode.getPointer` does today for a stream pointer; and every in-place
   change of `pos[i]` or of a value pointer is made under that monitor, as
   `setPointer` does today. So the slow path sees the newest of those
   changes. A resolver's `compareAndSet` only puts a live handle where
   there was null or a dead handle; if it fails, the resolver reads the
   pointer again with a volatile read and takes the handle it finds.
4. **A handle h** (C3, C4). The fast path reads two things of it:
   * `h.obj`, with an acquire read. It returns null, which sends the reader
     to the slow path, or an object o that an install stored with a
     volatile write. The read then synchronizes with that write, so all
     the installer did before it, the load of o from the stream with o's
     fields and arrays, is visible to the reader. That is what T6a gives
     after the handle too; T6a's acquire read of the pointer would add an
     edge to whoever published h, and the fast path reads nothing of h
     that needs one.
   * The CLOCK bit, a byte, plainly. Fields do not tear or disturb each
     other (17.6); a stale or lost bit changes only which handle the
     evictor takes.
   The fast path reads neither `state` nor `writtenPos`. The slow path
   needs `h.id`, which is final, so a thread that sees h through a race
   sees the id its constructor set (17.5; the constructor only assigns its
   fields). It changes `state` only by `compareAndSet`, which works on the
   newest value. And `LIVE` is 0, the default: a new handle is LIVE without
   a write in its constructor, because a non-final field's constructor
   value is not guaranteed through a race, and nothing may rely on one.
5. **A value node v** (C5). Its bytes are final (`ValueNode.value`), and so
   safe through a race, with the array's contents (17.5). But its position,
   `spos`, is volatile and set in the constructor, which 17.5 does not
   cover, and `getTpos()` reads it (`transactionInfo()`, 005-42). So a
   pointer to a value is read with an acquire: one barrier per get, not
   one per hop.
6. **The compiler** may reuse an earlier read of `pointers[i]`. That is
   the same as an older value: one of the cases above.

So a plain read is safe for a pointer to a handle, as long as the code
keeps C1 (a pointee never changes), C2 (the slow path, and every in-place
change of a pair, under the node's monitor), C3 (a handle's id final, its
object volatile, `LIVE` the default) and C4 (the fast path reads nothing
of a handle but its object and the CLOCK bit); and reads a pointer to a
value with an acquire (C5). The argument is the JMM's, not the
hardware's: it holds on x86 and on AArch64 alike. The code's comments
name the conditions where they apply, and the jcstress tests of 3.5 check
the outcomes: a handle published by `compareAndSet` and read plainly, its
object installed before, after or never; allowed are null, or the object
with its contents, never an object with default contents.

## 3.5 How to test it

* **jcstress** (OpenJDK's concurrency stress harness): small tests of the
  protocol's races (a handle published by `compareAndSet` and read plainly,
  3.4; an install against a fast-path read; an eviction against a
  fast-path read; a re-resolve against an eviction; two loaders), each
  with its allowed outcomes. Run on F53 (AArch64) and on s1 (x86). A
  tool of item 009 at first, not a gate: jcstress is not in BergDB's
  build.
* **Readers under eviction:** EvictionReaderTester and ReclaimReaders,
  extended with more readers and the forced schedules.
* **The audit:** the handle invariants (4.10) at transaction boundaries.

## 3.6 Sources

* The Java Language Specification, chapter 17, "Threads and Locks".
* J. Manson, W. Pugh and S. Adve, "The Java Memory Model", POPL 2005
  (JSR-133).
* D. Lea, "Using JDK 9 Memory Order Modes", 2018
  (gee.cs.oswego.edu/dl/html/j9mm.html).
* A. Shipilëv, "Java Memory Model Pragmatics" (2014) and "Safe Publication
  and Safe Initialization in Java" (2014), shipilev.net.
* B. Goetz and others, "Java Concurrency in Practice", 2006, chapter 16.
* jcstress: openjdk.org/projects/code-tools/jcstress.
* Mao, Kohler and Morris, "Cache Craftiness for Fast Multicore Key-Value
  Storage" (Masstree), EuroSys 2012, section 4.4.


# 4. The design

## 4.1 The handle

```java
final class Handle {            // in bergdb.dag
    final long id;              // the node id
    volatile Node obj;          // the node's one object, or null
    long writtenPos;            // where this process last wrote the node, or none
    volatile byte state;        // LIVE (0, the default), LOADING, DEAD; by CAS
    byte ref;                   // the CLOCK bit
}
```

32 bytes with JDK 27's compact headers and compressed oops: an 8-byte
header, 8 + 8 + 4 + 1 + 1, aligned to 8 (TableBench's handle has the same
size: 36.5 bytes measured with its array slot, section 8); 40 under ZGC,
which has no compressed oops. The state and the CLOCK bit are separate
bytes: readers write the bit without a CAS, and a plain write into the
state's word could undo the evictor's CAS.

* **LIVE:** in the table; `obj` set or null. **LOADING:** a loader holds
  the handle's monitor and reads the stream; the evictor skips the handle.
  **DEAD:** evicted, out of the table, `obj` null, never live again.
* The id stays (T3): a pointer whose handle is dead finds the live one by
  id, without reading a header.

## 4.2 Pointers

* `KeyNode.pointers` becomes `Pointee[]` (T4b): `Pointee`, an interface
  in `bergdb.dag` that `Handle` and `ValueNode` implement (the name
  decided by Frans). It holds a handle for an index pointee, a `ValueNode`
  for a value, null until the pointer is first followed. Which kind pointer i
  holds is also known from its klong (`NodeCollection.pointsToIndexNode`).
  `TopNode.pointers` becomes `Handle[]` and `rootPointer` a `Handle`.
* `pos[i]` (and `pointersPos`, `rootPointerPos`) always holds the pointer's
  serialized reference: the position or vpos it named when it was made,
  loaded, or last resolved by the writer. No access data.
* A split copies the pairs (handle, reference), as it copies (object,
  position) today.

## 4.3 The table

Decision T1 (section 6), measured (section 8). Proposed: **4,096
HashMaps** from node id to live handle, the map by today's `mapIndex`
(Fibonacci hashing, 12 bits), each map its own lock. Frans: "Just having
4096 HashMaps to start with is not such a bad idea either. It is simple,
and I understand it."

* Used only on slow paths: resolve, install of a new handle, eviction,
  startup, the audit.
* A resize stops one map, 1/4,096 of the table. Measured (ZGC): median
  0.044 ms at 10M entries, 0.233 ms at 30M (largest 1.2 ms); at 100M
  (G1) 0.197 ms. Today's 256 maps: 0.738 ms at 10M, 11.6 ms at 30M
  (largest 19.3), 3.8 ms at 100M (G1): a stop of its own that grows with
  the database, under the one `bigLock`.
* Memory: 79.0 bytes per entry with the handle (G1), of which 42.5 the
  table (a `HashMap$Node`, a `Long`, the array). The intrusive alternative
  (T1c) takes 47.0, of which about 10.5 the table.

## 4.4 Following

**The fast path**, for a pointer to an index node:

    h = pointers[i]                      // plain (T6b, 3.4)
    if h != null:
        o = acquire(h.obj)
        p = opaque(pos[i])
        if o != null and (o.isCanonical() or (!isVpos(p) and o.spos >= p)):
            if h.ref == 0: h.ref = 1
            return o
    return slowPath(x, i, h)

No lock, and no write to shared memory but the CLOCK bit when it is clear.
A vpos names no stream position, so a pointer that holds one takes the fast
path only to a canonical object. Values: `pointers[i]`, read with an
acquire (3.4, point 5), is the `ValueNode`, or null and the slow path.

**The slow path** (locks allowed, Frans):

1. **Resolve.** No handle, or a dead one: the id (a vpos is the id; else the
   dead handle's id; else the header at `pos[i]`, as today); under the id's
   map lock, the live handle or a new one; then `compareAndSet` it into
   `pointers[i]`. If the CAS fails, use the handle another thread put
   there.
2. **Load, under the handle's monitor.** If `obj` is still missing or older
   than the pointer's reference after Rule R: `state` LIVE to LOADING by
   CAS (if DEAD: back to 1); read the version (the pointer's, or the
   newest this process wrote, `writtenPos`, if newer); install it in `obj`
   unless a canonical or newer object got there first; LOADING to LIVE.
   Other loaders of the same node wait on the monitor (they need the same
   node); the evictor skips a LOADING handle and never waits (T7).
3. **The accounting** and the capacity controller's trigger (4.7), outside
   the monitor.

**Rule R on the fast path:** an open point (section 7, point 1). Today a
memory pointer is used without Rule R, and a stream pointer's load applies
it; with handles, the test above compares with `pos[i]` itself. Phase 2's
model says whether that is enough, or whether a pointer older than the
startup section must take the slow path.

## 4.5 The writer

* Follows as a reader, then needs the canonical object: if the handle's
  object is not canonical, it is lv(y) or older; the writer loads lv(y) if
  needed, and marks it canonical under the handle's monitor (the model's
  `promote`). One live handle per id gives one canonical object per node
  by construction.
* A node the writer makes gets its handle at once, in the table.
* `pointerCreated` (Dag, TopDs) becomes "the pointee's live handle into the
  pointer".
* When the writer writes a node, it sets the handle's `writtenPos`.

## 4.6 Records

The serialized reference of pointer i of x (004-01, 4.4): the canonical
object's position if the pointer's handle holds a canonical object; else
the larger of `pos[i]` after Rule R and the handle's `writtenPos`.
`resolvePointers` keeps its rule for pinned pointees (by id: the canonical
object's handle). Readers change neither `pos[i]` nor `writtenPos`, so a
record does not depend on what reads left in memory. The obligation: a
form of INV-SLOT for this rule, proved in phase 2 (step 2d), checked by
StreamDigest and EvictionInvariance after every step.

## 4.7 Eviction

* **Evictable:** a LIVE handle whose object is not pinned (not dirty, not
  in the record being written, not the super root or the newest written
  top node) and written (a stream position).
* **Evict(h)**, under h's map lock and with the write lock held: `state`
  LIVE to DEAD by CAS (fails if LOADING: skip); `writtenPos` from a
  canonical object's position; the object's canonical flag cleared (as
  M31 today); `obj` null; the table's entry removed; the object's bytes
  subtracted. A reader that holds the object finishes with
  it; the garbage collector keeps it until then.
* **The policy** (T2): CLOCK. The hand goes through the 4,096 maps in
  order; in a map, under its lock: a handle with its bit set gets it
  cleared; an evictable one with the bit clear is evicted. One map is a
  step: at most 1/4,096 of the handles (about 4,000 at 16M resident index
  nodes, 100M compact keys).
* **Batches:** the capacity controller as today (the budget as the high
  watermark, LOW of it as the low one): when the resident bytes pass the
  budget, steps until they are below the low watermark, at most K steps a
  batch (K = 16 to start; measured in step 3b); the next trigger
  goes on from the hand.
* **Triggers:** the writer at a transaction boundary, as today. A reader's
  load over the budget does not take the write lock (today it does, and
  waits for any transaction in progress, which can take far more than
  20 ms): it wakes the database's eviction thread, which takes the write
  lock between transactions (T5).
* **The test schedules** keep their meaning, with handles: `EVERY` evicts
  every evictable handle after every transaction (a walk of the table,
  for tests only), `RANDOM` each with probability 0.3 (seeded), `VALUES`
  unswizzles every written value pointer of resident leaves, `NONE`.
  EvictionInvariance compares their streams, byte for byte.
* **The accounting:** exact, without walks: an object's bytes are added
  when it is installed or grows, and subtracted when it is replaced or
  evicted; a leaf's bytes include its values (4.8).
* **Handles are counted too.** A live handle with its table entry counts
  as the table's (79 bytes, T1a). A dead handle stays in the pointers that
  hold it until they are followed again or their objects are evicted, so
  each pointer of a resident object that holds a handle adds the handle's
  32 bytes to that object's bytes: an upper bound, as a handle that
  several pointers hold is counted for each. How much that is: open
  point 8.

## 4.8 Values

As 004-01 (4.6): no handle, a direct pointer from the leaf; out of the
table. A value loaded or copied into a leaf's object is counted in that
object's bytes, so a value that two resident leaves share is counted
twice (an upper bound). When the leaf's object is evicted, its values go
with it unless another resident leaf holds them. Values over 1 MiB are
not kept, as today. Whether a leaf with many value bytes needs its values
unswizzled one by one is measured in phase 5 (`performance.sh`'s 1,000-byte
values).

## 4.9 Startup

Unchanged reads. Rule 4 (`linkD`): D's pointers resolved to their nodes'
handles by id. The cold-cache startup is measured in phase 5 (004-02,
10.5.8); 009 must not make it slower.

## 4.10 The audit, the trace exporter, the checker

* **The audit** adds: one live handle per id, the table's; a dead handle
  has no object and is not in the table; a LIVE handle's object has the
  handle's id; no handle is LOADING at a transaction boundary; the
  record rule of 4.6 gives each pointer of a current or dirty node its
  pointee's latest version.
* **The trace exporter** (`TraceExport`) maps the handles to today's trace
  format: a pointer whose handle holds an object is a memory pointer to
  it, any other a stream pointer with its serialized reference. The
  checker's C-P on `main` then checks the branch unchanged. A check of the
  handle state itself comes with phase 4.

## 4.11 What handles cost and save in memory

* Today, per KV (006-02): the table 69.7 bytes (1.10 entries: `HashMap$Node`
  24, `Long` 16, `CacheEntry` 16, the arrays), of MEM's 191.
* With handles: index nodes only, about 0.16 a KV for compact keys (004-01,
  5.2: 162,499 resident index objects for a million 4-byte keys), at 79.0
  bytes each with the table (T1a): about 13 bytes per KV; with T1c, 7.5.
* So MEM about 191 − 70 + 13 ≈ 135 bytes per KV (T1a), 129 (T1c): an
  estimate, measured in phase 5 (target 4 of 009-01).
* Random 16-byte keys have 2.16 index nodes per key (004-01, 9): there
  T1a costs about 170 bytes per key and T1c about 100. If such keys
  matter, T1c (section 6) is the later step.


# 5. The steps

Each step: the files, the tests, and its gate. "Gate": `before-commit.sh`
and StreamDigest against 2026.1, unless more is said. Every step passes
its gate alone.

## Phase 1. On `main`

* **1-0. Java 17.** The build compiles with `--release 17` instead of 8,
  so that VarHandle's access modes (3.1) can be used (Frans, 2026-10-25:
  "Move to --release 17. Code compiles for that. But we will test
  performance on the latest jvm."). Performance is measured on the newest
  JDK, 27. Size: S.
* **1a. The pause probe.** `java/stress/PauseProbe.java`: a database with
  the capacity controller and a budget well below the data, a writer in
  transactions of 1 and of 1,000 puts, 1 to 8 readers of random keys, each
  operation timed; with `-Xlog:gc*,safepoint` to tell the collector's
  stops from BergDB's. Prints the largest and the 99.9th percentile wait of
  a get and of a commit, and the sweep or eviction time. Run on 2026.1 and
  on `main`, with G1 and ZGC, 1M and 10M keys: the numbers before 009,
  into this item. And `CacheStats`, a small interface in `Db.Internal`
  (resident bytes, eviction steps and bytes, loads) that ScaleBench and the
  probe read instead of Eviction's and Residents' internals. Size: S to M.
* **1b. The table.** Cache3's 256 maps become 4,096 (T1a), each with its
  own lock: `getLock(id)` returns the id's map, and the operations on the
  whole table (`nodes()`, `totalSize()`) take the maps in turn. Readers
  add entries too (the values they load, which count as canonical), as
  they do today between the sweep's snapshot of the table and its walk;
  a snapshot taken map by map is no weaker for the sweep. The audit says
  if that is wrong. `refCount` goes. Test: Cache3's tests, a
  test of 4,096 maps with large ids; the pause probe. Size: S.
* **1c. Publication without the readers' monitor.** The readers'
  `synchronized (readSync) {}` in `getOne`, `getMany` and `getTrans` become
  volatile reads, in this order: the database state, then the clock, then
  reclaim's first available position. Db's `state` field and reclaim's
  position become volatile; the writer's blocks stay. `aux.getOpCount`
  becomes a `LongAdder`. The review of section 3.2 written into Db.java's
  notes. Tests: ReclaimReaders, EvictionReaderTester, the reader tests of
  `level3.sh` and `level4.sh`; gets from 1 to 8 threads in memory,
  before and after (ScaleBench M). Size: S to M.
* **1d. Seams.** Only refactors: every read of a pointer pair outside
  KeyNode and TopNode through their methods (Dag's `reportNewPointers`
  reads `node.pointers[i]`); the serialized reference in one method; the
  stamp's writes in one method; `pointerCreated`'s callers through one
  interface. So that phase 3 changes the representation in few places.
  Size: S.

## Phase 2. The Lean model, on `main`

* **2a. The state and the operations,** in `lean/SIS/Handle.lean`
  (trusted): objects by address; handles (node, object or none, written
  position, dead); the table, node to live handle; per object, per pointee,
  a reference and a handle or none. Follow (resolve, load, install, with
  the fast path's test), promote, the writer's change (new pointers take
  handles), `writeNode` with the record rule of 4.6, evict, re-resolve,
  rule 4. `HCacheOp`: reads and evictions between transactions. Size: M.
* **2b. Examples,** `lean/SIS/HandleExample.lean`: EvictExample's runs
  with handles, `#guard`s that the records are the model's, under schedules
  that evict everything, nothing, and at random. Size: S.
* **2c. The statements:** T-CACHE, T-READ and T-PIN over the new state, as
  definitions (`Prop`s), not theorems, until they are proved: no `sorry`.
  T-PIN gets simpler: every LIVE handle whose object is not pinned and is
  written may be evicted, in one step. Size: S.
* **2d. The serialization invariant, proved:** with any schedule of reads
  and evictions, the records are the model's (T-CACHE's first part for
  handles), with the invariant it needs. The merge waits for it (G2b).
  Size: L.

Done when, for each: `lake build` with no warnings and no `sorry`;
lean/README.md lists the files as work in progress.

## Phase 3. On the branch `009-handles`

Gate for each: `before-commit.sh`, `level4.sh quick`, StreamDigest
against 2026.1; `level4.sh` in full at 3b and 3d.

* **3a. Handles, with the old selection.** Handle and `Pointee` (T4b), the
  pointers of 4.2,
  the table of handles (CacheEntry goes), the followers still under
  PointerLocks, Dag, `resolvePointers` with 4.6's rule, `linkD`,
  TraceExport's mapping (4.10). Eviction becomes `evict(h)` (4.7); the
  schedules select as today, and `BUDGET` still by age and with walks for
  its choice and its byte count, now through handles (the stamp moves into
  the handle for this step). Values leave the table. This is the step
  where the representation changes; all gates as today. Size: L.
* **3b. Eviction without walks.** CLOCK (T2) in bounded batches, the exact
  accounting, the eviction thread for readers' triggers (T5); the sweep,
  `drop`, `resync` and the walks leave the budget path (the audit and the
  test schedules keep walks of the table). Measured: the pause probe;
  LargerThanMemory; K. Size: M.
* **3c. The lock-free fast path.** Section 3.3's barriers; PointerLocks
  and the stamp off the fast path; the slow path under the handle's
  monitor and the map's lock; the conditions C1 to C5 of 3.4 in the
  code's comments; the jcstress tests of 3.5 on F53 and s1. Size: M to L.
* **3d. The audit and the tests:** 4.10's invariants; EvictionReaderTester
  and ReclaimReaders for the races of 3.5; Eviction's twin tests; the docs
  of the classes. Size: M.
* **3e. 005-38's investigation,** on the branch with the sweep gone: the
  loads beyond the budget on s1's disk (004-02, 10.5.4), and what of their
  slowness was the sweep. Its findings into 005-38, and into phase 4 if
  they change what is pinned or written. Size: M, mostly runs.

## Phase 4. Lean: the proofs, on `main`, mostly after the merge (G2b)

* **4a.** T-CACHE, T-READ and T-PIN over handles proved, and T2-C for
  restarts. Size: L.
* **4b.** The alignment: `docs/handles-alignment.md`, the mapping of
  Java's handle state to the model and its register, as
  level4-alignment.md does for the old design, which stays as history.
  Size: M.
* **4c.** The checker's C-P for the handle state; TraceExport exports it.
  Then today's `Phys*` and `Evict*` files that only the old design uses
  go. Size: M.

## Phase 5. Measure and accept

009's jar against 2026.1's, in turns on one machine (008-01): the pause
probe (1a), J10's gets, gets from 1 to 8 threads, P4's soak with eviction,
LargerThanMemory, ScaleBench at 10M keys on F53 and on s1, Props (MEM),
`performance.sh quick`, the cold-cache startup; with G1, ZGC and
generational Shenandoah. The table of results, and targets 2 to 4 of 009-01,
into this item. Size: M.

## Phase 6. The merge

After 2d and phase 5: `main` merged into the branch, all gates on the merged
tree (`night.sh` included), Frans's go, `git merge --no-ff 009-handles`;
`main` pushed when Frans says. Then: docs/levels.md, Level 4; README.md's
known limits; docs/log.md; 004 done. Size: S.


# 6. Decisions

Frans, 2026-10-25, 19:10: "I decide: T1a, T2a. [...] I decide: T4b, T5a.
[...] T6. Use T6b if you argue it is safe. I decide: T7a." Section 3.4
argues T6b; T3 is open, expanded below at his request ("T3. Please expand
and explain the options more. Pros and cons with T3a and T3b. Why did you
propose T3a?"). The options are kept as they were proposed.

**T1. The table from node id to handle: T1a, decided.**

* T1a. 4,096 `HashMap<Long, Handle>`, a lock each. Simple and known; a
  resize stops one map (0.23 ms at 30M entries, ZGC). 79 bytes per entry
  with the handle.
* T1b. Linear hashing (Litwin): one bucket split at a time, never a whole
  rehash; chains through the handle. Bounded pauses whatever the size,
  compact; the most code, and the least known.
* T1c. 4,096 small tables of BergDB's own, chained through a `next` field
  in the handle, each doubled at 0.75 (Frans's MyLongMap of 2017, growing):
  the same pauses as T1a (0.39 ms at 30M), 47 bytes per entry, half T1a's
  fill time; about 100 lines of code to own. The CLOCK hand can stop and
  go on inside a map.
* T1d. Today's 256 HashMaps. Not enough: 11.6 ms at 30M entries.
* Proposed: T1a now (step 1b), T1c later if phase 5's MEM for long random
  keys asks for it.

**T2. The eviction policy: T2a, decided.**

* T2a. CLOCK over the table, one map at a time (4.7). A bit per handle,
  set by readers only when clear.
* T2b. Random choice into a cooling FIFO (LeanStore): sample handles,
  move unpinned ones to a FIFO, evict from its end unless they are used
  again. Better for scans, more state.
* Proposed: T2a; T2b if phase 5 shows CLOCK evicts what is used.

**T3. The node id in the handle: T3a, decided.**

What needs a node's id, and where it comes from without the field:

| Need | With the id in the handle | Without it |
|---|---|---|
| Re-resolve a dead handle (4.4, slow path step 1): find the node's live handle, or make one | `h.id`, then a table lookup | from `pos[i]`: a vpos is the id; else the header at `pos[i]`, or the node itself read there |
| Remove a handle's table entry at eviction | `h.id` | the map entry's key (T1a's `Long`): the evictor walks the entries anyway |
| The intrusive table (T1c, a possible later step) | its key | T1c would need the field back |
| The audit and debugging: which node a handle is for | `h.id`, also when dead | the object's id while it has one; nothing for a dead handle |
| A first follow, the writer's `resolvePointers`, rule 4 | as today: a vpos, or the header at `pos[i]` | the same |

**When dead handles are followed.** A handle dies when its node's object
is evicted, and stays in every pointer that holds it. Under eviction the
parents stay longer than their children: CLOCK keeps the upper levels,
which every lookup passes. So the way back to an evicted node is almost
always through a dead handle, about once per load of an evicted node; in
a database larger than its budget, that is the path of most cold gets.
In a database that fits its budget no handle dies, and this need never
arises.

* **T3a. The id in the handle,** `final long id`: 32 bytes (40 under
  ZGC).
  * Pros:
    * A re-resolution is a table lookup, with no read of the stream to
      learn the id. If the node is resident again through another pointer
      (38 to 72 percent of resident index objects have more than one
      parent, 004-01, 3.3), the reader takes that object and reads
      nothing.
    * It fits T7a: the reader finds the live handle first, then loads
      under its monitor, so no two readers load the same node. Without
      the id the reader must read before it has the handle (T3b's cons).
    * T1c stays possible without changing the handle.
    * A dead handle still names its node: the audit can check dead
      handles, and a heap dump can be read.
  * Cons:
    * 8 bytes more per handle, live or dead. Live handles: for compact
      keys (0.16 index nodes per KV) 1.3 bytes per KV, about 1 percent of
      the estimated MEM of 135 (4.11); for random 16-byte keys (2.16 index
      nodes per key) 17 bytes per key. Dead handles: 8 bytes more each
      (open point 8).
    * With T1a, a live handle's id is stored twice: in the handle and in
      the table's `Long` key.
* **T3b. No id in the handle:** 24 bytes (32 under ZGC).
  * Pros:
    * 8 bytes less per handle, live or dead: the numbers above, saved.
    * One copy of a live handle's id: the table's key.
  * Cons:
    * A re-resolution must get the id from `pos[i]`, in one of two ways:
      * The header first (`readNodeHeader`, as today's loader does for a
        first follow), then the table, then, if the node is not
        resident, the node's own read. One more random read per
        re-resolution when the header's page is not in the OS cache:
        from s1's disk 0.37 to 0.88 ms (004-02), before the read of the
        node. Even a node that is resident again through another pointer
        costs that read.
      * The node first, read at `pos[i]`, then the table by its id. No
        extra read when the node is not resident, but the read comes
        before the reader has the handle: it holds no monitor, so two
        readers may load the same node (T7a's guarantee lost on this
        path); a node resident again through another pointer is read for
        nothing; and Rule R, which is looked up by id, can only be applied
        after the read, which may then have read an older version than
        needed.
    * The writer's cache of ids by position (`idByPos`, 100,000 entries
      under one global lock) would serve the readers too, or the readers
      read headers.
    * T1c would need the field back, at T3a's size.
* **Why T3a was proposed.** BergDB optimizes for large databases and for
  worst cases first; a read from disk costs about 100 times a lookup in
  memory (Frans, 004-03, section 1). T3b saves 8 bytes per handle, about 1
  percent of the memory for compact keys, and pays for it on the slow path
  of cold gets: a random read more, or loads without T7a's monitor. T3b
  would pay off in a database held in memory, with long random keys: no
  dead handles, so no reads to save, and 17 bytes per key.
* **T3c, a variant: the id only in dead handles.** A live handle has no id
  field (24 bytes; with T1a the table's key has the id); when the evictor
  kills a handle, it puts the id in `obj` as a small object (a `Long`, 16
  bytes), which the fast path tells from a node by its type. Live handles
  cost T3b's 24 bytes, dead ones 40; a re-resolution reads nothing. Cons:
  an allocation per eviction; `obj` typed `Object`, with a type test on
  the fast path; more to get right. Not proposed now: a later step if
  phase 5 shows that handles' memory matters.
* Proposed: T3a; T3c later if handles' memory matters.

**T4. The type of `KeyNode.pointers`: T4b, decided.**

* T4a. `Object[]`, a handle or a `ValueNode`; the klong says which, a cast
  where it is used.
* T4b. A common interface for handles and value nodes: `Pointee` (4.2).
* T4c. Two arrays, `Handle[]` and `ValueNode[]`: more memory.
* Proposed: T4a.

**T5. A reader's load over the budget: T5a, decided.**

* T5a. An eviction thread per database, woken by the reader, that takes
  the write lock between transactions and runs batches. The reader never
  waits; eviction stays under the write lock, as the model has it.
* T5b. The write lock becomes a `ReentrantLock`, and the reader evicts only
  if `tryLock` succeeds: 32 places that use the monitor change.
* T5c. The reader only sets a flag, and the writer evicts at its next
  boundary: no eviction in a workload without writes.
* Proposed: T5a.

**T6. The barriers of the fast path: T6b, decided, with the argument of
3.4.** A plain read of a pointer to a handle; an acquire read of a pointer
to a value (3.4, point 5).

* T6a. An acquire read of `pointers[i]` and of the handle's object: an
  explicit edge on every hop.
* T6b. A plain read of `pointers[i]`, safe as argued (the id final, the
  object volatile, a null sends the reader to the slow path), one barrier
  less per hop.
* Proposed at first: T6a (Frans: "A barrier is needed."); T6b only if step
  3c measured the second acquire as dear and the jcstress tests passed
  with it.

**T7. Loads under the handle's monitor: T7a, decided.**

* T7a. A loader holds the handle's monitor during the read, the state
  LOADING: no two loads of the same node, and waiting readers need that
  node anyway; the evictor skips LOADING handles.
* T7b. Load without a lock, install by `compareAndSet`: two readers may
  both read the same node from the stream; no monitor at all.
* Proposed: T7a (Frans: "If we read from disk, locks are relatively cheap
  compare to the time to read from disk.").


# 7. Open points, settled in the steps

1. **Rule R on the fast path** (4.4): the model in 2a says whether the
   test with `pos[i]` is enough.
2. **Stale reads of `pos[i]`** while the writer applies Rule R in
   `resolvePointers` (3.3): the model in 2a.
3. **A vpos in `pos[i]`.** Today's Rule R compares a vpos with positions as
   numbers (`followStreamPointer`, step 2); 4.6's rule would too, and the
   fast path sends a vpos pointer to the slow path unless its object is
   canonical (4.4). The model in 2a says whether a vpos needs a case of its
   own in the record rule (004-01, 4.4: "a vpos handled as Rule R
   does").
4. **K**, the steps of a batch (4.7): measured in 3b.
5. **The table's whole-table operations** with a lock per map (1b): the
   audit and the tests say whether any needs the table frozen.
6. **Value-heavy leaves** (4.8): phase 5.
7. **The collector:** the docs recommend ZGC or generational Shenandoah
   for the 20 ms target (004-04); which of them is Frans's choice, open
   since 004-04.
8. **Dead handles' memory** (4.7). Under eviction, a resident parent keeps
   the dead handles of its evicted children until it follows them again
   or is evicted itself: at most one per pointer, about 16 a key node, 32
   bytes each, next to a key node of about 400 bytes (006-02: 63.6 bytes
   per KV in key nodes, about 0.16 key nodes per KV). Counted (4.7);
   measured in phase 5, with LargerThanMemory and P4's soak.


# 8. The measurements: the table

TableBench ([02-implementation-plan/TableBench.java](02-implementation-plan/TableBench.java),
run by [run.sh](02-implementation-plan/run.sh)) fills a table with n handles
(ids odd numbers in a scattered order, as `Spos.nextVpos` makes them; the
map by `mapIndex`), and times every put; a put that resizes a map is timed
alone. F53, JDK 27 (Homebrew), compact headers, 2026-10-25 16:11 to 16:14,
with no other JVM running (this session read files meanwhile). Each run in
a JVM of its own. The outputs:
[out/table.txt](02-implementation-plan/out/table.txt) and the GC logs.

The resize of one map, at the largest and the next largest size reached:
median and largest, in ms (the count is 256 or 4,096 resizes):

| Entries | Collector | maps256 (today) | maps4096 (T1a) | intr4096 (T1c) |
|---|---|---|---|---|
| 1M | ZGC | 0.087, 0.162 | 0.005, 0.053 | 0.004, 0.041 |
| 10M | ZGC | 0.738, 2.04 | 0.044, 0.183 | 0.043, 0.443 |
| 30M | ZGC | 11.6, 19.3 | 0.233, 1.16 | 0.388, 1.01 |
| 100M | G1 | 3.77, 255 | 0.197, 254 | 0.204, 233 |

At 100M the largest values are G1's evacuation pauses during the fill (204
to 393 ms, the GC logs), not resizes: the medians are the resizes. ZGC's
heap at 100M would have needed an estimated 22 GB, so G1 ran it. A resize is
dearer under ZGC than under G1 (maps256's resize to 2^18: 11.6 ms against
2.3), likely its load barriers and its larger references.

Heap bytes per entry, handles included, at 10M:

| | G1 (compressed oops) | ZGC |
|---|---|---|
| handles alone, in an array | 36.5 | 51.6 |
| maps4096 (T1a) | 79.0 | 113.2 |
| intr4096 (T1c) | 47.0 | 65.0 |

Filling 30M took 8.4 s with maps4096 and 5.2 s with intr4096 (ZGC).

What it shows:

* **4,096 maps are enough** for 009's sizes: a resize stops one map for
  at most about a millisecond up to 100M entries (0.2 ms measured under
  G1; about 0.8 ms under ZGC, extrapolated from 30M), against the 20 ms
  target. At 100M compact keys BergDB has about 16M index nodes; at 100M
  random 16-byte keys about 216M, where a resize would take about 2 ms
  under ZGC (extrapolated).
* **Today's table is a stop of its own.** With values in it (1.10 entries
  per KV), a database of 30M KVs has resizes of about 12 ms under ZGC, and
  every reader's load and the writer wait for them on `bigLock`. Step 1b
  removes it, before handles.
* **The intrusive table saves about 32 bytes per entry** and fills faster,
  with the same pauses.

How to rerun: `items/009-handles/02-implementation-plan/run.sh OUT_DIR` on
a quiet machine (about 3 minutes; the 100M runs need 16 GB of heap).


# 9. Changes made in the implementation

Recorded 2026-10-25 during phase 3 (the branch `009-handles`), with what
found each:

* **The written position and a re-resolve** (phase 2's runs, Handle.lean's
  header, choices 1 and 7). A handle's `writtenPos` is set only by an
  eviction, from a canonical object's position (Cache3.evict). When the slow
  path follows a pointer that holds a dead handle, it takes as the reference
  the newer of the pointer's after Rule R and the dead handle's written
  position, writes that back into the pointer (no record changes: the
  record rule gives the same before and after), and compares the live
  handle's object with it. The live handle's written position is not
  changed, so 3.3's row stays true: no reader writes `writtenPos`. (The
  model first kept the position in the live handle instead; it is being
  aligned with Java.)
* **A vpos is older than any position** where references are compared
  (`Spos.newer`: Rule R, the record rule, the slow path), not by its number
  (open point 3).
* **Values have no handles**: the startup's registration skips them
  (`Cache3.register`); they were registered as canonical objects before.
* **Maintenance reads are keyed by the version a pointer names**, its
  reference raised as above: reclaim's step read a stale version through a
  key by position (Eviction.testReclaimWithMissesF, whose twins compare
  streams byte for byte, found it).
* **A read that keeps nothing** (a cache policy that caches nothing) leaves
  no empty handle in the table (`Cache3.dropIfEmpty`).
* **A CLOCK batch is bounded by the handles it examines** (4,096, or 65,536
  under pressure) and by two rounds of the hand, not by K maps (4.7): with
  16 maps a batch freed almost nothing in a small database
  (CapacityTester). The trigger is raised only after a round that met no
  detachable object (pinned state above the budget), not one that only
  cleared CLOCK bits.
* **Large values** leave memory when their record is written: those the
  transaction made (the writer's list, `Eviction.largeValueCreated`) and
  those of the key nodes written (`recordWritten`); 4.7 had them with the
  batches.
* **Tests sample the resident bytes after the eviction thread's batch**
  (`Eviction.awaitBatch`), as a reader no longer runs it (T5a).
* **A swizzle is a release store under the node's monitor** (C2):
  `KeyNode.setPointee`, `setPointer` and `swizzle` store with
  `setRelease`, which pairs with the fast path's acquire read of a pointer
  to a value (C5; step 3c). A reader's swizzle is a compare-and-set under
  the monitor (`Node.swizzle`, step 3d), as 3.3's row of `pointers[i]`
  says: it replaces only what the reader read in the pointer, and its
  write-back of the reference only raises it (`Node.raiseRef`). In step
  3c both were plain stores, and a reader could replace a newer handle
  that the writer had put there with a dead one of its own, or lower a
  reference that another reader had raised: the written position of the
  node's last record was then lost, and the next follow read an older
  version. Step 3d's test of readers under the capacity controller found
  it, as stale reads (`get(k21)` gave transaction 70's value, not 82's),
  in 2 runs of 9; after the change, none in 20. The writer's swizzle
  replaces whatever is there: its handle holds the canonical object. A
  reader that stores a handle that an eviction killed meanwhile leaves a
  dead handle in the pointer, which the next follow resolves again
  (`EvictionReaderTester.testDeadHandleInAPointer`).
* **`pos[i]` is read and written plainly**, not opaque (3.3): BergDB
  relies on a 64-bit JVM, where a plain long does not tear (JLS 17.7 allows
  it elsewhere), as it did before 009, whose searches read `pos[i]` without
  a lock. A reader's slow path writes `pos[i]` too, the raised reference,
  under the node's monitor; 3.3 had the writer only.
* **The pointer locks** (`PointerLocks`) are off every follower since step
  3c, the writer's and the maintenance follower's included: they read a
  pointer's pair under the node's monitor.
* **The eviction thread gives way to a writer** that waits for the write
  lock (`Db.writersWaiting`; step 3d). A monitor is not fair: with readers
  that kept loading, the thread ran batch after batch and the writer waited.
  Found by step 3d's new `level4.sh` run (ReclaimReaders, 4 readers, a 20 KB
  budget): 132 s where the random schedule took 4 s, the writer blocked on
  the write lock in every thread dump; 4 s after the change. s1's pause
  probe at a 20 MB budget showed it too: 2,583 commits in a minute under G1
  where 2026.1 made 221,900.
* **The trigger is the budget, or the pinned bytes plus the gap** between
  the watermarks if that is more (step 3d, second commit): each round of
  the hand counts the bytes of the objects that are not detachable, and a
  batch goes down to the low watermark or to those bytes. With pinned state
  above the budget, the controller then runs once the detachable objects
  have grown by the gap. 3b raised the trigger only after a round that met
  no detachable object, and readers that kept loading kept the batches
  going (3d's first commit tried a back-off after two rounds above the
  budget instead).
* **A batch is bounded by time too**, 2 ms (`Eviction.BATCH_NANOS`), as
  well as by its handles and two rounds (step 3d, second commit): at step
  3c s1's pause probe had batches of up to 100 ms, and a writer waits for
  the batch in progress. If the resident bytes are still over the trigger
  after a batch, the eviction thread goes on, batch after batch, woken by
  the writer's transaction end as well as by loads, giving way to a waiting
  writer before each, and stopping after a batch that freed nothing.
* **Loads wait for eviction when it falls behind** (step 3d, second
  commit): a reader's load that finds the resident bytes over the trigger
  by more than the gap waits up to 2 ms for the eviction thread's next
  batch (`Eviction.LOAD_WAIT_NANOS`), so that loads, which grow the
  resident bytes, go at eviction's pace. At step 3c the resident bytes
  went far above the budget on s1, where two readers and the thread share
  two CPUs.
* **The pointer locks are gone** (`PointerLocks`, `Db.Internal.getPointerLock`,
  `Cache.DbInfo.getPointerLocks`; step 3d); `Cache.DbInfo` has no methods.
* **An eviction reads the handle's object after its compareAndSet** to
  DEAD (`Cache3.kill`'s callers; step 3d): a loader sets the object only
  while the handle is LOADING, so not after it, but it may have installed
  one between the evictor's read and its compareAndSet. Read before, the
  object stayed in the dead handle; the audit's new check found it in
  `CapacityTester`'s f-test.
* **The values of pinned key nodes leave memory** in the batches (step 3d;
  4.8): a pinned object is never evicted, so the values that reads loaded
  into D's leaves stayed resident. s1's pause probe at a 100 MB budget
  ended with 153 to 181 MB resident under G1 in step 3c; 2026.1's sweep
  took such values first.
