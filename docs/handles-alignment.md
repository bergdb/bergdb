# BergDB Level 4 with handles: the Java code and the Lean model

Written 2026-10-26 by Claude (Opus 5.5, Claude Code) for Frans Lundberg,
as step 4b of bergdb item 009
([items/009-handles/](../items/009-handles/readme.md); 009-01, phase 4). It
does for handles what [level4-alignment.md](level4-alignment.md) does for
the design before them, which stays as its history: the mapping α from
Java's state to the model's, and the register of where they differ.

Java: the branch `009-handles` at step 3d (java/src/bergdb/dag/Handle.java,
dag/KeyNode.java, dag/TopNode.java, core/Cache3.java,
core/NodeCollection.java, core/Eviction.java, core/Residents.java). The
model: lean/SIS/Handle.lean (trusted, like Evict.lean), with the statements
in lean/SIS/HandleTheorems.lean. The design both follow:
[02-implementation-plan.md](../items/009-handles/02-implementation-plan.md),
section 4, and its section 9, what the implementation changed.


## 1. What is proved

* **T-CACHE over handles** (`tc_handles`, `TC_handles_records`;
  lean/SIS/Proof/HandleRecords.lean, step 2d, 2026-10-26): from the startup
  with handles from R(0), with any reads and evictions between transactions
  and no restart, the physical writer with handles appends exactly the
  model's records and leaves the model's D, and the memory keeps the
  invariants of `TC_handles` (the table and the handles, INV-CAN, INV-SNAP,
  INV-SLOT for the record rule, Rule R, live handles without a written
  position).
* **T-READ, T2-C and T-PIN over handles** (phase 4a, 2026-10-26):
  `tr_handles` (a read through the handles at any time up to the last record
  gives P at that time; SIS/Proof/HandleReadT.lean), `t2_handles` and
  `tr_handles_restarts` (the same with restarts: the records and D stay the
  model's, and reads give P; SIS/Proof/HandleRestart.lean), and `tp_handles`
  (every object outside the pinned set may be evicted;
  SIS/Proof/HandlePin.lean). Java's runs are checked against the model by
  the trace checker through the trace format of the design before handles,
  and since step 4c through their handle state itself (section 4).


## 2. The mapping α

| Java | Model (SIS/Handle.lean) | Notes |
|---|---|---|
| An index node's object (`KeyNode`, `TopNode`), by identity | `HObj`, by address | canonical flag, version, history as in Evict.lean |
| A value (`ValueNode`), held directly by a leaf's pointer | a data node with a handle, like an index node | register R1 |
| Pointer i of an object: `pointers[i]` (a `Handle`, a `ValueNode` or null) and `pos[i]` | `HPtr`: `handle` (a handle's number, or none) and `ref` (a record, or none for a vpos) | `pos[i]` is the serialized reference, never access data |
| `Handle`: `id`, `obj`, `writtenPos`, `state` | `Handle`: node, object, written position, dead | `LOADING` is not modeled (R2) |
| The node table, `Cache3`'s 4,096 maps of live handles | `HMem.table`, node to live handle | one live handle per node (`HTableOK`) |
| `Handle.usable(o, ref)`, the fast path's test | `HObj.usable` | a canonical object, or a version at or after the reference |
| `NodeCollection.followPointer` (the fast path) and `followStreamPointer` (the slow path: Rule R, `newerPos` with the held handle's written position, `Node.raiseRef`, `Cache3.liveOrNewHandle`, the load and `Cache3.install`, `Node.swizzle`) | `HMem.followR`: the fast path; the slow path with `ruleRRef`, `maxRef`, `HMem.setRef`, `HMem.resolve`, `HMem.load` | Handle.lean's header, choices 1, 3 and 7 |
| The writer's follower and `Cache3.makeCanonical` | `HMem.follow` with `HMem.promote` | choice 8 |
| `Handle.serializedRef`, the record rule | `HMem.ptrRef`, `HMem.refOf` | 02, 4.6; choice 3 for a vpos |
| `NodeCollection.resolvePointers`, the records' writers | `HMem.writeNode`, `HMem.writeNodes`, `handleTrans` | choice 2 |
| `Residents.isPinned`, `Eviction.detachable` | `HMem.pinned`, `HMem.evictable` | the super root, D, the record being written, the newest written top node |
| `Cache3.evict` and `kill`, `Cache3.clockStep` | `HMem.evict` | the written position set only here (choice 1) |
| `Eviction.unswizzleValue` (values of pinned leaves, large values) | an eviction of the value's handle | R1 |
| Startup: `DbStarter`, `Cache3.register`, rule 4 by id | `handleStartup`, `Mem.toH`, `HMem.linkD` | |
| Reads and the eviction batches between transactions | `HCacheOp` (`read`, `evict`) and `runHandles` | R2, R3 |


## 3. The register

Where Java and the model differ, and why the model's theorem still speaks
for Java.

* **R1. Values have handles in the model, not in Java** (choice 5). A value
  has one version, written in the record of the transaction that makes it,
  so every object of it is that version and a pointer's record for it is
  its position either way. Java's unswizzle of a value (a large value once
  written, or a written value of a pinned leaf in a batch) is, in the
  model, an eviction of the value's handle, allowed as the value is written
  and D holds index nodes only.
* **R2. The model's operations are atomic; Java's run concurrently.** Readers
  follow pointers while the writer runs a transaction and while the
  eviction thread runs a batch. What Java relies on, and where it is argued
  or tested:
  * The fast path's barriers (02, 3.3 and 3.4: C1 to C5), tested by the
    jcstress tests in java/stress/jcstress/ (009-03, section 2).
  * Every change of a pointer's pair under its node's monitor; a reader's
    swizzle a compare-and-set and its write-back of the reference monotonic
    (02, section 9; `EvictionReaderTester`'s readers under the capacity
    controller found the lost update that both prevent).
  * A loader holds the handle's monitor and its state is `LOADING`, so an
    eviction, a compareAndSet from `LIVE` to `DEAD` under the map's lock,
    never takes a handle being loaded and never waits for one (T7a).
  * An eviction reads the handle's object after its compareAndSet (02,
    section 9; the audit found the dead handle with an object).
  * A reader reads a handle's written position without the write lock (02,
    section 9: it misses no position that its lookup time needs).
  * Readers read only times before the transaction in progress, as at
    Level 4 before handles (level4-alignment.md, 7.4).
* **R3. The eviction schedule.** The model allows any evictions between
  transactions, in any order. Java's capacity controller chooses by CLOCK,
  in batches bounded by time and handles, in the writer at a transaction's
  end and in the eviction thread under the write lock between transactions:
  one schedule among those the theorem covers. The bytes, the CLOCK bit, the
  trigger and the thread are not in the model.
* **R4. Objects a reader still holds** (choice 4): in the model an object
  that leaves its handle leaves memory; in Java the garbage collector keeps
  it for a reader that holds it, which may finish with it, as it is the
  version at its position.
* **R5. A load that finds no version** changes nothing in the model (choice
  6); Java throws.
* **R6. Restarts** are in `T2_handles`, not yet proved. Java's startup
  registers handles by id and links D by them (rule 4), as `handleStartup`
  does.
* **R7. The top nodes' skip list** (`TopDs`): the model's root object stands
  for it, as in Evict.lean.


## 4. How Java is checked against the model

* **The trace checker, C-P** (`conformance.sh evict`, `level4.sh` step 5):
  the trace exporter (`stress/TraceExport.java`) maps the handles to the
  trace format of the design before them (a pointer whose handle holds an
  object usable for it is a memory slot to that object, any other a stream
  slot with its serialized reference), and the checker's C-P checks them
  against Evict.lean's physical states.
* **The trace checker, C-H** (step 4c, 2026-10-26; the same runs): the
  exporter also writes run E's memory as the model's memory with handles, by
  α of section 2, at each transaction's end and under the write lock (HMEM,
  HTABLE, HANDLE, HOBJ and HPTR lines; level2-alignment.md, 9.2), and the
  checker's C-H (`handleFailures`, lean/Check/Steps.lean) checks it against
  the invariants of HandleTheorems.lean, which the model's theorems prove:
  `HTableOK` (the table and the handles, a pointer's handle of its
  pointee); `HCanOK` and `HSnapOK` (by position, and an object's history by
  its number of entries and its contents: a hash of the entries, which the
  exporter writes and the checker computes from P's node or the stream's
  version, FNV-1a with 64 bits over the entries as on the trace's H lines;
  level2-alignment.md, 9.2); `HSlotOK`, with the model's own record rule
  (`HMem.refOf`) on Java's pointers, handles and objects; `HRuleROK`;
  `HLiveWrittenOK`; `HWrittenOK`, and that a pointer names a pointee of its
  object's history; `HFastOK`; T-PIN's first part, every object outside the
  pinned set written; and 02's 4.1 and 4.10, no handle loading at a
  transaction's end and a dead handle never live again. Run E reads between
  its transactions in four configurations of the set, and restarts in three
  (TraceExport's `ereads` and `erestart`): without reads its states held no
  snapshot (the writer promotes what it follows), and without a restart
  Rule R is R(0)'s, about which `HRuleROK` says nothing. C-H also counts how
  often the states reach the cases that HandleExample.lean's runs found
  (`pointCounts`): a pointer written with its dead handle's written position
  (choice 1 of Handle.lean), with a vpos (open point 3), and snapshots of
  nodes in the startup section after a restart; open point 1's case (a
  snapshot that a pointer older than the section names) does not occur, as
  in the model's runs, since the slow path writes Rule R back.
  What C-H does not check: values, which have no handles in Java (R1; C-P
  checks their slots); the virtual root's object, which Java does not have
  (R7); the operations' interleavings (R2: it sees states between
  transactions); the CLOCK bit and the bytes (R3); T-PIN's second part,
  which is the definition of `HMem.evict`. A history is compared by its hash,
  not entry by entry: a history with other entries and the same hash would
  pass, about one chance in 2^64 for a given pair. A pointer that leads to no
  object that may serve it and whose reference is before the stream's first
  record (reclaim's cut, M33) is not checked against the record rule, as
  C-P's dead slots.
* **The audit** (`core/Audit.java`): INV-CAN, the pins and INV-SLOT as
  before, and the handles: a live handle that a pointer of a resident object
  holds is the table's, a dead one has no object.
* **EvictionInvariance**: the same stream byte for byte with every
  schedule, the capacity controller's included.
* **StreamDigest** against release 2026.1 after every step of the branch:
  the same digests (36 of 36), so the records did not change.
