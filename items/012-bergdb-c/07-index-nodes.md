012-07. Task: the index nodes
=============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done, 2026-10-28 17:30** (started 16:19), in
the clone `/Users/f/fl/bench/012/07-index-nodes/`, for the conductor to
check and copy in; approved with 012-01 by Frans's go (012-01, 9.1).
Phase B (012-01, section 8). Effort: max. After: 012-04, 012-06.


# 1. The goal

The nodes of the index in C, ported faithfully from `dag`: klongs, key
nodes with their versions, value nodes, top nodes and the top node
structure, with pointers and their serialized references; their writers,
to the bytes Java writes. This is BergDB's core data structure, and the
largest single port (`KeyNode` alone is 1,219 code lines).

Done when:

1. `Klong` complete: every type of klong, its time, length and compare
   value, the order of klongs.
2. Key nodes: their klongs and pointers, the versions and the time index,
   `searchLte` and `searchEq` at a time, adding and changing entries, the
   delete bitmap, `toPreviousState`, the checks (`check()`), and the
   splits and replacements at the maximum node size, as `KeyNode` does
   them.
3. Value nodes, and top nodes with `TopDs`: the super root, top node
   ordinals (up to 2^48 − 1, 005-02), root times, skip pointers,
   `findRoot` at a time, new top nodes.
4. Pointers: a memory pointer or a stream pointer, the node's position and
   id, vpos, and the serialized reference as Java decides it (`Handle`,
   009). The representation chosen here also serves eviction (012-12).
5. Writers: `StoredKeyNode.toLongs`, `StoredTopNode.toLongs`,
   `StoredValueNode.toBytes`, with their checksums; every node of every
   reference stream, parsed (012-06) and written again, gives its bytes.
6. Java's tests of these classes ported where C has the behaviour:
   `KeyNodeTester`, `TopTester`, the `@Nano` tests of `KeyNode`, `Klong`,
   `TopNode`, `TopDs`, `ValueNode`. All pass.


# 2. Read first

* Java, `dag`: `Klong` (191 code lines), `KeyNode` (1,219), `TopNode`
  (245), `ValueNode` (171), `TopDs` (136), `Node` (38), `Pointer` (47),
  `Spos` (26), `Handle` (73), `KlongWithPointer`, `PutData`, `GetData`,
  `OpData`, `AccessData`, `Keys`; their testers.
* `docs/sis-model.md` (nodes, versions, pointers), 011-11 (how Java maps
  onto the model), 009-02, section 3 and 009-05 (handles, serialized
  references), 005-02 (ordinals), 005-50 (node sizes); 012-01, 4.5
  (memory).
* 012-02, sections 6 and 7.


# 3. The work

1. **Design first**, written in this file before the code: the C structs
   of the nodes and of a pointer; how a node is identified (id, the
   canonical object, the node table); what a "handle" is in C
   (recommended: as Java's, a small struct per node with the node's id,
   its object or none, and `writtenPos`, so that a pointer's serialized
   reference is decided as Java decides it; live in the node table, or
   dead after an eviction and freed when no pointer holds it; Java's
   LOADING state serves concurrent loaders, which C does not have); and
   memory as 012-01, 4.5 says. For that, list every field in Java that
   holds an index object, a handle or a value beyond a call (the holders
   that count), and every place that changes such a field, so that each
   change keeps the counts; and the pending list with its safe points.
2. Port `Klong`, then `KeyNode` method by method, keeping Java's names in
   comments (`/* KeyNode.searchLte */`) so that a reader can follow both.
3. `ValueNode`, `TopNode`, `TopDs`.
4. The writers, and the round trip of done item 5 as a test over
   012-05's streams.
5. The ported tests.


# 4. Tests

The ported Java tests; the round trip of every node of the reference
streams; random tests of a key node against a simple model (a sorted list
of (compare value, time, entry)) for searches at random times after
random changes, under the sanitizers; after each change, the recount of
012-01, 4.5 agrees with the counts, and after the last free the
allocator's count is 0.


# 5. Notes

* Faithful before clever (012-01, 4.2): the split points, the order of
  entries, when a TIME klong is added, the sizes at which a node is
  replaced: all as Java, since they decide the bytes. Where Java's code
  looks wrong, write it in this file's notes and keep Java's behaviour; a
  real bug goes to 005 (012-01, section 9).
* Java's integer arithmetic (012-04's rules) matters most here: klongs
  pack lengths, types and times into 64-bit numbers.

**Where Java looks odd** (found in the port, 2026-10-28; Java's behaviour
kept in C in each case):

1. **`KeyNode.checkIncreasingTime` checks nothing**: its `time` starts at
   `Long.MIN_VALUE` and is never updated in the loop, so no time klong is
   ever `<= time`. `check()`, `assertOk` (Dag's asserts) and
   `validateStreamNode` (`DbStarter`'s check of the section's key nodes
   at a start) take a node whose time klongs decrease. A real defect of a
   check, not of the bytes: finding F1 in Progress, with its probe. C's
   `check_increasing_time` is Java's, vacuous too.
2. **`searchFirst` takes the first of equal compare values**, not the
   latest: its test is a strict `<`, where `searchGt` and `searchGte` have
   `<=`; so of a key put twice it returns the older pointer. No
   production code calls it (`GetMany` takes the first key with
   `searchGt(time, -1)`, which gives the latest); a test shows it
   (`knode_search_first_takes_first`).
3. `getLastDeleteBitmap(sz)` ignores `sz` and reads `this.size`; its
   callers pass the size. Harmless.
4. `addToEnd`'s test `klongs.length + 1 > sz` is always true;
   `ensureCapacity` decides. Harmless.
5. `getInfo` sets `lastCompareValue = klong` where the compare value is
   meant; debug text only, not ported.
6. `toPreviousState` leaves the dropped slots' pointees in place (only
   concurrent readers can read them); C releases and clears them (6.5).
   No reader and no byte depends on them.


# 6. The design

Step 1 of section 3, written before the code (2026-10-28, 16:20 to
16:45). The modules are in section 6.6; Java's names are kept in the
comments of the code (`/* KeyNode.searchLte */`).

## 6.1 The objects

Java's index objects, values and handles are four kinds of C objects,
each a `malloc`ed block (through `mem`), with one common head:

```c
struct obj {                 /* every counted object (obj.h) */
    int32_t refs;            /* its counted holders (6.4) */
    uint8_t kind;            /* OBJ_KEY, OBJ_TOP, OBJ_VALUE, OBJ_HANDLE */
    uint16_t flags;          /* OBJ_PENDING, OBJ_MARK, and Java's booleans */
    struct obj *next;        /* the pending list's link, or a walk's */
};
```

The flags are Java's booleans and the handle's state: `OBJ_DIRTY`
(`isDirty`), `OBJ_CANONICAL` (`isCanonical`), `OBJ_IN_TRANS`
(`isInTransNodes`, `ValueNode.isInTransactionNodes`), `OBJ_LEAF`
(`KeyNode.isSegmentLeaf`, final), `OBJ_DEAD` (a handle's DEAD; LIVE
without it), `OBJ_REF` (`Handle.ref`, the CLOCK bit), and `OBJ_LEFT` (an
index object that a handle let go of, 6.3).

A *node* is Java's `Node`: the head and Java's two longs.

```c
struct node { struct obj o; int64_t id; int64_t spos; };      /* node.h */

struct knode {               /* KeyNode (knode.h) */
    struct node n;
    int16_t size;            /* KeyNode.size: klongs used */
    int16_t last_time_index; /* KeyNode.lastTimeIndex */
    int32_t cap;             /* klongs.length = pointers.length = pos.length */
    int64_t *klongs;         /* one block of cap * 24 bytes (MEM_INDEX), or NULL */
    int64_t *pos;            /*   = klongs + cap: each pointer's reference */
    struct obj **pointers;   /*   after pos: what each pointer holds */
    struct handle *handle;   /* KeyNode.handle: the back reference, not counted */
};

struct tskip { struct handle *p; int64_t pos; int64_t time; };
struct tnode {               /* TopNode (tnode.h) */
    struct node n;
    int64_t top_node_id;     /* the ordinal, 0 to 2^48 - 1 */
    int64_t root_time;
    struct handle *root_pointer;      /* counted */
    int64_t root_pointer_pos;
    struct handle *handle;   /* back reference, not counted */
    int16_t pointers_length; /* h, the ordinal's bit length (final) */
    struct tskip skip[];     /* pointers[i], pointersPos[i], pointersTime[i] */
};

struct vnode {               /* ValueNode (vnode.h) */
    struct node n;
    uint32_t offset_from_trans;  /* Java's int, read unsigned (005-34) */
    int32_t len;             /* the value's bytes; -1: a delete (value == null) */
    uint8_t value[];
};

struct handle {              /* Handle (handle.h) */
    struct obj o;
    int64_t id;              /* final */
    struct node *obj;        /* the node's one object, counted; or NULL */
    int64_t written_pos;     /* set by hd_kill only */
};
```

* **A key node's arrays** are one block, `klongs`, `pos` and `pointers`
  in turn, at Java's lengths (`ARRAY_SIZES` 2, 6, 14, 30, 62, 126, then
  `neededSize + 10`; `setContentFrom`'s `max(sz, other.length)`), so
  that the memory follows Java's; a growth allocates a new block, copies
  the three parts and frees the old one, as Java's `growCapacity`. Only
  memory depends on the capacity, no byte.
* **A top node's** skip pointers are fixed at its making (the ordinal is
  final), so they are a flexible array in the node's own block.
* **A value node** holds its bytes in its own block; its key is not in
  it, as in Java: the record (`TransNodes.keys`, 012-09) and the parsed
  node (012-06) have it, and the writer takes it as an argument.
* **Sizes**, without the allocator's own: a key node 72 bytes and 24 per
  array slot, a top node 80 and 24 per skip pointer, a value node 40 and
  its bytes, a handle 40. Java's estimates (`getMemSize`) are 80 + 24 per
  slot, 112 + 24, 56 + bytes, and about 40 for a handle.

**A pointer** is what Java's `KeyNode` and `TopNode` hold per pointer
since 009: *what it holds* (Java's `Pointee`), a `struct obj *` that is
NULL, a handle (an index node's) or a value node (`kind` tells which, as
`instanceof` in Java), and *its reference*, an `int64_t`, a position, a
vpos or −1. A top node's pointers hold handles only. The reference
written for a pointer is Java's record rule, `hd_serialized_ref`
(`Handle.serializedRef`, 012-02, 6.5). Java's `Pointer` (an output
parameter: `node`, `pos`, `index`) and `KlongWithPointer` (`klong`,
`pointerIndex`, `klongTime`, `node`, `pos`) are plain structs,
`struct pointer` and `struct kwp`, whose `node` is a borrowed reference
(6.4.2).

## 6.2 How a node is identified

As in Java:

* **The id**, `node.id`: a vpos given by the database when the node is
  made (`Db.setIdOfNode`, 012-02, 2.5; 0 for the creation's root key
  node), the same in every version, and never changed afterwards.
* **The position**, `node.spos`: the id until the node is first written,
  then the position of its latest version (set by the serializer,
  `prepareToSerialize`, 012-09). A key node's version also stores
  `prevPos`, its previous position (012-02, 6.3).
* **The canonical object**: the one object of a node that holds its whole
  history and can change (`OBJ_CANONICAL`), at most one per node; the
  writer changes only canonical objects. Other objects of the node are
  *versions*, read from the stream for older lookup times; a value node is
  always canonical (`vn_is_canonical`).
* **The node table** (012-12; the parts that 012-08 to 012-10 need before
  it, by whoever needs them first): node id to the node's *live handle*,
  at most one per id, and through it the node's one resident object,
  canonical or the newest version loaded. A value has no handle and is
  not in the table (009-02, 4.8): its pointers hold it directly.

## 6.3 The handle

As Java's `Handle` (009-02, 4.1), without what serves threads:

* **States**: LIVE (no flag), the node table's handle of its node, with
  an object or none; DEAD (`OBJ_DEAD`), evicted: out of the table, no
  object, never live again. Java's LOADING is left out: it lets one of
  several concurrent loaders read a node, and C has one caller, which
  loads in the call that follows the pointer. The CLOCK bit is `OBJ_REF`.
* **`hd_new(id)`**: a live handle with no object (`new Handle(id)`,
  `Cache3.liveOrNewHandle`). **`hd_of(node)`**: the node's back reference,
  or a new handle that holds the node when it has none (`Handle.of`: a
  test's node, the creation's, and the startup's adoption, `Cache3.register`
  of a handle made by `Handle.of`). **`hd_pointee_of`**: a value itself,
  else `hd_of` (`Handle.pointeeOf`).
* **`hd_set_obj(h, o)`**: the handle's object becomes `o` (counted), the
  object it held before is let go (released), with the back references
  kept right: what `Cache3.register`, `install` and `makeCanonical` do to
  `h.obj`. **`hd_kill(h)`**: `Cache3.kill` and the state change of
  `evict`: a canonical object's valid position into `written_pos`, its
  canonical flag cleared, the object let go, DEAD. The table's removal is
  the table's (012-12).
* **The back reference** (`KeyNode.handle`, `TopNode.handle`) is not
  counted, else a handle and its object would hold each other. Its rule:
  *an object's back reference is NULL or the handle that holds it*
  (`o->handle == h` implies `h->obj == o`). So a handle that lets go of an
  object (`hd_set_obj`, `hd_kill`, the handle's free) clears the object's
  back reference and sets `OBJ_LEFT` on it. Java keeps the back reference
  of an object that left its handle; it uses it only in `Handle.of`, and
  the survey (6.4.3, C(2)) found that no call of `Handle.of` or
  `pointeeOf` passes such an object (the writer passes canonical objects
  only, and a canonical object never leaves its handle while canonical).
  `hd_of` asserts it: an object with `OBJ_LEFT` and no back reference
  would get a new handle where Java returns the old one, and stops the
  test build.
* **What decides the bytes**: `hd_usable(o, ref)` (`Handle.usable`) and
  `hd_serialized_ref(p, ref)` (the record rule), ported exactly; the
  written position of a dead handle stays as long as a pointer holds the
  handle (its counts, 6.4), as Java's garbage collector keeps it.

## 6.4 Memory (012-01, 4.5)

### 6.4.1 The mechanism

* **Counts.** Every object counts its *holders*: the fields listed in
  6.4.2 as counted. A field that starts to hold an object retains it
  (`refs + 1`), one that stops releases it (`refs − 1`), the new one
  retained before the old one is released (they may be the same).
  Locals do not count.
* **The pending list** (`struct obj_ctx`, one per database, with its
  `struct mem`). An object is made with no holder and goes on the pending
  list at once (`OBJ_PENDING`, linked by `next`); an object whose count
  falls to 0 goes on it, if not on it already. Nothing is freed then.
* **Safe points** (`obj_collect`). At a safe point the code holds
  nothing uncounted that it will use afterwards. There, each pending
  object leaves the list, and is freed if its count is still 0. A free
  releases what the object's own fields hold: a key node its pointers
  0 to `size − 1` (handles and values), a top node its root pointer and
  skip pointers (handles), a handle its object (clearing the object's back
  reference). Each release can make another object pending, in the same
  loop, which ends when the list is empty: no recursion. In a database a
  free never takes a subtree (P1): every live handle is held by the node
  table, so releasing a child's handle frees at most a dead handle, and
  values. Outside a table (the tests, the creation's two nodes) a handle
  is held by its pointers only, and a free can go down a tree, still
  without recursion.
* **Why it is safe.** Between two safe points the code can hold any
  object in locals, in any order, as Java's code does: nothing is freed
  in between. At a safe point, an object that the code needs afterwards
  has a counted holder. So the ported code keeps Java's order line for
  line.
* **No cycles.** Counted references go from a key node to its children's
  handles and to values, from a top node to handles, from a handle to its
  object, and from the database's structures (6.4.2) to objects. The
  index is a DAG: a node never names itself or an ancestor, a top node
  only older top nodes and roots. The back reference, which would close a
  cycle, does not count (6.3).
* **The invariant** that close and the recount rely on: every live
  object has a counted holder that is itself live, or is on the pending
  list; so every live object is reachable from the database's roots (the
  node table, D, the record, its fields) and the pending list.
* **Failures.** A function that allocates allocates first and changes
  counts and fields after, so a NOMEM (`false` or NULL) leaves the counts
  consistent; the half-built objects are pending and go at the next safe
  point or at close. After the go point a NOMEM fails the database (P7;
  012-09), so nothing is undone.
* **Close** (`obj_free_all`): frees, once each, every object reachable
  from the given roots and the pending list, without trusting the counts:
  a walk that marks what it reaches (`OBJ_MARK`) and links it through the
  objects' `next`, as its stack and then as the list of what it reached,
  which it frees in a second pass. So it allocates nothing, never reads a
  freed object, and works after a failure too.
* **The recount** (`obj_recount`, a check for tests and the audit): from
  given roots (each one counted holder) and the pending list it reaches
  every object, subtracts one per counted holder it finds, checks that
  every count is then 0, and adds them back. It finds a count that is too
  low or too high, or an object held by something unreachable. 012-12
  gives it the node table, D and the record as roots.

### 6.4.2 The holders

From a survey of every production field of `dag` and `core` (2026-10-28,
a helper agent; Java at `1a45f31`) that holds a `KeyNode`, `TopNode`,
`ValueNode`, `Node`, `Pointee` or `Handle` beyond one call. *Counted*:
the field counts as a holder. *Borrowed*: it does not, and the column
says why that is safe: no safe point while it holds the object, or a
counted holder that holds the object meanwhile, or a stale entry that is
never read. The task in the last column ports the field.

| Java field | Holds | C | Task |
|---|---|---|---|
| `KeyNode.pointers[i]`, `i < size` | a child's handle or a value | counted | 07 |
| `KeyNode.pointers[i]`, `i >= size` (after `toPreviousState`) | stale handles and values | none: C clears and releases them (6.5) | 07 |
| `TopNode.rootPointer`, `TopNode.pointers[i]` | handles | counted | 07 |
| `Handle.obj` | the node's object | counted | 07 |
| `KeyNode.handle`, `TopNode.handle` | back reference | not counted; the rule of 6.3 | 07 |
| `Cache3.maps` (id to live handle) | live handles | counted (the table) | 12 (08 to 10 as they need it) |
| `TopDs.superRoot` | the super root | counted | 07 (`struct topds`) |
| `Db.newestWrittenTop` | the newest written top node | counted | 09 |
| `TransSeq.TransInfo.gotDirtyNodes` (D) | dirty canonical objects | counted, each entry | 09 (10 rebuilds) |
| `TransNodes.topNodes`, `keyNodes`, `valueNodes` (the record) | taken nodes; the transaction's values and delete nodes (a delete node has no other holder) | counted until `clear` | 09 |
| `GetMany.Chain.linkNodes` | the chain's key nodes, versions and temporaries included | counted (the cursor), released by `removeLink` | 08 |
| `Eviction.largeValues` (holder, index, value) | key nodes and values over 1 MiB | counted, or rebuilt by eviction | 12 |
| `NodeCollection.MaintenanceFollower.read` | versions read in a reclaim step, not installed | counted if a safe point falls inside the step; else borrowed | 11 |
| `DbStarter.posMap`, `superRoot`, the temporary `Dag`, `linkD`'s `byPos` | the section's newest versions; handles | counted if a safe point falls while they hold (between records); else borrowed | 10 |
| `StoredTrans.nodes`, `Stored*Node.node` | parsed nodes | none in C: 012-06's parse makes views, not objects; 07's constructors (6.6) make objects from them | 06, 07 |
| `Db.opMarks` | the op's followed, made and changed nodes | borrowed: cleared at `endOfOp`, before any safe point | 09 |
| `Db.replacedInTrans` | replaced key nodes and super roots | borrowed: each stays canonical in its live handle (counted) until the transaction ends, as eviction runs only at a call's end (012-12); 09 may count it | 09 |
| `ExecuteData.transInfo` | a `TransInfo` (D's after `store`) | borrowed alias of D's struct; not an object | 09 |
| `OpData.kwi.node`, `OpData.tempPointer.node`, `PutData.oneKwi`/`twoKwis` `.node`, `KeyAccessPath.nodes` | the last search's result; the op's new nodes; the writer's path | borrowed: read only within the op; C clears them at the op's end, so no stale pointer outlives a safe point | 08 |
| `GetData` kept by `Trans.warmupGetData`, `GetMany.gd`, the Pub layer's | as `OpData` | borrowed, cleared at the op's end; the Pub layer is not in 012 | 08 |
| `StoredTrans.Serializer.transNodes`, `topNode`, `gotDirtyNodes` | the last record's | borrowed: never read after the write; C's serializer keeps none | 09 |
| `Reclaim.TouchCounter` maps, `Dag.Walked`, the debug walks' sets | nodes of one call | borrowed: no safe point inside | 08, 11 |
| `KeyNode.countedMemSize`, `TopNode.countedMemSize` (Residents) | a number | not a holder; 012-12 counts bytes by the allocator | 12 |

### 6.4.3 Every place that changes a counted holder

Each C function keeps the counts itself, so a caller never adjusts a
count by hand. The ones of this task, with the Java they port and its
callers (Java line numbers of `1a45f31`):

* **Key node pointers** (`knode.c`):
  * `kn_add_klong` (`addKlong` 805 to 849): a new TIME klong's slot holds
    nothing; the new key klong's slot holds `hd_pointee_of(node)`.
    Callers: `Dag.setValue` 695, `setNode` 746, `appendKlongs` 892,
    `timeSplitInPlace` 979, `timeSplit` 1062, `spaceSplitInPlace` 1014 and
    1016, `spaceSplit` 1131, 1133, 1156, 1158; `addDeleteKlong` 794 (none).
  * `kn_add_to_end` (`addToEnd` 950): the slot holds the given pointee
    (retained). Callers: `nodeWithTime` 133, `lastVersionGivenDel` 1063,
    `firstAndSecond` 1243 to 1271 (copies of `last`'s pointees, so the
    halves share handles and values with the replaced node), the
    constructor from a parsed node (`StoredKeyNode.parse` 158; nothing).
  * `kn_replace_klong` (`replaceKlong` 858 to 882): the slot's pointee is
    replaced (new retained, old released). Callers: Dag 978, 1061.
  * `kn_add_to_sorted` (`addToSorted`, on `lastVersionGivenDel`'s new
    node): insert (moved slots keep their counts) or overwrite (replace).
  * `kn_set_content_from` (`setContentFrom` 1004): new arrays holding
    `other`'s pointees (retained); the node's old pointees released.
    Callers: `Dag.timeSplitInPlace` 982, `spaceSplitInPlace` 1004.
  * `kn_to_previous_state` (`toPreviousState` 975): the slots past the new
    size are released and cleared (6.5). Callers: `Dag.handleFullNode`
    965; `DbStarter` 223, 491; `NodeCollection.readVersion` 551.
  * `kn_set_pointee`, `kn_swizzle`, `kn_set_pointer` (275, 294, 306):
    replace. Callers: `NodeCollection.followStreamPointer` 505, 507,
    `followValuePointer` 588, `resolvePointers` 671, `linkToCanonical`
    738; `DbStarter.updateStreamPointers` 208, `createMemoryPointers` 247;
    `Eviction.unswizzleValue` 334.
  * The growth (`ensureCapacity`, `growCapacity` 903 to 944) moves the
    pointees to the new block: no count changes.
* **Top node pointers** (`tnode.c`): `tn_new` (the constructor 66: the
  root's handle, `hd_of`); `tn_set_pointee`, `tn_swizzle`, `tn_set_pointer`
  (319 to 357; callers `TopDs.newSuperRoot` 71, `DbStarter` 105, 208,
  247, `NodeCollection` 505, 507, 671, 738).
* **`TopDs`** (`topds.c`): `tds_new_super_root` (`newSuperRoot`: the new
  top node's skip pointers inherit the super root's handles, 108, or get
  `hd_of(superRoot)`, 115; the root pointer of a super root of the same
  time is replaced, 71), and `TopDs.superRoot` itself (`tds_init`,
  `newSuperRoot` 122).
* **Handles** (`handle.c`): `hd_of` (98, 103), `hd_set_obj` (`Cache3`'s
  `register` 255, `install` 277, `makeCanonical` 305), `hd_kill`
  (`kill` 349, from `evict` 326, `clockStep` 380 and 397, `dropIfEmpty`
  417).
* **The frees** (`obj_collect`): what the freed object held.

The places of the other tasks' fields, from the survey, for their tasks:
the node table (`Cache3.liveOrNewHandle` 147, `register` 249, `evict`
328, `clockStep` 383 and 399, `dropIfEmpty` 418); D (`TransSeq.add` 58
to 66, `take` 191 to 210, `TransInfo.addGotDirtyNode` 326 from
`Db.makeDirtyIfNeeded` 1212, `DbHelper.handleStillDirtyNodes` 219 and
`DbStarter.rerunTransaction` 456, `Db.endOfTrans` 1189); the record
(`TransNodes.addTopNode` 66, `addKeyNode` 82, `addValueNode` 102,
`clear` 159 to 201); `Db.newestWrittenTop` (`Db.store` 2142,
`setNewestWrittenTop` 2426 from `DbStarter` 116 and 289);
`GetMany.Chain.addLink` 133, 142 and `removeLink` 166;
`Eviction.largeValues` (661, 674, 693).

### 6.4.4 The safe points

* **The end of every call** of the API: the read calls (012-08), execute
  (012-09; after its record and reclaim's steps), open (012-10), and
  after eviction, which runs at the end of a call (012-12), so that what
  it lets go is freed at once.
* **Inside long calls**, where their tasks name them: between the puts of
  a large transaction (after an operation's `endOfOp`, when `opMarks` is
  empty, every new node is in the table and every new value in the
  record), between the leaves of a `getMany` (its cursor counts what it
  holds), between the records a startup reads.
* **In this task's tests**: after each change, a recount; at chosen
  points, `obj_collect`; at the end, `obj_free_all` and the allocator's
  count 0 (`CHECK_MEM_ZERO`).

## 6.5 What C does otherwise than Java, and why no byte changes

* **No monitors, volatiles or the LOADING state**: one caller (012-01,
  4.2). Java's coherent pairs (`getPointer`, `getSerializedRef` under the
  node's monitor) are plain reads.
* **The slots past `size`**: Java's `toPreviousState` lowers the size and
  leaves the slots' pointees (only concurrent readers may read them; the
  writer overwrites them later without looking). C releases and clears
  them, so that a slot holds something exactly when it is below `size`.
  No one reads them in C.
* **The back reference** is cleared when its handle lets go of the object
  (6.3).
* **Access data**: since 009, step 3a, only `AccessData` constants are
  left in the dag (`DEFAULT_ACCESS_DATA`, `ZERO`); a pointer's `pos` is
  always its reference. Ported as constants.
* **Errors**: Java's `assert` is C's `assert` (on in both builds); a
  failed allocation is `false` or NULL (NOMEM, 012-01, 4.5, point 7);
  the check functions (`check`, `validateStreamNode`) return a message,
  NULL when the node is right, where Java throws `AssertionError` or
  `KeyNode.Invalid`.
* **Debug text** (`print`, `toString`, `getInfo`, `printGraph`): a
  small `kn_print` for tests; the dumps are 012-05's and 012-08's.

## 6.6 The modules

| Module | Java | Prefix |
|---|---|---|
| `obj` | the counts, the pending list, safe points, the recount, close's walk (012-01, 4.5) | `obj_` |
| `node` | `Node` (the accessors common to the three kinds), `Pointer`, `KlongWithPointer`, `AccessData`'s constants | `node_`, `ptr_`, `kwp_` |
| `handle` | `Handle`, and `Cache3`'s changes of a handle | `hd_` |
| `knode` | `KeyNode`, and `StoredKeyNode.parse`'s making of the object | `kn_` |
| `tnode` | `TopNode`, and `StoredTopNode.parse`'s | `tn_` |
| `vnode` | `ValueNode`, and `StoredValueNode.parse`'s | `vn_` |
| `topds` | `TopDs` | `tds_` |
| `opdata` | `OpData` and the Dag's interfaces that the nodes and `TopDs` call: `PointerFollower`, `Dag.PointerListener`, `PointerCreatedListener`, `NodeChangeListener`, `CachePolicy`, with their do-nothing versions; a callback that can fail (NOMEM, a read) returns `false`, where Java's would throw | `op_` |
| `nwrite` | the writers: `StoredKeyNode.toLongs`, `StoredTopNode.toLongs`, `StoredValueNode.toBytes`, their `getByteSize` | `nw_` |
| `klong` | `Klong` (012-04's, extended) | `kl_` |

The objects are made from 012-06's parsed nodes (`snode`) by the
constructors of `knode`, `tnode` and `vnode`, which take the fields and
arrays as `snode` gives them, so that these modules do not depend on
`snode` until 06 is in main.

## 6.7 How the next tasks use them

Written after the ports (17:15), for 012-08 to 012-12:

* **One `struct obj_ctx` per database** (`obj_ctx_init` with the
  database's `struct mem`). Every object is made pending; a field that
  keeps an object past a safe point holds it with `obj_retain` and lets it
  go with `obj_release` (or `obj_set` for both); `obj_collect` is the safe
  point, called where 6.4.4 says, the end of every call at least. A local
  is safe until the next `obj_collect`.
* **NOMEM**: every function that allocates returns `false` or NULL, with
  the counts kept; after the go point the caller fails the database
  (P7) and goes on to close, whose `obj_free_all` takes the database's
  roots (the node table's handles, D, the record, the super root, the
  newest written top node) and the pending list.
* **The Dag's listeners** (`opdata.h`) return `bool`: Db's implementations
  allocate (the table, the marks), so the Dag stops on `false`, as Java
  would on an exception. `TopDs` already does.
* **The node table** (012-12; a first one by whoever needs it):
  `Cache3.register` is `hd_new` (or the object's `hd_of` handle when it
  has one, as Java adopts it) plus `hd_set_obj`, the table's own count an
  `obj_retain` of the handle; `install` and `makeCanonical` are
  `hd_set_obj`; `evict` is `hd_kill`, the removal from the table, and the
  release of the table's count. Db's `registerNewNode` sets the object
  canonical, as Java's.
* **Values**: `vn_new` copies the bytes; a value node does not hold its
  key, the record (`TransNodes`) does, and `nw_value_to_bytes` takes it.
  A delete node is held by the record only (6.3.1 of 012-02).
* **`struct kwp` and `struct pointer`** hold borrowed nodes: valid until the
  next safe point; `GetMany`'s chain must retain what it keeps across
  leaves (6.4.2).
* **The writers** take a record's long buffer and its byte buffer as
  Java's serializer does; the serializer (012-09) sets the positions and
  `prevPos` first (`prepareToSerialize`), as `t_nwrite.c` does for the
  creation's record.


# 7. Progress

**Java's reference:** `main` at `1a45f31`, `java/` as of `decc677`.
**Clone:** `/Users/f/fl/bench/012/07-index-nodes/` (a clone of `bergdb` at
`1a45f31`).

* 2026-10-28 16:19: started. Read 012-01, this plan, the C project, 012-02
  (sections 5 to 8), 012-06's `snode` and `strans` (its clone), and Java's
  `dag` classes and the three `Stored*Node`s. A survey of every Java field
  that holds a node, a value or a handle, and every place that changes it,
  by a helper agent (section 6.4.2 and 6.4.3 are made from it).
* 16:45: the design, section 6, written and committed.
* 16:54: the modules of 6.6 ported (`obj`, `node`, `handle`, `knode`,
  `vnode`, `tnode`, `opdata`, `topds`, `nwrite`; `klong`'s `DELETE_BITS`
  public as `kl_delete_bit`), and `KeyNodeTester` (45 of its 46 tests;
  `testPrint` left out with `print`).
* 17:02: the tests (162 unit tests in all, 81 of them this task's):
  * `t_obj.c`: the counts, safe points, the recount (finds a count too
    high or too low), close's walk (with wrong counts), the handle's
    states, `hd_kill`'s written position and the record rule, `swizzle`,
    `toPreviousState`'s and `setContentFrom`'s releases, and the
    allocation failures in turn over a workload of every allocating node
    function (each run NOMEM or done, the recount right, nothing left);
  * `t_tnode.c`: `TopNode`'s two tests, `TopTester`'s six, and
    `StoredTopNode`'s that C has (the stream pointer times, the ordinals'
    round trip up to 2^48 − 2, the ordinal field, `toLongs` 1 and 2);
    the parser's refusals are 012-06's;
  * `t_nwrite.c`: the writers against Java's bytes, the creation's top
    node and root key node of 012-02, 8.2, byte for byte with their
    checksums; `StoredKeyNode.testSerialize`, `StoredValueNode`'s tests
    but the parser's refusal, `ValueNode.testDummy`;
  * `t_kmodel.c`: a key node against a model, 300 seeds: puts and
    deletes of ten keys at increasing times, then every search at every
    time, the last version, a split of it, `toPreviousState`; 6.2 million
    checks, 0.7 s with the sanitizers.
  * The gate: C BEFORE COMMIT OK (38 s), with the quick cross set.
* 17:05: **Java's `KeyNode` against C's**: `knode.txt`, 12 runs of 480
  operations as the Dag makes them, written by Java (a generator in the
  scratchpad, `bergdb.core` with `Vectors`' header; it goes into
  `Vectors.java` once 012-06's change of that file is in main, so that
  the two do not conflict), with the size and the hash of the node's
  stored bytes after each operation: C replays them, all equal
  (`t_knodevec.c`).
* 17:07: **Java's `TopDs` against C's**: `top.txt`, 8 chains of 196 new
  super roots as the Dag makes them (the same-time case, a second
  ordinal, the ids given by the listener as Db gives them, the super root
  written now and then) with the stored bytes' hash after each, and 68
  `findRoot`s: all equal (`t_topvec.c`).
* 17:09: 012-06 in main (`dd5c10f`), merged into the clone (`a1ccf2b`;
  `test/unit/main.c` kept both sides' tables).
* 17:10: **done item 5's round trip** (`t_roundtrip.c`): each node of a
  record parsed by 012-06's `st_parse` (`struct sn_node`), made into an
  object as Java's parse makes it (`kn_new_stored`, `tn_new_stored`,
  `vn_new_stored`) and written again (`nwrite`), gives its bytes. In the
  unit tests over 012-06's `records.txt`; over directories when
  `BERGDB_STREAMS` names a file that lists them. 012-05's quick set, kept
  (`cross.sh quick KEEP=1`): 273 directories (crash variants and turns
  included; the 56 cut streams' walks end at the cut, with Java's read
  past the end), 53,417 records, 35,191 top, 364,438 key, 118,834 value
  and 6,776 delete nodes, every one its bytes again.
* 17:12: the generators of `knode.txt` and `top.txt` in `Vectors.java`;
  run again, it writes all eight vector files as committed.
* 17:14: the recount after every change in the model test and Java's
  `KeyNode` runs; `TopDs`'s chains in the allocation-failure runs.
* 17:27: `cross.sh full KEEP=1` (both sides Java, to keep 012-05's
  streams): CROSS full OK, 278 workloads, 1262 crash cuts, 498 corrupt
  variants, 6 in turns (934 s).
* 17:29: **the round trip over the full set**: 6,016 directories (1,142
  of them cut crash variants, whose walks end at the cut), 5,056,194
  records, 2,794,740 top, 39,398,768 key, 12,049,935 value and 1,086,821
  delete nodes, every one its bytes again (the release build, asserts
  on; 96 s). The quick set's 273 directories ran in the test build too
  (the sanitizers). The kept directories (48 GB) deleted after.
* 17:31: C BEFORE COMMIT OK (38 s): 185 unit tests, 6,289,009 checks;
  the quick cross set with C's scanner as side B.
* F1 is registered already: 005-75 (by 012-02's review, `ab2dca4`).

**Done when**, as it holds at the end (17:30):

1. `Klong` complete: 012-04's port, with `DELETE_BITS` as `kl_delete_bit`;
   `toString` and `getKeyString` left out (debug text).
2. Key nodes: every method of `KeyNode` ported (`knode.c`), the checks
   returning messages; against Java operation by operation (`knode.txt`,
   480 operations, the stored bytes' hash after each), against a model
   (300 seeds), and Java's `KeyNodeTester` (45 of 46; `testPrint` left
   out with `print`).
3. Value nodes, top nodes and `TopDs` (`vnode.c`, `tnode.c`, `topds.c`):
   ordinals to 2^48 − 1, root times, skip pointers, `findRoot`, new super
   roots with the same-time case; against Java (`top.txt`, 196 new super
   roots, 68 `findRoot`s), `TopTester`, `TopNode`'s tests.
4. Pointers: what a pointer holds (NULL, a handle, a value) and its
   reference; `Handle` with LIVE and DEAD, `written_pos` and the record
   rule (`handle.c`), which eviction (012-12) uses as Java's does.
5. Writers (`nwrite.c`): the creation's bytes of 012-02, 8.2, and the
   round trip of every node of 012-05's quick and full sets.
6. The ported tests pass, under the sanitizers and in the release build
   without leaks; the memory checks of section 4: the recount after every
   change, the allocation failures in turn, the allocator's count 0 at
   every test's end.

Not done, for the conductor: `c/readme.md`'s table of modules (012-04's
file, not in this task's list) lacks this task's nine modules (section
6.6 has them).

**Findings** (for the conductor, who registers them in 005):

* **F1. `KeyNode.checkIncreasingTime` checks nothing** (section 5, note
  1). Probe, against `java/` at `decc677` (compiled by
  `test/cross/java-build.sh`; run with `-ea`):

  ```java
  KeyNode node = new KeyNode();
  node.addToEnd(Klong.createTime(20), null, Spos.NULL);
  node.addToEnd(Klong.createKey(new byte[] {97}), null, 100);
  node.addToEnd(Klong.createTime(10), null, Spos.NULL);   // earlier than 20
  node.addToEnd(Klong.createKey(new byte[] {98}), null, 200);
  node.checkWithMessage();          // null: check() passes
  node.validateStreamNode(1000);    // no KeyNode.Invalid
  ```

  Both pass (run on 2026-10-28, 17:00). The fix would set
  `time = klongTime` in the loop; `validateStreamNode` would then refuse
  such a node at a start, as its name says.
