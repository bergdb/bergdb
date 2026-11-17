# 023-01. Introduction

Created 2026-11-10 by Frans Lundberg. Status: open.

What an agent, or a person, needs to know before working on any part of
023: what triggered the work, and how the Core works today where deleted
keys and old versions are concerned. It describes what is, not what should
be; the problem is stated in 023-02.

Code places are `Class.method` and file:line on `main` at `795c2155`, whose
Java code is the release candidate's, `d00096e`; the files are in
`java/src/bergdb/dag/`, `core/` and `pubimp/`.


## 1. What triggered the work

### 1.1 The findings

Round 6 of the new-user applications ran on the candidate (020-24-16 to
18). Two found slow scans over deleted entries and one found reclaim
stopped by deletes, as 021-25 had found earlier that day from a C user's
log. No read was wrong in any of them. For the FIFO, 2026.3 writes the
same stream, byte for byte: not a regression (021-25, "Findings").

* **020-24-16, U16-1, a job queue.** Reading the first 16 entries of the
  index scan `eq("PENDING")` slows with every job that ever left PENDING:
  0.14 ms fresh, 24.4 ms after 190,000 left, 27.2 ms after a restart. The
  primary scan of a directory: 0.04 ms, then 2.0 ms after 190,000 deletes.
  Key nodes followed: 27, then 204,226, 1.07 per deleted entry (021-28,
  "Cause"). Reclaim does not help; the same index built again over the same
  data takes 0.049 ms.
* **020-24-17, U17-1, a graph store.** An empty scan at the end of index
  "in", after K creations and deletions of an index "ix2" of the same
  directory, whose entries sort right after: 0.05 ms, then 30.9 ms after 160
  cycles. Key nodes followed: 10, then 139,233, 0.087 per deleted entry.
  With the churned index named "aa", which sorts before, no slowdown. In the
  application, transactions took up to 3.1 s, as their scans were slow.
* **020-24-18, U18-1, a metrics store.** 50 sensors, a sample a second,
  each deleted after 15 minutes, retain duration 20 minutes, keys in time
  order. Reclaim cut once, at 0.91 simulated hours, and never again. At 12
  hours the directory was 1,188 MB for 1.8 MB of live data; one tick grew
  it by 148.6 MB, and ticks took up to 4.2 s. A ring of keys overwritten in
  place, with no deletes, stayed bounded (150 MB, a cut every half hour).
* **021-25, a FIFO.** 1,024 live keys in time order, one put and one delete
  a transaction, retain duration 20 s, 300,000 transactions. 15 cuts, the
  last between transactions 190,000 and 195,000; then the first available
  lookup time fell behind, and the directory reached 135 MB for 300 KB of
  live data, with user records of up to 4.17 MB. The first step of the 17th
  iteration scanned 20,642 index nodes to find 4 KVs and made 17,493 dirty.

### 1.2 What was found and done before this item

021-25's cause has three parts: (1) the index keeps the nodes of deleted
keys, about one node per 10 deleted keys in the FIFO, and reclaim's touch
makes them dirty in every iteration; (2) the touch runs on to the next live
key, past every key deleted since the iteration began; (3) every
transaction cleared the whole key access path, whose array grew with the
largest touch. Fix (c), for part 3, is in the candidate (`e8cbf9d`). Fix
(a), ending the touch at its range, is a prototype on branch `021-25-fix-a`:
the FIFO kept cutting (80 MB against 134 MB), but each iteration's first
step still touched every deleted key's node, with records of up to 7.27 MB,
and u18's store made 4 cuts in 5 hours (021-25, Log).

021-28 is a read-path prototype on branch `scan-deleted-keys` (in
`/Users/f/fl/bench/2026-11-09/clone-q34`; the item's file is on that
branch, not on `main`): `GetMany.endKey` ends a forward scan when the key
nodes it follows pass the range's end, live or deleted, and the Pub API's
index scan and directory listing set it. u17's empty scan then follows 10
key nodes at every K. u16's case is unchanged: its deleted entries lie at
the head of the range, before its first live entry.

020-30 (sections 3, 4.1 and 4.2) wrote down how it works today and gave a
first overview of options. This item uses its facts, not its options.

### 1.3 Frans's rule and decision

Frans, 2026-11-10, 08:29: "Scans are supposed to be O(n) amortized for
scanning n items." 08:50, the rule: "a deleted KV must consume zero
resources eventually after the retain period has passed." 09:03: release
2026.4 is paused until this is sorted out. 09:37: look at resource cleanup
in general, "Things affect each other here." (023's readme; 020-30,
section 1.)


## 2. Terms

### 2.1 Data and index

| Term          | Meaning                                                                   |
|---|---|
| KV            | A key and its value, both byte arrays; a delete removes the key's value   |
| segment       | Up to 7 bytes of a key, as a compare value with its length, 0 to 7        |
| klong         | A long in a key node's array: a TIME, KEY or DELETE_BITMAP klong          |
| key node      | An index node: up to 30 klongs, each KEY klong with a pointer             |
| segment leaf  | A key node in which a segment is found by equality                        |
| inner node    | A key node that is not a segment leaf; its KEY klongs are lower bounds    |
| segment tree  | The key nodes that look up one segment of a key                           |
| space root    | The root of segment 0's tree, named by a top node's root pointer          |
| value node    | A value, immutable, written in its transaction's record                   |
| delete node   | A value node without a value: a delete, in its record only                |
| top node      | A node of the skip list by time that finds the space root (TopDs)         |
| super root    | The newest top node                                                       |
| live klong    | A KEY klong at time t: neither deleted nor shadowed at t                  |
| shadowed      | A KEY klong with a later klong of the same compare value in its node      |
| current       | Reachable from the space root at the latest time                          |
| empty node    | A key node with no live KEY klong at the latest time                      |
| version       | A node as written once to the stream, its history up to then              |
| record        | What one transaction appends to the stream (StoredTrans)                  |
| lookup time   | The time a read reads at; actual: at most the last commit's time          |

### 2.2 Memory, startup and reclaim

| Term              | Meaning                                                               |
|---|---|
| canonical object  | A node's one object that holds its whole history; the writer's        |
| D                 | The dirty index nodes, pinned in memory until written                 |
| pointer i of x    | Klong i's pointer in x: a reference (position or vpos) and a pointee  |
| memory pointer    | A pointer whose handle holds an object that serves it                 |
| stream pointer    | A pointer resolved by the node's id and read from the stream          |
| handle            | Holds a node's one object, or none; the live one is in the node table |
| startup section   | The records from the last record's startup pos to the end             |
| startup distance  | The startup section's target size; 50 MB by default                   |
| retain duration R | Reads work for every time in [now - R, now]; forever by default       |
| first available f | The first available lookup time; reads before it are refused          |
| iteration         | One pass of reclaim over the live keys, in steps                      |
| touch             | A step's walk at the current time that makes index nodes dirty        |
| cut               | Removal of the stream's front, before pCut                            |


## 3. Keys, values, the stream and time

### 3.1 Keys

The Core is a key-value store: keys and values are byte arrays (010-01,
P12; Db's Javadoc, "Keys and values"). Keys are in the unsigned order of
their bytes. A key is cut into segments of 7 bytes (`Keys.toSegments`,
Keys.java:240): a key of n bytes has n/7 + 1 segments (integer division),
each of 7 bytes but the last, which has 0 to 6. A key of 7 or 14 bytes ends
with an empty segment. A segment is a compare value: its bytes, then its
length (Klong.java, format comment, lines 20 to 46).

```
key "customer:00042", 14 bytes
segment 0   "custome"   length 7
segment 1   "r:00042"   length 7
segment 2   ""          length 0    (the key's last segment)
```

### 3.2 Transactions and records

A transaction (`Trans`) holds one operation a key, in key order: a put or a
delete (`Trans.Builder.build`, Trans.java:480). `Db.executeInner`
(Db.java:2442) checks everything that may refuse it before its go point
(2493), then changes the Dag (`putKvs`, 2496), makes its time a lookup time,
and appends one record (`store`, 2513). Transactions run one at a time under
the write lock; reads run in parallel, at earlier times.

The stream is append-only: bytes are appended, never changed, and only
reclaim's cut removes its front. A record (`StoredTrans`, `RECORD_FORMAT`
5, StoredTrans.java:53) holds a header (the time, the startup pos, the
position of the newest top node), the transaction's value nodes, a delete
node for each delete, the index nodes that the take writes now (section
7.2), and the got-dirty list (ids and positions). A delete of a key that has
no value is a noop: nothing is created or stored (Dag.java:762-766).

### 3.3 Time and lookups at earlier times

Each transaction has a time, strictly increasing, in units of 100 ns
(`Clock.UNITS_PER_SEC`). A read gives the state at its actual lookup time:
the time asked for, or the last committed transaction's time if that is
earlier (`DbClock.lookupTime`, DbClock.java:69); `Long.MAX_VALUE` is the
latest state. A read at an earlier time sees the state then: every node
keeps its history (section 4). A read before the first available lookup
time is refused with `LookupTimeNotAvailableException` (`getOneInternal`,
Db.java:1999; `getManyInner`, 2102). With the default retain duration,
forever, every time since the creation can be read.


## 4. The index

### 4.1 Klongs

A key node is an array of klongs, appended in time order (Klong.java's
comment; `KeyNode.addKlong`, KeyNode.java:837):

* **TIME**: a 56-bit time. The klongs after it, up to the next TIME klong,
  are in the node from that time on.
* **KEY**: a segment's compare value, with a pointer: to a value node, to a
  child key node, or to the next segment's tree.
* **DELETE_BITMAP**: 62 bits, one for each index of the array: the klongs
  at the indexes whose bit is set are deleted from its time on. Each bitmap
  holds the bits of the one before it (the union, Dag.java:955).

The array is not sorted by key. A search reads it from the start up to the
first TIME klong after its lookup time, with the last bitmap up to that
time (`KeyNode.searchEq`, 403; `searchLte`, 466; `getDeleteBitmapAtTime`,
1845). Of several KEY klongs with one compare value, the latest wins. The
klongs of earlier transactions are never changed; the running transaction
may change its own, which no reader sees (its bitmap in place, Dag.java:960;
the splits of section 4.7; KeyNode's class comment).

An example, a segment leaf:

```
index   0       1        2        3       4        5       6
klong   T 100   K "a"    K "b"    T 105   K "a"    T 110   D {2}
pointer         -> v1    -> v2            -> v3
```

At time 104 the node gives a = v1, b = v2; at 107, a = v3 (klong 4 shadows
klong 1), b = v2; from 110, a = v3 and no b. Klongs 1 and 2 stay in the
node, and v1 and v2 stay in the stream.

### 4.2 Key nodes

A key node (`KeyNode`) has at most `maxNodeSize` klongs: 30 by default and
in the Pub API (`DbBuilder.maxNodeSize30`; 8, 14 and 62 for tests), stored
in each meta block, and a start with another size is refused (005-50). Its
canonical object holds its whole history since it was made. A version in
the stream is the whole array and a reference for each pointer, with the
position of the node's previous version (`StoredKeyNode.toLongs`,
StoredKeyNode.java:51): 32 bytes and 16 a klong, 512 bytes at 30 klongs.

* **Inner nodes** route: each KEY klong is the lower bound of its child,
  and a lookup takes the largest live klong at or below its segment
  (`searchLte`). The first child of a root made by a space split has the
  empty klong (`Klong.EMPTY_KEY`). Every put relies on an inner node having
  a live klong at or below any key routed to it: else `Dag.checkFound`
  (Dag.java:835) throws "corrupt data", and the database fails.
* **Segment leaves** hold the segments themselves, found by equality
  (`searchEq`). A klong of length 0 to 6 is a key's last segment and points
  to a value node; one of length 7 points to the root of the next segment's
  tree.

### 4.3 Segment trees: a key is a path

Segment 0 is looked up in the tree under the space root; segment i + 1 in
the tree that segment i's klong points to. A new segment tree starts as one
segment leaf (`Dag.setNode`, Dag.java:842).

```
super root --> space root                      tree of segment 0
                 inner nodes ...
                   segment leaf: K "custome"
                       |
                       v                       tree of segment 1
                   segment leaf: K "r:00042"
                       |
                       v                       tree of segment 2
                   segment leaf: K ""  -->  value node
```

A key costs a path of nodes per 7 bytes. The Pub API's index entries are
keys of about 32 to 52 bytes, 5 to 8 segments; when a segment near the end
differs for every entry, every entry has a segment tree of its own for its
last segment (021-28, "Cause", u16's 7th segment).

### 4.4 Value nodes and the top

A value node (`ValueNode`) holds an immutable value and is written in its
transaction's record. A leaf's pointer to it holds the value, or, after
eviction, only its position.

The top finds the space root for a lookup time. `TopDs` holds the super
root. Each top node (`TopNode`) has a root time, a root pointer, and skip
pointers to earlier top nodes. `TopDs.findSuperRootAtTime` (TopDs.java:151)
walks them to the top node that was super root at the lookup time, and
`findRoot` (136) follows its root pointer. A new space root, made by a time
split or a space split of the old one, makes a new top node
(`newSuperRoot`, 61), at most one a transaction. Top nodes are never taken
out of the skip list.

### 4.5 A put

`Dag.putKv` (Dag.java:729), at the transaction time tt, from the space root:
for each segment but the last, `setNode` (842) goes down the inner nodes by
`searchLte`, finds the segment in its leaf by `searchEq` and follows it, or
makes a new segment leaf and a klong to it. For the last segment, `setValue`
(779) goes down to its leaf and appends a KEY klong that points to a new
value node, after a TIME klong if the node has none of tt. A put of an
existing key appends a new klong: the old one stays in the node, shadowed.
A node without room goes to section 4.7. The nodes followed are kept in
`PutData.keyAccessPath`, which gives the parents for splits. Every change of
the Dag goes through `putKv`.

### 4.6 A delete

`putKv` with a null value. `setNode` makes nothing: a missing segment ends
the delete as a noop. `setValue` calls `appendDeleteKlong` (Dag.java:794,
899) on the segment leaf of the key's last segment: it sets the bit of every
KEY klong with the key's compare value, in a new DELETE_BITMAP at tt that
holds the node's earlier bits, or in the transaction's own bitmap; no such
klong, or all deleted already, is a noop. A delete node goes into the
record. A full leaf goes to section 4.7, with the deletes applied
(`lastVersionGivenDel`, Dag.java:972).

Nothing above the leaf changes. `appendDeleteKlong` is called from
`setValue` only, so no klong of an inner node, and no klong of a segment
leaf that points to a next segment tree, is ever deleted.

### 4.7 Full nodes: time splits and space splits

When a node has no room for its new klongs and a TIME klong,
`Dag.handleFullNode` (Dag.java:1058) takes its last version: a new node
with a TIME klong of tt and, for each compare value, the latest klong that
is not deleted, sorted (`KeyNode.lastVersionGivenDel`, KeyNode.java:1091).
The copied klongs now have tt as their time. Then:

* **Time split**, if the last version has at most `maxNodeSize / 2` klongs,
  its TIME klong included: the last version replaces the node
  (`Dag.timeSplit`, 1172). The parent, an inner node or for a segment root
  the segment leaf above it, gets a new klong with the node's compare value
  that points to it (time-split-1); a space root's last version gets a new
  top node (time-split-2).
* **Space split**, otherwise: the last version is cut into two new nodes
  (`KeyNode.firstAndSecond`, 1276; `Dag.spaceSplit`, 1233). The parent gets
  two klongs (space-split-1), or a segment root or the space root gets a new
  root above the two (space-split-2 and -3).

A klong added to the parent may fill it, so splits go up (`appendKlongs`,
995). The replaced node loses its klongs of tt (`toPreviousState`, 1090) and
stays as it was: the node for earlier times, through the parent's older
klong, which the new klong shadows from tt on. A node made in the same
transaction is split in place instead (`timeSplitInPlace`,
`spaceSplitInPlace`; the comment at 1049 to 1056).

So a split drops deleted and shadowed klongs from the current version of
the node it splits, and only from that one. A leaf whose keys are all
deleted gets a last version with a TIME klong only: an empty node, which
the parent links with a new live klong. `Dag.timeSplit`'s comment of
2013-10-05 says "Last version is small enough not to split into two nodes,
but not empty"; nothing checks it.

### 4.8 Nodes are never merged or removed

There is no code that merges nodes or that removes a node or a klong from
the current tree. An inner node's klongs are never deleted, and its time
splits keep the latest klong of every compare value, so the key ranges it
routes to only grow in number: the tree keeps the size it once had, after
any deletes (011-01, Q1, which asked which bound to promise; not decided).
A child whose keys are all deleted stays linked, whether a split has made
it an empty node or not, and so do the segment trees of deleted long keys.
A key put again into such a range is routed into the same node and fills it
again. Keys that never come back, as in time order, a FIFO or a deleted
index generation, leave their nodes empty for good.


## 5. Reads

### 5.1 A get

`Db.getOne` (Db.java:1828) checks the first available lookup time, takes
the actual lookup time (`getOneInternal`, 1994) and calls `Dag.getOne`
(Dag.java:347): the root at that time, then per segment
`getEqNodeInSegment` (408), `searchLte` down the inner nodes and `searchEq`
in the leaf. One path a segment tree: deleted keys cost a get only through
the trees' height.

### 5.2 A scan

`Db.getMany` (Db.java:2064) and `Dag.getMany` (Dag.java:660). A `GetMany`
has a lookup time, a start key (null: the first key, or backward the last),
inclusive or not, forward or backward, and a stop condition.

* `Chain.setup` (GetMany.java:204) goes down to the start key and keeps a
  stack of links, a node and a compare value each, one for every node level
  of every segment tree on the path, and the segments passed.
* `Chain.next` (331) searches the deepest link's node for the next KEY klong
  after the link's compare value at the lookup time (`searchGt` forward,
  `searchLt` backward; both skip deleted klongs). None: it pops the link
  and goes on in the parent (358 to 367). Else it follows the pointer
  (373): a value node is the next KV, a `Kvt` with key, value, the klong's
  time and position (375 to 383); a key node is pushed (389).
* `Dag.getMany` gives each KV to the stop condition (688), which answers
  ADD, CONTINUE, STOP or ADD_AND_STOP; at the end of the data it calls
  `eod()`. The conditions in `GetMany`: DontStop, Endpoint, GetN, GetOne,
  Prefix, PrefixN.

So a scan walks every node below every live klong it meets, and returns
only KVs live at its lookup time. The stop condition sees live KVs only: a
scan learns that it has passed its range at the first live key after it,
and nothing can stop it inside a run of deleted keys. Each KV's value node
is read, also when the condition then drops it (U16-9). A search is a pass
over the node's klongs, up to 30, and an inner node with k children visited
is searched k + 1 times. In u17's file database, with its nodes evicted, a
deleted entry cost several microseconds; in memory about 20 ns (020-24-17,
U17-1).

```
inner node   K ""      K "c"      K "f"      K "m"        every klong live
               |         |          |          |
leaves       a b       c d e      f ... l    m ...
             deleted   deleted    deleted    live
```

A forward scan from the first key follows "", finds no live klong in the
leaf, climbs back, and does the same for "c" and "f" before it returns m.


## 6. The Pub API on the Core

### 6.1 Directories and the primary scan

A Pub key such as "/a/b" is the ikey "/da/-b" (`PubKeys`: 'd' before a
directory's name, '-' before a file's), and its bkey by key-encoding.md
(each byte plus 2, '/' as 1). A directory's own keys are one key range. A
put or a delete of the Pub API is a put or a delete of the Core.

The primary scan, `Connection.usePrimary` (`UsePrimaryBuilderImp`), reads a
directory's keys in pages: each page is a new `Db.getMany` from the last key
(`Scan.readPage`, UsePrimaryBuilderImp.java:266), of at most 100 keys
(`PAGE_KEYS`, 29), whose stop condition (`Page`, 370) stops at the first
live key outside the directory's prefix.

### 6.2 User indexes

An index's definition is at `/#i/didef/-NAME`. Its entries are Core keys
with an empty value: bkey(`/#i/dient/dNAME/`), the generation G (the
creation's time, 8 bytes), the levels' encodings, then the file part of the
object's key (`IndexKeys`, class comment). A new generation is a new key
range after the old ones.

* **Maintenance** (`RwEnvironmentImp.indexEntries`,
  RwEnvironmentImp.java:458): every put or delete at an object key of an
  indexed directory reads the previous value, deletes its entry
  (`deleteIndexEntry`, 420) and puts the new value's entry, in the same
  transaction; an entry that is the same for both stays (015-40).
* **Scans** (`UseIndexBuilderImp.Scan.readPage`,
  UseIndexBuilderImp.java:404): pages of 100 entries (`PAGE`, 35), each a
  new `Db.getMany`, whose stop condition stops at the first live entry at
  or after the range's end (forward) or before its start (backward). For
  each entry the object is read with a get and checked against the entry,
  so a stale entry is skipped (`hasNextInner`, 357).
* **Deletion** (`deleteIndex`; `IndexManager.deleteInner`, 334): one
  transaction deletes the definition and puts a marker
  `/#i/didel/dNAME/-G16`. A thread (`startCleanup`, IndexManager.java:480)
  then deletes the generation's entries, at most 100 a transaction
  (`CLEANUP_KEYS`, 55), each step reading after the last key it deleted: a
  read from the prefix passed the deleted keys before it, and the cleanup
  took the square of the entries' number (020-18, F5). Last, it deletes the
  marker.

### 6.3 Where the Pub API makes deletes

Every change of an indexed field deletes an entry key and puts another. A
queue whose jobs leave PENDING leaves deleted entries at the head of its
index range (u16). A deleted index leaves every entry of its generation
deleted, in one run of keys, right after the entries of the indexes whose
names sort before it (u17). A deleted object deletes its key and its
entries. A time-ordered layout deletes at the low end of its range (u18).


## 7. Memory and the writing of index nodes

### 7.1 Dirty nodes, D

Marking (Db.java:1450 to 1550): every index node that a put or a delete
follows, creates or changes gets dirty when the operation ends, if it
changed something: its whole path from the super root down, all its segment
trees included. A delete dirties its path as a put does. A node that the
transaction replaced leaves D at its end (`endOfTrans`, 1503). D, with the
transaction in which each node got dirty, is kept in `TransSeq`.

### 7.2 Index nodes are written lazily

`Db.store` (Db.java:2741): `TransSeq.take` (TransSeq.java:164) picks whole
transactions of the startup section, oldest first, as many as the record's
share asks for, in proportion to the stream it adds, and every one that
begins twice the startup distance or more before the stream's end (the
deadline). Their got-dirty nodes are written in this record. A written node
with a dirty child stays dirty and is written again later (Rule A, the
conservative still-dirty test, `handleStillDirtyNodes`, 2819). The record
stores the new startup pos (levels.md, 5). A dirty node is so written within
about twice the startup distance of stream; a written node is clean.

### 7.3 Objects, pointers and handles

(Item 009; levels.md, 7.) A node has at most one object in memory: its
canonical object, or a version read from the stream. Pointer i of x has a
reference (`pos[i]`: a position, or a vpos before the pointee is written) and
holds nothing, its pointee's handle, or a value. The node table (`Cache3`,
4,096 maps) holds one live handle per index node that has a resident object
or that a pointer of a resident object names; the handle holds the node's
object or none. A reader follows a pointer without a lock when the handle's
object serves it (`Handle.usable`); else the slow path resolves the pointer
by the node's id and loads the version (`NodeCollection`).

### 7.4 Eviction, and what keeps a node in memory

Pinned, never evicted (`Residents.isPinned`, Residents.java:274; levels.md,
7): the super root, the canonical objects of D and of the record being
written, and the newest written top node. Every other written object can
go. When the resident bytes pass the budget (`cacheSizeInMb`; a fifth of the
heap in the Pub API, 200 MB in `DbBuilder`), a batch of CLOCK steps over the
node table takes objects whose CLOCK bit is clear (`Eviction`; `Cache3.evict`,
Cache3.java:332): the handle dies, and a pointer that holds it is resolved
again by the id. A value over 1 MiB leaves memory once written. So an
object stays while it is pinned, recently used, or the resident bytes are
under the budget. Nothing frees an object because no current node points to
it, and the nodes that a scan walks are loaded as any read's are. The Pub
API always evicts; with `DbBuilder.noEvict()` (Core only) nothing is ever
freed. A Pub database in memory keeps its whole stream in the heap
(020-24-17, U17-9).

Reclaim's scan reads through a maintenance follower, which loads versions
for the step and swizzles nothing (`NodeCollection.MaintenanceFollower`,
NodeCollection.java:303). Its touch goes through the writer's follower: every
node of its range becomes canonical and dirty, so pinned until written; a
reserve of 4 MiB splits a step that would pin more (`DEFAULT_STEP_RESERVE`,
Reclaim.java:213).


## 8. Startup

### 8.1 Correction

`Db.startInner` (Db.java:888) refuses an incomplete creation and another
node size, then recovers the stream (`RecoverableStream.recover`; 014-01):
a torn last record is completed as an aborted one, by appending; nothing is
overwritten or shortened. The startup pos comes from the last valid meta
block and the records after it.

### 8.2 The startup section and Rule R

The startup section is the records from the last record's startup pos to
the end (`readTransactions`, 1067). `DbStarter.doOrdinaryStartup`
(DbStarter.java:124): the newest version of each index node in the section,
by id (`createMaps`, 144; Rule R: a pointer to a node with a version there is
followed to it); the key node versions of the section cut back to the
startup time (221); the super root at the startup time, from the last
record's topPos (275); the rerun; and D linked to its canonical objects
(`linkD`, 535). Everything else is read when first touched (sis-model.md,
6.2 and 15).

### 8.3 The rerun and its node-id check

`rerunTransaction` (373) runs every put and delete of each record but the
section's first through `Dag.putKv` (439), at its own time. New nodes get
their ids in the order they are made, vpos counted from the record's
position (`Spos.nextVpos`), so a rerun by the same rules makes the same
nodes with the same ids. Then each id in the record's got-dirty list must be
found (`canonicalNode`, 488): else "startup error, node ... not found" (452),
a `StreamFormatException`. The Dag's rules for puts and deletes are so part
of what a record means; a start with another node size used to fail this
way (005-50).

The touch of a reclaim step is not stored and not rerun: D is rebuilt from
the stored ids, not from the rerun (`canonicalNode`'s comment, 474 to 486).
A cold start reads the nodes on the rerun's paths that have no version in
the section (levels.md, 5).


## 9. Reclaim

### 9.1 Iterations

Reclaim (`Reclaim`, class comment at lines 32 to 82; levels.md, 6) is off
until a retain duration is set (`Db.setRetainDuration`); its settings are in
the stream, at `/#i/dreclaim/-settings.txt`. It runs inside each user
transaction's call, after its record (Db.java:2538; `transactionCompleted`,
Reclaim.java:451). An iteration starts when the stream has grown by more
than twice the startup distance since the last one started and a quarter of
R has passed (460 to 469): pStart and tStart are the stream's length and the
time; pCut is the previous iteration's pStart (the first's own). One
iteration runs at a time, and only a finished one can be cut. Its state is
the table at `/#i/dreclaim/-table.txt` and the row at
`/#i/dreclaim/-current.txt`.

### 9.2 Steps

A user transaction allows a step while the bytes charged are below the
internal fraction, a quarter, of the stream's growth since pStart (472 to
476); a step covers 10 to 16 KB of KVs. A step (`step`, 540), in one internal
transaction:

1. scans the KVs live at tStart after `lastKey` (555 to 579). Its size limit
   and its reserve are checked in the stop condition, so at live KVs only;
2. reads each at the latest state, and puts it again if it is live and its
   transaction lies before pCut (622);
3. touches its key range at the current time (section 9.3);
4. stores the row with the new `lastKey`.

A `RerunException` leaves the step for a later transaction.

### 9.3 The touch

The step sets `Trans.touch`, from the last key before the step to its own
last key, or to the end (Reclaim.java:674 to 676). `Db.putKvs` runs it
before the puts (Db.java:2903 to 2913): `Db.touchRange` (2944) is a
`getMany` at tt with the writer's follower and pointer listener, which marks
every index node it follows, and all of them get dirty. Its stop condition
(2977 to 2986) sees live KVs only, so the touch ends at the first live key
after its range. It changes no node: the nodes are written as they are,
history, deleted klongs and bitmaps included, by later takes. The bytes it
dirtied are charged to the iteration (656) and delay the next step. Why it
exists: before 2026-10-13, nodes that held deleted keys only kept their old
versions, and after a cut a lookup could follow a pointer into the removed
stream (011-01, Q7; the comment at Reclaim.java:670).

### 9.4 The cut and the first available lookup time

When the scan reaches the end, the iteration is done, with tEnd and pEnd,
the time and position of its last step (713 to 726). pSafe is set when the
startup pos has passed pEnd (`markSafePositions`, 734). The cut
(`pretruncateIfPossible`, 827) takes the latest done iteration whose tEnd is
older than R, whose pSafe the startup pos has passed, and whose pCut the last
valid meta block's transaction is at or after. The table marks the cut and
is stored, rows before it are dropped, the first available lookup time
becomes tEnd, and the physical cut follows when the table is durable
(`cutIfDurable`, 498). `FileStream` cuts whole files. A read admitted before
the cut that reaches removed bytes expires with
`LookupTimeNotAvailableException`.

### 9.5 What reclaim copies and what it frees

Copied forward in every iteration: each live value whose transaction lies
before pCut, and every index node current in the touched range. Freed by
the cut, everything before pCut, which no read from tEnd on needs: the value
nodes of deleted and overwritten values, older versions of nodes written
again since, and the nodes that splits replaced, which are not current, so
no touch reaches them. The empty nodes and the segment trees of deleted
keys are current, so each iteration copies them forward, and the deleted
and shadowed klongs in every copied node go with it. The stream kept is the
retention window plus one or two iteration spans (levels.md, 6).


## 10. Where deleted keys and old versions are today

At each place, what a deleted key leaves, and for how long:

| Place                     | What stays                           | How long                     |
|---|---|---|
| stream: its value node    | the value                            | until a cut passes it        |
| stream: its record        | the delete node                      | until a cut passes it        |
| its segment leaf          | its KEY klongs and bitmap bits       | until the leaf's time split  |
| a leaf left with no key   | the node, linked by a live klong     | for ever                     |
| inner nodes, no key below | the nodes, linked by live klongs     | for ever                     |
| a long key's own segments | their segment trees, linked          | for ever                     |
| scans of its range        | a walk through those nodes           | for ever, through restarts   |
| reclaim's scan at tStart  | the same walk                        | every iteration              |
| reclaim's touch           | those nodes, dirty and written again | every iteration              |
| memory                    | D until written, then cached         | until CLOCK takes it         |
| startup                   | the delete's rerun, its path's reads | while in the startup section |

The rows on nodes are about the current tree. A leaf is split only when it
fills, by puts or by deletes (each deleting transaction adds a TIME klong
and a bitmap), so a leaf that gets no more writes keeps its deleted klongs.
"For ever" includes every iteration's copy; the versions written before a
cut go with the cut.

The code: Reclaim.java:622 (the value), Dag.java:899 and 972 (the leaf),
Dag.java:1058 and 1172 (the empty leaf), Dag.java:842 (segment trees),
GetMany.java:331 (scans), Reclaim.java:579 (the scan at tStart), Db.java:2944
(the touch), DbStarter.java:439 (the rerun).

A get passes one path, so it pays for deleted keys only through the trees'
height. A put or a delete passes its own path. With the retain duration
forever, nothing is ever cut: the value nodes and the records stay too.

Old versions of live keys and nodes:

* A put over a key leaves the old klong in its leaf, shadowed, until the
  leaf's next time split, and the old value node in the stream until a cut.
* A split leaves the replaced node with its history for earlier times; it
  is not current, so no touch copies it, and the cut frees its versions. The
  copied klongs carry the split's time from then on.
* A node rewritten after a cut can still hold klongs and references for
  times before the first available lookup time; no read follows them.
* Top nodes stay in the skip list; their versions before a cut are cut.
* The STM keeps the hashes of the last 96,000 to 128,000 key writes in
  memory, deletes included (Db's Javadoc, "Optimistic transactions").


## 11. Intent stated and not built

Facts from Frans's notes of 2012 (F1-007; 020-30-02, section 1), and from
the code's comments:

* 2012-01-27: "Merges are made when the current version of a node shrinks
  because of a delete. It may then be merged with its parent."
* 2012-02-17: "Start with split, no merge right now." 2012-03-19, a
  limitation: "no node deletion (always grows in memory)".
* 2012-06, the delete bitmaps: "The last version of the full [node] could
  be empty (no key klongs). This happens when all key klongs have been
  deleted. In this case, we want to delete the node by adding a delete klong
  to its parent." Its summary: "If lastVersion is empty, remove from
  parent." The code has no such step (section 4.7).
* 2012-07, space reclaim: reclaim rewrites the live KVs, and the stream is
  estimated at "between 2 and 4 times the dbSize", the live KVs' size.
  011-01, Q8, leaves the space bound open.
* 011-01, Q1 (2026-10): nodes are never merged; which bound BergDB promises
  for lookups is not decided.


## 12. Where the documents and the code differ

The code is right in each case:

* levels.md, 6, says that a step "touches its key range at the current
  time". The touch runs on to the first live key after the range
  (`Db.touchRange`'s stop condition, Db.java:2977), past every key deleted
  there (021-25, part 2).
* levels.md, 6, says that a step scans "at most about 16 KB of KVs". The
  size and the reserve are checked at live KVs only; the deleted keys
  between them are not counted (Reclaim.java:565 to 573; 021-25, part 1).
* Reclaim.step's comment at lines 613 and 614 says that a value "stored
  before pStart" is rewritten; the code compares its transaction's position
  with pCut (622), as the class comment and levels.md say.
* Dag.timeSplit's comment says the last version is "not empty"; a leaf
  whose keys are all deleted has an empty last version (section 4.7).


## 13. Where to read next

levels.md, 5 to 7; sis-model.md, 6 and 15; 020-30, sections 3 and 4.1 to
4.3, with 020-30-01 (reclaim), 020-30-03 (how a key maps onto nodes) and
020-30-04 (the format and the rerun); 021-25, "Cause"; 021-28, on its
branch; 020-24-16 to 18; 011-01, Q1, Q7 and Q8; item 009 for handles.
