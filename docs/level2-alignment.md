# BergDB Level 2: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-15.
Work packages B1, B2, B3 and later of the plan F1-008-11 (repository f1,
`b/008-bergdb-lean-model/11-level2-alignment-plan-claude/`). Source commit
`a116ec7`; line numbers below are at that commit.

Status, 2026-10-15: B1, B2, B3, C3 written; D0 (M18) fixed; E1 (marking)
and E2 (BergDB's still-dirty test) proven in Lean. Waiting: D1 (10's
change), E3 (the virtual root and the other model changes), F1, F2.

The goal of the plan is that the Java code and the Lean model in
[../lean/](../lean/README.md) agree at Level 2 (reclaim off): the Java
transactions meet the model's assumptions, every Java transaction does what
the model's `step` does, and restarts are invisible. This document says what
"agree" means in detail: the mapping α from the Java state to the model's
state (section 2), how each step of the model's algorithm and of startup is
done in Java (sections 3 and 4), what in Java gives each assumption (section
5), and the list of known differences, the register (section 6), with the
arguments for the rows resolved by argument (section 7).

Terms of the model: P, the structure (nodes with histories); D, the dirty
set (node id and got-dirty index); S, the stream of records R(0), R(1), ...;
x@t, a history cut at time t; lv(x), the latest version of x in S. See
[sis-model.md](sis-model.md) and the Lean files `SIS/Basic.lean` to
`SIS/Theorems.lean`.


## 1. Scope

Level 2 only, with infinite retention, the API's default: no reclaim
iterations, no touch transactions, no cuts. The model has no reclaim; the
Level 3 code paths (`Reclaim`, `Db.touchRange`, the first available time)
stay out of this mapping, and the Level 3 gate guards them.

Not in the model, as before: bytes and their encoding, torn records,
durability, concurrency (readers run beside the writer), resource bounds.


## 2. The mapping α

### 2.1 Records and time

* R(0) is the primordial record (`StoredTrans.isPrimordial`: tpos equal to
  `RecoverableStream.META_BLOCK_SIZE`). R(i), i ≥ 1, is the i-th record after
  it in stream order. Every executed transaction writes one record, also when
  it changes nothing (`Db.store`, line 1326, runs for every transaction).
* Model time i is the time of R(i): Java's transaction time tt(i). Java's
  times increase strictly (`DbClock`), so tt(i) ↦ i is a bijection. An entry
  that Java makes at tt(i) has model time i. A Java lookup at a time t
  corresponds to model time max { i : tt(i) ≤ t }.

### 2.2 Node ids

Java ids are vpos values: odd numbers made from the position where the
transaction's record will start, and a counter (`Db.setIdOfNode`, line 797;
`ExecuteData.begin`, line 1661: `nextVpos = nodeStream.getNextPos() + 1`; the
rerun uses `Spos.nextVpos(tpos)`, `DbStarter.rerunTransaction`, line 335).
α maps a Java id x to the model id x + 1: Java's primordial key node has id 0
(`Db.writePrimordialTransaction` assigns ids before any transaction has set
the counter), and id 0 is the model's root (section 8).

### 2.3 Nodes and their kinds

| Java | Model |
|---|---|
| `TopNode` | index node |
| `KeyNode` | index node |
| `ValueNode` of type `TYPE_VALUE` | data node |
| `ValueNode` of type `TYPE_DELETE` (`ValueNode.createDelete`) | not a node: part of the transaction T(i) (M13) |
| — | the root, id 0, virtual (option (a) of Q7, section 8) |

P is all nodes ever created, as in the model, where nodes are never removed.
In Java, an object of every node stays reachable in memory at Level 2: from
the top nodes through pointers (live and dead), or from D. A node that is
created and then not referenced at all is a case of M1.

### 2.4 Entries, `ptrs` and `live`

The entry values V of the BergDB instance:

* **Key node.** Its klong array, read in order, grouped by the time klongs
  (`Klong.TYPE_TIME`; the time of an entry is the time of the time klong
  before it):
  * a key klong (`TYPE_KEY`) with its pointer is an entry `key(c, y)`: compare
    value c (`Klong.getCompareValue`), child y (the id of the node the pointer
    names, in memory or in the stream);
  * a delete bitmap klong (`TYPE_DELETE_BITMAP`) is an entry `del(cs)`, with
    cs the compare values of the key klongs whose bits it sets and the
    previous bitmap of the node did not. Bitmaps are cumulative
    (`Dag.appendDeleteKlong`, line 621, writes the union with the previous
    one), and a delete sets the bits of every key klong with that compare
    value. So `del(cs)` means: every earlier `key` entry with a compare value
    in cs is deleted.
* **Top node.** `rootKey(y)` for its root pointer, to the root key node y,
  and `skip(j, z)` for each set skip pointer j, to the older top node z, all
  at the top node's `rootTime`. A top node does not change after the
  transaction that creates it (`TopDs.newSuperRoot`, line 42, changes the
  root pointer of a top node only in the transaction that created it).
* **Value node.** One entry `data(h)`, h a hash of the value bytes, at the
  time of its transaction.
* **The root.** `top(z)` for each top node z, at z's `rootTime` (section 8).

`ptrs`: `key(c, y)` ↦ [y], `rootKey(y)` ↦ [y], `skip(j, z)` ↦ [z], `top(z)`
↦ [z], `del` and `data` ↦ [].

`live(h)`, the children of a node with history h:

* key node: for each compare value c, the child of the last `key(c, _)` entry,
  unless a `del` entry after it names c. This is what `KeyNode.searchLte`
  (line 337) and its siblings compute: they skip the klongs of the bitmap in
  force (`getDeleteBitmapAtTime`, line 1654) and prefer the latest klong for
  a compare value.
* top node: the child of the last `rootKey` entry. The skip pointers are dead
  pointers in the model: Java follows them only to find older top nodes
  (`TopDs.findSuperRootAtTime`, line 137), which the root gives directly in
  the model.
* root: the child of the last `top` entry.
* value node: none.

The checker validates `live` against Java's own lookups (trace lines LIVE,
section 9).

### 2.5 Levels

Section 8: value nodes 0; key nodes by key segment and height; top nodes
above all key nodes, by top node id; the root above all.

### 2.6 Versions and references

A record's nodes (`StoredTrans.nodes`, parsed by `StoredTrans.Parser`, line
208) are, in this order, top nodes, key nodes and value nodes
(`Serializer.prepareToSerialize`, line 510, assigns every position before
anything is written). α maps each to a model version:

* node: the stored id; record: i; level and kind: as in P;
* history: from the stored klongs, as in 2.4 (`StoredKeyNode`), or the top
  node's fields (`StoredTopNode`: root pointer, skip pointers, `rootTime`), or
  the value;
* references: for each pointee y, the index of the record that holds the
  version at the stored position of y. A position is the start of a version
  in an earlier record or in R(i) itself. A vpos names a node that had not
  been written: no reference, as in the model.

The stored `prevPos` of a key node version (the position of the node's
previous version) has no counterpart in the model; startup does not need it
(Rule R by id replaced the prevPos chains, `docs/levels.md`, Level 2).

Delete markers (2.3) are not versions.

### 2.7 The other fields of a record

* **sp(i)**: the index of the record that starts at the stored startup pos
  (a tpos; `StoredTrans.startupPos`).
* **gd(i)**: the ids of `gotDirtyIdsAndSpos`, in their order (M9 for the
  order). The positions stored with the ids are Java's `pos` log of 08: not
  in the Level 2 model; startup uses them only for nodes of D that the rerun
  does not create (`DbStarter.canonicalNode`, line 431).
* **top(i)**: section 8 and M18. Java has no such field before WP D0.
* **trans(i)**: the stored value nodes with their keys, delete markers
  included (`StoredTrans.getValueNodes`).

### 2.8 D

For each `TransInfo` in `TransSeq` (the transactions whose nodes have not all
been taken), for each node x of its `gotDirtyNodes`: (x, j), with j the index
of the record at the `TransInfo`'s tpos.

### 2.9 P after a restart

After a restart, Java holds in memory the nodes of the startup section and the
nodes that the rerun reached; every other node is read when a pointer to it
is first followed (section 4), as the canonical object of its id if the writer
follows the pointer, else as a snapshot of the version read. So "α of the
restarted state" is not a set of objects one can simply read: reading every
pointer, live or dead, with the writer's follower would itself make old
versions canonical, which Java never does.

The exporter therefore checks the restarted state by what it does (C-R):
run B executes the same transactions with restarts; after each restart, D must
equal run A's, and lookups of every key at the latest time and at random
earlier times must give the values of the transaction history; at the end,
run B's stream must equal run A's byte for byte. That covers T1 for what
lookups see, and T2. M8 (lemma M) is the question whether this holds; a Lean
model of lazy reading would make it a proof (Q8).


## 3. The algorithm, step by step

The model's `step` (`SIS/Algorithm.lean`) for transaction i, and where Java
does the same. Java's transaction runs in `Db.executeInner` under
`writeLock`: `putKvs` (line 1429), then `store` (line 1326).

| Model | Java | Notes |
|---|---|---|
| 1. Change: `c := exec tr i (view P (i-1))`, `P := P.apply i c` | `Db.putKvs`: for each KV of the sorted transaction, `Dag.putKv` (line 463) at tt | A whole Java transaction must be one model change: M1. The Java Dag reads only nodes as of tt, which is i-1 for the earlier transactions; A1 also needs the rerun to make the same change: M15 |
| 2. Write the data versions of the new data nodes | Value nodes go into `TransNodes` when created (`newPutData`, `valueNodeCreated`) and are written in R(i) | Order within the record: M6 |
| 3. Got dirty: the dirty index nodes not in D (exact test), sorted by id | Marking: every index node an operation follows, creates or changes gets dirty at once (`makeDirtyIfNeeded`, line 819, from the listeners of `newPutData`, line 615) | M2 (more than the dirty nodes), M9 (order) |
| 4. Startup pos s(i), clamped to s(i-1) ≤ s(i) < i | `TransSeq.take` (line 83) in `store`: takes whole transactions from the front of `TransSeq` while their tpos ≤ stream length − startup distance, and at least two or until a node count limit | The policy also depends on T(i): M10 |
| 5. Take every node with d(x) ≤ s(i) | The nodes of the taken `TransInfo`s go into `TransNodes`; `TransNodes.clean` clears their dirty flags | The current transaction's `TransInfo` is added after the take, so s(i) < i |
| 6. Write a version of every taken node, lowest level first, references to the latest versions | `resolvePointersOfTakenNodes` (line 1360, `NodeCollection.resolvePointers`, line 292), then `NodeStream.appendNodes` (line 114): top nodes, key nodes, value nodes | References: M5; order: M6 |
| 7. Still dirty: a written node goes back to D (d = i) if the still-dirty test says so; tested lowest level first | `handleStillDirtyNodes` (line 1368): `DbHelper.handleStillDirtyNodes` (line 210) repeated until nothing changes; a written node with a dirty child in memory (`hasDirtyChild`, line 188) is put back | The conservative test: M3; memory children only: M4 |
| 8. Append R(i): trans, sp, versions, gd = step 3 then step 7, top | `NodeStream.appendNodes` writes R(i) with gd = `TransInfo.gotDirtyNodes` (step 3's, then step 7's); `transSeq.add(transInfo)` | top: M11, M18 |

A transaction that changes nothing (no KVs, or only deletes of missing keys)
still makes a record with steps 4 to 8.


## 4. Startup

The model's `startupWith` (`SIS/Startup.lean`) with Rule R, and Java's
`Db.startInner` (line 475) with `DbStarter.doOrdinaryStartup` (line 124).

| Model | Java | Notes |
|---|---|---|
| s := sp of the last record | `x.startupPos`, read from the stream's meta data and records | — |
| The section: R(s+1), ..., R(k) | `readTransactions(startupPos)`: R(s), ..., R(k); R(s) is the base record | M7 |
| D from gd(s+1), ..., gd(k), with d = the record's index | `rerunTransaction`: for each rerun record, the stored got-dirty ids, through `canonicalNode` (line 431) | Same set and the same d. A node of D that the rerun does not create is read from its newest section version, or from the stored position |
| Rule R: a pointer to a node with a version in R(s), ..., R(k) is followed to its newest version there (`newest`, `follow`; R(s) since 2026-10-16, M7) | `createMaps` (line 137) builds `newById` from R(s), ..., R(k); `updateStreamPointers` (line 185); `NodeCollection.followStreamPointer` (line 184) applies Rule R on first touch | M7, closed |
| `baseStruct`: P up to s, read at every time t ≤ s from top(k) (with a virtual root, from the root rebuilt from the root children, 8.6), each node with the history of the version read at the latest such t, cut at s | `changeKeyNodesToStateAtStartupTime` (line 214) cuts every section key node version back to the startup time; `findSuperNodeAtStartupTime` (line 266) finds the super root at the startup time; every other node is read on first touch (`followStreamPointer`: the node table's canonical object, else the newest of the version named and the section's version, cut back if from the section) | Lazy, not eager: M8. The root: M11, M18 |
| `rerun`: T(s+1), ..., T(k), each at its time | `rerunTransactions` (line 320): `Dag.putKv` of each stored value node, at its tt, with ids from the record's tpos | M15 |


## 5. The assumptions

`SIS/Assumptions.lean`: `SpecOK` (the initial structure) and `StepOK` (each
transaction). A1 holds by the type of `Spec.exec`.

| Assumption | What gives it in Java | How it is checked |
|---|---|---|
| Distinct ids, root exists, entries at time 0, data nodes without pointers, A4 and reachability in R(0) (`SpecOK`) | The primordial record: one top node and one empty key node (`DbStarter.doPrimordialStartup`) | Checker C-A on R(0) |
| `fresh`, `distinct`: new ids unused and distinct | vpos ids from the record's own position and a counter | C-A |
| `current` (A2): entries only to nodes reachable at i | Fails today when a later key of a transaction replaces a node an earlier key changed (M1) | C-A; 10's `A2A3Check` |
| `dataFixed`, `dataNoPtrs` | Value nodes never change, and have no pointers | C-A |
| `levels` (A4) | The level function of section 8 | C-A |
| `newReachable` (A3) | Fails today when a later key of a transaction replaces a node an earlier key created (M1) | C-A; 10's `A2A3Check` |
| A5, no resurrection (08's `StepOK.noRes`; not in the Level 2 model) | A node replaced by a split is never linked again | C-A; 10 found no failure |


## 6. The register

Verified against the code at `a116ec7` in B1, 2026-10-15. "Java" names
classes and methods in `java/src/bergdb/`, "model" definitions in
`lean/SIS/`. Status: open (o), resolved in a WP (WP name), closed (c).

| | Mismatch | Java | Model | Resolution | WP, status |
|---|---|---|---|---|---|
| M1 | A transaction applies its keys one at a time, all at tt. A later key can replace (split) a node that an earlier key changed or created: the changed node keeps entries no lookup sees (A2 fails), the created node is never reachable (A3 fails). Measured in F1-008-10. | `Db.putKvs`; `Dag.handleFullNode` (771), `timeSplit` (789), `spaceSplit` (850); `TopDs.newSuperRoot` | `StepOK.current`, `newReachable` | Code: 10's change | D1 done 2026-10-16 (in-place splits of nodes the transaction created; a replaced node loses the transaction's klongs; 10.4), c |
| M2 | Step 3 marks every index node an operation follows, creates or changes: also nodes the same transaction later replaces, and the path of a delete of a missing key, which changes nothing. | `Db.newPutData` listeners; `makeDirtyIfNeeded` | `gotDirtyOf` | Code (10's change 3), and model: marking as a step 3 option, T13 | Model: E1 done (`Algo.mark`, T13); code: D1 done 2026-10-16 (marks at the end of an operation that changed something; replaced nodes leave D; 10.4), c |
| M3 | Step 7 is the conservative test over all pointers, repeated to a fixpoint; T1 and T2 are proved for the exact test only. | `Db.handleStillDirtyNodes`; `DbHelper.hasDirtyChild` | `Algo.stillDirty`, `exactTest` | Model: T1, T2 for Java's test | E2 done (`javaTest`, `Proof/Still.lean`; no T15 needed in the Level 2 model), c |
| M4 | Java's step 7 sees only children in memory (`getPointerNode`). It relies on every pointer of a written node to a node of D being a memory pointer then. | `DbHelper.hasDirtyChild`; `NodeCollection.resolvePointers` | 08's `ruleA`: all pointees | Argument (7.1) and an assertion in the exporter | Checked: no failure of the assertion in run B (C3, D0), c |
| M5 | References: Java writes for each pointer the position of the newest version it knows (memory pointer: the object's spos; stream pointer: Rule R and the node table); the model writes lv(y), for live and dead pointers alike. | `NodeCollection.resolvePointers`; `Pointer.getSposForStream` (81); `StoredKeyNode`, `StoredTopNode` | `mkVersion` | Argument (7.2), and C-S compares every reference | Checked: every reference agrees (C3), c |
| M6 | Record order: top nodes, key nodes, value nodes, every position assigned first; the model writes data versions, then index nodes lowest level first, each naming only earlier versions of the record. | `Serializer.prepareToSerialize`, `serializeNodes` | `writeAll`, `byLevel`, `Stream.building` | Argument (7.3); C-S compares versions as a set | Argued and checked (C3), c |
| M7 | Rule R takes the newest version in R(s), ..., R(k); the model in R(s+1), ..., R(k). | `DbStarter.createMaps`; `followStreamPointer` | `Startup.newest` | Model change with proof (Q6) | E3 done 2026-10-16 (`newest` from R(s); L-SEC with ≤), c |
| M8 | First touch after a restart: lazy; the newest of the named version and the section version (cut back to the startup time), or the node table's canonical object. The model reads all of P up to s at startup. Lemma M of `levels.md`. | `NodeCollection.followStreamPointer`; `DbStarter.canonicalNode` | `baseStruct`, `readFrom` | Argument (7.4) and C-R (Q8) | Argued (7.4); C-R restarts, lookups and streams agree (C3, D0); a Lean model of lazy reading is optional, o |
| M9 | gd order: Java has step 3's nodes in marking order, then step 7's in loop order; the model sorts step 3's by id, then step 7's lowest level first. | `TransInfo.gotDirtyNodes` | `gotDirtyOf`, `step` | Argument (7.3); C-S compares sets (Q9) | Argued and checked (C3), c |
| M10 | The startup pos policy uses T(i) (`valueCount`, `kvSize` set the node count limit) and byte lengths. | `Db.store`; `TransSeq.take` | `Algo.policy : Stream → Dirty → Time → Nat` | Model: the policy also gets T(i); bytes are a function of the concrete stream (7.5) | E3 done 2026-10-16 (`Algo.policy` gets T(i)), c |
| M11 | The root: the model's root 0 is an ordinary node, written and named by top(i); Java has a chain of top nodes and no node 0. | `TopDs`, `TopNode`; `DbStarter.findLatestSuperRoot`, `findSuperNodeAtStartupTime`, `doPrimordialStartup` | `root`, `reachList`, `Record.top`, `readAt`, `init` | Q7 = (a), a virtual root (section 8) | Designed (B2); model: E3 done 2026-10-16 (`Spec.virt`, 8.6); the checker runs the model's definitions; to close with F1 on the D1 code, o |
| M12 | Levels (A4): Java has none; keys longer than 7 bytes chain key trees through segments. | `Keys.toSegments`; `KeyNode.isSegmentLeaf` | `Node.level`, `StepOK.levels` | The level function of section 8; C-A checks A4 | Designed (B2); checked: no A4 failure (C3), c |
| M13 | A delete makes a value node of type delete. It is written in the record, for the rerun, but is never in the tree. | `Dag.setValue` (513); `ValueNode.createDelete` | A3 for data nodes | α: part of T(i), not a node (2.3) | B1, c |
| M14 | Node ids are vpos values from the record's position and a counter; the model makes ids from i and a counter, and its root is 0. | `Db.setIdOfNode`; `DbStarter.rerunTransaction` | `Spec.exec` | α: ids kept, 0 for the root (2.2); argument (7.6) | B1, c |
| M15 | The first run of a transaction applies key and value transformations and goes through no-op deletes; the rerun replays the stored value nodes. The model has one `exec` for both. | `Db.putKvs`; `DbStarter.rerunTransaction` | `Spec.exec`, `rerun` | Argument (7.6); `RestartInvariance` checks it | B1, c |
| M16 | Java's times are timestamps; the model's are record indices. | `StoredTrans.tt` | `Time` | α (2.1) | B1, c |
| M17 | Reclaim's touch marks nodes without adding entries. | `Db.touchRange` | — | Level 3, not this plan | —, out of scope |
| M18 | **A startup bug.** Startup finds the super root by scanning the startup section for the newest top node. A transaction that changes nothing does not mark the super root, so the startup pos can move past the last version of every top node, and the database cannot start ("Could not find super node in startup section"). Reproduced on `a116ec7` (F1-008-11, `probe/`). With 10's change, deletes of missing keys do the same. | `DbStarter.findLatestSuperRoot`, `findSuperNodeAtStartupTime`; `TransSeq.take` | `Record.top`, `readAt` | Code: every record names the position of the latest version of the newest written top node, the model's top(i) (section 8) | D0 done (format 5, topPos), c |
| M19 | `TransSeq.take` can move the startup pos with transactions that have no got-dirty nodes; the model's policy is clamped only by s(i-1) ≤ s(i) < i, which Java meets. Recorded to make M18's cause explicit; not a mismatch. | `TransSeq.take` | `startupPos` | None | B1, c |

Findings while writing B1, beyond the plan's initial list: M19 (a note), and
two details of α: delete bitmaps are cumulative and delete every klong of a
compare value (2.4); a top node never changes after its transaction (2.4).


## 7. Arguments

### 7.1 M4: Rule A sees every child in D

Java's `hasDirtyChild` looks only at pointers whose object is in memory. Every
node of D is a canonical object in memory (D holds objects, `TransInfo`), and
`resolvePointersOfTakenNodes` runs before the still-dirty test: for each
pointer of a taken node to an index node, `resolvePointers` replaces a stream
pointer by a memory pointer to the canonical object when the node table has
one (`usable` when `best.isCanonical()`, line 330 and on). A node of D has a
canonical object in the node table (it was registered when created or read
by the writer). So every pointer of a written node to a node of D is a memory
pointer when the test runs, and `hasDirtyChild` sees it. The exporter asserts
this for every written node (C1).

### 7.2 M5: Java's references are the latest versions

The model's reference for pointee y is lv(y) in the stream so far, including
the versions already in the record being written. Java writes, for a memory
pointer, the pointee's current spos (`Pointer.getSposForStream`), which
`prepareToSerialize` has already set to its position in R(i) when y is
written in R(i); and for a stream pointer, after `resolvePointers`, the
newest of the named position and y's newest position in the startup section,
or a memory pointer to y's canonical object (whose spos is lv(y)).

Why that is lv(y): during a run without restarts every node object stays in
memory and every pointer to an index node is a memory pointer to its one
object, whose spos is its latest written position, or a vpos if it has
never been written (no reference in the model either). Value nodes are
written in the record of their transaction and never change. After a
restart, a stream pointer names some version of y; if y was written after
that version, y's newer versions are either in the section (Rule R takes the
newest) or y was written before the section, in which case y's canonical
object, if any, carries lv(y). The remaining case is a stream pointer whose
target is not in memory, with a newer version of y before the section; then
the node holding the pointer was written before y's newer version, and its
version's reference to y is stale. Whether this can happen for a node that
is written again is exactly what C-S checks for every reference; the
argument above covers the run without restarts. To be completed with the
red list (C3).

### 7.3 M6, M9: order within a record

The model's references name records, not positions, and a node is written at
most once per record (Java: `TransNodes` holds each node once,
`isInTransNodes`). Java assigns every position of R(i) before writing any
node, so a reference to a node written in R(i) names R(i) whatever the order.
The model writes lowest level first and lets a version name only earlier
versions of the record; with A4 every pointee of a node is on a lower level,
so every pointee written in R(i) is written before the node, and its
reference also names R(i). So both orders give the same references.

The order of gd(i) and of the versions in R(i) is used by nothing in the model
except record equality in T2; startup reads gd(i) as a set of (x, i) pairs and
looks versions up by node. Java's orders are deterministic functions of the
transaction and the state (marking order along the access paths, the order of
`TransNodes`), which a restart reproduces (`RestartInvariance` checks the
bytes). So comparing gd(i) and the versions as sets, as the checker does,
loses nothing for T1 and T2.

### 7.4 M8: first touch (sketch)

The model reads at startup, for every time t ≤ s, every node reachable at t,
from the version that its parent's reference names, or the newest version in
the section (Rule R), and gives the node the history of the version read at
the latest such t, cut at s. T1 says this is P up to s.

Java reads a node when a pointer to it is first followed: the canonical
object if the node table has one; otherwise the newer of the version the
pointer names and the newest section version; a section version is cut back
to the startup time. A node's versions have growing histories (every version
holds the whole history so far, and entries are only appended), so any
version written at or after the node's last entry before s, cut at s, gives
the node's history up to s. The newest of the candidates is at least as new
as the version the model reads at the latest time; lemma M is the claim that
it is new enough. C-R compares the restarted P with the P before the restart
for every probe; the Lean model of lazy reading is optional (Q8).

### 7.5 M10: the policy

`TransSeq.take` decides from the transactions in `TransSeq` (D with their
tpos), the stream length, the startup distance and the current transaction's
value count and KV bytes. The stream length is a function of the concrete
records, which a restart reproduces; the model's `policy` sees S, D and i but
not T(i). The model change: give the policy T(i) as well. Its proofs use the
policy only through s(i-1) ≤ s(i) < i and through restarts reproducing the
same inputs.

### 7.6 M14, M15: ids and the rerun

The model asks that `exec` makes new ids from i and a counter, and that the
rerun of T(i) makes the same change as the first run. Java's ids come from
the record's position (a function of the stream before R(i)) and a counter in
the order the Dag creates nodes; the rerun starts its counter at the same
position (`Spos.nextVpos(tpos)`) and creates the same nodes in the same order,
because it puts the same stored KVs in the same order into the same
structure. Value transformations run before the value is stored, and the
stored value is what the rerun puts; no-op deletes are not stored and change
nothing (after 10's change, they also mark nothing). `RestartInvariance`
checks the outcome: the same stream bytes, the same D and the same node
identity with and without restarts.


## 8. Root and levels

Work package B2, 2026-10-15. Frans chose option (a), a virtual root (Q7),
before B2; this section works it out, with the levels (M12) and the fix of
M18.

### 8.1 The difference

The model has one root, id 0, an ordinary index node: it is marked when
anything changes, written when taken, and every record names the record of
its latest version, top(i). Startup starts reading there.

Java has no such node. It has a chain of top nodes (`TopDs`, a skip list):
each top node points to the root key node of its time and to some older top
nodes; the newest, the super root, is the entry point. A root change (a
time or space split of the root key node) makes a new top node, except that
a second root change in the same transaction updates that transaction's top
node in place (`newSuperRoot`, line 45). Top nodes never change after their
transaction. Startup scans the section for the top node with the largest id
and walks the skip pointers to the one at the startup time
(`findSuperNodeAtStartupTime`). No record says where the super root is: M18.

### 8.2 Option (a): the root is virtual

The model keeps the root as a node of P, with an entry `top(z)` at time c
for each top node z created at time c; its live child at t is the newest top
node created at or before t. The changes:

1. **The root is never in D and never written.** Step 3 leaves it out; R(0)
   has no version of it. Nothing else in steps 4 to 8 needs to change: a node
   that is never in D is never taken, written or put back.
2. **Root children.** The `Spec` gets two more functions: `topLevel`, the
   level from which nodes are root children (top nodes), and `rootVal z`, the
   root's entry value for a child z (`top(z)`). New assumptions, all met by
   BergDB:
   * R1. The root is above every node. Its pointees, the root children, are
     exactly the nodes at levels ≥ `topLevel`. A root child points only to
     root children and to nodes below `topLevel`.
   * R2. A transaction gives the root one entry (i, `rootVal z`) for each
     root child z it creates, in creation order, and no other entries.
   * R3. A root child gets all its entries in the transaction that creates
     it.
   * R4. From each root child, every older root child can be reached through
     pointers (live or dead) between root children. In BergDB, the skip
     pointers: `findSuperRootAtTime` must find the top node of any earlier
     time from the newest, by following them.
3. **top(i)** := the record of lv(c), for the newest root child c that has a
   version in the stream including R(i). That is the root child live at
   s(i): a root child created at time c is in D from c on (it is new) and is
   taken, and so written, exactly when the startup pos reaches c.
4. **Startup** rebuilds the root before it reads the rest. From top(k), with
   Rule R, it reads the newest written root child, and from it, through the
   references of each root child version to pointees at levels ≥
   `topLevel` (Rule R again), every root child up to s. The root's history up
   to s is then (c_z, `rootVal z`) for each root child z read, c_z the time of
   z's entries (R3), in the order of c_z. Then `baseStruct` reads as now,
   starting at time t from the root's live child at t, at the version just
   read; the rerun adds the root's later entries, as for every node.

The statements of T1 and T2 stay as they are: P with the root and its whole
history, D, and the records. The proofs change where they handle the root:
the invariant "every dirty index node is in D" leaves the root out (it has
no version, so it is dirty by definition); marking and D's upward closure
(T13, T15, WPs E1 and E2) leave it out; L-SEC and the base reading
(`Proof/Recon.lean`, `Proof/Base.lean`) get the root-child chain. Estimate:
M to L in Lean, after E2, as WP E3 plans.

Why (a) fits Java: Java's root is the skip list, and Java rebuilds it lazily
by walking skip pointers from the super root (`findSuperRootAtTime`); the
model rebuilds it eagerly from the same versions. The checker can compare
records exactly: no root version and no root in gd, on either side.

### 8.3 The fix of M18 (WP D0)

Java gets the model's top(i): every record names the position of the latest
version of the newest written top node. By 8.2 point 3 that is the super root
at the record's startup time.

* Java keeps the newest written top node (the largest `topNodeId` among the
  top nodes written so far) and its latest position. `prepareToSerialize`
  assigns the positions of R(i) first, so the field can name a version in
  R(i) itself.
* `StoredTrans`: a new header field after the startup pos (8 bytes), and a
  new format byte; streams of the old format are refused with a clear
  message (Q5). Today the header's version byte is 2 (`serializeHeader`,
  line 595; the parser checks `version != 2`), while
  `CURRENT_FORMAT_VERSION = 4` is used for nothing; one constant for both.
* Startup: the super root at the startup time is the version that the last
  record's field names, or the newest version of the same node in the
  section (Rule R). `findLatestSuperRoot`'s scan goes. `findSuperRootAtTime`
  from that top node returns it (it is the super root at the startup time);
  older top nodes are read through the skip pointers, as now.
* Cost: 8 bytes per record.

The same field closes a possible silent variant of M18, not observed: if the
section held a version of an older top node but none of the newest written
one, the scan would start from the older one and find a super root that is
too old.

### 8.4 Levels

For a run (Java's structure is finite at any time):

* value nodes: 0;
* a key node in key segment g (0 for the first segment, `Keys.toSegments`)
  at height h within its segment tree (0 for a segment leaf): 1 + (G − g) ×
  (H + 1) + h, where G is the largest segment index and H the largest
  height;
* a top node with id k: L + 1 + k, where L = 1 + G × (H + 1) + H is the
  highest key node level;
* the root: L + 2 + `TopNode.MAX_TOP_NODE_ID_VALUE` (2^30 − 1), above every
  top node.

Every pointer goes strictly down: an internal key node to its children (one
height less, same segment); a segment leaf to value nodes (0) and to the
roots of the next segment (every level in segment g + 1 is below 1 + (G − g)
× (H + 1), the lowest level in segment g); a top node to its root key node
and to older top nodes (smaller ids); the root to top nodes. A key node's height and
segment never change: splits make nodes at the same height in the same
segment, and a new root above.

`topLevel` (8.2) is L + 1.

G and H are bounded for a run, which is all that a level function needs: the
model's `Spec` belongs to a run. G is at most the longest key in segments of
7 bytes; H is at most about log2 of the number of key nodes, at most 64 with
63-bit positions.

The exporter computes the levels after a run, from the final structure, and
the checker checks A4 for every pointer (C-A).

### 8.5 For the checker before E3

Until E3 changed the model (2026-10-16, 8.6), the checker implemented (a) in
checker-local definitions: step 3 leaves the root out, R(0) has no root version, top(i) is
8.2 point 3, and it compares records without a root version. The model's
current definitions (root written) are the checker's `exact` reference for
how far Java is from the unchanged model.

### 8.6 The virtual root in the model (WP E3, 2026-10-16)

Done in `lean/` (see its README, "Changes to the trusted part on
2026-10-16"). What was built, where it differs from the design above:

* `Spec.virt` switches the virtual root on (default off, so that the
  examples with a written root stay valid); `Spec.topLevel` and
  `Spec.rootVal` as in 8.2. Step 3 never gives the root (`written`), R(0)
  does not write it. `Record.top` is now a node and a record: BergDB's topPos
  names a version.
* top(i) is the root's child named by the root's last entry up to s(i), with
  the record of its latest version (`topV`): the super root at the startup
  time. 8.2 point 3 defined it as the newest root child that has a version,
  which is what Java stores. The two are the same: a root child created up to
  s(i) has a version (`Inv.topAt_lv` in `Proof/VRead.lean`), and one created
  after s(i) has not been taken yet (an argument, not proven in Lean). The
  checker compares the model's top(i), node and record, with Java's topPos on
  every record (C-S): no difference (10.3).
* Startup reads the root children from top(k)'s version through their
  pointers, live or dead, with Rule R (`readTops`), and rebuilds the root: for
  each time t ≤ s at which a root child read has its entries, the entry
  (t, rootVal z) (`rootVersion`); then reads as before.
* The assumptions (`VirtInit`, `VirtStep`): R1 to R4 as in 8.2, and two more:
  at most one new root child per transaction, an index node with entries
  (`TopDs.newSuperRoot` updates the transaction's top node in place); a root
  child that a root child points to is not reachable (BergDB's older top
  nodes are dead). The checker checks all of them on Java's traces (C-A).
* **A finding**: with a virtual root, T1 and T2 need BergDB's still-dirty
  test, Rule A over all pointers (`exactWitness3` in `SIS/Example.lean` is a
  run where the exact test breaks T1 with the virtual root). Startup finds an older top node only through
  the references of newer top nodes (the skip pointers, dead pointers in the
  model). The exact test puts a written node back only if it is dirty, which
  looks at live pointers only; so a top node could keep a reference to a
  stale version of an older one. BergDB's test puts back a top node that
  points to a node of D, so the latest version of every top node names the
  latest versions of the older top nodes it points to (`VInv.fresh` in
  `Proof/VStep.lean`). The theorems are now stated for BergDB's test, or, with
  a written root, the exact one.
* M7 and M10 too: Rule R looks at R(s), ..., R(k) (`newest`), and the policy
  gets the transaction (`Algo.policy`).
* The checker now runs the model's own `init` and `step`; its checker-local
  definitions of 8.5 are gone. The exporter writes the node of top(i) on the
  `REC` line (9.2).

## 9. Trace format

Work package B3, 2026-10-15. The exporter (`java/stress/TraceExport.java`,
WP C1) writes a trace of a Java run in model terms; the checker (`lake exe
tracecheck` in `lean/`, WP C2) reads it.

A trace is a text file in UTF-8, one item per line, tokens separated by one
space. Lines starting with `#` are comments; empty lines are ignored.
Numbers are decimal natural numbers. `-` stands for "none". Every id is a
model id (2.2): a Java id, or 0 for the root.

### 9.1 Entries

An entry value is one of (2.4):

| Tokens | Value | `ptrs` |
|---|---|---|
| `K c y` | key klong: compare value c, child y | [y] |
| `D n c1 ... cn` | delete bitmap: deletes the key entries before it with compare values c1 ... cn | [] |
| `R y` | top node's root pointer to key node y | [y] |
| `S j z` | top node's skip pointer j to top node z | [z] |
| `T z` | the root's entry for top node z | [z] |
| `V h` | value node data, h a hash of the bytes | [] |

### 9.2 Lines

    TRACE 1                      format version, first line
    CONFIG text                  workload parameters, seed, bergdb commit
    TX i                         starts transaction i (record R(i)); TX 0 is R(0)
    NEW x level kind             a node created by T(i); kind I (index) or D (data)
    ADD x t entry                an entry added to node x by T(i), at time t = i
    REC i sp top src [z]         record R(i): sp(i) and top(i) (record index or -);
                                 src is field (Java stores it) or derived (computed
                                 by the exporter from the stream); z, the node of
                                 the version top names (since 2026-10-16, WP E3)
    VER x kind                   a version of node x in R(i), in Java's order
    H t entry                    the version's history, one line per entry, in order
    F y r                        the version's reference for pointee y: record r
    GD x1 x2 ...                 gd(i), in Java's order
    DIRTY x1 d1 x2 d2 ...        D after T(i)
    LIVE x t y1 y2 ...           Java's live children of x at time t (optional)
    PROBE i ok|fail text         run B (2.9): a restart after T(i) and its checks
                                 (D, lookups), or the stream comparison at the
                                 end; fail with what went wrong
    ERROR text                   a problem the exporter found (counts as a failure)
    END i                        ends transaction i
    DONE n                       last line: n transactions after R(0)

Within `TX i`, the order is: `NEW` lines, `ADD` lines, `REC`, the versions
(`VER` with its `H` and `F` lines), `GD`, `DIRTY`, `LIVE`, `PROBE` blocks, then
`END`. `ADD` lines are in the order the entries stand in each node, so that
applying them gives Java's order of entries. A comment line after the
`ERROR` lines counts the key nodes that no top node reaches: nodes that a
later key of their transaction replaced (M1), which the checker reports as A3
failures.

The root (id 0) appears in `TX 0` as a node, and gets an `ADD 0 i T z` for each
top node z that T(i) creates.

Levels are those of 8.4, computed after the run, so a trace is written when
its run ends.

The exporter reports as `ERROR` what α cannot express: a change that is not
new nodes plus entries at time i (an entry removed or changed, a node whose
kind changed), a stored position that is not the start of a version, a
version whose node is unknown, a stream pointer in a run without restarts,
and M4's assertion (7.1).

### 9.3 Example

A hand-made trace (ids and numbers shortened): R(0) with the top node 3 and
the empty root key node 5; T(1) puts one key; T(2) changes nothing, and the
startup pos moves to 1, so that R(2) writes the nodes of D.

    TRACE 1
    CONFIG example
    TX 0
    NEW 0 9 I
    NEW 3 8 I
    NEW 5 1 I
    ADD 0 0 T 3
    ADD 3 0 R 5
    REC 0 0 0 field
    VER 3 I
    H 0 R 5
    F 5 0
    VER 5 I
    DIRTY
    END 0
    TX 1
    NEW 7 0 D
    ADD 7 1 V 123
    ADD 5 1 K 40 7
    REC 1 0 0 field
    VER 7 D
    H 1 V 123
    GD 3 5
    DIRTY 3 1 5 1
    END 1
    TX 2
    REC 2 1 2 field
    VER 3 I
    H 0 R 5
    F 5 2
    VER 5 I
    H 1 K 40 7
    F 7 1
    GD
    DIRTY
    END 2
    DONE 2

The checker builds P(0) from `TX 0`, and P(i) from P(i−1) and the `NEW` and
`ADD` lines of `TX i`. `exec` of the instance returns, for transaction i, the
changes of `TX i`.


## 10. Red list

### 10.1 The unchanged code, 2026-10-15 (WP C3)

`java/stress/conformance.sh small` and `medium` on `a116ec7` (production code
unchanged). The small set is five configurations with ten seeds each: mixed
transactions with deletes, transactions that change nothing and a restart
after every transaction; long keys (two segments); 40-key transactions;
sorted bulk loads of 40 keys; mostly idle transactions (30 percent empty, 20
percent deletes of missing keys) at a startup distance of 100 bytes. The
medium set: 300 to 500 transactions, node sizes 8 to 30, up to 3,000 keys.
Raw summaries: [evidence/level2-redlist-baseline.txt](evidence/level2-redlist-baseline.txt).

The checker in its target mode (marking in step 3, Java's still-dirty test,
the virtual root), 50 small traces, 3,700 transactions after their R(0):

| Check | Result | Register |
|---|---|---|
| C-A: A2 fails | 579 transactions | M1 |
| C-A: A3 fails | 100 transactions | M1 |
| C-A: A4, A5, fresh and distinct ids, data nodes | no failure | — |
| C-S: gd and D differ | 1,535 transactions; in every one, the difference is nodes in Java's gd and D that the model does not mark | M2 |
| C-S: sp, top, the versions, their histories and references | no difference | M5, M6, M11 (a) agree |
| C-V: live children | 0 differences in 130,683 LIVE lines | 2.4 validated |
| C-R: restarts | 11 restarts fail with "Could not find super node in startup section", all in configurations with transactions that change nothing | M18 |
| exporter errors | none | — |

The medium set, 9 traces: A2 in 164 transactions, A3 in 47, gd and D in 1,504
(Java's extra nodes again); nothing else.

In the unchanged model's mode (`--model`), 6 small traces: the root (id 0) in
the model's R(0), gd, D and top(i) on every transaction (M11), and A2 in 16
transactions (M1). The self-check, the checker's step with all switches off
against the model's own `step`, agreed on all 360 transactions.

**The same set on 10's prototype** (scratch copy): no C-A failure and no C-S
difference in any trace; 33 of 50 traces pass every check. The 17 others fail
only C-R, with M18; more than on the unchanged code, because deletes of
missing keys no longer mark the super root. So M1 and M2 are what 10's change
removes, and M18 must be fixed first (WP D0).

**Classification: every failure maps to a register row (M1, M2, M11 in the
model mode, M18). Checkpoint K1 passes automatically.** What agrees exactly,
on every transaction checked: the references Java writes (M5, argument 7.2
now checked), the versions of each record as a set (M6), sp, the virtual
root's top(i), and the live children.

### 10.2 After D0, 2026-10-15

With D0's fix of M18 (format 5, topPos), `conformance.sh small` on the work
tree: C-R has no failure left (the 11 restart failures are gone), the
exporter finds topPos equal to its own derivation on every record, and the
rest is as in 10.1: M1 (A2 in 579 transactions, A3 in 100) and M2 (gd and D
in 1,544).

**D0 together with 10's prototype** (scratch copy): `CONFORMANCE OK`, all 50
small traces pass every check in the target mode (C-A, C-S, C-V with 127,707
LIVE lines, C-R, the exporter's own checks). So with D0 and D1, every Java
transaction checked is a step of the model with marking, BergDB's
still-dirty test and the virtual root. What remains on the model's side is
the virtual root itself (E3).

**Performance** (`SUITE=quick java/stress/performance.sh ab l2a-base current`,
22:31 to 22:45, 95 percent idle at the start, with `FORCE=1` after a first
attempt was refused at 69 percent idle; one run, so not a reference): no
alerts. Medians: reads 1,262,440 to 1,316,920 gets/s (get_latest), writes
89,241 to 89,327 commits/s (w-uni-1k-inf) and 58,367 to 58,654 (w-uni-1k-fin),
startup 0.666 to 0.651 s (r-1k-fin). The stream grows by topPos's 8 bytes per
record: 1,920.8 to 1,934.8 MB in r-1k-fin, bytes appended per user byte 1.22
to 1.23 and 1.69 to 1.70. The comparison flags two maxima (the slowest single
commit of a run): 23 to 90 ms in the reference's runs and 82 to 88 ms in the
candidate's (r-1k-fin), 29 to 165 ms and 21 to 183 ms (w-uni-1k-inf); the
p99.9 is unchanged (34 to 36 µs), so these are single outliers.

### 10.3 After E3, 2026-10-16

The checker now runs the model's own `init` and `step`, with the virtual
root of the model (8.6), and checks R1 to R4 and the dead older top nodes
(C-A); the exporter writes the node of top(i), and the checker compares
top(i) as a node and a record.

* **The work tree** (D0, without 10's change), `conformance.sh small`: as in
  10.2, M1 (A2 in 579 transactions, A3 in 100) and M2 (gd and D in 1,544),
  nothing else: R1 to R4 hold on every transaction, and the model's top(i)
  (the root's child at s(i)) is Java's topPos, node and record, on every
  record.
* **D0 together with 10's prototype** (scratch copy, standing in for D1):
  `CONFORMANCE OK`, 50 of 50 small traces pass every check (127,707 LIVE
  lines), and 9 of 9 medium traces. The medium set took the checker 1 hour 51
  minutes (2 minutes in C3): since E1 it evaluates the model's `markOf`, which
  is quadratic in the nodes of P.
* The unchanged model's mode (`--model`, a written root and the exact tests):
  the root in gd, D and top(i) (M11), as before; the checker's self-check is
  gone, since its step is now the model's.
* sistest has a third structure with a virtual root (8 algorithms, 20 seeds,
  40 transactions: assumptions, T1 and T2 pass) and a witness for the finding
  of 8.6: a run of 41 transactions where the exact still-dirty test breaks T1
  with the virtual root, and BergDB's test does not.



### 10.4 After D1, 2026-10-16

D1 makes 10's change production code (`Dag.handleFullNode`,
`timeSplitInPlace`, `spaceSplitInPlace`; `KeyNode.setContentFrom` and its
class comment; `TopDs.newSuperRoot`; Db's `markAtEndOfOp`, `endOfOp`,
`endOfTrans`). On bergdb `01f386a` plus the work tree:

* **The Java tier** (`java/stress/A2A3Check2`, 10's checker, ported): ten
  configurations, 16,701 transactions, node sizes 8 to 62, 1 to 400 keys per
  transaction, deletes, two-segment keys, sorted and unsorted: no node with a
  klong at tt that is not reachable at tt (A2), no created node that is not
  reachable (A3), no resurrection (A5), and Db's marking equals the model's
  marked set in every transaction. DagFuzz: 5 configurations, 200 rounds
  each, 0 failures.
* **The checker**, `conformance.sh small`: `TRACECHECK OK`, 50 of 50
  traces (127,707 LIVE lines). The model's own mode (`--model`) shows only
  the root (M11), as expected.
* **Stream bytes** (`java/stress/DbJunk`, 10's five workloads, before D1 =
  `01f386a`):

  | Workload | Stream bytes, before D1 → D1 | Nodes in D not reachable, average |
  |---|---|---|
  | 1 to 3 keys, node size 30 | 3,991,496 → 3,855,424 (−3.4%) | 6 → 4 |
  | the same with 20% deletes | 3,530,968 → 3,269,528 (−7.4%) | 5 → 4 |
  | 200 keys | 24,659,712 → 24,305,256 (−1.4%) | 19 → 14 |
  | 2,000 keys | 108,732,408 → 100,260,160 (−7.8%) | 411 → 257 |
  | 1 to 40 keys, node size 8, 20% deletes | 33,389,400 → 28,831,048 (−13.7%) | 21 → 4 |

* The gates: `LEVEL 1 OK`, `LEVEL 2 OK`, `LEVEL 3 OK`; 908 unit tests, 37
  f-tests.
* **Performance** (`SUITE=quick java/stress/performance.sh ab l2a-base
  current`, twice, 10:22 to 10:52, against `a116ec7`, so D0's topPos is in
  the comparison too): no alerts either time. The first run had `FORCE=1` at
  89 percent idle (three attempts before were refused at 61 to 83 percent
  idle while the machine was in use), the second started at 95 percent idle.
  Medians of the second: reads −4.3 to +2.6 percent (get_latest −2.7,
  get_latest_mt4 −4.3, scans +2.2 to +2.6), writes −1.0 (w-uni-1k-fin) and
  +0.3 percent (w-uni-1k-inf), startup −0.9 to −2.7 percent. In the first run
  reads were +0.9 to +7.3 percent and writes −1.3 to +0.3 percent, so the
  differences are noise. Flagged in both, as after D0: the slowest commit of
  r-1k-fin, 81 to 85 ms in every candidate run (in the first run equal to the
  longest GC pause) against medians of 28 to 36 ms in the reference's (with
  CVs of 61 to 85 percent); not an alert.
