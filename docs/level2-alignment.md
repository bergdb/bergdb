# BergDB Level 2: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-15.
Work packages B1, B2, B3 and later of the plan F1-008-11 (repository f1,
`b/008-bergdb-lean-model/11-level2-alignment-plan-claude/`). Source commit
`a116ec7`; line numbers below are at that commit.

Status, 2026-10-16: all work packages done; D0 and D1 committed (`01f386a`,
`d5c56dd`). The outcome is in section 11, the proposal for the gates in
section 12; next is Frans's checkpoint K4.

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
| M8 | First touch after a restart: lazy; the newest of the named version and the section version (cut back to the startup time), or the node table's canonical object. The model reads all of P up to s at startup. Lemma M of `levels.md`. | `NodeCollection.followStreamPointer`; `DbStarter.canonicalNode` | `baseStruct`, `readFrom`; since bergdb item 001, the physical layer (`lean/SIS/Phys.lean`) | Model: the physical layer (13); proofs and C-L | Proved (item 001: LM, T1-L, CC, T2-L, 13.2 to 13.4); checked: C-L, every first touch after a restart follows the rule (13.5), besides C-R and `RestartInvariance`, c |
| M9 | gd order: Java has step 3's nodes in marking order, then step 7's in loop order; the model sorts step 3's by id, then step 7's lowest level first. | `TransInfo.gotDirtyNodes` | `gotDirtyOf`, `step` | Argument (7.3); C-S compares sets (Q9) | Argued and checked (C3), c |
| M10 | The startup pos policy uses T(i) (`valueCount`, `kvSize` set the node count limit) and byte lengths. | `Db.store`; `TransSeq.take` | `Algo.policy : Stream → Dirty → Time → Nat` | Model: the policy also gets T(i); bytes are a function of the concrete stream (7.5) | E3 done 2026-10-16 (`Algo.policy` gets T(i)), c |
| M11 | The root: the model's root 0 is an ordinary node, written and named by top(i); Java has a chain of top nodes and no node 0. | `TopDs`, `TopNode`; `DbStarter.findLatestSuperRoot`, `findSuperNodeAtStartupTime`, `doPrimordialStartup` | `root`, `reachList`, `Record.top`, `readAt`, `init` | Q7 = (a), a virtual root (section 8) | Designed (B2); model: E3 done 2026-10-16 (`Spec.virt`, 8.6); the checker runs the model's definitions; checked on the D1 code (F1, 10.5), c |
| M12 | Levels (A4): Java has none; keys longer than 7 bytes chain key trees through segments. | `Keys.toSegments`; `KeyNode.isSegmentLeaf` | `Node.level`, `StepOK.levels` | The level function of section 8; C-A checks A4 | Designed (B2); checked: no A4 failure (C3), c |
| M13 | A delete makes a value node of type delete. It is written in the record, for the rerun, but is never in the tree. | `Dag.setValue` (513); `ValueNode.createDelete` | A3 for data nodes | α: part of T(i), not a node (2.3) | B1, c |
| M14 | Node ids are vpos values from the record's position and a counter; the model makes ids from i and a counter, and its root is 0. | `Db.setIdOfNode`; `DbStarter.rerunTransaction` | `Spec.exec` | α: ids kept, 0 for the root (2.2); argument (7.6) | B1, c |
| M15 | The first run of a transaction applies key and value transformations and goes through no-op deletes; the rerun replays the stored value nodes. The model has one `exec` for both. | `Db.putKvs`; `DbStarter.rerunTransaction` | `Spec.exec`, `rerun` | Argument (7.6); `RestartInvariance` checks it | B1, c |
| M16 | Java's times are timestamps; the model's are record indices. | `StoredTrans.tt` | `Time` | α (2.1) | B1, c |
| M17 | Reclaim's touch marks nodes without adding entries. | `Db.touchRange` | — | Level 3, not this plan | —, out of scope |
| M18 | **A startup bug.** Startup finds the super root by scanning the startup section for the newest top node. A transaction that changes nothing does not mark the super root, so the startup pos can move past the last version of every top node, and the database cannot start ("Could not find super node in startup section"). Reproduced on `a116ec7` (F1-008-11, `probe/`). With 10's change, deletes of missing keys do the same. | `DbStarter.findLatestSuperRoot`, `findSuperNodeAtStartupTime`; `TransSeq.take` | `Record.top`, `readAt` | Code: every record names the position of the latest version of the newest written top node, the model's top(i) (section 8) | D0 done (format 5, topPos), c |
| M19 | `TransSeq.take` can move the startup pos with transactions that have no got-dirty nodes; the model's policy is clamped only by s(i-1) ≤ s(i) < i, which Java meets. Recorded to make M18's cause explicit; not a mismatch. | `TransSeq.take` | `startupPos` | None | B1, c |
| M42 | Rule R applies for the whole process: every first touch after startup, also of a pointer to a node written after startup, takes the newest version in the last startup section if it is newer than the version named (item 001, A2). | `NodeCollection.section`, `followStreamPointer` (step 2), `newestInSection` | `follow` (startup only); `ruleRRef` in the physical layer, for the whole process | Model: Rule R in the physical loader | Item 001: L1 (`ruleRRef`), proved with T1-L and T2-L (L3, L4; the writer after a restart reads from the stream of the startup, 13.4); checked: C-L (L5, 13.5), c |
| M47 | **New (item 001, L3).** The proof of T1-L assumes of every transaction what BergDB's pointers and splits give (`PhysStep`): a node's new live children are pointees of its new entries (a klong stays live until a later klong of its key), and a new live child of a reachable node that the transaction does not create was, just before, a live child of a reachable node that the transaction changes or replaces (a split's new nodes take the children of the node they split; M43). | `KeyNode` (klongs); `Dag.handleFullNode` and the splits | `PhysStep`, `PhysRunOK` (`lean/SIS/Phys.lean`) | An assumption of the physical layer (13.3). Java: `liveNew` by α (2.4: a key node's child for a compare value is that of its last klong, and a delete only removes); `adopt` from TREE and A5 (13.3), both checked on Java (A4: TREE in 68,901 transactions; A5: C-A). Checked by running on the model's examples (`physRunOKB`) | Item 001: L3, argued (13.3); a direct check in the trace checker is open (L5 or E1), o |

Since 2026-10-16, bergdb item 001 reopens M8 (stage 1, WPs L1 to L5: a Lean
model of lazy reading, which also closes M42) and M17 (Level 3). The rows of
Levels 3 and 4, M17 and M20 on, are in [level3-alignment.md](level3-alignment.md)
and [level4-alignment.md](level4-alignment.md). Lemma M itself is proved
(WP L2: `LM_newer`, `LM_ruleR`, `LM_cutTo` in `lean/SIS/PhysTheorems.lean`).

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
* the root: L + 2 + `TopNode.MAX_TOP_NODE_ID_VALUE` (2^48 − 1 since bergdb
  005-02, 2026-10-19; 2^30 − 1 before), above every top node.

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
    DONE n                       last line: the last record, R(n) (n transactions
                                 after R(0); with reclaim, user transactions and
                                 reclaim's records)

Format 2 (`TRACE 2`, since 2026-10-16, bergdb item 001, WP L5; the checker
still reads format 1) adds, from the item's plan (8.2):

    SKIPT j t                    after a top node version's H lines: its skip
                                 slot j caches time t (the time index of the
                                 target's root time, Java's pointersTime; M29)
    FIRST x n r kind cut         run B: a first touch of a stream pointer to
                                 node x after the restart after T(i) (in TX i,
                                 up to the next restart, the startup's own
                                 rerun included): the pointer names record n
                                 after Rule R (- for a vpos); Java took record
                                 r (- for a canonical object); kind is
                                 canonical, version (read from the stream) or
                                 snapshot (the node table's object); cut is 1
                                 if the version read was cut back to the
                                 startup time

With reclaim (the exporter's `retain=S`, since 2026-10-17, bergdb item 001,
WP R2; level3-alignment.md, 2.7), every executed transaction is a record:
the user transactions, and reclaim's steps and table stores, each an ordinary
`TX` block, with `kind=user`, `step` or `table` in its comment line. Format 2
then also has:

    TOUCH x1 x2 ...              in TX i, after the ADD lines: the index nodes
                                 T(i)'s touch visited (Db.touchRange), sorted
    FA t                         in TX i, when it changes: fa(i), the first
                                 available time, as a model time
    CUT c t                      in TX i: Java decided a cut at R(i): records
                                 before c may go; t is the first available time
    PHYSCUT c                    in TX i: after R(i), the stream's first position
                                 moved; R(c) is the first record that starts at
                                 or after it

`FA`, `CUT` and `PHYSCUT` come after `DIRTY`. Run B also restarts right after
each call that decided a cut, and looks up only from the first available time
on; its `PROBE` lines are in the block of the last record of the call (the
user record without reclaim).

With eviction (the exporter's `rune=S`, since 2026-10-18, bergdb item 001,
WP J4; level4-alignment.md, 7.3), run E executes run A's workload with a
forced eviction schedule (S: values, every or random; from J7 also budget,
the capacity controller), and format 2 also has:

    SLOT x y r kind              in TX i, at the end of the call whose last
                                 record is R(i): run E's resident canonical
                                 object of node x has a slot for pointee y
                                 that serializes record r (- for a vpos);
                                 kind is canon (a memory slot to y's
                                 canonical object), mem (to another object,
                                 or to a value), stream, or dead (a stream
                                 slot below the stream's first position)

SLOT lines come after the FIRST lines of their transaction, sorted. Run E's
`PROBE` line (its stream against run A's) is in the last record's block. The
checker's C-P checks the SLOT lines against the model's INV-SLOT.

FIRST lines come after the `PROBE` lines of their transaction. With `live=1`,
the root's `LIVE` lines cover every time t ≤ i on each record, at the record's
own time and at the last Java time before the next record (review-13-claude,
5.2: so that C-V compares the search's predecessor branch too).

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
* `conformance.sh medium` on the D1 code: `TRACECHECK OK`, 9 of 9 traces
  (F1, 10.5).

### 10.5 F1, the conformance campaign, 2026-10-16

The full set of 8.5 on the final code and model: bergdb `d5c56dd` (D0 and
D1), the model of E3. Raw summaries, with the time and memory of each run:
[evidence/level2-conformance.txt](evidence/level2-conformance.txt).

| Set | What ran | Result |
|---|---|---|
| Small, Lean tier | `conformance.sh small`: 50 traces, 3,700 transactions after their R(0) transactions, every one checked (C-A, C-S, C-V, C-R, diagnostics); 6 traces also in the unchanged model's mode | `CONFORMANCE OK`: 50 of 50 traces pass every check. No failing transaction in C-A, C-S or the diagnostics; C-V: 127,707 LIVE lines, no difference; C-R: 2,320 probes, no failure; no exporter error. 5 minutes 20 seconds, at most 237 MB (the exporter) and 12 MB (the checker). The model's own mode differs only by the root (M11) |
| Medium, Lean tier | `conformance.sh medium`: 9 traces of 120 to 500 transactions, node sizes 8 and 30, up to 3,000 keys, every transaction checked | `CONFORMANCE OK`: 9 of 9 traces, 3,360 transactions after their R(0) and 57 probes, no failure in any check. 1 hour 53 minutes (3 to 21 minutes per trace) on one core |
| Small, medium and large, Java tier | `A2A3Check2` on 21 configurations, 68,901 transactions: 10's set; node sizes 8 to 62 with 500 to 3,000 keys and 500 to 2,000 transactions; and the sizes of `RestartInvariance`'s configurations in `level2.sh`, up to 12,000 transactions | no A2 (net), A3 or A5 failure; Java's marking equals the model's in every transaction |
| | `DagFuzz`, 5 configurations, 200 rounds each | 0 failures |
| Large, restarts | `RestartInvariance` on `level2.sh`'s six configurations, with 10 percent empty transactions and 10 percent deletes of missing keys (new options `empty` and `nodel`) | the same stream bytes, transaction sequence, KVs, node identity and lookups with and without restarts, in every configuration |
| Transactions that change nothing (M18) | `RestartInvariance` with 30 percent empty transactions and 20 percent deletes of missing keys, a startup distance of 100 bytes, restarts every 1 or 10 transactions; 5 seeds each | on `a116ec7`, before D0: all 10 runs fail ("Could not find super node in startup section"); on `d5c56dd`: all 10 pass |
| The gates | `level1.sh`, `level2.sh`, `level3.sh` | `LEVEL 1 OK` (908 unit tests; 1.5 minutes), `LEVEL 2 OK` (11 minutes), `LEVEL 3 OK` (5 minutes), on a scratch copy of the final work tree, 11:22 to 11:40 |

Every set includes transactions that change nothing: the small set's
`mixed` and `idle` configurations, the medium set's `m-mixed`, and the
`RestartInvariance` runs above. Nothing failed, so there is nothing to fix
or to register.

The medium set is smaller than 8.5's (C3's choice: the checker's time grows
fast with the number of versions); the Java tier covers 8.5's medium and
large sizes instead. The checker checks every transaction of the medium
traces, not a sample. Since bergdb item 001's WPs C2 and C3, the Lean tier
also has a large set (`conformance.sh large`, 12 traces of 1,000 to 5,000
transactions, node sizes 8 to 62, up to 3,000 keys): all pass, in 60 minutes
with four traces at once (section 12;
[evidence/level2-conformance-c3.txt](evidence/level2-conformance-c3.txt)).

## 11. Outcome (WP F2, 2026-10-16)

The outcome of section 1.2 of the plan F1-008-11, point by point, on bergdb
`d5c56dd` and the model of E3.

1. **Correspondence: done.** α is in section 2; the steps of the model's
   algorithm and startup are mapped to Java in sections 3 and 4, the
   assumptions in section 5. Every register row (section 6) is resolved:
   by a code change (M1, M2: D1; M18: D0), by a model change with proofs
   (M2: E1; M3: E2; M7, M10, M11: E3), by an argument with checks (M4 to M6,
   M8, M9, M13 to M16; section 7), by the level function and the check of
   A4 (M12), or is out of scope (M17, Level 3) or a note (M19). No row
   needed Frans's acceptance beyond the plan's defaults.
2. **Java runs meet the assumptions: done.** C-A, on every transaction of the
   59 traces of 10.5: `SpecOK` for R(0); `StepOK`, that is fresh and distinct
   ids, A2, the data node rules, A4 and A3; A5; and the virtual root's R1 to
   R4. No failure. The Java tier, on 68,901 transactions up to node size 62,
   400 keys per transaction and 12,000 transactions: no A2, A3 or A5
   failure.
3. **Java's steps are the model's steps: done.** C-S, on every transaction
   of the 59 traces: the model's `step`, from α of Java's state before T(i)
   with Java's startup pos, gives Java's record R(i) (sp, top(i) as node and
   record, the versions as a set with their histories and references, gd as
   a set) and Java's D. No difference. The Java tier: Java's marking equals
   the model's marked set on all 68,901 transactions.
4. **Restarts: done.** C-R: every probe of the 59 traces (a second
   database started from the stream after transaction i) gives the P and D
   of the run without restarts. `RestartInvariance`: the same stream bytes,
   D, node identity and lookups with and without restarts, in `level2.sh`'s
   configurations and with transactions that change nothing. Lazy reading
   after a restart (M8, lemma M) is argued (7.4) and checked by these
   restarts; the model reads all of P at startup.
5. **Proofs: done, without T15.** Lean proves T1 (`T1_recovery`,
   `T1_crash`, `T1_nodes`), T2 (`T2_restart`) and T13 (`T13_markExact`) for
   the model with marking in step 3 (or testing), BergDB's still-dirty test
   (or, with a written root, the exact one), the virtual root, Rule R from
   R(s), and a policy that sees T(i), under the assumptions of point 2.
   `lake build` gives no warnings and has no `sorry`; `#print axioms` shows
   only propext, Classical.choice and Quot.sound. T15 (D stays closed
   upward) is not proved: the proofs of T1 and T2 for BergDB's test did not
   need it (E2). The property is checked instead: the checker's
   diagnostics test it on every transaction (no failure).
6. **No regressions: done.** The gates pass in full on the final code
   (10.5). The quick performance suite against A1's baseline (`l2a-base`,
   `a116ec7`), after D0 (10.2) and twice after D1 (10.4): no alerts, the
   medians within noise. Flagged, not an alert: the slowest single commit of
   r-1k-fin (81 to 88 ms in every run after D0 and D1, against 23 to 90 ms in the baseline's runs), with
   an unchanged p99.9. These runs are not reference runs (one had
   `FORCE=1`).

Not claimed, as in the plan: that every possible Java run is a run of the
model. α is written down and checked on many runs, not proven; bytes, torn
records, durability, concurrency and resource bounds stay outside the
model, and the gates cover them.

## 12. Proposal for checkpoint K4: conformance in the gates

**Adopted 2026-10-16 13:14** (Frans: "Yes, as you propose"): points 1 and 2
in both modes, point 3 as proposed (10 traces quick, 50 full). Done in
`level2.sh`: the mostly idle runs in step 4, the rest as step 7.

A step 7 of `level2.sh`, "Conformance with the Lean model", in both modes
(times measured on F1's runs):

1. `RestartInvariance`, mostly idle: `-Dsd=100 -Dkeys=100 -Devery=1
   -Dlong=1 -Dn=400 -Ddel=1 -Dempty=30 -Dnodel=20`, seeds 1 and 2, checked
   as step 4 checks its runs. About 5 seconds each. It catches M18: on
   `a116ec7` every seed fails.
2. `A2A3Check2` on three configurations: `-Dops=4 -Ddel=25 -Dlong=1`;
   `-Dops=40 -Dexact=1 -Dn=50 -Dkeys=1000 -Ddel=25 -Dlong=1`; `-Dmaxnode=62
   -Dkeys=1000 -Dn=2000 -Dops=40 -Ddel=20 -Dseeds=3`. Under 5 seconds in all.
   It fails unless the NET line, A3, A5 and the MARKING differences are 0;
   since 2026-10-20 (bergdb 005-04) also unless TREE, A6' and A-COPY hold,
   and the checker's C-A checks them too (point 3).
3. The checker on the small set: `conformance.sh small 2` in quick mode
   (10 traces), `conformance.sh small` in full mode (50 traces, 5 minutes 20 seconds;
   16 seconds since bergdb item 001's C2 and C3, with the fast checker and four
   traces at once). It needs the checker (`cd lean && lake build`, with Lean 4
   v4.34.1); the step would build it, and fail if it cannot.

Points 1 and 2 need only the JDK and cost seconds. Point 3 is the strongest
check, since it compares every record with the model's, but it makes the gate
depend on Lean. Frans decides (K4); until then, `conformance.sh` and
`A2A3Check2` can be run by hand, as in 10.5.

**Times, 2026-10-16, after bergdb item 001's WPs C2 and C3** (fast checker, four
traces at once; `docs/evidence/level2-conformance-c3.txt`): step 7 about 20 seconds
in full mode (A2A3Check2 4 seconds, `conformance.sh small 10` 16 seconds) and about
8 seconds in quick mode (since bergdb item 001's L5 the small set has a sixth
configuration, `hot`, one key at node size 8 with the root queried at every
time: 60 traces, 19 seconds, 12 in quick mode). The sets by hand: small 16 seconds (50 traces), medium
46 seconds (9 traces; 1 hour 53 minutes before C2), and the new large set
(`conformance.sh large`: 12 traces, node sizes 8 to 62, 1,000 to 5,000 transactions,
up to 3,000 keys, two configurations with 133 and 501 top nodes) 60 minutes, of which
the two traces at node size 62 take 45 and 49 minutes; the trace of 5,000 transactions
at node size 30 takes under 8 minutes. All CONFORMANCE OK.


## 13. Lazy reading (bergdb item 001, stage 1)

Work packages L1 to L5 of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)),
from 2026-10-16: what Java holds in memory after a restart, and how it reads a
node on first touch, as definitions of the model (`lean/SIS/Phys.lean`), and
the theorems that make M8 (lemma M) a proof. The logical model stays the
specification; this is the first part of the physical layer, which stage 2
(eviction, [level4-alignment.md](level4-alignment.md)) extends.

### 13.1 The physical layer, part 1 (WP L1)

**State** (`Obj`, `Slot`, `Mem`):

* An object is a Java `Node` object: its node, level and kind, its history, a
  canonical flag (`Node.isCanonical`), its position (`pos`, Java's spos: the
  record of the version it holds, none before its first write), and one slot
  per pointee of its history, live or dead (Java's `pointers[i]` and
  `pos[i]`): a memory slot names an object, a stream slot names a record, or
  none for a vpos.
* The memory: the objects by handle; the node table (`Cache3`), one object per
  node; the startup pos s of the last startup (Rule R takes the newest version
  in R(s), ..., R(k); a key node version of the section read at startup is
  cut back to s); the root's object.

**The first touch** (`Mem.follow`; `NodeCollection.followPointer` for readers,
`WriterFollower` for the writer). A memory slot gives its object; the writer
makes it canonical. A stream slot naming record r:

1. Rule R (`ruleRRef`): the newest version of the pointee in R(s), ..., R(k),
   if it is newer than r; from a vpos, that version whenever there is one.
2. The table's object, if it is canonical or a snapshot at least as new
   (`Obj.usable`).
3. Otherwise the version is read (`Obj.ofVersion`), cut back to s if it is a
   key node version of the section (`isKeyLevel`; Java's
   `toPreviousState(startupTime)`), and entered in the table (`Mem.register`,
   `Cache3.isBetter`: never over a canonical object, else the newer).
4. The slot then names the object (it is swizzled), and the writer makes the
   object canonical (`Mem.makeCanonical`: the table's canonical object, else
   the newer of the two by position, now canonical and the table's).

Rule R applies for the whole process, at every first touch (M42).

**Reads** (`Mem.read`, `Mem.readAt`): from the root's object at time t, down
the live children at t, through the readers' follower; each object reached,
with its history at t.

**Startup** (`lazyStartup`; `DbStarter.doOrdinaryStartup`):

1. The canonical objects of the section's index nodes (`sectionNodes`), each
   from its newest version in R(s), ..., R(k), cut back to s, with Rule R in
   its stream slots (`canonOfVersion`; `createMaps`, `updateStreamPointers`,
   `changeKeyNodesToStateAtStartupTime`, `registerSectionNodes`); but not the
   nodes whose newest version has no entries up to s, which Java leaves out
   as created in the rerun section (`wasCreatedInRerunSection`; since L3,
   13.3).
2. The root's object: with a virtual root, rebuilt from the root children read
   from top(k), as the logical startup does (`rootVersion`, `topsRead`).
3. Memory slots between canonical objects (`Mem.linkCanonical`;
   `createMemoryPointers`).
4. The rerun of T(s+1), ..., T(k). For each: the writer reaches the nodes of
   its paths (`pathOf`: the nodes reachable at j - 1 with a node below them that
   the change changes or that it replaces; `Mem.reachOnPath`), which become
   canonical; the change is applied to the canonical objects
   (`Mem.applyChange`: a canonical object for each new node, the entries
   appended, and for each pointee of a new entry the slot of a new pointer
   (`Mem.newSlot`): a memory slot to its canonical object, else a copy of the
   slot of a canonical object whose node was reachable at j - 1 and had the
   pointee as a live child then, as a split copies the split node's pointers,
   else the object's own slot, else a copy of any canonical object's slot, as
   a new top node copies the super root's skip pointers; since L3, 13.3); and
   the nodes of gd(j) get canonical objects (`Mem.canonicalNode`: the
   table's, else the newest section version, else the latest version, cut
   back to s).

What it leaves out, and why:

* The TopDs search: the root's object stands for the skip list. Reads start
  at the root's live child at their time, as in the logical model; a top node
  never changes after its transaction, so every version of an older top node
  has its whole history (`VInv.topVers`).
* The keys: the writer's paths are given by the change (`pathOf`), not
  searched by key. Level 2 showed that Java's marking is the model's marked
  set (A2A3Check2's MARKING line), and Java marks what its put path follows.
* Which pointer a split copies: any canonical object whose node had the
  pointee as a live child just before; in BergDB the split node, the only one
  when TREE holds (level4-alignment.md, 4).
* The P that directs the rerun's paths is the logical startup's (`baseStruct`
  and `rerun`), which T1 shows to be the run's P.
* Smaller differences: Java's posMap includes value nodes and reads them at
  startup; the model reads them on first touch (they never change, and Java's
  value nodes are always canonical). Java leaves nodes created in the rerun
  section out of posMap; since L3 the model leaves out the nodes whose newest
  section version has no entries up to s, which are the same nodes but for a
  key node with no klongs at all (Java keeps it, which reads the same: no
  entries). Before L3 the model made their objects from their newest section
  version, so a node created after s had two canonical objects.
* Concurrency, access data, bytes; eviction (stage 2).

**Checks by running** (`lean/SIS/PhysExample.lean`, `#guard`):

* In every state of runs of example 3 (a virtual root) and of example 2 (a
  written root, four algorithms): the lazy startup, then reads at every time,
  in increasing and then in decreasing order, give P at that time, and every
  canonical object holds its node's whole history; also when the writer walks
  to every reachable node between reads.
* First touches: Rule R (a slot naming R(0) while R(2), in the section, has a
  newer version: the newer one is read, and, since the node has no canonical
  object, cut back to the startup time: Java's runtime cut-back, M22); a newer
  snapshot in the table serves an older reference; the writer makes it
  canonical; without it, the version named is read; `canonicalNode` for a node
  of D without a section version.
* A node of D that the rerun does not reach: it does not arise in the model. A
  node gets into D marked on the path of a change, or put back by step 7 after
  a write in the section. In Java it came from a delete of a key that did not
  exist, which marked its path and stored nothing to rerun, until F1-008-11's
  D1. `canonicalNode` still covers it.

### 13.2 The theorems of stage 1, in plain English

* **Lemma M** (WP L2, proved; `lean/SIS/PhysTheorems.lean`): `LM_newer`, in
  every run, a version of a node written at or after a version that is good
  for time t is good for t; `LM_ruleR`, so is the newest version in R(s), ...,
  R(k), which Rule R takes; `LM_cutTo`, a version cut back to s is good for t
  ≤ s exactly when the whole version is.
* **T1-L** (`T1_lazy`, WP L3, proved; `lean/SIS/PhysTheorems.lean`): after a
  run with BergDB's still-dirty test that meets the assumptions of the
  physical layer (`PhysRunOK`, M47), the lazy startup from its stream, or from
  a prefix of it (a crash), and then any sequence of reads (at times up to
  the last record) and writer follows (of live slots of canonical objects of
  nodes reachable at the last time): a read at any time t up to the last
  record gives P at t, each node reachable at t with its history at t. Every
  object in memory is canonical, with its node's whole history, or holds a
  version of its node from the stream, all of it or cut back to s; and a
  memory slot that a canonical object's node uses at a time t (the node
  reachable at t, the pointee a live child then) leads to a canonical object,
  or to one that holds a version good for t if it holds all of it.
* **CC** (`CC_canonical`, WP L4, proved): in a run with lazy restarts, after
  any of its transactions, every canonical object in memory, whether the
  startup made it or the writer's follows did, holds its node's whole
  history.
* **T2-L** (`T2_lazy`, WP L4, proved): a run with restarts, each a lazy
  startup, whose writer reads its view of P and reaches the nodes of its
  paths through the physical layer, appends exactly the same records as the
  run without restarts. Its versions and references still come from
  `mkVersion` (the node's history, `S.lv`); computing them from the canonical
  objects and their slots is stage 2 (E3).

### 13.3 The proof of T1-L (WP L3)

T1-L is proved (`T1_lazy`; the proofs in `lean/SIS/Proof/Fresh.lean` and
`lean/SIS/Proof/Phys*.lean`, listed in `lean/README.md`). The proof found
three places where the lazy startup of 13.1 did not do what Java does, and
needs two assumptions of every transaction.

**Refinements of the model** (`lean/SIS/Phys.lean`, trusted; each checked by
running, `phystest`, before the proof was done):

1. Step 1 leaves out a node of the section whose newest version has no
   entries up to s (Java's `wasCreatedInRerunSection`). Before, a node
   created after s got two canonical objects: one at startup, and one when
   the rerun created it.
2. The slot of a new pointer (`Mem.newSlot`) copies the slot of a canonical
   object whose node is reachable at j - 1 and has the pointee as a live
   child then (`srcOK`); before, the node did not have to be reachable, so a
   slot of a node that a split had already replaced could be copied. Next
   come the object's own slot and then, as before, any canonical object's
   (skip pointers). The slots are taken from the objects as they were before
   the transaction's entries, as a split copies the pointers its node had.
3. Every pointee of a new entry gets the new pointer's slot (`Obj.putSlot`),
   also one the object already had a slot for. Before, an old slot stayed: a
   stream slot naming an old version, when a node got a new pointer to a
   child it had pointed to before.

**Operations** (`Op`, `Mem.step`, `OpsOK`): what the theorem lets happen
between the startup and the read: reads at times up to the last record, and
the writer's follows of live slots of canonical objects of nodes reachable at
the last time (its walk down from the root).

**Assumptions** (`PhysStep`, for every transaction of the run `PhysRunOK`;
register M47). For the transaction at time i with change c:

* `liveNew`: a node's live children at i that were not its live children at
  i - 1 are pointees of its new entries. In BergDB a key node's pointer, its
  klong, is live until a later klong of the same key; a node gets a new live
  child only by a new klong.
* `adopt`: a new live child y at i of a node x reachable at i, which c does
  not create, was at i - 1 a live child of a node reachable then that c
  changes or that is not reachable at i. In BergDB a split's new nodes take
  the children of the node they split, which stops being current (or
  changes, in an in-place split); no path moves a child from one current node
  to another (M43). It follows from TREE and A5: y is reachable at i and not
  new, so by A5 it was reachable at i - 1, the live child then of some
  reachable node z (TREE at i - 1). If c did not change z and z were still
  reachable at i, y would still be z's live child at i, and z is not x (y was
  not x's live child at i - 1): two parents at i, against TREE.

The writer's paths after a restart reach only nodes on the paths of the
change; `adopt` says where a split's new node gets the slots for the children
it takes: from the node it splits, which is on a path. Both hold in the
model's examples 2 and 3 (`physRunOKB`, in `lake build` and in phystest).
On Java, `liveNew` holds by α (2.4) and `adopt` through TREE and A5, which
are checked; a direct check of `PhysStep` in the trace checker would need
nothing new in the traces (P before and after each transaction, and the
change), and is not done.

**The proof.** An invariant of the memory at time K, with respect to the run's
final state (`MemInv`, `lean/SIS/Proof/PhysInv.lean`): every canonical object
is the node table's object of its node and holds the node's history up to
K, and its slots are good at every time up to K at which the node is
reachable (they lead to a canonical object, or to a version good for that
time) and fresh at K (they lead to the latest version, or to a canonical
object); every other object holds a version of its node, all of it, or cut
back to s if it is the table's object of a node with no entries up to K; a
memory slot names the table's object or an older version; and the nodes that
must have canonical objects have them: the nodes of gd(d) for s < d ≤ K, the
section's index nodes with entries up to s, and the nodes with entries in
(s, K]. Nodes without a canonical object are then the ones the logical
invariants describe: their latest version is good (MG, `Cover.mg`) and, with
BergDB's still-dirty test, names the latest versions of their live children
(CF, `KCtx.fresh_ref`; from `CleanFresh`, a new invariant of every run, in
`Fresh.lean`). The invariant holds after startup's steps 1 and 2 and the
memory slots, at K = s (`PCtx.base_ok`); each transaction of the rerun takes
it from K to K + 1 (`rerunStep_ok`: the writer's paths, highest level first,
then the change); reads and writer follows keep it at the last time
(`MemInv.ops_ok`); and under it a read at any time up to K gives P at that
time (`MemInv.read_ok`). The proof uses L-OUT and L-SEC (`Inv.lout`,
`Inv.recon`, `Inv.ruleR_section`) and lemma M (`Inv.newer`).

What T1-L does not cover: CC and T2-L (WP L4), and Java's first touches
checked against the rule (WP L5, C-L).

### 13.4 The writer after a lazy startup (WP L4)

**Model** (`lean/SIS/Phys.lean`, trusted):

* A read returns, for each node it reaches, the node its object gives at the
  time: level, kind and history (`Mem.readAt`, `Obj.nodeAt`); before, only the
  history. Java's reads return node contents. The writer's view of P at time
  t is then a read at t (`Mem.view`).
* The writer's transaction after a lazy startup (`lazyTrans`): its change
  comes from the view it reads through the physical layer at i - 1; it
  reaches the nodes of its paths, highest level first (its follows make them
  canonical), and applies the change to the canonical objects, as the rerun
  does; the record is that of `stepWith`, steps 2 to 8 of `step` with the
  change given (`step_eq_stepWith`). Rule R and the versions that the
  physical layer reads come from the stream of the last startup: Java's
  section map is fixed at startup (M42), and every stream slot names a record
  of that stream.
* A run with lazy restarts (`runLazy`): after a transaction marked as a
  restart, the logical startup for ⟨P, D, S⟩ (as `runRestarts`), the lazy
  startup for the memory.

What stage 1 leaves out: the versions and references the writer writes come
from ⟨P, D, S⟩ (`mkVersion`), and steps 3 and 7 from P; computing them from
the canonical objects and their slots is the physical writer of stage 2
(E1, E3).

**The proof** (`lean/SIS/Proof/PhysFrozen.lean`, `PhysT2.lean`). After a
lazy startup at k1, the writer's memory after each later transaction j is
read against another run: the same transactions, with the startup pos frozen
from k1 on (`frozenAlgo`). That run has the same P at every time; after k1
it takes no node and writes only versions of new data nodes, so its stream
says nothing new about the nodes that the memory reads, and its state at j +
1 only grows from that at j (`frozen_grow`). The memory meets L3's invariant
for the frozen run's state at j (`LazyInv`): the read of the writer's view
gives P@j (`MemInv.read_ok`, with the stream of the startup, which agrees
with the frozen run's on every node without a canonical object,
`StreamAgree`); the writer reaches the paths (`MemInv.reachPath_ok`); the
invariant carries over to the frozen state at j + 1 (`MemInv.transfer`); and
the change applied takes it to j + 1 (`MemInv.applyChange_ok`). At a
restart the lazy startup meets it again (T1-L). So the view is P's at every
transaction, the change is the run's, and the records are the run's; and
every canonical object holds its node's whole history.

**Checks by running**: `checkLazy` in `lean/SIS/PhysExample.lean` (`#guard`s
on examples 2 and 3) and in `phystest`: after every transaction of runs with
lazy restarts, the writer's view is P's, the records are the run's, every
canonical object is whole, and the memory meets the invariant for the frozen
run (`memInvB`); 20 seeds of 40 transactions, 9,600 transactions, 0
failures, before the proof.

### 13.5 Java's first touches checked: C-L (WP L5)

**The exporter** (`java/stress/TraceExport.java`, trace format 2, 9.2): in
run B, a test-only hook in `NodeCollection.followStreamPointer`
(`NodeCollection.firstTouchListener`, a static field that is null, and so
does nothing, unless a test sets it) tells the exporter of every first touch
of a stream pointer: the node, the position after Rule R, the object Java
took, whether it read the version, and whether it cut it back. The exporter
writes a FIRST line for each, from the restart's own rerun up to the next
restart. It also writes the cached times of the top nodes' skip slots
(SKIPT, M29) and, with `live=1`, the root at every time.

**The checker** (`lean/Check/Steps.lean`, `firstFailures`, `topFailures`):

* C-L: every FIRST line follows `Phys.lean`'s rule (`Mem.follow`): the record
  that the pointer names after Rule R holds a version of the node, and is at
  least the newest of the node in R(s), ..., R(i), the section of that
  startup (`ruleRRef`; from a vpos, Rule R gives that version if there is
  one); Java took the node table's canonical object, a snapshot at least as
  new, or the version named, cut back to the startup time exactly when it is
  a key node version of R(s) on (`isKeyLevel`).
* In C-S, for each top node version: its skip slots are the set bits of its
  ordinal (the level minus `topLevel`), each names the target of the formula
  (the ordinal with the bits below the slot cleared, minus one), and caches
  the target's creation time (review-13-claude, 5.2).
* Test traces: `badfirst.trace` (a version reported as cut back before the
  startup pos: C-L fails) and `badskip.trace` (a wrong cached time: C-S
  fails, `skip`).

**Results**, 2026-10-16, bergdb `e24e633` with this WP's changes (the small
set with a sixth configuration, `hot`: one key at node size 8, the root
queried at every time):

| Set | Traces | FIRST lines | C-L failing | Other checks |
|---|---|---|---|---|
| small | 60 | 252,539 | 0 | `CONFORMANCE OK`; C-V 1,870,868 LIVE lines, no difference; no failing transaction; 19 s |
| medium | 9 | 43,873 | 0 | `CONFORMANCE OK`; 45 s |
| l-hot (large set, two seeds) | 2 | 4,961 and 4,920 | 0 | `TRACECHECK OK`; 501 top nodes, 4,425 SKIPT lines each |

Of the small set's first touches, 137,473 found the node table's canonical
object (a section node, or one the writer made canonical), 22,352 a snapshot
at least as new, and 92,714 read the version named; the medium set's: 24,784,
1,911 and 17,178. None was cut back: every key node of the section has a
canonical object, so Java's runtime cut-back is not reached today (M22), and
C-L checks that no key node version of the section is read without it.

So M8 and M42 are closed: lazy reading is proved for the model (LM, T1-L,
CC, T2-L) and Java's first touches after restarts follow the model's rule
(C-L). What stays open from stage 1: the physical layer's assumptions
(M47, argued; a direct check in the trace checker is not done).

**C-L4, the Level 4 loader** (2026-10-17, bergdb item 001, WP R8, change 3;
`loader4Failures`): since that change Java's loader is the Level 4 one
(`Mem.follow4`, `lean/SIS/Evict.lean`): the node table's canonical object,
or exactly the version the pointer names after Rule R, which the table does
not get; never a snapshot from the table (register M27 of
level4-alignment.md). C-L still checks stage 1's rule, which allows such a
snapshot; the diagnostic C-L4 counts the FIRST lines that took one, and does
not fail a trace, since traces of Java before the change have them. A cut
back stays C-L's: Java cuts back only while it reconstructs the database
(R8, change 2), and the trace does not mark which first touches those are.
Test trace: `snapfirst.trace` (a snapshot that C-L accepts and C-L4
counts). With the change, the small set (`level2.sh`, step 7) has
281,434 FIRST lines, 153,610 of them the canonical object and
127,824 the version read, none a snapshot (C-L and C-L4: 0 failing);
R2's small reclaim set, 375,663 (237,824 and 137,839), none a snapshot
either; before the change, 6 percent of a reclaim trace's FIRST lines took
one (430 of 6,438 in `r-small-1`).
