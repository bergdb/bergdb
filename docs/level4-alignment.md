# BergDB Level 4: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-16.
Work package A2 and later of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)).
Source commit `75d3c2d`; line numbers below are at that commit, in
`java/src/bergdb/`.

Status, 2026-10-16: A2's draft. The scope (section 1), a first α for the
cache (section 2) and the register (section 3), checked against the code;
the probes of A4 (section 4). To come: the design of E1 (section 5), what
Java must do (E7, section 6) and the outcome (F2).

Level 4 is eviction: data and index larger than memory, under a memory
budget, with readers, reclaim, crashes and restarts. The plan of item 001
puts it in the model before it is in Java: the model's physical layer says
what Java holds in memory, how it reads a node it does not hold, and how it
evicts; Java then implements that, and the checker compares. This document
says what "aligned" means for the cache, as
[level2-alignment.md](level2-alignment.md) does for Level 2: α of Java's
resident state (section 2) and the known differences, the register
(section 3). Reclaim is in [level3-alignment.md](level3-alignment.md).

Terms of the model as in level2-alignment.md: P, the structure; D, the dirty
set; S, the stream of records; lv(x), the latest version of x in S. The
physical layer adds objects, slots, the node table, the canonical flag and
pins (the plan, section 8.6).


## 1. Scope

* The physical layer of the model, over the logical one, and Java's resident
  state: objects, slots, the node table, pins, eviction, and the loader
  that reads a node Java does not hold.
* Lazy reading after a restart is the physical layer without eviction. It
  closes a Level 2 gap (M8, lemma M), so its record is in
  level2-alignment.md; its definitions are the first part of this layer
  (stage 1 of the plan, WPs L1 to L5).
* The reference rule with eviction: what a written version names for each
  pointee when the writer can no longer find every node in memory (M20,
  Option K or Option F of the plan, section 8.5).
* Reclaim's reads under eviction (M28): here. What reclaim is in the model:
  level3-alignment.md.

Not in the model: concurrency (readers beside the writer and beside
eviction: a Java protocol with targeted tests, Q8 of the plan); bytes and
memory accounting; the capacity controller's policy; the TopDs skip list's
lookup (the model abstracts it, level2-alignment.md, 2.4).


## 2. The mapping α for the cache (draft)

A draft, from the plan's 8.1. L1 completes it for lazy reading, E1 for
eviction.

### 2.1 Objects

* An **object** is a Java `Node` (`TopNode`, `KeyNode`, `ValueNode`), by
  identity. Its node: α of `getId()` (level2-alignment.md, 2.2). Its
  history: as in 2.4 there, from the object's own klongs (`KeyNode.klongs`,
  up to `size`), its fields (`TopNode`: the root pointer, the skip pointers,
  `rootTime`), or its value.
* **Canonical objects** (`Node.isCanonical()`): the one object per node that
  holds the node's whole history and may change. Made by the writer
  (`Db.registerNewNode`, line 831), by startup
  (`DbStarter.registerSectionNodes`, 251; `canonicalNode`, 451;
  `topNodeOfLastTransaction`, 289; the rerun's `nodeCreated` in
  `rerunTransaction`, 355), and when the writer's follower reaches a
  snapshot (`NodeCollection.makeCanonical`, 255, and `Cache3.makeCanonical`,
  137, which pick the table's canonical object or the newer of the two).
  Value nodes never change and are always canonical.
* **Snapshots**: objects read from a version on a reader's first touch
  (`NodeCollection.followStreamPointer`, 184, its step 3), with the
  version's history, cut back to the startup time if the version lies in
  the startup section (line 228). A snapshot never changes, apart from its
  slots.
* **Temporary objects**: read and not cached (`OpData.cachePolicy`; the
  default `Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES`, 1159, does not cache
  values over 1 MiB), never put into a slot.
* A canonical index object changes in place (puts, splits). Its `spos` is
  the position of its latest written version, or its vpos before its first
  write (level2-alignment.md, 2.6).

### 2.2 Slots

* For each pointer index i of an object, the **slot** is the pair
  (`pointers[i]`, `pos[i]`) of a `KeyNode` (fields at lines 69 and 72 of
  `dag/KeyNode.java`), or (`rootPointer`, `rootPointerPos`) and
  (`pointers[j]`, `pointersPos[j]`) of a `TopNode` (lines 16 to 28 of
  `dag/TopNode.java`); a skip slot also caches the target's time,
  `pointersTime[j]` (M29).
* A **memory slot** has an object; its long field then holds access data
  (`dag/AccessData.java`), not a position (M23). A **stream slot** has no
  object; its long field is a position (the start of a version), a vpos
  (the id of a node that had not been written when the pointer was
  written: no reference), or `Spos.NULL` (an unused skip slot).
* α of a slot: its pointee (the node of the object, of the version at the
  position, or of the vpos), and its serialized reference
  (`Pointer.getSposForStream`, line 81): the object's `spos` for a memory
  slot, the position for a stream slot. Before an index node is written,
  `NodeCollection.resolvePointers` (292) may change its slots (Rule R and
  the node table); the reference written is that of the slot afterwards
  (level2-alignment.md, 7.2).
* How slots change today:
  * a first touch makes a stream slot a memory slot (`followStreamPointer`,
    step 4, line 238): to the table's canonical object, to a newer snapshot
    in the table, or to a version read (M27);
  * the writer's follower replaces a memory slot to a snapshot by one to the
    canonical object (lines 161 and 243, `makeCanonical`);
  * `resolvePointers` makes a stream slot a memory slot to a canonical or
    newer object, or a stream slot to a newer position (Rule R);
  * the Dag's changes to canonical objects add klongs with memory slots, and
    splits copy slots (`KeyNode.setContentFrom`, `lastVersion`,
    `firstAndSecond`; `TopDs.newSuperRoot`, 42, inherits skip slots);
  * startup applies Rule R to the section's objects
    (`DbStarter.updateStreamPointers`, 182) and links them
    (`createMemoryPointers`, 226).

  No slot goes from memory back to stream: eviction adds that change, and
  the code relies on its absence (M24).

### 2.3 The node table

* `Cache3`, one per database, shared by `Db` and `NodeCollection`: a map
  from node id to one object (`CacheEntry.node`). It names the canonical
  object when there is one: `register` (115) never replaces a canonical
  object and replaces a snapshot by a canonical or newer one (`isBetter`,
  167).
* Entries are never removed (`pointerDestroyed`, 180, has no caller; M25):
  the table holds an object of every index node ever read or made (M26).
* Snapshots that `register` did not take (an older snapshot when the table
  has a newer one or a canonical object) are not in the table; the slots
  that point to them keep them.

### 2.4 Pins: what eviction must keep (for E1)

* D: the objects of `TransSeq`'s `TransInfo.gotDirtyNodes` (`TransSeq.add`,
  39; at startup, `DbStarter.rerunTransaction`). They are canonical and
  dirty.
* The record being written: `TransNodes`, from `TransSeq.take` to
  `NodeStream.appendNodes` in `Db.store` (1407). `TransNodes.clean` clears
  the dirty flags before the record is appended, so "not dirty" does not
  mean "written" (level4-plan.md, 4.3).
* The super root (`TopDs.superRoot`) and the root chain that E1 chooses.
* The objects of an operation in progress: a reader's path, the writer's
  path in `Db.putKvs`.

### 2.5 Other state of the process

* **Rule R for the whole process**: `NodeCollection.section`
  (`setStartupSection`, 270), the map from id to the newest position in
  R(s), ..., R(k) of the last startup, with the startup time. Used by every
  first touch and by `resolvePointers` (M42).
* **`NodeCollection.idByPos`** (52): a bounded map from a position to the
  node id in that version's header, for `resolvePointers`. It caches facts
  of the stream, which do not change, so its contents change no result.
* **Access data** (`Db.getAccessData`, 1605): today the constant -10,000,
  minus `Cache3.putSize`, which never moves (M40).
* **The writer's own reads**: `Db.warmup` (1501) reads the keys of every
  transaction through the readers' follower before it takes the write lock.
  So first touches by readers, and snapshots, occur in every run, also in
  runs with no readers.

### 2.6 What the model has instead

* P is logical: the model's step names lv(y) from S for every pointee y
  (`mkVersion`), whatever Java holds in memory (M20).
* Stage 1 of the plan models sections 2.1 to 2.5 without eviction
  (`lean/SIS/Phys.lean`, WP L1); stage 2 adds unswizzling, release and the
  Level 4 loader (`lean/SIS/Evict.lean`, E1 and E2).


## 3. The register

Checked against the code at `75d3c2d` in A2, 2026-10-16. "Java" names
classes and methods in `java/src/bergdb/`, with lines; "model" names
definitions in `lean/SIS/`. The stages and WPs are those of the plan,
section 5. Status: open (o), resolved in a WP (WP name), closed (c). Rows of
Level 3 are in level3-alignment.md; M8 and M42 stay in
level2-alignment.md's register, where stage 1 closes them.

| | Mismatch or open question | Java | Model | Proposed resolution | Stage, WP, status |
|---|---|---|---|---|---|
| M20 | With eviction, the writer cannot find lv(y) for a dead pointer without a table of all nodes (reference-theory.md, 5.1; `lean/References/SISCase.lean`). Today it finds y's canonical object by id in the node table, which holds every node (M26) | `NodeCollection.resolvePointers` (292), lines 317 to 333; `Cache3.getNode` (198) | `mkVersion` (`S.lv`) | Option K: A6 and INV-SLOT, references from slots and the pinned set (plan, 8.5); fallback Option F (K1) | 2: A4, E1 to E6; K1; o |
| M21 | `resolvePointers` may take a newer snapshot from the node table (`usable`: canonical, or `getSpos() >= ref`), so the reference written can depend on what readers left in the table (level4-plan.md, 2.1, second case). Confirmed: lines 324 to 330. Readers include the writer's own warm-up reads (2.5) | `NodeCollection.resolvePointers` (292) | — | Code: resolve by id against the pinned set, Rule R and, if E1 adopts it, the window only; INV-SLOT says the result is lv(y) | 2, 3: E1, R8; o |
| M22 | A runtime first touch of a key node version in the startup section is cut back to the startup time (line 228; level4-plan.md, 2.1, first case). Not reachable today: every index node with a version in the section has a canonical object from startup on (`registerSectionNodes` for the nodes of R(s), the rerun's `nodeCreated` for the others), so step 3 of `followStreamPointer` finds it. Reachable once canonical objects can be released | `NodeCollection.followStreamPointer` (184), lines 228 to 231; `KeyNode.toPreviousState` (893) | — | Code: cut back only during reconstruction (startup), never at runtime | 3: R8; o |
| M23 | A memory slot keeps access data in its position field, so the slot's position is lost while the slot is a memory slot (`setPointer(i, node, accessData)` at every swizzle) | `KeyNode.pos` (field, line 72), `setPointerAccessData` (240); `TopNode.pointersPos`, `rootPointerPos` (lines 18, 28), `setPointerAccessData` (303); `NodeCollection.followStreamPointer`, line 240; `AccessData` | — | Code: unswizzling writes the target's position; the access clock kept apart from the position, or updated only under the slot's lock with a recheck | 3, 4: R8, J1; o |
| M24 | Readers of a slot's pair assume that a memory slot stays one: `KeyNode.getPointer` reads the object, then `pos[index]` separately, without the lock; `TopNode.getPointer` tests the object and reads it again; `TopNode.setPointerAccessData` and `getPointerAccessData` assert a memory slot. The comments say so ("Level 4 (eviction) must revisit this") | `KeyNode.getPointer` (202), `TopNode.getPointer` (252), `TopNode.setPointerAccessData` (303) | — | Code: capture the slot once; defined behavior for an evicted slot (level4-plan.md, 4.5.1) | 3, 4: R8, J5; o |
| M25 | `Cache3`'s reference counts are unbalanced: `pointerCreated` is called on swizzles, canonicalization, resolution and Dag pointer creation; `pointerDestroyed` has no caller | `Cache3.pointerCreated` (90), `pointerDestroyed` (180); callers `NodeCollection` lines 239, 258, 329, `Db` line 697 | — | Not used for eviction: the registry and the sweep instead (Q9) | 4: J1; o |
| M26 | `Cache3` keeps every index node ever read or made, canonical objects and the newest snapshots, for readers and the writer; nothing leaves it | `Cache3.register` (115), `getNode` (198); `NodeCollection.followStreamPointer`, line 233 | — (P is logical) | Physical layer: the table holds resident objects only; the writer needs only the pinned ones (T-INDEX) | 2, 4: E1, J1, J3; o |
| M27 | A first touch swizzles a slot to an object that may be newer than the slot's reference: the version after Rule R, the table's canonical object, or a table snapshot at least as new (`usable`). With a memory slot to a newer snapshot, the slot's serialized reference changes too (2.2) | `NodeCollection.followStreamPointer` (184), lines 202 to 241 | — | Model: allowed by lemma M (stage 1). Level 4 loader: the canonical object, or the exact version the slot names after Rule R (Q7) | 1, 2, 3: L1, E1, R8; o |
| M28 | Reclaim's scan reads through the readers' path at the old time tStart, and then reads each KV again at the latest time: both swizzle and register what they read (historical snapshots included) | `Reclaim.step` (345): `db.getMany`, line 368, with `Db.newGetMany`'s readers' follower; `db.getOne`, lines 380 and 382 | — | Code: maintenance reads, without admission or swizzling; the value's position from the slot where it suffices (level4-plan.md, 5.1, point 3) | 3, 4: R8, J6; o |
| M29 | Top node skip slots cache the target's time (`pointersTime`); the trace does not export it, so the checker cannot see a wrong cached time (F1-008-13, 5) | `TopNode.pointersTime` (line 20); `StoredTopNode.toLongs` (160) writes it, `parse` (54) reads it; `java/stress/TraceExport.java`, `topEntries` (line 290) | entries `skip` | Trace: SKIPT lines (plan, 8.2); checker: equal to the target's time; kept on unswizzling | 1, 4: L5, J3; o |
| M30 | Top node ordinals of 32,768 and more are written wrong: `node.topNodeId << (2 * 8)` shifts an `int` before it is widened (F1-008-13, 5.1). Confirmed at line 176. The stored ordinal is the low 16 bits, read as a signed number: with bit 15 set the parser refuses it; otherwise, from 65,536 on, it is accepted silently as the ordinal modulo 65,536 with the wrong height, and a restart loses history and goes on with wrong ordinals (review-13-claude, 2). `parse` (54) checks neither the slot count against the ordinal (line 77 against 130 to 145) nor which slots are populated | `StoredTopNode.toLongs` (160), line 176; `StoredTopNode.parse` (54) | — | Code fix, two parser checks, a round-trip test and a restart test (A3, with review-13-claude, 7.1) | A3 done, `280525a`; c |
| M31 | One canonical object per node id must survive release and reload | `Cache3.makeCanonical` (137), `isBetter` (167); the `isCanonical` fields of `KeyNode` and `TopNode` | Phys: the node table | Model and code: release clears the table's entry and the flag; the writer's follower makes a reloaded node canonical | 2, 4: E1, J3; o |
| M39 | Eviction beside concurrent readers | `NodeCollection.followPointer` (93) takes the slot's lock (`PointerLocks`, 128 stripes) on every follow | — (sequential) | Java protocol (Q8) and its tests | 4: J5; o |
| M40 | Memory accounting is not implemented: `Cache3.totalSize` and `putSize` are set once and never advanced; access data is `-putSize`, the constant -10,000 | `Cache3` fields (lines 25, 26); `Db.getAccessData` (1605); `Cache3.setSizeIndicator`, called from the `Db` constructor (line 173), stores the budget and nothing reads it | — | Code | 4: J1, J7; o |
| M43 | Option K relies on A6 (no adoption) and TREE (one current parent), which the model does not assume today. A4: TREE holds on every transaction checked; A6 fails in 5 of 68,901 Java-tier transactions (an in-place split of a new segment root), and the weaker A6' holds in all (section 4). By the code: a split makes new nodes and the replaced node stops being current (`timeSplit`, `spaceSplit`), or changes in place a node of the same transaction (`timeSplitInPlace`, `spaceSplitInPlace`); a new top node's skip slots point to older top nodes, which are not current; no path moves a child from one current node to another | `Dag.handleFullNode` (780) and the splits (821, 841, 894, 955); `TopDs.newSuperRoot` (42) | `StepOK` | Checked on Java (A4: TREE, A6'); an assumption in the model, A6' or A6 (E1) | 2: A4 done, E1; o |
| M44 | After a restart, a node of D can hold a stream slot to a node of D that is written before it; today the node table gives the newer version, with eviction nothing does (plan, 8.5, the gap) | `DbStarter.canonicalNode` (451); `NodeCollection.resolvePointers` (292) | — | Model and code: the window (Rule R at runtime for the records after the previous startup pos), or startup resolving D's slots against D | 2, 3: E1, R8; o |
| M45 | **New (A2).** The public API's cache size is computed in `int`: `this.cacheSizeInMb * 1000000` overflows for more than 2,147 MB. The default is a fifth of the JVM's maximum heap, so it overflows with heaps above about 10.7 GB. With `-ea` the `Db` constructor then fails (`Cache3.setSizeIndicator` asserts a positive size); without it, the budget becomes 4 MB. No effect today, since nothing reads the budget (M40); J7 makes it the budget | `pubimp/DatabaseBuilderImp.start`, line 173; `Cache3.setSizeIndicator` (50) | — | Code fix (widen to `long`), with a test, before J7 relies on it | 4: J7; o |
| M46 | **New (A2, from review-13-claude, 3).** Top node ordinals are bounded by `MAX_TOP_NODE_ID_VALUE`, 2^30 − 1, over the database's whole life; reclaim bounds the stream but not the ordinals. With one hot key (about 15 transactions per top) that is about 186 days at 1,000 transactions per second. At the bound, `TopNode.height` throws from the constructor in `newSuperRoot`, in the middle of a root split, after the Dag has made the new root | `TopNode.height`, `MAX_TOP_NODE_ID_VALUE` (lines 105 to 125); `TopDs.newSuperRoot` (42) | `Spec.topLevel`, levels (level2-alignment.md, 8.4) | Frans: a wider ordinal (the header has 48 bits for it) or a clean refusal before the transaction changes anything. Not urgent | —; o |

Findings of A2, beyond the plan's list: M45, and M46 from review-13-claude; that reads occur in every run
through `Db.warmup` (2.5), which matters for M21 and M27; that
`TransNodes.clean` clears the dirty flags of the record being written
before it is appended (2.4); and the exact lines of M22's argument that the
runtime cut-back is not reachable today.


## 4. Probes

WP A4, 2026-10-16: does Java's Dag have the structure that Option K needs
(the plan, 8.5)? Two properties, for every transaction i:

* **A6, no adoption**: for every node x reachable at i, every pointee y of x,
  live or dead, that is not a live child of x at i is a data node or not
  reachable at i.
* **TREE, one current parent**: every node reachable at i, the root aside,
  is the live child at i of exactly one node reachable at i.

They are diagnostics, not assumptions yet (E1 decides): in the checker
(`adoptionFailures`, `treeFailures` in `lean/Check/Steps.lean`, computed
with the model's `reachList`, `pointees` and the instance's `live`, and
reported under "diagnostics"; a test trace, `adopt.trace`, fails both), and
in the Java tier (`java/stress/A2A3Check2.java`, a new line in its summary;
`-DdebugA6=1` prints each failure). The Java tier also counts a weaker form,
**A6'**: such a y is at least reachable at i from x, through live pointers.

| Set | Transactions | A6 | A6' | TREE |
|---|---|---|---|---|
| Lean tier, small (`conformance.sh small`, 50 traces) | 3,700 | 0 | — | 0 |
| Lean tier, medium (`conformance.sh medium`, 9 traces) | 3,360 | 0 | — | 0 |
| Java tier, the 21 configurations of level2-alignment.md, 10.5 | 68,901 | fails in 5 | 0 | 0 |

The traces are those of A1's run of `level2.sh` (small) and of F1-008-11's
campaign on `d5c56dd` (medium; production code and exporter unchanged since),
checked by the checker with A4's diagnostics and C2's fast versions, which
compute the same as the model's definitions (proven; 31 s for the medium set).

**A6 fails, A6' holds.** The five failures are in two configurations, both
at node size 8 with two-segment keys and deletes: `-Dmaxnode=8 -Dkeys=1000
-Dn=50 -Dexact=1 -Dops=40 -Ddel=25 -Dlong=1 -Dseeds=10` (seed 4, T2: one
transaction) and `-Dmaxnode=8 -Dkeys=500 -Dn=2000 -Dops=10 -Ddel=20
-Dlong=1 -Dseeds=3` (seed 2, T26 to T29: one dead pointer, seen in four
transactions). Each time a segment leaf has a dead pointer to a node that
the same transaction created, and that is still below the segment leaf: the
transaction created the root of the next key segment's tree and then split it
in place (`Dag.spaceSplitInPlace` with a segment leaf as the parent, D1 of
F1-008-11). The parent gets a new klong for the same compare value, to the
new root above the split node, and its earlier klong of the same transaction,
to the split node, becomes dead; the split node is now the new root's child.
So the adopter is a node below the old parent, and A6' holds in every
transaction checked.

What it means for Option K (for E1): the argument for a dead slot (the
plan, 8.5) needs that a current node with a dead pointer to y is rewritten
after every later write of y. With A6', y stays below x: every change below
y is marked through x, and D is closed upward, so x is in D whenever y is,
as in the argument for live slots. E1 must decide whether A6' is the
assumption, and check it in the model.


## 5. The design

WP E1.


## 6. What Java must do

WP E7.
