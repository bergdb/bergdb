# BergDB Level 4: the Java code and the Lean model

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, from 2026-10-16.
Work package A2 and later of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)).
Source commit `75d3c2d`; line numbers below are at that commit, in
`java/src/bergdb/`.

Status, 2026-10-17: the scope (section 1), a first α for the cache (section
2) and the register (section 3), checked against the code (A2); the probes
of A4 and the A-COPY checks (section 4); the design of E1, and what E2 to
E6 ran and proved (section 5); what Java must do (E7, section 6). To come:
the outcome (F2).

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
| M20 | With eviction, the writer cannot find lv(y) for a dead pointer without a table of all nodes (reference-theory.md, 5.1; `lean/References/SISCase.lean`). Today it finds y's canonical object by id in the node table, which holds every node (M26) | `NodeCollection.resolvePointers` (292), lines 317 to 333; `Cache3.getNode` (198) | `mkVersion` (`S.lv`) | Option K: A6 and INV-SLOT, references from slots and the pinned set (plan, 8.5); fallback Option F (K1) | 2: A4, E1 (designed: 5.4), E2 (run), E3 (proved without restarts: `TC_records`, 5.11), E4 (`TR_view`, 5.12), E5 (with restarts: `T2_cache`, 5.13), E6 (`TP_pins`, T-INDEX: 5.14); K1; o |
| M21 | `resolvePointers` may take a newer snapshot from the node table (`usable`: canonical, or `getSpos() >= ref`), so the reference written can depend on what readers left in the table (level4-plan.md, 2.1, second case). Confirmed: lines 324 to 330. Readers include the writer's own warm-up reads (2.5) | `NodeCollection.resolvePointers` (292) | — | Code: resolve by id against the pinned set, Rule R and the slot; no window (E1, 5.2 and 5.4); INV-SLOT says the result is lv(y) | 2, 3: E1 (designed), E3 (the model's writer proved, 5.11), R8; o |
| M22 | A runtime first touch of a key node version in the startup section is cut back to the startup time (line 228; level4-plan.md, 2.1, first case). Not reachable today: every index node with a version in the section has a canonical object from startup on (`registerSectionNodes` for the nodes of R(s), the rerun's `nodeCreated` for the others), so step 3 of `followStreamPointer` finds it. Reachable once canonical objects can be released | `NodeCollection.followStreamPointer` (184), lines 228 to 231; `KeyNode.toPreviousState` (893) | — | Code: cut back only during reconstruction (startup), never at runtime (E1, 5.2: the Level 4 loader) | 3: E1 (designed), R8; o |
| M23 | A memory slot keeps access data in its position field, so the slot's position is lost while the slot is a memory slot (`setPointer(i, node, accessData)` at every swizzle) | `KeyNode.pos` (field, line 72), `setPointerAccessData` (240); `TopNode.pointersPos`, `rootPointerPos` (lines 18, 28), `setPointerAccessData` (303); `NodeCollection.followStreamPointer`, line 240; `AccessData` | — | Code: unswizzling writes the target's position; the access clock kept apart from the position, or updated only under the slot's lock with a recheck | 3, 4: R8, J1; o |
| M24 | Readers of a slot's pair assume that a memory slot stays one: `KeyNode.getPointer` reads the object, then `pos[index]` separately, without the lock; `TopNode.getPointer` tests the object and reads it again; `TopNode.setPointerAccessData` and `getPointerAccessData` assert a memory slot. The comments say so ("Level 4 (eviction) must revisit this") | `KeyNode.getPointer` (202), `TopNode.getPointer` (252), `TopNode.setPointerAccessData` (303) | — | Code: capture the slot once; defined behavior for an evicted slot (level4-plan.md, 4.5.1) | 3, 4: R8, J5; o |
| M25 | `Cache3`'s reference counts are unbalanced: `pointerCreated` is called on swizzles, canonicalization, resolution and Dag pointer creation; `pointerDestroyed` has no caller | `Cache3.pointerCreated` (90), `pointerDestroyed` (180); callers `NodeCollection` lines 239, 258, 329, `Db` line 697 | — | Not used for eviction: the registry and the sweep instead (Q9) | 4: J1; o |
| M26 | `Cache3` keeps every index node ever read or made, canonical objects and the newest snapshots, for readers and the writer; nothing leaves it | `Cache3.register` (115), `getNode` (198); `NodeCollection.followStreamPointer`, line 233 | — (P is logical) | Physical layer: the table holds resident objects only; the writer needs only the pinned ones (T-INDEX) | 2, 4: E1, E6 (T-INDEX by the definitions, 5.14: the model's table holds resident objects only), J1, J3; o |
| M27 | A first touch swizzles a slot to an object that may be newer than the slot's reference: the version after Rule R, the table's canonical object, or a table snapshot at least as new (`usable`). With a memory slot to a newer snapshot, the slot's serialized reference changes too (2.2) | `NodeCollection.followStreamPointer` (184), lines 202 to 241 | — | Model: allowed by lemma M (stage 1). Level 4 loader: the canonical object, or the exact version the slot names after Rule R (Q7; E1, 5.2) | 1, 2, 3: L1, E1 (designed), R8; o |
| M28 | Reclaim's scan reads through the readers' path at the old time tStart, and then reads each KV again at the latest time: both swizzle and register what they read (historical snapshots included) | `Reclaim.step` (345): `db.getMany`, line 368, with `Db.newGetMany`'s readers' follower; `db.getOne`, lines 380 and 382 | — | Code: maintenance reads, without admission or swizzling; the value's position from the slot where it suffices (level4-plan.md, 5.1, point 3) | 3, 4: R8, J6; o |
| M29 | Top node skip slots cache the target's time (`pointersTime`); the trace does not export it, so the checker cannot see a wrong cached time (F1-008-13, 5) | `TopNode.pointersTime` (line 20); `StoredTopNode.toLongs` (160) writes it, `parse` (54) reads it; `java/stress/TraceExport.java`, `topEntries` (line 290) | entries `skip` | Trace: SKIPT lines (plan, 8.2); checker: equal to the target's time; kept on unswizzling | 1, 4: L5 done (SKIPT lines; C-S checks every cached time and the slot layout, level2-alignment.md 13.5), J3 (kept on unswizzling); o |
| M30 | Top node ordinals of 32,768 and more are written wrong: `node.topNodeId << (2 * 8)` shifts an `int` before it is widened (F1-008-13, 5.1). Confirmed at line 176. The stored ordinal is the low 16 bits, read as a signed number: with bit 15 set the parser refuses it; otherwise, from 65,536 on, it is accepted silently as the ordinal modulo 65,536 with the wrong height, and a restart loses history and goes on with wrong ordinals (review-13-claude, 2). `parse` (54) checks neither the slot count against the ordinal (line 77 against 130 to 145) nor which slots are populated | `StoredTopNode.toLongs` (160), line 176; `StoredTopNode.parse` (54) | — | Code fix, two parser checks, a round-trip test and a restart test (A3, with review-13-claude, 7.1) | A3 done, `280525a`; c |
| M31 | One canonical object per node id must survive release and reload | `Cache3.makeCanonical` (137), `isBetter` (167); the `isCanonical` fields of `KeyNode` and `TopNode` | Phys: the node table | Model and code: release clears the table's entry and the flag; the writer's follower makes a reloaded node canonical (E1, 5.2) | 2, 4: E1 (designed), E3 (INV-CAN proved, 5.11), J3; o |
| M39 | Eviction beside concurrent readers | `NodeCollection.followPointer` (93) takes the slot's lock (`PointerLocks`, 128 stripes) on every follow | — (sequential) | Java protocol (Q8) and its tests | 4: J5; o |
| M40 | Memory accounting is not implemented: `Cache3.totalSize` and `putSize` are set once and never advanced; access data is `-putSize`, the constant -10,000 | `Cache3` fields (lines 25, 26); `Db.getAccessData` (1605); `Cache3.setSizeIndicator`, called from the `Db` constructor (line 173), stores the budget and nothing reads it | — | Code | 4: J1, J7; o |
| M43 | Option K relies on A6 (no adoption) and TREE (one current parent), which the model does not assume today. A4: TREE holds on every transaction checked; A6 fails in 5 of 68,901 Java-tier transactions (an in-place split of a new segment root), and the weaker A6' holds in all (section 4). By the code: a split makes new nodes and the replaced node stops being current (`timeSplit`, `spaceSplit`), or changes in place a node of the same transaction (`timeSplitInPlace`, `spaceSplitInPlace`); a new top node's skip slots point to older top nodes, which are not current; no path moves a child from one current node to another | `Dag.handleFullNode` (780) and the splits (821, 841, 894, 955); `TopDs.newSuperRoot` (42) | `StepOK` | Checked on Java (A4: TREE, A6'); E1: the model assumes TREE and A6' (not A6), in `EvictStep` (5.5); E3: also A-COPY for a transaction's new pointers (`CopyStep`, 5.10); E3's proof uses all three (5.11) | 2: A4 done, E1 done (A6'), E2 checked TREE, A6' and A-COPY by running, E3 proved T-CACHE from them; A-COPY checked on Java (section 4: no failure); o |
| M44 | After a restart, a node of D can hold a stream slot to a node of D that is written before it; today the node table gives the newer version, with eviction nothing does (plan, 8.5, the gap) | `DbStarter.canonicalNode` (451); `NodeCollection.resolvePointers` (292) | — | Model and code: E1 chose startup linking by id (rule 4, 5.4), which gives today's records; E5 extended it to the root's object, which Java's `TopDs` holds by reference already (5.13); the window is the fallback | 2, 3: E1 (designed), E5 (proved with restarts: `T2_cache`, 5.13), R8; o |
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

**A-COPY** (2026-10-17, after E3). The assumption that E3 added (5.10,
`CopyStep`): every pointer of a new entry of transaction i names a node that
i creates, a node of the writer's paths (the nodes reachable at i − 1 with a
node below them, themselves included, that i changes or that is not
reachable at i), or a pointee, live or dead, of one (of a virtual root: a
live child at i − 1). Checked as A6 is: a diagnostic in the checker
(`copyFailures` in `lean/Check/Steps.lean`, with the model's `pointees` and
`live`, the paths computed lowest level first; a test trace, `copy.trace`,
fails it), and in the Java tier (`A2A3Check2`, a new summary line, which
also counts the pointers that need the second clause: a pointee of a node of
the paths that is not on them itself).

| Set | Transactions | New pointers | Of them to a pointee of the paths, not a node of them | A-COPY fails |
|---|---|---|---|---|
| Lean tier, small (60 traces) | 6,760 | — | — | 0 |
| Lean tier, medium (9 traces) | 3,369 | — | — | 0 |
| Java tier, the 21 configurations of level2-alignment.md, 10.5 | 68,901 | 487,786 | 453,197 | 0 |

The traces are those of L5's runs in `java/build/traces/` (the production
code that made them is today's); the large set of C3 (12 traces) was still
being checked when this was written. The Java tier's counts are in
[evidence/level4-acopy.txt](evidence/level4-acopy.txt). Most new pointers
are of the second kind: a split copies the split node's pointers to its
children, which are below the paths, not on them.


## 5. The design

WP E1, 2026-10-16, for E2 to E6. The design of the Level 4 model, as far as
the evidence allows before the executable model (E2) and the proofs (E3 to
E6). It extends the physical layer of stage 1 (`lean/SIS/Phys.lean`, WP L1;
level2-alignment.md, 13.1) with eviction, and settles the reference rule
(Q3: Option K). Section 5.9 says what is not settled.

### 5.1 In short

* **Option K, kept.** Every version still names the latest version of every
  pointee, lv(y), live or dead (`mkVersion`), as today; records, format and
  existing databases do not change. The physical writer computes lv(y) from
  three things only: the slots of the objects it writes, the pinned objects
  by node id, and Rule R's section map. No map from every node id, and no
  runtime window (8.5 of the plan offered one; 5.4 shows that two rules make
  it unnecessary).
* **The invariant INV-SLOT** (5.4): a slot of a resident canonical object of
  a node that is current or in D serializes lv(y), unless y is pinned. Four
  rules keep it, besides those of stage 1: (1) the loader takes the canonical
  object or the exact version the slot names after Rule R, never a snapshot
  from the node table, and never cuts back after startup (Q7); (2) a new
  pointer to a node with a resident canonical object is a memory slot to it;
  (3) a memory slot is unswizzled only when its target is clean, unpinned and
  written, and becomes a stream slot naming the target's position; (4) after
  startup, every stream slot of an object of D's nodes (and, since E5, of
  the root's object; 5.13) that names a node with a canonical object becomes
  a memory slot to it.
* **Assumptions**: TREE (one current parent) and **A6'** (no adoption, the
  weaker form that A4 found to hold on Java where A6 fails in 5 of 68,901
  transactions), per transaction, in a structure of their own beside
  `PhysStep`; D closed upward, which the model must prove (F1-008-08's T15),
  not assume.
* **Java's changes** (5.7): the loader and resolution rules of Q7 and M21,
  M22, M27; unswizzling that writes the target's position (M23); the startup
  linking (rule 4, M44); release that clears the table entry and the
  canonical flag (M31); pins, the registry and the sweep (M25, M26, M40);
  and a check that Java's copies of slots already meet rule 2.

### 5.2 The physical layer, part 2: state and operations

State, beside the logical ⟨P, D, S⟩, as in stage 1 (`Mem`: objects with
node, history, canonical flag, position and slots; the node table; Rule R's
startup pos; the root's object). Part 2 adds no field; it adds operations
and a policy for the loader.

* **The pinned set** Π, a function of the state at a transaction boundary:
  the canonical objects of the nodes of D, and the root's object (a virtual
  root's object is rebuilt at every startup and never written). Java pins
  more, which the model treats as atomic (5.8): the record being written
  (`TransNodes`, from `TransSeq.take` to `NodeStream.appendNodes`), the
  objects of an operation in progress, and the super root `TopDs.superRoot`,
  which the model's root object stands for.
* **Eligible** object h (for release): h is not in Π (so a canonical h is of
  a node not in D, and holds exactly its latest version, by INV-CAN; a
  snapshot holds the version at its position, by INV-SNAP); it has a position
  (written: `pos = some r`); and no resident object has a memory slot to h.
* **Unswizzle** (hp, y): the slot of object hp for pointee y is a memory slot
  to h, and h is eligible but for incoming memory slots. The slot becomes a
  stream slot naming h's position. Its serialized reference
  (`Pointer.getSposForStream`: a memory slot gives the target's position, a
  stream slot its own) does not change. hp may be any object, pinned or not.
* **Release** (h): h is eligible. The object goes; the node table's entry
  goes if it names h. (Java also clears h's canonical flag, M31, since a
  reader may still hold h.)
* **Follow, Level 4** (the loader, Q7): a stream slot naming record r of node
  y. With r' = Rule R's record (`ruleRRef`, as stage 1): the node table's
  canonical object of y if there is one; otherwise the version at r'
  exactly, as a new snapshot, not cut back, not entered in the node table
  (the table names canonical objects only); the slot becomes a memory slot
  to it. A memory slot gives its object, as in stage 1. Stage 1's rule (also
  a snapshot from the table that is at least as new, and the cut-back of a
  key node version of the section) stays for Java as it is today; Level 4
  replaces it (M21, M22, M27).
* **The writer's follow** (promotion), as stage 1: the object reached, or the
  table's canonical object if there is one, becomes canonical and the
  table's, and the slot names it. Stage 1 also picked "the newer of the
  object reached and the table's object"; with the table holding canonical
  objects only, that case is gone. CC (`CC_canonical`) must hold again: the
  object promoted holds its node's whole history; INV-SLOT gives it (a live
  slot of a current canonical object on the writer's path names lv(y), or y
  is pinned and has a canonical object).
* **A change** (`applyChange`), as stage 1, with rule 2 for new pointers:
  a memory slot to the pointee's canonical object if there is one (stage 1's
  `newSlot` does this already, as its first case); else a copy of the slot
  of a node the writer reached (a split copies its node's pointers), and so
  on as in stage 1.
* **The physical writer** (steps 6 and 7, new): for each taken node x, in
  the model's order (lowest level first), the version from x's canonical
  object (pinned): its history, and for each pointee y the reference that
  `resolvePointers` gives at Level 4: if y is pinned, its canonical object's
  position (a version written earlier in the same record included, which the
  object then names); otherwise the slot's serialized reference, a stream
  slot's after Rule R. The object then names the record. Rule A tests the
  written nodes lowest level first: x goes back into D if a pointee of it,
  live or dead, is pinned (by node id, against Π as it grows); that is the
  model's `javaTest`, and Java's `hasDirtyChild` after `resolvePointers`
  made a memory slot to every pinned pointee (level2-alignment.md, 7.1).
* **Startup**, as stage 1 (`lazyStartup`), with rule 4 at the end: each
  stream slot of a pinned object (a canonical object of a node of D, or the
  root's object, since E5: 5.13) that names a node with a canonical object
  becomes a memory slot to it (Java's `createMemoryPointers` links by exact
  position; rule 4 links by id).
  Reconstruction keeps its cut-back to the startup time (`canonOfVersion`);
  only runtime loads lose it.
* **Reads**, as stage 1 (`Mem.readAt`), through the Level 4 loader.

A **cache schedule** is any sequence of reads (at times up to the last
record), unswizzles and releases between transactions. The writer's own
follows come with its transactions (`lazyTrans`).

### 5.3 The invariants

* **INV-CAN.** At most one canonical object per node, and the node table
  names it. A canonical object holds its node's whole history in P (CC).
  Every node of D has one, resident. A canonical object of a node not in D,
  with a position, holds exactly its latest version: its history is lv's
  history and its position is lv's record.
* **INV-SNAP.** Every other object is the version of S at its position,
  exactly (the Level 4 loader). Stage 1's loader also made versions cut back
  to the startup time; the Level 4 loader does not, and reconstruction makes
  canonical objects only.
* **INV-SLOT** (the plan's 8.5, made precise in 5.4).
* **No dangling slot.** A memory slot names a resident object (release
  needs no incoming memory slot).

### 5.4 The reference rule: why Option K holds

**INV-SLOT.** For every resident canonical object x of a node that is current
at the last time or in D, and every pointee y of x's history, live or dead:
the slot's serialized reference is lv(y), or y is pinned. Moreover, when y is
pinned and x's slot for y is not a memory slot to y's canonical object, x is
in D and is written no later than y: in an earlier record, or in the same
record after y.

The second half is what makes unpinning safe: when y is written and leaves
D, every slot that matters for y is a memory slot to y's canonical object,
which then serializes y's new position, or belongs to an object written
after y in that record. Slots of objects that are neither current nor in D
do not matter for records (step 3 marks only current nodes, and Rule A puts
back only taken ones, so such an object is never written again); for reads,
their versions are good for the times their parents use them (LM, T1-L).

lv(y) moves only when y is written, and y is written only from D. So the
check is, for each way a slot changes and for each kind of slot, that the
invariant survives, and that it survives every write. The table goes through
them; "pinned" means that y is in D.

| Event | Effect on the slot of x for y | Why INV-SLOT survives |
|---|---|---|
| Load (first touch), Level 4 loader | stream → memory slot to y's canonical object, or to the snapshot of the version the slot names after Rule R | The serialized reference stays, or moves to the canonical object's position, which is lv(y) (INV-CAN) or y is pinned. Stage 1's newer table snapshot (M21, M27) and the runtime cut-back (M22) are gone |
| The writer's follow | memory slot to a snapshot → to y's canonical object | Moves to lv(y) (INV-CAN) |
| A new pointer (a change, a split's copy, a new super root's skip slots, `TopDs.newSuperRoot`) | memory slot to y's canonical object if there is one (rule 2); else a copy of a slot of a node the writer reached | A copy has the serialized reference of its source, which is lv(y) by INV-SLOT for the source (a current node the writer reached); if y has a canonical object the copy is a memory slot to it, so the second half holds |
| Resolution at x's write | to pinned pointees: memory slots to their canonical objects; others: Rule R | After the write, the second half holds for every pinned y; x's new version names lv(y) for the others by INV-SLOT |
| Unswizzle | memory slot to h → stream slot naming h's position | Only for h clean, unpinned and written: the serialized reference stays, and is lv(y) (INV-CAN) or the snapshot's version, which the slot already named |
| Release | none (no incoming memory slots) | — |
| Startup | D's objects come from the stream: stream slots with their versions' references, Rule R applied; then rule 4 | Without rule 4, the plan's gap of 8.5 (M44): x and y in D, d(y) < d(x), x's slot naming y's version of that time; y is taken first, written, clean and evicted; x is then written naming an older version than lv(y). Rule 4 makes x's slot a memory slot to y's canonical object, so the second half holds, and y cannot be released before x's slot is unswizzled to y's new position. For y not in D: y's latest version is in the section if it came after x's (5.4, case 5), so Rule R gives it |
| A write of y (lv(y) moves) | — | By the second half: every slot that matters is a memory slot to y's canonical object, or its object is written after y in the same record |

The second half for each kind of slot, when y becomes pinned (enters D):

1. **A live slot of a current node x.** By TREE, x is y's only current
   parent. y enters D by marking: the writer's path goes through x's slot,
   and the writer's follow makes it a memory slot to y's canonical object.
   Or by Rule A, after a write of y while in D: the slot was a memory slot
   already. Reclaim's touch also follows the writer's path (M17).
2. **A dead slot of a current node x, with y current.** By A6', y is below
   x through live pointers, so every change below y is marked through x, and
   D stays closed upward: x is in D whenever y is, and d(x) ≤ d(y) (x is in
   D already, or gets the same index). So x is taken no later than y: if in
   an earlier record, its write resolves the slot by id (y pinned) and Rule A
   puts x back with the index of that record, at or after d(y), so from then
   on x's slot is a memory slot and x is taken with y or after it; if in the
   same record, x is written after y (lower level first). This is the case of
   A4's five A6 failures: a segment leaf with a dead pointer to a node that
   the same transaction created and split in place, still below it.
3. **A dead slot of a current node x, with y not current** (a data node, or a
   node a split replaced, or one under a deleted key). A data node has one
   version. When y stops being current, it is clean, and then lv(y) never
   moves again: a node that is not current never enters D by marking, and
   Rule A puts back only taken nodes; or y is in D, and then x's slot to it,
   live until then, is a memory slot to y's canonical object (case 1), and x
   is in D too (closed upward). From then on Rule A couples them: x is
   written no later than y, or with it, and goes back into D whenever it is
   written while y is in D (y is a pointee of x). So x is in D whenever y
   is.
4. **A slot of a node x that is not current but in D** (a historical node
   still in D, the plan's third case of 8.5). If x shares a child y with its
   replacement, a change of y goes through the new parent, and x, already
   in D, has the smaller index: taken no later than y, it resolves the slot
   by id, or is written after y in the same record. If y was in D when x
   stopped being current, x's live slot to it was a memory slot already
   (case 1).
5. **After a restart.** For x and y both in D: rule 4. For x in D and y not:
   if y was written after x's latest version, y was in D then and x too
   (cases 2 to 4), with d(x) at or before that write; x was not taken by the
   last startup pos, so d(x) is after it, and so is y's write: in the
   startup section, where Rule R finds it. Otherwise x's version names lv(y).

**Checked by hand against the known counterexamples.**

* `lean/References/SISCase.lean` moves Y from P to Q, both current: P keeps a
  dead pointer to Y, which stays current under Q but not below P. A6 and A6'
  both exclude it (in Java, no path moves a child from one current node to
  another, M43).
* The two component cases of level4-plan.md, 2.1. The runtime reload that
  cuts a version back (four klongs become two): excluded by rule 1, no
  cut-back after startup (M22). The writer resolution that emits 200 with a
  newer snapshot in the table and 100 without: excluded by rule 1 and the
  writer's resolution, which never read a snapshot from the table (M21);
  and in a reachable state, INV-SLOT says that a slot of a canonical dirty
  parent serializes lv(y) or y is pinned, so the two answers cannot differ.
* The restart gap of 8.5: rule 4 (above). The window of 8.5 would also close
  it, at the cost of a new runtime map; rule 4 needs none, and gives the
  records Java writes today, whose `resolvePointers` finds every canonical
  object by id in a table that never forgets (M26). It is the fallback if E2
  finds a case rule 4 misses.

**Found in this search, for E2 to test.** Java copies a slot as the pair it
is: a split's new nodes get the live klongs of the node it splits
(`KeyNode.lastVersionGivenDel`; `setContentFrom` copies a node of the same
transaction), and a new super root inherits the old one's skip slots,
a stream slot as a stream slot ("as after a restart", `TopDs.newSuperRoot`,
lines 77 to 90, at `a66e4d9`). A copied stream slot to a pinned node whose position moves
before the new node is written would be stale: the new node's index is
later than the pinned node's. Rule 2 excludes it in the model. In Java it
holds without a change, by the cases above: the live slots that key node
copies take are memory slots to their pinned children (case 1), and a
super root with a skip slot to an older top node in D is itself in D (case
3's coupling: it was made while that node was in D, and Rule A keeps it
there), so after a restart rule 4 has linked its slot. That is an argument,
to be checked: E2's example 5 should include a root split after a restart
while an older top node is in D, and the exporter should check rule 2 on
Java's physical states (C-P).

### 5.5 The assumptions, and where they go

* **TREE**: every node reachable at time i, the root aside, is the live child
  at i of exactly one node reachable at i.
* **A6'**: for every node x reachable at i and every pointee y of x that is
  not a live child of x at i: y is a data node, or not reachable at i, or
  reachable at i from x through live pointers.
* Both are properties of P per transaction, like `PhysStep`'s `liveNew` and
  `adopt` (L3), and go into a structure of their own in `SIS/Evict.lean`
  (`EvictStep`, with `EvictRunOK` over a run), not into `StepOK`: the
  Level 2 theorems do not need them, and keeping them apart keeps those
  statements as they are. The checker already computes them (`treeFailures`,
  `adoptionFailures`; A4); E2 adds A6' to the checker and to the random runs.
* **D closed upward** (every current ancestor of a node of D is in D): needed
  by cases 2 and 4. F1-008-08 proved it for BergDB's bookkeeping in its
  model (T15, from marking the access path and Rule A over all pointers);
  bergdb's model has both (`Algo.mark`, `javaTest`), and E3 proves it there.
* **A5** (no resurrection; `StepOK.noRes`): used as in stage 1.

### 5.6 The theorems of stage 2, in plain English

For runs that meet the Level 2 assumptions (`RunOK`), the physical layer's
(`PhysRunOK`) and TREE and A6' (`EvictRunOK`), with BergDB's bookkeeping
(marking, `javaTest`):

* **T-CACHE** (`TC_records`, E3). Whatever the cache schedule (any reads,
  unswizzles and releases between transactions), every transaction of the
  physical writer appends exactly the model's record R(i) and leaves the
  model's D; INV-CAN, INV-SNAP and INV-SLOT hold after every operation.
  Proved (E3, 2026-10-17) for runs from the startup from R(0) without
  restarts (5.11); restarts are T2-C's (5.13).
* **T-READ** (`TR_view`, E4). In every state reachable as above, a physical
  read at any time up to the last record gives P at that time: every node
  reached, with its content then. Proved (E4, 2026-10-17) for the runs of
  T-CACHE (5.12), and with restarts (E5, `TR_view_restarts`, 5.13).
* **T2-C** (`T2_cache`, E5). A run with restarts, lazy startups (with rule 4)
  and any cache schedules appends the same records as the logical run; after
  each startup the invariants hold again. Proved (E5, 2026-10-17; 5.13):
  after every transaction and its cache operations or its restart, the
  records and D are the run's, P has the run's nodes, and the invariants of
  T-CACHE hold for the stream of the last startup.
* **T-PIN** (`TP_pins`, E6). Every eligible object may be released at any
  transaction boundary (after its incoming memory slots are unswizzled), and
  the theorems above still hold: the pinned set is what must stay. Proved
  (E6, 2026-10-17; 5.14), for the runs of T2-C: every object outside the
  pinned set may be detached, and unswizzling its memory slots and then
  releasing it removes it.
* **T-INDEX** (E6, by the definitions). The physical writer reads only the
  slots of the objects it writes, the pinned set by node id, and Rule R's
  section map; never a map from every node id, and never what readers
  happened to leave in memory. Stated with the definitions it rests on in
  5.14 (E6, 2026-10-17).

### 5.7 What Java must change, and what it keeps

For R8 (before eviction, records unchanged, checked by the byte comparison
against `l34-base`) and the J WPs (eviction). E7's list, with the register
rows, the WPs and the checks, is section 6.

1. **The loader** (`NodeCollection.followStreamPointer`): the canonical
   object, or the exact version after Rule R; no snapshot from the table
   (M27), no cut-back after startup (M22). R8.
2. **`resolvePointers`**: by id against the pinned set (D's canonical
   objects, and the record being written), Rule R, and the slot; no snapshot
   from the table (M21). R8. With everything resident, it gives today's
   records: a canonical object of a node not in D holds its latest version.
3. **Copies of slots** (splits, `TopDs.newSuperRoot`): rule 2 should hold
   as Java copies today (5.4, "Found in this search"); check it with the
   exporter (C-P) on runs with root splits after restarts while older tops
   are in D, and change the copy only if the check fails. R8 or J3.
4. **Startup** (`DbStarter`): link D's objects by id (rule 4, M44), not only
   by exact position (`createMemoryPointers`). R8. Rule 4 also links the
   root's object (E5, 5.13), which asks nothing of Java: its virtual root's
   one slot, `TopDs.superRoot`, is a memory reference to the super root's
   canonical object.
5. **Unswizzle** writes the target's position into the slot, under the slot's
   lock, after rechecking that the target is clean, unpinned and written
   (M23, M24, Q8). The access clock moves out of the position field (M23,
   M40). J1, J2, J3.
6. **Release** clears the node table's entry if it names the object, and the
   canonical flag (M31); the registry of resident objects and the sweep
   replace `Cache3`'s reference counts (M25, M26). J1 to J3.
7. **Pins**: D (`TransSeq`), the record being written (`TransNodes`, whose
   dirty flags are cleared before it is appended, so "not dirty" is not
   "written"), the super root, and the objects of operations in progress.
   J1.
8. **Reclaim's reads** as maintenance reads (M28): stage 3 and J6.

Java keeps: the record format; Rule R's section map; `javaTest` (Rule A over
all pointers) and marking; TREE and A6' (properties of its Dag, checked by
A4's diagnostics); one canonical object per node; the readers' path.

### 5.8 What the model leaves out

Concurrency (Q8: eviction under the write lock at transaction boundaries,
each slot under its pointer lock; Java's protocol, J5); the record being
written and operations in progress (atomic in the model); the TopDs skip
list's search (the root's object stands for it, as in stage 1, so the skip
slots of rule 2 and 5.4 are checked on Java by the exporter, C-P, not in
the model); bytes, memory accounting and the capacity policy (J7); reclaim's
maintenance reads (stage 3).

### 5.9 Not settled by E1

* Whether rule 2 needs a Java change: 5.4 argues that it does not (item 3 of
  5.7 is then a check only); E2's random runs and the exporter decide.
* Case 4 of 5.4 rests on "x, already in D, has the smaller index" for a
  historical node sharing a child; E2's example 5 and the random runs test
  it; E3 proves it or finds the missing condition.
* A6' is checked on Java (A4: 0 failures in 68,901 transactions) and on the
  model's examples by running; it is an assumption, not a theorem. So is
  A-COPY (5.10), which E3 added; it holds on every Java run checked (section
  4).
* The window (8.5) stays the fallback for rule 4.

### 5.10 E2: the model, run, and what E3 changed in it

`lean/SIS/Evict.lean` is 5.2 as a Lean model (WP E2, 2026-10-16 and 17), and
`lean/SIS/EvictExample.lean` runs it: examples 2 and 3, and a new example 5
(example 3 with drops: a leaf replaced by an empty one, so that a subtree
goes cold), each with restarts and four cache schedules (none; every object
that may be detached, after every transaction; each such object with
probability 0.3; and unswizzles and releases apart, so that objects stay in
memory with some of their slots unswizzled). After every transaction the
records and D are the model's, reads at three times give P, and INV-CAN,
INV-SNAP and INV-SLOT hold (`checkEvict`). `lake exe phystest 20 40 evict`:
20 seeds of 40 transactions on every example and schedule, 25,600
transactions, none fails. Rule 4 is needed: without it (the startup links
nothing by id) example 3 writes a wrong record after a restart (seed 8),
the gap of the plan's 8.5. The plan's example 5 also asked for two root
changes in one transaction; the model's assumptions exclude it (every node
a transaction creates or changes is reachable after it), and Java splits a
node of the same transaction in place (F1-008-11's D1), so example 5 has one
root split a transaction.

While proving T-CACHE (E3) three things of 5.2 changed; each was checked by
running before a proof relied on it, and the runs above are of the model as
it is now.

1. **The writer's walk follows every slot of its paths**
   (`Mem.reachOnPath4`). Stage 1's walk skips a node that has a canonical
   object already. With eviction the parent's slot for such a node can be a
   stream slot (unswizzled while the node was clean) or name another object
   of it; if the node then gets dirty, the live slot of its current parent is
   not a memory slot to its canonical object, which reads at the last time
   and INV-SLOT's second half rely on. The old walk kept that only through a
   further invariant (no live slot of a current canonical object names a
   snapshot of a node that has a canonical object), which held in the runs
   but rests on how objects can come back into the writer's reach; the new
   walk makes it direct. Java's writer walks from the root and follows every
   pointer on its paths (`NodeCollection.WriterFollower.followPointer`, lines
   161 to 191 at `e5b643b`), so the model now does what Java does.
2. **A new pointer's slot comes only from what the writer has in hand**
   (`Mem.newSlot4`, `Mem.applyChange4`): a memory slot to the pointee's
   canonical object; else a copy of the slot of a canonical object of a node
   that was reachable before the change and has the pointee in its history
   (live there, for a virtual root, whose dead slots go stale since it is
   never written); else the object's own slot. Stage 1's last resort, a copy
   of any canonical object's slot for the pointee, is gone: a canonical
   object of a node no longer current may hold a stale slot, which stage 1
   never wrote from but the physical writer does. This needs an assumption,
   **A-COPY** (`CopyStep`, in `EvictRunOK`): a pointer of a new entry names
   a node the transaction creates, a node of the writer's paths, or a
   pointee of a node of the paths (written, or a live child of a virtual
   root). Java's writer meets it by construction (a split copies the split
   node's pointers, `TopDs.newSuperRoot` the old super root's skip
   pointers); the examples meet it (`copyB`); and both tiers of the Java
   checks find it in every transaction checked, as A4 found TREE and A6'
   (section 4, 2026-10-17).
3. **A fourth cache schedule**, unswizzles and releases apart: the three of
   E2's plan always release an object right after unswizzling every slot to
   it, so an object with some slots unswizzled was never tested.

The invariant of E3's proofs (`EInv` in `lean/SIS/Proof/EvictInv.lean`, with
E3) is 5.3 made precise, with one more part for the live slots of a current
canonical object (a virtual root's too): for a child in D, a memory slot to
its canonical object; otherwise one that serializes the child's latest
version. It held after every operation of the runs above, before the proofs.

### 5.11 E3: T-CACHE, proved

`TC_records` (`lean/SIS/PhysTheorems.lean`, WP E3, 2026-10-17) is T-CACHE for
runs without restarts. A run of BergDB's algorithm (`javaTest`, with marking)
that meets the assumptions (`RunOK`), those of the physical layer
(`PhysRunOK`) and those of stage 2 (`EvictRunOK`: TREE, A6' and A-COPY),
from the Level 4 startup from R(0), with any cache schedule (any reads,
unswizzles and releases after each transaction): after every transaction
and its cache operations the state is the model's (the physical writer has
appended exactly the model's records, and D is the model's), and the memory
meets INV-CAN (a canonical object is the node table's for its node, holds its
node's whole history, level and kind, and is at its node's latest position;
every node of D has one), INV-SNAP (every other object is exactly the version
at its position), no memory slot dangles, and INV-SLOT (a canonical object
of a written node that is current or in D has a slot for every pointee of
its history; writing it now would give every pointee its latest version; and
the second half of 5.4). Since the schedule is any, this holds after every
operation. Only Lean's standard axioms; the proofs are in
`lean/SIS/Proof/Evict*.lean` (about 6,600 lines).

The proof keeps one invariant, `EInv` (5.10), through every operation:

1. The logical facts (`EvLogic`, `evLogic_st`): D is closed upward
   (F1-008-08's T15, also stated alone, `T15_closed`), and a current node
   not in D has no pointee in D and its latest version names the latest
   version of each pointee, live or dead. Marking and `javaTest` give the
   first; A6' gives the second for dead pointees.
2. Cache operations: the Level 4 loader, reads, unswizzles and releases keep
   the invariant (`EInv.cacheOps`, `EInv.unswizzle`, `EInv.release`).
3. One transaction (`EInv.evictTrans_ok`): the writer's view, read through
   the loader, is P at the last time (`EInv.view4_ok`); the walk makes every
   node of the paths canonical, with memory slots along the paths
   (`EInv.reachPath4_ok`); the change keeps the invariant (TREE: a current
   node has one current parent, the node of the path; A-COPY: a new
   pointer's slot is copied from a node the walk reached;
   `EInv.applyChange4_ok`); the two loops of writes give the model's
   versions (`AInv.loops_vs`: every pointee gets its latest version, from
   the pinned set or by INV-SLOT); and the memory after the record has the
   next state's invariant (`AInv.final_ok`: when a node is written and
   leaves D, INV-SLOT's second half makes the slots that matter memory slots
   to it, or slots of nodes written after it).
4. The startup from R(0) gives the invariant (`einv_init`): D is empty, and
   every slot names its pointee's latest version.

Not covered by E3: restarts (T2-C, E5; 5.13), reads at earlier times
(T-READ, E4; 5.12), and Java (the J WPs).

### 5.12 E4: T-READ, proved

`TR_view` (`lean/SIS/PhysTheorems.lean`, WP E4, 2026-10-17): in the runs of
5.11, after every transaction and its cache operations, a read through the
Level 4 loader at any time t up to the last record reaches exactly the nodes
reachable at t, each with its node at t. Only Lean's standard axioms; the
proofs are in `lean/SIS/Proof/EvictHist.lean`, `EvictHistTrans.lean` and
`EvictReadT.lean` (about 1,450 lines).

The writer's read at the last time is E3's (`EInv.view4_ok`). Earlier times
need more than INV-SLOT, which says nothing about the objects of nodes that
are neither current nor in D, nor about a virtual root's dead slots, and lets
a slot for a pinned pointee be stale. The proof keeps a second invariant,
`HInv`: for every canonical object, every time t at which its node is
reachable, and every live child at t, the slot is a memory slot to an object
a read at t may use (canonical, or the snapshot of a version good for t), or
a stream slot that names, after Rule R, a version good for t, or (INV-SLOT's
second half) a node of D, whose canonical object the loader finds by id.
Lemma M (a newer version is good whenever an older one is) and INV-2 (a
written node not in D is clean: its latest version is good at every time at
which it is reachable) give it at each change of a slot:

* a load swizzles to exactly the version the slot named, or to the canonical
  object;
* an unswizzle names the object's position: a clean node's latest version,
  or a snapshot's version;
* a new pointer's slot names the pointee's canonical object, or copies a slot
  that serializes a clean node's latest version;
* a write makes the slots for pinned pointees memory slots to their canonical
  objects;
* a snapshot that the writer promotes is a clean node's latest version, so
  good at every time at which the node is reachable;
* when a node leaves D, the slots that relied on INV-SLOT's second half were
  written away: their object's node was taken in the same record.

A snapshot's slots need no invariant: its version is good for t, so its
references are, and so is any newer version (lemma M). At the new time k + 1,
INV-SLOT's live part gives `HInv`. A probe checked `HInv` by running before
the proof (the E3 entry in the progress log). The read then goes as stage 1's
(T1-L): every object it reaches is canonical, or the snapshot of a version
good for t.

### 5.13 E5: T2-C, proved

`T2_cache` (`lean/SIS/PhysTheorems.lean`, WP E5, 2026-10-17) is T-CACHE with
restarts. In a run as in 5.11 (BergDB's algorithm with marking, the
assumptions, those of the physical layer and of stage 2, the Level 4 startup
from R(0), any cache schedule), now with restarts after any transactions
(`runEvict`: the logical startup for ⟨P, D, S⟩ and the Level 4 startup,
`evictStartup`, for the memory, both from the stream), after every
transaction and its cache operations or its restart:

* the stream and D are the run's without restarts, so restarts change no
  record; P has the run's nodes;
* the memory meets the invariants of 5.11 (INV-CAN, INV-SNAP, no dangling
  slot, INV-SLOT) for the startup it last made, from the run's stream after
  some earlier transaction k1, with Rule R of that stream's section. Right
  after a restart (k1 = j) they are the invariants of the startup's memory.

`TR_view_restarts` (the same file and WP) is T-READ for the same runs: a read
through the Level 4 loader, with Rule R from the stream of the last startup,
at any time up to the last record gives P at that time. With `TR_view`, T-READ
then holds in every state that a run with eviction reaches.

Only Lean's standard axioms; the proofs are in
`lean/SIS/Proof/EvictRerun.lean` and `EvictRestart.lean` (about 1,800
lines), with the lemmas of rule 4 in `EvictInit.lean`.

1. **The rerun** (`rinv_lazyStartup`). The startup from the stream after
   T(k) is stage 1's (`lazyStartup`): the objects of the section's start,
   then the rerun of the section's transactions, which keeps stage 1's
   invariant (`MemInv`, `lazy_ok`). It also keeps `RInv`: every object is
   canonical; every stream slot names, after Rule R of the section, its
   pointee's latest version at k; every memory slot names an object of its
   pointee; every object has a slot for each pointee of its history. A
   stream slot comes from a version: a version of the section names the
   latest version before it, which Rule R moves to the newest in the section;
   a latest version written before the section, of a node current and clean
   at the section's start, names latest versions already (`EvLogic`'s clean
   nodes). A new pointer of the rerun gets a memory slot to its pointee's
   canonical object, or a copy of a slot of a node that the rerun's writer
   reached (A-COPY). The node table has no repeated keys.
2. **Positions and rule 4** (`einv_hinv_startup`). The startup then gives each
   canonical object its node's newest record in the section as its position
   (`Mem.sectionPos`), or keeps the one it has (`RInv`: the latest record),
   and rule 4 links the pinned objects. Every node of D has a canonical
   object (it got dirty in the section, which the startup covers). The
   invariant of 5.11 then holds at k: INV-SLOT's first half by `RInv`; its
   second half because a slot of a relevant object to a node of D is a
   memory slot to the canonical object: the object is pinned (of a node of
   D, or the root's), or of a node current, written and not in D, which has
   no pointee in D (`EvLogic`). So for a current canonical object's live
   slot to a node of D: its object is in D (D is closed upward), or is the
   root's. And E4's invariant for reads at earlier times (`HInv`, 5.12)
   holds at k: a memory slot names a canonical object; a stream slot names
   its pointee's latest version, which is good at every time t at which the
   pointee is a live child: the pointee is clean (INV-2), or it is in D and
   then the slot's object is not pinned, so its node is clean too, and its
   latest version names a version of the pointee good for t, which lemma M
   carries to the latest.
3. **Transactions from the logical startup's state** (`evictTrans_congr`).
   After a restart the logical state is the logical startup's, with the
   run's stream and D and the run's nodes (T1, `T1_strong`), but not the
   run's structure as a term. The physical writer depends on P only through
   its nodes, as the logical step does (stage 1's T2, `step_congr`), so it
   appends the same record and leaves the same D and the same memory.
4. **The run** (`evictInvR_all`), by induction over the transactions with the
   last restart, as stage 1's T2-L (`LazyInv`), but without its frozen run:
   the invariants take the stream of the last startup as a parameter. E3's
   and E4's steps (`EInv.run_step`, `HInv.run_step`) carry them through each
   transaction and its cache operations; each restart starts them again.

**The model change: rule 4 links the root's object.** E1's rule 4 linked D's
objects only. The invariant needs every live slot to a node of D of a
current canonical object to be a memory slot to the canonical object (5.10:
the writer's walk and INV-SLOT's second half rely on it); rule 4 gives it
for D's objects. A virtual root is never written, so its object is not in
D, and its live slot to a super root in D is left to the startup's rerun.
The rerun leaves it a memory slot in every startup of E2's examples 3 and 5
(a probe: 0 stream slots among the 623 such slots of 656 startups), but a
proof of that would have to follow the virtual root's slots, whose dead ones
go stale, through the rerun. Since E5, rule 4 links the pinned objects, D's
canonical objects and the root's object (`Mem.linkD`, `lean/SIS/Evict.lean`;
the pinned set of 5.2), which gives it directly. Java needs nothing for it:
its virtual root's one slot, `TopDs.superRoot`, is a memory reference to the
super root's canonical object, set at startup (`DbStarter.prepareDb`, line
335: `new Dag(superRoot, ...)`, whose constructor makes the `TopDs`,
`Dag.java` line 48) and by `TopDs.newSuperRoot` (line 109), at `73320ec`.
It changes no record: a virtual root is never written, and a written root
with a pointee in D is in D itself. E2's runs with restarts pass with the
change (`phystest 20 40 evict`).

Not covered by E5: Java (the J WPs).

### 5.14 E6: T-PIN proved, T-INDEX by the definitions

`TP_pins` (`lean/SIS/PhysTheorems.lean`, WP E6, 2026-10-17): in the runs of
5.13 (any cache schedules, restarts after any transactions), after any
transaction and its cache operations or its restart, every object in memory
outside the pinned set (`Mem.pinned`: the canonical objects of the nodes of
D, and the root's object) may be evicted. It has been written, so it may be
detached (`Mem.detachable`); unswizzling each slot that is a memory slot to
it and then releasing it leaves it out of memory. The theorems of 5.11 to
5.13 hold for every cache schedule, so they hold whatever objects outside
the pinned set are evicted, in any order, at any transaction boundary. Only
Lean's standard axioms; the proofs are in `lean/SIS/Proof/EvictKeys.lean`
and `EvictPin.lean` (about 870 lines).

1. **Outside the pinned set, every object has been written**
   (`EInv.detachable_of_unpinned`). A snapshot is the version at its
   position (INV-SNAP). A canonical object outside the pinned set is of a
   node not in D and not the root (the root's object is pinned): a written
   node, so clean (INV-2), so it has a latest version, which is the
   object's position (INV-CAN).
2. **No object has two slots for the same pointee** (`SlotsND`,
   `slotsND_runEvict`), in every memory of every run, whatever its
   assumptions: an object is made with one slot per pointee of a history
   (`Obj.ofVersion`; the pointees have no repeats) or with none, and the
   operations change slots in place (`Obj.setSlot`) or add one for a pointee
   that has none (`Obj.putSlot`). So unswizzling the slot of each object, for
   each pointee, that is a memory slot to h (`Mem.slotsTo`) leaves no memory
   slot to h (`Mem.unswizzles_incoming`), and h may then be released
   (`Mem.evict_ok`).

Checked by running before the proof (a probe, scratch): in the runs of
examples 3 and 5 with the four cache schedules and restarts (4 seeds of 40
transactions each, 1,280 states), no object outside the pinned set lacks a
position, `evictObj` (`lean/SIS/EvictExample.lean`) removes every object that
may be detached, and no object repeats a pointee in its slots; 21,374
objects outside the pinned set were seen.

T-PIN does not say that the pinned set must stay: the model never allows a
pinned object's release (`Mem.eligible`), so the theorems say nothing of
one. E2's runs show what goes wrong without part of the design (without rule
4, a wrong record after a restart; 5.10). Java's pins beyond the model's (the
record being written, the objects of an operation in progress) are atomic in
the model (5.8).

**T-INDEX, by the definitions.** The physical writer computes each version
(`Mem.writeNode`) from its node's canonical object (a taken node, from D and
the nodes the transaction marks, which are pinned during the writes; or a
data node the transaction creates), and each reference (`Mem.refOf`) from:

* for a pointee in D (pinned), its canonical object by node id
  (`Mem.canonicalOf`, the node table) and that object's position;
* otherwise the object's slot for the pointee (`Obj.slot?`): a memory slot
  gives its object's position (`Obj.pos`); a stream slot its record after
  Rule R (`ruleRRef`), which reads only `newest S0 s y`, the newest version
  of y in the startup section R(s), ... of the stream of the last startup.

It reads no map from every node id. `Stream.lv`, the latest version of every
node, which the logical writer uses (`mkVersion`), appears in the physical
layer only as the last resort of the startup's `Mem.canonicalNode`, which the
runs of the theorems never reach (every node of gd(j) has a canonical object
when the rerun reaches it: `foldl_canonicalNode_noop`, stage 1). The other
memory reads of a transaction are the loader's (`Mem.follow4`: a memory
slot's object; else the node table's canonical object of the pointee; else
the record the slot names after Rule R, read by its position,
`Stream.versionAt`), the walk's (`Mem.reachOnPath4`), and a new pointer's
(`Mem.newSlot4`: the pointee's canonical object; else the slot for the
pointee of a resident canonical object of a node reachable before the change
that has the pointee in its history, `srcOK4`; else the object's own). The
node table
holds resident canonical objects only (`Mem.release` removes the entry), so
it is bounded by memory, not by the number of nodes; and the records do not
depend on which objects outside the pinned set are resident, or on what
readers left in memory, since T-CACHE and T2-C hold for every cache
schedule. The logical part of a transaction (the change, the paths, marking,
Rule A and the top: `pathOf`, `markOf`, `stillDirtyOf`, `topOf`) is the
model's step, which Java computes on its Dag and its D (`TransSeq`); it
decides which nodes are written, not what their versions name. E1 did not
adopt the window of 8.5, so there is no other map.


## 6. What Java must do

WP E7, 2026-10-17: the Java changes that the Level 4 design (E1, section 5)
and its proofs (E3 to E6, 5.11 to 5.14) ask for, each with its register row,
the WP that makes it and its check. Option K holds: no change to the record
format, to existing databases, to the public API or to a default (eviction
is on by default from J7 on, Q10). The model that Java must match is
`lean/SIS/Evict.lean`. Lines are at `e2e5bd5`, in `java/src/bergdb/`.

### 6.1 Before eviction (R8): every record stays the same

These change no record: with everything resident they give today's
references (5.7). R8 makes them one at a time.

| | Change | The model | Rows | WP | Check |
|---|---|---|---|---|---|
| 1 | `NodeCollection.resolvePointers` (317): a pointee in the pinned set (the canonical objects of D's nodes, and of the record being written) by node id, its canonical object's position; any other pointee from the slot: a memory slot's object's position, a stream slot's position after Rule R. No snapshot from the node table (`usable`), no table lookup for an unpinned pointee | `Mem.refOf`, `Mem.writeNode` | M20, M21, M26 | R8, change 1 | The gates; the byte comparison against `l34-base` (8.9), the same stream in every configuration; `conformance.sh small` and the reclaim set; `performance.sh ab l34-base current` on a quiet machine |
| 2 | Runtime loads are not cut back: only reconstruction at startup cuts a key node version back to the startup time (`followStreamPointer`, lines 247 to 251) | `Obj.ofVersion` with no cut in `Mem.follow4` | M22 | R8, change 2 | As 1 |
| 3 | The loader, `NodeCollection.followStreamPointer` (202): the pointee's canonical object if there is one; else exactly the version the slot names after Rule R, as a snapshot not entered in the node table; never a newer snapshot from the table (`usable`, line 233) | `Mem.follow4` | M27 (Q7) | R8, change 3 | As 1; the checker's C-L, which compares Java's first touches with stage 1's rule (`Mem.follow`), then compares them with the Level 4 loader |
| 4 | Startup, rule 4 (`DbStarter.createMemoryPointers`, 226): every stream slot of a canonical object of a node of D that names a node with a canonical object becomes a memory slot to it, by node id, not only by exact position. The root's object needs nothing: the virtual root's one slot, `TopDs.superRoot`, is a memory reference already (5.13) | `Mem.linkD`, `evictStartup` | M44 | R8 | As 1; `RestartInvariance` |
| 5 | A slot's pair is read once (`KeyNode.getPointer`, 202; `TopNode.getPointer`, 265); access data leaves the position field, or is written only under the slot's lock with a recheck; the access clock becomes a field of its own | Slots are a pair (`Slot`) | M23, M24 | R8, change 4; J1 (the clock) | As 1, with the performance comparison |
| 6 | Reclaim's scan and its per-KV reads (`Reclaim.step`, 345) are maintenance reads: they neither register nor swizzle what they read; a slot's position stands in for a load where it suffices | — (stage 3) | M28 | R8, change 5; J6 | As 1, with the reclaim set |

### 6.2 Eviction (J1 to J10)

| | Change | The model | Rows | WP | Check |
|---|---|---|---|---|---|
| 7 | A registry of resident objects, and the pins: D's canonical objects (`TransSeq`), the record being written (`TransNodes`, whose dirty flags `clean` (131) clears before the record is appended, so "not dirty" is not "written"), the super root, the objects of an operation in progress. Everything else may be evicted (T-PIN) | `Mem.pinned`, `TP_pins` | M25, M26 | J1 | The audit (J1): every pinned object resident and canonical, one canonical object per node id, INV-SLOT against a test-only oracle of latest positions, on every configuration of 8.4 |
| 8 | Unswizzle: under the slot's lock, after rechecking that the target is clean, unpinned and written, a memory slot becomes a stream slot naming the target's position | `Mem.unswizzle`, `Mem.detachable` | M23, M24 (Q8) | J2 (values), J3 (index nodes) | `EvictionInvariance`: the same stream with the schedules none, every and random; the audit |
| 9 | Release: the object leaves the registry; the node table's entry goes if it names the object, and its canonical flag is cleared (a reader may still hold it); the writer's follower makes a reloaded node canonical again. The node table then holds resident objects only (T-INDEX) | `Mem.release`, `Mem.promote` | M26, M31 | J3 | As 8, and J3's tests |
| 10 | Copies of slots (splits; `TopDs.newSuperRoot`, 42): no change. A-COPY holds on every Java run checked (section 4), and a copied stream slot serializes what its source did (5.4). Top node skip slots keep their cached times when unswizzled | `Mem.newSlot4`, `CopyStep` | M29, M43 | J3 (check only) | C-P on Java's physical states (J4); `A2A3Check2`'s A-COPY count |
| 11 | Readers under eviction: the protocol of Q8 | — (sequential) | M39 | J5 | Interleaving tests; `ReclaimReaders` with a forced schedule |
| 12 | Memory accounting, the access clock, the capacity controller; the cache size computed in `long` | — | M40, M45 | J1, J7 | J7's tests; a unit test for M45 |

J4 adds the checks with eviction (the exporter's run E, SLOT lines, C-P in
the checker, an eviction set in `conformance.sh`); J8 to J10 the
larger-than-memory run, `level4.sh` and the performance comparison.

### 6.3 What Java keeps

The record format and every existing database; Rule R's section map;
`javaTest` (Rule A over all pointers) and marking; one canonical object per
node; the readers' path; the copies of slots. And three properties of its Dag
that the model assumes and that hold on every Java run checked: TREE, A6'
and A-COPY (section 4). A6, which the plan's 8.5 assumed, fails in 5 of
68,901 Java-tier transactions; the model does not need it.

### 6.4 Not settled here

M46 (the ordinal bound): Frans, not urgent. The details of Q8's protocol: J5.
Level 3's corrections come from R7's red list (level3-alignment.md) and go
into R8 with these. M30 (the top node ordinals) was fixed in A3
(`280525a`).
