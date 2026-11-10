# 020-30. A deleted KV eventually costs nothing

Created 2026-11-10 by Frans Lundberg. Status: open.

The index of a BergDB database keeps the nodes of deleted keys for ever:
they stay reachable at the current time, every scan, put and reclaim step
through their key range passes them, and reclaim copies them forward, so
neither the time of a scan nor the size of the stream is bounded by the
live data. This subitem is the study and the fix. Release 2026.4 waits
for it.


## 1. Frans's decision and rule

Frans, 2026-11-10, 08:29, on 021-28 and the slow scans of 020-24-16 and
020-24-17: "The theme of 2026.4 is a bug-free database. I consider this a
bug. The bounds are not ok. Scans are supposed to be O(n) amortized for
scanning n items. This is deep in the core of the low-level part of the
database. I thought this was stable. I consider cancelling the release
2026.4 for now. And fix the bug first."

08:38, on the coordinator's proposal (when a delete leaves a node with no
live klong at that time, the same transaction also deletes the parent's
klong that points to it, and so on upward): "This seems to be the correct
way to handle this. How does it work today? I am afraid of unreleased
resources. How are parent nodes deleted when they are no longer needed?"

08:50, **the rule**: "Deletes need to be handled so that eventually, some
time after the retain period has passed, deleted KVs consume no resources
of the database. I see this as some sort of clean up. We can do as much as
possible in the deleted transactions. But it is also possible to leave
things for the Reclaim to clean up. Either way, a deleted KV must consume
zero resources eventually after the retain period has passed."

09:03, **the decision**: "This is major. [...] My decision is to pause
2026.4 until this has been sorted out." The candidate `03ce6ec` is not
tagged.


## 2. The rule, made checkable

The coordinator's reading of the rule (08:50), to be confirmed or
corrected by the study and by Frans. Some time after a delete is older
than the retain duration (at most one finished reclaim iteration and its
cut later), the deleted KV costs nothing:

1. **No bytes in the stream:** not its value node, not its key nodes,
   not its klongs, not a delete bitmap kept only for it.
2. **Nothing reachable at the current time:** no node and no klong of it
   can be reached from the current root, also not a deleted klong in a
   node that still holds live keys.
3. **No work:** no scan, get, put, delete, reclaim step, eviction or
   startup visits anything of it.
4. **No memory:** no node, handle or cache entry of it is held.

How it can be checked: a test deletes keys, lets the retain duration pass
and a reclaim iteration and its cut finish, and compares the database with
one that only ever held the live keys: the stream's length after the cut,
the number of index nodes reachable at the current time, and the key nodes
a scan of the whole database follows, each about the same. Workloads: 021-25's FIFO of
keys in time order (and its hashed variant), 020-24-16's job queue,
020-24-17's index cycles, 020-24-18's metrics store.

Frans's scan bound (08:29): a scan of n KVs costs O(n) amortized,
whatever was deleted before.


## 3. How it works today

As found on 2026-11-10 by the coordinator (coord-1110), from the code on
`main` (`1d8c5b1d`; the candidate's Core is the same):

* A delete sets one bit: `Dag.setValue()` (Dag.java:794) calls
  `appendDeleteKlong()` (Dag.java:899) on the segment leaf that holds the
  key's last segment, which appends a DELETE_BITMAP klong (or updates the
  transaction's) with the bit of that klong's position. Nothing above
  that node changes.
* A full node is time-split into its last version (only live klongs,
  `KeyNode.lastVersionGivenDel()`, KeyNode.java:1091) or space-split, in
  `Dag.handleFullNode()` (Dag.java:1058). Nodes are never merged and
  never removed; there is no merge code. A node whose klongs are all
  deleted stays, and its parent's klong to it stays live; so do the
  segment subtrees of deleted long keys. 011-01's Q1 (October 2026) named
  this and asked which bound BergDB should promise; it was not decided.
* A scan (`GetMany.Chain.next()`, GetMany.java:331) descends into every
  such subtree, finds nothing live and climbs back; its stop condition is
  called for live KVs only (Dag.java:688), so it learns of its range's end
  only at the first live key after it (020-24-17, U17-1; 021-28 is a
  read-path fix for that case on a branch). Deleted keys at the head of a
  range are passed by every scan of it (020-24-16, U16-1).
* Reclaim: the 2012 design (F1-007, `2012-07-space-reclaim.txt`)
  rewrites live KVs only, and so did the 2017 code; the nodes of deleted
  keys stayed in the tree, and after a cut a lookup could follow a pointer
  into the removed stream (011-01, Q7). Since 2026-10-13 each step touches
  every index node of its key range (Reclaim.java:670), also those that
  hold deleted keys only, so they are copied forward on every iteration
  and never released (021-25, part 1); and the touch runs on to the next
  live key (021-25, part 2). The value nodes of deleted keys are released
  by the cut already: reclaim rewrites live values only.

Related: 021-25 (reclaim stops cutting a FIFO; fixes (a), (b), (c); (c) is
in the candidate, `021-25-fix-a` a prototype of (a) on a branch), 021-28
(branch `scan-deleted-keys` in `/Users/f/fl/bench/2026-11-09/clone-q34`),
020-24-16 to 020-24-18, 011-01 Q1 and Q7.

The direction discussed (the coordinator, in the same discussion; not decided): the deleting
transaction makes an emptied subtree unreachable at once (the delete goes
upward), so scans are bounded at any time; reclaim releases what must
wait for the retain duration (it does not copy unreachable nodes, drops
deleted klongs and versions older than the first available time when it
rewrites a node) and the cut frees the bytes. Merging underfull nodes (as
the multiversion B-tree does, for a bound in the live keys) is a separate
decision.


## 4. The study

By d30 for coord-1110, at effort max (Frans, 09:03). Frans changed the
scope at 09:21: phase 1 is this first overview of the alternatives, by
10:00; full proposals, with tests and prototypes, come in a phase 2. So no
new measurement here: the figures are those of the items cited. Read: the
code of `main` (`0b93d273`, Java as `1d8c5b1d`), 021-25 (with the branch
`021-25-fix-a`), 021-28 (branch `scan-deleted-keys`), 020-24-16 to 18,
011-01 (Q1, Q7, Q8), Frans's notes of 2012 to 2016 (F1-007), the Lean
model's definitions (`SIS/Basic.lean`, `Check/Trace.lean`) and
`docs/sis-model.md`. Four helpers' files beside this one, 020-30-01 to
020-30-04 in `30-deleted-kvs-cost-nothing/`, go deeper on parts of it
(section 4.7); they are cited where they add.

**State** (09:45): phase 1 done, this section. No code: the clone
`/Users/f/fl/bench/2026-11-10/d30/clone` has the branch
`020-30-deleted-kvs` at `main`'s `0b93d273`, unchanged. Next: phase 2, as
the coordinator assigns it.


### 4.1 What a deleted KV holds today

| What a deleted KV holds | How long | Code (main) |
|---|---|---|
| Its value node                        | until a cut passes it         | Reclaim.java:622       |
| The delete in its record              | until a cut; rerun at a start | Db.putKvs, DbStarter   |
| Its klong and bitmap bit, in its leaf | until the leaf is split       | Dag.java:899           |
| A leaf with no live key, linked       | for ever                      | Dag.java:1058, 1172    |
| Inner nodes with no live key below    | for ever                      | nothing unlinks them   |
| A long key's next segment trees       | for ever                      | Dag.java:729           |
| Work of scans through its range       | for ever, through restarts    | GetMany.java:331       |
| Reclaim's scan at tStart              | every iteration               | Reclaim.java:579       |
| Reclaim's touch: dirty, rewritten     | every iteration, never cut    | Db.java:2944           |
| Memory: in D, then in the cache       | until written; until CLOCK    | Db.java:1531; Eviction |
| Handles: in the table; dead in nodes  | while the objects are held    | Cache3, Handle         |

Places in `java/src/bergdb/` on `main`. Row 4: a full leaf with no live
key is replaced by an empty node, still linked (section 4.2). Lookups at
earlier times within the retain duration need the old value node, the
leaf's version with the klong and the versions on the path: every option
keeps them until a cut, and only then may they go.

The rest of a deleted KV's cost follows from the rows above. Puts and
deletes pass the nodes on their own path only. A get passes one path, so
it pays for deleted keys through the height of the tree only (nodes are
never merged; 011-01, Q1). A start reruns the delete while it is in the
startup section, and a cold start reads the nodes on the rerun's paths.
Eviction takes clean objects by CLOCK when the resident bytes pass the
budget; nothing frees an object because no current node points to it any
more (2012-03-19 already: "no node deletion (always grows in memory)",
020-30-02, section 1). The top nodes (`TopDs`, one per new space root) are
history, not of deleted KVs: never removed, they are cut with their
records.

Where the cost becomes unbounded: rows 4 to 6 keep nodes reachable at the
current time, so rows 7 to 10 repeat for ever and grow with every delete:
021-25's FIFO (an iteration's first step scanned 20,642 index nodes for 4
KVs and made 17,493 dirty, 4.17 MB), u18's metrics store (1,188 MB for 1.8
MB of live data, records of 149 MB), u16's queue head (204,226 key nodes
followed for 16 entries), u17's empty scan past index cycles (139,233 key
nodes).


### 4.2 Sections 2 and 3, checked

Section 3 is right. Four additions:

1. A leaf whose keys are all deleted stays as it is while it has room for
   the delete bitmap. When it is full, `Dag.handleFullNode` replaces it by
   its last version, an empty node (a time klong only), and links that
   with a new klong in the parent. `Dag.timeSplit`'s comment says "Last
   version is small enough not to split into two nodes, but not empty"
   (2013-10-05): an assumption the code does not check.
2. The touch is not stored and not rerun at a start (the comment of
   `DbStarter.canonicalNode`): D is rebuilt from the stored ids. So
   anything that reclaim's touch changes in the tree, beyond making nodes
   dirty, would not be redone by the rerun. This matters for option B.
3. Reclaim's own scan at tStart (a maintenance scan, Reclaim.java:579)
   passes the nodes of deleted keys too, before the touch does.
4. Memory: the Pub API always evicts (`noEvict()` is the Core's only).
   With `noEvict()` no object is ever released, the old versions of live
   nodes neither: not special to deleted keys.

Section 2's reading: points 1 to 4 and the check seem right to me, with
three remarks for Frans.

* Point 2's last words, "also not a deleted klong in a node that still
  holds live keys", are what separates option A from C below: A alone
  leaves such klongs, at most a node's size of them in each node that
  holds live keys, until that node is split.
* With the retain duration "forever" (the default) nothing is cut, so
  points 1 and 4 cannot hold: the history of a delete is kept by
  definition. Points 2 and 3 can, and they are what the scan bound needs.
* "At most one finished reclaim iteration and its cut later": an index
  node version written during an iteration is cut only by the cut after
  the next one, so the bytes may need two iterations after the retain
  duration, not one.


### 4.3 The original intent

From Frans's notes (020-30-02 has more, and the literature):

* 2012-01-27 (the 2012 log, DAY12-11): "Merges are made when the current
  version of a node shrinks because of a delete. It may then be merged
  with its parent."
* 2012-02-17 (DAY12-21): "DECISION. Keep the klong-array approach.
  Implement working split. Optimize split/merge later. Start with split,
  no merge right now."
* 2012-06 (2012-06-notes, the NewDelete branch of the delete bitmaps):
  "The last version of the full [node] could be empty (no key klongs).
  This happens when all key klongs have been deleted. In this case, we
  want to delete the node by adding a delete klong to its parent." And:
  "If lastVersion is empty, remove from parent." Not in the code: since
  2013-10-05 it assumes "but not empty" (4.2, point 1).
* 2012-07 (2012-07-space-reclaim): reclaim rewrites the live KVs; the
  stream is estimated at "between 2 and 4 times the dbSize", dbSize being
  the live KVs. The design took for granted that deleted KVs cost nothing
  after reclaim.

So the upward delete (A) is Frans's intent of 2012, there for the full
node; merges (D) were meant and postponed; and the rule of 08:50 is the
2012 space estimate made explicit. In the literature (020-30-02, sections
2 to 6), the structures with a scan bound in the live keys (the
multiversion B-tree, LMDB, Btrfs) unlink, and merge, in the deleting
transaction; those that leave it to background work (LSM trees, CouchDB,
the time-split B-tree) have no bound until that work has run; all free the
bytes only after the oldest snapshot, here the retain duration and the
cut.


### 4.4 The options

**(A) The delete goes upward, in the deleting transaction.** In
`Dag.setValue`, a delete that leaves its leaf with no live key at the
transaction time does not touch the leaf: it deletes the parent's klong to
the leaf instead, and so on upward while a node keeps no other live klong,
also across segment trees (the parent segment leaf's klong of a long key's
next segment). One bitmap entry, at the first node that keeps a live
klong; the emptied nodes get no entry (A2 of sis-model 3.4), and lose any
of the transaction's own (`toPreviousState`, as a node replaced by a split
does; `keyNodeReplaced`, so they leave D). It is Frans's 2012 rule,
applied to every emptied node, not only a full one. `appendDeleteKlong`
already works on any key node, and every search applies a bitmap in any
node, in 2026.3 too (020-30-03, section 1). The emptied child's key range
then belongs to its left sibling: a later put there lands in the sibling,
which is right, as a klong above the leaf is a lower bound.

Special cases, for phase 2 (020-30-03, sections 2 and 4). Every put relies
on an inner node having a live klong at or below any key routed to it
(`checkFound`, Dag.java:835, else "corrupt data", in 2026.3 too), and
backward scans on the same; so the smallest live klong of an inner node
cannot just be deleted, and that is the common case (a FIFO, a queue's
head, the left edge). Either re-key it, A-relabel (add a klong with its
bound for the next child and delete both old klongs, and the same down
that child's left edge: O(h) node writes once per emptied leftmost child;
nothing is left), or keep that one empty child, A-keep (at most one chain
of empty nodes on the left edge of each live inner node, about h squared
nodes in a FIFO; scans pass it). A node created by the same transaction
stays linked (A3: a new node is reachable), or the transaction's own klong
to it is taken back. An inner space root left without a live klong is
replaced by a new empty leaf root (a new super root).

A meets rule points 2 and 3 at once, from the delete on (also with retain
forever), and points 1 and 4 after the cut: no touch copies the unlinked
nodes, their versions are cut, their objects are clean, and CLOCK takes
them. It leaves deleted klongs in nodes that hold live keys. Bound: every
node reachable at a time t, but the root and the special cases, has a live
key below it at t, so a scan of n KVs follows at most about (n + 2) · h
key nodes, h the number of key node levels on a path (all its segment
trees), each node with at most B klongs (B = 30): forward and backward, at
the latest state and in the past. Space: at most B klongs a reachable
node. h does not shrink: it is at most about the logarithm, base B/2, of
all keys ever put (Q1). With A, reclaim's Q7 copies end with no change in
reclaim (its touch follows reachable nodes only), and 021-25's parts 1 and
2 shrink to the live data (020-30-01, section 3).

Cost: the emptiness test is one more pass over the node's klongs; a delete
that empties a node writes its bitmap higher up instead of in the leaf,
and the emptied nodes are not written again; the climb is O(1) amortized
per node made, at most the path's height for one delete; no new node but
for the root case. `Dag.dirtyNodeBound` must count a delete's entries on
its whole path, and A-relabel's off it. Risks: time travel is unchanged
(entries at the transaction time only); readers as today (the class
comment of `KeyNode`); the rerun redoes it (a function of the state and
the delete); crashes as today. Lean: no new theorem (the model is generic
in the entries; the checker's `blive` reads a delete in any node), but the
trace checker must accept A's transactions (A2, A3, A5, TREE, A6', A-COPY
for A-relabel's copied pointers).

Format: no new klong or node type, and 2026.3's parser reads every shape A
writes, if the invariant above is kept. But a start reruns its startup
section through the Dag, so the delete's rule is part of what a record
means: 2026.3 opening a stream of A, or A opening a stream of 2026.3,
reruns deletes by the other rule, makes other nodes and ids, and fails
("node ... not found") or builds another tree (020-30-04, section 2;
020-30-03, section 3). So A is a format change in the sense of 018-01,
section 2: a `RECORD_FORMAT` 6 that Frans approves, and either a rerun of
format 5 records by today's rule or a refusal of 2026.3's databases. Other
bytes too: StreamDigest's digests change in most of its 12 configurations,
and the C port must follow, about 150 to 300 lines of C (020-30-04,
sections 3 and 5).

**(B) Reclaim cleans up.** Reclaim's touch, which visits every node
reachable in its range at the step's time, (B1) unlinks every node it
finds with no live key, as A does, and (B2) compacts every node it
rewrites that holds klongs not live at the step's time: it replaces the
node by its last version (a time split at the step's time, in post-order,
when the scan leaves the node, so a parent is replaced once, after its
children). The old version serves the times before the step and goes with
the iteration's cut. Meets all four points, but only after a touch of the
range: with retain forever there is no reclaim, and between touches the
scans pay for every delete since the last one, so it gives no scan bound
of its own (020-30-01, section 2: reclaim alone meets the resource rule
eventually, not the scan bound). 020-30-01 puts an empty node's bytes at
about R and two iteration spans after its delete, a pruned klong in its
parent at about 2R and three to four spans, and a chain of h emptied
levels at up to h iteration starts, unless a step checks a node after its
last child. B1 is the only cleanup of the empty subtrees that databases of
2026.3 already hold. Cost: one new node per compacted node and iteration
(the touch writes every reachable node anyway), a new super root per
iteration. Risks: the touch is not rerun at a start (4.2, point 2), so its
changes must be redone from the step's record (its range follows from the
rows' `lastKey`, or a new field holds it): a format change as A's,
`RECORD_FORMAT` 6 (020-30-04, where my B1 is its B3; its B1, not copying
what is unreachable from the first available time on, is what A gives the
touch for free). C port: 200 to 400 lines; StreamDigest: the 4 `l3-*`
configurations. Not B2 as an in-place compaction of a node (dropping
entries dead before the first available time): readers admitted before a
cut would get wrong answers instead of `LookupTimeNotAvailableException`,
lemma M (a newer version serves every time an older one serves) would no
longer hold, and the Lean model would need a new kind of change
(020-30-04, section 4).

**(C) A and B.** A for the bound at every time, with or without a retain
duration; B1 for what A leaves linked (a node created and emptied in one
transaction, A-keep's chains) and for old databases; B2 for the deleted
klongs in live nodes. The only option that meets all four points of
section 2, with A's scan bound. After a cut, the kept stream holds the
live data's index and the retained history: the condition for 2012's
estimate (011-01, Q8).

**(D) Merge underfull nodes**, as the multiversion B-tree (Becker et al.
1996; Q1 of 011-01): when a delete leaves a node with fewer than about B/4
live klongs, it is merged with a sibling (one or two new nodes, the
parent's klongs replaced), and a root with one child is replaced by it.
A's unlink is the case of an empty node. Bound: gets O(log_B n_t), scans
O(n / B + log_B n_t), space O(n_t / B) nodes, for n_t live keys: the bound
that Q1 asked for. Cost: amortized O(1) restructuring a delete, besides
its path; a merge reads the sibling (a stream read under eviction) and
writes new nodes. Risks: the most code and the most cases (splits and
merges of the same transaction, segment roots); the Lean model needs no
new theorem (new nodes and entries), but TREE, A6' and A-COPY must still
hold; a format change as A's; 300 to 600 lines of C. A decision of its
own, after A.

**Others.**

* (E) Ends of scans and of the touch: 021-28's `GetMany.endKey` (u17's
  scan past its range) and 021-25's fix (a) (the touch's end). They bound
  two cases on the read path and release nothing; u16's head and the
  touch's first step stay. With A they pass only the path to the next live
  key (O(h)); `endKey` still saves the read of that key's value. Optional
  with A, not a fix without it. No format change.
* (F) A range delete (2012-06 notes: "A range-delete operation could
  possibly be significantly more efficient"): `deleteIndex` and a
  directory's delete could unlink whole subtrees in one transaction. An
  addition to A for u17's index cycles, not a replacement.
* (G) Compaction by copy: an operation that writes the live keys into a
  new tree (the application's workaround of a new index generation, u16).
  Bounded, but a large transaction, and the old tree is still cut only by
  reclaim. Not incremental; not recommended.
* Memory under `noEvict()`: an explicit release of the objects below a cut
  would be needed for point 4 there; the Pub API always evicts.


### 4.5 Comparison

By the four points of section 2:

| Option | 1 bytes | 2 nothing reachable | 3 no work | 4 memory | Format |
|---|---|---|---|---|---|
| today     | no  | no                     | no            | no    | 5 |
| A         | cut | nodes now; klongs stay | nodes now     | CLOCK | 6 |
| B         | cut | after a touch          | after a touch | CLOCK | 6 |
| C         | cut | now; klongs at a touch | now           | CLOCK | 6 |
| D, with A | cut | nodes now; klongs stay | now           | CLOCK | 6 |
| E         | no  | no                     | two cases     | no    | 5 |

"Cut": after the retain duration, at most two reclaim iterations and their
cuts later; never with retain forever. "Now": from the delete's
transaction on, also with retain forever. "CLOCK": clean objects that no
current node points to are taken when the resident bytes pass the budget,
not at once. Format: `RECORD_FORMAT`, 5 today; 6 means that a start must
know which rules wrote a record (020-30-04). E is 021-28's `endKey` and
021-25's (a).

Bounds and costs (n live KVs scanned, h key node levels on a path, B the
node size, 30; A-relabel adds O(h) node writes once per emptied leftmost
child):

| Option | Scan, key nodes followed | Space, reachable index | Cost of a delete |
|---|---|---|---|
| today | (n + 2) h + deleted keys' nodes | grows with the deletes  | a bitmap in the leaf  |
| A     | about (n + 2) h                 | at most B klongs a node | a bitmap higher up    |
| B     | as today until a touch          | as C after a cut        | as today; more touch  |
| C     | about (n + 2) h                 | live keys' nodes only   | as A; touch compacts  |
| D     | O(n / B + log n)                | O(n / B) nodes          | amortized O(1) merges |


### 4.6 For phase 2, and questions for Frans

Full proposals, in this order:

1. **A**, with its special cases (the smallest klong of an inner node:
   A-relabel or A-keep; the root; a node of the same transaction),
   `dirtyNodeBound`, the format 6 and the rerun of format 5 records, and
   the tests of section 2's check (021-25's FIFO, u16's head, u17's
   cycles, u18) in key nodes followed and stream bytes, against a database
   that only held the live keys. It carries the scan bound and most of the
   rule. Recommended first.
2. **B1 and B2** (C with A): the touch's work redone at a start from the
   step's record; the compaction's post-order and its write cost. Best in
   the same format change as A, if it is ready in time.
3. **D**, as its own decision: the bound in the live keys of Q1.

E (021-28 and 021-25's (a)) needs no proposal: with A, a small
optimization to take or leave.

Questions for Frans, each with a recommendation:

* F1. Section 2, point 2: must a deleted klong in a node that still holds
  live keys go too (C), or is a bounded rest, at most a node's size of
  klongs in each live node, enough (A)? Recommended: it must go (C), but A
  first, as it carries the bound.
* F2. The scan bound, "O(n) amortized": is A's (n + 2) · h node visits, h
  at most the logarithm of all keys ever put, enough, or is the bound in
  the live keys (D) required? Recommended: A now, D a later decision.
* F3. With retain forever, the history of a delete is kept, so only points
  2 and 3 can hold. Is that the intent? Recommended: yes.
* F4. Databases of 2026.3 and before already hold empty subtrees, and A
  alone never cleans them. Clean them by B1 (with a retain duration only),
  by a one-time pass, or leave them? Recommended: B1, and a note for
  databases without reclaim.
* F5. Format: A, B and D change what a record means at a start, so
  `RECORD_FORMAT` 6 (018-01, section 2). Should 2026.4 open 2026.3's
  databases (rerun their format 5 records by today's rule, a small second
  path) or refuse them? Recommended: open them; 2026.3 refuses format 6 by
  its version check.
* F6. Release 2026.4: with A only, or with C, in one format change?
  Recommended: A in 2026.4 if phase 2 shows it sound and gated; B in the
  same format 6 if ready, else 2026.5 with a format 7; D in 2026.5 or
  later.
* F7. 021-28's `endKey` and 021-25's fix (a), both on branches: with A
  they are optimizations (a scan past its range's end saves the read of
  the next live key's value; a step's dirtying stays within its range).
  Recommended: take them with A's change, not before (020-30-01, section
  3).


### 4.7 The helpers' files

* 020-30-01, the reclaim side (r30): what reclaim does with deleted keys,
  reclaim alone (B) step by step with its delays, reclaim with A (the Q7
  copies end; fix (a) not needed for the bound), and the risks: the cut's
  safety, lookups within R, the rerun of the touch.
* 020-30-02, the original intent and the prior art (p30): Frans's notes of
  2012, the multiversion B-tree, the time-split B-tree, LMDB, Btrfs,
  CouchDB and the LSM trees.
* 020-30-03, the upward delete's mechanics (a30): how a key maps onto
  nodes, A step by step, the smallest klong of an inner node (A-keep,
  A-relabel), the root, the transaction's own nodes, `dirtyNodeBound`,
  what 2026.3 reads, and A's variants.
* 020-30-04, outside the write path (f30): the stream format and the rerun
  (why A, B and D are format changes), StreamDigest, the Lean model per
  option, the C port's places and sizes, and the tests and conformance to
  redo.


## 5. Log

2026-11-10. Created at Frans's request (09:03), with his rule and his
decision to pause 2026.4; the study started (coord-1110).

2026-11-10. Section 4, phase 1 (Frans's change of scope, 09:21): a first
overview of the alternatives by d30 for coord-1110, with the helpers'
files 020-30-01 to 020-30-04: what a deleted KV holds today, sections 2
and 3 checked, the original intent, the options A to G, their comparison,
the proposals for phase 2 (A first, then B with it, D apart) and the
questions F1 to F7 for Frans. No code and no new measurement.
