028-72. Investigate: the action's 7/8 against the worst action by the Lean's node count
=======================================================================================

Status: open. Kind: Investigate. Frans: decision.
Created 2026-11-27 by Frans Lundberg.

What: since 031-06's step 2 (on `main` since `5b88cc80`), an action's
index nodes are admitted up to 7/8 of the record limit
(`actionDirtyLimit`, 1,879,048,185 bytes at the release's limits).
031-06 (section 9) states that a transaction within L1 to L5 makes at
most 1.47 GB dirty at node size 8, so that none is refused by it. That
figure uses 024-17's count of 14 nodes a level (c = 14, H = 61). The
Lean model's `Params.nodesALevel` (`SIS/Tree/Bound.lean`) has counted 19
at node size 8 since 028-21; by that count the worst action, decided by
L3's sum of segments, makes about 2.00 GB dirty, 106 % of 7/8.
`releaseFits8` shows only that it fits 15/16. Found by the investigation
of BergDB's own long keys (2026-11-27, 031-06, section 8, O1); a cap on
those keys does not change it, as the worst action is L3's sum, not one
key.

Why: if the Lean's count is the right one for Java's tree, a
transaction within the published limits can be refused at node size 8
by the action's 7/8, which 031-06 says cannot happen; and 031-06,
section 3's mixed record, by the same count, is about 118 % of the
record limit at node size 8 and 108 % at 62 (75 % at 30), even with a
cap of 1,024 bytes on own keys. Today the record is protected by the
actual-key count (`recordDirtyFits`) and the loud failure before the
append (`checkTakeable`), not by the arithmetic.

Frans: decision: options A to G under Options; A recommended for
2026.7, and B with the next change to the Lean's tree bound.

Done when: it is stated, with the reason, which count bounds Java's tree
at node size 8 (024-17's 14 nodes a level or the Lean's 19), and either
a test at the release's limits shows the worst transaction admitted, or
the admission's limit or the text is changed so that no transaction
within L1 to L5 is refused; 031-06, sections 3 and 9, and 024-17 say
what holds.

First step: `Params.nodesALevel` and its docstring in
`SIS/Tree/Bound.lean` against 024-17, section 5.2a, and the Java tree's
split rule at node size 8; then the worst transaction of 024-17,
section 5.3, at the release's limits, through `Db.execute()`, on a
large heap.

Small slips to fix with whichever change comes next (the same
investigation):

* 024-17, section 6.2 (a), and the comment in
  `DbTesterLimits.testTransKeyBytes` give the longest Pub index entry as
  497 bytes, 72 segments; the investigation counts 496 bytes, 71
  segments: the object's file part is at most 110 bytes, as the ikey is
  at most 111 and begins with "/".
* `ReclaimRoomTester.testLongKeyCopiedByAStep`'s Javadoc says a key of
  6,000 segments (42 kB); the key is 35,997 bytes, 5,143 segments.
* 031-06's `landing.md`, step 2: 1 KiB is 147 segments, not 146.


Finding
-------

Investigated on 2026-11-27 by an agent of lead-1127 (branch
`028-72-count`, nothing on `main`). The probes and their output are in
this directory (The probes, below).

* **Db compares Java's count, not either formula.** `Db.countDirtyNodes`
  refuses a transaction only if both the cheap test and the walk,
  `Dag.dirtyNodeBound` on the tree the transaction meets, are over
  (`actionDirtyLimit()` - `TOP_BYTES`) / 192 = 9,786,700 nodes at node
  size 8 (`DirtyNodeCounts.refused`). 024-17's count with q (14 a level)
  and the Lean's `Limits.dirtyNodes` (19 a level) are bounds on that
  walk from the limits alone (TP26, stated, not proved).
* **At node size 8, 024-17's 14 bounds Java's count. The Lean's 19 is a
  looser bound of the same count, not a different case and not an
  error.** On the worst path, Java's count of a delete is 13 nodes a
  level and 869 nodes a segment at H = 61, which is 13.79 (H + 2).
  024-17 allows 14 (H + 2) = 882 a segment, the Lean 19 (H + 2) = 1,197
  (The count, below).
* **No transaction within L1 to L5 is refused by the 7/8, at any node
  size.** The worst one is 500 deletes of 8,692 segments, on paths of
  full nodes in segment trees 62 key nodes high. At node size 8 it
  counts 7,488,343 nodes: 1,437,763,520 bytes, 76.5 % of the 7/8
  (1,879,048,185 bytes), 2,298,357 nodes (23.5 %) under the refusal. At
  node size 14 it is 48.2 %, at 30 46.8 %, at 62 66.9 %. By the Lean's
  count it would be 10,411,324 nodes (106.4 %); by 024-17's, 7,673,344
  (78.4 %).
* **At node size 14, 024-17's 9 a level no longer bounds Java's count.**
  Java counts 365 nodes a segment there, against 9 (H + 2) = 360 at
  H = 38. The difference is the new roots above a cut segment root,
  which 028-21 added: 3 nodes a tree at node size 14. A count of 10 a
  level would bound it, and the Lean's 13 does. At node sizes 30 and 62,
  8 a level holds (186 against 192; 137 against 144).
* **The result rests on two things that are not proved.** First, H comes
  from V1 (TP30), as in every count here. Second, the worst tree for
  Java's count is the one the probe builds: this is an argument (The
  count), checked by the probe's variants and on trees that PE built.
  The result is about the count that Db compares. That the count bounds
  what PE writes is TP23: proved for puts, tested for deletes (028-21,
  030-29). On PE's trees the count was 39 to 63 times the key nodes PE
  marked.


The count, from the code
------------------------

Node size 8 uses Dag's thresholds, v x B / 30 (024-21):

* **The node.** A key node holds at most B = 8 klongs (TIME klongs, KEY
  klongs and delete bitmaps), so it has at most 7 children. The
  thresholds are h = 4 (`splitAbove`), m = 2 (`minFill`), c = 4
  (`mergeCap`), a cut size of 4 (B / 2) and theta = 2. The room after a
  replacement is q = `roomAfterReplacement` = max(2, min(4, 4, 4) - 3)
  = 2.
* **H.** Every key node but a segment tree's root holds at least
  m = 2 live klongs (V1). A stream under 2^63 bytes holds under 2^60
  klongs, so a segment tree is at most 1 + log2(2^60) = 61 high
  (024-17, 5.2): 62 key nodes on a path. With V2's inner root of two
  klongs, a tree of L levels holds at least 2^L live klongs, so L is at
  most 59. H = 61 is therefore 3 levels generous; this entry keeps it.
* **What `Dag.dirtyNodeBound` counts for a delete,** at each node of its
  path:
  * the node itself (1);
  * the merges: 4 nodes a level (`mergeLevels`), and two levels more for
    each delete;
  * the node's klongs, x. These are the delete's 4, plus what comes from
    below: the parts of the child, or, at a segment leaf, the overflows
    and one of the root below and the root collapses of that tree (its
    inner nodes on the path, H);
  * its overflows, 1 + floor((x + 1 - room - 1) / q), where room is
    max(0, B - 2 - size), and at most q on a delete's path;
  * its parts, max(overflows + 1, cutPartsBound(size + x));
  * at a tree's root, also the new roots above the parts,
    max(overflows, rootsAbove(parts)).
* **The worst node, 13 a level.** The worst node has 6 to 8 klongs, so
  it has no room. Its overflows are then 1 + floor(x / 2) and its parts
  2 + floor(x / 2). The cut, 2 + ceil(x / 4), is never more for x >= 2,
  and x >= 4 on a delete's path. With x = 4 + p, p the child's parts,
  this gives p = 4 + floor(p / 2). Its fixed points are 7 and 8, and the
  count settles at 8 once the input from below is larger, which the
  collapses make it. So a level counts 1 + 4 + 8 = 13.
* **The collapses.** Each segment tree on the path adds the collapses'
  climb. The segment leaf above a tree gets 4 + 8 + 61 = 73 klongs and
  is cut into 38 parts; the levels above it get 23, 15, 11 and 9 parts,
  then 8. That is 56 parts over the 8 a level, about H, as the excess
  halves at each level at q = 2. The tree's root adds 7 new roots.
* **A middle segment, 869.** A segment in the middle of a key's path
  counts 13 x 62 + 56 + 7 = 869 = 14 (H + 1) + 1 nodes, which is
  13.79 (H + 2). The first and the last segments count less: nothing
  collapses below the last, and the space root has no leaf above it. A
  delete of s segments counts 869 s - 115, or 754 for one segment.
* **A put** counts 4 a level (3 parts), 250 a segment.
* **Against 024-17.** 024-17's count with q, 14 (H + 2) S + 14 n, is 882
  a segment, so it bounds Java's count with 13 a segment to spare.
  Before 028-21, Java's count of one delete of 16 segments was 13,685
  (024-17, 5.2a). Since 028-21 it is 13,789. The 104 more are the new
  roots above the 15 cut segment roots below the space root's tree: 7
  for each of them, 6 for the last.
* **The Lean's `nodesALevel`, since 028-21.** It bounds a node's parts
  by its overflows and two. So a node gets 4 klongs and at most x + 2
  from below, and overflows at most x = 2 + (6 + x) / q times. At q = 2
  that is x = 10 overflows and 12 parts. With the node, the merges, a
  new root a level and one more for the collapses, the total is 19.
* **Why the two differ.** Java's count at q = 2 has 7 overflows
  (1 + floor(x / q), not 2 + x / q), and 8 parts: the overflows and one,
  as a delete's path is never cut into more at node size 8. It has 7 new
  roots a tree, not one a level. The Lean's formula holds for every q,
  with two margins of one klong each. The second is needed at node sizes
  30 and 62: there a full node that gets 7 klongs is cut into 3 parts
  with one overflow. At q = 2 each klong more a level doubles in the
  fixed point, x = 2 (...). So the margins cost 4 parts a level, and the
  new roots about one more: 19 against 13.8. The Lean's count is a
  sound bound, and a loose one at q = 2.

On the worst path at the four node sizes, the parts a level, the
collapses' climb and the new roots of a tree give Java's count of a
middle segment, (H + 1) (5 + parts) + climb + roots. The last two
columns are 024-17's and the Lean's c (H + 2):

| B  | H  | q  | Parts | Climb | Roots | Java, a segment | 024-17  | Lean      |
|----|----|----|------:|------:|------:|-----------------|---------|-----------|
| 8  | 61 | 2  |     8 |    56 |     7 | 869 (13.79)     | 14: 882 | 19: 1,197 |
| 14 | 38 | 4  |     4 |    11 |     3 | 365 (9.12)      | 9: 360  | 13: 520   |
| 30 | 22 | 10 |     3 |     1 |     1 | 186 (7.75)      | 8: 192  | 11: 264   |
| 62 | 16 | 24 |     3 |     0 |     1 | 137 (7.61)      | 8: 144  | 11: 198   |

**Why the probe's tree is the worst for Java's count:**

* A node with fewer than B - 2 klongs has room, so it overflows less.
  The cut grows with the node's size.
* A node that several operations share is walked once, and overflows
  less than the operations would apart: 1 + floor((a + b) / q) is less
  than or equal to (1 + floor(a / q)) + (1 + floor(b / q)), and the cut
  parts are subadditive in the same way. So the paths are kept apart as
  far as full nodes allow: at most 7 children a node.
* Deletes count more than puts: 4 klongs and 4 merge nodes a level.
* A KV with a value transformation is walked as a put and a delete
  (`countDirtyNodes`). Its put adds one klong at the leaf, and the count
  here does not change.


At the release's limits
-----------------------

The worst transaction within L1 to L5 for Java's count:

* **500 operations (L1),** each a delete or a KV with a value
  transformation. A delete counts 13.7 a level, a put 4.
* **Keys whose bytes are multiples of 7 and sum to L3,** 57,344 bytes:
  8,192 full segments and the 500 empty last ones, so S = 8,692
  (024-17, 5.2a). How the bytes are split among the keys hardly matters.
  192 keys of 119 bytes and 308 of 112, or 499 keys of 7 bytes and one
  of 53,851, both count 7,488,343. Keys over L2 are BergDB's own: the
  Pub layer's index entries, at most 496 bytes (031-06, O1). A user's
  keys alone (L2) give at most 500 x 16 = 8,000 segments.
* **A tree in which every segment tree on the paths is 62 key nodes high
  and every node of the paths is full,** with the paths apart below the
  space root's top levels.

The counts of that transaction, and their shares of the 7/8 (%):

| B  | H  | Java      | %    | 024-17    | %    | Lean       | %     |
|----|----|-----------|------|-----------|------|------------|-------|
| 8  | 61 | 7,488,343 | 76.5 | 7,673,344 | 78.4 | 10,411,324 | 106.4 |
| 14 | 38 | 3,145,889 | 48.2 | 3,136,120 | 48.1 | 4,526,840  | 69.4  |
| 30 | 22 | 1,616,605 | 46.8 | 1,675,864 | 48.5 | 2,301,688  | 66.6  |
| 62 | 16 | 1,190,813 | 66.9 | 1,258,648 | 70.7 | 1,728,016  | 97.1  |

* **A user's keys alone** (500 deletes of 105 bytes, 8,000 segments)
  reach 70.4 % at node size 8 (the Lean's count: 97.9 %). Even one key
  at L3 alone is 100.2 % by the Lean's count (8,193 segments), and
  72.7 % by Java's.
* **How far from a refusal.** At node size 8, a refusal needs about
  2,640 segments more than L3 allows, which is an L3 of about 74 KiB at
  L1 = 500. So would segment trees about 80 high (H = 80, a stream of
  about 2^79 klongs).
* **Smaller databases.** With H = 48 or 38 (streams of under 2^47 or
  2^37 klongs, about 1 PiB or 1 TiB), the share is 60.7 % or 48.3 % at
  node size 8.
* **031-06, section 3's mixed record, by Java's count.** This is the
  action's 500 deletes and a step of 401 puts (2,060 segments), walked
  together as `recordDirtyFits` walks them, against 15/16. It takes
  76.3 % at node size 8 (49.6, 48.8 and 69.7 % at 14, 30 and 62), and
  73.5 % of the record limit with its own bytes of 42.3 MB. With the
  step's last KV at O1 (b)'s cap (147 segments) it is 76.5 %. With an
  own key at L3 (8,193 segments, O1 (a)) it is 95.7 % at node size 8 and
  99.2 % at 62. So the record fits at every node size, where this
  entry's Why gives about 118 %. With an own key near L3 in the step, it
  is within 1 % of 15/16 at node size 62: a reason for O1 (b).


The probes
----------

* **`ActionRoomProbe.java`** (package bergdb.core, run against
  java/build/bergdb.jar) builds the worst tree of the keys in memory,
  making the key nodes directly. Only the paths exist. Each node is
  filled to B klongs with KEY klongs that point nowhere and that no
  search of the walk picks. The probe then calls `Dag.dirtyNodeBound`
  as `Db.countDirtyNodes` does and compares the count with
  `StoredTrans.actionDirtyLimit()`. At the release's limits (H = 61 at
  node size 8) the tree has 537,304 key nodes; a run takes under 20 s
  and at most 4 GB of heap, and writes no record. Its variants:
  * nodes of 7 or 6 klongs on the paths count the same as 8, as they
    have no room either;
  * nodes of 4 klongs count 11.7 a level (65.4 %);
  * keys that share their first 14 segments count 8.55 a level
    (44.0 %);
  * puts count 4 a level (22.1 %).
* **`RealTreeProbe.java`** (package bergdb.dag) works on trees that PE
  built, in memory, at node sizes 8, 14 and 30. A key K has six
  segments, and each of its segment trees holds 30,000 other entries:
  180,000 keys, put in transactions of 1,000 in random order, then
  thinned by deleting 60 % of them. V1, V2 and V4 hold (`checkFill`).
  K's paths have 9 key nodes in each of its segment trees at node size
  8, 6 or 7 at 14, and 4 at 30.
  * One delete of K: Java counts 691 and 697 at node size 8, under the
    770 of the worst tree of the same heights; 312 and 337 at 14
    (against 348 and 401); 174 and 163 at 30 (against 206).
  * 500 deletes at random: 8.1, 5.3 and 4.1 nodes a level, and 39 to 63
    times the key nodes PE marked.
* **`run.sh`** runs both. The output is in `out/`.
* **No test through `Db.execute()` at the release's limits.** It would
  need a database whose segment trees are 62 high, 2^60 klongs: not
  possible. The probe calls the same count on the same shape.


Options
-------

Nothing within L1 to L5 is refused by the 7/8, so the admission needs no
change; the options are about what the documents and the proofs say. The
public limits (L1 to L5) and the node sizes that DbBuilder offers are
Frans's. No option changes the stream format.

* **(A) The text, and a guard test. Recommended.**
  * 031-06, sections 3 and 9, and 024-17, 5.2, 5.2a and 5.3, say what
    holds:
    * the 7/8 suffices by Java's count, which Db compares (76.5 % of it
      at worst, at node size 8);
    * 024-17's count with q holds at node sizes 8, 30 and 62, and at 14
      it needs 10 a level since 028-21;
    * the Lean's 19 is a looser bound of the same count, by which the
      worst action is 106 % of the 7/8, so `releaseFits8` shows 15/16
      only;
    * section 3's mixed record, by Java's count.
  * A test in `DagTester` of this probe's worst path, made the same way
    at H = 61 with a few keys, takes milliseconds. It checks Java's
    count against 14, 10, 8 and 8 (H + 2) S + 14 n at the four node
    sizes, so that a change that raises the count fails a test, as
    028-21's change raised it.
  * Touches: 024-17, 031-06, this entry, and
    java/src/bergdb/dag/DagTester.java (about 100 lines). No change to
    the API, the format, the limits or the proofs. Gate: BEFORE COMMIT
    OK.
* **(B) A, and the Lean's count restated from Java's.**
  * `nodesALevel` becomes 6 + p*, where p* is the largest fixed point of
    p = 2 + max(floor((4 + p) / q), ceil((4 + p) / (M / 2))), Java's
    parts a level on a full path. That is 14 at node size 8, 10 at 14,
    and 9 at 30 and 62. The 6 is the node, its 4 merge nodes, and one
    for the collapses and the new roots. It covers Java's count of a
    middle segment at the four sizes (882 against 869, 400 against 365,
    216 against 186, 162 against 137).
  * A new theorem says that an action fits 7/8 (`ActionFits`, by
    `decide`, beside `ReleaseFits`): 78.4 % at node size 8.
  * Touches lean/SIS/Tree/Bound.lean: the definition, its docstring and
    four theorems. TP26 (`DirtyBoundFromLimits`) stays stated. treetest
    and C-T8 (level2.sh) then check the sharper count on every traced
    transaction, at the model's test sizes too. Nothing in
    lean/contract/ uses `nodesALevel`.
  * Gate: `lake build`, treetest, LEVEL 2 OK.
* **(C) A smaller L3 at small node sizes** (the brief's (a)). For the
  Lean's 19 to fit the 7/8 at node size 8, S must be at most 8,170, so
  L3 at most 53,690 bytes.
  * That is under 500 x 111 = 55,500 bytes, so L3 would refuse
    transactions within L1 and L2, against L3's rule (024-17, 6.1).
  * A smaller L1 does not help: one key at L3 alone is 100.2 %.
  * Limits by node size go against one set of limits for every node
    size (024-17, QL12 (a)).
  * Not needed.
* **(D) A larger room for actions** (the brief's (b)). The Lean's worst
  action, 1,998,975,872 bytes, is 93.1 % of the record limit. Under the
  15/16 that leaves the step 14.3 MB: about 74,000 nodes at node size 8
  (about 300 segments of copies), in place of 1/16 (134 MB). Steps would
  then be shrunk often (`Reclaim.plan`). Not needed.
* **(E) A smallest node size of 14** (the brief's (c)). DbBuilder would
  no longer offer 8, which removes a size that users can choose. Node
  size 8 is the smallest size of DagTester and of the model (028-38).
  The worst action would then be 48.2 % by Java's count and 69.4 % by
  the Lean's. Not needed.
* **(F) A refusal by the room, stated** (the brief's (d)): 005-31's
  DbException, documented as one that a transaction within L1 to L5 can
  meet. By Java's count no such transaction exists, so the documents
  would warn of something that does not happen. The check stays as a
  guard for changes of the count or of the limits. Not recommended.
* **(G) A height budget in the Lean's count.**
  * The segment trees on one transaction's paths are different trees,
    which together hold under 2^60 klongs, so they cannot all be 61
    high. At m = 2 and 8,692 segments, their mean height is at most
    about 48, and by the Lean's 19 the worst action is then about 85 %
    of the 7/8.
  * This needs a new form of `Limits.dirtyNodes` and of its theorems:
    more work than B, for less.
  * Not needed with B.

Recommended: A for 2026.7, a text change and a test that take an agent
about a day; and B with the next change to the Lean's tree bound. None
of C to G.


Log
---

2026-11-27. Registered by lead-1127, from the investigation of BergDB's
own long keys under "/#" (an agent of lead-1127, 17:20 to 17:28,
read-only).

2026-11-27. Investigated by an agent of lead-1127, 18:52 to 19:20, on the
branch `028-72-count` in a clone (Finding; the probes in this directory):
by Java's count no transaction within L1 to L5 is refused by the 7/8 at
any node size (76.5 % at worst, node size 8); 024-17's 14 bounds Java's
count at node size 8, the Lean's 19 is a looser bound of it; 024-17's 9
at node size 14 is short since 028-21. Frans: decision (Options). The
entry became a directory, with the probes.
