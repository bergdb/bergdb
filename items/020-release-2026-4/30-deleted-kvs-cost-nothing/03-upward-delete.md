# 020-30-03. Option A: the delete goes upward

Agent a30 of coord-1110, 2026-11-10, phase 1 (an overview, not a proposal).
Read-only study of `main` (`12fcb7ba`). Code places are in `java/src/bergdb/dag/`
unless named. KeyNode's search code is the same in `release-2026.3` (only messages differ).

## 1. How a key maps onto nodes

* A key is a list of 7-byte segments. Segment i is looked up in a segment tree: inner
  nodes (`isSegmentLeaf()` false) route with `searchLte` (Dag.java:783, 849); the segment
  leaf is searched with `searchEq` (Dag.java:858). In the leaf, the klong of the last
  segment points to a value node; the klong of any other segment points to the root of
  the next segment's tree (`setNode`, Dag.java:842; a new segment tree starts as one leaf).
* An inner node's klong is the lower bound of its child, not a key. Roots made by a space
  split start with `Klong.EMPTY_KEY` (Dag.java:1139, 1256, 1281); space-split-1 gives the
  parent the old klong for the first half and the second half's first klong
  (Dag.java:1314). Invariant used by every put: an inner node has a live klong at or below
  any key routed to it, else `checkFound` (Dag.java:835) fails the database.
* Today a delete bit is set only in the segment leaf of the key's last segment
  (`setValue` -> `appendDeleteKlong`, Dag.java:794, 899). But nothing ties the bitmap to
  leaves: `appendDeleteKlong` works on any KeyNode, and all searches apply the bitmap at
  the lookup time in any node (`getDeleteBitmapAtTime`, KeyNode.java:1845; searchLte
  KeyNode.java:466). The bitmap is cumulative (`union`, Dag.java:955) and deletes every
  klong with that compare value, so an older shadowed klong of the same child (left by a
  time split, Dag.java:1172) does not come back.

## 2. Option A step by step

1. The emptiness test. In `appendDeleteKlong`, with `union` known: the node is empty at tt
   if no KEY klong is outside `union`. One more pass over at most 62 klongs, the same loop.
2. If not empty: as today (bitmap, or a split via `lastVersionGivenDel`, Dag.java:972).
3. If empty: do not write the node at all (no bitmap, no split; today an emptied full node
   is time-split into a node with only a TIME klong, Dag.java:1071, 1172). Instead call
   `appendDeleteKlong(parent, depth - 1, compareValue(keyAccessPath.getKlong(depth)))`,
   the same way the splits find the parent (`pd.getParent`, PutData.java:93). Repeat.
4. A parent that is a segment leaf (the node was a segment root): this is the same as
   deleting a segment. `setNode` already treats a deleted segment klong as absent and makes
   a new segment tree on a later put (Dag.java:858-878); a delete of a key there is a noop.
5. A parent that is an inner node, klong K_i not its smallest live klong: delete it. A
   later put of k in [K_i, K_i+1) gets the previous child C_i-1 from `searchLte`. Safe for
   order: all keys of C_i-1 are below K_i <= k < K_i+1. Scans move between children with
   searchGt/searchLt on the parent (GetMany.java:345-353), which skip K_i; gets use
   searchLte (Dag.java:432). Readers before tt still see K_i and the old child.
6. **The smallest live klong of an inner node is the problem.** Deleting it while the node
   has other live klongs breaks the invariant of section 1: a later put of a key below the
   next live klong finds nothing (`checkFound`), a get returns "not found". This is the
   common case: a FIFO, a job queue, a time-ordered index delete at the left edge. Two
   ways out:
   * A-keep: do not delete it; the empty leftmost child stays (it gets its bitmap, as
     today). At most one empty chain of nodes per live inner node, down to an empty leaf.
     Bounded by the live tree (FIFO: about h^2 nodes, h the height), not by the deletes,
     but not zero, and scans pass it.
   * A-relabel: append a klong with K_0's compare value pointing to C_1, and delete K_0 and
     K_1. If C_1 is an inner node its smallest klong is above K_0, so the same relabel goes
     down C_1's left edge, one node per level. O(h) node writes, once per emptied leftmost
     child. Keeps the format and the invariant; nothing is left.
   (A third way, "an inner node's smallest live klong covers every key below it", changes
   searchLte and the reading code: 2026.3 would not find such keys with get; rejected.)
7. The space root (parent null, depth 0). Leave it, or when it has no live klong, make an
   empty segment leaf the new super root with `topDs.newSuperRoot` (as in time-split-2,
   Dag.java:1197). One node either way. TopNode/TopDs need no change.

## 3. Can 2026.3 read it?

* Reads: yes, if the invariant is kept (A-keep or A-relabel). The stream reader accepts a
  DELETE_BITMAP in any key node (core/StoredKeyNode.java:174). searchLte/Gt/Lt/Gte/First
  and `getMaxValidTime` (KeyNode.java:1899) apply it in any node at every lookup time;
  `lastVersionGivenDel` drops deleted klongs of inner nodes too. Scan setup copes with a
  node with no klong at or below the start key (GetMany.java:266).
* Writes by 2026.3 on such a database stay consistent (its deletes just do not climb).
* Risk, to check: the startup rerun. DbStarter reruns the stored tail with the opening
  version's `putKv` (core/DbStarter.java:358) and must create the same node ids (the noop
  comment, Dag.java:764). A 2026.3 rerun of an option-A delete writes the leaf (and may
  split it) where main wrote the parent: other nodes, other ids. Probably safe after a
  clean close if nothing is rerun; not verified here. The same applies to the C clone.

## 4. Costs and interactions

* Per delete: the emptiness test is O(node size), in a loop that runs anyway. The climb
  runs only when a node empties; a node empties once and then gets no writes, so the climb
  is O(1) amortized per node created. Worst case one delete: the sum of the heights of the
  segment trees on its path (a long key with unique tail segments). A-relabel adds O(h)
  writes per emptied leftmost child. Fewer bytes than today: emptied nodes are not written.
* Splits in the same transaction: the parent may be full; the delete then goes through
  `handleFullNode` (Dag.java:1058) with no klongs to insert, as for leaves today. Keys of a
  transaction are sorted and unique (core/Trans.java:481), so later keys see the deletes:
  searchLte at tt includes the bitmap of tt, and `lastVersion` drops the deleted klongs.
* **newInTrans** (Dag.java:1069): a node made at tt (a new segment leaf, or a space-split
  half holding older keys) can be emptied later in the same transaction. Deleting its
  parent klong leaves a node the transaction created unreachable at tt, against the rule in
  the comment of `handleFullNode` (assumptions A2 and A3 of the Lean model). Needs a rule:
  stop the climb there, or remove the parent's klong of tt in place and drop the node from
  the record (no reader sees klongs of tt). Open.
* `dirtyNodeBound` (Dag.java:477) counts a delete as one klong in the leaf (Dag.java:500).
  The climb adds klongs to ancestors (already counted as dirty), and A-relabel dirties
  nodes off the path: the bound must grow (about h per delete), or Db's check before the
  go point underestimates.
* Readers: no new protocol. A bitmap appended to an inner node is a klong of tt behind its
  TIME klong, which readers before tt never pass (KeyNode class comment); in-place update
  of the transaction's bitmap is the same as in leaves (Dag.java:960).
  `lastVersionGivenDel` keeps its monitor (KeyNode.java:1091). Unreachable nodes stay in the
  cache until evicted; readers at older times may still follow them.
* Reclaim: its touch is a scan at tt (core/Db.java:2944), so it no longer reaches dropped
  subtrees and does not copy them forward; the cut frees them after the retain duration.

## 5. Variants

* Segment level only: climb only from a segment leaf that is its tree's root into the
  parent segment leaf. Cheap and no invariant issue (segment leaves use searchEq). Fixes
  deleted long keys with small tails; does nothing for many deletes inside one big segment
  tree (FIFO, 020-24-16, 020-24-17).
* Also inner nodes: needed for Frans's scan bound. Needs A-keep or A-relabel (2.6).
* Lazily at the next time split: a node emptied by deletes gets no more writes unless keys
  come back to its range, so in a FIFO the split never comes. Not enough alone. The lazy
  hook that does work is reclaim's touch, which visits every node of its range at tt
  anyway; it could drop the klongs of empty children there (see 020-30-01).
* Suggestion for phase 2: A-relabel with the climb in the delete, the newInTrans rule, the
  dirtyNodeBound change, and a rerun check against 2026.3.
