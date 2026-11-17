# 020-30-01. The reclaim side

By agent r30 of coord-1110, 2026-11-10, phase 1 (a first overview, read-only;
nothing built or run). Code on `main` (`772c1e5a`). Places are file:line in
`java/src/bergdb/`.

## 1. What reclaim does today

* **Values of deleted keys.** A step scans live KVs at tStart (core/Reclaim.java:560,
  579) and rewrites a value only if it is live at the step and stored before pCut
  (core/Reclaim.java:622). A deleted value is never copied; the cut at pCut frees it.
  This part already meets Frans's rule.
* **Nodes and klongs of deleted keys.** The step's internal transaction touches its
  key range at the current time (core/Reclaim.java:674-676; core/Db.java:2909, 2944):
  a scan as the writer whose pointer listener makes every index node it follows
  dirty, so it is written again at pStart or later. The scan follows every live
  klong, and a parent's klong to a node of deleted keys only is still live
  (020-30, section 3), so such nodes and the segment subtrees of deleted long keys
  are copied forward on every iteration, with their deleted klongs and delete
  bitmaps. Nothing drops them: a dirty node is written as it is; only a time split
  of a full node drops deleted klongs (dag/KeyNode.java:1091, dag/Dag.java:1058).
* **Why the Q7 fix copies them.** The cut is safe only if every node reachable at
  times from tEnd on is at pCut or later, or dirty (core/Reclaim.java:52-55). Nodes
  of deleted keys only are reachable at the current time; before 2026-10-13 they kept
  their old positions, and after a cut a lookup in their range followed a pointer
  into the removed stream (011-01, Q7). Copying them was the simple safe fix.
* **The touch's end.** Its stop condition sees live KVs only (core/Db.java:2979,
  called at dag/Dag.java:688), so it runs on to the first live key after touchTo,
  past every key deleted since tStart (021-25, "Cause", part 2).

## 2. Reclaim alone (no upward delete in the transaction)

Possible in principle. A step would, inside its touch at the current time:
1. On the way back from a node, know whether its subtree has a live klong. If
   not, delete the parent's klong to it (a delete bit in the parent, at the
   step's time ts) in the step's internal transaction, and not make the node dirty.
   Lookups before ts still reach it; lookups from tEnd on (tEnd >= ts) do not, so
   the cut's invariant holds without the copy.
2. Compact each node it rewrites: drop klongs deleted before the first available
   lookup time F, and klongs replaced before F (versions no read can ask for).
3. End the touch at touchTo (fix (a)), on keys passed, not on live KVs.

How long. A delete at td. The next iteration starts within R/4 and a growth of
twice the startup distance (core/Reclaim.java:460-462); its step over the key's
range prunes the empty node at ts. That node was last written by the iteration
before, at or after this iteration's pCut, so this iteration's cut keeps it and the
next iteration's cut frees it: about R plus 2 iteration spans after td. The pruned
klong in the parent goes when a step compacts the parent after F > ts (after the
first iteration's cut, about R later), and its old bytes go two cuts after that:
about 2R plus 3 to 4 spans. A parent emptied by the prune is found by the next
iteration, so a chain of h levels adds up to h quarter-R starts (less if a step
checks a node after its last child). No writes, no iterations: an idle database
never gets there.

Scans between iterations. Deleted subtrees stay reachable at the current time until
a step passes them: a scan pays for every key deleted in its range in the last
iteration span or two (up to R/4 plus a span, or longer when writes are few). A
queue or FIFO that scans its head after each delete pays this on every scan: not
O(n) amortized. Reclaim alone meets the resource rule eventually, not Frans's scan
bound. Each first step's scan at tStart (021-25, part 1) shrinks to the deletes of
one iteration, not of all history.

## 3. With the upward delete in the transaction

Emptied subtrees are unreachable from the delete's time on. Reclaim then:
* **Stops copying them, with no change of its own.** The touch follows only nodes
  reachable at the current time, so the Q7 copies end; the cut stays safe for the
  same reason as in section 2 (unreachable from td <= tEnd). The Q7 test
  (Reclaim.Tester.testDeletedKeysAfterCut) should still pass and be kept.
* **Still must compact.** Deleted klongs in nodes that keep live keys, the pruned
  klongs in parents, the delete bitmaps and replaced klongs stay until a time split.
  Rule 2.2 of 020-30 needs reclaim (or the next write of the node) to drop those
  invisible from F on, as in section 2, item 2. Old node versions are then reachable
  from no klong visible at or after F, and the cuts free them.
* **Part 2's long touches end.** Between touchTo and the next live key lie only
  nodes with live keys (O(height) of them), so the touch is bounded by live data.
  Part 1 too: the scan at tStart does not reach subtrees emptied before tStart.
  Fix (a) is then not needed for the bound or for the cuts of 021-25's FIFO; it
  stays a cheap way to keep a step's dirtying (and its charge, core/Reclaim.java:656)
  within its range. My advice: do it with the change, not before.
* **Not solved by either:** underfull nodes (one live key each, no merge; 011-01, Q1).

## 4. Risks

* **Cut safety.** pEnd and pSafe (core/Reclaim.java:740, 839) assume every node
  reachable at times from tEnd on was made dirty by the touch. A prune at ts or a
  delete at td, both before tEnd, keeps that true. Compaction must use F as it is
  at the step (the table's cut row), never a pending cut.
* **Lookups within R.** A klong may go only when invisible at every time >= F. A
  read admitted before a cut today expires on a cut byte (core/Reclaim.java:79-81);
  a node compacted in place in memory would instead give it a silently wrong answer.
  Compaction must make a new node (a replacement, as a time split does), or such
  reads must check F after the read.
* **Startup rerun.** The touch is not stored and not rerun (core/DbStarter.java:480);
  only the step's puts are. A prune or compaction made by the touch changes the
  index and must be stored in the record (a format change) or rerun from stored
  state; else INV-RESTART fails. The upward delete in a user delete is rerun with
  the delete, as any put; no new record kind.
* **Crash.** A step stays one internal transaction; the table-before-cut order is
  unchanged. Both ways change the stream's bytes (StreamDigest, the C port, 022),
  the trace format, and the Lean model of reclaim (001-07): its touch makes nodes
  dirty but does not change the index.
* **Routing.** After a parent's klong to an empty child is deleted, keys of that
  range route to the left sibling; puts into the range then land there. To be
  checked with the agent on the upward delete's mechanics.
