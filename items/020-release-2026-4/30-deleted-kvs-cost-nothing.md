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

By a coordinator's agent at effort max (Frans, 09:03), started
2026-11-10. Its brief, its State note and its findings follow in the
sections it adds below.


## 5. Log

2026-11-10. Created at Frans's request (09:03), with his rule and his
decision to pause 2026.4; the study started (coord-1110).
