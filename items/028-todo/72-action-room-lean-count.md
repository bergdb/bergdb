028-72. Investigate: the action's 7/8 against the worst action by the Lean's node count
=======================================================================================

Status: open. Kind: Investigate. Frans: none.
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

Frans: none.

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


Log
---

2026-11-27. Registered by lead-1127, from the investigation of BergDB's
own long keys under "/#" (an agent of lead-1127, 17:20 to 17:28,
read-only).
