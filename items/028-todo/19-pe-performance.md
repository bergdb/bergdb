028-19. Measure and change: PE's speed and reclaim's pace with PE
==================================================================

Status: open. Kind: Change. Frans: decided (2026-11-19, 09:32).
Created 2026-11-19 by Frans Lundberg.

Frans, 2026-11-19, 09:32, on merging Java's PE (026-25): "Yes, do it. As
recommended including the follow-up." The follow-up, as recommended: an
optimization round of PE's Java writer and a look at reclaim's pace with
it. 09:25, before the decision: "Is there room for optimizations still?
[...] Could performance end up as good as or even better than main after
optimizations?"

What, from 026-25 (sections 6 and 7):

* **The short way** (small transactions): `PeWriter`'s short path builds
  the leaf's whole live list (`PeWriter.live`) and an `IdentityHashMap` a
  transaction; when the leaf is full the try is wasted and the plan and
  emit follow. CORE's set is 11 to 18 % slower than with the old writer
  (1.94 against 1.75 µs a transaction, quiet F53). Decide the leaf by
  counts, without the list; detect a full leaf before the try.
* **The plan's allocations:** a VN object a node and a leaf's changes are
  garbage at a transaction's end: GC time and RSS about 10 % above the
  old writer's. Work arrays for a leaf's changes; VNs reused between
  transactions; emit reusing what plan found on the path.
* **The load:** 0.90 to 0.97 of the old writer's puts a second at 10M
  keys.
* **Reclaim's pace:** at 10M keys with reclaim, PE made 3 physical cuts in
  6M transactions against 1, wrote 6.8 % more bytes a put although its
  user records are 16 % smaller, and its worst commit was 1.2 to 1.8
  times longer. Find why (reclaim's pacing on PE's tree shapes, or the
  reclaim row's bytes, 026-25 section 2) before changing anything.

The rule: an optimization that keeps the trees (node for node the proved
writer, `Contract.PE.peTx`) needs no proof work; the level scripts check
it against the oracle. One that changes the trees (such as an uneven
split for sorted appends) changes the model's writer and its proof
(030-21) too, and needs Frans's word first.

Done when: each point above measured before and after on a quiet machine
(F53 or s1, as 026-25 section 7), changes gated (`java/before-commit.sh`,
`level1.sh` to `level4.sh` with the PE oracle, kill-restart, CORE and the
10M timing again), reclaim's pace explained, and the result written here:
how close to the old writer, or better, each point came.

Sources: 026-25 (sections 2, 6, 7), 026-24, 030-21.


Log
===

2026-11-19. Registered by coord-1118 at Frans's word (09:32).
