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
  **Part of it explained and fixed by 028-26** (2026-11-19): a step's
  row charged only the nodes that its touch made dirty, not PE's new
  nodes (replacements, cuts, joins), so the allowance let reclaim
  rewrite more than f of the growth (Codex's review of PE, finding 1:
  90,832 of 301,856 index bytes uncharged in a probe's first iteration
  at node size 8). Now charged, the row stored again after the step; in
  the probe's workload over 20,000 updates the stream grew 1.5 to 7.8 %
  less, with fewer steps (028-26, Measurements). To remeasure here, as
  026-25 section 7, on F53 and s1: Perf write at 10M keys with reclaim
  (bytes a put, physical cuts in 6M transactions, the stream kept at
  most, reclaim's steps and records, the worst commit), against main
  before 028-26 and the old writer; whether the rest of the 6.8 % and
  the extra cuts remain.

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


Measurements of 2026-11-21
--------------------------

`java/timing.sh` on F53, quiet, `main` at `40cb9ae9` (PE, with 028-26)
against release 2026.5 (the old writer), run `2026-11-21-0800`
(`java/build/timing/`, not in the repository):

* CORE: 0.265 against 0.250, ratio 1.060 (alert above 1.10). The run of
  01:52 the same night had 1.102.
* Pauses (PauseProbe, ZGC): the longest get or commit 14.5 ms against
  14.4 ms (guide 50 ms).
* Writes with reclaim at work, faster: `w10m-fin` +27.4 % commits/s
  (68,936 against 54,104), `r-100-fin` +27.2 % in its mixed phase,
  `w-uni-100-fin` +10.2 %.
* Writes with no reclaim (retain=inf), slower: `w10m-inf` -6.3 %,
  `w-uni-100-inf` -9.7 %; restart after `w-uni-100-inf` 1.98 s against
  1.75 s.
* Reads: -1 % to -5 %; `get_longkey` -5.4 %, the run's one alert
  (unconfirmed, threshold 5 %); `r-100-fin`'s mixed gets -12.3 % (no
  threshold for it).

The rest of the done criterion (each point measured before and after a
change, s1, reclaim's pace explained) is open.


Log
===

2026-11-19. Registered by coord-1118 at Frans's word (09:32).

2026-11-19. Reclaim's pace: the uncharged PE nodes fixed in 028-26; what
to remeasure noted above. By an agent of coord-1118.

2026-11-21. timing.sh's figures against 2026.5 added, by coord-1120.
