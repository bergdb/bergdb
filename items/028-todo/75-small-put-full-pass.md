028-75. Decide: one small put, then maintain() calls rewrite the whole live data
==============================================================================

Status: open. Kind: Decide. Frans: decision.
Created 2026-11-27 by Frans Lundberg.

What: `Reclaim.passDue` (`Reclaim.java`, M1 of `planPart`) begins a
pass when no iteration runs or waits for its cut and the stream kept
holds a record of the application's (`appA` at or after the first
available position). A pass that a call begins cuts at its own start:
it rewrites every live value stored before it. That is 031-04's design
("no drain, no MIN_RELEASE"), which came to `main` with A2 (Frans,
2026-11-27, 14:36: `maintain(int budget)` replaces `maintain()`) and
031-06's merge (`5b88cc80`). Until that merge a call began an iteration
only if its cut released 400 kB (028-51, 028-62).

So one put of a byte, followed by `maintain(budget)` calls, rewrites the
whole live data. Measured by the independent review of 031-06's landed
diff (2026-11-27, `review-main.md`, R4), with
`review-main-probes/RmPassProbe.java` (`runs/pass.txt`), at the
release's limits: a database brought to rest by calls, one put of 1
byte, calls until five in a row write nothing; three rounds each.

* 20,000 keys of 100 bytes (about 2.3 MB live): the put's record 568 to
  624 bytes; the calls then wrote 4.40 to 4.43 MB; the stream kept 4.36
  MB before and 4.35 to 4.38 MB after.
* 100,000 keys of 200 bytes (about 21.6 MB live): a record of 576 to 648
  bytes; 31.9 MB written; the stream kept 32.0 MB before and 31.6 to
  31.7 MB after.

An application that writes a little and calls `maintain(budget)` when
idle rewrites its live data about once a retain duration: the calls go
quiet once the pass is cut, and the next small write begins the next
pass. At 100 GB of live data that is 100 GB written for each such write
that comes after the last pass was cut.

Why: the cost of a decided rule, not a fault of one record an action
(031-06): the calls end by construction (RB-007 and RB-006's rest fixed,
033), at the price of a full rewrite for any write. BergDB is optimized
for large databases first (1M to 100M keys); a rewrite of everything
for a byte is the worst case of write amplification. It belongs to the
landing's step 3, the pace (031-06, section 9).

Frans: decision. The rule is part of 031-04's design that A2 took; a
change of when a call begins a pass changes what `maintain(budget)`
promises. The options:

* **(a) Keep the rule.** No change. The calls end by construction, with
  no threshold to tune and none of the cases of RB-006 and RB-007; an
  application that writes a little between idle calls pays a rewrite of
  its live data each retain duration. State it in `maintain(budget)`'s
  Javadoc and in 027-13.
* **(b) A threshold of released bytes again.** A call begins a pass only
  if the bytes its cut would release are at least a fixed amount, 400 kB
  as before the merge. The bytes a cut releases are not known before the
  pass's scan; an estimate (the stream kept less the live bytes of the
  last scan) brings back a judgment of when there is work, which is what
  031-04 removed. RB-006 and RB-007 came from such judgments: with a
  fixed threshold, an emptied database again keeps up to the threshold,
  and the cases at its edge (two stretches, an iteration within 400 kB of
  its cut point) need their own care and probes.
* **(c) A pass when the stream kept is a share over the live data.** A
  call begins a pass only if the stream kept is more than k times the
  live bytes (for example k = 1.5) and more than a floor in bytes over
  them (for example 400 kB): both. The live bytes must be those of the
  stream kept, not a stale count: the last scan's sum with the
  application's writes and deletes since, kept by each record (a count
  from before an emptying would leave RB-007's case), so the decision is
  a function of the stream (P2). A small put leaves the share near 1: no
  pass. An emptied database (RB-007's case) has a large share: a pass,
  and the calls end within the floor of a fresh database's stream, as
  now. The cost of a write is then bounded by k: the stream kept grows
  to about k times the live data before the calls rewrite it. To be
  designed in step 3 and checked with RB-006, RB-007 and RB-010's probes
  (033's `probes/`), 031-04's cases and `RmPassProbe`.
* **(d) A pass that cuts at the iteration before's start**, as a
  commit's iterations do (pCut the pStart of the iteration before): a
  call's pass then rewrites only what the last pass left. Brings back
  the iteration that waits for its cut, RB-007's cause; not recommended.

Recommendation: (c): it bounds the cost of a small write by the share,
keeps the calls' end by construction for an emptied database, and keeps
the decision a function of the stream. Its k and floor are measured in
step 3.

Done when: Frans has chosen; for (b) or (c), the rule built in the
landing's step 3 on `main`, with the probes above and `RmPassProbe`
showing a small write's cost, and `before-commit.sh`, the level scripts
and the item's sweep green; for (a), the Javadoc and 027-13 say the cost.

First step: Frans's choice.


Log
---

2026-11-27. Registered by lead-1127, from the review of 031-06's landed
diff (R4).
