028-51. Fix: maintain()'s rule M1 stops beginning iterations in a written database
===================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: `maintain()`'s rule M1 (`Db.maintain()`, `Reclaim.maintain`;
027-13, section 1.10) begins a reclaim iteration only if the new
iteration's cut would release at least `MAINTAIN_MIN_RELEASE` (400 kB),
that is, only if lastPStart - fp is at least 400 kB, and writes change
neither. Once the last iteration is cut, fp is the pStart of the one
before it (its own, for the first). So if the two began within 400 kB
of each other, as when the clock begins them about a quarter of R apart
in a slowly written database, `maintain()` begins no iteration until
the growth rule of commits (more than 2 sd since the last began) begins
one. Found by 028-47's study, section 6, F1.

Why: `maintain()` is the way that 028-47 recommends, and Frans kept
(028-47, option A), for a database written slowly after a mass delete;
F1 limits it. `SlowDriveProbe 50000000 1 300 twin maintain` (028-47's
`probes/`) on `main`: sd 50 MB, one key of 900 bytes overwritten 1,000
times an R, `maintain()` until false after each commit. After the first
cut kept grew to 93 MB by 90 R, fell to 12 MB when the growth rule began
an iteration at about 100 R, grew again to 98 MB by 180 R, and stayed
near 3 MB from 190 R on. G5 of `CountGates` does not see it: its drive
has no writes.

Frans: none, unless the fix changes what `maintain()` promises; then a
decision, with the options in full.

Done when:

* The entry says, with the sentences quoted, whether F1 breaks what the
  Javadoc of `Db.maintain()` and of the Pub's `Database.maintain()`
  promises (such as "Calls of this method begin iterations and do their
  steps by the clock, without that growth", and the 400 kB of an emptied
  database), and of `Db.setRetainDuration()`; if it does, an RB entry in
  033, with its severity (033's rules: a fault that can be considered a
  bug is registered, Frans, 2026-11-24).
* A fix, with a test that fails before it and passes after it (such as
  F1's case at a size that runs in seconds, or a `CountGates` gate on a
  drive with writes), and the texts that describe M1 (027-13, section
  1.10; the Javadoc) as the code then is.
* `java/before-commit.sh` prints BEFORE COMMIT OK; as the change needs,
  `java/stress/conformance.sh reclaim` CONFORMANCE OK, `StreamDigest`
  (the streams that change, and why), and `java/stress/count-gates.sh`
  COUNT GATES OK.
* If the fix changes what `maintain()` promises: the options in full in
  this entry, status in progress for Frans's decision, nothing landed.

First step: read 028-47's study (sections 3 and 6), 027-13, section
1.10, `Reclaim.maintain` and `Reclaim.cutPending`; run `SlowDriveProbe`
as above, then find a smaller case that shows the stall.


Log
---

2026-11-24, 12:30. Registered by an agent of lead-1124, from 028-47's
finding F1 (Frans, 2026-11-24, 12:30).
