028-53. Investigate: maintain() keeps rewriting live data in an idle database
==============================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: on `main` before 028-51, an idle database with about 4.5 MB of live
data or more, which has had reclaim iterations begun by commits, keeps
rewriting that data under regular `maintain()` calls: 24.5 MB written per
10 R with no user writes. Found by 028-51 while it compared rules for
`maintain()`'s M1 (its probes, `IdleLiveProbe`); 028-51's rule writes
exactly what `main` wrote in every idle run, so it neither causes nor
fixes this.

Why: `maintain()` on a quiet database should cost little once the stream
holds nothing to give back; rewriting the same live values again and
again costs writes and wear for no space (010-01, P3 and P4). Whether it
breaks what `maintain()`'s Javadoc promises decides whether it is a
released bug (033's rules, Frans 2026-11-24).

Frans: none, unless a fix changes what `maintain()` promises (then
options in the entry).

Done when: the case reproduced on `main` (028-51's probe or a new one),
its cause in `Reclaim` named, the Javadoc of `Db.maintain()`,
`Database.maintain()` and `Db.setRetainDuration()` read against it; if it
breaks a promise, an RB entry in 033; a fix with a test that fails before
it, or the reason it stays, written here; `java/before-commit.sh` prints
`BEFORE COMMIT OK`, with the reclaim conformance, CountGates and
StreamDigest as the change needs.

First step: 028-51's readme and its probe `IdleLiveProbe`, and 027-13,
sections 1.10 and 6.


Log
---

2026-11-24. Registered by lead-1124, from 028-51's report.
