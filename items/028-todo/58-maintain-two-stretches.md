028-58. Investigate: maintain() leaves an emptied database at 790 kB, two stretches each below 400 kB
=====================================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `maintain()`'s M1 (`Reclaim.maintainBeginDue`; 027-13, section
1.10) tests its two stretches one by one, the stream from fp to the
last pStart and the stream written since the table's last store, so
each can stay just below MIN_RELEASE (400 kB) for good. Found by the
review in 031-03 (section 9.1): `TwoStretchProbe 390000 390000 390000
10000 20000` (a value put and deleted on each side of the second
iteration's pStart) keeps 790,264 bytes on `main` after 20 R of calls,
789,560 more than a fresh database; 028-53's B keeps the same; 031-03's
one threshold (its R4) keeps 19,480.

Why: the Javadoc of `Db.maintain()` and `Database.maintain()` says the
calls bring an emptied database to within about 400 kB of a fresh
one's stream; 024-30's G5 allows 600 kB. If 2026.5 and 2026.6 keep the
same, a released bug (033's rules; S4, disk space only, as RB-006 and
RB-007).

Frans: none for the investigation. The fix goes with RB-007's (031-03,
decided by Frans), unless he decides otherwise.

Done when: `TwoStretchProbe` (031-03's probes) run on `main`, 2026.6
and 2026.5, the bytes kept quoted; whether it breaks the Javadoc; if
so, an RB entry drafted for 033; the fix named (031-03's R4, or a
change of `main`'s M1 alone) with what it costs.

First step: 031-03, sections 3.4 and 9.1, and its `TwoStretchProbe`.


Log
---

2026-11-25. Registered by lead-1125, from 031-03, section 9.1.
