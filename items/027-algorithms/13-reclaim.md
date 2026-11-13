# 027-13. Reclaim

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 9 of 027's outline (027-04, section 2.3; levels: 3). How the front of
the stream is cut: the retain duration and its stored settings; an
iteration's start and its positions (pStart, tStart, pCut); the steps,
their allowance by the internal fraction, each one scanning at its own
time (026-05), rewriting live values as puts and touching only the paths
of its own puts (024-07); the iteration's end; the cut's conditions, the
reclaim table, the physical cut and the first available time; reads that a
cut overtakes; `maintain()`.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").
