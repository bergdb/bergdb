028-59. Investigate: a stop or a crash between the filler's put and delete leaves it live
========================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `maintain()`'s filler (M5, 024-32) is a put of
`/#i/dreclaim/-fill.txt`, up to 200 kB of zeros, and a delete of it in
a later record. A stop or a crash between the two leaves it live until
another filler is needed, though 027-13, section 2, says that it is
never live after a call. Found by the review in 031-03 (section 9.2):
`StopAtProbe 10 100 20000` in `main`'s mode: after the stop and 20,000
calls, the filler is live, 199,672 bytes kept. 031-03's design stores
the filler as the table padded with spaces, one record with nothing to
delete.

Why: a document of the code (027-13) that the code does not meet, and
up to 200 kB kept in a database that should return to empty; whether
it breaks a promise of the Javadoc (within about 400 kB of a fresh
database, with other overheads) decides whether it is a released bug.

Frans: none for the investigation. The fix goes with RB-007's (031-03),
unless he decides otherwise.

Done when: `StopAtProbe` run on `main`, 2026.6 and 2026.5, with a stop
and with a crash; whether a promise of the Javadoc is broken; if so,
an RB entry drafted for 033; 027-13, section 2 corrected to what the
code does, or the fix named.

First step: 031-03, sections 3.2 and 9.2, and its `StopAtProbe`;
024-32 (M5).


Log
---

2026-11-25. Registered by lead-1125, from 031-03, section 9.2.
