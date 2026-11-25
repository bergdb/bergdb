028-61. Investigate: an emptied database keeps 2 to 3 times the startup distance under maintain()
================================================================================================

Status: in progress. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: 031-02's app hunt, finding F2 (section 5): with a retain duration
of 5 to 24 s and a startup distance of 5 MB, a database whose keys are
all deleted, then not written to, keeps 0.4 to 15.2 MB of stream under
`maintain()` called again and again as the clock moves (RetainChurn,
seeds 1 to 7; 19 of 20 emptied rounds more than 400 kB above a fresh
database's 904 bytes); the first available time stops near the end of
the deletes and stays, 19 minutes behind the clock in seed 1. `java
RetainChurn DIR 5 1` keeps 10,400 kB in about 4 minutes. Release 2026.6
gives the same bytes. 028-53's prototype A2 keeps 9,200 kB.

Why: the Javadoc of `Db.maintain()` and `Database.maintain()` says that
the calls bring an emptied database to within about 400 kB of a fresh
one's stream. RB-007's stated bound is below 2 sd (10 MB here); 15.2 MB
is above it, and A2 does not give the space back, so the case may be
RB-007 with a larger bound, 028-58, or a fault of its own.

Frans: none for the investigation. A fix goes with RB-007's (031-03),
unless it is a fault of its own that needs no decision.

Done when: RetainChurn's case run on `main`, 2026.6 and 031-03's
prototype (`031-03-proto`), the bytes kept and the first available time
quoted; the cause named (why no iteration begins or no cut comes); its
relation to RB-007 and 028-58; an RB entry drafted for 033 if it is a
released bug of its own, or RB-007's text corrected.

First step: 031-02, section 5, F2, and its app RetainChurn (e3);
027-13, sections 1.6 to 1.10; 031-03, sections 3.4 and 7.


Log
---

2026-11-25. Registered by lead-1125, from 031-02's finding F2.
