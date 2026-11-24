028-52. Investigate: CountGates' G4 fails ST6 at C2's settings
===============================================================

Status: in progress. Kind: Investigate. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: G4 of `CountGates` (`java/stress/count-gates.sh g4`) at 026-13's
C2 settings, `g4sd=1000000 dt=50000` (a startup distance of 1 MB, R =
200 drive transactions, 40 R), fails its gate ST6 on `main`: the
emptied database's cache table slots are 62,912 against the twin's
25,488, 2.47 times, over the limit of 2 (`g4slots`). The gate passes at
G4's own settings (sd 100 kB, R = 1,000). The same holds with 028-47's
options B and B2 (2.40 to 2.47 times). Found by 028-47's study,
sections 1 and 6, F3.

Why: either the gate is wrong at these settings (it compares slots that
depend on the cache's history, not on what the database holds), or the
emptied database keeps cache tables that it should shrink (024-33, ST6;
the tables shrink to `Table.MIN_CAPACITY`), which G4 at its own
settings does not reach. At C2's settings G4's lag gate fails too
(14.8 R against 2 R), as the cut waits for the startup pos (028-47,
section 3); whether ST6 follows from that is part of the question.

Frans: none.

Done when: the entry says why ST6 is 2.47 times the twin's at C2's
settings (which maps hold the slots, and why they have not shrunk), and
whether the gate or the database is wrong; with the run's lines quoted.
If the database is wrong, a 028 entry for the fix (and an RB entry in
033 if it is a fault of a released version, 033's rules); if the gate,
its fix or a note in `CountGates` on the settings where it holds.

First step: read 028-47's study, section 1, `CountGates.g4` and
`Cache3`'s shrinking (024-33); run `count-gates.sh g4` with
`g4sd=1000000 dt=50000` on `main` and print the slots by map for the
emptied database and the twin.


Log
---

2026-11-24, 12:30. Registered by an agent of lead-1124, from 028-47's
finding F3 (Frans, 2026-11-24, 12:30).

2026-11-24, 12:35. Taken by an agent of lead-1124 (in progress), in a
clone of `main` at 6d1d7805, on the branch 028-52.
