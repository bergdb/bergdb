028-66. Investigate: the cut's deletes lag behind a fast writer
================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-26 by Frans Lundberg.

What: since 005-46 the cut's own thread deletes the stream files below a
cut one at a time, forcing the directory after each. 028-62 made a new
file a tenth of the stream kept, not a quarter, so a database has about
three times as many files. In 028-62's measurement (`ReclaimCost`, disk
on, 20 MB live, about 120 MB/s of stream), with 56 to 60 files against
16 to 23, a fast writer stays further ahead of the deletes: the stream
not yet deleted below the cut was 50 to 55 % of the stream kept, against
24 to 44 % with the quarter, and the disk over the stream went from 1.28
to 1.48 to 1.49 to 1.56. The part of the file that the cut lands in fell
from 6.3 % (at most 23.5) to 2.1 % (at most 5.5) of the stream kept.
027-13's 6 to 9 % dates from 2026-10-13, when the deletes were
synchronous.

Why: the disk a database takes beyond its stream; a tenth was chosen to
make it smaller (028-62), and the deletes' lag takes back part of that
for a writer that writes fast.

Done when: the lag measured at a few writing rates, with the quarter and
the tenth; a change such as deleting all the files below a cut with one
force of the directory, measured; or the reason it stays, written here.

First step: 028-62's result and `ReclaimCost`'s `DISK PARTS` line;
005-46 and `FileStream`'s deletion of files at a cut.


Log
---

2026-11-26. Registered by lead-1126, from 028-62's measurement.
