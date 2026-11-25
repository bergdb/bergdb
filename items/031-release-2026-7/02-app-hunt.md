# 031-02. An app hunt on main before 2026.7

Created 2026-11-25 by Frans Lundberg. Status: open.

A hunt for faults with new user applications, written as a new user
would write them, from the README and the Javadoc only, each with an
oracle of its own, run on the release jar of `main`. Apart from the
earlier hunts (024-26, 026-13, 026-26), whose apps it does not read; it
stresses most what changed since 2026.6: STM's record of recent writes
(028-01, 028-48), transactions with key transformations near the
record limit (028-50), `maintain()` (028-51), and the index writer's
short way and routing (028-19). Findings are named by severity as in
026-26: S1 data lost or wrong, S2 a database that fails or cannot
start, S3 a call refused wrongly, S4 minor or documentation.


Log
===

2026-11-25. Created by lead-1125 (006-35): fixing bugs comes first, and
no bug is known on `main` but RB-007; an app hunt is the method that
found most of 2026.4's bugs.
