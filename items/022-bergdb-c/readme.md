022-bergdb-c
============

Created 2026-11-09 by Frans Lundberg. Status: open.

BergDB's Core in C, updated to Java's releases: first 2026.3, then
2026.4, maybe later ones. A fresh start from 012's C clone, which stays
the port of release 2026.2; 012-18 is the feasibility study for 2026.3.

Frans, 2026-11-09, 10:08: "D1. Create a new item for the updated C port,
release 2026.3 (then 2026.4). This allows us to leave some history behind
and start fresh. Call it nnn-bergdb-c. I will decide later how long to
update it in that item, at least 2026.3 and 2026.4, maybe longer."

The code is in `c/` ([c/readme.md](c/readme.md)), copied from
`items/012-bergdb-c/c/` at `be51a78`, 012's last commit to it (the port
of release 2026.2); 022-01, section 1.


Files
=====

* [01-plan.md](01-plan.md), 022-01: the plan, 2026.3 and then 2026.4;
  the steps, the clones, the gate and how the work lands.
* [02-update-to-2026-4.md](02-update-to-2026-4.md), 022-02: the study of
  the port from 2026.3 to 2026.4, from the candidate (`main` at
  `770d88b`): what changed in Java's Core, what C needs, how C is tested
  before the tag, what may still move, the steps, decisions D1 to D5.
* [c/](c/): BergDB's Core in C.


Log
===

2026-11-09. Created the item, by coord-1109.

2026-11-09. `c/` copied from 012 at `be51a78`; 022-01, the plan, from
coord-1109's of 10:18. By the session `022-bergdb-c`.
