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
  `94a1520`, with 021-11; its section 2.1): what changed in Java's Core,
  what C needs, how C is tested before the tag, what may still move, the
  steps, decisions D1 to D7; its log records the port, step by step, and
  the re-pins.
* [03-report-2026-3.md](03-report-2026-3.md), 022-03: the report of the
  port to 2026.3 (022-01): what changed, the evidence, the faults found in
  C and in Java, the known cases, the departures, the size and the time;
  step 5's long runs to be added.
* [04-report-2026-4.md](04-report-2026-4.md), 022-04: the report of the
  port to 2026.4 (022-02), on `main` as pinned until the release
  candidate: what changed, the evidence, the faults found in C and in
  Java, the departures, the size and the time; the candidate and the long
  runs to be added.
* [c/](c/): BergDB's Core in C.


Log
===

2026-11-09. Created the item, by coord-1109.

2026-11-09. `c/` copied from 012 at `be51a78`; 022-01, the plan, from
coord-1109's of 10:18. By the session `022-bergdb-c`.

2026-11-09. 022-02's step 5: `c/readme.md`'s "Which Java" for 2026.4
(its pin in one line, for the re-pin to the release candidate), 022-02's
decisions as taken, and the report 022-04, with the candidate and the
long runs to be added. By the session `022-bergdb-c`.
