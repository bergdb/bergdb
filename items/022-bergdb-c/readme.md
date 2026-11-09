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
* [05-java-tests-in-c.md](05-java-tests-in-c.md), 022-05: Java's Core
  tests (891 methods at `main` `2566df1`) read against C's, the valuable
  ones written in C and run, two faults of C found and fixed; the parts in
  [05-java-tests-in-c/](05-java-tests-in-c/).
* [06-user-apps/](06-user-apps/), 022-06: three black-box users of the C
  library (a device store, the error paths, an audit log with retention),
  their reports and what came of each finding.
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

2026-11-09, 19:30. The day's end, by the session `022-bergdb-c` (Frans
allowed no Claude use after 22:00). The port to 2026.3 (022-01) is coded,
gated and documented (022-03); its long runs are tonight's step
`/Users/f/fl/bench/022/night/step5.sh` in coord-1109's night plan (on
int.git `ecc5319`, the final 2026.3 code). The port to 2026.4 (022-02) is
at the release candidate, Java's `main` `03ce6ec5` (022-04, sections 1 to
8); its long runs are `/Users/f/fl/bench/022/night/runs-2026-4.sh` (on
int.git `8772b934`), the night plan's last step, run only if time is left.
Also today: 022-05 (Java's Core tests in C) and 022-06 (three black-box
users and the fixes).

For the morning of 10 November:

1. Read `/Users/f/fl/bench/022/out/night/run.log` (its last line is
   `STEP5 OK` or `STEP5 FAILED`; each part's log beside it): fill 022-03,
   section 9; if it passed, 022-01 is done (its status, its log, the index
   line). A failed part: its log, a fix in a clone, the gate.
2. Read `/Users/f/fl/bench/022/out/night4/run.log` if it ran: fill 022-04,
   section 9; if not, plan the runs for the next quiet block.
3. At Frans's tag of 2026.4: the diff from `03ce6ec5` to `release-2026.4`
   in the Core layer, `JAVA_REF=2026.4` with the release's source zip, and
   D5 (a short confirming run if only `BuildInfo` changed).
4. Frans's open points, with the defaults that went ahead: D7 (C forces a
   new file and the directory as Java does); `GetN(0)` not expressible in
   C's API; `bergdb_close` gives `BERGDB_IO` after a failure already
   reported (Java's returns normally since 019-09); the memory stream now
   frees cut bytes (a change of 012-11's design, 022-05); a read-only open,
   a buffer-size option and a close with an error text (06-user-apps,
   `fixes.md`, section 1.3); C's NOMEM refusal; 015-67's bounded sweep and a
   limits harness, not made. Java's, on his list through coord-1109: 021-25
   (reclaim and a log keyed by time; C follows Java's fix, byte for byte),
   021-27, the still-dirty loop's cost with long keys, U2-6, U2-8.

Where things are: the integration repository
`/Users/f/fl/bench/022/int.git` (branch `2026.4` holds what `main` has under
`items/022-bergdb-c/`; `022` the 2026.3 port; `candidate-2026.4` the Java
candidate), its clones in `/Users/f/fl/bench/022/`, the landing script
`/Users/f/fl/bench/022/land.sh` (its state in `landed.txt`), the users'
applications in `/Users/f/fl/bench/022/apps/` and their kit in
`/Users/f/fl/bench/022/userkit/`.

2026-11-09, 19:35. coord-1109 put `runs-2026-4.sh` before `step5.sh` in
the night's steps (the release's own checks first, then C at the
candidate), in a window that likely leaves 2026.3's `step5.sh` for a later
quiet block. The session agrees: C has moved on to the candidate, and the
2026.4 runs test the code that `main` now has. 022-01 then closes either on
`step5.sh` in a later block or on Frans's word that the 2026.4 runs stand
for it.
