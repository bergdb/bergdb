008-release-2026-1
==================

Created 2026-10-25 by Frans Lundberg. Status: done.

Release 2026.1 of BergDB: an internal release, not published, made as a
real one (a tag, the jar, release notes, the tests on the final jar), and
the baseline for performance measurements before handles (004) and gradual
eviction.


Files
=====

* [01-plan.md](01-plan.md). 008-01, the plan: the release directory
  `releases/2026.1/` and its five files, the release notes' contents, the
  baseline runs, how to compare a later version, the two hours step by
  step, and the decision for Frans.


Log
===

2026-10-25. Created the item, at Frans's request ("Propose how to make
this release. Item 008 perhaps."), with the plan proposed by Claude (Opus
5.5, Claude Code) in 008-01. Nothing done yet; the plan waits for Frans's
decisions (008-01, the last section).

2026-10-25. 008-01 revised at Frans's request: two hours from his command
to the tag, with the performance runs cut to fit (F53 about 40 minutes, s1
beside it); everything in the repository, in `releases/2026.1/` (the jar,
the source, the release notes, the outputs of the runs, at most about 20
MB). The known issues updated with Frans's decisions of the day (005-11,
005-33, 005-42, 007-03). The release waits for his command.

2026-10-25. Release 2026.1 made at Frans's command (12:47), by Claude (Opus
5.5, Claude Code): commit A `a42947c` (the version), the night run on it
(NIGHT OK, 12:51 to 13:35), the jar and its tests, s1's runs (12:52 to
14:00), and F53's timed block (15:17 to 15:49). It took three hours, not
two: the F53 script waited for its own `caffeinate` after the tests on the
jar (a `wait` that also waited for that child) and hung from 13:39 until it
was found at 14:43, and the quiet check then waited until 15:17. Commit B holds `releases/2026.1/`; the tag is on A.
Status: done.
