018-release-2026-3
==================

Created 2026-11-05 by Frans Lundberg. Status: open.

Release 2026.3 of BergDB: a bug-free Core, with no known issue at the
release but in DbObject and user indexes, which are experimental. The
plan, its decisions and the work towards the release.


Files
=====

* [01-plan.md](01-plan.md). 018-01, the plan:
  * the goal, in Frans's words: what the Core is (the Core Layer and the
    Pub API, but DbObject and user indexes), and when 2026.3 is ready;
  * the rules: 010's principles hold, and Frans approves any change of
    the stream format;
  * the Core's 54 known faults (52 entries of 015, S2-F24 and 014-01),
    and what is outside the goal;
  * the strategy proposed on 2026-11-05 and Frans's decisions D1 to D7;
  * his exceptions (none yet);
  * the harnesses by fault class, proposed;
  * the work W1 to W5.


Log
===

2026-11-05. Created the item, at Frans's request ("Create item
nnn-release-2026-3 with this plan for working towards 2026.3."), with the
plan in 018-01. Claude (Opus 5.5, Claude Code) proposed the strategy that
morning, and Frans answered it at 09:28. Nothing started.

2026-11-05. 018-01 updated with Frans's answers of 09:43 (D4 to D7: the
rest of the Pub API in the goal, the limits not known issues, the
experimental methods, when the release is ready) and his rules (010's
principles; the stream format).
