031-release-2026-7
==================

Created 2026-11-20 by Frans Lundberg. Status: open.

Release 2026.7 of BergDB, after 2026.6 (026): its plan, its decisions and
the work towards it. No theme yet: as with 2026.5 and 2026.6, the theme
and the scope settle as the work does, not in advance (Frans,
2026-11-20).

Created together with 2026.8 (032), so that work meant for after 2026.6
has a place before its release is planned. Work may move between 2026.6,
2026.7 and 2026.8 until a release's scope settles. Short tasks that no
release owns stay in 028; a release item says which 028 entries it
takes.

The release is made as 034 says, the process for every release (Frans,
2026-11-24): its steps (034-01), its checklist (034-02) and its scripts
(`items/034-releases/scripts/`). This item holds the release's plan,
scope and decisions, and says where it departs from 034.


Work for this release
=====================

What 2026.6 does not finish comes here, unless Frans decides otherwise.

* 026-03, a single maintenance step: not started in 2026.6; carried here
  on 2026-11-24 (026 done). Designed together with 028-53's
  fix in 031-01 (Frans, 2026-11-25).
* 026-04, the settings of reclaim's fraction: the values and the default
  not chosen in 2026.6 (1/4 kept); carried here on 2026-11-24.
* 026-14, the Lean model's scope and three additions: not decided in
  2026.6; carried here on 2026-11-24 (Frans).
* 028-49, the release scripts make the GitHub release's body with
  absolute links: needed before this release is made (from the review of
  2026.6, 2026-11-24); in 034's scripts since 2026-11-24.


Files
=====

* [031-01](01-one-maintenance-path/readme.md): one maintenance path for a commit
  and `maintain()`, back to empty and quiet when done; the design of
  026-03 with 028-53's fix (RB-007).


Log
===

2026-11-20. Created (Frans), with 032.

2026-11-24. 026-03 and 026-04 carried here from 2026.6, open (026 done).

2026-11-24. 026-14 carried here from 2026.6, open (Frans).

2026-11-24. 028-49 taken, for the release scripts (review of 2026.6).

2026-11-24. The release is made as 034 says, the process for every
release (Frans); 034 created.

2026-11-25. 031-01 created: 026-03 and 028-53's fix designed together
(Frans).

2026-11-25. A review by Codex of the Java changed since 2026.6 (11
commits, to `4ce8f942`): no new bug; RB-007 reproduced independently;
STM (028-01, 028-48), 028-50's refusal, PE's writes (028-19, the same
bytes as 2026.6's writer) and 028-51 found sound by probes that ran
(006-35).
