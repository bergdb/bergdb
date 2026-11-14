# 006-25 Day work, 14 November 2026

Created 2026-11-14 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-14 (coord-1114), a Saturday, and the time
until Frans is back on Sunday 15 November, 10:00 at the earliest: the
progress and the outcome. The way of working is 013-02's (the
coordinator).


## 1. The request

coord-1113's handover (006-24, sections 4 and 5): decisions 1 to 8 for
Frans; 026-09 on its branch; 007-09's update with 13 November's T4 and
bounded-startup results; `night.sh` skipped on 13 November.

Frans's answers:

* 11:35, on 006-24's decision 1 (026-09, Q1 to Q4, recommended yes to
  all), after the gain, the cost and the Lean model were explained:
  "Yes, land it. Plan a 10M timing run for later today, some time after
  15:00. Won't attend this session after that and will be back no sooner
  than 10:00 on Sunday, so that is a good period to run performance
  testing."


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents that
change code work in clones and do not commit to `main`. Clones and runs
under `/Users/f/fl/bench/2026-11-14/`.

Usage: plenty at 11:12; the week at 72 % (reset Monday 16 November,
22:00). Subagents on Opus 5.5, high, xhigh for planning.

From 15:00 to Sunday 10:00 F53 is for the timing run (026-15): no other
heavy work while it times; the coordinator stays idle between check-ins.


## 3. The work

| ID | Task | Agent | Result |
|---|---|---|---|
| 026-09 | Land the keys-only scan (Q1 to Q4 yes); gates on main merged | coordinator | gating |
| 026-15 | The timing pass at 10M keys: the plan and its scripts by 14:30 | timing (xhigh) | started |
| 026-15 | The timing pass, run | coordinator | from 15:00 |


## 4. Progress

* 11:12 coord-1114 started; coord-1113 closed at 11:13.
* 11:17 024-19's Q2, Q3 and Q5, carried from coord-1112, were decided
  on 13 November (08:54, 09:17) and made in 026-08.
* 11:36 026-09: `main` (3d2beedc, with 028-09's fix in `Db` and
  `NodeCollection`) merged into the branch, 542927c5; before-commit,
  level 3 (full) and the count gates running
  (/Users/f/fl/bench/2026-11-14/land0909/).
* 11:40 026-15 registered; the agent "timing" plans the run.


## 5. For Frans to decide

From 006-24 (still open): 2 (028-04), 3 (028-10), 4 (028-11), 5
(028-12), 6 (where the policy of 13 November, 16:50, lives), 7 (the
proofs from here), 8 (the 10 premises to read). 006-24, sections 4 and
5, has each with its recommendation.
