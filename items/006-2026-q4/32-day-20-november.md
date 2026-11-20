# 006-32 Day work, 20 November 2026

Created 2026-11-20 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-20 (coord-1120), a Friday: the progress and
the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1118 (006-31) closed at 11:04 and keeps its three agents until they
finish: 030-29 (the dirty-node bound proved), 030-30 (daily trace seeds,
the contract check in week.sh) and 030-31 (the user apps' traces against
the model); coord-1120 lands their work.

Decisions of the morning:

* The week's usage stop is 95 % for today (Frans, 11:06).
* Released bugs are registered in 033, from release 2026.5, as RB-nnn
  with severities S1 to S4 (Frans, 11:30). RB-001 and RB-002 are fixed
  by 026-06.
* Known faults before a release are fixed first (Frans, 11:08). No open
  fault of the database is known; the open fixes are in the tests and
  the texts: 028-28, 028-29, 028-30 and 028-31, started now (Frans,
  11:35).


## 2. The ground rules

* Usage level tight; the stop file at week 95 %. Subagents on Opus 5.5,
  high.
* Each agent works in its own clone under the day's bench directory;
  coord-1120 lands on `main` after the gates.


## 3. The work

| Agent | Item | What | Effort |
|---|---|---|---|
| hf | 028-29, then 028-28 | the harnesses on a loaded machine; the unit test flake | Opus high |
| tx | 028-31, 028-30 | a reclaim text since 028-15; 2026.4's refusal message | Opus high |


## 4. Progress

* 11:05 coord-1120 started; coord-1118 closing.
* 11:36 033 created (14436f96).
* 11:40 hf and tx started.


## 5. Outcome

Not yet.
