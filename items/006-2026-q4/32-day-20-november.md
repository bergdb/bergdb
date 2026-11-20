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

* Usage level tight; the stop file at week 95 %, 98 % from 14:00
  (Frans). Subagents on Opus 5.5,
  high.
* Each agent works in its own clone under the day's bench directory;
  coord-1120 lands on `main` after the gates.


## 3. The work

| Agent | Item | What | Effort |
|---|---|---|---|
| hf | 028-29, then 028-28 | the harnesses on a loaded machine; the unit test flake | Opus high |
| tx | 028-31, 028-30 | a reclaim text since 028-15; 2026.4's refusal message | Opus high |
| fx1 | 028-38, 028-39, 028-37 | freshTreeBound; dirtyNodeBound's Javadoc; the bridge checker once | Opus high |
| fx2 | 028-35, 028-36 | KillEmpty; an IndexJobsHarness test under load | Opus high |


## 4. Progress

* 11:05 coord-1120 started; coord-1118 closing.
* 11:36 033 created (14436f96).
* 11:40 hf and tx started.
* 11:44 028-31, 028-30 landed (289b2dc8): the refusal message was main's
  (028-15), not 2026.4's; not a released bug.
* 12:32 028-34 registered: transactionInfo(), Decide, open.
* 12:39 028-29, 028-28 landed (906f9854): four races of the harnesses
  under load, no fault of the database.
* 13:29 030-31 and 030-30 landed together (0613b4ef): the user apps'
  traces and reclaim across restarts and crashes against the model; the
  day's seeds in night.sh; Java's contract check in week.sh. 028-35 to
  028-37 registered from their findings.
* 13:30 The week's usage reached 95 %: the work stops for the day.
* 13:35 030-29 landed (6954f1d6): PE's dirty nodes within Java's
  dirtyNodeBound for transactions of puts (deletes open); PE accepts
  Java's transactions at G = 8192, H = 126. 028-38, 028-39 registered.
* 14:03 The usage stop raised to 98 % (Frans); fx1 and fx2 started on
  the small 028 fixes.

* 14:20 Codex started on an independent review of the Lean statements
  against 030-26 (to be 030-32).
* 14:55 028-37, 028-38 (a Dag refuses node sizes below 8, Frans's
  decision), 028-39 landed (99047e73); 028-35, 028-36 landed (416cfa93);
  no fault of the database. week.sh's conformance-large on the day's
  seeds (Frans; 34d4b599). 028-40 registered.
* 14:58 The runs before release 2026.6 started on 3334bb0f: night.sh and
  week.sh in parallel, then timing.sh on a quiet F53. The release is
  planned for Tuesday 24 November, after the usage reset.

* 15:50 week.sh's first try failed on a unit test's timing at a low
  priority (fixed, 2bb2b851); night.sh and week.sh restarted on
  2bb2b851 at `nice -n 10`, timing.sh after them.
* 15:55 The review of the statements landed as 030-33 (four findings);
  F4 corrected (bf9b3428); F2, F3 corrected in 030-26 and TransCheck's
  Javadoc (4f1ff7e7); 028-40 done, RB-003 (S4) in 033 (dd92de21).
* 17:29 030-34 landed (a1d1a123): C-STEP checks the values a reclaim
  step writes back and refuses its other writes; 0 failures.
* 18:07 030-35 landed (2151cd4b): reclaim's step model requires the
  values read, and reads after reclaim give the users' values, proved
  (`PE.pe_reclaim_user_reads_steps`; 215 theorems). 030-33 done.


## 5. Outcome

Not yet.

## 6. Next: Monday 23 November and the release

Decided by Frans (2026-11-20), for the coordinator of Monday (after the
usage reset of Monday 22:00 where usage requires it):

* **The scope of the proofs as a closed list of user guarantees** (a new
  030 subitem): 030-26's "What it means for a user" made a numbered list
  G1 to Gn, each marked proved (its theorem) or tested on purpose (its
  assumption in 030-26, section 5, and its check); written by an agent,
  reviewed independently against the pinned statements. 030's goal 2
  (strengthen the tested links) is done when 030-36 lands or the delete
  case is left tested by decision; further links only by a new decision.
  026's release steps get the check: the guarantee list reviewed against
  the pinned statements before the tag.
* Land 030-36 (the dirty-node bound with deletes, running tonight) after
  its gate; turn the bug hunt's findings (026-26, running tonight) into
  028 entries, or RB entries in 033 when 2026.5 has them.
* The release runs' results (night.sh, week.sh, timing.sh, started
  15:50): failures fixed; timing.sh's figures against 2026.5 for
  028-19's decision (not blocking unless a large loss at 1M or 10M).
* Release 2026.6 on Tuesday 24 November: the notes from `releases/next.md`,
  033's RB-001 to RB-003, 030-26 current.

