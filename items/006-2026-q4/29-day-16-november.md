# 006-29 Day work, 16 November 2026

Created 2026-11-16 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-16 (coord-1116), a Monday: the progress and
the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1115's handover (006-27, section 8): the key tree's top theorem
`invGetScanOK_merges_tbL` from `hp`, `hth`, `l4` and `htbL`; five
decisions for Frans, most of them for after the week's reset (Monday
22:00). Week 90 % at 07:59, level tight.

Frans's words:

* 10:26: 2026.6's preliminary theme is "simpler algorithms" (026).
* 10:29, on 006-28's questions 7 to 9: MT's trial first, but not started yet, its plan first; the provers wait for it; deletes may cost more bytes ("Let's keep measuring performance and and judge complexity so we can make the right tradeoffs.").
* 08:26: a study, "Simpler algorithms for simpler proofs", as a
  subitem of 006 (006-28), by an agent at Fable High: "No rush, take
  your time."


## 2. The ground rules

* Usage tight (week 90 %, reset Monday 22:00): at most two agents at a
  time.
* Agents may run until the week reaches 99 % before the reset (Frans,
  10:57: "No need to leave tokens "on the table" so to speak.").
* STOP for an agent: `/Users/f/fl/bench/2026-11-16/NAME/STOP`, set by
  the coordinator if the week reaches 99 % before the reset; the
  agent then writes its State note in its item and ends, and is resumed
  after the reset.


## 3. The work

* **W1, the study 006-28** (agent simpler, Fable at high): writes
  006-28 in the main tree; the coordinator commits.
* **W2, the plan for MT's trial, 026-17** (agent mtplan, Fable at high;
  Frans, 10:47): writes 026-17 in the main tree; the trial not started.
* **W3, 028-14 and 028-07** (agents t14 and t07, Opus at high, each in
  a clone; Frans, 11:01): fix or options; the coordinator lands after
  `before-commit.sh`.
* **W4, MT's trial, 026-17** (Frans, 11:17: "Run the trial unattended
  now; if you run out of usage, restart it at 22:01 tonight."): T0 by
  the coordinator, then agents A (Opus at xhigh for T1 and T4) and B
  (Opus at high) by 026-17's plan; STOP at a week of 99 %, resumed at
  22:01. The trial's state: `/Users/f/fl/bench/026-17/state.md`.
* **028-15** registered (the startup distance in an internal KV; Frans,
  10:32), taken by 2026.6.


## 4. Progress

* 08:28 006-28 and this plan created (bb255d4b); W1 started.
* 08:39 and 08:43 the agent stopped on API 529 (Fable overloaded); resumed 08:40 and 08:54.
* 09:07 006-28 done (816 lines; the counts in 28-simpler-algorithms/): top three NW (a writer that computes the net change; a one-day spike in the model before SF10), RT (Rule A with times; measure S1 first), OT (one tree, after `l4`); scan removal: no. Six questions for Frans, section 7.

* 10:11 006-28's section 7 (Frans's Q1 to Q4: MT, maintenance transactions) committed 1bdda15e.
* 10:26 2026.6's theme: simpler algorithms (d93d9d7a).
* 10:29 Frans's answers to 006-28's questions 7 to 9 recorded in 006-28, section 8; the provers (`l4`, `htbL`) wait for MT's trial.

* 10:32 028-15 registered (a9001d7e).
* 10:47 026-17 registered; agent mtplan started (Fable at high).
* 11:02 agents t14 (028-14) and t07 (028-07) started (Opus at high).
* 11:04 026-17's plan written: T0 to T8, about 12.5 agent-hours, 7 to 9 h on the clock, 5 to 10 % of a week; not before the reset; eight questions for Frans (section 11).

* 11:14 028-07 landed (c925c11e); 028-16 registered (d8da4a35).
* 11:18 MT's trial: T0 done; agents A (T1) and B (T2) started.

* 12:34 MT's trial: T4 (12:05), T7 (12:12), T5 and T6 (12:34) done; all runs pass; the scan finding A1 walked through with Frans (12:32).
* 13:12 026-18 written down: main transactions and subtransactions, Frans's idea (12:54); a short proof trial proposed, maybe tonight after 22:00.

* 13:36 MT's trial done (T8): MT passes every check in the model, with one rule added (A1) for Frans; result in 026-17, evidence in 17-mt-trial/, branch 026-17-mt-trial kept.


## 5. Outcome

Not yet.
