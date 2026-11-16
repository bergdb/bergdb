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
* **W5, the plan for 026-18's proof trial, 026-19** (agent ptplan,
  Fable at high; Frans, 13:48): writes 026-19; the trial perhaps from
  22:05 on Frans's go.
* **W6, the night's preparation** (14:40, by shell, no model): the
  clones and builds for 026-19 (P0a) and the main line's prover, the
  main line's gate `gate-1116.sh` with a new base, the briefs (section 5).
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
* 11:32 028-14 landed (b47eae04), the combined tree gated with 028-07 (BEFORE COMMIT OK).
* 12:34 MT's trial: T4 (12:05), T7 (12:12), T5 and T6 (12:34) done; all runs pass; the scan finding A1 walked through with Frans (12:32).
* 13:12 026-18 written down: main transactions and subtransactions, Frans's idea (12:54); a short proof trial proposed, maybe tonight after 22:00.
* 13:36 MT's trial done (T8): MT passes every check in the model, with one rule added (A1) for Frans; result in 026-17, evidence in 17-mt-trial/, branch 026-17-mt-trial kept.
* 13:40 026-17 committed (c03296e3), news.md entry.
* 14:13 026-19's plan written: statements I and I_sub, the fix step's and the readers' theorems, about 14 prover-hours, one night from 22:05 on Frans's go.
* 14:32 030-proofs made (96918d92): the map of all proof work; Frans: both proof lines tonight.
* 19:58 night.sh: NIGHT OK (166 minutes) on 5b8f337b, all steps.
* 20:18 the going-public preparation started (three agents).


## 5. The night of 16 to 17 November

Frans, 14:25 and 14:32: both proof lines in parallel, the map 030-proofs
("Yes, do this, sounds good."); 026-19's go ("Yes.", 14:25).

**What runs, from 22:05** (after the week's reset at 22:00), all Opus 5.5
at xhigh, each in its own clone made at 14:40 (W6,
`/Users/f/fl/bench/2026-11-16/night/prep.sh`):

* **PT-A and PT-B**, 026-19's provers (030, D2): briefs
  `/Users/f/fl/bench/2026-11-16/night/briefs/pt-a.md` and `pt-b.md`, the
  common brief `/Users/f/fl/bench/2026-11-16/pt/common.md`; clones
  `pt/a/clone`, `pt/b/clone`; their own gate (PT-B writes it in P0b);
  nothing lands on main; STOP `/Users/f/fl/bench/2026-11-16/pt/STOP`.
* **htbl**, the main line's prover (030, D1): 025-05's step 8, then step
  9; brief `night/briefs/htbl.md`, common brief `night/common.md`; clone
  `night/htbl/clone`; the gate `night/gate-1116.sh` (gate-1115.sh with its
  base made from main this afternoon); the coordinator lands GATED steps
  on main.
* **l4plan**, a planning agent (030, D1): writes 030-01, `l4`'s plan;
  brief `night/briefs/l4plan.md`; the coordinator commits.
* STOP for the main line: `/Users/f/fl/bench/2026-11-16/night/STOP`.
* **Added at 17:05** (the coordinator's proposal, by default from 17:30;
  Frans left at 17:08): `night.sh`, started at 17:12 on Frans's word
  ("Should we run night.sh now. I dont need the computer", 17:11), the
  first night run since 028-07 and 028-14 landed; **t16**, 028-16 (Opus at high, clone
  `/Users/f/fl/bench/2026-11-16/t16/clone`, brief `night/briefs/t16.md`;
  the coordinator lands it after BEFORE COMMIT OK); **d3plan**, the plan
  for 030's D3, the bridges, as 030-02 (Opus at xhigh, brief
  `night/briefs/d3plan.md`); and a prover on `l4` once 030-01 is
  written, only if its route needs no statement change.
* **The going-public preparation** (Frans, 20:08 and 20:17: "Yes. Go
  ahead with those three. [...] do it now using a new agent."), started
  20:18, Opus at high, nothing committed or published: **gp-inventory**,
  the full inventory of the history (a file of Frans's private notes); **gp-dryrun**, a dry run of the
  cleaned public history (`/Users/f/fl/bench/2026-11-16/public/build/`,
  no push); **gp-drafts**, README, LICENSE (Apache-2.0) and NOTICE,
  CONTRIBUTING and SECURITY on the branch `029-public-files` of a clone.
  The morning adds a one-page checklist of the release's decisions.
* Unattended from 17:10 until Tuesday 07:00 (Frans: "I am about to
  leave", 17:08; the return time a default): check-ins every 20
  minutes, the watchdog, a one-off at 22:03 that starts the night.

**The rules of the night:**

* The clock: no new step after 04:30; provers stop at 05:30; all ends at
  06:00 (026-19, section 6.3).
* Usage: 026-19's provers stop at 9 % of the new week (10 % with the
  write-up; 026-19, question 2, default). The coordinator sets every STOP
  file if the whole week reaches 25 % before 06:00 (the coordinator's
  rule: about 10 % for 026-19, the rest for the main line, a margin for
  Tuesday).
* The machine: at most six heavy runs at once (`slot.sh`); nothing is
  timed tonight.
* The coordinator: unattended check-ins every 20 minutes (013-02); it
  lands htbl's GATED steps (merge, the gate on the combined tree, push),
  logs PT's GATED messages, restarts a stopped agent from its state, and
  at 06:00 writes the morning: this plan's Outcome, 026-19's Result (or
  one Opus agent at xhigh writes it), 030's map, and `news.md`.

**The morning, Tuesday 17 November** (030, the decision point): `htbL`
proved or how far it got; `l4`'s plan and size (030-01); 026-19's
evidence. Frans decides the direction.


## 6. Outcome

Not yet.
