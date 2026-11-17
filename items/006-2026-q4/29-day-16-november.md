# 006-29 Day work, 16 November 2026

Created 2026-11-16 by Frans Lundberg. Status: done (the outcome written
2026-11-17, 04:18). The plan for the
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

* 08:28 006-28 and this plan created (7e188024); W1 started.
* 08:39 and 08:43 the agent stopped on API 529 (Fable overloaded); resumed 08:40 and 08:54.
* 09:07 006-28 done (816 lines; the counts in 28-simpler-algorithms/): top three NW (a writer that computes the net change; a one-day spike in the model before SF10), RT (Rule A with times; measure S1 first), OT (one tree, after `l4`); scan removal: no. Six questions for Frans, section 7.
* 10:11 006-28's section 7 (Frans's Q1 to Q4: MT, maintenance transactions) committed 977cd68e.
* 10:26 2026.6's theme: simpler algorithms (bf8e2d92).
* 10:29 Frans's answers to 006-28's questions 7 to 9 recorded in 006-28, section 8; the provers (`l4`, `htbL`) wait for MT's trial.
* 10:32 028-15 registered (afe20bcb).
* 10:47 026-17 registered; agent mtplan started (Fable at high).
* 11:02 agents t14 (028-14) and t07 (028-07) started (Opus at high).
* 11:04 026-17's plan written: T0 to T8, about 12.5 agent-hours, 7 to 9 h on the clock, 5 to 10 % of a week; not before the reset; eight questions for Frans (section 11).
* 11:14 028-07 landed (6695d48c); 028-16 registered (00a3a29b).
* 11:18 MT's trial: T0 done; agents A (T1) and B (T2) started.
* 11:32 028-14 landed (105be197), the combined tree gated with 028-07 (BEFORE COMMIT OK).
* 12:34 MT's trial: T4 (12:05), T7 (12:12), T5 and T6 (12:34) done; all runs pass; the scan finding A1 walked through with Frans (12:32).
* 13:12 026-18 written down: main transactions and subtransactions, Frans's idea (12:54); a short proof trial proposed, maybe tonight after 22:00.
* 13:36 MT's trial done (T8): MT passes every check in the model, with one rule added (A1) for Frans; result in 026-17, evidence in 17-mt-trial/, branch 026-17-mt-trial kept.
* 13:40 026-17 committed (94aa6772), news.md entry.
* 14:13 026-19's plan written: statements I and I_sub, the fix step's and the readers' theorems, about 14 prover-hours, one night from 22:05 on Frans's go.
* 14:32 030-proofs made (9789291c): the map of all proof work; Frans: both proof lines tonight.
* 19:58 night.sh: NIGHT OK (166 minutes) on f278cd57, all steps.
* 20:18 to 20:43 the preparation for the public release (three agents; details outside this repository).
* 22:03 the night started: the week reset to 0 %; six agents: PT-A and PT-B (026-19), htbl (`htbL`), l4plan (030-01), d3plan (030-02), all Opus at xhigh; t16 (028-16), Opus at high.
* 22:10 028-16 landed (ccd384ac): a refused second start of one Db closes nothing; BEFORE COMMIT OK, LEVEL 1 OK.
* 22:26 030-01, `l4`'s plan, written and committed (7d1c65fb): route B, additions only, no statement change; prover l4 started on its steps 1, 0 and 2.
* 22:31 `l4`'s step 1 landed (703d8282): `invGetScanOK_merges_l4L` from hp, hth, htbL and l4L. 030-02, the bridges' plan, written and committed (a6dc3c43): TP14 and TP19 false as stated at the top node ordinal bound, by reading; no D3 prover tonight (not agreed; Frans's question 1 first).
* 23:12 `l4`'s steps 0 and 2 landed (cdc20d8e, 480d6997): the run check, 0 failures in 15 families; the hole's form; the pilot. Steps 3 to 6 split over two provers, l4a (3, 4) and l4b (5, 6), Opus at xhigh.


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
* **The preparation for the public release** (Frans, 20:17), started
  20:18 and done by 20:43, Opus at high, nothing committed or published
  here; the details are in Frans's private notes, outside this
  repository (029).
* Unattended from 17:10 until Tuesday 07:00 (Frans: "I am about to
  leave", 17:08; the return time a default): check-ins every 20
  minutes, the watchdog, a one-off at 22:03 that starts the night.

**The rules of the night:**

* The clock: no new step after 04:30; provers stop at 05:30; all ends at
  06:00 (026-19, section 6.3).
* Usage: 026-19's provers stop at 9 % of the new week (10 % with the
  write-up; 026-19, question 2, default). Changed at 22:57 by the
  coordinator: the week's figure is shared with the main line's
  provers (4 % at 22:56, about half of it 026-19's), so 026-19's STOP is
  set at 16 % of the whole week, about 9 % of its own. At 23:13, with
  five provers, 20 % for 026-19 and 30 % for all (the week at 5 %). The coordinator sets every STOP
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

Written 2026-11-17, 04:18, by coord-1116; nothing runs after 04:16.

**The day (16 November).** The study 006-28 (where the proofs'
complexity is; MT, Frans's idea of maintenance transactions); 2026.6's
theme "simpler algorithms" (026); MT's trial in the model (026-17: MT
passes every check, one rule added, A1); Frans's idea of main
transactions and subtransactions written down (026-18); the proof
trial's plan (026-19); the map of all proof work (030); 028-07, 028-14
and 028-16 fixed and landed; 028-15 registered (the startup distance in
an internal KV, for 2026.6); `night.sh` OK on f278cd57; the preparation
for the public release (details outside this repository, 029).

**The night (22:03 to 04:16)**, 13 Opus agents, about 60 landings on
`main`, each gated on the combined tree; `lean/` from 236,184 to 279,136
lines; the week from 0 % to 19 %.

* **`htbL` proved** (025-05, step 8; prover htbl, about 3,950 lines): a
  delete never takes back a node it found at its start with a height at
  or above the fuel. The key tree's best top theorem with no premise
  known false is now `invGetScanOK_merges_noTb`: TP7, TP10 and TP11 for
  Java's parameters from `hp`, `hth` and `l4` (030, D1).
* **026-19, the proof trial of MT with subtransactions:** reduced, not
  proved; by its rule the proofs' gain is not supported, nor refuted.
  The merge's room case is smaller under MT; the hard case left (a
  merge whose parent is full, with its cascade) is the same as `l4`'s;
  MT adds the frames (about 6,000 lines each, by estimate). Result in
  026-19.
* **`l4`, by 030-01's route B** (provers l4, l4a to l4g): most of the
  delete is proved in pieces (the merges' loop, root collapse, every
  full leaf but R4's case, the upward delete, the full parent in 94 % of
  the cases on the runs). The night's top theorem
  `invGetScanOK_merges_noL4Night` has four named premises; one of them,
  `R3Calls`, is believed false at unreached states (030-01's log, 01:56
  to 02:22), so that theorem is believed vacuous. Two findings: the
  premise `UpHtWalk` (added at 00:18) is false, proved in Lean, and its
  true form is proved; R3 needs a new made-for invariant, planned in
  030-03 (one night, no statement change). R4's general case: every
  piece but the merge tail with the hole is proved (prover l4g).
* **Plans:** 030-01 (`l4`), 030-02 (the bridges TP14, TP16, TP19; TP14
  and TP19 false as stated at the top node ordinal 2^48, by reading),
  030-03 (R3).

**For Frans to decide**, each with a recommendation:

1. The direction (026-19): today's model, or one more MT night ("holes
   as key ranges") before SF10. Recommended: today's model; MT kept as a
   record (026-17, 026-18, 026-19, the branches).
2. R3 (030-03): its route M0 to M5 in the next night. Recommended: yes.
3. R4 (030-01's log, 03:54 and 04:13): the merge tail with the hole
   (about 3 hours) and the leaf's and stop node's forms. Recommended:
   beside R3.
4. The bridges (030-02, question 1, the ordinal bound). Recommended: its
   default (b), the bounded forms as new statements.
5. 028-15, older streams: A or B. Recommended: A if SF4 gives no
   fallback.
6. The close step: the vacuous lemmas (`liveDel_upRoom`,
   `liveDel_upRoom_live`), the `noL4` family until R3, the superseded
   corollaries. Recommended: after R3.
7. The branch `026-17-mt-trial` on `origin` (pushed 13:40): keep or
   delete. Recommended: keep.
8. The public release's checklist: in Frans's private notes.
