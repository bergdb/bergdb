# 006-25 Day work, 14 November 2026

Created 2026-11-14 by Frans Lundberg. Status: done (closed by coord-1114
on 2026-11-15, 08:55; the rest handed to coord-1115). The plan for the
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
* 11:43, 028-04 (decision 2): option A.
* 11:58: 007-09 updated as recommended; decisions 4 (028-11) and 5
  (028-12, A) as recommended; the night, option c (the provers on F53,
  the timing pass when they stop): "if the proofing stops (like
  tonight), use the remaining time for timing-sensitive things. I
  expect there to be plenty of calm machine time available after
  proofing finished due to AI usage limits."
* 12:10, decision 3 (028-10): "Remove the parameters if possible. It if
  works with the current testing. Then clean up the code. Do it in a
  separater agent at high to keep this session interactive."
* 12:16: the week's ceiling 92 %; the proofs: "cleanup will be the
  focus today. Don't start yet." 12:18: the builder refuses while the
  setter clamps, A for now, a 028 entry (028-13).
* 12:32: a report on the proofs (006-26), "easy to read independently
  from other documents [...] Max 60 min reading time", by an agent on
  Fable at high. 13:02: its epub to be mailed to his Kindle.
* 12:45 and 12:53: a study of simpler algorithms for the remaining
  premises (026-16, his words quoted there), on Fable at high, beside
  the cleanup.
* 13:00, the cleanup (025-02: a plan now, the provers tonight under the
  92 % ceiling, then the timing pass): "Yes, good. Go ahead."


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents that
change code work in clones and do not commit to `main`. Clones and runs
under `/Users/f/fl/bench/2026-11-14/`.

Usage: plenty at 11:12; the week at 72 % (reset Monday 16 November,
22:00), its ceiling 92 % (Frans, 12:16). Subagents on Opus 5.5, high,
xhigh for planning and proofs; Fable at high where Frans asked for it
(006-26, 026-16).

The night (option c, Frans 11:58): the provers of 025-02 on F53 first;
when they stop (their plan, or the ceiling), the timing pass (026-15),
with no other heavy work while it times and the coordinator idle
between check-ins.


## 3. The work

| ID | Task | Agent | Result |
|---|---|---|---|
| 026-09 | Land the keys-only scan (Q1 to Q4 yes) | coordinator | landed c7c7a02b |
| 028-04 | A value transformation's null deletes the key (A) | nullvt (high) | landed 6a543f13 |
| 028-11 | P5's sentence | coordinator | 9f00cdd0 |
| 028-12 | The builder refuses a startup distance above 10^9 | sdmax (high) | landed 5f413438 |
| 007-09 | Brought up to the Lean of 13 November | doc009 (high) | b99d6124 |
| 028-13 | The startup distance's two ranges; A for now | coordinator | registered ae20138c |
| 028-10 | `Db.start(StartParams)` removed | startparams (high) | landed 71932de0 |
| 026-15 | The timing pass: plan, scripts, probes | timing (xhigh) | READY, dadbf7fd |
| 006-26 | The proofs as of 14 November, a report | proofreport (Fable, high) | 205b477d |
| 026-16 | Simpler algorithms for the remaining premises | simplify (Fable, high) | running |
| 025-02 | The proofs' cleanup: the plan | cleanplan (xhigh) | running |
| 025-02 | The proofs' cleanup: the provers | provers (xhigh) | tonight |
| 026-15 | The timing pass, run | coordinator | after the provers |


## 4. Progress

* 11:12 coord-1114 started; coord-1113 closed at 11:13.
* 11:17 024-19's Q2, Q3 and Q5, carried from coord-1112, were decided
  on 13 November (08:54, 09:17) and made in 026-08.
* 11:36 026-09: `main` (3d2beedc, with 028-09's fix in `Db` and
  `NodeCollection`) merged into the branch, 542927c5; before-commit,
  level 3 (full) and the count gates running
  (/Users/f/fl/bench/2026-11-14/land0909/).
* 11:40 026-15 registered; the agent "timing" plans the run.
* 11:52 028-04 landed (6a543f13).
* 11:59 028-11, P5's sentence (9f00cdd0).
* 12:04 026-09 landed (c7c7a02b): before-commit, level 3, the count
  gates on the merged tree, and before-commit again after `main` moved.
* 12:06 028-12 landed (5f413438). 12:09 007-09 (b99d6124).
* 12:20 028-13 registered (ae20138c).
* 12:37 028-10 landed (71932de0): before-commit, level 1 and level 2
  quick on the branch, before-commit on the merged tree.
* 12:53 026-16 registered (7ced25db); 13:00 025-02 (eb1a04a0).
* 13:05 006-26 committed (205b477d). Mailing its epub to the Kindle
  failed: the Gmail connector can read but not send or draft; the epub
  given to Frans in the session instead.
* 13:08 026-15 READY (dadbf7fd). The stale heavy slot of 02:55 (cost's
  HeightsFitsR build, no process) released.


* 13:31 to 15:45 025-02, the proofs' cleanup, its five steps landed:
  notes 5458ac36 (14:30), prune b8fae26c (14:43), names 73852c9b
  (14:58), dups a04dbd78 (15:17), close 2413e669 (15:45). lean/SIS/Tree
  227,923 to 140,264 lines, lean/ 296,684 to 209,065; one top theorem
  `invGetScanOK_merges`; every step gated; level 2 OK.
* 13:46 Frans accepted F1 (026-16); 025-03 created (95b71a6b).
* 15:58 to 03:11 026-15, the timing pass: 105 runs, 9 rounds, every run
  ok and quiet; stopped by STOP at 03:08 (b9acd055, section 9).
* 03:07 Frans: "Can you continue to work on the proofs now?"
* 03:43 025-03 step 1 (f1check, 7a5b6b98): NoOutside holds on every
  traced run with H + 1 (205 traces; 2 transactions need it).
* 03:50 025-03 step 2 (f1thm, ad4e9cf5): `invGetScanOK_merges_noOutside`
  without `htb`; step 3 (`hMSF`, `hCoF` from NoOutside) does not follow.
* 04:00 to 06:03 provers putinv2, cost2 and (from 05:08) coll:
  * 1d149b59 `hCoU`, `hU` and `hHL` are false as stated (PremisesFalse):
    the top theorem holds vacuously; 006-26 corrected (858951e5);
  * bc7d81ea `hMF` proved; 82d68225 the true forms of `hHL` and of
    `hCoU`'s ids half; 74ff5be5 `hHL` gone on the joint route;
  * 2fee65cc to 3a95f624 `hchk` narrowed, four of its checks proved;
  * a4c328a0 to 25b03569 `hCoU` gone by root collapse's commutation
    (`invGetScanOK_merges_joint6`).
* 08:27 Frans back. 08:33 his answers to section 7; agents hu-plan
  (025-04, Fable at high) and tops (one top theorem per route).
* 08:46 tops done on its branch (d6cedb46), not landed: the permission
  system refused its edit of the gate's copy (the statement check's base
  and 41 new closure lines of `hchk5`); for Frans (a, b or c).
* 08:54 coord-1115 started; coord-1114 closing. Handed over: hu-plan's
  result, tops, decision 2's prover (DelInvJ), decision 8's answer.

## 5. While Frans is away (13:58 to Sunday 10:00)

Frans, 13:57: "I am leaving in a few minutes. Are you ready for
unattended work as far as possible. As planned."

* **The proofs' cleanup (025-02)**, by its plan: prune (to 18:00) and
  notes (to 16:30) from 13:31; names when prune has landed (to 21:00);
  close and, if the week is below 83 %, dups when names has landed (to
  22:00). Each prover lands its own gated step on `main`. The
  coordinator starts each next prover at a check-in and creates
  `cleanup/STOP` at 87 % of the week (75 % at the start, 12 points) or
  91 %, whichever comes first.
* **At 22:00** a script (`/Users/f/fl/bench/2026-11-14/night/
  timing-waiter.sh`, independent of the session) creates `cleanup/STOP`
  if it is not there. When the cleanup is over (STOP, or `ALLDONE` from
  the coordinator) and no Lean process has run for 15 minutes, it
  starts the timing pass (026-15) with its end at Sunday 09:00: about
  four rounds from 22:30.
* **Check-ins** every 20 minutes from 06:00 to 22:59; none from 23:00 to
  05:59, so that the session stays idle while the pass times. The
  watchdog keeps the Mac awake until Sunday 10:00.
* **Not tonight:** 025-03 (F1), proposed for after the timing pass and,
  for its Lean steps, the week's reset (Monday 22:00); `night.sh` (the
  timing pass takes the machine to 09:00).
* **Sunday morning**, by 09:30: the timing pass's tables, the cleanup's
  counts, the summary in `news.md` and here (section 6).


## 6. Outcome

Written 2026-11-15, 06:20, by coord-1114.

* **Done on 14 November:** 026-09, 028-04, 028-10, 028-11 and 028-12
  landed; 007-09 brought up to date; 028-13 registered; the reports
  006-26 (the proofs) and 026-16 (simpler algorithms; F1 accepted).
* **The proofs' cleanup (025-02):** done, lean/ 296,684 to 209,065 lines.
* **The timing pass (026-15):** 026-09 saves 4.7 to 8.6 % of the phase in
  (a) to (c) and 5.8 % in (d); 2026.6 so far against 2026.5 saves 8.6,
  16.0, 8.7 and 5.8 %. Every pair a gain except B/R in (d), within the
  noise.
* **The proofs in the night:** three premises found false as stated
  (`hCoU`, `hU`, `hHL`), so every top theorem holds vacuously. Removed
  with no statement change: `hMF`, `hHL`, `hCoU`; `htb` gone for NoOutside
  runs (F1); `hchk` narrowed to two holder checks. The current theorem
  `invGetScanOK_merges_joint6` has hp, hth, hchk5, htb, d4, l4, hU, hMSF,
  hCoF. Left: `hU`'s true form (an invariant on the nodes a transaction
  leaves out, size unknown), `hMSF` and `hCoF` (likely false as stated;
  need the merge's holder fact), `hchk5` (DelInvJ to be stated at
  afterDelete's calls), `d4` and `l4`.
* **Usage:** the week 72 % at the start, 81 % at 06:20 (ceiling 92 %).
* **Not done:** `night.sh`; the Kindle mail (the Gmail connector cannot
  send); the older top theorems still carry `hCoU` and `hHL` (about 150
  lines to bring them up); one top theorem per route again (several
  variants landed in the night).


## 7. For Frans to decide

Frans, 2026-11-15, 08:33: "1, 2, 3, 5, as you recommend. 4, walk me
through the decisions. The planning for hU, run it with Fable 5.2 High."
So: 1, a planning agent on Fable at high (025-04); 2, DelInvJ first,
then `hMSF`'s and `hCoF`'s true forms; 3, a close step to one top
theorem; 5, the night's decisions by rule stand; 4, walked through.

Decision 4, 006-24's 6 (where "the policy of 13 November, 16:50"
lives), Frans, 08:47: "No, that is not policy. Just a thing we
discussed. I have made no decision on it. We still try to prove
everything now. Once that work is done, I may decide on a general
policy on this." So there is no such policy: proofs are not limited to
spare tokens, and 006-24's "So: no release waits for proofs [...]" was
the coordinator's reading, not Frans's decision.

1. **`hU`, false as stated.** Its true form needs an invariant on the
   nodes a transaction leaves out; no one has found it. Recommended: a
   planning agent (xhigh) for that invariant before more provers; read
   024-22, section 11.1.
2. **`hMSF` and `hCoF`.** Recommended: first state DelInvJ at
   afterDelete's calls (cost2's plan in 024-12, section 1), which the
   rest of `hchk` needs too, then their true forms.
3. **One top theorem again.** Recommended: a short close step that keeps
   `invGetScanOK_merges_joint6` (and the NoOutside one) and removes the
   superseded variants, as 025-02 did.
4. From 006-24, still open: 6 (where the policy of 13 November, 16:50,
   lives) and 8 (the premises to read: 006-26, section 4.3, with its
   correction).
5. Decisions taken by rule in the night, to overturn if wanted: notes'
   two extra docstrings and 007-09 Q2 option B (025-02, section 13.6);
   dups' five renames; close's removal of 5 empty files and 93 empty
   headers.
