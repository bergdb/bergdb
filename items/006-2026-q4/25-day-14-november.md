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


## 5. For Frans to decide

From 006-24 (still open): 6 (where the policy of 13 November, 16:50,
lives) and 8 (the 10 premises to read; 006-26, section 4.3, has them in
plain words). Decision 7 (the proofs from here) is answered by 12:16
and 13:00: the cleanup first. 006-24, sections 4 and 5, has each with
its recommendation.
