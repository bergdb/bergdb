# 006-27 Day work, 15 November 2026

Created 2026-11-15 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-15 (coord-1115), a Sunday, unattended from
09:00 until Monday 16 November, 07:00: the progress and the outcome. The
way of working is 013-02's (the coordinator) and 013-01's (the
unattended night).


## 1. The request

coord-1114's handover (006-25, sections 4, 6 and 7): tops (one top
theorem per route, decision 3) done on its branch but not landed, as the
permission system refused the agent's edit of its gate; the plan for
`hU`'s true form (025-04) being written; decision 2's prover (DelInvJ,
then `hMSF`'s and `hCoF`'s true forms) not started; decision 8 (the
premises Frans reads) open.

Frans's words:

* 08:57, on tops' gate (option (a): he approves the edit; (b) he reads
  the 41 definitions first; (c) the variants stay): "Yes I approve. (a)
  as recommended."
* 08:59: "It is Sunday, so I don't plan to work with this today. Can
  you work unattended for the rest of the day with the proofs as far as
  possible?"

The questions asked at 09:05, in text, each with a default that goes
ahead without an answer:

1. Until when: Monday 07:00, the provers going on through the night.
2. Usage: the week 82 % at 08:54; Frans's ceiling 92 % (2026-11-14,
   12:16); the provers stop at 91 %, Opus at xhigh.
3. What lands on `main`: gated additions only, as in the night of 14
   to 15 November; a change of an existing premise's definition (such
   as `hU` replaced by its true form) stays on a gated branch for Frans.
4. `night.sh` (not run since 12 November; 026-09, 028-04, 028-10 and
   028-12 landed since): run this afternoon on `main`, beside the
   provers.

Answers: none yet; the defaults hold.


## 2. The ground rules

013-01, section 4, and:

* At most two provers at a time (usage tight), Opus 5.5 at xhigh
  (Frans, 2026-11-13: when tokens are the limit, Opus xhigh). The
  provers' common brief: `/Users/f/fl/bench/2026-11-15/day/common.md`.
* Provers gate each step with
  `/Users/f/fl/bench/2026-11-15/day/gate-1115.sh` (base: `main`
  9e408f06; the trusted closure and the two top theorems' statements
  unchanged) and report GATED; the coordinator lands with 025-02's
  `land.sh`. Provers do not edit a gate.
* STOP for all provers: `/Users/f/fl/bench/2026-11-15/day/STOP`, set by
  the coordinator at a week of 91 %.


## 3. The work

* **W1, tops** (decision 3): land d6cedb46 after a gate whose base is
  `main`'s `joint6` (Frans's (a)). The gate's base, the agent's
  `guard-main.txt`, is checked against a fresh guard run on `main`.
* **W2, prover delj** (decision 2): DelInvJ at afterDelete's calls
  (cost2's plan, 024-12, section 1); what is left of `hchk5`; then
  `hMSF`'s and `hCoF`'s true forms. Stop 15:00, then a successor from
  its report if the usage allows.
* **W3, the plan for `hU`'s true form** (025-04, coord-1114's agent
  hu-plan, Fable at high): commit 025-04 when it is done (about 11:00).
* **W4, a prover for `hU`'s true form**, from 025-04's plan, after W3.
* **W5, `night.sh`** on `main` (question 4).
* If there is time: `d4`, `l4`.


## 4. The principles

The provers keep 013-01's: no `sorry`, no new axiom, no change of a
trusted file or an existing statement on `main`; KISS (Frans,
2026-11-13).


## 5. The timeline

* 09:03 W1 landed; 09:10 W2 started.
* About 11:00 W3; then W4.
* The afternoon: W5.
* 15:00 delj's stop; its successor.
* 06:00 Monday: the morning summary (013-01, section 8).


## 6. If the session stops

The state is in `/Users/f/fl/bench/coord/2026-11-15/state.md`; the
watchdog writes `news.md` if the session's process is gone. The
provers' branches and reports are in
`/Users/f/fl/bench/2026-11-15/day/NAME/`; a successor starts from
`REPORT.md`.


## 7. Progress

* 08:54 coord-1115 started; 08:55 coord-1114's handover, its last hunk
  committed (7b02b6e1).
* 08:57 Frans approved tops' gate change (a). 09:01 the agent's base
  equals a fresh guard run on `main` (10,832 lines); gate-tops PASS:
  the trusted closure differs from the cleanup's base by exactly
  `NoOutside`, the 41 definitions of `hchk5` and `StateOK` leaving; the
  two top theorems' statements equal `main`'s `joint6` and
  `noOutside'`; 24 theorems on the standard axioms; 41 traces.
* 09:03 tops LANDED 9e408f06, pushed: `invGetScanOK_merges` (hp, hth,
  hchk5, htb, d4, l4, hU, hMSF, hCoF) and
  `invGetScanOK_merges_noOutside` (hp, hth, hchk, d4, l4, hU, hHL,
  hMSF, hCoF, hCoU); 361 lines of variants removed.
* 09:10 W2: prover delj started (Opus xhigh, stop 15:00).


## 8. Outcome

Not yet.
