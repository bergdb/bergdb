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

Frans, 09:10: "Defaults are good. Work unattended, good luck!"


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

* 09:03 W1 landed; 09:04 W2 started.
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
* 09:04 W2: prover delj started (Opus xhigh, stop 15:00).
* 09:19 W3 done: 025-04's plan (coord-1114's agent), route (b): the
  split from a state with the chain's bitmap set, no statement change;
  5 steps, 700 to 1,200 lines; committed 6ca79849. coord-1114 closed
  09:20.
* 09:22 W4: prover hu started (Opus xhigh, stop 16:00), 025-04's
  steps 1 to 5.
* 09:50 delj LANDED 62e55741 (gate-1 PASS): root collapse's
  `checkRoot` proved (`opDelChk5OKR_of_chk6`, from `hMSF`'s MergeStepOK
  and `hCoF`); `invGetScanOK_merges_chk6` (hp, hth, hchk6, htb, d4, l4,
  hU, hMSF, hCoF), where `hchk6` is `hchk5` without `checkRoot`, with
  DelInvJ and the books at afterDelete's calls stated as a check. Left
  in `hchk6`: carrying DelInvJ, and the merge's `checkFree`.
* 09:56 hu LANDED 3f696db6 (53a7f745 merged with 62e55741; the merged
  tree's gate PASS): 025-04's steps 1 to 5, `hU` out of the joint route.
  `invGetScanOK_merges_noU` has the premises hp, hth, hchk5, htb, d4,
  l4, hMSF, hCoF; checked beyond the gate: audited, on the standard
  axioms, the trusted closure unchanged with it, and its statement is
  `invGetScanOK_merges`'s without exactly the `hU` premise. The old top
  theorem is now a corollary of it. hu goes on with step 6 (the
  NoOutside route).
* 09:59 hu LANDED 5bb18a72 (gate PASS on main's tree): step 6,
  `invGetScanOK_merges_noOutside_noU` (hp, hth, hchk, d4, l4, hHL,
  hMSF, hCoF, hCoU), audited as above, its statement
  `invGetScanOK_merges_noOutside`'s without exactly `hU`; still vacuous
  there through `hHL` and `hCoU`. 025-04 done: about 2,300 lines, of
  which about 1,100 are now unused (for a close step). hu goes on with
  `d4`, then `l4`.
* 10:04 delj LANDED e1e9b836: `invGetScanOK_merges_chk6` now on the
  route without `hU`: hp, hth, hchk6, htb, d4, l4, hMSF, hCoF. With it
  audited, the closure grows only by `hchk6`'s 31 new definitions.
* 10:11 delj LANDED ada8757c: DelHoleJ (DelInvJ and the books) carried
  to the leaf's call of afterDelete; `invGetScanOK_merges_chk7` replaces
  `_chk6` (hp, hth, hchk7, htb, d4, l4, hMSF, hCoF; against
  `invGetScanOK_merges_noU` only `hchk5` became `hchk7`). Next for delj:
  the upward delete's climb and loop, which leaves only the merge's
  `checkFree` in `hchk`.
* 10:04 hu on `d4`: 2,000 to 3,000 lines, more than today; it gates a
  dead-bound framework for every writer function but the merge, then
  the merge, and writes the plan for the rest; `l4` a plan only.
* 10:20 delj LANDED fbce47ac: DelInvJ carried to both of afterDelete's
  calls (DelHoleClimb.lean); `invGetScanOK_merges_chk8` replaces `_chk7`;
  `hchk8` has one check left, the merge's `checkFree`. W2's first task
  (DelInvJ) done.
* 10:57 hu LANDED 3008ae57: `d4`'s pieces, additions only: the dead
  bound (every node the writer reads at most theta dead klongs, well
  formed) kept by every write of the delete but the merge itself
  (DeadLocal.lean, DeadSplit.lean, DeadDelete.lean). Left for `d4`: the
  merge, the merges' loop, the case lemmas; the plan for the rest and
  for `l4` in 024-12, section 1. DeadSplit.lean takes about 7 minutes to
  elaborate (for a close step).
* 11:11 delj LANDED 079c89e5: the merge's `checkFree` proved at every
  merge of the merges' loop from a call of afterDelete
  (DelMergeUp.lean); `hchk` GONE. `invGetScanOK_merges_free`: hp, hth,
  htb, d4, l4, hMSF, hCoF; its statement is `invGetScanOK_merges_noU`'s
  without exactly `hchk5`; audited, on the standard axioms, the closure
  unchanged with it. delj goes on with `hMSF` and `hCoF`.
* 11:13 delj LANDED c2bfeded (as 99e90e96): `ht_merge_of_J`, the
  heights' walk through every merge of the merges' loop with no holder
  premise; additions, toward `hMSF` and `hCoF`.
* 11:17 hu LANDED e097d266 (as d4cc7ca8): `d4` GONE.
  `invGetScanOK_merges_free_noD4`: hp, hth, htb, l4, hMSF, hCoF; its
  statement is `invGetScanOK_merges_free`'s without exactly `d4`;
  audited, on the standard axioms, the closure unchanged with it. By a
  consumer change: the dead bound is carried write by write, through
  the merge (from DelInvF's ranges) and the merges' loop, by copies of
  the route lemmas; `d4` as stated (for RunOK runs) is not proved, as
  its proof needs the induction's facts. hu goes on with `l4`.
* 11:17 hu ended (landed 584c73af: `l4`'s State note in 024-12,
  section 1). `l4` not started: it builds the joint induction, so its
  proof gets none of the induction's facts; a near-copy of
  `jointHtJ_reachedJ` first (about 300 lines), a non-local invariant;
  3,000 lines or more by copies, much less by option (b), a statement
  change for Frans (024-12, section 1). No prover in its place: with
  four points left to 91 %, delj goes on alone.
* 11:17 W5: `night.sh` started on `main` 584c73af.
* 11:20 to 11:37 delj LANDED 2c4009a9, 4108d6b6, bc2cdd65, 1364f7e3:
  run checks of `hMSF`'s and `hCoF`'s true forms (139 of 3,032 merges
  made the tree deeper, so "a merge keeps the depth" is false; no
  operation of 17,390 made it deeper twice; the heights stayed within
  H); `mergeFits_of_htJ` and `collapseFits_of_htJ`, the true forms for
  one merge and one replaceRoot given the heights' books at the step's
  start. Left: the heights' bound across a delete's steps, the books
  carried to each step, and the reading's walks that use MergeStepOK
  (024-12, section 1).
* 11:37 delj stopped early for the usage; resumed at 11:39 on the same
  task until the STOP file (91 %).


## 8. Outcome

Not yet.
