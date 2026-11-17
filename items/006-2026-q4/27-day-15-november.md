# 006-27 Day work, 15 November 2026

Created 2026-11-15 by Frans Lundberg. Status: done (the outcome
written 14:45; unattended until Monday 07:00 with nothing running). The plan for the
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
  9dc5ba78; the trusted closure and the two top theorems' statements
  unchanged) and report GATED; the coordinator lands with 025-02's
  `land.sh`. Provers do not edit a gate.
* STOP for all provers: `/Users/f/fl/bench/2026-11-15/day/STOP`, set by
  the coordinator at a week of 91 %.


## 3. The work

* **W1, tops** (decision 3): land 29632e54 after a gate whose base is
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
  committed (8bf67da8).
* 08:57 Frans approved tops' gate change (a). 09:01 the agent's base
  equals a fresh guard run on `main` (10,832 lines); gate-tops PASS:
  the trusted closure differs from the cleanup's base by exactly
  `NoOutside`, the 41 definitions of `hchk5` and `StateOK` leaving; the
  two top theorems' statements equal `main`'s `joint6` and
  `noOutside'`; 24 theorems on the standard axioms; 41 traces.
* 09:03 tops LANDED 9dc5ba78, pushed: `invGetScanOK_merges` (hp, hth,
  hchk5, htb, d4, l4, hU, hMSF, hCoF) and
  `invGetScanOK_merges_noOutside` (hp, hth, hchk, d4, l4, hU, hHL,
  hMSF, hCoF, hCoU); 361 lines of variants removed.
* 09:04 W2: prover delj started (Opus xhigh, stop 15:00).
* 09:19 W3 done: 025-04's plan (coord-1114's agent), route (b): the
  split from a state with the chain's bitmap set, no statement change;
  5 steps, 700 to 1,200 lines; committed 37aa2d82. coord-1114 closed
  09:20.
* 09:22 W4: prover hu started (Opus xhigh, stop 16:00), 025-04's
  steps 1 to 5.
* 09:50 delj LANDED 442a9557 (gate-1 PASS): root collapse's
  `checkRoot` proved (`opDelChk5OKR_of_chk6`, from `hMSF`'s MergeStepOK
  and `hCoF`); `invGetScanOK_merges_chk6` (hp, hth, hchk6, htb, d4, l4,
  hU, hMSF, hCoF), where `hchk6` is `hchk5` without `checkRoot`, with
  DelInvJ and the books at afterDelete's calls stated as a check. Left
  in `hchk6`: carrying DelInvJ, and the merge's `checkFree`.
* 09:56 hu LANDED 425b5027 (3b61cfc9 merged with 442a9557; the merged
  tree's gate PASS): 025-04's steps 1 to 5, `hU` out of the joint route.
  `invGetScanOK_merges_noU` has the premises hp, hth, hchk5, htb, d4,
  l4, hMSF, hCoF; checked beyond the gate: audited, on the standard
  axioms, the trusted closure unchanged with it, and its statement is
  `invGetScanOK_merges`'s without exactly the `hU` premise. The old top
  theorem is now a corollary of it. hu goes on with step 6 (the
  NoOutside route).
* 09:59 hu LANDED d8fd54ab (gate PASS on main's tree): step 6,
  `invGetScanOK_merges_noOutside_noU` (hp, hth, hchk, d4, l4, hHL,
  hMSF, hCoF, hCoU), audited as above, its statement
  `invGetScanOK_merges_noOutside`'s without exactly `hU`; still vacuous
  there through `hHL` and `hCoU`. 025-04 done: about 2,300 lines, of
  which about 1,100 are now unused (for a close step). hu goes on with
  `d4`, then `l4`.
* 10:04 delj LANDED 42ebc9cb: `invGetScanOK_merges_chk6` now on the
  route without `hU`: hp, hth, hchk6, htb, d4, l4, hMSF, hCoF. With it
  audited, the closure grows only by `hchk6`'s 31 new definitions.
* 10:11 delj LANDED 90acb7d3: DelHoleJ (DelInvJ and the books) carried
  to the leaf's call of afterDelete; `invGetScanOK_merges_chk7` replaces
  `_chk6` (hp, hth, hchk7, htb, d4, l4, hMSF, hCoF; against
  `invGetScanOK_merges_noU` only `hchk5` became `hchk7`). Next for delj:
  the upward delete's climb and loop, which leaves only the merge's
  `checkFree` in `hchk`.
* 10:04 hu on `d4`: 2,000 to 3,000 lines, more than today; it gates a
  dead-bound framework for every writer function but the merge, then
  the merge, and writes the plan for the rest; `l4` a plan only.
* 10:20 delj LANDED 3189efbe: DelInvJ carried to both of afterDelete's
  calls (DelHoleClimb.lean); `invGetScanOK_merges_chk8` replaces `_chk7`;
  `hchk8` has one check left, the merge's `checkFree`. W2's first task
  (DelInvJ) done.
* 10:57 hu LANDED b4a1e89d: `d4`'s pieces, additions only: the dead
  bound (every node the writer reads at most theta dead klongs, well
  formed) kept by every write of the delete but the merge itself
  (DeadLocal.lean, DeadSplit.lean, DeadDelete.lean). Left for `d4`: the
  merge, the merges' loop, the case lemmas; the plan for the rest and
  for `l4` in 024-12, section 1. DeadSplit.lean takes about 7 minutes to
  elaborate (for a close step).
* 11:11 delj LANDED 1fdb6127: the merge's `checkFree` proved at every
  merge of the merges' loop from a call of afterDelete
  (DelMergeUp.lean); `hchk` GONE. `invGetScanOK_merges_free`: hp, hth,
  htb, d4, l4, hMSF, hCoF; its statement is `invGetScanOK_merges_noU`'s
  without exactly `hchk5`; audited, on the standard axioms, the closure
  unchanged with it. delj goes on with `hMSF` and `hCoF`.
* 11:13 delj LANDED 4b03fcf6 (as 5e5aa6fa): `ht_merge_of_J`, the
  heights' walk through every merge of the merges' loop with no holder
  premise; additions, toward `hMSF` and `hCoF`.
* 11:17 hu LANDED 6a4afcc9 (as 4fdd9099): `d4` GONE.
  `invGetScanOK_merges_free_noD4`: hp, hth, htb, l4, hMSF, hCoF; its
  statement is `invGetScanOK_merges_free`'s without exactly `d4`;
  audited, on the standard axioms, the closure unchanged with it. By a
  consumer change: the dead bound is carried write by write, through
  the merge (from DelInvF's ranges) and the merges' loop, by copies of
  the route lemmas; `d4` as stated (for RunOK runs) is not proved, as
  its proof needs the induction's facts. hu goes on with `l4`.
* 11:17 hu ended (landed af943131: `l4`'s State note in 024-12,
  section 1). `l4` not started: it builds the joint induction, so its
  proof gets none of the induction's facts; a near-copy of
  `jointHtJ_reachedJ` first (about 300 lines), a non-local invariant;
  3,000 lines or more by copies, much less by option (b), a statement
  change for Frans (024-12, section 1). No prover in its place: with
  four points left to 91 %, delj goes on alone.
* 11:17 W5: `night.sh` started on `main` af943131.
* 11:20 to 11:37 delj LANDED b4115f95, 7c28e601, ff771213, ad568556:
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
* 11:45 delj ended (its plan note landed, 5d635f46): the bound across a
  delete's steps has no local invariant (a root a step adds may be split
  by a later step of the same delete), and carrying the heights to the
  calls that use MergeStepOK is a restructure of the reading (about 100
  lemmas in 42 files, or a checked copy); it recommended a planning
  agent, as for `hU`.
* 11:48 025-05 created (68e9addd): the plan for `htb`, `hMSF` and
  `hCoF`; planning agent hplan started (Opus xhigh, stop 14:00).
* 12:39 025-05 ready (96ac19ab): route P, a fuel above every node id.
  Every writer state with PutInv fits its next id, so at a fuel above
  both p.fuel and the next id the reading is always right, and the
  loops keep it with no fit premise: `hMSF` and `hCoF` leave by a
  consumer change, 6 steps, 1,750 to 3,500 lines; the first of the six
  consumers already proved in scratch. `htb` after it (part 2, 2,500 to
  5,000 lines). Run checks: 4,573 take-backs, 0 failures.
* 12:43 prover fit started (Opus xhigh): 025-05's part 1.
* 13:02 to 13:37 fit LANDED 025-05's part 1, steps 1 to 6 (89273873,
  0846a5e8, 85d38375, c4cf497c, 8f58da68, 78545945): `hMSF` and `hCoF`
  GONE. `invGetScanOK_merges_noFit` (DeadTop.lean): hp, hth, htb, l4;
  its statement is `invGetScanOK_merges_free_noD4`'s without exactly
  `hMSF` and `hCoF`; audited, on the standard axioms, the closure
  unchanged with it; `invGetScanOK_merges_free_noD4` its corollary. No
  statement changed: each loop got one proof under a condition, each
  family a form over an invariant, the old ones their instances; about
  2,750 lines added and 630 removed in 22 files.
* 13:40 prover htb started (Opus xhigh): 025-05's part 2, `htb` out.
  13:59 LANDED 358fadc6 (the joint induction without `htb`, reduced to
  stratum families); 14:12 LANDED e834fda7 (one family; 4 of its 7
  cases proved). Top theorem unchanged.
* 14:04 W5: `night.sh` on af943131 FAILED one step, the night tests:
  CorruptStreamTester found a damaged node (its checksum made right)
  whose start or reads did not end in 60 s; it repeats alone. The other
  15 steps OK. Registered as 028-14 (Investigate); news.md entry.
* 14:28 to 14:38 htb LANDED 8c07356c, 50e82214, 17498510: 025-05's
  step 7 done (the joint induction with no `htb`, no fit and no
  heights' bound; `hchk` with no `htb`), and step 9's reduction:
  `invGetScanOK_merges_tbL` (hp, hth, l4, htbL), where `htbL`
  (`TakeBelowFuelDelSL`, two new definitions) is `htb` at one delete of
  the induction's runs whose start has the first stratum's facts;
  `invGetScanOK_merges_noFit` its corollary. Left: step 8, `htbL` from
  the take-back sites.
* 14:40 htb ended (its notes landed, 4e571378): step 8 needs a frame
  argument over a delete's segment roots, too large for the usage left.
  No new prover: the week at 90 %, under a point to the 91 % stop.


## 8. Outcome

Written 2026-11-15, 14:45; the provers stopped at a week of 90 %, by
the usage; nothing runs until Frans is back.

**The key tree's top theorem.** In the morning,
`invGetScanOK_merges` (the joint route) had 9 premises, and held
vacuously: `hU` is false as stated. The best theorem on `main` now is
`invGetScanOK_merges_tbL` (DeadTop.lean): TP7, TP10 and TP11 for Java's
parameters from 4 premises, `hp`, `hth`, `l4` and `htbL`. `hp` and `hth`
are the parameters' conditions (`mergeParamsOK_java`, `theta_java`). No
premise left is known to be false: `l4` (a delete keeps the live
counts) and `htbL` (a node a delete takes back, found at its start, is
below the fuel) are tested on runs with no failure. Each step was
audited: standard axioms, the trusted closure unchanged, and the new
theorem's statement the old one's without exactly the premises removed
(`htbL` in place of `htb` adds its two definitions).

| Premise | Gone by | Prover | Landed |
|---|---|---|---|
| `hU` | the split from a state with the bitmap set (025-04) | hu | 425b5027 |
| `hchk` | DelInvJ carried to afterDelete's calls | delj | 1fdb6127 |
| `d4` | the dead bound carried write by write | hu | 4fdd9099 |
| `hMSF`, `hCoF` | route P, a fuel above every node id (025-05) | fit | 78545945 |
| `htb` to `htbL` | the joint induction with no `htb` (025-05, step 7) | htb | 17498510 |

All by consumer changes and additions: no existing statement changed
(tops at 09:03, Frans's (a), renamed the top theorems). `hU` also left
the NoOutside route (d8fd54ab); that route still holds vacuously
through `hHL` and `hCoU`. lean/ grew from 222,700 to 236,184 lines.
Plans: 025-04 (done), 025-05 (part 1 done, part 2 at step 8).

**Not done.** `l4`: not started; its plan in 024-12, section 1 (3,000
lines or more by copies). `htbL`: 025-05's step 8, a frame argument
over a delete's segment roots (025-05, section 8). The superseded
corollaries (`invGetScanOK_merges_noU`, `_free`, `_free_noD4`,
`_noFit`, ...) and about 1,100 unused lines stay for a close step.

**night.sh** on af943131: 15 of 16 steps OK; the night tests failed
on a damaged node whose start or reads did not end (028-14).

**Usage.** The week from 82 % (08:54) to 90 % (14:40); five provers
and two planning agents, Opus at xhigh.

**For Frans to decide:**

1. **`l4`'s route.** hu's option (b): `DelStepsCaseOK`'s obligations
   carry an extra invariant (a statement change of definitions; also
   removes `d4`'s `_D` copies), or copies (3,000 lines or more).
   Recommended: a planning agent after the week's reset, which weighs
   (b) against route P's generic families (they may give what (b)
   needs with no statement change). 024-12, section 1.
2. **`htbL`, step 8.** Go on after the reset (today's provers were
   much faster than the plans' estimates), or keep `htb` as a tested
   premise. Recommended: go on. 025-05, sections 6.2 and 8.
3. **A close step to one top theorem per route** (decision 3 of
   006-25): `invGetScanOK_merges_tbL` as the top theorem, the
   superseded corollaries and unused lines removed; the gate's base
   moves, as for tops (Frans's (a) this morning). Recommended: after
   1 and 2, or now if the top theorem's name should carry today's
   result.
4. **What Frans reads** (006-24's decision 8, still open).
   Recommended: a short update of 006-26 for today's theorem and its
   two premises, after the reset.
5. **028-14**, the damaged node whose start does not end: an
   Investigate entry, low priority (best effort, 2026-11-12).
   Recommended: one agent on it after the reset.
