# 006-24 Day work, 13 November 2026

Created 2026-11-13 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-13 (coord-1113), a Friday, the progress
and the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1112's handover (006-23, section 6): the tag of 2026.5 (made by
Frans at 06:27), the second prover's run 2 to land, a todo of the tests'
time limits, 027's two questions, 026-04's open point.

Frans's answers:

* 06:38, on the todos: "Yes, register them." (021-28, 021-29.)
* 06:47, "Yes", to coord-1113's recommendation for TP11 (024-12): option
  B, `keyWf` unchanged (what `Keys.toSegments` makes, any length);
  `ScanOK` gets a premise, every key of the run at most `scanFuel`
  segments, which Java meets by L3 (57,344 bytes a transaction, about
  8,192 segments); `scanFuel`'s comment corrected. Rejected: A, `keyWf`
  bounded at L2's 16 segments (BergDB's own long keys pass L2, so runs
  Java makes would leave `Within`); C, a fuel from the structure (changes
  the trusted reader). Also yes: land the run 2 now, and delete the two
  false theorems instead of keeping unbuilt modules.


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents that
change code work in clones and do not commit to `main`. Clones and runs
under `/Users/f/fl/bench/2026-11-13/`; the common brief stays
`/Users/f/fl/bench/2026-11-12/common-brief.md`; heavy runs by
`/Users/f/fl/bench/2026-11-11/slot.sh` (in zsh, name both slots).

Usage: the week at 89 % at 06:33, "tight"; Frans's ceiling 95 % until the
reset on Monday 16 November, 22:00. At most two agents at a time, Opus
5.5 at high.


## 3. The work

| ID | Task | Agent | Result |
|---|---|---|---|
| 024-38 | The tag's record: 024-38 done, 024's log | coordinator | b3f64bb1 |
| 021-28, 021-29 | Two todos registered | coordinator | 9f32bff9 |
| 024-22 | Land the second prover's run 2; ScanOK's premise (B) | tp11b (high) | landed 59510cb5 |
| 024-12 | TP11 option C: the scan's fuel from the parameters; then TP11, TP7 | Codex run 3 (Sol xhigh) | landed 2e71a297: C made; TP11 reduced to TP7 + LatestScanOK |
| 024-12 | TP7, the tree's invariants | Codex run 4 (Sol max) | partial, landed 6caf8750: klong well-formedness through the writer |
| 024-12 | TP7, continued | Codex run 5 (Sol max) | running |
| 024, 015 | Statuses after the release; post-release notes (021-27, 020-29) | tidy (high) | committed ee5712c5 |
| 026-05 | P8: each reclaim step scans at its own time | p8 (xhigh) | landed fe5000ec: back to empty's lag about 1,270 at every n and f |
| 026-06 | A value transformation's failure refuses the transaction | vt (high) | landed 8bd6e3a7..944b4868 |
| 026-07 | The write buffer grows with use (ST8) | wb (high) | running |
| 026-04 | The back-to-empty lag at 10M keys, understood | frac (high) | done 07:44: the phase of reclaim's iteration at the deletes' end (a step scans at its iteration's start), not f; keep 1/4; P8 cures it |
| 021-29 | Unit tests that wait with no timeout | waits (high) | landed dc69b7a6 |
| 021-28 | Unit tests with fixed time limits | limits (high) | landed ffa39b4e |


## 4. Progress

* 06:33 coord-1113 started; coord-1112 closed 06:35.
* 06:47 Frans: TP11 option B; land run 2. Agent tp11b started.
* 06:57 tp11b landed 59510cb5: ScanOK's key premise; false theorems deleted; lake build 272 jobs, axioms standard. Open: a premise on the parameters for the positive TP11 proof (024-12).
* 07:21 Frans: option C instead of B ("OK, do C as recommended"): the proofs for every key length and tree size, no fixed constant; the scan's fuel from the parameters (`Params.fuel`, as the get's). Codex run 3 at xhigh started 07:22 (/Users/f/fl/bench/2026-11-13/cx3/).
* 07:24 Frans away until 09:00; unattended.
* 07:30 Frans 07:30: "Raise the limit to 98% of the usage" (was 95 %).
* 07:30 Frans 07:28: "Let's spend the AI usage left." 026-04 (frac) and 021-29 (waits) started at high.
* 07:36 021-29 landed dc69b7a6 (38 waits bounded, tests only; before-commit OK on 59510cb5 = main).
* 07:44 026-04 explained (frac): the lag follows the phase of reclaim's iterations against n, flipping order three times between 1M and 10M; predicted and measured to within 2 %; keep 1/4; P8 (023-05) removes it.
* 07:38 limits (021-28) started.
* 07:54 Frans 07:53: Codex run 4 at Max on TP7, on top of run 3 (/Users/f/fl/bench/2026-11-13/cx4/).
* 07:57 021-28 landed: the Eviction failure was a race between two reads of a thread's state (not the 2 s deadline); about 90 limits in 20 test files; before-commit OK, and three runs beside 20 CPU hogs OK. Tests only.
* 07:58 Codex run 3 landed 2e71a297 (lake 278 jobs, axioms of 40 theorems standard); 024-12 updated.
* 08:06 Frans 08:04: merge 020-29: landed b0cd3ac4 (lake build 291 jobs, 15 theorems on the standard axioms); 020-29 done.
* 08:09 Frans: usage reset, "plenty of usage left now". Started 2026.6's decided work: 026-05 (P8, xhigh), 026-06 (value transformations, R5), 026-07 (ST8, the write buffer).
* 08:12 tidy done: 024's subitems' statuses (3 open: 02, 12, 22), 015 has no open entry, post-release notes for 021-27 and 020-29.
* 08:41 Frans back.
* 08:47 Frans 08:45 "yes to all" (026-06 Q1 to Q4): 026-06 landed (value and key transformations refuse; gated before-commit, level1, level3); 010-04's R5 line done.
* 08:47 Frans: "Use effort xhigh as default for new agents. We have plenty of AI usage left."
* 08:51 Frans 08:50, yes: 027-02 the trace format kept current; 024-02 moves into 027 as 027-03 (agent sf).
* 08:55 Frans: 024-19 Q2 "Yes as recommended", Q3 "as built" (ea6d1d41).
* 09:12 Frans 09:11, 026-02: QK1 `bergdb.pub.Limits`, QK2 no `isKey`, QK3 "Leave it out. We can easy add it if requested." (no `levelBytes`, no `checkPut`), QK4 2026.6. Agent keys started.
* 09:21 Frans 09:17 and 09:21: the node size fixed at 30 for users, other sizes for tests only: 026-08 registered (3ed1ee7d); 024-19's Q2 revised, Q5 dropped.
* 09:24 Frans 09:23: QM1 and 027-03's section 21 decided work for 2026.6.
* 09:33 Frans, 026-02: Q9-1 `keyBytes` returns long, "Yes"; the new dependency of pub on core (D3) not accepted: "This needs to be discussed. A new package dependency." -> "Yes" to taking the constants through pubimp. The agent keys changes it.
* 09:36 026-02 landed 59c6e4b6: `bergdb.pub.Limits` (keyBytes, checkKey, the constants through pubimp).
* 09:37 Codex run 4 stopped by itself at 09:02 (TP7 partial, 137 theorems); checked (lake 306 jobs, axioms standard) and landed 6caf8750. Run 5 started 09:37 at max, told not to stop at a checkpoint.
* 09:38 Frans: Q34-1 option (b) for 2026.6 after P8: 026-09 registered.
* 09:42 Frans 09:41: 026-05's Q1 to Q4 "Yes to all four." P8 merged with main, gated again before landing.
* 09:54 026-05 (P8) landed fe5000ec, gated on the merged tree (before-commit, level1, level3).
