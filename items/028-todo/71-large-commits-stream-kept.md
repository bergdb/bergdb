028-71. Investigate: under sustained large commits the stream kept grows far past the live data
==============================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-27 by Frans Lundberg.

What: a commit allows at most one reclaim step, and a step copies at
most about 16 kB (`MAX_STEP_SIZE`), whatever the commit's size. When the
commits are much larger than that, reclaim uses only a small part of its
fraction and falls behind, and the stream kept grows with the commits'
size. Measured by the independent review of 031-06's prototype (031-06,
`review-fable.md`, F3; its probe `RvPace`): 4,000 cold keys of 1,000
bytes (4.2 MB live), a commit every 200 ms of database time, a retain
duration of 1 s:

* commits of 20 kB: reclaim's share of the growth 0.257, the stream kept
  7.7 times the live data;
* commits of 100 kB: 0.171, and 13.8 times;
* commits of 300 kB: 0.063, and 36.4 times, steady from third to third
  of the run; 35.8 times on 031-05's prototype.

The rule of one step of at most 16 kB a commit is `main`'s too (the
review marks the finding as `main`'s as well; it ran the two
prototypes).

Why: the stream kept is then about 2 x (live / 16 kB) x the commit's
size, not a small multiple of the live data, and the bound that 031-06's
`SafetyProbe` states did not hold in the run with commits of 300 kB
(188 % of it). Space, not safety: no value is lost and no cut is unsafe.

Frans: none.

Done when: a commit's step is sized by its allowance (the fraction of
the stream's growth, less what is charged), so that large commits carry
more of reclaim's work, and the stream kept is bounded in the review's
run (step 3 of 031-06's landing, 031-06, section 9); or the bound that
holds is stated in 027 and in the Javadoc. P1 is measured with it: a
larger step is a longer scan before the go point (the review's F4).

First step: `Reclaim.planCommit` and `MAX_STEP_SIZE` on 031-06's branch;
the review's `RvPace` (031-06, `review-probes/`).


Log
---

2026-11-27. Registered by lead-1127, from the independent review of
031-06's prototype (F3).
