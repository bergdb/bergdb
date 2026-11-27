028-71. Investigate: under sustained large commits the stream kept grows far past the live data
==============================================================================================

Status: open (built on a branch, 2026-11-27; done when it lands). Kind:
Investigate. Frans: none.
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


Built
-----

2026-11-27, in 031-06's landing, step 3, on the branch `031-06-pace`
(031-06, `landing.md`, step 3):

* What: a commit's step scans up to its allowance, at most the larger of
  `MAX_STEP_SIZE` (16 kB) and twice the allowance that the application's
  last record and the records after it added, `2 fractionOf(L0 - a)`
  (`Reclaim.commitStepSize`, `STEP_GROWTH_FACTOR`). Until then at most
  16 kB a commit. A commit after small records keeps 16 kB; a commit after
  large ones carries a step of about their size times the fraction, so
  the steps spend the allowance as it grows, with room to catch up. A
  part's step stays at `MAX_STEP_SIZE`.
* When, by whom: `Reclaim.planCommit`, in the plan before the go point;
  the step reserve, 015-50's value limit and the record's room
  (`Db.recordDirtyFits`) bound it as before.
* Deterministic: L0 and a are the stream's before the record (a is read
  off the stream at a start, 031-04's R3), so a restart plans the same.
* Checked: `probes/PaceProbe.java` (the review's `RvPace`, with
  `maintenanceNone()` called directly), the review's runs of F3 and two
  with commits of many small puts at random keys:

  | Commits | Kept x live, before | After | Share, before | After |
  |---|---:|---:|---:|---:|
  | one put of 20 kB      |  7.7 |  8.1 | 0.257 | 0.248 |
  | one put of 100 kB     | 13.8 |  7.2 | 0.171 | 0.279 |
  | one put of 300 kB     | 36.4 |  7.8 | 0.063 | 0.237 |
  | 200 puts of 100 bytes | 21.9 | 10.7 | 0.100 | 0.238 |

  "Kept" is the largest stream kept in the run's last third over the cold
  live data; it was steady from the middle third to the last in each run
  after the change. The figures after include step 3's charge (the
  after-row charge in the record), which changes the share of small
  commits too (0.305 to 0.281 at 200-byte values).


Log
---

2026-11-27. Registered by lead-1127, from the independent review of
031-06's prototype (F3).

2026-11-27. Built in 031-06's landing, step 3 (section Built), on a
branch, gated there; open until it lands.
