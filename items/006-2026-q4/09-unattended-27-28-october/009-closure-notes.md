009's closure: notes on the draft
=================================

Written 2026-10-27, about 17:00, by Claude (Opus 5.5, Claude Code), a
subagent of the session of 006-09, at Frans's choice (16:41) to draft 009's
closure now and finish it in the morning, after the quiet block (W1.3,
W1.4, `perf-ab.sh`). Made in the clone /Users/f/fl/bench/006-09/w9 (from
`0f978f8`); nothing in `java/` or `lean/`. Both diffs pass
`git apply --check` on the main tree as of 17:00.

Every number that waits for tonight is `[TBD ...]`: 22 in
009-closure.diff, 5 in 009-closure-done.diff (`grep -n TBD`).


# 1. The two diffs

**009-closure.diff**, to apply in any case, with its `[TBD]`s filled in
(target 2 "met" or "not met"):

1. 009-01, the header: "draft" becomes "approved and carried out". The log
   has no word "approved" for 009-01; Frans's "Go ahead and adjust 01 and
   then write 02." (2026-10-25, 13:25) is read as the approval, as 02 was
   to come "when 01 approved". Section 8: G3 moves from "Open" to
   "Decided with 009-02" (it was decided on 2026-10-25).
2. 009-01, section 1: a new list "Where the targets stand", one line per
   item of "Done when". 1, 3 to 6 and 8 met or recorded; 2 and 7 have
   placeholders (2: the soak, ScaleBench C; 7: `perf-ab.sh`).
3. 009-03, section 0: rewritten for `main` with 005-46 (sections 9,
   005-46's "Measured after the change", 009-04, section 8); the step-3d
   figures kept where still current, marked as such. Placeholders: the
   soak, ScaleBench C, Props, `perf-ab.sh`, and the section of 005-46
   where tonight's results go.
4. 009-03, section 8 ("Still to run"): what became of each run listed on
   2026-10-26, the quiet block's three runs with `[TBD]`, and a line that
   LargerThanMemory was not reported with handles.
5. docs/levels.md, section 7's limits: "confirm it in 006-09's quiet
   block" replaced by the soak's figures (`[TBD]`), and a new bullet: the
   waits above 20 ms left are the collector's, s1's disk and the writer's
   waits for room; target 2 `[TBD: met]`.
6. README.md: a paragraph "Pauses (2026-10-28)" after the two known
   limits: BergDB's own waits within about 20 ms (`[TBD]`), the collector
   and a slow disk on top. The Level 4 row is unchanged.
7. 010-01, P1: the force and cut deviation is now "fixed" (005-46). Beyond
   the brief, two more bullets of P1 updated, as they were stale: the
   collector (Shenandoah's default mode meets the target, not the
   generational one; the target counts BergDB's code only) and 007-03's
   deadline (the readers no longer wait). Drop these two if unwanted.

**009-closure-done.diff**, to apply only if the soak confirms target 2:
009's status line set to done, its log entry of 2026-10-28 (placeholders:
the time, the soak's figures, the section of 005-46, and what is left of
009 as Frans decides, section 3 below), and items/readme.md's index line
for 009 set to done.


# 2. To check in the morning

1. The results: `items/005-todo/46-stream-file-lock/night/out/` (soak/,
   props/, scalebench-c/, perf-ab/) and the conductor's
   /Users/f/fl/bench/006-09/night/results.txt. Fill every `[TBD]`.
2. If the soak shows a commit or read above about 20 ms that is BergDB's
   (a cut, a force, a lock), target 2 is not met: write "not met" and why
   in 009-01 and 009-03, do not apply the done diff, and 005-46 opens
   again (its header says so).
3. `git apply --check` again: the seven files may have changed since
   `0f978f8`.
4. Whether the 2,760 ms get on s1 (009-03, section 9), put down to s1's
   disk or the kernel's reclaim, is accepted as not BergDB's: a judgement
   for Frans that target 2's "met" rests on.
5. Target 7 needs `perf-ab.sh`'s alerts read as `performance.sh` says (two
   runs before calling one a regression).


# 3. Left of 009 outside target 2: recommendations for Frans

None of these is in 009-01's "Done when", so none needs to hold 009 open.

* **T9 and T12 over handles, then the old Lean files go.** Level 3's
  reclaim theorems with eviction (`T9_readCut`, `T12_evictCut`) are stated
  over Evict.lean's runs, so none of the 42 Phys and Evict modules can go
  (009's log, 2026-10-26, 09:00). Recommended: a new 005 entry. It is Lean
  work of its own (M), and it would also cut the Lean size (about 47k
  lines on 2026-10-21).
* **LargerThanMemory's report.** 009-01's phase 5 listed it; it passes in
  `level4.sh` in full and so in `night.sh`, but no figures with handles
  are in 009-03. Recommended: in 009, a short paragraph in 009-03 from the
  latest night run's log, no new run; or nothing, since ScaleBench at 10M
  keys covers more.
* **The test schedules still walk** (`VALUES`, `EVERY`, `RANDOM` in
  `Eviction.afterTransaction`, with `Residents.walk` and `resync`), as
  009-02 planned for step 3b; test-only, outside the budget path.
  Recommended: nothing now; a 005 entry only if Level 4's code is to
  shrink. Their comments still say "slots" (pointers, since 009).
