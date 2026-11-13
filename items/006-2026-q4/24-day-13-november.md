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
| 024-22 | Land the second prover's run 2; ScanOK's premise (B) | tp11b (high) | running |


## 4. Progress

* 06:33 coord-1113 started; coord-1112 closed 06:35.
* 06:47 Frans: TP11 option B; land run 2. Agent tp11b started.
