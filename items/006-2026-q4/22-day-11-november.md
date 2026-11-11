# 006-22 Day work, 11 November 2026

Created 2026-11-11 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-11 (coord-1111), a Wednesday, the progress
and the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1110's handover (006-21, section 9): release 2026.4 made at 04:55;
2026.5 started (024-01 to 024-03); four points for Frans.

Frans, 06:44, on the aim of 2026.5: "I first though that "stable stream"
should be the theme of the release. But after sleeping on it, I am more
more leaning towards "solid algos". [...] The internal core algorithms of
the database must be right. This is what we want to prove correct. And
not change later." 06:50: "both storage and operations are proportional
to the value they bring to the user." 06:54: "Yes, create a subagent at
High that updates 024. Create a subitem nn-aim for this release
theme/aims as stated by you above."


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents that
change code work in clones under `/Users/f/fl/bench/2026-11-11/` and do
not commit to `main`; item-only agents write their own file in the main
tree; heavy runs one at a time. Effort: the session xhigh; subagents
high, xhigh for a hard task. At most 8 agents at a time (Frans,
2026-11-10, 09:21).


## 3. The work

| ID | Task | Agent | Result |
|---|---|---|---|
| 024-04 | The aim of 2026.5, "solid algorithms"; 024's readme | aim (high) | done 06:58 |
| 024-05 | The aim against the known cases: the list, bounds, tests | cases (high) | done 07:10 |
| 024-06 | The model gap: the Lean model against 2026.4's code | gap (high) | done 07:08 |
| 026 | Item for release 2026.6, "a stable stream" (preliminary) | coordinator | done |
| 024-07 | The last touch of a reclaim iteration (CL7): design, fix | touch (xhigh) | |
| 024-08 | MEM 327 at 10M keys against 129.6 at 1M: the cause | mem (high) | done 07:25 |
| 024-09 | The tie of model and code repaired (024-06, A1 to A4) | tie (xhigh) | |
| 022-07 | The C clone to release 2026.4 as released (CC1) | cc (high) | |
| 024-10 | The builder's rule "the last operation wins" (CA1) | low (high) | |
| 024-11 | The underfill fix: a design study, no code | fill (xhigh) | |
| 024-12 | The key tree's model in Lean, run against Java | tree (xhigh) | |

024-04 to 024-06 are read-only studies. 024-07 to 024-10 and 022-07 work
in clones under `/Users/f/fl/bench/2026-11-11/<name>/clone` on their own
branches, by the common brief `/Users/f/fl/bench/2026-11-11/common-brief.md`
(heavy runs one at a time by the lock `heavy.lock` there). Nothing lands
on `main` without Frans's word.

Frans, 07:08, on the coordinator's proposal (CL7, the heap growth, the
Lean model when 024-06 has reported, the C clone): "Do so, start 1 to 4
in subagents. Also implement the "last operation wins" using a separate
agent. I am back 09:00." A record format change in 2026.5: "Yes." Heavy
measurements at 10M keys while he is away: "Yes." 07:10: "I changed
Effort to High (was Medium)" (the session's effort; his word).

Task 3 was planned as "the Lean model for 2026.4's delete path". 024-06
found that the model has no keys at all, so that no proof covers the
delete path and none broke; the task became 024-06's first step, the
repair of the tie (A1 to A4), which needs no decision. The key tree in
Lean (024-06, B) waits for Frans's answers to 024-06's questions.


## 4. If the session stops

The state is in `/Users/f/fl/bench/coord/2026-11-11/state.md`; each
agent's file ends with a State note. `/coordinator resume` restarts
from them.


## 5. Progress

* 06:38 coord-1111 started; coord-1110 closing (its message 06:39:
  nothing of its runs or is uncommitted).
* 06:44 to 06:54 The aim of 2026.5 discussed and changed to "solid
  algorithms" (section 1).
* 06:56 Started 024-04, 024-05, 024-06.
* 06:58 Item 026 created. 07:00 024-04, 026 and this plan committed
  (bddd9aad); 07:02 the old theme marked in 024-02 and 024-03 (1826cb37).
* 07:08 024-06 done. 07:10 024-05 done: MEM 327 probably a matter of key
  shape (7-byte keys make two segments), not of size; 024-03's "25
  versions a get" is wrong (1.9 loads a get); the last touch may reach
  the record limit at 100M keys (not read yet). Both sent on to mem and
  touch.
* 07:10 Unattended until 09:00. Started touch, mem, tie, cc, low.
* 07:23 Frans: 2026.5 may refuse 2026.4's databases ("2. as
  recommended"); item commits may be pushed ("Sure, feel free to
  push"). 07:24 started fill (024-11).
* 07:25 024-08 done: the 327 is the shape of MEM's keys (a key of
  exactly 7 bytes gets a key node of its own, 226 heap bytes), not the
  count; 024-03 and 024-04 corrected; committed 9d134987, pushed.
* 07:26 low disturbed touch's timing run (07:21 to 07:25) and said so;
  touch told to rerun or mark those times.
* 07:27 Frans on the order of work: model first, and the proofs wanted
  (024-04, section 6): "Yes, start it." Started tree (024-12); touch
  told to settle the cut question in Lean first; tie and tree told of
  each other.


## 6. Outcome

Not yet written.
