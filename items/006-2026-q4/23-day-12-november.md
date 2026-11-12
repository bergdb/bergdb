# 006-23 Day work, 12 November 2026

Created 2026-11-12 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-12 (coord-1112), a Thursday, the progress
and the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1111's handover (006-22, section 6, and its message of 07:29):
its finished work on main and pushed (699a98b4); its agent tp32s (TP32
restated, 024-22) to land; U26-5 (024-26) and 024-19's Q4 and Q6 for
Frans.

Frans's answers, 07:36: the week's usage "use up to 95%"; U26-5: "B.
Ensure the behaviour is clear in the Javadoc." (a refused call spoils the
builder); 024-19, Q4 (theta at least 2) and Q6 (62 the largest node
size): "Yes I confirm."


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents that
change code work in clones under `/Users/f/fl/bench/2026-11-12/` and do
not commit to `main`; item-only agents write their own file in the main
tree. Heavy runs by the two slots of coord-1111's
`/Users/f/fl/bench/2026-11-11/slot.sh`, kept for today. The common brief:
`/Users/f/fl/bench/2026-11-12/common-brief.md`.

Usage: the week at 83 % at 07:29, "tight" by usage.sh; Frans's ceiling
95 % of the week (07:36), until the reset on Monday 16 November, 22:00.
So at most two agents at a time, all on Opus 5.5 at high; the session at
high.


## 3. The work

| ID | Task | Agent | Result |
|---|---|---|---|
| 024-22 | TP32 restated with the premises Java meets (coord-1111's tp32s) | tp32s (xhigh) | landed c0a8cadf |
| 024-27 | U26-5 B, theta at least 2, 62 the largest size, U26 Javadoc | rules (high) | |
| 026 | 2026.6 work moved from 024 to 026, 024-20 first (026-01) | move (high) | done 07:42 |

024-27 lands on its gates, by Frans's decisions of 07:36: its changed
expected values follow from them.


## 4. If the session stops

The state is in `/Users/f/fl/bench/coord/2026-11-12/state.md`; each
agent's file ends with a State note. `/coordinator resume` restarts
from them.


## 5. Progress

* 07:28 coord-1112 started; coord-1111 closing (07:29), closed at 07:37.
* 07:37 tp32s done (head cb57e5c8); landed as c0a8cadf after the
  coordinator's check (the logs of its lake build, 215 jobs; no sorry or
  axiom in the diff; `#print axioms` standard; the statement diff as
  briefed). Left open by tp32s: MergeParamsOK (TP28) is not a premise of
  TP32; Java meets it; to add only if a proof needs it.
* 07:39 rules started (024-27).
* 07:40 Frans, 07:39: "Start a new agent at high to go through the
  current work and move things for 2026.6 to 026. In particular this
  024-20 should move there." move started.
* 07:42 move done: 024-20 is now 026-01 (a stub left at 024-20); nothing
  else of 2026.5 was decided for 2026.6; what is only proposed for it
  (024-19 Q5, 024-22 QM1, 024-02 section 21, 024-01 OT4, PA5, PA9) is
  listed in 026's readme for Frans.


## 6. Outcome

Not yet.
