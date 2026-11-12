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
| 024-27 | U26-5 B, theta at least 2, 62 the largest size, U26 Javadoc | rules (high) | landed a7dfb6f7 |
| 026 | 2026.6 work moved from 024 to 026, 024-20 first (026-01) | move (high) | done 07:42 |
| 024-27 | QR1 kept as is: RwEnvironment's Javadoc, "Refused calls" | coordinator | landed |
| 026-02 | A public key check: the options, a recommendation; no code | keychk (high) | done 09:39 |
| 010-04 | Rules, beside the principles: R1 to R3 from 024-27 (R4 removed) | coordinator | written |
| 010-01 | P14, the Pub API cannot destroy the database's integrity | coordinator | written |
| 024-28 | The release checklist of 2026.5 | check (high) | done 10:37 |
| 024-29 | Reclaim's fraction: previous work, how to compare, the default | frac (high) | done 11:15 |

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
* 08:13 rules done: branch 024-27-rules, head 40275fd7, gates on it
  before-commit (62 s), lake build (215 jobs), level1, level2 (with the
  Lean conformance) OK; five changed tests, each its own commit; QR1
  (spoil an rw() action that catches a refused put?), QR2 (550 in the
  Eviction test). 08:14 landed as a7dfb6f7, pushed; 024-23's QO2 marked decided.
* 08:51 Frans: QR2 as recommended (keep 550).
* 09:16 Frans on QR1, the line between the user's and the database's
  responsibility: "use of the Pub API must keep the integrity of the
  database. Including features in the pub layer. This includes indexes.
  But only indexed created by the database itself. [...] the user is
  responsible for the code in Action. [...] This is a borderline case."
* 09:34 Frans: QR1 decided, keep as is, in the Javadoc; a place for
  fundamental rules like this one to be proposed and discussed first; a
  todo for a public key check, studied by an agent at high, for the next
  release (026-02). keychk started; the Javadoc by the coordinator in
  /Users/f/fl/bench/2026-11-12/qr1/clone (5a7f644d), before-commit
  OK (64 s), landed 09:36 and pushed.
* 09:39 keychk done (026-02): recommended a class bergdb.pub.Limits
  (the limits as constants, keyBytes, checkKey, levelBytes; one checking
  method shared with put and delete), about a day; QK1 to QK4.
* 09:58 Frans: QK1 to QK4 wait for the work on 2026.6. On 010: separate
  principles (about 10, stable) from rules (up to about 100, from
  decisions, valid for every implementation).
* 10:07 Frans: "Add 010-03 with the four rules. Keep the principles as
  they are. Do not edit principles unless I explicitely tell you to."
  Written as 010-04 (03 was used and removed on 2026-10-27, not reused):
  R1 a refused call changes nothing, R2 a commit holds all of its
  accepted calls or none, R3 the database keeps its own structures
  consistent and the user owns what her keys mean, R4 a safety belt is
  decided case by case. 010's readme (Frans's open edit) not touched.
* 10:15 Frans: "Yes, add this as Principle P14. In the details, note
  that the Core API is different. It can destroy the integrity of the
  upper Pub layer. This is intentional. Needed, since Pub is implemented
  by using Core API." Written into 010-01; R1 to R3 serve it; 010's
  readme: P14, 010-04 and the Log (only these lines committed; Frans's
  own edit of the readme's top left uncommitted).
* 10:19 Frans: "Remove Rule R4." Removed (its number kept, not reused);
  P14's "Where BergDB stands" now names R1 to R3.
* 10:23 Frans, on P2's details: it is for accepted transactions; the
  STM's state is not kept across a restart, so a transaction may be
  accepted or refused depending on a restart between two transactions,
  "This is acceptable."; a refusal under overload too. Written into P2
  (010-01). Committed with Frans's own edit of 010's readme, at his word.
* 10:32 Frans: night.sh needed now? (the change since run 2 is small);
  yes to the checklist agent; walk through QF1 to QF8. check started
  10:33.
* 10:37 check done (024-28): not ready now; the earliest after one
  release night, and after Frans's decisions on aim 4's proofs, QF1,
  QF3, QF6, QF8 and the small cases (OP4, OP8, ST6, ST7, ST8).
* 10:42 Frans on QF1: the reclaim fraction (default 0.25) is one of the
  few settings a user should know; assume a finite retain time; maybe
  change the default (forever) some day. "By fresh, we must mean one
  that keeps the same history, same retain period. Otherwise, we are not
  comparing the same things." The coordinator: 024-03's "fresh" was the
  live state without history (R was 1,000 transactions, so nearly the
  same there); the bound's form: kept = H(R) + k L, k about 1/f to 2/f.
* 10:56 Frans: with retain forever "The storage is proportional. All
  history is kept and available. The stream grows proportional to the
  history kept. Cost follows value." The four aims of 024-04 added near
  the top of 024's readme ("Bugs first" kept as it is).
* 11:04 Frans: investigate 0.25, 0.40 and 0.50 as the default of
  reclaim's fraction; previous work first; how to judge and compare;
  guidance for users; maybe a few distinct settings. frac started
  (11:05), 024-29.
* 11:13 Frans: the Pub API without a setter for the fraction "may not
  be so bad actually. If we can find a internal fraction that always
  works, that is good. Advanced users could still set it using core
  layer if really needed. [...] But for the sake of testing, it still
  seems right to define three recommended values somehow." Sent to frac.
* 11:15 frac done (024-29): 0.25 since the 2013 Git's first commit, no
  reason recorded (Frans's 2012-07 note: fixed, 0.4 to 0.7 of the user's
  writes, "not needed as a setting"); 0.5 measured once (011-04); a step
  cap (16 kB a user transaction) often paces reclaim, not f; a plan of
  4 to 5 h of F53 for 1/4, 3/8, 1/2; QF29-1 to QF29-5. Frans waits for
  it before deciding.


## 6. Outcome

Not yet.
