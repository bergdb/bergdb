# 006-21 Day work, 10 November 2026

Created 2026-11-10 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-10 (coord-1110), a Tuesday, the progress and
the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1109's handover (006-17, section 6): the night on 2026.4's
candidate `03ce6ec` was clean but for a JDK 17 test race; ten decisions
for Frans in 006-17, section 6.3, the first whether to tag 2026.4.

Frans, 08:29, on the slow scans of 021-28: "The theme of 2026.4 is a
bug-free database. I consider this a bug. The bounds are not ok. Scans
are supposed to be O(n) amortized for scanning n items." 08:50, his rule:
a deleted KV must consume zero resources eventually after the retain
period has passed (quoted in full in 020-30, section 1).

09:03: "This is major. I don't want to file it as a todo item, that
should be smaller things fixed by AI. Put it in a new 020 subitem for
now. My decision is to pause 2026.4 until this has been sorted out. [...]
Create the item now. Include my rule that a deleted KV should eventually
cost nothing. Start a new subagent at Max effort to study this carefully
and thoroughly. Report to the new subitem. And here."


## 2. Ground rules

013-02's: the coordinator commits to `main` in Frans's name; agents work
in clones under `/Users/f/fl/bench/2026-11-10/` and do not commit to
`main`; heavy runs one at a time. Effort: the session xhigh; subagents
high, xhigh for hard tasks; W1 at max (Frans, 09:03). From 09:59,
subagents xhigh by default (Frans: "We have plenty of Claude usage left;
ensure subagents start with effort xhigh by default."), max where Frans
asks for it.


## 3. The work

* **W1. 020-30, the study** (agent d30, effort max): every resource a
  deleted KV holds today, the causes in the code, the design options
  against Frans's rule, failing tests, a prototype on a branch, the cost
  in the stream, the Lean model and the C port, an estimate. Clone
  `/Users/f/fl/bench/2026-11-10/d30/`. Reports to 020-30 and to the
  coordinator.
* **W2. 020-30, the same study by Codex** (Frans, 09:07: "How about doing
  this study in Codex too. Codex Sol 6.1 Max. Independent work to start
  with. Then a possible 'merge' of ideas."): `codex exec`, gpt-6.1-sol at
  effort max, workspace-write in its own clone at `0b93d273`, in
  `/Users/f/fl/bench/2026-11-10/codex30/`; it does not read d30's work nor
  d30 its. Its study goes to `codex-study.md` on its branch `020-30-codex`.
  The two are compared after both are finished.


## 4. Principles

010-principles; for W1 above all: maintenance proportional to the user's
work, a deterministic stream, and Frans's approval of any change of the
stream format (018).


## 5. Timeline

| Time  | What                                  |
|---|---|
| 09:06 | W1 started                            |
| 09:08 | W2 started                            |
| 17:00 | W2 done at the latest                 |
| 18:00 | W1 done at the latest; then the comparison |


## 6. If the session stops

The agent's State note in 020-30 says where it stands; a new coordinator
restarts it from there (013-02, `resume`).


## 7. Progress

* 07:27 coord-1110 started; coord-1109 closed at 07:30 (handover in
  006-17, section 6).
* 07:47 to 09:03 Frans and the coordinator on 021-28: the index keeps
  the nodes of deleted keys (020-30, section 3).
* 09:03 2026.4 paused (Frans). 020-30 created; W1 started 09:06.
* 09:08 W2 started (Codex), at Frans's idea (09:07).
* 09:21 Frans: the first study by 10:00, an overview of the alternatives;
  several subagents allowed; full proposals in a phase 2. W1 rescoped to
  the overview; four helpers at high (r30 reclaim, p30 Frans's notes and
  prior art, a30 the upward delete in the Dag, f30 format, Lean and C),
  09:23 to 09:30.
* 09:33 Phase 1 done: 020-30 section 4 and files 020-30-01 to 04
  (90f8d315). Codex (W2) still runs its full study.
* 09:37 Frans: a wider framing, resource cleanup in general; a new item,
  023-cleanup (09:45).
* 09:47 023-01 (introduction) and 023-02 (the problem) started, xhigh.
* 09:59 023-03 (the test specification) started, max, after Frans's
  practical test of the rule (09:55).
* 10:02 to 10:30 023-01, 023-02 and 023-03 done. 10:13 023-04 (the
  options, max) started. 10:22 Codex stopped and resumed with a phase 1
  options brief (by 11:45). 10:30 to 10:49 Frans answered 023-02's F2,
  F3, F5, F7, F9 and F10.
* 10:53 023-05: three prototypes started, xhigh (Frans, 10:51): P1
  relabel, P2 relaxed invariant, P3 reclaim compaction and `maintain()`;
  each in its own clone, by 14:30 at the latest.
* 11:53 P4 (LE-b, Frans 11:52). 12:00 023-06, the architecture review on a
  stronger model at max (Frans 11:59); first pass 12:12, second 13:30.
  12:23 P5 (merges at the delete), 12:37 P6 (memory, Frans's Y6 (b)),
  13:43 P7 (the dirty top-node window, Z13) and P8 (reclaim's scan at the
  step's time, Z14). 14:00 023-06 section 18 recommended fix (b); 14:06 P7
  showed it unsound (a counterexample, a failing unit test); 14:12 the
  review agreed (18.7): (a) plus (b'). 14:29 the long-run answer: (b') an
  efficiency only. P1 to P6 and P8 done, reports committed.
* 14:26 to 14:36 Frans: KISS; pause and review. 14:37 023-07, the
  proposal for 2026.4 (a KISS core against the full set), by 15:25; then
  three independent reviews (Codex, and fresh agents on two other models).
* 14:43 Frans away (a walk): unattended until about 17:30. While away:
  023-07 committed when written, then the three reviews, then a merged
  verdict for Frans; P7's report committed when done (by 16:30).
* 14:48 023-07 written (e45fd4c1). 14:49 P7 done: fix (a) closes the
  window; report 0a0f0016. 14:49 the three reviews of 023-07 started
  (023-08), each in its own clone, by 16:45.
* 15:36 to 16:06 the reviews in (B, C, A). All three: P8 can stop the
  cuts; C: fault 12 in the take-back. 15:38 and 15:50 two checks: both
  confirmed, each with a fix (fault 12 also with sorted keys). 16:23
  023-08, the merged verdict: the delete design stands, P8 out, a smaller
  core frozen, a stop rule (Frans, 16:14: "I smell expanding complexity").
* 16:34 Frans answered 023-08: Q1 to Q8 as recommended, except Q4: sort
  a transaction's keys after their transformation. 16:36 the integration
  branch (023-09) started, by 20:30; then level2 to level4 full and a night
  of fuzzing.
* 17:18 023-09 done (023-core, 2c67f887): before-commit, level1, fuzz OK.
  17:19 level2 to level4 full started on it.


## 8. Outcome

(at the end of the day)
