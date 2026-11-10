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


## 8. Outcome

(at the end of the day)
