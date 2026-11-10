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
high, xhigh for hard tasks; W1 at max (Frans, 09:03).


## 3. The work

* **W1. 020-30, the study** (agent d30, effort max): every resource a
  deleted KV holds today, the causes in the code, the design options
  against Frans's rule, failing tests, a prototype on a branch, the cost
  in the stream, the Lean model and the C port, an estimate. Clone
  `/Users/f/fl/bench/2026-11-10/d30/`. Reports to 020-30 and to the
  coordinator.


## 4. Principles

010-principles; for W1 above all: maintenance proportional to the user's
work, a deterministic stream, and Frans's approval of any change of the
stream format (018).


## 5. Timeline

| Time  | What                                  |
|---|---|
| 09:10 | W1 started                            |


## 6. If the session stops

The agent's State note in 020-30 says where it stands; a new coordinator
restarts it from there (013-02, `resume`).


## 7. Progress

* 07:27 coord-1110 started; coord-1109 closed at 07:30 (handover in
  006-17, section 6).
* 07:47 to 09:03 Frans and the coordinator on 021-28: the index keeps
  the nodes of deleted keys (020-30, section 3).
* 09:03 2026.4 paused (Frans). 020-30 created; W1 started.


## 8. Outcome

(at the end of the day)
