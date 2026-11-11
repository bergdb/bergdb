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
| 024-07 | The last touch of a reclaim iteration (CL7): design, fix | touch (xhigh) | on main, a780b957 |
| 024-08 | MEM 327 at 10M keys against 129.6 at 1M: the cause | mem (high) | done 07:25 |
| 024-09 | The tie of model and code repaired (024-06, A1 to A4) | tie (xhigh) | |
| 022-07 | The C clone to release 2026.4 as released (CC1) | cc (high) | |
| 024-10 | The builder's rule "the last operation wins" (CA1) | low (high) | on main, a780b957 |
| 024-11 | The underfill fix: a design study, no code | fill (xhigh) | done 08:18 |
| 024-12 | The key tree's model in Lean, run against Java | tree (xhigh) | |
| 024-13 | The integration branch: doubles.py, 024-10, 024-07; gates | int (Opus, high) | landed 10:07 |
| 024-14 | The merge's thresholds measured in Java at 10M keys | thr (Opus, high) | |
| 024-15 | The cost of key shape: documentation, bound, Mem runs | shape (Opus, high) | |
| 024-16 | One operation a key, strict: a collision fails the commit | strict (Opus, high) | |
| 024-17 | The limits of a transaction, a key, a value, a record | limits (Opus, high) | |

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
* 07:30 Frans: the cost of key shape is within aim 3 ("Yes."); logged
  in 024-04. He left until 09:00.
* 07:49 024-10 done on its branch (head 3ad9fa1e in
  /Users/f/fl/bench/2026-11-11/low/clone): before-commit, level1 and
  level2 OK; the stream's bytes the same without repeated keys; two
  expected values changed, for Frans to approve; not landed. Its
  finding F2: `java/doubles.py` takes 181 s on main, so
  before-commit.sh is about 4.5 minutes.
* 07:50 The usage: 38 % of the week, about 12 points an hour with six
  agents; nothing new started. tie silent since 07:18: resume message
  sent.
* 07:56 tree disturbed touch's timing for 45 s (07:53:40) and said so;
  touch told. tree's first result: the Lean tree gives Java's change
  and klongs on 76 traces (9,080 transactions), 0 differences.
* 08:18 024-11 done: merges at the delete alone (P5's), with the bound
  BU1; with merges the index is 1.12 to 1.90 times the twin's key nodes
  (35 runs on P5's build), without 2.0 to 20.2; a plan of about two
  weeks; QU1 to QU8 for Frans.
* 08:49 The usage level turned tight (48 %): tree told to gate and stop
  before the proofs, cc to stop after its next gate run. 09:02 024-07's
  gates all pass on its branch (level3, level1, before-commit; two Lean
  theorems, T-COVER and T-LATEST).
* 09:17 Frans back; attended. The usage: 27 % at 06:39, 50 % at 09:17.
* 09:25 Frans: "1. Use Opus 5.5 for subagents by default. At effort High
  or XHigh depending on how hard the task it. Only this coordinator
  session continues with Fable 5.2. Continue with several agents in
  parallell. 2. Yes. 3. Yes. 4. Yes. 5. Yes. 6. Yes, as recommended."
  That is: land 024-07 with its two changed tests when its last runs
  have reported; land 024-10 with its two changed expected values; the
  underfill by merges alone with the bound BU1, the denser thresholds
  measured in Java at 10M keys before the model is written; fix
  `doubles.py` (09:26: "Yes do it."); land the C clone and the tree
  model when their gates report, the tree model merged with the tie's
  branch. The rule on Opus written into the coordinator's skill
  (013-02). Started int (024-13) and thr (024-14), both on Opus.
* 09:29 Frans: "Feel free to push." (code on main after a landing).
  09:31 024-07's branch final at 5bbdbf6e; int has merged the
  doubles.py fix (188 s to 2.9 s), 024-10 and 024-07 (head 524732d8),
  its gates wait for the lock. 09:34 Frans: "Sure, do it.": started
  shape (024-15).
* 09:43 to 09:47 Frans on 024-10's finding F1 and the rule: "One
  transaction must not set (put or delete) a value more than once! This
  is a strict rule. [...] So, yes, 3, refuse it if it happens." Of the
  coordinator's three scopes he chose B ("Yes!"): in the builder the
  last call on a key as written wins, silently (024-10's R1 stays); at
  the commit a transaction fails when key transformations make two of
  its keys one key, in the Core and the Pub layer alike (this replaces
  024-10's R2 and his word of 2026-11-10, 17:46). 024-10 lands as
  built; the change is 024-16 on top. Started strict (024-16).
* 09:54 to 10:06 Frans on limits: "It is reasonable to limit
  transactions. Actually, I see no reason for a transaction with
  250,000 operations." 10:03: "This is important. Setting limits. I
  suggest creating a subitem of 024 to document this." Started limits
  (024-17): the discussion, today's limits, the cost against the batch
  size, a proposal (user limits checked, internal bounds proved).
* 10:07 **The first landing: main a780b957**, the merge of 024-13-int
  (524732d8), pushed: doubles.py (188 s to 2.9 s; before-commit.sh 80
  s), 024-10, 024-07. Gated as one tree: the Lean build, before-commit,
  level1, level2 and level3 full (C-CUT 0 of 310 cuts). main's java/,
  lean/ and docs/ equal the gated head's.
* 10:16 024-07's final report: the old touch was also two faults of
  2026.4 as shipped: near 104M keys in time order the step passes the
  record limit and the startup position stops for good; with a small
  heap a user's commit ends in OutOfMemoryError. Fixed on main.
* 10:18 Frans on the key's size: "256 is a reasonable limit to key size.
  I think this is the one limit that need to go into the db user's mind.
  [...] The other limits are typically large enough for nearly all use
  cases." And on "user limits checked, internal bounds proved": "Yes,
  sure. Good." Sent to limits (024-17).
* 10:21 Frans on 024-07's three decisions: "1, 2, 3 decisions; all as
  recommended.": a known issue in 2026.4's notes
  (020-33, started); the cut's safety rests on the delete's upward
  unlink, stated in the tree model, with 024-09's gates landed; the
  touch removed altogether later, with the tree model.


## 6. Outcome

Not yet written.
