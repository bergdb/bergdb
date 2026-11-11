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
| 024-09 | The tie of model and code repaired (024-06, A1 to A4) | tie (xhigh) | on main, 379d8acf |
| 022-07 | The C clone to release 2026.4 as released (CC1) | cc (high) | on main, 51a7224c |
| 024-10 | The builder's rule "the last operation wins" (CA1) | low (high) | on main, a780b957 |
| 024-11 | The underfill fix: a design study, no code | fill (xhigh) | done 08:18 |
| 024-12 | The key tree's model in Lean, run against Java | tree (xhigh) | |
| 024-13 | The integration branch: doubles.py, 024-10, 024-07; gates | int (Opus, high) | landed 10:07 |
| 024-14 | The merge's thresholds measured in Java at 10M keys | thr (Opus, high) | done 13:50 |
| 024-15 | The cost of key shape: documentation, bound, Mem runs | shape (Opus, high) | on main 12:25 |
| 024-16 | One operation a key, strict: a collision fails the commit | strict (Opus, high) | |
| 024-17 | The limits of a transaction, a key, a value, a record | limits (Opus, high) | done 11:59 |
| 020-33 | The known issue of 2026.4 in its notes; next.md | notes (Opus, high) | done 10:28 |
| 024-18 | Dead klongs: what they cost, three options measured | dead (Opus, high) | done 13:49 |
| 024-19 | The node size: which, and one fixed constant or not | nsize (Opus, high) | postponed 11:50 |
| 024-20 | A more compact stored form of an index node | compact (Opus, high) | postponed 11:50 |
| 024-21 | Merges at the delete, in Java on main, format 7 | mgj (Opus, xhigh) | |
| 024-22 | Merges at the delete in the Lean tree model, run first | mgl (Opus, xhigh) | |

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
* 10:25 The usage: 59 % of the week (50 % at 09:25). Frans, 10:28: a
  ceiling of 75 % for today ("Yes."); the Fable agents finish as they
  are, every follow-up on Opus. 10:26 Frans on a value's limit: "I think
  1 MB is too small for the limit. But 10 MB could work. Ordinary photos
  should fit."; the repo's largest file is 15.6 MB; 16 MiB suggested;
  sent to limits. 10:28 020-33 done: the known issue in 2026.4's notes
  (65b8bfdc).
* 10:34 024-09 done: T-SCHEME's argument holds for 2026.4's code; the
  gates now reach the take-back; PhysStep proved; head e6b6bda6, sent
  to int to merge and gate (unlinkfuzz, conformance reclaim and evict,
  level3 not yet run after its merge of main).
* 10:48 Frans: two heavy runs at a time when neither is timing ("Yes.").
  A second slot and a helper (`slot.sh`); the helper's test matched the
  word in "not timing" and held waiting agents back twice (11:05,
  11:20); corrected.
* 10:50 Frans: 024-04 rewritten in place, the aim as it is (16526107).
* 10:53 to 11:10 Frans on 024-09's questions, one at a time: the
  trusted statements name `LiveAppend` in place of `PhysRunOK`, in a
  commit of its own after 024-12 has landed, its diff shown to him
  ("Yes, as recommended."); the gates require A6 everywhere ("Yes.
  Sound very good. Nice to avoid the need to support such a corner
  case."); 015-03 closed when the branch lands ("yes"); the longer gates
  ("Yes, accepted.").
* 11:24 **The second landing: main 379d8acf**, the merge of 024-13-int
  (e74bb8ff), pushed: 024-09. Gated: the Lean build, before-commit,
  level1, level3 full, unlinkfuzz.sh (3,226 rounds), conformance.sh
  reclaim (C-CUT 0 of 326) and evict; level2 full on the branch's head,
  whose java/, lean/ and docs/ the merge equals. 015-03 closed.
* 11:24 Frans on dead klongs in live nodes (024-11, QU3), not decided:
  "This is important. I need to understand this better. We need to.
  Perhaps with measurements. Let's call the options 1, 2, and 3. I like
  the idea of 3, that reclaim will rewrite nodes so the cost goes to
  zero eventually. [...] By the way, the node size of 30 is open for
  discussion. And should it even be a fixed constant? And should an
  index node be stored more compact in the stream? Big questions. But
  these are important now when we want to settle the algos." Started
  dead (024-18). 11:31: "Node size is worth a separate study. Compact
  stored format too.": started nsize (024-19) and compact (024-20).
  The usage: 63 % at 11:27.
* 11:36 Frans: "I fail to see the overall picture. [...] What is the
  most important algos to get in place now, today?" The coordinator:
  one algorithm is left, the delete path's final form (merges at the
  delete), and it waits for three numbers (the node size, the
  thresholds, the dead klongs). 11:44, Frans: "Could we instead make
  reasonable assumptions on 1, 2, 3. Go with this "for now". To get the
  merges at the delete done today. [...] To be able to change one thing
  at a time." The assumptions, as named constants: node size 30, P5's
  thresholds (a quarter, a half), nothing more for dead klongs, P5's
  way of making merged nodes. 11:49: "Yes." Started mgj (024-21, Java)
  and mgl (024-22, the Lean tree, run first); 024-19 and 024-20
  postponed until after the merges.
* 11:49 Frans: "I will be back at 14:30 for 30 minutes. Use up to 85% of
  AI usage limits. You can land the C clone, the key-shape doc, the
  one-operation rule. I would like to approve the new tree model."
  Unattended from 11:56 until 14:30.
* 11:52 024-19 and 024-20 stopped with their interim states (the node
  size: a flat optimum at 1M keys, 30 and 62 within 2 %; the stored
  form: index nodes 57 % of the stream under random overwrites, a
  compact encoding at 41 to 43 % of today's index bytes).
* 11:56 **The third landing: main 51a7224c**, the C clone at release
  2026.4 as released (022-07; `items/022-bergdb-c/c` only): C's gate OK
  on the head, 0 differences with Java's release on every comparison
  set; no fault of Java's product code, three notes on Java.
* 11:59 024-17 done (the limits; a proposed table: 1,000 operations, a
  key of 256 bytes, a value of 16 MiB, 64 MiB a transaction). 024-16
  done on its branch; as it moves the key transformations to before
  the go point and adds a cancel to the clock, it went to a full gate
  by int and an independent review, not to main on its own gates.
* 12:16 The review of 024-16: land with four small fixes; no fault found
  in the commit path, by reading or by a concurrency probe; an old
  fault beside it (a key-replace put over an indexed object leaves a
  stale index entry). The fixes are with the branch's agent.
* 12:25 **The fourth landing**: 024-15, the cost of key shape documented
  and bounded (the merge of 251cd1e0): before-commit and level1 full on
  the merged tree; SEG 226.4 (at most 230), MEM10M 127.0 (at most 131).
  The usage: 67 % at 12:15.
* 12:25 024-12 done on its branch (d90586d0): the tree's model writes
  Java's records on 115 traces; it waits for Frans's approval; int
  prepares it on today's main. 12:23 to 12:33 thr's timing hold
  disturbed by mgl's runs and by dead's scripts, which kept starting
  runs: the coordinator stopped dead's processes.
* 13:06 024-16's four fixes made (3412ee7a); with int for the full
  gates.
* 13:34 The merge is in the Lean model (63e39de6) and Java with merges
  (024-21) agrees with it: 15,084 transactions, 9,243 merges, 0
  differences. 13:37 024-21's head 331dd400 passed before-commit,
  unlinkfuzz, level1, level2 and level3. The two slots starved mgl and
  thr; an order set by message.
* 13:50 024-14 done: no threshold set showed a fault or a thrash; the
  recommendation m8 (8/17/17): at most 1.49 times the twin's key nodes
  (P5 1.90, main 21.5), 1 % more bytes a put, no slower.
* 13:57 024-12 gated on today's main (ca3824aa): lake build, no sorry
  or axiom, test-traces, before-commit, level1, treeconf, level3; waits
  for Frans's approval at 14:30.
* 14:12 024-16 landed: 47c93e34, the merge of 3af7513e, gated with
  before-commit, level1 to level4 full, unlinkfuzz and conformance drain
  (013-integration, section 6). Release notes filled (releases/next.md).
  024-12 lands second, after a re-merge and new gates.


## 6. Outcome

Not yet written.
