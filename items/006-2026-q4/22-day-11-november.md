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
| 024-07 | The last touch of a reclaim iteration (CL7): design, fix | touch (xhigh) | on main, 36924319 |
| 024-08 | MEM 327 at 10M keys against 129.6 at 1M: the cause | mem (high) | done 07:25 |
| 024-09 | The tie of model and code repaired (024-06, A1 to A4) | tie (xhigh) | on main, 773c2105 |
| 022-07 | The C clone to release 2026.4 as released (CC1) | cc (high) | on main, 54780032 |
| 024-10 | The builder's rule "the last operation wins" (CA1) | low (high) | on main, 36924319 |
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
  (ab3279ad); 07:02 the old theme marked in 024-02 and 024-03 (1d5b18fa).
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
  count; 024-03 and 024-04 corrected; committed e3ba6295, pushed.
* 07:26 low disturbed touch's timing run (07:21 to 07:25) and said so;
  touch told to rerun or mark those times.
* 07:27 Frans on the order of work: model first, and the proofs wanted
  (024-04, section 6): "Yes, start it." Started tree (024-12); touch
  told to settle the cut question in Lean first; tie and tree told of
  each other.
* 07:30 Frans: the cost of key shape is within aim 3 ("Yes."); logged
  in 024-04. He left until 09:00.
* 07:49 024-10 done on its branch (head 3fc470c6 in
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
  09:31 024-07's branch final at e11c4791; int has merged the
  doubles.py fix (188 s to 2.9 s), 024-10 and 024-07 (head 0a873e46),
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
* 10:07 **The first landing: main 36924319**, the merge of 024-13-int
  (0a873e46), pushed: doubles.py (188 s to 2.9 s; before-commit.sh 80
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
  (8fabbb2e).
* 10:34 024-09 done: T-SCHEME's argument holds for 2026.4's code; the
  gates now reach the take-back; PhysStep proved; head 43cebf22, sent
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
* 11:24 **The second landing: main 773c2105**, the merge of 024-13-int
  (61333dc5), pushed: 024-09. Gated: the Lean build, before-commit,
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
* 11:56 **The third landing: main 54780032**, the C clone at release
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
  and bounded (the merge of c9bc3854): before-commit and level1 full on
  the merged tree; SEG 226.4 (at most 230), MEM10M 127.0 (at most 131).
  The usage: 67 % at 12:15.
* 12:25 024-12 done on its branch (46478dd5): the tree's model writes
  Java's records on 115 traces; it waits for Frans's approval; int
  prepares it on today's main. 12:23 to 12:33 thr's timing hold
  disturbed by mgl's runs and by dead's scripts, which kept starting
  runs: the coordinator stopped dead's processes.
* 13:06 024-16's four fixes made (2f81651e); with int for the full
  gates.
* 13:34 The merge is in the Lean model (10c8de77) and Java with merges
  (024-21) agrees with it: 15,084 transactions, 9,243 merges, 0
  differences. 13:37 024-21's head 30c393df passed before-commit,
  unlinkfuzz, level1, level2 and level3. The two slots starved mgl and
  thr; an order set by message.
* 13:50 024-14 done: no threshold set showed a fault or a thrash; the
  recommendation m8 (8/17/17): at most 1.49 times the twin's key nodes
  (P5 1.90, main 21.5), 1 % more bytes a put, no slower.
* 13:57 024-12 gated on today's main (ca3824aa): lake build, no sorry
  or axiom, test-traces, before-commit, level1, treeconf, level3; waits
  for Frans's approval at 14:30.
* 14:12 024-16 landed: e6e93272, the merge of 51edfdcf, gated with
  before-commit, level1 to level4 full, unlinkfuzz and conformance drain
  (024-13, section 6). Release notes filled (releases/next.md).
  024-12 lands second, after a re-merge and new gates.
* 14:14 Frans back (attended). 14:27 dead klongs decided (024-18,
  QD1): option 2 with theta 7, after the merges, as a change of its own
  through the model; it lands on its gates, without the 10M measurement
  first ("Let's get this in now. We will measure carefully and study
  alternatives later."). 3c shelved.
* 14:28 Frans approved the tree model (024-12) for landing: "Yes, I
  approve." It lands after int's re-merge onto main (with 024-16) and
  its gates; int gets the next free slot.
* 14:34 Frans: the merge's thresholds 8/17/17 (024-14, QT1; QT2 open),
  and 024-22's QM1 to QM5 as their defaults. 024-22's agent finished
  (d39f0e9b; 239 traces against Java equal).
* 14:45 Frans: a key at most 112 bytes (024-17, QL2; 16 segments; the
  user's rule of thumb "about 100 characters"). 024-17 to be reworked
  for it (L3, L6, the bound's arithmetic with merges, the tests).
* 14:47 Frans left; unattended until 2026-11-12 07:00 (the default; he
  gave no time). While he is away: the tree model lands on its gates
  (approved); the merges (024-21 at 8/17/17, 024-22) are gated and run
  against each other, not landed; option 2 with theta 7 is built on top
  of them, model first, not landed; 024-17 reworked for 112-byte keys;
  night.sh on main after the tree model, if the machine is free. Usage
  ceiling 85 %.
* 14:48 Frans, on the three things waiting for him (the four re-found
  CorruptStreamTester copies of 024-21, 5fa27223; the diff of the
  trusted Lean statements, LiveAppend in place of PhysRunOK; the merges
  branch before it lands): "Handle these for me as you see fit." And:
  "I am plan to be back 17:00. If not back by 18:00, keep working
  unattended through the night." So the coordinator lands the merges
  (024-21 with 024-22) once fully gated, Java against the model at
  8/17/17, and after an independent review finds nothing that blocks;
  the LiveAppend change lands on its gates, its trusted diff quoted in
  its item for Frans to read; 5fa27223 goes in with the merges.
* 14:56 The tree model landed: ab1b9e42, the merge of a935b6e0 (024-12
  re-merged onto main with 024-16; gates: lake build, treetest, no
  sorry or axiom, test-traces, before-commit, level1 full, level2 full
  with its new treeconf step, level3 full).
* 14:59 024-17 reworked for 112-byte keys (lim2). Three corrections to
  the coordinator's figures of 14:40 to 14:45: TP26 is stated and
  checked, not proved; 112 bytes are 17 segments (111 are 16); with
  merges TP26's form counts 20 nodes a level, which covers only 452
  operations. A sharper count with q (about 8 a level) covers 1,128
  (QL8). Proposed L3 112 KiB, L6 112 bytes refused; QL1, QL4, QL8,
  QL11 (112 or 111), QL12 (node sizes 8 and 62) for Frans.
* 15:28 The independent review of the merges (024-21, review.md): land
  with fixes; R1 (land with 024-22, the thresholds in the TREE line, the
  combined head gated with level2 to level4), R2 to R6 fixed by mgj
  (54f0a6f5). 15:38 024-21 at 8/17/17 passed before-commit, unlinkfuzz,
  level1 to level4 full; 15:02 to 15:20 Java at 8/17/17 equal to the
  model on 260 traces. 15:45 int combined main + 024-22 + 024-21
  (0520b8c5); its gates running.
* 16:00 The 024-09 follow-up landed: the merge of 74cb07b5 (LiveAppend
  in place of PhysRunOK in the trusted statements, its diff quoted in
  024-09, section 9.2 for Frans; A6 required by the gates). The merges'
  combined head takes main in and reruns its Lean and level2 to level4
  and conformance gates with it.
* 16:03 024-23 (option 2, theta 7) started, model first, on the merges'
  combined head. 16:03 to 16:06 mgj and mgl finished (items final).
* 16:54 The merges at the delete landed: 67925924, the merge of
  f3f2ac05 (main + 024-22 + 024-21 + the 024-09 follow-up; gates: lake
  build, treetest, no sorry or axiom, test-traces, before-commit, level1
  full, unlinkfuzz, level2 full with A6 and treeconf with merges, level3
  full, level4 full, conformance small, medium, reclaim, evict, drain).
  Record format 7; 2026.4's databases are refused. Landing delegated by
  Frans at 14:48; the six changed tests (024-21, QJ1) accepted under it.
* 17:20 Frans back. 17:33 the review of option 2 (024-23): land with
  fixes (R1, a changed test made vacuous; docs).
* 17:41 Frans decided the limits (024-17, section 8): L1 = 500
  operations, L2 = 111 bytes (16 segments), L4 = 8 MiB, L5 = 32 MiB,
  the rest as recommended ("a bit more conservative, possibly
  increasing in a future version").
* 17:43 Frans left ("You can plan the unattended work"). Unattended
  until 2026-11-12 07:00 (the default; no time given). The plan, in
  order, each step by its own rule:
  1. Option 2 (024-23) lands when its gates pass with the review's R1
     fixed (Frans 14:27: "Let's get this in now"); the landing says
     that format 7's meaning changes without a new format number (R2).
  2. 024-17 restated for the decided limits (lim2, by 19:30).
  3. The limits implemented, a new item (024-24), on main after option
     2: the constants and the count with q in the Lean model (QL8 (a)),
     Java's checks with refusals (L1 to L6), the reader reading a
     record's header first (QL7), the tests and benchmarks that use
     longer keys; full gates and an independent review, then it lands
     (Frans decided the values; the coordinator lands as for 024-21).
  4. CRC32C (QL9) as its own item after 024-24, only if the week's
     usage is under 82 % when 024-24 lands.
  5. night.sh on main when no agent needs a slot (both slots), its
     report in news.md.
  No new agent at or above 83 % of the week (ceiling 85 %). The Lean
  proofs (TP30 to TP33) wait for a day with more usage. The morning: a
  summary in news.md and this plan's Outcome.
* 17:48 Frans: "Fine to use up to 90%. Use Opus 5.5 High for coding
  agents to save usage. Use xhigh for planning. This session is Opus 5.5
  xhigh. [...] Keep on working until 07:00 or you get to 90% usage." So
  the ceiling is 90 % (no new agent at or above 88 %); 024-24 (the
  limits) started at 17:49 on Opus high; CRC32C (QL9) as 024-25 after
  option 2 lands, on Opus high, when usage is under 85 %; with usage
  left after night.sh, the proofs of the count with q (TP23, TP26 for
  format 7) on Opus high.
* 18:01 Frans: offload the proofs to his Codex (GPT Plus, gpt-6.1-sol at
  max; "Sol Max does not use too much"), to save the Claude week (80 %
  spent in two days). 18:10 the first Codex run started: TP32
  (`MergeOpBound`, 024-22) in a clone of main
  (/Users/f/fl/bench/2026-11-11/cx/clone, branch 024-22-tp32), brief
  /Users/f/fl/bench/2026-11-11/cx/brief-tp32.md: no changed statement,
  no sorry or axiom, Lean only, commits in Frans's name without AI
  attribution, stop at 06:00. The coordinator checks it mechanically
  (lake build, the statements' diff empty, print axioms) and lands it.
  Next for Codex, one at a time: TP23 and TP26 with the count with q
  (after 024-24), TP39 and TP40 (024-23), TP31, TP7 and TP30.
* 18:05 Frans reset the Claude usage (the 5 hours and the week 100 %
  left) and confirmed Codex on TP30 to TP33 ("Yes, start it."); Codex
  takes them one at a time after TP32. 18:06 CRC32C (QL9) started as
  024-25 on Opus high, now that usage allows. 18:06 Frans left: "Work
  unattended."
* 18:16 Option 2 for dead klongs landed: 08659847, the merge of
  335a3c40 (gates: lake build, no sorry or axiom, test-traces,
  before-commit, level1 to level4 full, unlinkfuzz, conformance small,
  medium, reclaim, evict, drain; the review's R1 fixed). At 1M keys
  0.29 to 0.31 dead klongs a live one (0.48 to 0.85 with the merges
  alone), stream bytes -3 % to +8.5 %, 13 to 16 % fewer key nodes. The
  landing says that format 7's meaning changes without a new number.
* 18:45 to 19:04 The reviews of CRC32C (land with fixes: level1's
  stream-size limits, a node size under 12 untested, 024-02's text) and
  of the limits (land with fixes: R1, a value over L4 through the public
  Trans.kvs failed the database when reclaim rewrote it; docs). Both
  fixed by their agents.
* 19:24 CRC32C landed: 3dd38b23, the merge of 8c7fbff1 (gates:
  before-commit, level1 full, unlinkfuzz, level2 to level4 full,
  conformance small, medium, reclaim, evict, drain, CorruptStreamTester's
  full set; 48 of 48 StreamDigest digests change). Checksum 5.6 to 0.12
  ms a MB; an 8 MiB commit 49-57 to 2-11 ms (rough). Its changed tests
  and level1's raised stream-size limits (QC2) accepted for Frans to see.
* 20:19 The limits landed: 87afef86, the merge of b0d41461 (main with
  CRC32C merged in; gates: lake build, no sorry or axiom, test-traces,
  before-commit, level1 full, unlinkfuzz, level2 to level4 full,
  conformance small, medium, reclaim, evict, drain). About 30 changed
  tests and programs, each its own commit (024-24, section 3), accepted
  for Frans to see (Q2); the index build over values longer than L6
  gives no entry (Q1, as recommended).
* 20:19 night.sh started on main (8664db0e), holding both slots.
  20:21 024-26 started (Opus high, to 02:00): a round of "AI as the user"
  (006-20) against the new algorithms (merges, option 2, CRC32C, the
  limits): bugs first (024-04, aim 1).
* 21:15 Codex's first run ended at its usage limit (it could not commit:
  its sandbox makes .git read-only; the coordinator checks and commits).
  22:13 to 23:07 night.sh's four failures, all from the limits, fixed:
  one product bug (L6 refused puts that get no entry), two test
  generators; landed 9dd763df. 00:39 024-26's user apps: seven apps,
  about 900,000 transactions, 3,000 restarts, 1,070 kills, no bug;
  Javadoc findings U26-1 to U26-8. 01:33 024-19 (node size) done on
  format 7: keep B = 30; Q1 to Q6. 01:35 024-20 (compact stored form)
  resumed.
* 02:30 Codex's second run (23:07 to 02:26, usage limit again) landed
  after the coordinator's checks (29a03f04, Lean only): the writer's
  frame ported to option 2, merges at most the deletes times the
  greatest height seen, TP32's bound when no node is made above H + 1,
  and two proved counterexamples: MergeOpBound as stated is false for
  transactions that repeat or misorder keys, so it needs the premise
  that Java's transactions meet (one operation a key, sorted; 024-16).
  TP32 for sorted transactions is the third run's goal (04:12).
* 02:30 024-20 (compact stored form) done on format 7: for 2026.6.
  03:05 a stale constant after CRC32C fixed (reclaim's value-node bytes,
  cbe11242). 03:05 to 05:39 night.sh run 2 on main: all OK but one night
  test: CorruptStreamTester reached 024's open item (a time klong's
  unused bits not checked); 06:01 fixed and landed (90184540; gates
  before-commit, CorruptStreamTester's night set, level1, level2).
  04:12 Codex's third run (TP32 for sorted transactions), to 06:40.


## 6. Outcome

Written 2026-11-12, 06:35, by coord-1111 (unattended since 2026-11-11,
17:43).

**Landed on main (all pushed, each on its gates):** 36924319 (024-07
the last touch, 024-10, doubles.py), 773c2105 (024-09 the tie), 54780032
(022-07 the C clone at 2026.4), 6b6f04de (024-15 key shape), e6e93272
(024-16 one operation a key), ab1b9e42 (024-12 the tree model in Lean,
approved by Frans 14:28), 01b14c68 (024-09's follow-up: LiveAppend in
the trusted statements, A6 in the gates), 67925924 (024-21 and 024-22
merges at the delete, record format 7, 8/17/17), 08659847 (024-23
option 2, theta 7), 3dd38b23 (024-25 CRC32C), 87afef86 (024-24 the
limits), 9dd763df (the night run's fix: L6, one product bug), 29a03f04
(TP32's proof work in Lean and two counterexamples), cbe11242 (a stale
constant after CRC32C), 90184540 (a time klong's unused bits checked),
and a9c72fb2 (06:41, TP32's groundwork for sorted transactions: 180
theorems). 16 in all.

**Studies done:** 024-14 (thresholds), 024-17 (limits), 024-18 (dead
klongs), 024-19 (node size: keep 30), 024-20 (compact stored form: for
2026.6), 024-26 (user apps: no bug in about 900,000 transactions, 3,000
restarts, 1,070 kills).

**night.sh:** run 1 (20:18) found four failures, all from the limits,
fixed by 23:07; run 2 (03:05 to 05:39) all OK but one night test, a
known open item, fixed by 06:01. Not rerun since.

**Proofs (by the second prover, checked and committed by the
coordinator):** the writer's frame, merges bounded by the height seen,
TP32 under a height premise, and MergeOpBound shown false without the
premise Java guarantees (sorted, one operation a key). The third run
(04:12 to 06:37, stopped by its usage limit, which resets at 09:12)
added the groundwork for sorted transactions (a9c72fb2); TP32 for sorted
transactions is neither proved nor refuted. Its reports:
/Users/f/fl/bench/2026-11-11/cx/REPORT-tp32*.md.

**For Frans to decide** (each with the coordinator's recommendation):

1. 024-19, Q1 to Q6 (node size): keep B = 30, B a property of the
   database, thresholds and theta as v*B/30, theta at least 2 (changes
   one test value and Lean's Params.theta), 62 the hard maximum.
   Recommended: yes to all.
2. TP32's statement (024-22): MergeOpBound as written is false; restate
   it with the premises tx.sorted, tx.wf and a fresh base. Recommended:
   yes (a change of a statement, so his).
3. The key klong's unused bits checked like the time klong's: a patch
   (/Users/f/fl/bench/2026-11-11/tkb/key-klong-bits.patch) that changes
   one expected refusal text (CorruptStreamTester.testFound021_12).
   Recommended: yes.
4. 024-26, U26-5: a WBuilder stays usable after a refused put(), and
   execute() then commits the rest. Recommended: a refused put makes the
   builder refuse execute() (all or none). U26-1 to U26-8 otherwise
   Javadoc fixes, one small agent.
5. 024-20, QC1 to QC5 (compact stored form): 2026.6, accounting nominal.
   Recommended as the item says.
6. To see, accepted under his delegation of 14:48 and 17:43: the changed
   tests of 024-21 (QJ1), 024-23 (section 4.1), 024-24 (section 3, Q2)
   and 024-25 (QC2, with level1's raised stream-size limits); 024-23's
   QO1 to QO3 as their defaults; the trusted Lean diff in 024-09,
   section 9.2; the commit message of 29a03f04 says "written by a second
   prover" (no AI named).

**Corrections by the coordinator:** the key limit's figures given to
Frans at 14:40 to 14:45 were wrong (TP26 is not proved; 112 bytes are
17 segments); corrected in 024-17 before he decided 111.

**Frans's answers, 2026-11-12, 07:26:** 1. "OK, good. Let's keep 30.
Document this." (024-19, Q1, recorded). 2. TP32 restated with the
premise, "in a separate agent. Opus at xhigh" (started 07:28). 3. The
key klong patch: "In general, we are focusing too much on a corrupted
stream. Sure, we want a corrupted stream (not an unwritten tail) to
produce an error message when we open the database. But this is best
effort, we do assume correct bytes from storage [...] The assumption
made is that the storage layer (filesystem or whatever) will handle
integrity (checksums etc) for us." So the patch is not applied, and
work on catching damaged bytes is low priority. 4. U26-5: "Tell me
more", pros and cons given. 5. "QC1. For 2026.6 as recommended.
QC2,3,4,5 should wait" (024-20, 026, recorded).

**Usage:** the week at 83 % by usage.sh at 06:30 (Frans reset it at
18:05; the script did not show the reset). The second prover's runs
were stopped twice by its own limit.

