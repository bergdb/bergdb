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
| 024-22 | The open proofs TP32, TP33, TP7, TP30, TP10, TP11, TP31 | second prover | checkpoint landed 2a7bdc52 |
| 024-30 | Count gates G1 (BD1), G2 (BD13), G3 (BD10) at 1M keys, a night step | gates (high) | landed |
| 024-31 | OP4: a cap on the take's pace after a decrease (015-84) | pace (high) | landed c1137b69 |
| 024-32 | maintain(), in Core and Pub, with G5 (back to empty by maintain()) | maint (high) | landed 94edfe6b |
| 024-33 | ST6: the cache's tables shrink | tidy (high) | landed a156fd51 |
| 024-34 | OP8: reclaim reads only what it rewrites | tidy (high) | landed a156fd51 |
| 017-11 | A startup distance that follows the database's size: known, plan | sdk (xhigh) | done 13:03 |
| 021-27 | Db.getTrans inside a record fails the database: refused instead | gtr (high) | landed 3ffe0b51 |
| 024-35 | A double-check for open work forgotten for 2026.5 | sweep (high) | |

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
* 11:16 Frans: "Next thing! Let's work towards 2026.5. Quickly." The
  coordinator's fast path (aim 4 by conformance and the proofs that
  hold, count gates BD1, BD13, BD10, OP4's cap, the small cases to 026,
  the QF defaults, releases/next.md, the release recipe tonight).
* 11:21 Frans: "Step 1. Could you run these with Codex now? GPT-6.1 Sol
  at Max, to prove these." The second prover started 11:22 on the open
  proofs in order TP32, TP33, TP7, TP30, TP10 and TP11, TP31 (clone
  /Users/f/fl/bench/2026-11-12/cx/clone, branch 024-22-proofs; stop
  2026-11-13, 06:30; the coordinator checks and lands).
* 11:35 Frans: step 2, "Yes, start it. Use an Opus agent at high."
  (gates started 11:36, 024-30, at 1M keys only); step 3, a plan first.
* 11:38 Frans: step 3, "Yes, start it." (pace started 11:39, 024-31).
* 11:47 Frans on ST6: "will they never be released? It is ugly. If we
  would go from 10M keys to zero, the cost is unproportional high [...]
  I think a general test is the back-to-empty test. Big database, then
  all kvs removed, check eventual resource consumption. Does it go
  towards something similar to a fresh empty database?" The coordinator:
  that is 023-03's T1; proposed G4 (back-to-empty at 1M, with the cache's
  tables, the path arrays and the heap added).
* 11:53 gates done (024-30): G1 108,912 B of 1 MB, G2 1.296 of 2, G3
  4.41 of 6, all PASS on main; G1 and G2 FAIL on release 2026.4; before-
  commit OK, count-gates.sh OK (125 s). Landed and pushed.
* 11:52 Frans: G4 yes, "but with a comment for ST7. There may be a
  performance reason for KeyAccessPath.clear() to work as it does. It is
  better to close ST7 as neglectable than to degrade performance." gates
  resumed for G4 (11:52): ST7 measured, not gated, not changed.
* 12:01 gates done with G4 (back to empty at 1M keys): all within 2
  times the twin after 40 R (stream 1.07, key nodes 1.00, dead klongs
  1.33, resident 1.08, heap 1.46) but the cache's table slots (ST6,
  3.76, printed as known); the first cut after the deletes at drive
  transaction 4,117 (the twin's 1,214), within 2 times the twin's stream
  after 4,395 (4.4 R). Landed and pushed. Q30-3 (gate the lag), Q30-4
  (ST6: fix or close).
* 12:10 Frans on step 4: ST8 to 026 ("As recommended"); OP8 "Do for
  this release. This changes the reclaim algorithm, or its
  implementation at least. Want this in place for solid internal
  algos."; P8 to 026; maintain() "No, I want this now. In this
  release."; ST6 fixed in 2026.5. Started maint (024-32) and tidy (024-33
  then 024-34) at 12:11, three Claude agents with pace (over the tight
  level's two: pace mostly waits on its runs). ST12 (G4's finding)
  registered in 024-05, not decided.
* 12:12 Frans: "Eviction off is a test mode not use in production at
  all! Only for testing." ST12 closed as not a case.
* 12:22 Frans: aim 4, "Yes, good plan": 2026.5 ships with conformance
  and the proofs that hold, the open ones named in the notes; what the
  second prover proves in time lands. The release night: "Sounds good,
  but I will be back after coffee, no need to plan the unattended night
  yet." Step 5: asked which QF questions need his input.
* 12:33 Frans: QF3 and QF1 are his to look into; "Handle the other ones
  for me." The coordinator settled QF2, QF4 to QF8 as recommended in
  024-05, section 7; Q30-1 and Q30-2 as applied in 024-30.
* 12:46 Frans on QF3: for 2026.5 as recommended; a startup distance
  that follows the number of KVs as a default "users won't need to think
  about" is "a big step and not for now"; a new 017 topic, written by an
  agent at xhigh: sdk started 12:47 (017-11).
* 12:53 Frans: the disk 98 % full (22 GB free; /Users/f/fl/bench 582
  GB): "Start removing files. You created bench/, so please handle
  this." Cleanup from 12:54 (log /Users/f/fl/bench/cleanup-2026-11-12.log;
  unlanded branches bundled to /Users/f/fl/bench/archive-branches/).
* 12:59 Frans on QF1: "Do the measurement now. It is ok to limit
  database size so it takes less than 60 minutes [...] Let's see if we
  can sort this out before the release." fracm started 12:59 (024-29).
* 13:02 The cleanup done: 22 GB free to 410 GB (55 % used); 516 clones
  removed, their 368 branches not on main saved as bundles (80 MB) in
  /Users/f/fl/bench/archive-branches/; 62 of the clones had uncommitted
  edits of tracked files (probes and scratch), removed without a copy.
  Kept: 022, 015-02, the Android SDK, today's directories.
* 13:03 sdk done (017-11): candidate rules R0 to R6; a put's bytes
  constant only if sd grows with K, which costs about 0.2 to 0.5 s of
  warm start and 10 to 15 MB of pinned heap a million keys, against P5
  as written; Frans asked the same question on 2013-04-08; the first
  steps: his D1 from the tables, GM4 (45 minutes, bytes only).
* 13:05 pace done (024-31): the rule changed from the brief's (min(S, c
  sd) changed the stream with a constant setting at the tests' small sd:
  32 of 48 digests) to a cap of the section's span at 2 sd in the share
  (c = 2; StreamDigest identical, 48 of 48); at 10M keys the largest
  record halved, the catch-up 4.5 times longer (1000 to 100 MB); gates
  OK. Waits for Frans: the rule, and commit B's changed expected values.
* 13:09 Frans approved 024-31 (the span rule, c = 2, and its changed
  expected values); merged in /Users/f/fl/bench/2026-11-12/land/clone,
  gated there before main moves.
* 13:21 Frans on 021-27: "Yes, fix this in a agent at high. This is
  important. I consider it a bug. It does destroy the Core database, the
  KV store. The Core API may damage the integrity of the functionality
  built on top of it such as Pub layer's secondary indexes, but it
  should not destroy the integrity of the KV store itself." gtr started
  13:22 (option A).
* 13:24 Frans: his rule of 13:21 "as a new rule": 010-04, R5, the Core
  API never destroys the KV store.
* 13:26 Frans on 021-27: "Why is this tricky. It is a read-only
  operation. It should fail or succeed, but never block the database.
  This position comes from the user and cannot be fully trusted. It is
  not from the internal database." gtr told: no walk; the public
  getTrans refuses what does not parse, an I/O error still fails the
  database (P7), internal callers keep failing on damage.
* 13:27 tidy done: 024-33 (ST6 1.06 times the twin's slots after back
  to empty, was 3.76) and 024-34 (a step's second reads halved, loads 3.6
  % fewer with a 20 MB cache, stream bytes identical), all gates OK, no
  changed tests; Q34-1 (a keys-only scan, which changes bytes).
* 13:35 fracm done (024-29, section 9; 9 minutes of machine time, 1M
  keys): against 1/4, 3/8 keeps 8 to 29 % less stream beyond the history
  and cuts the lag after a mass delete by 58 %, for 15 to 27 % more bytes
  written, 1.3 to 1.7 times the loads a put and 23 % fewer puts a second
  (one pass); 1/2 more so (38 % fewer puts a second). A changed default
  changes seven tests and the l3 digests. For Frans: QF1.
* 13:36 maint done (024-32): maintain() in Core and Pub (begin, step,
  take, filler, cut, dead hand; returns whether more is due now); G5: an
  emptied idle database from 254 MB to 83 kB of stream by maintain()
  alone; no change of the Lean model or the trace format (two new
  conformance configurations pass); before-commit, level1, level3,
  count-gates OK; no changed expected values. Q32-1 to Q32-5.
* 13:38 Frans: TP11, option (a): keyWf to say what Keys.toSegments
  makes (each segment below 2^62, its lowest three bits zero), after the
  prover's run; recorded in 024-12.
* 13:46 The second prover stopped at its own usage limit (resets
  16:17). Its first checkpoint landed 13:50 (2a7bdc52; lake build 248
  jobs, 275 theorems, axioms at most propext, Classical.choice,
  Quot.sound; only imports added to an existing file): TP1 and TP9
  proved, TP30 reduced to TP7, TP31 and TP33 to stated premises, TP11
  refuted as stated.
* 13:50 gtr done (021-27, no walk, by R5): the public Db.getTrans
  refuses what it cannot read as a committed record with
  IllegalArgumentException; Db.Internal.getTrans for the database's own
  positions; the record header's last byte checked before its array;
  before-commit, level1, level3 OK. Q27-1: a garbage size that passes
  the header check (about 1 in 65,000) still asks for an array up to 2
  GB.
* 13:44 Frans on maintain(): the sync, ordinary transactions only, one
  single way to do a maintain step.
* 13:52 Frans: "For 2026.5, land maintain() as built." The single step
  and the simple form registered as 026-03.
* 14:01 maint: main merged into 024-32 (head 5edb773a); before-commit,
  level1, level3, level4 quick, count-gates, e-r-maint OK. G5 found a
  floor of ST6 since 024-33: a used map keeps at least 16 slots, so an
  emptied database keeps up to 4,096 x 16 slots (about 256 kB) whatever
  its size; G5 allows that floor.
* 14:07 Frans on QF1: 1/4 kept for 2026.5; larger databases, three
  recommended fractions and one default for 2026.6 (026-04); the
  measurements tonight if the machine has time.
* 14:09 Frans on Q27-1: "fix it." gtr resumed 14:09 (021-27, the size
  bound for a caller's position).
* 14:12 Frans: "Start a new agent to search for other open things we
  have forgotten that should be included in the release. Just a
  double-check." sweep started 14:12 (024-35).
* 14:16 gtr done with Q27-1: above 1 MiB the public getTrans confirms a
  record's start by walking the record headers before making its array;
  before-commit and level1 OK; landed 4dadb80c.


## 6. Outcome

Not yet.
