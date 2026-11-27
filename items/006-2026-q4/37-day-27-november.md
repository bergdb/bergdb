# 006-37 Day work, 27 November 2026

Created 2026-11-27 by Frans Lundberg. Status: open. The plan for the
lead's day of 2026-11-27 (lead-1127), a Friday, and the weekend to
Monday 07:00: the decisions, the progress and the outcome. The way of
working is 013-04's (the lead).


## 1. The request

* lead-1127 took over from lead-1126 at 07:49 (006-36 closed,
  `ce458202`). Nothing ran. The week's usage: 25 %, the limit 70 %.
* Open from 006-36, all for Frans: 028-60's part 2 (the branch
  `028-60b`), 028-66, 031-05 with its review, 031-04, 028-67, 028-54.
* An overview of the week for Frans (08:27): where the code's stability
  stands, why the core is not done, and what is left that is hard.
* The open questions on one page, each with a default (section 4).


## 2. Decisions

Frans, 2026-11-27:

* The redesign of `maintain()` (031-04, 031-05) is worth its cost: it
  is simpler than `main`'s, and the design to build on (08:36).
* The principle of a deterministic stream extended to every write
  (031-05) is wanted (08:36).
* The order: first 031-04 with 031-05 is made to work, so that it is
  known to be possible; the principles (010) and the documents are
  updated after that (08:41).
* Frans's design notes of 2012 on the deterministic stream are not
  sensitive and may be quoted in the repository (08:41): the note of
  May 2012 (the stream's contents deterministic given the SET
  operations; for testing, and for a secure hash of a sequence of
  operations) and the note of July 2012 (reclaim piggyback on the
  transactions, which allows a deterministic stream and no load when
  the database is not used; no background threads). Where they go:
  below.
* A1, when and how a commit's maintenance is written, is the day's
  focus: the centre of the work left before 2026.7. It is to be solved
  today, with a clean solution. Backwards compatibility of the stream
  does not count against a design; stability going forward does
  (09:38). This bears on A3, whose rule is still Frans's to state.
* Two more options for A1, their feasibility studied today (section
  4.1):
  * (e), raised 09:15: the maintenance inside the user's record
    itself.
  * (d), 09:28: the user's record and its maintenance records as one
    compound unit, marked in the user's record; a start treats an
    incomplete unit as a torn record, so both are kept or both are
    void.
* A `maintain()` part takes its own time from the clock, as a
  transaction does (`DbClock.transactionBegin`), and the part is the
  unit (11:16): an action is a transaction, a setter or a `maintain()`
  part, each with its time, and a call of `maintain(budget)` does the
  parts that fit its budget. The clock is not held, and there is no
  maintenance time.
  * The reasons: one rule of the clock for every record;
    `currentTime()` moves during a call; a crash, a stop or a commit
    between two parts needs no rule of its own.
  * What it gives up: a call of `maintain(budget)` as one action with
    one time. What is due in a call can depend on the clock during the
    call, as it does between two commits.
  * It holds whichever of A1's options is taken, where the option
    allows it. It is the option (a) of the question on a part's time in
    the study of (e), and the review's F4 (031-05, section 12) with the
    part's own time in place of its call's.
  * It answers B5, and A4 and B4 in part (section 4).
* Frans, 11:18: a prototype of (e), one record an action, is built
  today. It is item 031-06 (the lead's number); its files come with the
  prototype's landing. A1 itself stays open until the prototype's
  evidence, and (c) is the fallback. The rules fixed in its brief:
  * `Reclaim`'s plan and apply behind an interface, with an empty
    second implementation;
  * the part as `maintain()`'s unit, with its own time (11:16);
  * the setters carry no maintenance;
  * the step has an allowance of its own in the record, so that large
    transactions cannot starve reclaim (Codex's finding on progress,
    section 3, 10:55);
  * a key of reclaim's is the witness of reclaim's own record (Codex's
    finding on the empty user commit);
  * the copy mark on a value node;
  * the after-row charge of 028-26 is left dropped, and measured;
  * Lean, the trace format and the contract checkers are out of scope,
    so the conformance levels are not expected to pass on it.
  * Its gate: `before-commit.sh`; a crash and a stop at every record
    boundary; as many records as accepted actions; Codex's three tests
    (section 3, 10:55: its report names them); a figure of the time of
    a commit that carries a step.
* The finished prototype gets two independent reviews in parallel, by
  an agent on Fable, high, and by Codex (11:22). Each gets the code, the
  probes and the item, and neither the other's report nor the lead's
  recommendation; each tries to break it, and says whether (e) as built
  is simpler and safer than (c).
* The next release's focus, 2026.7 (11:37): the algorithms in place,
  `maintain()` and reclaim included; a bug hunt; clean-up; quality; the
  documentation's update. The theme's wording is Frans's. 2026.8's
  theme is left undecided (11:50).
* For P2's wording (11:50):
  * the unit is an action, a user action where precision is needed;
  * the Pub layer's index jobs are user actions: the user starts them,
    and to the Core their commits are transactions like any other;
  * the storage's one expected fault is called a partial append: an
    append written in part, which leaves part of a record or zeros at
    the tail. After it, the stream as the start leaves it is what the
    actions continue from: accepted;
  * what is appended is a function of the stream as it is and of the
    user actions that follow.
* The stream is the bytes from reclaim's cut to the end. Bytes before
  the cut that the storage still holds belong to the storage's
  implementation of the stream, not to the stream (12:05).
* No setting outside the stream is to affect the stream's bytes
  (12:05). Two do in the code of today:
  * the internal crypto key: the crypto code is removed (12:11;
    028-69), and the removal is recorded in 017-10's log for the later
    design. When encryption comes back, the key is the one exception:
    the stored bytes depend on it, and it cannot be in the stream;
  * the reclaim step reserve, a setting for tests: 028-68, decided
    with 031-06's landing.
* These answer C1 and B2, and A4 and B3 in part (section 4).
* Frans, 13:53: Codex's review of the prototype is not needed to go on:
  the review by the agent on Fable is enough, if it is ok.
* Frans, 14:00 to 14:09, on the prototype's three problems (031-06,
  section 8): none is a blocker. That readers see a commit after its
  scan is not a problem. The record's size needs no formal bound: that
  it works in practice, with enough testing, is enough, and a guarantee
  that is cheap is welcome. The after-row charge (B1): the fixed-width
  patch of the row is tried first, later; the fallback is the charge
  one record later.
* **A1 is (e), one record an action** (14:32): by Frans's condition of
  13:53 and the review's verdict of 14:30 (section 3): no probe broke
  the prototype, and (e) is the one for `main` after three fixes. The
  landing is 031-06's section 9. Section 4.0 says what this answers.
* **A2 and A3** (14:36): `maintain(int budget)` replaces `maintain()` in
  the Core and the Pub API in 2026.7. 2026.7 does not open a database of
  2026.6: a new format version, refused with a clear message, with no
  upgrade path (031-06, section 8).
* **028-67: C1 and C3, in 2026.7** (15:50 to 16:02), built in 031-06's
  landing: a meta block holds its own position and is valid only with
  this database's ID; a record header holds, in its three unused bytes,
  a CRC-32C of the ID, its position and its fields, truncated to 24
  bits; a tail that fails is refused with the cause and the way out,
  before anything is written. C2 after C3 is in and tested; C4 not
  taken. The stream's checksums are reviewed for 2026.7, the new check
  with them: 031-07.

Gone ahead by default:

* 09:15, where the notes of 2012 go (class 2; proposed by the lead at
  08:41, section 4.4's D1 until then): a section "The origin" in
  031-05 (its section 13) with the two notes quoted and dated, and one
  sentence in `AGENTS.md`'s rule on Frans's notes: a passage may be
  quoted, with its date, when Frans approves it. P2's text in 010 is
  not touched: it waits for Frans (A4).

The history of reclaim's records (an agent, 09:19 to 09:30, reading
Frans's notes, the Git history of 2013 to 2017 and this repository):

* No reason was ever recorded for reclaim's records of their own. They
  follow from the design of July 2012: reclaim as a thread or piggyback
  on the transactions, with transactions of its own either way.
* The alternative, one record, was not weighed for reclaim before
  2026-11-25.
* On 2014-11-01 Frans merged the index writes, which had a record of
  their own since September 2014, into the user's record, to reduce
  variability and to ease the startup's reruns of the transactions.

The lead's reading of the proofs for A1's options (09:40; reasoning
from 031-05, section 9 and section 12, nothing built):

* (e), one record, and (d), the compound unit, map an action to one
  record of the model, so `T1_crash` and `T2_restart` apply as they
  are. For (d), recovery of the bytes, a prefix of whole units, is an
  assumption to test, as a torn record is today.
* (a), (b) and (c) need the new theorem of 031-05's sketch, a crash
  inside a call continued by a later writer (800 to 1,600 lines by the
  sketch); in (a) and (b) it holds only as a prefix that a later call
  completes (F3).
* In all five, `maintain()`'s parts are records of their own, and that
  Java's maintenance is a function of the stream alone stays tested.

The lead's overview (08:30), its conclusions:

* **The released bugs of the week**, RB-004 to RB-012 (033), nine:
  * six in code new in 2026.5: `maintain()` (RB-006, RB-007, RB-010,
    RB-011, all S4) and `Db.getTrans` (RB-008 and RB-009, S3, fixed);
  * one at the boundary to the operating system: RB-012, S2, zeros
    after a kill on APFS (part 1 fixed; part 2 on a branch);
  * two possible in theory only: RB-004 and RB-005, S4.
* None is S1: no value lost or wrong. None is in the proved part, the
  writer and reclaim's cuts, under 031-02's about 9,500 kills, its 11
  apps, `week.sh` and Codex's review of the Java changed since 2026.6.
* **Why the core is not done:** the register (2026-11-20), its rule
  that faults possible in theory count (2026-11-24), the app hunt and
  `week.sh`'s soak found what the earlier tests did not; and RB-007's
  fix became a redesign of maintenance (031-03, then 031-04 and
  031-05), a choice of scope, not a need of the bugs.
* **What is left that is large:** one task, landing 031-04 with 031-05
  as one design. The others are small: 028-60's part 2, 028-66, 028-67.
* **The lead's proposal, not decided by Frans:** D2 with Q2 (c)
  (031-05); landed in Java with its tests in 2026.7; the Lean statement
  of the extended P2 after the release; no new study until it is in.
  The lead's estimate: about a week with the reviews and the runs, and
  an app hunt on it, as it is new code.


## 3. Progress

* 07:49 lead-1127 started; lead-1126 closed (006-36, `ce458202`).
  Nothing ran; `main` clean. The run data that lead-1126 listed as
  landed was not deleted (the session's permission mode refused it;
  407 GB free).
* 08:30 The overview for Frans (section 2).
* 08:36 Frans: the redesign and the principle (section 2). This plan
  made, with the page of section 4.
* 08:41 Frans: the order (the design made to work first, 010 and the
  documents after), and the notes of 2012 may be quoted (section 2).
  The lead's proposal for where they go: section 4.4, by default at
  09:15.
* 09:15 By default: D1 carried out (section 2): 031-05's section 13
  and the sentence in `AGENTS.md`.
* 09:19 Frans asked why reclaim's writes are records of their own and
  not part of the user's record. An agent (Opus, xhigh, reading only)
  searches the history for the reason.
* 09:21 031-05's section 13 landed (`ee8bbc42`).
* 09:30 The history agent's result (section 2): no recorded reason.
* 09:38 Frans: A1 is the day's focus (section 2).
* 09:44 Two agents (Opus, xhigh, to stop at 11:15) study the
  feasibility of (d) and of (e), each in a clone of 031-05's
  prototype. Their reports become a subitem of 031 if Frans takes one
  of the two.
* 09:53 to 10:40 Frans's questions on the code, answered in the
  session. `Db.execute()` and `Db.maintain()` meet in `Reclaim`, whose
  writes are internal transactions through `Db.execute()`. The Pub layer
  adds a transaction's index entries before the Core's `execute()`, with
  the Core API only (`RwEnvironmentImp.indexEntries`). By the code, (e)
  holds the write lock no longer than `main`; a commit that carries a
  step becomes readable later, by the time that the step's planning
  takes. To be measured in a prototype.
* 10:05 The study of (e), one record, done: feasible, with three warts.
  * A copy flag in the value-node header.
  * 028-26's after-row charge stays dropped.
  * A larger rework than (c): reclaim plans KVs for the commit's
    record; the trace format, C-STEP and the contract's `StepTx`
    change.
  * A lag of one record for the decisions that need a record's own
    length.
  * `T1_crash`, `T2_restart` and `T12_restartCut` apply as they are.
* 10:17 The study of (d), the compound unit, done: it works, with three
  warts.
  * It needs the mark as the record's last byte, appended last, and a
    cut of the void tail (the start decides it, the first append cuts):
    new code in the storage.
  * On the prototype a stop right after a user record returned from
    `execute()` in 30 of 30 runs with no maintenance written; under (d)
    that would be an acknowledged commit dropped at the next start.
  * No change in Lean is required.
* 10:20 Neither (d) nor (e) is built or gated. The lead recommends (e)
  to Frans: it leaves the storage and the recovery as they are, has one
  rule (an accepted action appends one record) and the smallest proof
  work; (d) is the second choice. The two reports are outside the
  repository until Frans chooses; they become subitems of 031 with his
  choice.
* 10:45 Codex reviews the two studies against the code, for a second
  opinion on (c), (d) and (e).
* 10:55 Codex's second opinion, done (its report is outside the
  repository; it ran every probe of both studies again, with the same
  results): it would build (c); (e) is a credible later simplification;
  (d) is its last choice.
  * Against (e): a step that is skipped when it does not fit has no
    guarantee of progress (inferred): it needs a reserved share of the
    record, or another rule.
  * Against (e): the study's test of reclaim's own record is passed by
    an empty user commit, which holds no KV (ran): it needs a key of
    reclaim's as a witness.
  * Against (e): the claim about P1 is not measured, and the contract's
    `StepTx` must be generalized to records that mix the user's writes
    and reclaim's copies.
  * Against (d): a listener that syncs from the writer's thread inside
    a unit waits for a close that the same thread has yet to write
    (inferred); the encryption's cursor is wrong after a cut of the
    tail (ran).
  * For all three: (c) and (e) keep today's aborted torn record, so the
    goal holds at record boundaries; only (d)'s cut of the tail gives
    more.
* 11:00 The lead's recommendation after it: a prototype of (e) with the
  two holes closed by a rule each and Codex's three tests, and (c) the
  fallback: about 4 lines on the prototype, checked by Codex in a
  throwaway variant at 384 of 384 crash points and 384 of 384 stop
  points. Frans has not chosen.
* 11:03 to 11:16 Frans's questions on `maintain()` under (e), answered
  in the session, and his decision on a part's time (section 2).
* 11:19 The prototype of (e), 031-06, started (section 2, 11:18): an
  agent (Opus, xhigh) in a clone of 031-05's prototype, on a branch
  `031-06`, to stop at 17:00. Codex reviews the result before Frans
  decides A1.
* 11:26 The usage is logged at each check-in, with each of its rows.
  With the lead on Fable since 08:27: the week from 25 to 28 %, the
  row of the Fable models at 14 %.
* 11:35 A draft of P2's extended wording by the lead, for Frans,
  written for (e); revised at 11:50 and 12:08 on his answers (section
  2). It is outside the repository until 031-06 lands.
* 12:13 028-68 and 028-69 registered. An agent (Opus, high) removes the
  crypto code in a clone (028-69); the lead gates and lands it, then
  028-60's part 2 on it.

* 12:40 028-69 landed: the internal crypto code removed (`1809e04c`),
  `BEFORE COMMIT OK` in the agent's clone, recorded in 017-10's log. A
  database that an earlier release encrypted is still refused, by its
  `created.txt`; a new database's `created.txt` has no line "crypto
  key:" any more.
* 12:58 028-60's part 2 landed (`ac33aa93`), rebased on 028-69 without
  its opt-out, after a third review by Codex: RB-012 is fixed on `main`
  for 2026.7. `BEFORE COMMIT OK`; `KILL RESTART OK`, 200 kills;
  KillWriter's seeds 63 and 91 OK. 028-69 done; 028-70 registered from
  the review (a start refused after its recovery has written).
* 13:09 The prototype of (e) done, on the branch `031-06` (`fa11d15f`)
  in the agent's clone: `BEFORE COMMIT OK`; 27,720 crashes, failures and
  stops at record boundaries, and 49,029 more with the variants of
  031-05's review, all continued to the uninterrupted stream, with a
  start's memory the running database's; as many records as accepted
  actions in 59 runs; Codex's three tests; the count gates,
  `level4.sh quick` and `apps.sh quick` OK. `level2.sh` and `level3.sh`
  stop at their trace steps, as expected. Its own three problems: the
  mixed record's bound is assumed in part; the after-row charge not
  made is 25 % of the charge at node size 30 and 39 % at node size 8;
  readers see a commit after its scan.
* 13:12 The two reviews of the prototype started, each in a clone of
  its own, neither with the other's report nor the lead's
  recommendation: an agent on Fable, high, and Codex, run by an agent.
  Codex met its usage limit at 13:12 and went on at 14:22.
* 14:24 Codex's review was stopped by OpenAI's content filter ("flagged
  for possible cybersecurity risk"), after about three minutes of work,
  with no report. Not reworded or tried again (013-04, section 9); for
  Frans.
* 14:30 The review by the agent on Fable (031-06, `review-fable.md`):
  no probe broke the prototype: no live value lost, no acknowledged
  commit missing, no refused commit in the stream, no reader with a
  wrong state, no start that differs from the running database. F1 to
  F9 are of cost, margin and scope. (e) is the one for `main`, simpler
  and safer at crashes and starts than (c), after three fixes: the
  conformance (the trace format, the checkers, `StepTx`); the record's
  room by a check; the pace.
* 14:32 A1 = (e) (section 2). The landing started: an agent (Opus,
  xhigh) on its steps 0 and 1 in a clone (031-06, section 9). 031-06's
  files landed on `main` from the clones: the item, the study, the
  prototype's diff, the probes and runs, the review and its probes, the
  study of (d), Codex's opinion on the studies, and the draft of P2's
  wording. 028-71 registered from the review's F3 (large commits keep
  36 times the live data), and 028-68 updated from F7.
* 14:35 The lead asked Frans for A2 and A3 (section 4.0), needed before
  the branch is merged.
* 14:36 Frans: A2 and A3 (section 2).
* 14:42 to 15:26 A timing check of the prototype (`fa11d15f`) against
  2026.6, `timing.sh core pauses` at MINIDLE=80 (031-06, section 4.10):
  TIMING OK; CORE's median 0.255 against 0.260; the pause probe's
  longest 16.1 and 18.8 ms against 12.2 and 15.8 ms, two runs each, not
  established. A sanity check, not release figures.
* 15:36 The history of reclaim's own records published as 031-06's
  `history.md` (`a6a7d7a9`), with the passages of Frans's notes and logs
  that he approved.
* 15:50 to 16:02 Frans: 028-67 decided, C1 and C3 (section 2); 031-07
  registered.
* Tonight: the full `timing.sh` on the ported branch against 2026.6 when
  the landing's agent has stopped; then `night.sh` on `main`, whose Java
  changed today (028-69, 028-60's part 2).

## 4. Waiting for Frans

Every open question, each with a default: whose it is, and why. The
defaults of sections 4.1 to 4.3 have no time: nothing of them goes
ahead before Frans has read the page. Section 4.4 has the defaults
with a time: none is open.
"Class 3" marks what only Frans decides (013-04: the stream format, the
public API, a release's scope, the principles, an item closed). The
details are in the items, cited by ID and section.

### 4.0. After A1 = (e) (14:32)

A1 is decided (section 2). What that does to the questions below; the
text of sections 4.1 to 4.3 is left as it was written during the day.

* **Asked at 14:35, needed before the landing's branch is merged**
  (class 3); **both decided at 14:36** (section 2):
  * **A2:** `maintain(int budget)` replaces `maintain()` in the Core
    and the Pub API in 2026.7.
  * **A3:** 2026.7 does not open a database of 2026.6: a new format
    version, refused with a clear message. Under (e) the copy mark and
    one record an action change the format beyond what A3 lists
    (031-06, Q5).
* **Answered by (e) or by Frans today:** A1; B1 (the fixed-width patch
  first, later); B2 (the index jobs are user actions); B5 (the part is
  the unit); B7 (under (e) the setters carry no maintenance, as on
  `main`: what a setting makes due is decided by the next record that
  carries maintenance; 031-06, rule 9); C1 (028-69; part 2 landed,
  `ac33aa93`); 031-06's Q1 and Q2.
* **Moot under (e):** B4 (no maintenance record has a time of its own,
  and nothing is held); B6 (nothing is due, so a refused call writes
  nothing); A6 (the day's studies of (d) and (e) were Frans's focus;
  from here a finding is a 028 entry: 028-70, 028-71).
* **Still open, P2's wording** (A4, B3; the draft is 031-06's
  `p2-draft.md`): the text itself, which is Frans's; whether the
  setters stay actions of their own or become `execute()` calls (W2);
  the creation as part of the stream as it is, or as action 0 (W4);
  the README's sentence (W5).
* **Still open, the proof** (A5): when the Lean statement of the
  principle is made. The landing's step 1 restates the contract's
  `StepTx`, so that what 2026.6 proved stays proved; the new theorem
  is after it. 2026.8's theme is undecided (Frans, 11:50).
* **Still open, of 031-04's design, decided as the landing reaches
  them:** B8 (the getter's name, class 3), B9, B10, B11, B12 (the
  budget's range, class 3, with A2), B13 (the take before a pass, with
  A3), B14.
* **Still open, of the landing** (031-06, section 9): Q3, the step's
  room (step 2; no formal bound is required, Frans, 14:09); 028-68, the
  step reserve (step 2; Frans's decision between A, B and C); Q4 and Q5
  (step 4); Q6 (a timing run).
* **Still open, small and independent:** C2 (028-66), C3 (028-67;
  decided at 16:02, section 2), C4
  (028-54's question for 033), C5 (028-34), C6 (026-04), C7 (026-14).
* **For Frans, new:** whether the history of reclaim's records (an
  agent's file of 09:30, outside the repository) is published: it
  quotes passages of his notes of 2012 to 2014 that he has not approved
  for it; Codex's stop by the content filter (section 3, 14:24).
  The history was published at 15:36, with the passages Frans approved
  (section 3).

### 4.1. The direction, first

* **A1. When maintenance is written** (031-05, Q2 and section 12, F5
  and F6).
  * (a) D1: by the next call.
  * (b) D2: in the call that made it due, and by the next call after a
    crash or a stop.
  * (c) D2, and a start writes what a crash or a stop left due.
  * (d) The user's record and its maintenance records as one compound
    unit, marked in the user's record; a start drops an incomplete
    unit as it drops a torn record (Frans, 09:28). No call and no
    start writes for another; the format changes. Studied today
    (10:17): it works, with three warts. It needs the mark as the
    record's last byte, appended last, and a cut of the void tail (the
    start decides it, the first append cuts): new code in the storage.
    No change in Lean is required.
  * (e) The maintenance inside the user's record: one record a commit
    (Frans, 09:15). Studied today (10:05): feasible, with three warts
    (a copy flag in the value-node header; 028-26's after-row charge
    stays dropped; a larger rework than (c)). The step is sized to the
    room that the transaction leaves, a copy of a key that the
    transaction writes is dropped, and a decision that needs a record's
    own length is made in the next record. The storage and the recovery
    stay as they are.
  * The day's focus (Frans, 09:38; section 2). Neither (d) nor (e) is
    built or gated (section 3, 10:05 and 10:17).
  * Default: **(e)**, the lead's recommendation; Frans decides (the
    stream format changes: class 3). (d) is the second choice. (c), the
    default until the studies (the reviewer on Fable; 031-05's study
    recommends (b)), stays the fallback: every call and every start
    then leaves nothing due, and a start after a crash appends up to
    one commit's maintenance.
  * Codex (10:55; section 3): build **(c)**, with (e) a credible later
    simplification and (d) last. The lead after it (11:00): a prototype
    of (e) with its two holes closed, (c) the fallback. The two differ.
  * Frans, 11:18: the prototype of (e) is built today (031-06; section
    2). A1 is chosen on its evidence and Codex's review of it; no
    default goes ahead.
  * **Decided, 14:32: (e)** (section 2; section 4.0).
* **A2. In 2026.7** (class 3: the scope and the Pub API). The design
  lands in Java with its tests in 2026.7: `maintain(int budget)`
  replaces `maintain()` in `Db` and `Database` (031-04, C1), and it
  fixes RB-007, RB-010 and the rest of RB-006. Default: **yes** (the
  lead; Codex and the reviewer on Fable both say take the direction).
  * **Decided, 14:36: yes** (section 2).
* **A3. The streams of 2026.6** (class 3: the format; 031-04, Q8 and
  section 11; 031-05, F10). The internal format changes: `a` in the
  rows, a table without rows, the take's and the filler's records,
  pCut = pStart, a done row first in the current row.
  * (a) a one-way upgrade: 2026.7 reads and continues a stream of
    2026.6; 2026.6 is refused on a stream that 2026.7 wrote.
  * (b) (a) with a rule that reads mixed rows, as the prototype does.
  * (c) an old filler deleted once at the upgrade.
  * Default: **(a) with an explicit refusal of old writers, and (c)**
    (Codex). The sources differ: the study recommends (b) and (c);
    Codex found (b) unsafe for a writable downgrade (finding 2).
  * Frans, 09:38 (section 2): backwards compatibility of the stream
    does not count against a design. Whether 2026.7 opens a database
    of 2026.6 at all is still his to state.
  * **Decided, 14:36:** 2026.7 does not open a database of 2026.6: a
    new format version, refused with a clear message; no upgrade path
    (section 2).
* **A4. P2's wording** (class 3: 010 is Frans's; 031-05, Q1).
  * (a) the draft of 031-05, section 4.3, which names the setters.
  * (b) without the setters, which become `execute()` calls.
  * (c) commits only, `maintain()` as today.
  * Default: **(a), corrected as the review says** (section 12, F2 to
    F4 and F11): it holds at record boundaries; a torn record is an
    input; the unit of `maintain()` is a part; the settings are inputs.
    The text goes into 010 after the design is made to work (Frans,
    08:41), by Frans.
  * Answered by Frans's decision of 11:16 (section 2), as far as the
    part goes: the unit of `maintain()` in the wording is the part, an
    action with its own time. It replaces the draft's call that counts
    with the work it wrote and takes one time (031-05, sections 4.1 and
    4.3); (c) is out. Still open: the text itself; whether the setters
    stay calls of their own, (a), or become `execute()` calls, (b) (the
    decision names a setter as an action either way); the review's F2,
    F3 and F11 (record boundaries and the torn record; what a call
    leaves, which is A1's; the settings as inputs); and what stays
    outside (B2, B3).
  * Answered further by Frans's decisions of 11:50 and 12:05 (section
    2): the word for the unit; the stream as it is, first in the
    sentence; the partial append, accepted (F2); the stream from the
    cut; no setting outside the stream (F11; 028-68, 028-69). The lead
    drafted the wording for (e) on these (section 3, 11:35). Still
    open: the text itself, which is Frans's; the setters as (a) or (b);
    what a call leaves, with A1.
* **A5. The Lean statement** (031-05, Q9): with the landing, or after.
  Default: **after, and not a condition of 2026.7** (the study, the
  reviewer, the lead): P2 with crashes is tested in 2026.7, as five of
  030-38's guarantees are; the reviewer puts the proof at 600 to 1,100
  lines, most of it from `T2_restart` and T12.
* **A6. No new study until the design is on `main`.** Default: **yes**
  (the lead): a finding becomes a 028 entry, not a new direction.

### 4.2. What follows; the defaults settle these

Of 031-05 (section 10; the review, section 12):

* **B1. The after-row charge** (Q3, F8): (a) not charged, (b) an
  estimate stored in the step's row, (c) charge the records' bytes,
  (d) keep 028-26's second record, or F8's row patched at a fixed
  width. Default: **(b) or F8's, measured with G1 to G4, before the
  landing** (the reviewer). The sources differ: the study takes (a) for
  2026.7, which re-opens 028-26 (26 % less charged at node size 8).
* **B2. The Pub's index jobs** (Q4): (a) outside the goal, named in the
  wording; (b) their steps inside actions. Default: **(a) now, (b) as
  an item later** (the study, the reviewer). Answered by Frans, 11:50
  (section 2), with neither: the jobs' commits are user actions, and
  when each comes among the others is part of the order, which is
  given. Nothing of them is outside the goal at the Core.
* **B3. The creating start** (Q5): (a) the creation is action 0, its id
  and time inputs; (b) no random id. Default: **(a)** (both). In the
  lead's draft of the wording (section 3, 11:35) the creation is part
  of the stream as it is, which the principle starts from (Frans,
  11:50): no action 0 is needed. Open until Frans has the text.
* **B4. The clock held while maintenance is due** (Q6): (a) held, (b)
  not. Default: **(a)** (both); with A1 (c) only inside calls.
  * Answered by Frans's decision of 11:16 (section 2) for `maintain()`:
    a part takes its own time from the clock, so nothing is held for a
    call. Still open under A1 (c) and (d): the records that a commit's
    maintenance writes after the user's record take their times from
    the stream in the prototype, so that a later writer gives them the
    same bytes, and the clock is held while they are written (031-05,
    section 6.3). Under (e) nothing is left of Q6: a commit's
    maintenance has no record of its own.
* **B5. One record a part in `maintain()`** (Q7). Default: **yes**
  (both), and the part as the unit of the wording (F4).
  * Answered by Frans's decision of 11:16 (section 2): the part is the
    unit, an action with one time, so a part writes one record. Still
    open: nothing of Q7; which of M1 to M6 a part's record holds is the
    landing's design (031-05, section 6.4).
* **B6. A refused call that writes the maintenance due** (Q8). With A1
  (c) the case is gone: a refused call writes nothing. Under (b):
  accept (the study).
* **B7. A setter that makes a cut due** (F1): the setter cuts in its
  own call, and `testRestartWithOtherRetention` changes; or nothing is
  due after a settings record. Default: **it cuts in its own call**
  (the lead; A1 (c)'s rule, every call leaves nothing due).

Of 031-04 (section 9; Codex, section 11); Q9 is decided (the handoff,
2026-11-26):

* **B8. The getter of the stream kept** (class 3: the Pub API; Q1):
  `getStreamSize()`, `getStreamKept()`, `getStreamBytes()`,
  `getStorageSize()`. Default: **`getStreamSize()`** (the study,
  Codex), its Javadoc with the files' slack.
* **B9. The live bytes as a figure** (Q2): (a) none, (b) summed by a
  pass into its row, (c) from the last pass's `rewritten`. Default:
  **(a)** (both).
* **B10. The cache's part in a call** (Q3): (a) a batch of the dead
  hand a part, (b) one a call, (c) eviction too, later. Default:
  **(a)**, (c) as its own design (both).
* **B11. A commit's iteration after a pass** (Q4): (a) as `main`; (b)
  an iteration whose pCut is at or before the first position ends at
  its begin, with no scan; (c) commits cut at their own start. Default:
  **(b), as its own 028 entry**, gated by StreamDigest and G1 to G4
  (both); it changes the bytes of commit-only streams.
* **B12. The budget** (class 3: the Pub API; Q5): the range 100 to
  100,000 units of 1 kB; an overload `maintain()` or none. Default:
  **the range, no overload** (both); the Javadoc suggests 1,000 for an
  idle loop and says that a budget is not a limit of time.
* **B13. The take before a pass** (the format, with A3; Q6): (a) kept,
  (b) dropped, and RB-007's case keeps 873 kB of index nodes, (c) kept
  but not before the first pass. Default: **(a)** (both).
* **B14. The read charge** (Q7): (a) reads at a quarter, (b) lighter,
  (c) none. Default: **(a)** (both), and the Javadoc gives a measured
  range of calls for a pass, not a factor (Codex, finding 3: 2.8 to 31
  times kept / budget in its small case).

Of 031-03 (section 10.2), answered by the direction: F1 (031-04 with
031-05 in place of O-1), F2 (A3), F4 (no drain and no MIN_RELEASE), F5
(the Javadoc is 031-04's, B12 and B14), F6 (decided 2026-11-26). F3
stands as recommended there and by Codex: every record that is not
reclaim's own is the application's writing, an empty transaction and a
setter's record too. 028-53's options A and B are replaced by A2.

### 4.3. Small and independent

* **C1. 028-60, part 2: encrypted streams** (028-60, section 10 on the
  branch `028-60b`, `043bf11c`; gated, reviewed twice by Codex).
  `FileStream` leaves a tail of zeros out at open and cuts it at the
  first append. A committed encrypted record ends in a zero byte in 1
  stream of 256, so the rule is unsafe for ciphertext.
  * (a) the builder switches the repair off when the internal key is
    set: one line above `FileStream`, against the constraint of
    2026-11-26; an encrypted stream with such a tail is refused, as
    after part 1.
  * (b) a repair at the record level, above `FileStream`, which
    validates the key and the records before it cuts: also for
    encrypted streams, more work.
  * (c) `FileStream` tells plaintext from ciphertext by its bytes: not
    sound (Codex).
  * Default: **(a), and land the branch** (Codex: the safest and the
    simplest now). Frans's, as it sets the constraint aside.
  * Answered by Frans, 12:11 (section 2), with none of the three: the
    internal crypto code is removed (028-69), so no encrypted stream is
    left to choose for. Part 2 is rebased on 028-69 without the
    opt-out, looked at by Codex again, and landed.
* **C2. 028-66: the cut's deletes** (section 4). Since 028-62 a writer
  with hard sync at full speed is about 40 % slower on F53, and above
  100 MB/s it keeps 1.3 to 1.6 times its stream on disk; up to 60 MB/s
  1.15 at most.
  * A: as it is, a directory force per deleted file.
  * B: a batch with one force; the disk at 1.03 to 1.05; 011-07's rule
    changes, and a power loss on a file system that does not order
    unlinks can leave a directory that a start refuses.
  * C: a batch with a forced record of the first position; not designed.
  * Back towards a quarter (028-62's tenth undone in part).
  * Default: **A for 2026.7, C as a 028 entry** (the lead; the entry
    recommends none): the cost shows at 100 MB/s of stream and more,
    and B gives up 011-07's ordered deletes for it; `timing.sh` against
    2026.6 shows the cost before the release. B is Frans's if wanted:
    it changes 011-07.
* **C3. 028-67: bytes of a deleted file in a start's tail** (APFS
  images and RAM disks; not seen on F53's SSD).
  * C1: refuse with the cause and the way out, and no fill of up to
    2 GB before the check; about 80 lines, no format change.
  * C2: cut such a tail. C3: meta blocks and records hold their place
    and the database's ID (class 3: the format). C4: zero new files.
  * Default: **C1 now, C3 with the next change of the format (032)**
    (035-02).
  * **Decided, 16:02: C1 and C3, both in 2026.7**, with 031-06's
    format; C2 after C3 is tested; C4 not taken (section 2).
* **C4. 028-54: a released bug or not.** On `main`, 2026.5 and 2026.6 a
  stop or a crash inside a commit's maintenance gives other bytes for
  the same transactions; the README says "The same transactions in the
  same order give the same bytes" (031-05, section 4.5). Default:
  **yes, a new entry in 033, S4, fixed by A2** (the lead; 033 counts
  faults in theory). 028-54 closes when A2 is decided (class 3).
* **C5. 028-34: `transactionInfo()`** (class 3: the Pub API): kept in
  the Pub API with more tests, or the walk moved to the Core. Default:
  **as it is in 2026.7** (the lead; Frans's choice for 2026.6,
  2026-11-22).
* **C6. 026-04: three recommended fractions and a default for
  reclaim** (class 3: the scope). Default: **1/4 kept in 2026.7, the
  choice moved to 2026.8 (032)** (the lead): B1 and B11 change what
  reclaim writes, so figures measured before the landing would be
  measured again.
* **C7. 026-14: the Lean model's three additions** (class 3: the
  scope): reclaim as a whole, the format as bytes, the conflict check.
  Default: **none in 2026.7** (the lead): the first after the landing,
  with A5's statement; the second with the stable format; the third
  when transactions next change.

Not asked: 028-65 (no decision in it); 026-03 and 031-01's F1, one
maintenance path for a commit and a call, which the landing's design
item answers; G4's M5 at 1.933 of 2.0 (031-05, F9) and `catchUp()`
inside the code that fails the database (F7), both work of the landing.

### 4.4. By default, with a time

None open. D1, where the notes of 2012 go, went ahead at 09:15
(section 2).
