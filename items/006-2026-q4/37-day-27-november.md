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
* **028-68: B** (16:09): the reclaim step reserve a constant, with a
  hook for tests only; built in the landing's step 2.
* **028-66: C to be designed** (16:15): with the files before a hole
  removed by the Core's own cut; an agent works on the design; A until
  it is in.
* **P2's wording** (16:26 to 16:41; 031-06's `p2-draft.md`, W2, W4 and
  W5): the unit is the transaction, so a setter and a part of
  `maintain()` need no list of kinds (16:26); the creation is the
  primordial transaction (16:38); the README's sentence is reworded
  without "a crash": a restart or a stop changes no byte, and a crash,
  which may leave a partial append, is not promised (16:41).
* A transaction that asks for no maintenance exists already as a mode
  in the Core, a setter's; a flag for it on user transactions is a
  possible later feature, not now (16:31).
* **028-34** (16:45): `transactionInfo()` as it is in 2026.7; the API's
  question in a later release.
* **026-04** (16:47): 1/4 kept for now; the three values and the default
  are chosen after the landing's step 3, on the new pace, with the
  measurements made again.
* **026-14** (17:10): no additions to the model's scope in 2026.7; the
  first, reclaim as a whole, belongs with the proof of P2's extension,
  after 2026.7.
* **RB-013** (17:12): 028-54's stop case is a released bug, S4, in
  2026.5 and 2026.6, fixed by 031-06; the crash case is not counted.
* **The probes on `main`** (17:25): RB-007's, RB-010's and RB-006's
  rest are run again on `main` after the timing run.
* **028-66: C, with a rule** (17:26), as the lead recommended (028-66,
  section 4; the design in section 5 on its branch): (1) a start deletes
  the files before a gap only if their first meta block is this
  database's (028-67's check of the ID, C1), and else refuses; C does
  not land before that rule is in; (2) C replaces A for 2026.7, after a
  timing run on a quiet machine against `main`, that rule and a review.
  So C lands after the landing's step 4, the format, which brings
  028-67's ties. A stays on `main` until then.

Frans, 2026-11-28:

* **028-76: (a) for 2026.7** (06:05): 028-66's rule for the files
  before a gap stays as it is. A file before a gap whose first block is
  recovery's fill makes the start refuse, with the file and the way out
  named; nothing is lost. (b), the fill written as a valid block, is
  studied with 031-07's review of the stream's checks.
* **The usage limit is 90 % of the week** (06:10), from 50 %; the
  weekend's work need not be kept light.
* **028-67's C2 is held, and 028-77 registered** (07:07): whether the
  stream's files stay strictly append-only, or a start may rewrite the
  tail, is a decision of its own, on a model of what BergDB may take for
  granted from the storage (the review, 035-03). Taken up after 2026.7's
  work is stable. Until then a tail of zeros is cut as it is (028-60,
  part 2) and a tail of other bytes refused (028-67's C1).
* **O1: (b), a cap of 1,024 bytes on BergDB's own long keys**
  (07:27), a new limit L9 in 024-17, checked where a long key enters a
  transaction, not at reclaim's copies or at a start (031-06, section
  8). To be built.
* **028-73: (b)** (07:27): new stream files of at least 1 MB once the
  stream kept reaches 4 MB; the tenth unchanged above 10 MB. The fix is
  the branch's (`loadwait-1mb-floor`), to be rebased and landed.
* **028-74: (a)** (07:27): the limit stated in `currentTime()`'s Javadoc
  and in P2's draft: a time given holds for the session that gave it.
* **028-75: (c)** (07:27): a call begins a pass only when the stream
  kept is more than about 1.5 times the live bytes and more than about
  400 kB over them, the live bytes kept up to date by each record. To be
  designed and measured.
* **031-07's five, as its inventory recommends** (07:30): the node
  checksums stay (N1); the got-dirty list gets nothing new (GD1); the
  meta block holds its own position and the database's ID, nothing more
  (M1); the record header's check stays 24 bits (W24); and "the storage
  owns the integrity of the bytes, detection of damage is a best effort"
  is a rule, R6 of 010-04, not a principle. R6 is added to 010-04 in the
  inventory's wording (its section 5.4).
* **A check of the nodes' place goes with 028-77's review** (07:30),
  not into 2026.7: 028-67's finding that C3 does not cover nodes
  (another database's nodes behind a record's own header) would be
  closed by node checksums that include the position and the database's
  ID, a change of the format (035-03's scope).
* **028-71 and 028-53 are closed** (07:30). 028-71's limit stays as
  stated in 027-13: under commits of 1 MB the stream kept is 18 times
  the live data, by the cap of 128 KiB a step. What is left of 028-53's
  idle rewriting is 028-75.

The lead's, 2026-11-28 (class 1, from the timing run of 01:38 to 02:50;
section 3):

* Review 3's W1, a commit's warm-up reading ahead for up to 4 queued
  commits, is kept.
* Step 3 of 031-06's landing and 028-66's C landed on `main`: the
  conditions Frans set (the review, the rule, a quiet timing run
  against `main`) were met.

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
* 16:04 The landing's steps 0 and 1 done on the branch (031-06's
  `landing.md`): step 0 `BEFORE COMMIT OK`; step 1 `LEVEL 2 OK`,
  `LEVEL 3 OK`, the contract's `GATE OK` (254 theorems),
  `BEFORE COMMIT OK`, `LEVEL 4 OK` (quick).
* 16:09 Frans: 028-68, B (section 2).
* 16:15 Frans: 028-66, C to be designed (section 2); an agent designs
  it.
* 16:26 to 16:41 Frans: P2's wording (section 2), in 031-06's
  `p2-draft.md` (`dd62fc27`, `24f15bbb`, `a9d87266`).
* 16:45 Frans: 028-34 (section 2).
* 16:47 Frans: 026-04 (section 2).
* 17:00 The landing's step 2 done (031-06's `landing.md`): an action
  alone is admitted within 7/8 of the record limit; the record, action
  and maintenance together within 15/16, and a check before the append
  that a later record can take its index nodes. Record format 9; the
  step reserve a constant (028-68). `BEFORE COMMIT OK (81 s)`,
  `LEVEL 2 OK`, `LEVEL 3 OK`, `LEVEL 4 OK` (quick), `APPS OK` (quick).
* 17:01 The landing's branch merged into `main` (`5b88cc80`): steps 0
  to 2 of 031-06; steps 3 to 6 follow on `main`. 028-68 done.
* 17:10 Frans: 026-14 (section 2).
* 17:12 Frans: RB-013 registered, S4 (section 2; 033); 028-54 done.
* 17:15 028-66's option C designed and built by an agent, on the branch
  `028-66c` (`e6900401`) of a clone, not on `main`: `BEFORE COMMIT OK`,
  `LEVEL 3 OK`, `KILL RESTART OK` (200 kills), the native flush order
  and the backup gap probes OK; two questions for Frans (028-66,
  section 5.10, on the branch).
* 17:18 `timing.sh` started on `main` (`5b88cc80`) against 2026.6, in a
  clone, alone on F53; it ends about 19:30.
* 17:20 to 17:28 O1: BergDB's own long keys investigated by an agent,
  reading and arithmetic only (031-06, section 8): the longest key
  BergDB writes itself is a Pub index entry, 275 + L6 + L2 - 1 = 496
  bytes, 71 segments; a cap of 1,024 bytes is safe and recommended, as
  (b), for Frans (section 4). 028-72 registered from it: the action's
  7/8 against the worst action by the Lean's count of nodes a level.
* 17:24 RB-013 and the bookkeeping since 16:04 landed (`f3562aad`): 033
  and its counts, the notes of 2026.5 and 2026.6, `releases/next.md`,
  028-54 and 028-68 closed; the GitHub release pages of 2026.6 and
  2026.5 set from the notes.
* 17:25 Frans: the probes on `main` (section 2).
* 17:26 Frans: 028-66, C with a rule (section 2).
* Tonight, when the timing run ends: `night.sh` on `main`, and an agent
  that runs the probes of RB-007, RB-010 and RB-006's rest on `main`
  (033 and `releases/next.md` change only on their evidence);
  a `news.md` entry with the timing's figures and the night's result.
* The plan to Monday 07:00 (the lead, 17:24), each step gated before
  the next:
  1. An independent review, by an agent on Fable, of the diff landed at
     `5b88cc80`, and its fixes.
  2. 031-06's step 3, the pace: the after-row charge by the fixed-width
     patch (its fallback, the charge one record later), a commit's step
     sized by its allowance under large commits (028-71), a warm-up of
     the step's scan before the lock, and P1 measured on a database
     larger than memory.
  3. 031-06's step 4, the format: 028-67's ties (a meta block's own
     position and the database's ID checked; the record header's 24-bit
     check; C1's refusal), then 028-66's C with its rule, with a timing
     run; the clean-up of step 4 (the 1,024 kept times and ordinals, the
     tests that depend on the stream's layout).
  4. `week.sh` on `main`, once the code has been quiet.
  5. 031-07's inventory of the stream's checksums, as a study for
     Frans.
* Not done without Frans: the release's scope, tag and theme; the cap
  on own keys (O1); removing a checksum or changing 010; deletions other
  than the lead's own run data; landing 028-66's C before its rule and
  its review.
* 17:27 Frans left for the evening; the lead runs unattended until
  Monday 07:00 on the plan above.
* 17:28 The investigation's results on `main` (`a20b0034`): O1 in
  031-06 with options (a) to (c), 028-72 registered, 028-66's decision
  of 17:26 in its entry.
* 18:07 The timing run on `main` (`5b88cc80`, the run of 17:16, against
  release 2026.6): TIMING ALERTS: pauses. CORE 0.963 of 2026.6 (0.260
  against 0.270). The perf step: no alerts; writes 6 to 14 % faster
  (w-uni-100-inf +5.8 %, w10m-fin +7.3 %, w10m-inf +13.9 %). Pauses:
  one commit of 68.9 ms in one of the candidate's two runs (phase
  tsize=500, with gets of 33.6 ms at the same moment), 15.6 ms in the
  other; 2026.6 23.2 and 11.6 ms; guide 50 ms.
* 18:08 to 18:18 Two reruns of the pause step, ABBA against 2026.6:
  TIMING OK both, the candidate 10.2 to 13.4 ms, 2026.6 10.1 to
  11.5 ms; the 68.9 ms did not repeat. The probe's load phase, which
  its figure does not count, had waits for room in the write buffer
  in 6 of 6 runs on `main`, 144 to 282 ms, against 0 to 16 ms on
  2026.6 and 15 to 26 ms on 031-06's prototype.
* 18:22 The independent review of the landed diff started, an agent on
  Fable (plan step 1); with it, an agent on the load phase's waits.
* 18:41 The waits bisected to `05fc573c` (028-62, new files a tenth of
  the stream kept): a new database writes its first 10 MB in 200 kB
  files and the writer's thread drains slower than a fast load appends;
  the stream's bytes are the same, 031-06 is not involved. 028-73
  registered, options for Frans (section 4); (b), a floor of 1 MB from
  4 MB kept, made and gated on a branch (`5731b6c9`), not on `main`.
* 18:43 `night.sh` on `main` started (report `2026-11-27-1843`).
* 18:45 The agent for the probes of RB-007, RB-010 and RB-006's rest on
  `main` started.
* 18:52 RB-006's rest, RB-007 and RB-010 fixed on `main` (`17c7c7db`):
  each probe, ported to `maintain(int)` in 033's `probes/`, still shows
  its bug on 2026.6 and not on `main` (TwoStretchProbe 18,896 bytes
  kept against 790,264; HoleProbe 71,368 against 4,804,384;
  StopAtProbe: the filler never live on `main`, live after record 6 on
  2026.6). `releases/next.md`: no known released bug.
* 18:55 Two studies started, independent of the review: 031-07's
  inventory of the stream's checks, and 028-72's count of index nodes a
  level at node size 8.
* 19:15 The independent review of the landed diff done and on `main`
  (`4dc82fff` to `db92c882`, 031-06's `review-main.md`): no restart,
  stop, failure before the append, torn record or eviction schedule
  changed a byte (12,105 interruptions, 0 different). Its findings:
  * R1, medium, the Core API: a `Trans` executed again after a failure
    past the go point writes other bytes;
  * R2, medium for the tests: `checkTakeable` fails databases at lowered
    record limits with a larger startup distance; none found at the
    release's limits;
  * R3, not of this diff: a commit's time after a restart at or before a
    time a reader was given; 028-74;
  * R4, the cost of 031-04's rule: one small put, then `maintain()`
    calls, rewrite the whole live data; 028-75;
  * R5: `takeRoom()` counts a taker with no KVs, M4's record stores the
    table;
  * R6: the item's probes do not run on `main`;
  * R7: the Lean's check of one operation a key in a step's record only.
* 19:16 The fixes of R1, R2, R5, R6 and R7 (with `Db`'s stale Javadoc
  on 2026.6's filler) started on a branch, `031-06-review-fixes`.
  `night.sh` past its level 3: `LEVEL 2 OK`, `LEVEL 3 OK`.
* 19:18 028-72 settled and on `main` (`eeefa108`): by Java's own count,
  which `Db` compares, no transaction within L1 to L5 is refused by the
  action's 7/8 at any node size; the worst at node size 8 is 76.5 % of
  the 7/8; 024-17's 14 a level bounds it, the Lean's 19 is a looser
  bound of the same count; 024-17's 9 at node size 14 is short since
  028-21 (9.12 a level). Options A to G; A recommended (section 4.4).
* 19:22 031-07's inventory on `main` (`5d6fe4ae`): 44 checks of the
  stream's integrity; a probe of 255,169 damaged copies gave no wrong
  values with node checksums besides the decided known cases, and
  59,596 without them; of 4,783 stale tails the node checksum was never
  the only check that refused one; 2 stale tails took another
  database's records whole (028-67's S1 case), which C3 refuses.
  Recommended: N1, node checksums kept; GD1, nothing added to the
  got-dirty list; M1, the meta block's own position and database ID and
  nothing more; W24, the header's check of 24 bits, as decided; the
  principle as rule R6 in 010-04. For Frans (section 4).
* 19:27 Step 4's format checks, 028-67's C3 and C1, started on a branch
  (`028-67-c3`), beside the review's fixes.
* 20:29 The review's fixes on `main` (`97954827`, `48203205`): R1, the
  plan's fields set at every execution's go point (RmReuseProbe the
  same stream in 20 of 20; a unit test); R2 with R5, the take bounded
  by the check's own count, `takeRoom()` less the table's 256 KiB
  (RmRoomProbe 9 of 9 cases without failure; StreamDigest quick 44 of
  44 identical at the release's limits); R6, the item's probes compile
  and run on `main` (the sweep 27,720 interruptions and 567 torn
  records, 0 different); R7, the Lean's check of one operation a key in
  every record; `Db`'s stale Javadoc on 2026.6's filler. `BEFORE COMMIT
  OK`, `LEVEL 2 OK`, `LEVEL 3 OK` (C-STEP as the landing's). R3 and R4
  are 028-74 and 028-75.
* 20:36 Step 3, the pace, started on a branch (`031-06-pace`), until
  06:00: the after-row charge, a commit's step sized by its allowance
  under large commits (028-71), a warm-up of the plan's scan before the
  lock, and a probe for P1 on a database larger than its cache.
* 20:51 Step 4 built: a meta block holds its own position, valid only
  at the position it was read at and with the ID of the stream's first
  block (meta version 156: `main`'s older databases and 2026.6's are
  refused at the first block, before any write); a record header holds
  a 24-bit CRC-32C check, compared at every parse; the recovery walks
  the tail before it writes and refuses a bad one with
  `BadTailException`, which names the cause, the position and the cut.
  On its branch `BEFORE COMMIT OK`, `LEVEL 2 OK`, `LEVEL 3 OK`, `LEVEL 4
  OK` quick, `APPS OK` quick; being gated on the combined tree with
  `main`. `night.sh` so far: every step ok (through the night tests and
  the harness soak).
* 21:50 Step 4 on `main` (`b0aac3a9`, `53ff486f`, `734f05a2`), gated on
  the combined tree with the review's fixes: `BEFORE COMMIT OK`, `LEVEL 2
  OK`, `LEVEL 3 OK` (C-STEP 0 of 23,127, C-CUT 0 of 869), 031-06's sweep
  0 different in all 62 lines, `faults.sh` bad 0 in all 42.
* 21:55 028-66's option C ported onto `main` with Frans's rule of 17:26,
  on a branch (`028-66-c-rule`).
* 22:18 `night.sh` 2026-11-27-1843 on `a20b0034`: `NIGHT FAILED` in one
  step, `apptraces` (a2-1, a2q-1); every other step ok. The cause is the
  harness's: since 031-06 a commit's record carries its maintenance's
  KVs, and `AppRecord` recorded them as the application's operations, so
  the replay put reclaim's table in a user's transaction, which the Core
  refuses.
* 22:21 Step 3 built on its branch: the after-row charge exact
  (UndercountProbe's uncharged part from 25.7 and 39.5 % to 0.0 %;
  reclaim's share under small commits 0.26 to 0.28); a commit's step up
  to the larger of 16 kB and twice the allowance the application's last
  record added, at most 128 KiB (028-71: under 1 MB commits the stream
  kept 18.2 times the live data, steady, from 115.7 and growing); the
  step's reads warmed before the lock (loads under the lock from 32 to
  103 a step to 0.00 to 0.06). The sweep 27,741 interruptions and 570
  torn records, 0 different; StreamDigest's reclaim configurations
  differ, as the new widths, charge and step sizes make them.
* 22:24 `AppRecord` fixed on `main` (`50c60f13`): a user's transaction
  is recorded with its own operations only; and its comparison of
  records leaves out the header's check, which 028-67 made differ in a
  replay's database. `APPTRACES OK`, 11 of 11 `TRACECHECK OK`; `BEFORE
  COMMIT OK`. `night.sh` started again at 22:25 on `50c60f13`.
* 22:42 028-66's C with the rule built: every file before a gap is
  checked before the tail walk and before anything is written; a file
  that is not this database's is refused with the cause and the way out.
  `BEFORE COMMIT OK`, `LEVEL 2 OK`, `LEVEL 3 OK` (77 gap images started
  through the check), `LEVEL 4 OK` quick, the kill and power-loss
  harnesses, the sweep 0 different, `faults.sh` bad 0.
* 23:08 028-66's review: no reason not to land after the timing run;
  R1 (low), the power-loss tester's expectation of a force at close; R2
  (low), `created.txt` written before a refusal; R3 to R5, messages and
  text. Its probe of a power loss inside the start's own batch (every
  subset of a cut's files and of the batch, 2,060 starts): `NESTED GAP
  OK`. 23:37 R1 to R5 fixed on the branch (`028-66-c-fixes`), with the
  power-loss tester on 12 seeds at 3,000 transactions, `LEVEL 3 OK` and
  `NESTED GAP OK`. C waits for its quiet timing run.
* 23:10 Review 3 of step 3, the review's fixes and step 4 (`review-3.md`,
  on `main` as `80f50c37`): T1 (high, on `main` since step 4), a start
  refused the tail that recovery itself wrote for a record cut in its
  header, when no commit came between the starts; W1 and W2 (low, costs
  of the warm-up), D1 (text, section 3's bound for 128 KiB steps). Found
  right: step 3's streams the same with and without eviction and
  warm-up; R1, R2 and R5.
* 2026-11-28 00:18 T1 fixed on `main` (`b7f21db4`, `b3f2f98b`, the note
  in `review-3.md` `080c1f2f`): zeros at the end of a cut record count
  as bytes not written; a cut record is taken if its header holds its
  check, or if its bytes up to the last non-zero byte are fewer than 32,
  begin a valid header and only zeros follow; recovery's completion
  writes only zeros after a cut size field. The review's four probes
  start every case. `BEFORE COMMIT OK`, `LEVEL 2 OK`, `LEVEL 3 OK`, the
  sweep 0 different, `faults.sh` bad 0, `KILL RESTART OK` (1,000 kills).
* 2026-11-28 00:38 Step 3 after review 3, on its branch on `080c1f2f`:
  W2 fixed (a warm-up only when the row moved: scans a part from 2.29 to
  1.34); W1 fixed with a cost (a commit's warm-up also reads for up to 4
  commits queued ahead: scans that load under the lock from 14 to 44 %
  to 0 to 13.5 %, at 1.9 to 6.4 scans a step); D1's texts. `BEFORE
  COMMIT OK`, `LEVEL 3 OK`, the sweep 0 different, `faults.sh` bad 0.
* 2026-11-28 00:42 The timing sequence queued after `night.sh`, on a
  quiet F53: `timing.sh` on step 3 against 2026.6; P1 on a database
  larger than its cache, a commit carrying a 128 KiB step of small
  values, and a start whose last record is 100 MB or more, each on step
  3 and on `main`; 028-66's comparison of reclaim's cost, `main` against
  C. Step 3 and 028-66's C land after it if their figures are fine.
* 2026-11-28 01:43 `night.sh` 2026-11-27-2225 on `50c60f13` (the
  review's fixes, step 4 and the `AppRecord` fix; not T1's fix or step
  3): `NIGHT OK` (192 minutes).
* 2026-11-28 02:50 The timing sequence done, on a quiet F53 from 01:38:
  * `timing.sh` on step 3 against 2026.6: `TIMING OK`; CORE 1.000; the
    longest pause 10.7 ms against 14.1 ms; no alerts, +5.7 to +10.6 %
    against 2026.6 (`main` before step 3: +5.8 to +13.9 %).
  * P1 on a database larger than its cache (20M keys, a budget of
    200 MB, 1M commits), step 3 against `main`: 134 s against 140 s; a
    commit with a step, under the lock, median 0.19 ms against 0.23; the
    longest commit 11.6 ms against 20.9; 74.1M loads against 78.2M.
  * A commit carrying a 128 KiB step of small values: the longest time
    under the lock 12.5 ms against 12.0; the longest commit 20.4 ms, at
    2.6 s of uptime, against 12.8.
  * A start whose last record is 100 MB or more: 4.8 s on both.
  * 028-66's comparison of reclaim's cost, C against `main`: 113,580
    transactions a second against 67,052; the disk 1.096 of the stream
    kept against 1.623; 27 files against 63.
  * Decided by the lead (class 1): W1's read-ahead stays. Step 3 landed
    on `main` (`96daa4bb` to `cdc437b2`, `java/` as gated on its
    branch), the timing run in 031-06's `landing.md` (`9f446ad5`).
* 2026-11-28 03:35 028-66's C landed on `main` (`e848c58f` to
  `5f867e08`; the reviewed branch's hashes mapped in `8a0897cf`), on
  step 3 and T1's fix: a start reads the last meta block, checks the
  files before a gap, walks the tail and only then writes. One test,
  `testRefusedStartWritesNoCreatedTxt`, failed 2 times in 40 under load
  (the test's assumption of the first file; fixed in the test, 48 of
  48). `BEFORE COMMIT OK`, `LEVEL 2 OK`, `LEVEL 3 OK`, the power-loss
  tester on 12 seeds, `NESTED GAP OK`, the sweep 0 different,
  `faults.sh` bad 0, T1's probes all starting. `week.sh` started on
  `8a0897cf` at 03:30.
* 2026-11-28 04:05 The documents (the landing's step 5) on `main`
  (`6c17b10f`): 027-13 written again from the code; 027-03 at format 9;
  027-02, 027-08, 027-11, 027-14; `maintain(int budget)`'s Javadoc; the
  README's sentence on the one stream. `BEFORE COMMIT OK`.
* 2026-11-28 04:48 `week.sh`: one step failed, apps-kill-cc. The Kill
  app (seed 2078503, database 4, node size 62) could not start a
  database after its 30th kill: no valid meta block at the stream's
  first position, 800,000; nothing written. The other steps that had
  ended by 06:15 are ok (before-commit, apps-quick, apps-soak-cc, both
  kill-restart steps; the consistency checker no failure). An agent
  started on the failure at once.
* 2026-11-28 04:52 The clean-up (Q4) on `main` (`70f45c17` to
  `b9e45295`): the clock's margins for maintenance removed
  (`TIME_MARGIN`, `LAST_USER_TIME`, `TOP_ORDINAL_MARGIN`), one time kept
  for the creation's two records; `Clock.getTime()`'s Javadoc allows any
  time up to 2^56 - 1; the stale comments and messages the documents'
  agent listed; a copy mark on a delete node refused at parse. `BEFORE
  COMMIT OK`, `LEVEL 2 OK`, `LEVEL 3 OK`, the sweep 0 different,
  `faults.sh` bad 0, StreamDigest identical in all 48 against
  `8a0897cf`.
* 2026-11-28 05:55 The kill failure's cause and fix (`05bf46e3` to
  `27267148`; 028-76, `aa68efc4`). Since 028-67's C3 (`b0aac3a9`) a
  start read only the stream's first meta block. An earlier kill had
  ended the stream at a block's position, which the next start filled as
  recovery does, not a valid block; a later cut made that block the
  stream's first. The database was sound. Fixed: the stream's first
  block is the first valid one at or after the first position. Two tests
  that failed before; `BEFORE COMMIT OK`, `LEVEL 3 OK`, the Kill app
  with the seed (300 kills) and three others, `APPS OK` quick, the sweep
  0 different, `faults.sh` bad 0, the power-loss tester. No release has
  the rule (not a released bug).
* 2026-11-28 06:05 Frans decided 028-76's open part, (a) (section 2;
  `ee8a8165`). 06:10 the usage limit set to 90 % (section 2).
* 2026-11-28 06:12 A review of the start and recovery path on `main`
  at `ee8a8165` started (Fable, effort high, until 11:00): the format's
  checks (028-67's C1 and C3), T1's rule for a cut record, 028-66's C
  and its rule, 028-76's fix and the zero tail, under sequences of
  kills and power losses.
* 2026-11-28 06:15 Started: 028-70, a start refused after its recovery
  has written (an agent, until 10:00); and a round of user apps against
  2026.7's changes, 031-08, in two parts (until 11:30). `week.sh` still
  runs its long lanes; `night.sh` on the current `main` follows it.
* 2026-11-28 07:10 028-77 (Decide: strict append-only storage, or tail
  rewrites at a start) and 035-03 (the review, a stub, not started)
  registered; 028-67's C2 held (section 2).
* 2026-11-28 07:30 Frans decided O1 (b), 028-73 (b), 028-74 (a) and
  028-75 (c) at 07:27 (section 2). The work starts as agents become
  free, at most four at a time: 028-73 with 028-74 first, then O1, then
  028-75's design.
* 2026-11-28 07:32 Frans decided 031-07's five as recommended (R6 added
  to 010-04), the nodes' place with 028-77's review, and closed 028-71
  and 028-53, at 07:30 (section 2). Left of 031-07: the Javadoc and
  030-04 cite 010-R6.
* 2026-11-28 07:40 R6 marked provisional until 028-77 is decided, and
  encryption and replication named as requirements of 035-03's model
  (Frans; `6a34dde4`, `ea89dc4f`).
* 2026-11-28 07:58 The review of the start and recovery path reported
  (Fable, 06:12 to 07:53; `f2a88740`, `b0c65f2e`: 033,
  `reviews/2026-11-28-start.md`, with its probes). Checked and found
  right, with zeros and cut tails only: `StartChain`, 21,000 starts on
  files of 200 kB, 1 MB and 5 MB and with per-append forcing off, after
  kills, kills inside a recovery's own writes and power losses in a
  cut's batch: no refusal other than 028-76's decided case (a) (212
  times), no wrong value, no file changed by a refused start, no gap
  left; the completion taken again from every part of itself; the zero
  tail, the first valid block and the gap rule hold. With other bytes
  after a quarter of the kills (7,987 starts, 768 such tails): each
  taken as cut at the kill, or refused with a `BadTailException` and
  started after the cut at P with the right state. Four findings:
  * F1, S1 on a storage of 035-02 after a restore in place: a deleted
    copy of the database's own later bytes passes C3 (the same ID and
    positions); a start took the copy's records, or named a cut that
    lost two synced puts. No check of the bytes alone closes it: 028-78,
    for Frans, with 028-77.
  * F2, S2 on a storage that can leave other bytes at a new file's
    start (not a shape seen on APFS): other bytes at a file's first meta
    block, taken inside an aborted record or kept by the cut at P,
    refuse a later start with no way out named, once reclaim's cut makes
    the file the stream's first: 028-79; the smaller fix (the tail walk
    refuses such bytes at a meta position) by default at 10:30
    (section 4.4).
  * F3 and F4, S4: a creation that a kill left as zeros is refused with
    a `StreamFormatException`, not as a creation; the zero tail's bound
    of 8 MB rests on the default write buffer (the Core API only):
    028-80, to an agent.
  * F5, notes on 028-76 (a), no new bug: the refusal also meets a first
    block cut inside and completed, and a kill lands at a file's first
    block for the time of the file switch's forces, not at one instant
    (recorded in 028-76).
  An agent (Opus, effort xhigh) starts on 028-80 and prepares 028-79's
  fix on a branch.
* 2026-11-28 08:05 028-70 done on a branch: six checks of a start
  came after the recovery's first write; all moved: the recovery's
  writes are held in memory and written after the start's last check,
  the same bytes in the same order, so a refused start writes nothing;
  a committed record of another format is refused as a version, not as
  a tail with advice to cut it. `BEFORE COMMIT OK`, `LEVEL 2 OK`,
  `LEVEL 3 OK`, the sweep 0 different, `faults.sh` bad 0, the power-loss
  tester. An independent review before it lands (Opus, effort xhigh,
  until 09:15).
* 2026-11-28 08:58 028-70's review: no finding against the change; the
  files after 884 cuts identical to `main`'s, 333 cases with reclaim's
  cuts identical but for 8 where `main` refused after writing, 6,810
  starts of 033's `StartChain` with no failure; three notes of S4 (two
  stale texts, a missing test), given to the agent of 028-80. 028-70
  landed (`2b134c37`, `a5469731`). Started: 028-73 (b), 028-74 (a) and
  031-07's follow-up (an agent, Opus, effort high).
* 2026-11-28 09:30 Landed: 028-73 (b), new files of at least 1 MB from
  4 MB kept (`68a26a38`, `1270ec3c`, `28a557fd`; the wait to be timed on
  a quiet machine); 028-74 (a), the limit of `currentTime()` in the
  Javadoc of `Connection`, `Database` and `Db` (`1a136a9c`); 031-07's
  follow-up, 010-R6 cited in the Javadoc and 030-04 (`f51fa0b2`; 031-07
  done). `LEVEL 3 OK`, `BEFORE COMMIT OK`. Started: O1 (b), the cap of
  1,024 bytes on BergDB's own long keys (an agent, Opus, effort high,
  until 11:30).
* 2026-11-28 09:48 Frans asked that 031-02's apps be brought up to date,
  run, and kept running: they are only in 031-02's directory, run by no
  script, and no longer compile since `maintain()` takes a budget. An
  agent (Opus, effort high, until 12:30) updates them, runs them on
  `main` and moves them into `java/stress/apps.sh` (which `week.sh`
  runs).
* 2026-11-28 09:51 Frans away from BergDB until Monday 2026-11-30. The
  plan of 2026-11-27 holds until then; class 3 waits for him.
* 2026-11-28 10:00 028-72 A went ahead by default (section 4.4): an
  agent at the next free slot.
* 2026-11-28 10:16 028-80 landed (`d5aa1cf7`, with 028-70's follow-up
  `929537b5`, and `71cf993e`): a creation that a kill left as zeros is
  refused as a creation that did not complete, and `FileStream` writes
  at most 5 MB at a time, so the zero tail's bound holds for every
  buffer. On the combined tree `BEFORE COMMIT OK` and `LEVEL 3 OK`; on
  the branch the sweep, `faults.sh`, the power-loss tester, 1,000 kills
  of `kill-restart.sh` and 4,000 starts of `StartChain`. F3 is in
  2026.5 and 2026.6: RB-014, S4 (033). 028-79's fix is built, in its
  gates, with an independent review before it lands.

## 4. Waiting for Frans

Every open question, each with a default: whose it is, and why. The
defaults of sections 4.1 to 4.3 have no time: nothing of them goes
ahead before Frans has read the page. Section 4.4 has the defaults
with a time: one is open, 028-72's A.
"Class 3" marks what only Frans decides (013-04: the stream format, the
public API, a release's scope, the principles, an item closed). The
details are in the items, cited by ID and section.

### Open now (2026-11-28 08:00)

What is open for Frans after the decisions of 2026-11-27, 16:09 to
17:26, and of 2026-11-28, 06:05 to 07:30 (section 2). The text of
sections 4.0 to 4.3 is left as it was written. Answered on 2026-11-28:
028-76, (a); at 07:27 O1, (b), 028-73, (b), 028-74, (a), and 028-75,
(c), each to be built (the options are in 031-06's section 8 and in the
entries); at 07:30 031-07's five as recommended, with the principle as
rule R6 of 010-04, the check of the nodes' place (028-67's finding)
moved to 028-77's review, and 028-71 and 028-53 closed. Settled by the
lead: the warm-up's reading ahead (review 3's W1) stays, from the timing
run. New at 08:00, from the review of the start path (section 3,
07:58): 028-78.

* **028-77: strict append-only storage, or tail rewrites at a start**
  (class 3: the storage contract; not for today). Three tails after a
  crash are known: a cut record (the start appends zeros), a tail of
  zeros (`FileStream` cuts it at the first append, the one rewrite) and
  other bytes (refused; the automatic cut, C2, held). Options: (A)
  strictly append-only files, (B) the provider may rewrite the tail,
  (C) as today. No recommendation before the review, 035-03; taken up
  after 2026.7's work is stable. With it: 028-67's C2, and the check of
  the nodes' place.
* **028-78: a deleted copy of the database's bytes in the tail pass
  C3** (class 3: the format or the contract; with 028-77, not for
  today). On a storage that can leave a deleted file's bytes after a
  kill (035-02), after a backup was restored in place, the deleted
  files' later records have the database's ID and positions: a start
  took them, or named a cut that lost two synced puts (the review's
  probes, on constructed images).
  * (a) The storage's to prevent: a limit stated under R6 and in
    `Database`'s Javadoc (restore into a new directory or volume).
  * (b) A restore makes a new incarnation that later records and blocks
    are tied to: a change of the format and a restore tool or call.
  * (c) New stream files zeroed before use (028-67's C4, not taken on
    2026-11-27 for its cost).
  * Recommended: taken with 028-77; (a) meanwhile, as the state of the
    code.
* **The theme's wording for 2026.7** (Frans's; section 2, 11:37).
* **Codex's stop by the content filter** (section 3, 14:24), known to
  Frans.
* Still open from sections 4.0 to 4.3: A5, the Lean statement (026-14's
  answer puts the first model addition with the proof of P2's extension,
  after 2026.7); P2's text in 010, which is Frans's (031-06, step 5);
  B8 to B14 of 031-04's design, as the landing reaches them. Q4 and Q6
  of the landing are answered by the clean-up and the timing run of
  2026-11-28 (section 3).
* Answered since 16:02: 028-68 (B), C2 (028-66: C to be designed), C4
  (028-54: RB-013), C5 (028-34), C6 (026-04), C7 (026-14), P2's wording
  (W2, W4, W5), Q3 (step 2: the record's room by a check) and Q5 (step
  2: the record's format, 9); 028-66 (C with a rule, 17:26).

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

* **028-72, option A, by default Saturday 10:00** (the lead's, class
  2): the counts in 031-06's sections 3 and 9 and in 024-17 corrected
  (024-17's 9 a level at node size 14 becomes 10), and a `DagTester`
  guard test of the worst path against 14, 10, 8 and 8 nodes a level;
  B, the Lean's `nodesALevel` restated (14, 10, 9, 9) with a theorem
  that an action fits the 7/8, with the next change of `Bound.lean`.
* **028-79, the smaller fix, by default Saturday 10:30** (the lead's,
  class 2): the walk of the tail refuses other bytes at a meta position
  inside the tail that it takes (a cut record's blocks, and the block
  after the last whole record), with a `BadTailException` whose P is at
  or before the block, so that no later first block can be other bytes;
  a start then refuses, with the cause and P, a tail that it takes
  today. The wider fix (every reader of a first block passes over what
  is not this database's, with the ID from a source that other bytes
  cannot give) is left to 028-77. An agent prepares the fix on a branch
  before then; it lands after 10:30.

D1, where the notes of 2012 go, went ahead at 09:15 (section 2).
