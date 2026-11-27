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


## 4. Waiting for Frans

Every open question, each with a default: whose it is, and why. The
defaults of sections 4.1 to 4.3 have no time: nothing of them goes
ahead before Frans has read the page. Section 4.4 has the defaults
with a time: none is open.
"Class 3" marks what only Frans decides (013-04: the stream format, the
public API, a release's scope, the principles, an item closed). The
details are in the items, cited by ID and section.

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
* **A2. In 2026.7** (class 3: the scope and the Pub API). The design
  lands in Java with its tests in 2026.7: `maintain(int budget)`
  replaces `maintain()` in `Db` and `Database` (031-04, C1), and it
  fixes RB-007, RB-010 and the rest of RB-006. Default: **yes** (the
  lead; Codex and the reviewer on Fable both say take the direction).
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
* **A4. P2's wording** (class 3: 010 is Frans's; 031-05, Q1).
  * (a) the draft of 031-05, section 4.3, which names the setters.
  * (b) without the setters, which become `execute()` calls.
  * (c) commits only, `maintain()` as today.
  * Default: **(a), corrected as the review says** (section 12, F2 to
    F4 and F11): it holds at record boundaries; a torn record is an
    input; the unit of `maintain()` is a part; the settings are inputs.
    The text goes into 010 after the design is made to work (Frans,
    08:41), by Frans.
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
  an item later** (the study, the reviewer).
* **B3. The creating start** (Q5): (a) the creation is action 0, its id
  and time inputs; (b) no random id. Default: **(a)** (both).
* **B4. The clock held while maintenance is due** (Q6): (a) held, (b)
  not. Default: **(a)** (both); with A1 (c) only inside calls.
* **B5. One record a part in `maintain()`** (Q7). Default: **yes**
  (both), and the part as the unit of the wording (F4).
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
