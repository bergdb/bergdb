# 006-35 Day work, 25 November 2026

Created 2026-11-25 by Frans Lundberg. Status: open. The plan for the
lead's day of 2026-11-25 (lead-1125), a Wednesday, and its night to
Thursday 07:00: the progress and the outcome. The way of working is
013-04's (the lead).


## 1. The request

* 028-53 / RB-007, open from 006-34: the choice between its options.
* After it: what the combined design of 031-01 brings to Frans.


## 2. Decisions

Frans, 2026-11-25:

* 028-53: no choice between A, B and C on their own. The fix of RB-007
  and of the idle rewriting is designed together with 026-03 (one
  maintenance step for a commit and for `maintain()`), in 031-01, as a
  design with no landing (13:03). Reasons: `maintain()` in the public
  API is not an absolute requirement, the database's return to empty is
  wanted, and one way into the maintenance work would be the simpler
  design; A's mark of the application's writes is the first candidate
  for how a quiet database knows that it is done.
* RB-007 stays open while the design is made (S4, no release near).
* The design says if and how it affects the Lean proofs (13:04).
* 031-01's repair is weighed by the state it adds that must survive a
  stop, a crash or a restart, and its recovery cases; B (one line, no
  state) if every exact repair adds recovery machinery (14:17, after
  Codex's findings).
* The run data of 13 to 20 November and of the coordinator (`coord`) in
  the bench directory deleted, to free disk for `week.sh` (13:51).


## 3. Progress

* 08:56 lead-1125 started; 09:19 lead-1124 closed (006-34 closed,
  `f4e5e8b1`). Nothing ran.
* 12:35 to 13:03 028-53's options gone through with Frans: how often A
  writes W and its cost, A against P2, and the relation to 026-03.
* 13:05 031-01 registered; one design agent (Opus, xhigh) in a clone.
* 13:27 No known bug open but RB-007 (in 031-01). A review by Codex of
  the Java changed since 2026.6 (11 commits: 028-01, 028-48, 028-50,
  028-51, 028-19), in a clone, for findings before 2026.7.
* 13:44 031-01 designed (agent, Opus xhigh, 38 minutes): one step for a
  commit and `maintain()`, w in reclaim's table, M1 with it; RB-007 and
  the idle rewriting fixed in its prototype (branch `031-01-proto`,
  BEFORE COMMIT OK); no Lean statement, premise or checker changes.
  Landed as text; F1 to F7 for Frans (031-01, section 12).
* 13:37 Codex's review of the Java since 2026.6 (11 commits, `4ce8f942`):
  no new bug. RB-007 reproduced independently, on `main` and 2026.6.
  Found sound with probes that ran: STM's hashing and bins (028-01,
  028-48; 1.28M adds against a reference map), the refusal after key
  transformations (028-50; the retry's bytes equal a twin's), six
  concurrent writers, PE's short way and routing (028-19; 8 cases, the
  same bytes as the released writer, with restarts too), and 028-51's
  rule. BEFORE COMMIT OK. 13:49 Codex's second opinion on 031-01
  started.
* 14:09 The old bench data deleted: disk 52 to 387 GB free. `week.sh`
  started on `09bf9efb` (the Java of `4ac71aee`, 028-19's PE change
  included; the last week run was on 20 November), detached, nice 10.
* 13:59 Codex's second opinion on 031-01: the design fails as written.
  A w recovered at a start is not stored before a later record (a
  setting, an empty transaction, a stop) hides it: a database keeps 3 MB
  of deleted data for good, and a restart changes the stream (P2); a
  crash before w's store changes the records' order. The rest found
  sound. 14:15 the design agent resumed to repair w's persistence; F1
  to F7 wait for the repair and a check by Codex.
* 14:26 031-01 repaired (agent, 14 minutes; text landed `cb0ecfa9`):
  Codex's four cases pass, but the only exact repair adds a store and a
  start that writes (1 state, 1 store, 2 recovery cases); by the
  criterion of 14:17 the design now recommends B for RB-007 (F2). A
  finding on `main`: a stop or a crash inside a commit's maintenance
  changes the stream; 028-54 registered (Frans: whether P2 covers it).


## 4. Outcome

Not written yet.
