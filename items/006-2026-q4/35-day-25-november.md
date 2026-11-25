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
* RB-007's fix: neither 028-53's A nor B. A search for an elegant
  `maintain()` by an agent on Fable, high (031-03), from what 028-53 and
  031-01 found (14:54). The app hunt (031-02) runs now, on `main` as it
  is; its apps run again after the fix (15:02).
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
* 14:57 031-03 taken by an agent on Fable, high, until 22:00. 15:03
  031-02's app hunt taken by an agent on Opus, high, until 19:00.
* 15:19 `week.sh`'s soak of the user apps failed: Churn (seed 2078207,
  node size 30), `getTrans` refused the position of a committed
  transaction (a bad record header where its walk began, at the start of
  a stream file). 028-55 registered and taken by an agent on Opus, xhigh;
  `week.sh` goes on with its other steps.
* 15:50 028-55 fixed by its agent (38 minutes): `Db.getTrans` walked
  from the stream's first position, inside a record, after a cut; RB-008,
  S3, Core API only, in 2026.5 and 2026.6. 16:03 Codex's review: the fix
  holds; a race in the same walk since 2026.5 (028-56) and a test that
  failed in its sandbox (028-57) registered. Landed (Frans, 15:59).
* 16:07 Frans off for the day. 16:41 028-56 fixed by its agent (36
  minutes): the walk takes no named start before reclaim's cut and
  starts again when a cut removes what it reads; RB-009, S3, Core API
  only, in 2026.5 and 2026.6. 16:49 Codex's review: no finding (2,689
  interleavings, 18 stream cases, BEFORE COMMIT OK). Landed.
* 16:55 028-57 (Codex): the test's timing, not a fault of the database;
  the test fixed, BEFORE COMMIT OK on `main`, landed (`044c82a7`).
* 16:59 031-03 designed by its agent (Fable, high, 2 hours): w read off
  the stream at every record, no store and no recovery case of its own,
  M1 one formula; RB-007 and the idle rewriting ended in its prototype,
  Codex's four cases of 031-01 pass; landed as text. Two faults on
  `main` found on the way registered: 028-58 (an emptied database kept
  at 790 kB) and 028-59 (the filler left live after a stop); an agent
  checks the releases. 17:03 Codex reviews 031-03 for Frans's morning.
* 17:12 031-02's app hunt done (11 apps, 81 runs, about 9,500 kills):
  F1, S2, after a kill macOS can leave the last file's tail in zeros,
  and over a meta block the start refuses (028-60, an agent fixing it);
  F2, an emptied database kept at 2 to 3 sd under `maintain()` (028-61,
  an agent investigating, with 031-03's prototype). The rest sound.
* 17:14 028-58: no new released bug (RB-006's and RB-007's; RB-006 fixed
  in part on `main`); 028-59: RB-010, S4, the filler left live after a
  stop or a crash, in 2026.5 and 2026.6, not fixed (with 031-03).
* 17:17 Codex's review of 031-03 (031-03, section 14): the witness
  holds in every case tried, upgrades included; the drain can repeat
  with a reduced step reserve (a test setting, quiet at the default); a
  writable downgrade to 2026.6 and back can lose w; an old filler stays
  after an upgrade. For Frans's decisions in the morning.
* 17:27 028-61: an emptied file database keeps its last stream file
  (the stream itself is cut below 400 kB): RB-011, S4, in 2026.5 and
  2026.6, not ended by 031-03; 028-62 holds the options for Frans (the
  Javadoc, or a file boundary in the storage).
* 18:52 028-60, part 1 (agent, Opus xhigh): a meta block of zero bytes
  is not valid, so a zeroed tail inside the last record is recovered;
  zeros past a record's end get the documented refusal with P, which
  now works. Codex's review (after its own limit, 18:26 to 18:37): the
  code holds, two texts corrected. BEFORE COMMIT OK; landed. RB-012, S2,
  fixed in part; part 2 (B1 to B3) for Frans, B2 recommended by the
  agent and by Codex.


## 4. Outcome

Not written yet.
