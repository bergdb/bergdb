# 024-01. Inventory for 2026.5

Created 2026-11-10 by Frans Lundberg. Status: done (2026-11-10): the
inventory; Frans chose the theme on 2026-11-11 (024-04).

An inventory of the candidates for release 2026.5, so that Frans can
choose a theme and a scope (Frans, 2026-11-10, 19:24: "About 2026.5. I
would like to prepare for this work. What can we do now?"; 19:26: yes to
an inventory). The form is 020-01's: per candidate what it is, why it
matters, its risk, its size, what it depends on, and options with a
recommendation; then a summary table, possible themes, and the questions
for Frans in order.

**Nothing is decided here.** The recommendations are proposals. Read at
`main` `329d78f3`, with the integration branch `023-core` at `b7874541`
as 023-09 and 023's log describe it; read only, nothing built or run.


## 1. In short

* **Where 2026.5 starts.** Release 2026.4 (020), "a bug-free database",
  with 023's frozen core: a delete removes what it emptied, in the same
  transaction; reclaim, unchanged, frees the rest at the cut; the dead
  hand releases memory after each cut; forward scans end at their
  range's end; a transaction's keys are sorted after their
  transformation, one operation a key; record format 6 (023-08,
  sections 5 and 7). On `023-core` level2 to level4 full passed at
  `b7874541` (023's log); tonight's fuzzing and the rest of 023-08's
  gates (section 5) come before `main` and the tag.
* **49 candidates in eight areas** (section 3): the Core's cleanup (8),
  the Core API and its contracts (5), the Pub API (9), the Lean model
  (5), tests and tools (5), performance (7), the C clone (4), other (6).
  26 are small (a day or two, a todo entry as in 019 and 021), 16 are
  items of their own of some days, 7 are large or open-ended. 11 need
  Frans's thinking before work can start.
* **Decided already** (024's readme): the builder's rule "the last
  operation wins", with the C clone (CA1); and two things never to do,
  rule (b') of the window and the replaced queue on by default (023-08,
  section 5).
* **The main tension.** Most of what 023 put off adds rules to the
  Core's most intricate code (the Dag, reclaim, the take), right after
  Frans's "I smell expanding complexity where I [want] simple beauty"
  (023's log, 16:14). Whether each is worth it at 1M to 100M keys is not
  measured on 2026.4's code. So the first proposal is to measure (PF1).
* **Recommended theme** (section 14): (B), large databases, measured, on
  a calm Core: the measurement first, then only the Core changes it asks
  for (the last touch, reclaim's reads, maybe P8), on a base of tests as
  code, a bug hunt on 2026.4, the builder's rule and the C port. Strict
  cleanup (merges, compaction) and new Pub API features wait.
* **The first questions** (section 15): the theme; whether 2026.5 opens
  2026.4's databases (recommended: yes, so no format change unless it is
  additive); and the measurement first.


## 2. Scope, sources and method

* **Read.** 024's readme. 023's readme and log; 023-02 (R7, R12, F7,
  F11); 023-03 (section 4.3); 023-04 (section 2.8, X3, X4, X8,
  X9, X11); 023-05 P4 (section 3.4) and P8 (sections 1 and 8); 023-06
  (section 11.1); 023-07 (sections 5, 6.2, 6.4, 7); 023-08 whole; 023-09
  (sections 6 to 8); 023-10 (sections 1, 6, the addendum); 023-11 a and
  b. 020's readme; 020-01 (the form); 020-02 (sections 2.4, 2.5);
  020-08; 020-11 (sections 1 and 11); 020-16's log; the findings tables
  of 020-24. 021's readme, 021-19, 021-25, 021-27; the open tables of
  019 and 015, and 015-03, 015-18, 015-40, 015-84. 017's readme, 017-07,
  017-09, 017-10. 022's readme. 006-17 (section 6), 006-19, 006-20.
  docs/sis-model.md, section 15.2, for A6'.
* **Not read:** 025 (another session writes it).
* **Size.** S: a day or two, a todo entry (019, 021). M: an item of its
  own, about three to seven days with its gates. L: an item of its own,
  more than a week or open-ended.
* **Risk.** What can break, and how far: low (local, tests catch it),
  medium (a rule of the Core or a concurrency path, gates catch it
  late), high (a rule of the rerun, the format or the cut).
* **Frans.** "think": his thinking is needed before work can start;
  "decide": a choice among options already written; "-": neither.
* **IDs.** Each candidate has an ID of its area: CL, CA, PA, LM, TT, PF,
  CC, OT, and a number. They are this document's only.


## 3. The candidates by area

| Area                        | Section | Candidates | S  | M  | L |
|---|---|---|---|---|---|
| CL, the Core's cleanup      | 4  |  8 |  3 |  4 | 1 |
| CA, the Core API, contracts | 5  |  5 |  5 |  0 | 0 |
| PA, the Pub API             | 6  |  9 |  2 |  4 | 3 |
| LM, the Lean model          | 7  |  5 |  4 |  0 | 1 |
| TT, tests and tools         | 8  |  5 |  3 |  2 | 0 |
| PF, performance             | 9  |  7 |  3 |  4 | 0 |
| CC, the C clone             | 10 |  4 |  2 |  1 | 1 |
| OT, other                   | 11 |  6 |  4 |  1 | 1 |
| All                         |    | 49 | 26 | 16 | 7 |

**Not candidates: 2026.4's own closing work.** 023-08's gates before
`main` (section 5: UnlinkFuzz's new modes for a night, a reclaim
liveness test, T1, T3, T10, a cold start at 50 MB, `night.sh large`);
the documents that 023-09 left (section 6: docs/levels.md's format and
the delete's climb, sis-model.md section 3.4, `releases/next.md`,
018-01's format entry); and `releases/next.md`'s known issue of 021-25.
If any of them slips past the tag, it comes first in 2026.5.


## 4. The Core's cleanup (CL)

From 023: what 023-08 put off to later (section 5, "Later, each on its
own") and what its reviews and the ratchet test left.

### 4.1. CL1. P8: each reclaim step scans at its own time

* **What.** Each reclaim step scans the latest state up to E, the last
  key live when its iteration began, and counts against its 16 kB only
  the KVs stored before pStart (fault 13's fix, branch `023-v8-fix`,
  `0f4571fc`). In 2026.4, as before, each step scans at the iteration's
  start time tStart.
* **Why.** The iteration in progress at a mass delete ends with the
  deletes: P8 made 0 steps and 0 loads after them at 1M keys, against
  P4's 2,995 steps and, with a 20 MB budget, 175,860 loads (023-05 P8,
  section 1). 2026.4 keeps one iteration of lag: T1 at 1M needs a drive
  of 12,000 transactions, not 4,000 (023-08, section 5). P8 alone also
  removes the trigger of the dirty top-node window in T1 (023's log,
  14:48).
* **Risk.** Medium to high. A new argument for the cut's safety (I6, by
  P8's section 2.3); its first version could stop the cuts for good,
  which all three reviews found (fault 13); the fix has passed
  before-commit only (023-08, section 8). 24 % more stream during an
  ascending mass delete (85.0 MB against 68.4 MB). T-SCHEME stays
  checked, not proved. No format change; other stream bytes
  (StreamDigest, the C clone).
* **Size.** M.
* **Depends on.** PF1 (does the lag matter at 10M keys and more?); the
  liveness tests (TT2). CL5 drives whichever step exists. CL3: with P8
  the window may not form in T1.
* **Options.** (a) Leave it out; today's rule stays. (b) P8 with fault
  13's fix, the liveness tests, level3 and level4 full. (c) Review C's
  alternative, a quota in proportion to the transaction, which writes
  30 to 35 % more stream. **Recommended: (a), unless PF1 shows that the
  lag after a mass delete costs much at 10M keys; then (b).** It is the
  one mechanism that failed in review, and it gains one iteration.
* **Source.** 024's readme; 023-08, sections 3 to 5; 023-07, section
  5.5; 023-05 P8.

### 4.2. CL2. Strict shape: merges at the delete, or reclaim rebuilds

* **What.** MG (P5): in the deleting transaction, a node left with
  fewer than B/4 live klongs merges with a sibling, so no reachable node
  but a root is underfull after any transaction. The other way to the
  same end is RB: reclaim's touch rebuilds what it rewrites (023-04, X3).
* **Why.** Frans's strict allowance, wanted "if a good solution is
  found" (023's log, 10:38); 023-02, R12 (b), bounded underfill. 2026.4
  leaves about B/2 times the twin's nodes after scattered deletes
  ("sparse", 023-04, X3), so a scan and the stream follow the keys ever
  put in a range, not only the live ones.
* **Risk.** High. MG has the most cases in the Dag (023-04, X3's table);
  P5 found two faults of its own (7 and 8); thrash at a boundary is not
  measured; the merge count of `mergeBound` is an argument and a probe
  (023-07, 5.9). It is a rule of the startup rerun, so a change of the
  record format: either two rerun paths, switched by each record's
  format (review C's way), or 2026.4's databases refused (023-06,
  section 11.1; 023-08, section 3). No change of the Lean model.
* **Size.** L: P5's 545 lines of Java to integrate, its tests and gates;
  about 300 lines of C.
* **Frans.** think: is strict worth its code, and which way.
* **Depends on.** Q2 (2026.4's databases); CL4 (RB compacts, MG does
  not); CL5's full promise; PF1's numbers of underfill.
* **Options.** (a) Not in 2026.5; measure the underfill at 1M to 10M
  keys with realistic deletes first. (b) MG, switched on by the record's
  format. (c) RB with its compaction (CL4). **Recommended: (a).** 2026.4
  meets the bounded allowance, Frans's gate (023-04, X3); strict buys a
  smaller shape at the price of the Core's most intricate code.
* **Source.** 024's readme; 023-08, section 5; 023-07, section 5.9;
  023-04, X3; 023-06, section 11.1; 023-02, R12 and F11.

### 4.3. CL3. Fix (a) of the dirty top-node window

* **What.** The take also writes the dirty top nodes that a record's
  skip pointers name, with a rule for the start (P7, about 100 lines).
* **Why.** After a mass delete of 1M keys, `023-core` holds up to about
  2.5 times the twin's dirty top nodes (up to 152 against 48 to 66)
  until the next disturbance: a named allowance (023-10, section 6).
* **Risk.** Medium: the take, the start's rule, INV-1; the Lean model's
  step 5 and INV-1 and the checker (023-07, 5.10); the C clone.
* **Size.** M (the Java small; the Lean work days).
* **Depends on.** Frans's condition (023-08, Q6): only if the window
  grows. It does not: no ratchet in any run, the full run included
  (023-10, section 6 and the addendum). CL1 may remove its trigger.
* **Options.** (a) Drop it for 2026.5; keep the ratchet test as a night
  step (TT2). (b) Make it, to remove the allowance. **Recommended:
  (a).** Frans's condition is not met.
* **Source.** 024's readme; 023-08, Q6; 023-10; 023-07, section 5.10.

### 4.4. CL4. Dead klongs in live nodes: compaction

* **What.** The klongs of ended versions in a node that still holds live
  keys stay until the node's next time split: at most B a node, 2026.4's
  named allowance (023-08, Q5). With a retain duration, reclaim's
  rewrites bring the splits within about B iterations (023-04, X4).
* **Why.** 023-02, R7 (every ended version) and Frans's "eventually"
  (F2). With the retain period forever they stay for ever; in a cold
  chain of segment trees an old delete entry stayed after 700 cuts
  (023-08, section 3, review A's probe).
* **Risk.** Medium for DC (compaction at the delete), high for RB (the
  touch becomes a writer and is rerun).
* **Size.** M to L.
* **Frans.** think, with CL2.
* **Depends on.** CL2 (RB does both); Q2.
* **Options.** (a) Keep the allowance. (b) DC. (c) RB's compaction, with
  CL2 (c). **Recommended: (a)** in 2026.5; take it up with CL2.
* **Source.** 024's readme; 023-08, section 3 and Q5; 023-04, X4.

### 4.5. CL5. `maintain()`

* **What.** `Db.maintain()` and `Database.maintain()`: one bounded unit
  of cleanup a call, an iteration's start or a reclaim step, a forced
  take of D (at most 1 MiB), then the cut; it returns whether more is
  due (023-07, 5.13; 023-04, X11 (b)).
* **Why.** Cleanup is driven by the user's writes, so a database left
  idle after a mass delete gives nothing back until it is written to.
  Frans: yes, optional, never required of the user (Y10, 12:31);
  called again and again it must eventually bring a database with only
  the hello-world entry to a fresh one's resources (023-02, F7).
* **Risk.** Low to medium: a new public method in two APIs; its work is
  bounded a call (P1); it runs only when called, so a database stays
  calm when not used.
* **Size.** S (P3 had it; to be separated from P3's rebuild).
* **Frans.** decide: what its Javadoc promises.
* **Depends on.** The step it drives (CL1 or today's). F7's full promise
  needs CL2, CL4 and CL6; without them it promises the bounded allowance.
* **Options.** (a) Wait for strict. (b) Now, its Javadoc promising the
  bounded allowance only. **Recommended: (b)** with theme B or C: it
  makes 2026.4's "eventually" something a user can call and a test can
  drive, with no format change.
* **Source.** 024's readme; 023-07, section 5.13; 023-04, X11; 023-02,
  F7; 023's log, 12:31.

### 4.6. CL6. The cache's tables keep their peak size

* **What.** After a fill and a mass delete the cache's objects leave,
  but its hash table keeps its peak size: 219,104 slots against the
  twin's 22,144 (023-08, section 4, review A's `CacheCapacity`).
* **Why.** Frans's rule for memory (Y6 (b), 12:35): released eventually
  in the ordinary operations.
* **Risk.** Low: a shrink at a resize, under the map's lock.
* **Size.** S.
* **Depends on.** Nothing.
* **Recommended:** yes, a todo entry.
* **Source.** 024's readme; 023-08, section 4.

### 4.7. CL7. The last touch of a reclaim iteration

* **What.** The last step of an iteration touches every key put after
  the scan's end, in one transaction: one step dirtied 81,018 nodes
  (review A's `ReclaimTail`). Not new: `main` does the same. Review A
  prototyped marking only the rewrite paths: 27 nodes.
* **Why.** A record of many MB in one user's commit, at the end of every
  iteration, where keys are put in order (logs, metrics, queues): a
  pause against 010-01's no stop-the-world, and bytes. It grows with the
  keys put during an iteration, so with the database.
* **Risk.** Medium. The touch exists for the cut's safety; marking less
  needs the cut argument again and C-CUT on level3's traces. Other
  stream bytes (StreamDigest, the C clone), no format change: the touch
  is not rerun.
* **Size.** M.
* **Depends on.** PF1 (the record sizes at 10M keys in time order). TE,
  021-25's fix (a), ends the touch at its range: the same mechanism, to
  be changed once (CL8). CL1 changes the last step too.
* **Options.** (a) Leave it. (b) Mark only the rewrite paths. (c) TE
  with (b). **Recommended: (b), with (c) if the cut argument takes TE
  for free, after PF1.** It is the latency fault at scale of this list.
* **Source.** 024's readme; 023-08, section 4 (review A, section 4.2).

### 4.8. CL8. Close 021-25, and TE

* **What.** 021-25, reclaim stops cutting a FIFO in time order, waits
  for Frans with fixes (a), TE, and (b); Frans put both in 2026.5
  (021-25's log, 2026-11-09, 19:17). Since 023, (b) is in 2026.4 as the
  unlink at the delete: P4's ordered queue cut steadily to 1M
  transactions (023-05 P4, section 3.4). TE was optional (Y7) and not
  needed (023-06, Z9).
* **Why.** An open entry for a fault that 2026.4 fixes; a known issue in
  `releases/next.md` to take out.
* **Risk.** Low.
* **Size.** S.
* **Depends on.** 2026.4 on `main`; 023-03's T5 row "A FIFO in time
  order" at 021-25's settings.
* **Recommended:** run that row on 2026.4, close 021-25 (if not done for
  2026.4), and take TE only as part of CL7.
* **Source.** 021-25; 023-04, section 2.8 and X8; 023-03, section 4.3.

Not to do, as decided (023-08, section 5): rule (b') of the window, and
the replaced queue on by default.


## 5. The Core API and its contracts (CA)

### 5.1. CA1. The builder's rule: the last operation wins

* **What.** `Trans.Builder.build` keeps the last put of a key, or a
  delete if there is no put: a delete never replaces a put (015-40);
  2026.4's collapse of KVs that key transformations make one key uses
  the same rule (023-09, section 7.1). Frans: the last operation wins,
  put or delete, silently, for the builder too (023-08, section 7,
  17:41 to 17:48: "last operation takes precedent, put or delete. It
  should be silent").
* **Why.** One rule, the one a user expects; today a Core put and then a
  delete of one key commits the put.
* **Risk.** Low. The Pub API already gives the builder one operation a
  key (015-40: `kvOps`, and `indexOps` with `putIfAbsent`), so index
  maintenance needs no change. A Core transaction with a put and then a
  delete of one key writes other bytes: the C clone's equality.
* **Size.** S in Java, S in C.
* **Depends on.** CC1 (C at 2026.4 first); CC2.
* **Recommended:** yes, early, with C (decided for 2026.5).
* **Source.** 024's readme; 023-08, section 7; 023-09, section 7; 015-40.

### 5.2. CA2. `Db.getTrans` inside a record fails the database

* **What.** A position inside a committed record is read as a record
  and fails the database (021-27), as its Javadoc says.
* **Why.** Today's rule: misuse ends in an exception to the caller,
  never a failed database (020-27, Q2). Only the Core API (and C's
  public header) can give such a position.
* **Risk.** Low: option A works on the failure path only.
* **Size.** S (about 40 lines and tests; C follows).
* **Frans.** decide.
* **Depends on.** Nothing.
* **Options.** 021-27's A to D. **Recommended: A** (tell a bad position
  from damage on the failure path), as 021-27 recommends after 2026.4.
* **Source.** 021-27, section 2; 020-11, section 11.

### 5.3. CA3. Core writes to the internal keys

* **What.** The Core API accepts puts under "/#", and reclaim's settings
  that stop the next start (020-11, section 11, C-U2-8, from 022-06).
* **Why.** A Core user can make a database that does not start. Under
  020-22's A2 ("Core is root, with a detection floor") such writes are
  undefined.
* **Risk.** Low.
* **Size.** S.
* **Depends on.** 020-22's rules: which spaces the Core refuses and which
  stay the Pub layer's.
* **Recommended:** refuse writes to the Core's own internal keys and
  settings a start cannot take; leave the Pub layer's spaces as 020-22
  decided.
* **Source.** 020-11, section 11; 020-22.

### 5.4. CA4. Publish the Core API's Javadoc

* **What.** The Core API's Javadoc is not published; 020-24-15's Q1
  proposes to publish it in the release after 2026.4.
* **Why.** 020-27 made it true against behaviour and named what the Core
  API is at the top of `Db`'s Javadoc: less stable and less safe than
  the Pub API (Frans, 020-27, Q1).
* **Risk.** Low; a promise once published.
* **Size.** S.
* **Frans.** decide.
* **Recommended:** publish it apart from the Pub API's, with its status
  in the first sentence.
* **Source.** 020-11, section 11 (15-Q1); 020-27.

### 5.5. CA5. Exceptions of classes outside the API

* **What.** The Pub Javadoc names exceptions of packages that are not
  API, and some throw with internal messages (U15-6, U3-6).
* **Why.** A user cannot catch what the API does not name.
* **Risk.** Low.
* **Size.** S.
* **Recommended:** yes: an API exception for "directory in use" (as
  020-24-15's Q2 proposed), and the rest wrapped or named.
* **Source.** 020-11, section 11; 020-24-03; 020-24-15.

Considered, not proposed: `Kvt.tpos` or an exact write time (021-19,
options 2 and 3), a refusal of an oversized transformation result
(017-07, section 3), a get that copies (017-07, section 1). None has a
user asking.


## 6. The Pub API (PA)

2026.4 is meant as a stable baseline (Frans, 2026-11-09, 11:52, on
O16-1: "2026.4 should be a stable baseline reference"). The candidates
here are the new users' wishes (020-24) and the questions 2026.4 left.

### 6.1. PA1. Scans in `rw()`

* **What.** No scan inside `rw()` (020-01, section 14.1, N8); so "claim
  the next job" is two steps (U16-4), a delete misses a concurrent edge
  (U17-2), and a hub's delete never commits while edges are added
  (U17-3).
* **Why.** Two of 020-24's applications needed it (three findings of
  medium severity).
* **Risk.** High: the STM's read sets for ranges (phantoms), reruns.
* **Size.** L.
* **Frans.** think.
* **Recommended:** not in 2026.5 but under theme D; a design study first.
* **Source.** 020-01, section 14.1; 020-24-16, 020-24-17.

### 6.2. PA2. Scans without values: keys only, count, limit

* **What.** Every scan reads every value (U16-9, U17-5).
* **Why.** Cheap counts and listings; larger-than-memory reads.
* **Risk.** Low.
* **Size.** M.
* **Frans.** decide (new API).
* **Depends on.** PF3, the same Core path (reading a KV without its
  value).
* **Recommended:** yes under theme B or D.
* **Source.** 020-24-16 (U16-9); 020-24-17 (U17-5).

### 6.3. PA3. Index and directory administration

* **What.** No listing of the indexes or their definitions (U14-2), nor
  of subdirectories (U14-3); a rebuild under its name throws until built
  (U14-4); no word on limits (U14-5); no sign that a deleted index's
  cleanup has ended (U14-6); paging an index of two levels takes three
  scan forms (U13-5); no end for a primary scan (U18-5); no delete of a
  directory (U13-4; 023-04's RD would be a new Core operation, X9).
* **Why.** A multi-tenant or admin user cannot see what the database
  holds.
* **Risk.** Low for listings; medium for a rebuild under its name.
* **Size.** M as a group; each listing S.
* **Frans.** decide (new API).
* **Recommended:** the two listings and the cleanup's end (S each); the
  rest later; no RD.
* **Source.** 020-11, section 11; 020-24-13, 020-24-14 and 020-24-18;
  023-04, X9.

### 6.4. PA4. The index jobs' robustness

* **What.** One thread per build and per cleanup, so thousands at once
  can throw `OutOfMemoryError` and fail the database (18-O1); a status
  lag (18-O2, H3-O5); a build step reads one large value under the lock
  (18-F3r); several index names need a fair lock (29-fair); a literal
  key with a later time's digits keeps its old entry (KR-lit).
* **Why.** None breaks a promise of 2026.4; 18-O1 can fail a database.
* **Risk.** Medium: concurrency in the index manager.
* **Size.** M as a group.
* **Recommended:** 18-O1 (a queue, one thread) and 29-fair; the rest
  later.
* **Source.** 020-11, section 11; 020-18; 020-29, section 7.

### 6.5. PA5. Objects, and what a key holds

* **What.** Frans (O16-1, 2026-11-09, 11:52): "For a later release, we
  need to think long and hard on storing objects, bytes, strings at pub
  layer, indexing on them, and relationship with core layer." With it:
  object keys that hold objects only (017-09, its (a1) recommended);
  the conversion's report, option (D), which Frans wants to design in
  detail (020-02, section 2.5); records as Data Objects (L-rec), a key
  field (L-key, 017-07, section 6), path getters (L-F6); a type message
  (U12-4); a view over the database's array (020-08).
* **Why.** Usability of the public API, and the coupling that C-M8 pays
  for (PF7).
* **Risk.** Medium: an API change right after a baseline.
* **Size.** L.
* **Frans.** think.
* **Recommended:** a study only in 2026.5 (start 017-09 with Frans), no
  API change; U12-4 as a small fix.
* **Source.** 020-11, sections 1 and 11; 020-16's log; 017-09; 020-02,
  sections 2.4 and 2.5; 020-08.

### 6.6. PA6. `rw()` under contention

* **What.** `rw()` starves under a hot key: reruns are not fair (U16-2,
  medium); no rerun policy or count (U16-6); what `rw()` conflicts on,
  that commits are serial, and that its time has no bound, are not said
  (U16-3, U16-5, U16-8).
* **Why.** Services with hot counters.
* **Risk.** Medium for fairness (017-06's retries).
* **Size.** M.
* **Frans.** think (017-06: whether `rw()` should ever give up).
* **Recommended:** the three Javadoc points now (S); fairness with 017-06.
* **Source.** 020-24-16; 017-06.

### 6.7. PA7. The heap a database holds, whatever its size

* **What.** Each started database holds about 11 MB of heap, the 10 MB
  write buffer allocated at the start, with no setting in the Pub API
  (U10-2, high by its finder); `memory()` keeps every state (U17-9).
* **Why.** 48 small databases fill a heap of 512 MB; a phone holds about
  20.
* **Risk.** Low.
* **Size.** S.
* **Recommended:** a buffer that grows with use (or a setting), and the
  cost per database in `DatabaseBuilder`'s Javadoc.
* **Source.** 020-24-10 (U10-2); 020-24-17 (U17-9); 006-17, section 6.3.

### 6.8. PA8. Space and reclaim made visible

* **What.** No way to see the stream's size or reclaim's progress
  (U18-4); `StartupInfo` has no `toString()` (U18-7).
* **Why.** With 2026.4's cleanup a user can at last watch space come
  back; today only the directory's files tell.
* **Risk.** Low.
* **Size.** S.
* **Frans.** decide (new API).
* **Recommended:** yes, with CL5.
* **Source.** 020-24-18.

### 6.9. PA9. Encryption done right

* **What.** Encryption left 2026.4's API (020-28): keystream reuse and no
  integrity (020-24-07, U7-1, U7-3). 017-10 holds the options.
* **Risk.** High (a format, keys, integrity).
* **Size.** L.
* **Frans.** think.
* **Recommended:** not in 2026.5.
* **Source.** 017-10; 020-28.


## 7. The Lean model and its proofs (LM)

Frans's rule: theory only where it de-risks.

### 7.1. LM1. A6 rather than A6'

* **What.** The model's theorems assume A6', a weakened "no adoption"
  (docs/sis-model.md, section 15.2). Since fault 12's fix,
  conformance.sh requires no adoption below the old parent in 005-04's
  a6 traces (023-08, Q9), and A6 itself may hold for the whole core.
* **Why.** A stronger assumption that Java meets would simplify the
  model and its proofs: a smaller model, as Frans wants.
* **Risk.** Low (the model only).
* **Size.** S to check (A2A3Check2 and the traces with A6); the proofs'
  simplification after, if it removes lines.
* **Depends on.** CL2 (merges were checked against A6' only).
* **Recommended:** the check, yes; the simplification if the check holds
  and it shortens the proofs.
* **Source.** 023-08, Q9 and section 7; docs/sis-model.md, 15.2.

### 7.2. LM2. `dirtyNodeBound`, the check before the go point

* **What.** The bound of the nodes a transaction may dirty, checked
  before the go point, is not proved (023-07, section 7). Its count
  was found wrong three times: P5's fault 8, B1 and B2 (023-11 b).
* **Why.** An undercount lets a transaction pass the check and then fail
  the database after the go point.
* **Risk.** Low.
* **Size.** S as a fuzz in the night (review A's `BoundReviewProbe`
  compared bound and count in 24,000 transactions: 023-11 a, section
  3); a proof would be L.
* **Recommended:** the fuzz as a night step (TT2), no proof.
* **Source.** 023-07, section 7; 023-11 a and b; 023-09, section 8.

### 7.3. LM3. 020-29's proof of the indexes

* **What.** A Lean proof of the indexes' safety and liveness, 5,231
  lines, on the branch `020-29-index-proof`, not merged (020's readme;
  006-17, section 6.3, point 7: "when?").
* **Risk.** Low; upkeep when the index layer changes (PA4, PA5).
* **Size.** S to merge.
* **Frans.** decide.
* **Options.** (a) Merge it into `lean/` as its own library. (b) Keep it
  on its branch as 020-29's evidence. **Recommended: (b)**: the index
  layer may change after PA5's study; the proof stays citable.
* **Source.** 020's readme (29-index-proof); 020-11, section 11.

### 7.4. LM4. 015-03, Lean's take

* **What.** Lean's `javaTake` and TakeCheck describe the take before
  005-79's integer rule; optional since 2026.2 ("Lean is a tool, not a
  release artifact", 016-01, D7).
* **Risk.** Low. **Size.** S.
* **Recommended:** close it, keeping lean/README.md's sentence; nothing
  fails, as the checker takes sp from the trace.
* **Source.** 015-03.

### 7.5. LM5. The larger proofs

* **What.** T4 (007, planned), the cost bounds of 017-04, T-SCHEME
  (reclaim's scheme, checked, not proved; 023-07, 5.5), P8's values
  argument (023-05 P8, section 8).
* **Size.** L. **Frans.** think.
* **Recommended:** not in 2026.5; none de-risks a change planned here.
* **Source.** 007's readme; 017-04; 023-07, 5.5.


## 8. Tests and tools (TT)

### 8.1. TT1. 023-03's tests as code

* **What.** 2026.4's cleanup is gated by probes kept in items
  (CleanupRule, CleanupRatchet), not by tests in `java/`. 023-07,
  section 6.2: `CleanupTester` (T1 at 1,000 and the fast checks C1 to
  C11) and `cleanup.sh` in `night.sh` (T1 to T4 at 100,000 and 1M);
  023-03, section 4.3: T5's applications' workloads (U16-1, U17-1,
  U18-1, U14-1, the FIFO) into `java/stress/` with counts, not times.
  Not on `023-core` (023-09, section 6).
* **Why.** Frans's rule "a deleted KV eventually costs nothing" has no
  guard in the code; any later change of the Core could break it.
* **Risk.** Low. `before-commit.sh` must stay fast: only what adds a few
  seconds joins it; the rest goes to `night.sh`.
* **Size.** M.
* **Recommended:** yes, first. It guards 2026.4 before anything is added.
* **Source.** 023-07, section 6.2; 023-09, section 6; 023-03, 4.3.

### 8.2. TT2. The fuzz and the long tests as steps

* **What.** UnlinkFuzz as a `level1.sh` or `night.sh` step; the ratchet
  test (023-10) and the reclaim liveness tests in `night.sh`;
  `testRuleBCounterexample` (P7) as a unit test; LM2's bound fuzz.
* **Why.** They found fault 12 and fault 13; today they run by hand.
* **Risk.** Low. **Size.** S.
* **Recommended:** yes.
* **Source.** 023-07, section 6.2; 023-09, section 6; 023-10, section 7.

### 8.3. TT3. A bug hunt on 2026.4

* **What.** A round of black-box applications on the 2026.4 jar, by
  new users who have only the jar and the documentation (006-20; the 18
  of 020-24), on workloads that delete and churn.
* **Why.** The method found most of 2026.4's bugs (006-20); 023's core
  changed the Core after the last round.
* **Risk.** Low. **Size.** M (machine and review time, little of
  Frans's).
* **Recommended:** yes, early: what it finds comes before new work.
* **Source.** 006-20; 020-24; 022-06.

### 8.4. TT4. The test gaps 2026.4 left

* **What.** Two unit tests wait without a timeout, so a failure hangs
  `unit.sh` (006-17, section 6.3, point 10); the JDK 17 test race's test
  fix (006-17, section 6); the harnesses' blind spots (17-B), coverage
  (13-cov), kill-restart on ext4 and power loss (15-gaps), slow f-tests
  (13-slow), one flaky eviction test (21-flake) (020-11, section 11).
* **Risk.** Low. **Size.** S each.
* **Recommended:** the hangs and the race first; the rest as todo
  entries.
* **Source.** 006-17, section 6; 020-11, section 11.

### 8.5. TT5. 015-18, `night.sh large` after 2026.2

* **What.** Open since 2026.2: run `night.sh large` on that release.
* **Risk.** Low. **Size.** S.
* **Recommended:** close it as overtaken: 2026.4's gates run `night.sh
  large` (023-08, section 5), and each release can do the same.
* **Source.** 015-18; 023-08, section 5.


## 9. Performance (PF)

Frans's order: 1M to 100M keys and the worst cases first.

### 9.1. PF1. 2026.4 measured at 10M to 100M keys

* **What.** On 2026.4's tag, on a quiet F53 and on s1: bytes a put,
  startup cold at a startup distance of 50 MB and more, scans after
  churn, reclaim's lag after a mass delete (T1 at 10M), the last touch's
  records with keys in time order, the underfill after scattered
  deletes, heap per KV (MEM) and after a mass delete; and 006-16's CORE
  across releases. 023's measurements stop at 1M keys.
* **Why.** It decides CL1, CL2, CL7, PF2, PF3 and PF4 by numbers, not by
  argument.
* **Risk.** Low (no code). **Size.** M (a day or two of machine time).
* **Recommended:** yes, first.
* **Source.** 023-08, section 5; 023-10; 006-19, section 7; 006-16.

### 9.2. PF2. Write amplification

* **What.** At 10M keys and 50 MB a put writes 867 bytes, 92 % index
  nodes. Levers with a format change: a compact key node encoding
  (about 35 to 40 % fewer index bytes, estimated) and delta writes of
  key nodes (two to three times fewer, estimated, with chains to read).
* **Why.** Large databases; disk and SSD wear.
* **Risk.** Medium (a format change, Frans approves; 018-01).
* **Size.** M for the probe (006-19's M1), L for the change.
* **Frans.** think (the format).
* **Depends on.** Q2.
* **Recommended:** the probe M1 in 2026.5; the change, if any, later.
* **Source.** 006-19, sections 1, 6 to 8.

### 9.3. PF3. Reclaim reads a value only when it must

* **What.** A reclaim step reads each live KV's value, also when it is
  at pCut or later and needs no rewrite; `Kvt.spos` gives the value's
  position before it is read (023-05 P8, section 8: "halve the step's
  reads").
* **Why.** Fewer loads when the data is larger than memory.
* **Risk.** Low to medium: reclaim's step, no stream change expected.
* **Size.** S.
* **Depends on.** PA2 (the same path); whether it applies to today's
  step as to P8's (to check).
* **Recommended:** yes, after PF1.
* **Source.** 023-05 P8, sections 7 and 8; 023-07, section 5.5.

### 9.4. PF4. Long keys: the still-dirty loop

* **What.** The writer's still-dirty loop is quadratic for long keys: a
  4 MB put next to 1 MB keys with a shared prefix took 29 to 48 s
  (16-Q1; 021-16, Q1).
* **Risk.** Medium (Rule A). **Size.** M.
* **Recommended:** later, unless PF1 or a user meets it.
* **Source.** 020-11, section 11; 021-16.

### 9.5. PF5. 015-84, the pace's factor after a decrease

* **What.** After the startup distance is lowered, the catch-up's records
  reach 13 to 15 MB at 50M keys (007-07, section 11).
* **Risk.** Low. **Size.** S.
* **Recommended:** later; a decrease is rare.
* **Source.** 015-84.

### 9.6. PF6. Reader scaling

* **What.** Every read enters `BufferedStream`'s monitor; a read wholly
  in the file could skip it (017-07, section 5). Measure first.
* **Risk.** Medium (a core storage class). **Size.** M.
* **Recommended:** the measurement only, if theme B has room.
* **Source.** 017-07, section 5; 015-86.

### 9.7. PF7. C-M8, the cost of a write at an object key

* **What.** A `w()` of a `String` put at an object key costs 2.6 µs
  against 2.3, accepted (020-11, section 1).
* **Recommended:** no; 017-09 (PA5) removes the coupling it pays for.
* **Size.** S. **Risk.** Low.
* **Source.** 020-11, section 1; 017-09.


## 10. The C clone (CC)

### 10.1. CC1. C at 2026.4

* **What.** C is at 2026.4's candidate `03ce6ec5`, before 023. After the
  tag: the diff to `release-2026.4` (023's core, a little under 023-07's
  estimate of 500 lines, which counted P8's step; 023-07, section 6.4),
  the cross tests with a new pin, and
  the long runs (`runs-2026-4.sh`); then 022-01 and 022-02 close.
* **Why.** C found real faults of Java (021-11, 021-14, 021-15, 021-25,
  021-27 among them).
* **Risk.** Low. **Size.** M (its own session, 022).
* **Recommended:** yes, first, beside TT1.
* **Source.** 022's readme and log; 023-07, section 6.4.

### 10.2. CC2. C follows 2026.5

* **What.** Frans: at least 2026.3 and 2026.4, "maybe longer" (022's
  readme). Each change of the stream's bytes in 2026.5 (CA1, CL7, CL1)
  costs C a follow-up and a new pin.
* **Size.** S to M. **Frans.** decide.
* **Recommended:** yes; batch 2026.5's byte changes so that C follows
  once.
* **Source.** 022's readme; 015-40.

### 10.3. CC3. C's own open points

* **What.** 022's list for Frans: D7, `GetN(0)`, `bergdb_close` after a
  failure, the memory stream that frees cut bytes, a read-only open, a
  buffer-size option, a close with an error text, the NOMEM refusal,
  015-67's bounded sweep, a limits harness (022's log, 2026-11-09,
  19:30, point 4).
* **Size.** S. **Frans.** decide.
* **Recommended:** one sitting, the defaults that went ahead confirmed.
* **Source.** 022's log.

### 10.4. CC4. Bindings on C

* **What.** C on Linux as the base of bindings, then Rust and Python
  (006-18); the licence decides the reach.
* **Size.** L. **Frans.** think (017-01).
* **Recommended:** not in 2026.5.
* **Source.** 006-18; 017-01.


## 11. Other (OT)

### 11.1. OT1. A lost or cut last stream file; a full disk

* **What.** A start cannot tell a lost or cut last stream file from a
  crash's torn tail, so synced records go silently (U8-1, C-U2-6);
  options (a) the stream's length kept outside it at a clean close, (b)
  `StartupInfo` gives the end and whether a tail was cut, (c) a clean
  stop's record in the stream (a format change). After a full disk the
  torn record's size must be free (C-U2-2; 014-01). Checksums in the
  stream (017-08).
* **Risk.** Medium (the stream's contract, 014).
* **Size.** M. **Frans.** think.
* **Recommended:** (b) in 2026.5 (new API, no format); the rest with 014.
* **Source.** 020-24-08, section 4; 020-11, section 11; 014-01; 017-08.

### 11.2. OT2. The `unlockDir()` race on Linux

* **What.** `FileStream.unlockDir()` closes the lock file before it
  removes the directory from its locked set; a new database in a new
  directory can, rarely, be refused as in use (10 in 30,000 tests on JDK
  17, on s1). A product fix idea is ready (006-17, section 6).
* **Risk.** Low. **Size.** S.
* **Recommended:** yes, a todo entry.
* **Source.** 006-17, section 6.

### 11.3. OT3. `SecureDirectoryStream`

* **What.** It would close 021-24's remaining window between the check
  and the step.
* **Risk.** Low. **Size.** S.
* **Recommended:** later.
* **Source.** 021-24; 020-11, section 11.

### 11.4. OT4. The startup distance in an internal KV

* **What.** Out of the meta block, which is for what cannot be stored
  otherwise (Frans, 2026-11-05); a format change (017-07, section 2).
* **Size.** S. **Frans.** decide.
* **Recommended:** only with another format change.
* **Source.** 017-07, section 2.

### 11.5. OT5. A clear place for the database's design

* **What.** One place, citable by ID, for the design spread over
  docs/levels.md, sis-model.md, 010-01, the Javadoc and design subitems
  (017-07, section 4).
* **Why.** Simplicity: 023's work read the design from six places.
* **Size.** S. **Frans.** decide (the place).
* **Recommended:** yes, small.
* **Source.** 017-07, section 4.

### 11.6. OT6. The long-term topics

* **What.** 017-01 (publication, money), 017-02 (a paper), 017-03
  (replication), 017-05 (block storage), 017-06 (overload).
* **Size.** L. **Frans.** think.
* **Recommended:** none in 2026.5.
* **Source.** 017's readme.


## 12. Dependencies and conflicts

* **PF1 first.** It decides CL1, CL2 and CL4, CL7, PF2, PF3, PF4.
* **TT1 before new Core mechanisms.** The tests as code guard 2026.4's
  cleanup; any CL change after it is checked by them.
* **CL1 and CL3.** P8 removes the window's trigger in T1; doing both is
  redundant.
* **CL1 and CL5.** `maintain()` drives whichever step exists; with P8 an
  iteration it starts must store E (023-07, 5.13).
* **CL2 and CL4.** RB does both; MG only the shape. One way to strict.
* **CL5's full promise** needs CL2, CL4 and CL6.
* **CL7 and CL8.** TE and the last touch are one mechanism, changed
  once.
* **CL2, CL4, PF2, OT4 and Q2.** Each changes the record format or the
  rerun, so each meets the question whether 2026.5 opens 2026.4's
  databases.
* **Every change of the stream's bytes** (CA1, CL1, CL7, CL2, PF2) needs
  new StreamDigest digests and a C follow-up (CC2): batch them.
* **CC1 before CA1's C part.**
* **PA2 and PF3** read KVs without values: one Core path.
* **PA5, PF7 and LM3.** 017-09's objects-only keys remove C-M8's
  coupling; a change of the index layer costs 020-29's proof upkeep if
  merged.
* **LM1 and CL2.** P5 was checked against A6' only.
* **TT3 and everything.** A bug it finds comes before new work, as in
  2026.4.


## 13. Summary table

| ID  | Candidate                              | Size | Risk     | Frans  | Recommended          |
|---|---|---|---|---|---|
| CL1 | P8, each step scans at its own time    | M    | med-high | -      | only if PF1 asks     |
| CL2 | Strict: merges or RB                   | L    | high     | think  | not in 2026.5        |
| CL3 | Fix (a) of the top-node window         | M    | medium   | -      | drop                 |
| CL4 | Dead klongs in live nodes              | M    | med-high | think  | keep the allowance   |
| CL5 | `maintain()`                           | S    | low-med  | decide | yes, bounded promise |
| CL6 | The cache's tables at peak             | S    | low      | -      | yes                  |
| CL7 | The last touch of an iteration         | M    | medium   | -      | yes, after PF1       |
| CL8 | Close 021-25; TE with CL7              | S    | low      | -      | yes                  |
| CA1 | Builder: the last operation wins       | S    | low      | -      | yes, early, with C   |
| CA2 | `getTrans` inside a record (021-27)    | S    | low      | decide | option A             |
| CA3 | Core writes to internal keys           | S    | low      | -      | refuse them          |
| CA4 | Publish the Core API's Javadoc         | S    | low      | decide | yes, status first    |
| CA5 | Exceptions outside the API             | S    | low      | -      | yes                  |
| PA1 | Scans in `rw()`                        | L    | high     | think  | study, theme D only  |
| PA2 | Keys only, count, limit                | M    | low      | decide | yes, with PF3        |
| PA3 | Index and directory listings           | M    | low      | decide | listings only        |
| PA4 | Index jobs' robustness                 | M    | medium   | -      | 18-O1, 29-fair       |
| PA5 | Objects, what a key holds              | L    | medium   | think  | study only           |
| PA6 | `rw()` under contention                | M    | medium   | think  | Javadoc now          |
| PA7 | 11 MB of heap per database             | S    | low      | -      | yes                  |
| PA8 | Space and reclaim made visible         | S    | low      | decide | yes, with CL5        |
| PA9 | Encryption done right                  | L    | high     | think  | not in 2026.5        |
| LM1 | A6 rather than A6'                     | S    | low      | -      | check, then simplify |
| LM2 | `dirtyNodeBound` checked by a fuzz     | S    | low      | -      | fuzz, no proof       |
| LM3 | 020-29's index proof                   | S    | low      | decide | keep on its branch   |
| LM4 | 015-03, Lean's take                    | S    | low      | -      | close                |
| LM5 | T4, T-SCHEME, the larger proofs        | L    | low      | think  | not in 2026.5        |
| TT1 | 023-03's tests as code                 | M    | low      | -      | yes, first           |
| TT2 | Fuzz and long tests as steps           | S    | low      | -      | yes                  |
| TT3 | A bug hunt on 2026.4                   | M    | low      | -      | yes, early           |
| TT4 | 2026.4's test gaps, two hangs          | S    | low      | -      | hangs first          |
| TT5 | 015-18, `night.sh large`               | S    | low      | -      | close                |
| PF1 | 2026.4 at 10M to 100M keys             | M    | low      | -      | yes, first           |
| PF2 | Write amplification                    | M    | medium   | think  | the probe only       |
| PF3 | Reclaim reads values only when needed  | S    | low-med  | -      | yes, after PF1       |
| PF4 | Long keys' still-dirty loop            | M    | medium   | -      | later                |
| PF5 | 015-84, the pace after a decrease      | S    | low      | -      | later                |
| PF6 | Reader scaling                         | M    | medium   | -      | measure only         |
| PF7 | C-M8's lock                            | S    | low      | -      | no                   |
| CC1 | C at 2026.4                            | M    | low      | -      | yes, first           |
| CC2 | C follows 2026.5                       | S    | low      | decide | yes, batched         |
| CC3 | C's own open points                    | S    | low      | decide | one sitting          |
| CC4 | Bindings on C                          | L    | -        | think  | not in 2026.5        |
| OT1 | A lost tail file, a full disk          | M    | medium   | think  | (b) only             |
| OT2 | The `unlockDir()` race                 | S    | low      | -      | yes                  |
| OT3 | `SecureDirectoryStream`                | S    | low      | -      | later                |
| OT4 | Startup distance in a KV               | S    | low      | decide | with a format change |
| OT5 | A place for the design                 | S    | low      | decide | yes                  |
| OT6 | The long-term topics of 017            | L    | -        | think  | none                 |


## 14. Possible themes

Each theme includes what it names and leaves out the rest. All four
share a base, (A)'s list, because a bug-free 2026.4 is to stay so.

* **(A) Consolidate 2026.4.** No new mechanism in the Core: TT1 to TT5
  (TT3's bug hunt first), CA1 with C (CC1, CC2), CA2, CA3, CA5, CL6,
  CL8, LM1, LM2, LM4, OT2 and PA7. It leaves out every CL mechanism (CL1
  to CL5, CL7), new Pub API features and any format change.
* **(B) Large databases, measured, on a calm Core.** (A), and PF1 first;
  then CL7 (the last touch), PF3, CL5 with PA8 (`maintain()` and the
  space made visible), PA2, PF2's probe and PF6's measurement, with CL1
  and PF4 only if PF1's numbers ask for them. It leaves out strict (CL2,
  CL4), CL3, PA1, PA5's API change, PA9 and every format change.
* **(C) Strict cleanup.** (A), and the rest of 023's full set: CL1, CL2
  (MG or RB), CL4, CL5 with its full promise, LM1 again after merges.
  It leaves out the performance work but PF1, and new Pub API, and it
  needs Q2 answered first, as it changes the rerun.
* **(D) The Pub API for applications.** (A), and PA1 (scans in `rw()`),
  PA2, PA3's listings, PA4, PA6, PA8 and PA5's study. It leaves out the
  Core's mechanisms, and it needs Frans's design time.

**Recommended: (B).** Frans's order is a working, performant database
first, large databases first, and simplicity: (B) adds to the Core only
what a measurement at 10M keys and more asks for: CL7, the latency fault
at scale of 023's list, and PF3, which changes no stream byte. (C)
puts the Core's most intricate code and a format question right after a
baseline that Frans wanted simple; (D) needs his design time and changes
the API that 2026.4 has just made a stable baseline (O16-1).


## 15. Questions for Frans, in order

1. **The theme** (section 14). Recommended: (B).
2. **Does 2026.5 open 2026.4's databases?** Recommended: yes. 2026.4 is
   the first release meant as a stable baseline (O16-1; 2026.4 itself
   refuses earlier ones, 023-02, F9). Then a change of the record format
   or the rerun in 2026.5 must read format 6 beside the new one, or wait;
   under (B) none is planned (CL2, CL4, PF2, OT4 wait).
3. **Measure first** (PF1) on 2026.4's tag, before CL1, CL7, PF3 and
   PF4 start? Recommended: yes; a day or two of machine time on a quiet
   F53 and on s1.
4. **Strict and the window**: CL3 dropped (023-08, Q6's condition not
   met), CL2 and CL4 after PF1's numbers of underfill? Recommended: yes.
5. **`maintain()` in 2026.5**, promising the bounded allowance only
   (CL5), with the space made visible (PA8)? Recommended: yes.
6. **The C clone**: CC1 first, then 2026.5's changes of bytes batched
   (CC2)? Recommended: yes.
7. **The small decisions**, each as recommended: CA2 option A; CA4
   publish the Core API's Javadoc; LM3 keep 020-29 on its branch; LM4
   and TT5 closed; CC3 in one sitting.
8. **The Pub API**: which of PA2, PA3's listings, PA7 and PA8 as small
   API additions, and when the study of what a key holds (PA5, 017-09)
   starts. Recommended: PA2, PA7, PA8 in 2026.5; PA5's study when Frans
   has the time.


## 16. Log

2026-11-10. Written at Frans's request (19:24 to 19:26), read only at
`main` `329d78f3` and `023-core` `b7874541`. Nothing decided.

2026-11-13. Status set after the release (coord-1113).
