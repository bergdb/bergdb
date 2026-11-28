028-75. Decide: one small put, then maintain() calls rewrite the whole live data
==============================================================================

Status: decided (2026-11-28): (c); designed (2026-11-28): (c) needs a
change of the record format, Frans's (options (c1) to (c3) and (c0)
below, (c1) recommended); not built. Kind: Decide. Frans: to decide
the format change.
Created 2026-11-27 by Frans Lundberg.

What: `Reclaim.passDue` (`Reclaim.java`, M1 of `planPart`) begins a
pass when no iteration runs or waits for its cut and the stream kept
holds a record of the application's (`appA` at or after the first
available position). A pass that a call begins cuts at its own start:
it rewrites every live value stored before it. That is 031-04's design
("no drain, no MIN_RELEASE"), which came to `main` with A2 (Frans,
2026-11-27, 14:36: `maintain(int budget)` replaces `maintain()`) and
031-06's merge (`5b88cc80`). Until that merge a call began an iteration
only if its cut released 400 kB (028-51, 028-62).

So one put of a byte, followed by `maintain(budget)` calls, rewrites the
whole live data. Measured by the independent review of 031-06's landed
diff (2026-11-27, `review-main.md`, R4), with
`review-main-probes/RmPassProbe.java` (`runs/pass.txt`), at the
release's limits: a database brought to rest by calls, one put of 1
byte, calls until five in a row write nothing; three rounds each.

* 20,000 keys of 100 bytes (about 2.3 MB live): the put's record 568 to
  624 bytes; the calls then wrote 4.40 to 4.43 MB; the stream kept 4.36
  MB before and 4.35 to 4.38 MB after.
* 100,000 keys of 200 bytes (about 21.6 MB live): a record of 576 to 648
  bytes; 31.9 MB written; the stream kept 32.0 MB before and 31.6 to
  31.7 MB after.

An application that writes a little and calls `maintain(budget)` when
idle rewrites its live data about once a retain duration: the calls go
quiet once the pass is cut, and the next small write begins the next
pass. At 100 GB of live data that is 100 GB written for each such write
that comes after the last pass was cut.

Why: the cost of a decided rule, not a fault of one record an action
(031-06): the calls end by construction (RB-007 and RB-006's rest fixed,
033), at the price of a full rewrite for any write. BergDB is optimized
for large databases first (1M to 100M keys); a rewrite of everything
for a byte is the worst case of write amplification. It belongs to the
landing's step 3, the pace (031-06, section 9).

Frans: decided, (c) (2026-11-28). The rule is part of 031-04's design
that A2 took; a
change of when a call begins a pass changes what `maintain(budget)`
promises. The options:

* **(a) Keep the rule.** No change. The calls end by construction, with
  no threshold to tune and none of the cases of RB-006 and RB-007; an
  application that writes a little between idle calls pays a rewrite of
  its live data each retain duration. State it in `maintain(budget)`'s
  Javadoc and in 027-13.
* **(b) A threshold of released bytes again.** A call begins a pass only
  if the bytes its cut would release are at least a fixed amount, 400 kB
  as before the merge. The bytes a cut releases are not known before the
  pass's scan; an estimate (the stream kept less the live bytes of the
  last scan) brings back a judgment of when there is work, which is what
  031-04 removed. RB-006 and RB-007 came from such judgments: with a
  fixed threshold, an emptied database again keeps up to the threshold,
  and the cases at its edge (two stretches, an iteration within 400 kB of
  its cut point) need their own care and probes.
* **(c) A pass when the stream kept is a share over the live data.** A
  call begins a pass only if the stream kept is more than k times the
  live bytes (for example k = 1.5) and more than a floor in bytes over
  them (for example 400 kB): both. The live bytes must be those of the
  stream kept, not a stale count: the last scan's sum with the
  application's writes and deletes since, kept by each record (a count
  from before an emptying would leave RB-007's case), so the decision is
  a function of the stream (P2). A small put leaves the share near 1: no
  pass. An emptied database (RB-007's case) has a large share: a pass,
  and the calls end within the floor of a fresh database's stream, as
  now. The cost of a write is then bounded by k: the stream kept grows
  to about k times the live data before the calls rewrite it. To be
  designed in step 3 and checked with RB-006, RB-007 and RB-010's probes
  (033's `probes/`), 031-04's cases and `RmPassProbe`.
* **(d) A pass that cuts at the iteration before's start**, as a
  commit's iterations do (pCut the pStart of the iteration before): a
  call's pass then rewrites only what the last pass left. Brings back
  the iteration that waits for its cut, RB-007's cause; not recommended.

Recommendation: (c): it bounds the cost of a small write by the share,
keeps the calls' end by construction for an emptied database, and keeps
the decision a function of the stream. Its k and floor are measured in
step 3.

Decision: Frans, 2026-11-28, 07:27: (c). The landing's step 3 is on
`main` since 2026-11-28 without it: the rule is designed and measured
as work of its own, on `main` after it.

Done when: Frans has chosen; for (b) or (c), the rule built on `main`
(written before the decision: in the landing's step 3), with the probes above and `RmPassProbe`
showing a small write's cost, and `before-commit.sh`, the level scripts
and the item's sweep green; for (a), the Javadoc and 027-13 say the cost.

First step: Frans's choice among (c1), (c2), (c3) and (c0) (section 5
of the design below); then the build, on a branch, with the gates
named in "Done when".


Design of (c) (2026-11-28)
--------------------------

The design needs a change of the record format, which is Frans's:
nothing is built. A prototype of the rule on `main` at 16c64d9a
(`probes/prototype.diff`, a switch for each variant; `probes/run.sh`)
and the probes `probes/LiveProbe.java` and `probes/PassRoundsProbe.java`
(031-06's RmPassProbe with rounds and the startup distance) measured
each variant; the figures are in `runs/`, bytes only.

### 1. The rule and its terms

* S, the stream kept: L0 less the first available position, at the
  state before the record.
* V, the live bytes: the stream bytes of the state at L0, its value
  nodes and its key nodes, each at the size it has when written. A
  pass that cuts at its own start rewrites about V, and the stream
  kept comes down to 1.07 to 1.54 times V after its cut (section 6).
* M1 begins a pass when passDue holds as now (no iteration runs or
  waits for its cut, the stream kept holds a record of the
  application's) and S > k V and S - V > F, F the floor. The calls
  still end by construction: after a pass's cut the stream kept holds
  no record of the application's until it writes again.

### 2. The live bytes are not in the stream

* A key node's klongs name value nodes by position, not by size
  (027-03, section 11.2); no index node holds a count or a size of what
  is below it.
* The table's rows hold the last scan's figures only: rewritten (the
  steps' copies and their index charge) and kvCount (the KVs met). A
  commit's iteration, whose pCut is the pStart of the one before,
  rewrites only the values stored before its pCut.
* A start reads the meta block, the startup section and the last
  record (007): a sum over the records since the last scan, often far
  more than the startup section, is not rebuilt, and a sum in memory
  only would make a restart change the stream (P2).
* So live bytes that each record keeps up to date, with the
  application's writes and deletes since the last scan (the text of
  (c)), need a value that every record carries: a change of the
  record format.

### 3. Without a format change: measured, not enough

The prototype's rule 'rows' (`runs/rows.txt`) takes V from the
table's last done row: rewritten for a pass (pCut = pStart), pSafe -
pCut for a commit's iteration; and the exact live bytes when a scan of
at most F bytes of KVs at L0 reaches the end (an emptied database);
k = 1.5, F = 400 kB.

* The small put: after it the calls wrote 50,584 bytes once, then 0
  (20,000 keys of 100 bytes), and one commit's iteration of 5.5 MB,
  then 0 with B1 (100,000 keys of 200 bytes; section 4).
* The emptied databases: as section 6 gives them.
* With commits' iterations (100,000 keys of 200 bytes, startup
  distance 1 MB), pSafe - pCut holds the iteration's garbage, about the
  stream kept itself, so the calls begin no pass: 82.7 MB kept after
  random overwrites of every key (`main`: 32.7 MB), 58.2 MB after the
  deletes of 90 % of the keys, 2.5 MB of them live (`main`: 3.2 MB).

A count in place of sizes (rule 'counts', `runs/counts.txt`): the
value nodes in the stream kept against the KVs live, two counts that
each record would carry (kept in memory by the prototype: a format
change too). It sees the deletes (3.2 MB kept after the 90 %), not the
garbage of key nodes that random overwrites of small values make:
82.7 MB kept at 100,000 keys of 200 bytes (27.2 MB live in the stream,
`runs/exact.txt`), 101.0 MB at 200,000 keys of 20 bytes (18.2 MB live;
`main`: 32.7 and 26.3 MB).

### 4. A second cause: a commit's iteration that the calls complete

* A commit begins an iteration (B, `planCommit`) when the stream has
  grown by twice the startup distance since the last pStart and a
  quarter of the retain duration has passed. The calls take its steps
  at MAX_STEP_SIZE, without the commit's allowance (M2). Its pCut is
  the pStart of the iteration before, so it rewrites the values stored
  before that: in a database that the application leaves alone, about
  all of them, the copies of the iteration two before it among them.
* With a rule that begins no pass, each put of a byte a second apart
  then begins such an iteration, and the calls complete it: 5.5 MB and
  27 MB written by turns, for good, at 100,000 keys of 200 bytes and a
  startup distance of 1 MB (`runs/rows.txt`, B1 off; the copies of each
  iteration are the growth that the next B counts); 18.5 MB after
  overwrites of 2 MB at 20,000 keys of 1 kB (B1 on). On `main`, M1's
  pass after each put cuts at its own start, at 31.9 MB a put.
* B1, the smaller fix: B counts the application's growth only, L0 -
  lastPStart less the last row's rewritten. The chain stops (5.5 MB
  after the first put, the fill's growth, then 0), but a commit's
  iteration that the application's writes begin is still completed by
  the calls at full speed.
* M2', the fix of the design: the calls step a commit's iteration
  within its allowance only (the commits' own: the internal fraction of
  the stream's growth since its pStart, less its rewritten), and M1 may
  begin a pass while such an iteration runs, which the pass's cut then
  drops with the rows before it. With the exact V and M2' (B1 off), the
  calls wrote 0 bytes after each small put at every size measured
  (`runs/exact-paced.txt`). M2' changes no format; to check in the
  build: the table's rows (a running commit's row before the pass's),
  the trace checker's C-STEP (027-02) and the contract checkers' model
  of the steps (`lean/contract`, ReclaimSteps).

### 5. The options (Frans's: a change of the stream format)

* **(c1) The live bytes in each record, exact.** Record format 10: an
  i64 in the header after topPos, V after the record. The writer adds
  the size of each node it makes and subtracts the size of each it
  replaces or drops: the key nodes' from memory (PeWriter changes them
  and has their klong counts), a value's that a put replaces or a
  delete removes from its node if in memory, else from its node's size
  field in the stream, at the position its leaf names: a read of 4
  bytes for each replaced or deleted value not in memory, before the
  write lock (as 031-06's warm-up reads) or under it. Costs: 8 bytes a
  record (an empty record 48 to 56 bytes; RmPassProbe's put of a byte,
  568 to 648 bytes, 8 more); a start reads the field off the last
  record's header, which it reads now; the code: StoredTrans (the
  header, the empty record), the writer's sums (Db, PeWriter),
  DbStarter, Reclaim (the rule, M2'), 027-03 (sections 8.1 and 8.2),
  027-13, the Javadoc of maintain(int budget), the tests and the
  digests (every record changes); a stream of format 9, which no
  release has, refused. Simulated by the rule 'exact' (V by a full
  scan at each decision; `runs/exact.txt`, `runs/exact-paced.txt`).
* **(c2) As (c1), without the reads.** A value that a put replaces is
  counted at the put's value size, a deleted one at the mean live
  value size, from a second field, the count of live KVs (16 bytes a
  record). Exact for values of one size; it drifts, without a bound,
  where a key's value changes size. Not simulated.
* **(c3) Counts only.** The value nodes written and the KVs live, 16
  bytes a record, no reads: blind to the key nodes' garbage (section
  3).
* **(c0) No format change**, the rule 'rows' with B1: the calls begin
  no pass in a database whose commits run iterations (section 3).

Recommendation: (c1) with M2', k = 2 and F = 400 kB; (c2) if the
reads are not wanted.

### 6. k and the floor

* k: after a pass, the stream kept is 1.07 to 1.54 times V where V is
  above 1 MB (`runs/exact.txt`, `runs/exact-paced.txt`, startup
  distance 1 MB: 1.24 to 1.34 at 20,000 keys of 100 bytes, 1.38 at a
  startup distance of 50 MB, 1.07 to 1.19 at 20,000 keys of 1 kB, 1.17
  to 1.24 at 100,000 keys of 200 bytes, 1.40 to 1.54 at 200,000 keys of
  20 bytes). At k = 1.5 a database of small values is over the
  threshold after its own pass (1.51 and 1.54), so that its next small
  put would begin another; k = 2 leaves room. A pass rewrites about V
  when S reaches k V, so the calls write about 1/(k - 1) bytes for each
  byte of garbage they give back: 1 at k = 2, 2 at k = 1.5. The stream
  kept stays below about k V and the writes of a retain duration; at
  k = 2, 100,000 keys of 200 bytes keep 44.5 MB after their fill
  (`main`: 31.9 MB after a pass; `runs/exact-paced.txt`).
* F = 400 kB, two meta block distances: an emptied database keeps at
  most V + F, within 400 kB of a fresh one's as the Javadoc of the
  Pub's Database.maintain() says, and G5 allows twice the twin's and
  600 kB. Below about 1 MB of live data F decides, not k (after a pass
  the stream kept is up to 13 times V at 16 kB live). Measured, the
  same with 'rows', 'exact' and M2': HoleProbe (RB-007) with 4,000
  and 20,000 keys kept 208,584 bytes, its twin 29,000 (`main`: 71,368
  and 52,664), with 20,000 and 20,000 152,272 and 113,608 (`main`:
  125,976 and 113,512); TwoStretchProbe (RB-006) 18,000 bytes over a
  fresh database in its first case (`main`: 18,192), in its case
  'after' 16,160 with 'rows' and 'exact', 22,352 with M2' (`main`:
  16,216).

### 7. RB-006, RB-007, G5 and the tests

* With V exact, an emptied database has V near 0: a pass once S - V
  is over F, and the calls end by construction, as now. RB-007's case
  does not come back: the writes and deletes while an iteration runs
  or waits for its cut are garbage, not live bytes, and a pass comes
  once they are over the share and the floor. Nor RB-006's: there are
  no stretches, and the rule asks nothing of the cut point. G5's bound
  holds within its allowance (to run in the build: count-gates.sh g5).
* A database without garbage is quiet from the start: with 'exact', 4
  of the 56 reclaim unit tests failed, each one that expects a call to
  begin a pass on such a database (Reclaim.Tester's
  testMaintainBeginsWithEndKey, ReclaimMaintainTester's
  testLiveDatabaseQuiet, its first cut, ReclaimRoomTester's
  testTakeWithinTheSetRoom, and the check of stopped databases after
  the first); the build gives them garbage first.
* The new unit test: RmPassProbe's case by counts, the bytes that the
  calls write after a put of a byte into a database at rest, at most a
  few kB, failing on `main`.


Log
---

2026-11-27. Registered by lead-1127, from the review of 031-06's landed
diff (R4).

2026-11-28. Frans decided (c) (07:27). Not designed or built yet.

2026-11-28. Designed (section "Design of (c)"): (c) needs a change of
the record format, Frans's; options (c1) to (c3) and (c0), (c1)
recommended with M2', k = 2 and F = 400 kB; measured with a prototype
and the probes in `probes/`, the figures in `runs/`. The entry moved
from a file into this directory. Not built.
