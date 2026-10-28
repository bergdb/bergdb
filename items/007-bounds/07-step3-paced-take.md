007-07. Step 3 as a patch: the paced take with the deadline
===========================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code) for Frans Lundberg
(006-09, W10), at his choice (17:27): "007-03 step 3 as a patch". Status:
done. Frans decided on 2026-10-28 to apply the patch and to add D4:B as
007-06 measured it; both went into the code that day, gated, with
007-06's step-2 runs again on them (section 10). Sections 1 to 9 are the
patch as it was written for his review on 2026-10-27.

The patch: [07-step3-paced-take/step3.diff](07-step3-paced-take/step3.diff),
`git diff` against main's `2eaaa45`; it applies cleanly there. The same
change is one local commit, `2506e1c`, in the clone
`/Users/f/fl/bench/006-09/w10/repo/`, not pushed.


## 1. What changed

`TransSeq.take` is 005-49's paced take
([report](../005-todo/49-smooth-index-writes/report.md), section 6), with
the deadline of 007-03's step 3 as its backstop:

* A record takes its share of D, the got-dirty nodes of the section's
  transactions: share = D × (o / O) × (S / sd), with o the record's own
  bytes, O those of the section's records, S the section's length and sd
  the startup distance's setting. Whole transactions, oldest first; the
  next one, of which only a part fits, is taken if that part is larger
  than a number in [0, 1) hashed from the stream's length.
* The deadline: a transaction that begins d_h = 2 × sd or more before the
  end is taken whatever the share; `hardSp` is computed in a long
  (`2L * startupDistance`).
* The node limit (`nodeCountLimit`) and the minimum of two transactions
  go, and with them the comment's "TODO D." of 2015 and its claim that
  the startup pos "should never fall exceedingly behind" (007-03, step 3).
* `TransInfo.ownBytes`: the record's value nodes and 48 bytes
  (`TransSeq.ownBytes`). `Db.store` computes it, and uses it for the
  record limit's fixed bytes too, which were the same sum; `DbStarter`
  computes it from the record at a start.
* `TransSeq` keeps the sums D and O; its checksum covers both and each
  transaction's own bytes, so RestartInvariance compares them with and
  without restarts.
* `Db.setStartupDistance`'s Javadoc says what a decrease now does
  (section 7.3), in Frans's terms: the setting is the target size of the
  startup section, the actual startup distance is such that the stream's
  length minus it is the position a start reads from.
* docs/levels.md, section 5, and README.md's known limits: the take as it
  is now; the write overhead to measure again.

No new setting (P10); no time, thread or format change. The take reads
only what a start rebuilds, so the stream does not depend on restarts (P2;
StreamDigest, section 5).


## 2. Against 005-49's prototype

The prototype ([paced-take.diff](../005-todo/49-smooth-index-writes/paced-take.diff))
was reviewed, not copied:

1. **The hash was biased.** The prototype's `((pos * 0x9E37...) >>> 11)`
   is a product with a constant only, so a step of the stream's length is
   a fixed step of the number, mod 1. What a record takes changes its
   length, so the next number depends on the last decision, and records
   took more than their share when their sizes are regular. With
   transactions of one put of 1 kB, 2,000 keys: 0.98 nodes a commit
   against a share of 0.85 at sd 800 kB (section held at 0.87 sd), and
   0.65 against 0.50 at 2 MB (0.77 sd). The patch hashes with SplitMix64's
   finalizer: 0.92 against 0.92 and 0.54 against 0.54, sections at 1.001
   and 1.006 sd. In 005-49's runs, 1,000 puts a transaction, the section
   held at 1.00 sd, probably because the record sizes vary too much there
   for the bias to show.
   `TransSeq.testShare` checks the mean with record lengths that depend on
   what is taken: 2.50 transactions against a share of 2.5 (2.85 with the
   old hash).
2. No guard for O = 0 and no `Math.max(1, sd)`: every record has 48 own
   bytes, so O > 0 when D has a transaction (an assert says so), and sd is
   at least 10.
3. One `take` method; the overload without a byte limit went, as only
   tests used it.
4. The rounding keeps the prototype's two conditions: a transaction with
   no got-dirty nodes is taken free while the share is not used up, so a
   section of transactions with nothing dirty does not wait for the
   deadline.


## 3. The tests

In `TransSeq` (synthetic transactions):

* `testShare`: the share, the next transaction by the hash, and the mean
  share under feedback (2.1).
* `testDeadline`: transactions that begin d_h or more before the end are
  taken whatever the share (the one exactly d_h before too); the one
  younger waits.
* `testDecrease`: sd 100000 lowered to 25000. The record at the decrease
  takes the 25 transactions past the new d_h (250 nodes); the next records
  take what each record before moved past it (130, 70 and 40 nodes), then
  each its share and at most one transaction more; after 100 records the
  section is 25000 (the test allows 20 percent).
* `testSumsAfterTake`: after a take, D, O and the checksum are those of a
  TransSeq built from the transactions left, as a start builds it.
* `testTake1`, `testTake2`, `testTakeWithBudget`: as before, by the
  deadline; `testNodeCountLimit` went with the node limit.

In `DbTester` (a real database, in memory):

* `testPaceHoldsTheStartupSection`: 6,000 single puts on 2,000 keys at sd
  10 kB. After every commit no transaction but the last began 2 × sd or
  more before the stream's length before the record; the mean section is
  1.004 sd, the largest record 3.6 times the mean. Today's take: mean 1.30
  sd, transactions past 2 sd after 57 records, records up to 6.7 times the
  mean.
* `testDecreaseOfStartupDistance`: 1 MB lowered to 400 kB (the least
  `setStartupDistance` takes), the section at 1.04 MB, 1 kB values. The
  call leaves nothing past the new d_h; the section is 1.82 × the new
  setting just after (the dummy's own 236 kB record is in it), below 1.25
  after 294 commits, and at most 1.18 from the 300th on; the first 300
  records are 1.03 times those before. With today's take it went back to
  1.6.


## 4. The gates

In the clone, with `nice`:

* `java/before-commit.sh`: "Unit: SUCCESS, 1057 successful tests in 9.5
  s." "F: SUCCESS, 73 successful tests in 88.4 s." "BEFORE COMMIT OK (93
  s)". Again on the final tree:
  "Unit: SUCCESS, 1057 successful tests in 10.0 s." "F: SUCCESS, 73
  successful tests in 88.6 s." "BEFORE COMMIT OK (93 s)".
* `java/stress/level2.sh`, full: steps 1 to 5 pass: "SUCCESS, 1057
  successful tests"; RestartStress "0 failures" in all 13 runs, with
  default-disk ("Done: 2 rounds, 0 failures, 560 s."); RestartInvariance
  "stream identical, all checks OK" in all 8, inv-default-100MB with
  them; CrashTest "0 failures" in all 5. Step 6, BryanRepro, failed: "LEVEL
  2 FAILED: BryanRepro", in cycle 37 of 40, a cut's "Cound not delete file
  .../00000000000020.bergdb". **It fails on main too, since `eaec93e`
  (005-46, "no read waits for the stream's writer"):** in cycle 39 at
  `2eaaa45`, `a175840`, `e611709` and `eaec93e`, the same error; at
  `bf19075`, its parent, "Done: 40 cycles, 0 failures" twice, and twice
  with this patch's take applied to `bf19075` (TransSeq, Db, DbStarter).
  Step 7 on its own, as level2.sh full runs it
  ([level2-step7.sh](07-step3-paced-take/level2-step7.sh)): A2A3Check2 OK
  on its three configurations, "lake build: Build completed successfully
  (163 jobs)", "conformance: traces: 70, TRACECHECK OK: 70", "STEP 7 OK".
* `java/stress/level3.sh`, full, on the final tree: "LEVEL 3 OK": unit
  and f-tests; ReclaimStress "0 failures" in all 4; RestartInvariance with
  reclaim "stream identical, same cut, all checks OK" in all 4; CrashTest,
  ReclaimReaders "0 failures"; "POWERLOSS OK: 8 seeds, 440 cold
  recoveries"; "conformance: traces: 25, TRACECHECK OK: 25; C-CUT 0 of 305
  CUT lines fail"; InterruptStress, the flag kept by all.
* `java/stress/level4.sh quick`, since every stream changes (007-03's
  "Done when" asks for it then): "LEVEL 4 OK": EvictionInvariance OK on
  all 3; RestartInvariance "stream identical", CrashTest, ReclaimStress
  and ReclaimReaders "0 failures", every audit passed; "conformance:
  traces: 15, TRACECHECK OK: 15; C-P 0 of 3454 transactions fail", and
  C-H; LargerThanMemory within its budget.


## 5. StreamDigest

`StreamDigest all`, main's `2eaaa45` against the patch, one compiled copy
of the class (main's) against both jars
([digest-summary.txt](07-step3-paced-take/digest-summary.txt), with the
outputs): **all 36 streams change, as expected**, and within each of the 12
configurations the plain, reads and restarts streams agree (StreamDigest:
"the modes give the same stream"). The plain streams' lengths:

| configuration | main | patch | change |
|---|---|---|---|
| l2-sd100 | 5,131,920 | 5,131,920 | 0.0 % |
| l2-sd1000-node8 | 4,257,960 | 4,355,480 | +2.3 % |
| l2-sd10000-node14 | 2,421,648 | 2,556,312 | +5.6 % |
| l2-sd100000-node62 | 2,492,680 | 2,531,344 | +1.6 % |
| l2-every1 | 468,400 | 514,616 | +9.9 % |
| l2-idle-1 | 221,192 | 222,152 | +0.4 % |
| l2-idle-2 | 221,560 | 222,112 | +0.2 % |
| l2-default-100MB | 78,934,240 | 79,056,128 | +0.2 % |
| l3-every1 | 1,788,344 | 1,947,712 | +8.9 % |
| l3-node8 | 6,876,752 | 7,094,096 | +3.2 % |
| l3-node14 | 1,327,208 | 1,582,944 | +19.3 % |
| l3-node62 | 9,086,496 | 10,118,752 | +11.4 % |

The streams grow because the section no longer runs past sd, so nodes are
written younger (005-49, section 4). At sd 100 bytes (l2-sd100) both takes
write nearly everything at once: the length is the same, the bytes
differ. 005-49's prototype gave -3 to +20 percent on the same sets.


## 6. The evidence

005-49's measurements are the evidence for the pace
([report](../005-todo/49-smooth-index-writes/report.md)), with 10M and
50M keys, 1,000 puts a transaction, 50 to 1000 MB:

* At the same sd (section 6): the section held at 1.00 sd on average,
  1.14 at most; the largest record 2.2 to 2.5 times the mean and 0.27 to
  1.9 MB, against 2.5 to 11.6 MB for today's take; 12 to 36 percent more
  bytes a put, since the section no longer goes past sd. The deadline
  never fired.
* At the sd of today's peak section (section 4): 3 to 13 percent fewer
  bytes a put, records 6 to 11 times smaller.
* The deadline alone (section 3): records of up to 110 MB at 50 MB.

They were made with the prototype's hash; 2.1 says why that probably did
not matter for them. Step 2's runs again on this patch, which 007-06
prepares, are 007-03's own check (section 8).


## 7. Findings

### 7.1 Small commits after large transactions

005-49 did not measure transactions of mixed sizes (its section 8). With
whole transactions, a transaction is written by one record, whatever
commit takes it. Single puts with a batch of puts now and then, 20,000
keys, 100-byte values, sd 1 MB, 40,000 transactions:

| batch | take | single puts: mean record | largest | over 10 × mean | over 100 × mean |
|---|---|---|---|---|---|
| 500 puts every 1,000 | today's | 712 B | 104 kB | 173 | 26 |
| 500 puts every 1,000 | paced | 576 B | 209 kB | 102 | 40 |
| 100 puts every 200 | today's | 719 B | 26 kB | 227 | 0 |
| 100 puts every 200 | paced | 569 B | 57 kB | 285 | 1 |

Both takes make bursts here: a single put writes a batch's got-dirty
nodes whole. The paced take's largest is about twice today's. A batch's
record takes its share of D, large for its 500 puts, and the nodes it
writes that are still dirty (with a dirty child) join the batch's own
got-dirty nodes: 498 a batch on average, against 363 with today's take. A
pace by nodes, not transactions (005-49, section 5), would avoid it; it
changes the model (sis-model 6.1, step 6) and needs proofs of its own
(007-03, step 4).

### 7.2 Clumps

When a record takes much, its still-dirty nodes (written nodes with a
dirty child) go into its own got-dirty list, as they always have. That
transaction then comes due as one, about once a section, and moves to the
record that takes it. After 1 MB was lowered to 400 kB with 100-byte
values and 4,000 keys, a single put wrote 132 kB at 2 × sd (today's take:
20 kB at most). With 1 kB values and 1,000 keys there was none (largest
6.3 kB).

### 7.3 A decrease of the setting

To half of the actual startup distance or more, the deadline does not act
and the pace follows: each commit's share grows by S / sd, at most 2, so
the section's excess over the new setting shrinks about as exp(-x / sd),
x the stream written since. 8 MB lowered to 4 MB (single puts of 100
bytes, 50,000 keys, `TakeProbe`): over the next 3.7 MB the section was 1.74
times the new setting on average, the largest record 3.4 kB, 9 times the
mean. Today's take caught up faster (1.05 on average) with records of up
to 16 kB, 31 times the mean.

A larger decrease makes the deadline write the transactions past the new
d_h in the record of `setStartupDistance`'s dummy transaction. That record
moves more of the section past d_h, which the next record writes, and so
on: a series of records that shrinks by about the ratio of D's node bytes
to the section's length. It is 0.5 in `testDecrease`; 005-49's bytes a put
at 200 MB give about 0.9 (index bytes over all); at 1 or more the series
does not shrink until D is written. 8 MB lowered to 2 MB, as above: the
dummy's record was 1.4 MB; the next single puts wrote 427, 127, 43 and 15
kB; then, once a section, a single put wrote a clump (7.2) of 329, 276
and 240 kB. Today's take wrote no record over 16 kB, but its section
stayed at 3.8 times the new setting, and 1,628 of 10,000 records left
transactions past the new d_h.

So the Javadoc no longer says "no more than 10M for every call": repeated
calls without stream between them bring the setting below half the
section, and the deadline then acts at every call. It recommends a
decrease of at most a third a call, with about twice the new setting of
stream between calls: by the model above, the section is then about 1.07
times the setting at the next call, below twice the next setting, so the
deadline does not act.

D4 was decided B (Frans, 2026-10-26): `setStartupDistance` lowers the
distance in steps itself. This patch does not do that; the steps are the
caller's, as the Javadoc says (007-03's option C). Steps inside the method
need stream between them for the pace to follow, which only commits give;
dummy transactions of 200 kB each would be many at large distances.
(2026-10-28: D4:B is in the code as 007-06's "pace", section 10, and the
Javadoc's caller steps are gone.)

### 7.4 Existing databases

A database whose section today's take left past 2 × sd (up to 2.75 sd at
50 MB in 005-49's runs) gets the deadline at its first commits after the
patch, with a series of records as in 7.3. Once; not measured.


## 8. What remains of step 3's "Done when"

(2026-10-28: done, section 10, but the quick performance suite, which
waits for a quiet block, and the comments of the Lean files, for step 4.)

* Step 2's runs again on this take, and 005-49's: the section without its
  last record below d_h, the section at about sd, the largest record below
  a few times the mean. 007-06 prepares step 2's runs. The probes here are
  small: sd of 10 kB to 8 MB.
* level2.sh's step 6 on the combined tree, once BryanRepro passes on main
  again (section 4); `level4.sh` full (quick passed).
* The quick performance suite, in a quiet block.
* Docs after the runs: the write overhead at 50, 200 and 1000 MB (005-38's
  figures, which docs/levels.md now says are for the old take); P4's and
  P5's "Where BergDB stands" in 010-01. The comments of lean/SIS/Bound.lean
  and BoundExample.lean describe the old take, for step 4.
* D4:B, if Frans wants it now (section 7.3).


## 9. Questions for Frans

(Answered 2026-10-28, 006-09, section 8, decision 1: apply it; accept the
bursts of 7.1 and 7.2 for now, a pace by nodes is a model change for step
4; D4:B inside, as 007-06 measured it. Section 10.)

1. Apply the patch? Every stream changes; the format does not.
2. Sections 7.1 and 7.2: accept that a small commit after a large take can
   write a whole transaction, as with the old take, or a pace by nodes (a
   model change, with step 4)?
3. Section 7.3: D4:B inside `setStartupDistance` now, and how, or the
   caller's steps as the Javadoc now says?


## 10. Outcome (2026-10-28)

Frans decided on 2026-10-28 ([006-09](../006-2026-q4/09-unattended-27-28-october.md),
section 8, decision 1):

> 007-07: apply the step 3 patch, and add D4:B the way 007-06 measured it
> as "pace": the pace takes the new startup distance at once, and the
> deadline has its own distance, lowered with the lag to max(2 × new sd,
> lag) (007-06's deadline-probe.diff), not the caller's steps the patch's
> Javadoc now describes (007-06: steps of 10 MB gave records of up to 54
> MB). Accept 7.1/7.2's whole-transaction bursts for now; pace by nodes is
> a model change for step 4, not now.

Done by Claude (Opus 5.5, Claude Code) in the scratch clone
`/Users/f/fl/bench/006-09/d2-007-07`: the code in `f89846d`, on main's
`cefb473` (first made as `3612965` on `067d00b`, and gated on both), and
this text and the docs in the commit after it.

### 10.1 What went in

* `step3.diff` as sections 1 to 3 describe it. It applied cleanly to
  `067d00b` (005-63's lock and 005-56's import line in `Db.java` are
  elsewhere), and the commit rebased onto `cefb473` without conflicts.
* D4:B, in `TransSeq.take`. The deadline's distance is the larger of d_h =
  2 × sd and the span of the section's transactions, from the tpos of the
  oldest to that of the newest, as the last record left them
  (`TransSeq.span()`):

      hardSp = streamLength - max(2 * sd, span)

  * In steady state the span is below d_h after every record, since the
    deadline at d_h leaves no older transaction; so the deadline is at d_h
    and nothing changes. Every stream of StreamDigest is the patch's
    (10.3), and so are the records of step 2's steady runs (10.4).
  * After a decrease, the pace uses the new setting at once: a record's
    share grows by S / sd. The deadline does not jump to the new d_h: it
    is at the span. A record takes every transaction that begins within
    the last record's length of the oldest, so the span shrinks with every
    record, strictly, until it is below d_h; from then on the deadline is
    at d_h. The deadline's distance never rises while it comes down, and
    it is continuous where the span crosses d_h.
  * T3 holds for the deadline in force (007-06, section 5, point 2): the
    take keeps up with max(d_h, span), and the span is at most what it
    was at the decrease, which the deadline before it kept below the old
    d_h.
* Why the span and not a distance of its own, as 007-06's probe had (a
  static field, lowered every 10 transactions): a distance kept in memory
  is lost at a restart, so the stream would depend on restarts (P2), and
  keeping it in the stream is a format change. The span is a function of
  the transactions of the startup section, which a start reruns
  (`DbStarter`), as D and O are. It is the probe's "lag" less the record
  at the startup pos and the last record, and it is lowered at every
  record, not every 10 transactions. Measured from the startup pos, as the
  probe's lag was, a record at the startup pos longer than the records
  after it would keep the deadline from ever taking the next transaction;
  measured from the oldest transaction, the deadline takes at least one
  transaction a record while the span is longer than d_h.
* Raising the setting needs nothing of its own, and gets nothing. The
  share shrinks at once by the ratio of the settings, and the deadline is
  at the new d_h at once: the span is below the old d_h, so below the new
  one, and nothing becomes due. The commits that follow write fewer index
  nodes until the section has grown to the new setting, which it does at
  most as fast as the stream grows. With `D4Probe`, 1 MB raised to 4 MB,
  1 kB values: the section grew to 1.02 times the new setting, the records
  were smaller on average than before (1,203 bytes against 1,326), and the
  stream was the patch's, byte for byte.
* `Db.setStartupDistance`'s Javadoc: one call, no steps; a decrease does
  not make one commit write the index nodes of every transaction past
  twice the new setting; the section comes down only as transactions are
  committed.
* Not changed: no new setting (P10), no state outside `TransSeq`, no time
  or thread, no format change. The 200 kB value of `setStartupDistance`'s
  transaction still counts as its own bytes (007-06, section 5, point 4;
  10.5).

### 10.2 The tests

In `TransSeq` (synthetic transactions):

* `testDecrease`, rewritten for D4:B: sd 100000 lowered to 25000. The
  record at the decrease takes its share, 40 nodes, where the deadline at
  the new d_h took 250 and the next three records 130, 70 and 40; no
  record takes more than 40; after every record the deadline in force
  holds and, while the span is longer than d_h, the span has shrunk; it is
  below d_h after 15 records, and the section ends at 25000 (the test
  allows 20 percent).
* `testDeadlineAfterDecrease`, new: the deadline alone (no share), 20
  transactions 100 apart and sd 100: each record takes two transactions,
  not the 19 past d_h, the span shrinks by a record each time, and below
  d_h the deadline is at d_h.
* `testDeadline`: a second case, with a span longer than d_h, takes the
  transactions within the last record's length of the oldest, two, not
  four. Its first case and `testTakeWithBudget` and `testSumsAfterTake`
  moved their numbers so that their transactions span less than d_h, as
  in steady state; their assertions are unchanged. With the span longer
  than d_h, D4:B takes less there, by design.
* `testShare`, `testTake1`, `testTake2`: unchanged.

In `DbTester` (a real database in memory):

* `testDecreaseOfStartupDistance`, rewritten: 2 MB lowered to 500 kB, 1 kB
  values. Transactions that begin twice the new setting or more before the
  end are left after the call (with the deadline at the new d_h at once,
  none were); the span shrinks with every commit and is below twice the
  setting after 19; the deadline holds from then on. 0.3 s.
* `testPaceHoldsTheStartupSection`: unchanged, and passes unchanged.

In `DbTesterRestart`, the f-test `testSameStreamAfterDecreaseWithRestartsF`,
new: the same decrease, with a restart right after the call and one every
10 commits after it, gives the same stream, byte for byte, as without
(P2). 0.8 s.

Without D4:B, on the patch alone, `testDecrease`, `testDeadline`,
`testDeadlineAfterDecrease` and `testDecreaseOfStartupDistance` fail; the
restart test passes on both. D4Probe (in this item's directory) runs a
decrease, an increase, and restarts after them, on any build; with a
restart after every one of the 1,500 commits after a decrease from 8 MB to
1 MB, the stream was the same as without.

### 10.3 The gates and StreamDigest

In the clone, one after another with `nice`: on `3612965` (base
`067d00b`) from 09:45 to 10:20, and again after the rebase on `f89846d`
(base `cefb473`) from 11:12 to 11:47, with the same results. The
lines of the second:

* `java/before-commit.sh`: "Deps: 9 packages, all as package.html
  allows", "Unit: SUCCESS, 1064 successful tests in 9.9 s.", "F: SUCCESS,
  75 successful tests in 92.2 s.", "BEFORE COMMIT OK (97 s)" (on
  `067d00b`: 1062 and 75 tests, 91 s).
* `java/stress/level2.sh`, full, 13 minutes: "SUCCESS, 1064 successful
  tests"; RestartStress "0 failures" in all 13 runs, default-disk with
  them ("Done: 2 rounds, 0 failures, 607 s."); RestartInvariance "stream
  identical, all checks OK" in all 8, inv-default-100MB with them;
  CrashTest "0 failures" in all 5; BryanRepro "Done: 40 cycles, 0
  failures" (step 6 passes since `b0661ba`); A2A3Check2 OK on its three
  configurations; "conformance: traces: 70, TRACECHECK OK: 70"; "LEVEL 2
  OK".
* `java/stress/level3.sh`, full, 7 minutes: unit and f-tests; ReclaimStress
  "0 failures" in all 4; RestartInvariance with reclaim "stream identical,
  same cut, all checks OK" in all 4; CrashTest and ReclaimReaders "0
  failures"; "POWERLOSS OK: 8 seeds, 440 cold recoveries; negative controls
  caught"; "conformance: traces: 25, TRACECHECK OK: 25; C-CUT 0 of 305 CUT
  lines fail"; InterruptStress, the flag kept by all; "LEVEL 3 OK".
* `java/stress/level4.sh`, full, 13 minutes: the unit tests and the 16
  eviction f-tests; EvictionInvariance "EVICTION INVARIANCE OK" on all 9,
  every audit passed; RestartInvariance "stream identical", CrashTest and
  ReclaimStress "0 failures" with forced schedules, "0 failed" audits;
  ReclaimReaders "0 failures" in all 5; "conformance: traces: 45,
  TRACECHECK OK: 45; C-P 0 of 10344 transactions fail", and C-H 0 of
  10344; LargerThanMemory resident at 49 MB, within its budget of 50 MB;
  "LEVEL 4 OK".

StreamDigest all, main's compiled class against the jars, as in section
5, on `067d00b` and again on `cefb473` after the rebase:

* Main against the patched build: "DIGESTS DIFFER (36 of 36)", as
  expected, with the lengths of section 5's table. Main's digests are
  still those of `2eaaa45` (digest-base.txt), on both bases: the changes
  since, among them 005-63's lock file, 005-56's move of `SyncLevel` and
  005-66's builder, change no stream.
* The patched build twice: "DIGESTS IDENTICAL (36 of 36)", on each base;
  and the two bases' patched builds give the same digests.
* The patch alone (step3.diff on `067d00b`) against the patched build:
  "DIGESTS IDENTICAL (36 of 36)", and both are digest-patch.txt. No
  configuration of StreamDigest lowers the startup distance, so D4:B
  changes none of their streams, as 10.1 says.

### 10.4 Step 2's runs on the patched build

007-06's step-2 runs again, on the patched build, as step 3's "Done
when" asks: the whole of 007-06's queue 5, the steady runs (updates,
deletes and single puts at 50, 200 and 1000 MB), and the four decreases of
its queue 4, now one call each, since D4:B is in the code. 10M keys, as in
007-06; on F53 from 10:20 to 11:11, 51 minutes, byte counts only. The
scripts and the summaries are in [07-step3-paced-take/step2/](07-step3-paced-take/step2/);
the records (wb.rec) stay in `/Users/f/fl/bench/006-09/d2-007-07-runs/w8`.

**The steady runs are the patch's, byte for byte.** The records of all
eight runs (each record's size, index bytes, section, D and debt) are the
same bytes as those of 007-06's runs of the patch alone, so its table in
section 4 holds: the section at most 1.10 sd, the largest record 0.23 to
1.93 MB, and 867, 524 and 190 bytes a put for updates at 50, 200 and 1000
MB. The section without its last record stayed below d_h in every run.

**The decreases**, one call each, at 007-06's points: "worst", before the
record with the largest debt after 10M updates (pick.py on this build's
steady runs; the same points as 007-06's runs of the patch alone), and at
20M updates:

| decrease | section / debt before | `setStartupDistance`'s record | to 2 sd: puts, stream, largest user record | to sd: the same | after, second half: section max, largest record |
|---|---|---|---|---|---|
| 1000 to 100, worst | 988 / 601 MB | 3.34 MB | 0.67M, 822 MB, 2.30 MB | 0.74M, 931 MB, 3.21 MB | 1.04 sd, 1.67 MB |
| 1000 to 100, 20M | 1043 / 579 MB | 3.61 MB | 0.59M, 817 MB, 2.94 MB | 0.64M, 918 MB, 3.02 MB | 1.05 sd, 1.54 MB |
| 200 to 50, worst | 201 / 175 MB | 5.42 MB | 0.08M, 234 MB, 5.11 MB | 0.10M, 275 MB, 5.11 MB | 1.08 sd, 1.83 MB |
| 200 to 50, 20M | 198 / 170 MB | 5.34 MB | 0.09M, 234 MB, 4.66 MB | 0.10M, 275 MB, 4.66 MB | 1.10 sd, 1.97 MB |

Against 007-06:

* The patch alone, at the same "worst" points, wrote one record of 486 MB
  and then one of 145 MB at 1000 to 100, and 87 MB and then 72 MB at 200
  to 50. With D4:B no record is over 5.4 MB.
* The probe ("pace", 007-06's section 3, on 005-49's prototype, at its
  own points): a dummy record of 3.3 to 5.6 MB; the section below 2 sd
  after 0.59 to 0.67M puts and 815 to 825 MB at 1000 to 100, and after
  0.10M puts and 240 to 246 MB at 200 to 50; user records of at most 2.5
  to 3.1 MB and 3.9 to 4.0 MB; after it 1.04 to 1.15 sd. D4:B behaves as
  the probe, a little faster at 200 to 50, with one difference: there the
  commits right after `setStartupDistance`'s record of 5.4 MB wrote 4.4 to
  5.1 MB each, for about 9 commits, where the probe's wrote 1.7 to 2.1 MB;
  later both wrote 2 to 4 MB. The deadline, at the span at every record,
  makes each record take at least the last record's length of the
  section, and at that point D's bytes are 0.87 of the section's, so each
  record writes about as much as the one before (7.3's series), until the
  pace's share is the larger. At 1000 to 100, where they are 0.61 of it,
  the series fell from 3.3 MB to the pace's 1.1 MB in three records.

**The deadline held the section** in every decrease: the section without
its last record shrank with every record until it was below the new 2 sd,
after 81 to 86 records at 200 to 50 and 587 to 669 at 1000 to 100; it
never grew meanwhile, and it stayed below 2 sd after (ratchet.txt). So
step 3's "Done when" holds for these runs with the deadline in force: d_h,
or during a decrease the span at the decrease, which only shrinks.

How often the deadline takes a transaction that the share would not
([DlProbe.java](07-step3-paced-take/DlProbe.java) on a build with
dlprobe.diff, databases of 8 and 20 MB in memory): never in steady state
(0 of 10,000 to 100,000 commits before the decrease); during a decrease in
10 to 40 percent of the commits (8 to 1 MB: 103 of 678; 20 to 5 MB with
single puts: 4,270 of 10,544), mostly one transaction, the oldest; after
it, at most 2 commits in 20,000. 007-06's probe, its deadline lowered
every 10 transactions, never fired; D4:B's, lowered at every record, is
the backstop that keeps the span from growing.

### 10.5 Left

* **The quick performance suite**, in a quiet block:
  [night/run-quick.sh](07-step3-paced-take/night/run-quick.sh), `#
  minutes: 40`. `performance.sh ab` with `SUITE=quick` and `FORCE=1` on
  two preserved builds in the clone, `main-cefb473` and `d4b-f89846d`,
  their harness compiled; it compiles nothing. `SMOKE=1 sh run-quick.sh`
  passed: both sessions with all 7 scenarios of the smoke suite,
  "Comparison exit code 0", in under a minute. For 006-10's W1.1.
* **`setStartupDistance`'s 200 kB value** still counts as its own bytes
  (007-06, section 5, point 4). With D4:B its record is the largest of a
  decrease, 3.3 to 5.4 MB, and at 200 to 50 MB it starts the series of
  10.4. In small probes (D4Probe, 8 and 20 MB, 1 kB values or 10 puts of
  100 bytes a transaction) it wrote 0.5 to 1.7 MB and the next commit 0.18
  to 0.77 MB. A prototype that counts no own bytes for the value (in
  `Db.store` only; a real change needs the same rule in `DbStarter`, by
  the dummy key, so that a start computes the same) wrote 0.2 MB and then
  0.07 to 0.10 MB there, and the section came down later where the call
  had done much of the work (8 to 1 MB: below 2 sd after 370 commits
  instead of 73). For Frans: count the value, as now, or not.
* 007-06's "Left": 50M keys and a longer delete run, not run.
* Step 4 of 007-03: the take in Lean, with the deadline at max(d_h, span);
  the comments of `lean/SIS/Bound.lean` and `BoundExample.lean`, which
  describe the take before step 3, go with it.
* 010-01: P4's and P5's "Where BergDB stands" are updated. P1's bullet on
  the deadline's long commit after a decrease (007-04, points 6 and 7) and
  P2's "To check" on the deadline, which StreamDigest and the restart test
  of 10.2 now answer, are not.

The documents: 007-03 (the status, steps 2, 3 and 4, D4), this item's log,
docs/levels.md, section 5 (the take, its limits, the write overhead and
the largest records, from 007-06 and 10.4), README.md (as the patch had
it), 010-01 (P4, P5) and releases/next.md.


## Files

In [07-step3-paced-take/](07-step3-paced-take/):

* `step3.diff`: the patch, `git diff 2eaaa45` of the clone's commit.
* `ShareProbe.java`, `TakeProbe.java`, `DecreaseProbe.java`,
  `MixedProbe.java`: the probes behind sections 2, 3 and 7, in package
  `bergdb.core`; compile against a build's bergdb.jar and put the classes
  first on the class path.
* `level2-step7.sh`: level2.sh's step 7 on its own (section 4).
* `digest-summary.txt`, `digest-base.txt`, `digest-patch.txt`:
  StreamDigest (section 5); the patched build of section 10 gives
  digest-patch.txt's digests.
* `D4Probe.java`: a change of the startup distance on a database in
  memory, with restarts after it if asked, on any build (section 10).
* `DlProbe.java` and `dlprobe.diff`: how often the deadline takes a
  transaction that the share would not, on a build with the diff (section
  10.4).
* `step2/`: section 10.4's runs: `queue-d4b.sh` (with 007-06's `run.sh`,
  `pick.py`, `summary.py` and `tables.py`), `ratchet.py`, and the outputs
  `runs.txt`, `summary.txt`, `tables.txt` and `ratchet.txt`.
* `night/run-quick.sh`: the night step for the quick performance suite
  (section 10.5).
