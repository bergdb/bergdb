007-07. Step 3 as a patch: the paced take with the deadline
===========================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code) for Frans Lundberg
(006-09, W10), at his choice (17:27): "007-03 step 3 as a patch". Status:
done. Frans decided on 2026-10-28 to apply the patch and to add D4:B as
007-06 measured it; both went into the code that day, gated, with
007-06's step-2 runs again on them (section 10) and at 50M keys (section
11). Sections 1 to 9 are the
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
waits for a quiet block, and the comments of the Lean files, for step 4.
2026-10-29: the quick suite ran on the night of 2026-10-28, not in a
quiet block, and is done in substance, section 12.4.)

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

* **The quick performance suite**, in a quiet block (run on the night of
  2026-10-28, not quiet, and done in substance: section 12):
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
* 007-06's "Left": 50M keys and a longer delete run. Run in section 11:
  the steady bound holds at 50M keys, but a decrease's largest record
  grows with the keys, to 13 to 15 MB from 1000 to 100 MB (11.3).
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


## 11. 50M keys (2026-10-28)

007-06's "Left" (50M keys, a longer delete run), run on main's code in
006-10 by Claude (Opus 5.5, Claude Code): the set of 10.4 again, with 50M
keys instead of 10M. The build was main's `b362a8b`, whose `java/` has
`f89846d`'s take (step 3 and D4:B). Main moved during the runs. Its
`fd8f513` (005-53) changed `setStartupDistance` for the value in force
and for a refused transaction, not for a decrease. A smoke run (200k keys,
20 to 2 MB) gave the same records, byte for byte, on `b362a8b`, on main's
`0b6d08e` and on 10.4's d4b build.

On F53, `nice -n 19`, one JVM of 22 GB at a time, from 12:36 to 15:55,
byte counts only. Nothing was skipped. The settings are 005-38's for 50M
keys: 24-byte keys with 8-byte values loaded in random order, 1,000 puts a
transaction, windows of 2.5M puts, a ring of 1.3 GB, and no eviction.
Where they differ from 10.4:

* 20M updates after the load, not 30M, as 005-49 ran 50M keys. Steady
  runs are measured over the last 10M (4.6 to 12.4 GB of stream).
* The "worst" points come from pick.py on this build's steady runs at
  50M: 15.72M updates at 1000 MB and 11.71M at 200 MB. The "20M" points
  are as before. Each decrease run has 10M updates after the call.
* Deletes at 1000 MB: 40M of the 50M keys, 16.6 GB of stream (16.6 sd).
  At 10M keys the run covered only 1.4 sd (007-06). At 50 and 200 MB:
  8M, as at 10M.

Scripts and summaries are in
[07-step3-paced-take/step2-50m/](07-step3-paced-take/step2-50m/):
`run50.sh` and `queue50.sh` (with 007-06's `pick.py` and `summary.py`
and 10.4's `ratchet.py` beside them), `cmp50.py` for the tables below,
`big.py` for the records over a few times the mean, and `share.py` for
the share estimate of 11.2. Outputs: `runs.txt`, `summary.txt`,
`tables.txt`, `big.txt`, `ratchet.txt` and `share.txt`. The records
(wb.rec, 0.8 GB) stay in `/Users/f/fl/bench/006-10/r50/out/`. The 10M
rows are 10.4's records, reread.

### 11.1 Steady runs

Over the second half of each workload. "Mean record" is the mean record
in bytes, and the largest is also given in times that mean.

| run | keys | puts | B/put | mean record | largest record (× mean) | records over 3 / 5 / 10 × mean | over 100 kB | section mean / p99 / max (sd) | debt max (sd) | D max |
|---|---|---|---|---|---|---|---|---|---|---|
| updates, 50 MB | 10M | 15.0M | 867 | 867 kB | 1.93 MB (2.2×) | 0 / 0 / 0 | 14030 | 0.97 / 1.08 / 1.10 | 1.04 | 137k |
| updates, 50 MB | 50M | 10.0M | 1244 | 1244 kB | 2.82 MB (2.3×) | 0 / 0 / 0 | 9999 | 0.95 / 1.05 / 1.08 | 1.05 | 138k |
| updates, 200 MB | 10M | 15.0M | 524 | 524 kB | 1.12 MB (2.1×) | 0 / 0 / 0 | 14127 | 0.99 / 1.01 / 1.02 | 0.88 | 448k |
| updates, 200 MB | 50M | 10.0M | 851 | 851 kB | 1.78 MB (2.1×) | 0 / 0 / 0 | 9502 | 1.00 / 1.05 / 1.05 | 0.97 | 537k |
| updates, 1000 MB | 10M | 15.0M | 190 | 190 kB | 0.34 MB (1.8×) | 0 / 0 / 0 | 14695 | 1.03 / 1.09 / 1.09 | 0.59 | 1417k |
| updates, 1000 MB | 50M | 10.0M | 460 | 460 kB | 0.95 MB (2.1×) | 0 / 0 / 0 | 9532 | 1.00 / 1.01 / 1.01 | 0.85 | 2308k |
| deletes, 50 MB | 10M | 4.0M | 787 | 787 kB | 1.72 MB (2.2×) | 0 / 0 / 0 | 3749 | 0.97 / 1.08 / 1.10 | 1.03 | 137k |
| deletes, 50 MB | 50M | 4.0M | 1159 | 1159 kB | 2.53 MB (2.2×) | 0 / 0 / 0 | 3796 | 0.95 / 1.07 / 1.11 | 1.10 | 152k |
| deletes, 200 MB | 10M | 4.0M | 422 | 422 kB | 0.85 MB (2.0×) | 0 / 0 / 0 | 3779 | 0.99 / 1.01 / 1.01 | 0.86 | 464k |
| deletes, 200 MB | 50M | 4.0M | 783 | 783 kB | 1.71 MB (2.2×) | 0 / 0 / 0 | 3774 | 0.99 / 1.03 / 1.04 | 0.96 | 537k |
| deletes, 1000 MB | 10M | 4.0M | 121 | 121 kB | 0.23 MB (1.9×) | 0 / 0 / 0 | 2875 | 0.96 / 1.02 / 1.03 | 0.47 | 1219k |
| deletes, 1000 MB | 50M | 20.0M | 423 | 423 kB | 0.94 MB (2.2×) | 0 / 0 / 0 | 18882 | 1.00 / 1.01 / 1.01 | 0.86 | 2308k |
| single puts, 50 MB | 10M | 3.0M | 873 | 0.87 kB | 0.29 MB (328×) | 2451 / 2359 / 2359 | 1222 | 1.00 / 1.03 / 1.03 | 0.90 | 121k |
| single puts, 50 MB | 50M | 3.0M | 1225 | 1.23 kB | 0.33 MB (269×) | 1422 / 1397 / 1397 | 1397 | 1.00 / 1.03 / 1.04 | 0.95 | 132k |
| single puts, 200 MB | 10M | 3.0M | 537 | 0.54 kB | 0.23 MB (434×) | 6540 / 4117 / 4062 | 686 | 1.00 / 1.01 / 1.01 | 0.79 | 425k |
| single puts, 200 MB | 50M | 3.0M | 859 | 0.86 kB | 0.28 MB (324×) | 2645 / 2332 / 2194 | 1737 | 1.00 / 1.02 / 1.03 | 0.89 | 505k |

* **The section holds at sd at 50M keys.** It is at most 1.11 sd in
  every run, the same as at 10M (1.10). The debt is at most 1.10 sd. The
  section stayed below 2 sd at every record (ratchet.txt), and that
  includes the whole of the long delete run: 40M deletes and 16.6 sd of
  stream, with the section at most 1.06 sd and the debt at most 0.88 sd.
* **Bytes a put grow with the keys**, as 005-38 found on today's take:
  1.4 to 1.8 times at 50 and 200 MB, and 2.4 to 3.5 times at 1000 MB
  (190 to 460 for updates, 121 to 423 for deletes). At 1000 MB, D is
  2.3M nodes at 50M keys, against 1.4M at 10M.
* **Records stay near their mean** with 1,000 puts a transaction. The
  largest is 1.8 to 2.3 times the mean at both sizes, and no record is
  over 3 times the mean. The largest record grows with the mean, up to
  2.82 MB (updates at 50 MB).
* **Single puts are no worse at 50M.** The largest record is 0.33 and
  0.28 MB, against 0.29 and 0.23 MB at 10M. Of 3M records, 1,397 and
  1,737 are over 100 kB, against 1,222 and 686. A put's mean record is
  about 1 kB, so these are the whole-transaction bursts of 7.1/7.2,
  which Frans accepted for now.

### 11.2 Decreases, one call (D4:B)

From `setStartupDistance`'s record until the section is first below the
new 2 sd ("catch-up"). "Records" is the count of records in the
catch-up. "New mean" is the mean record in the second half of the rest
of the run, the new distance's steady records.

| decrease | keys | section / debt before | setStartupDistance's record | to 2 sd: puts, stream, records | largest user record (× new mean) | catch-up records over 3 / 5 / 10 × new mean | to sd: puts, stream | new mean record | after, 2nd half: section max, largest record |
|---|---|---|---|---|---|---|---|---|---|
| 1000 to 100, worst | 10M | 988 / 601 MB | 3.34 MB | 0.67M, 822 MB, 669 | 2.30 MB (3.3×) | 26 / 0 / 0 | 0.74M, 931 MB | 695 kB | 1.04 sd, 1.67 MB |
| 1000 to 100, worst | 50M | 1009 / 849 MB | 11.42 MB | 0.20M, 1146 MB, 201 | 13.34 MB (12.3×) | 202 / 62 / 16 | 0.21M, 1174 MB | 1080 kB | 1.08 sd, 2.56 MB |
| 1000 to 100, 20M | 10M | 1043 / 579 MB | 3.61 MB | 0.59M, 817 MB, 587 | 2.94 MB (4.3×) | 87 / 1 / 0 | 0.64M, 918 MB | 691 kB | 1.05 sd, 1.54 MB |
| 1000 to 100, 20M | 50M | 1004 / 847 MB | 11.56 MB | 0.20M, 1144 MB, 196 | 15.36 MB (14.1×) | 197 / 61 / 15 | 0.20M, 1175 MB | 1087 kB | 1.07 sd, 2.71 MB |
| 200 to 50, worst | 10M | 201 / 175 MB | 5.42 MB | 0.08M, 234 MB, 81 | 5.11 MB (5.9×) | 41 / 7 / 0 | 0.10M, 275 MB | 862 kB | 1.08 sd, 1.83 MB |
| 200 to 50, worst | 50M | 207 / 194 MB | 8.46 MB | 0.04M, 240 MB, 40 | 8.80 MB (6.9×) | 40 / 12 / 0 | 0.05M, 267 MB | 1268 kB | 1.10 sd, 2.82 MB |
| 200 to 50, 20M | 10M | 198 / 170 MB | 5.34 MB | 0.09M, 234 MB, 86 | 4.66 MB (5.3×) | 35 / 3 / 0 | 0.10M, 275 MB | 874 kB | 1.10 sd, 1.97 MB |
| 200 to 50, 20M | 50M | 195 / 180 MB | 8.81 MB | 0.03M, 222 MB, 32 | 8.77 MB (6.9×) | 33 / 23 / 0 | 0.04M, 242 MB | 1276 kB | 1.13 sd, 2.95 MB |

* **The deadline holds the section at 50M, as at 10M.** In all four
  decreases the section without its last record shrank at every record
  until it was below the new 2 sd, never grew in the meantime, and
  stayed below 2 sd afterwards (ratchet.txt). Afterwards it settles at
  1.07 to 1.13 sd.
* **The catch-up takes about the same stream for a given debt, but
  fewer puts.** Before it is below the new 2 sd, the stream grows by
  1.35 times the debt at the decrease from 1000 to 100 MB (1.37 to 1.41
  at 10M), and by 1.23 to 1.24 times it from 200 to 50 MB (1.34 to
  1.38). The debt is larger at 50M (849 MB against 601 MB at 1000 MB),
  but the commits during the catch-up are larger still: 5.7 kB a put
  against 1.2 kB at 1000 to 100 MB. So the section is below 2 sd after
  0.20M puts and about 200 records, against 0.59 to 0.67M puts and 587
  to 669 records at 10M. From 200 to 50 MB it takes 0.03 to 0.04M puts,
  against 0.08 to 0.09M.
* **The largest record of a decrease grows with the keys.** From 1000
  to 100 MB, `setStartupDistance`'s record is 11.4 to 11.6 MB, against
  3.3 to 3.6 MB at 10M, and the largest user record is 13.3 to 15.4 MB,
  against 2.3 to 2.9 MB. That is 12 to 14 times the new mean record, and
  29 to 33 times the mean record before the call. Every catch-up record
  is over 3 times the new mean, and 15 to 16 are over 10 times it. From
  200 to 50 MB the call's record is 8.5 to 8.8 MB (5.3 to 5.4 MB at
  10M), and the largest user record is 8.8 MB (4.7 to 5.1 MB), 6.9
  times the new mean. That is about the ratio at 10M (5.3 to 5.9).
* **The shape, from 1000 to 100 MB, is the same at both sizes and four
  times as large at 50M.** After the call's record (11.4 MB; 3.3 MB at
  10M), the records fall within about 8 records to a plateau: 3.7 to 5 MB
  (1.0 to 1.1 MB at 10M), while the section comes down slowly. A second
  peak follows in the last tenth of the catch-up: 12 to 15 MB (2.0 to 2.9
  MB at 10M), while the section falls from about 850 to 200 MB. After it,
  the records fall to the new steady mean.
* **The share writes both, not the deadline.** `share.py` estimates each
  record's share, o × D/O × S/sd, from the logged fields, with O summed
  over the records after the startup pos. At every record of the
  catch-up, the nodes written are 0.5 to 1.2 times the estimate (0.6 to
  1.6 at 10M), the peak included. S/sd starts at 10 at both sizes. D/O,
  the section's got-dirty nodes for each MB of its own bytes, starts
  where the old setting left it: 12k at 50M against 3.2k at 10M. With 50M
  keys, a put more often makes a node dirty that is not dirty already.
  That gives the plateau's four times. D/O then rises, as the old
  transactions are paid off and those made since the call become more
  of the section. At 90 percent of the catch-up it is 31k at 50M and 12k
  at 10M, while S/sd is still 7 and 4.5, and that is the peak. Since
  these are estimates, from own bytes that include the got-dirty list,
  they explain the shape, not each record.

### 11.3 What it means for D4:B and the bound

1. **Steady state scales to 50M keys.** The paced take holds the section
   at 1.11 sd at most and the debt at 1.10 sd at most, on updates,
   deletes and single puts. No record is over 2.3 times the mean. The
   long delete run (16.6 sd) shows no drift. T3's bound with the
   deadline at 2 sd is never reached in steady state, as at 10M.
2. **D4:B keeps its guarantee at 50M:** a ratchet down to the new 2 sd,
   with the deadline a backstop that never lets the section grow. The
   catch-up costs about 1.2 to 1.4 times the debt in stream, whatever
   the keys. There is no large commit of the kind 007-06 measured on the
   patch alone (486 MB at 10M keys).
3. **But the largest record of a decrease grows with D, so with the
   keys:** 13 to 15 MB at 50M keys from 1000 to 100 MB, against 3.6 MB at
   10M. That is 4 times as large for 5 times the keys and 1.4 times the
   debt. It is 13 to 15 percent of the new setting. For the startup bound
   (T3_bounded, d + 2M with M the largest record), M is then 15 MB
   against d = 200 MB. Of a catch-up's 196 to 201 commits, 61 to 62 write
   over 5 times the new mean record and 15 to 16 over 10 times. 100M
   keys, which needs a heap over F53's 32 GB, was not run, and the
   records there are not known; from 10M to 50M they grew 4 times.
4. **What would bound it.** The plateau and the peak are the pace's
   share, with S/sd at up to 10 times its steady value of 1. Capping the share's factor
   S/sd (at 2 or 4, say) would bound a decrease's records near the
   steady ones, at the cost of a longer catch-up. 007-06's "follow",
   whose factor was at most 2, took 3.0 to 3.4M puts from 1000 to 100 MB
   at 10M keys. The deadline at the span would still keep the section
   from growing. That is a change to step 3's take, for Frans, and no
   test has been run on it. `setStartupDistance`'s 200 kB value (10.5) is
   no longer the main question at 50M. The call's record is 11.4 MB, but
   the user records after it reach 15 MB.


## 12. The quick suite and Props, 2026-10-28 night

Section 10.5's quick performance suite and Props (MEM, CORE, SS) before
and after 007-07, run in a gap on the evening of 2026-10-28 for 006-10's
W1.1 and W1.2, by Claude (Opus 5.5, Claude Code); written up the next
morning. Both were marked not quiet: the conductor's 10-minute check did
not find the machine quiet and went on, and performance.sh measured
84.52 % idle CPU before the runs (its own limit is 90 %; `FORCE=1`). The
two builds are the preserved ones of section 10: `main-cefb473`, main
just before 007-07, and `d4b-f89846d`, 007-07's code (step 3 with D4:B).
Also the night run of `night.sh` at 18:22 (java/build/night/2026-10-28-1822/,
on main after 007-07), whose only failure was level1's SS limits.

### 12.1 The quick suite

[night/run-quick.sh](07-step3-paced-take/night/run-quick.sh): 4 scenarios,
3 runs of each build per scenario in ABBA order, from 19:13 to 19:27.
"Comparison exit code 0", no alerts. The comparison and the metrics that
moved are in
[night/results-quick-2026-10-28.md](07-step3-paced-take/night/results-quick-2026-10-28.md).
Medians of 3 runs, main-cefb473 against d4b-f89846d:

| scenario | throughput | change (CV ref / cand) | latency (median of the runs) |
|---|---|---|---|
| read-1k (warm reads) | get_latest 1,262,180 / 1,267,990 gets/s | +0.5 % (1.4 / 1.1 %) | p50 667 / 667 ns, p99 1799 / 1751 ns, p99.9 2175 / 2127 ns |
| w-uni-1k-inf (updates, infinite retention) | 103,664 / 103,400 commits/s | -0.3 % (0.4 / 0.5 %) | append p50 7.6 / 7.6 µs, p99.9 25.6 / 25.9 µs |
| w-uni-1k-fin (updates, finite retention) | 66,622 / 66,683 commits/s | +0.1 % (0.1 / 0.2 %) | append p50 8.2 / 8.0 µs, p99 64.5 / 70.1 µs, p99.9 92.7 / 102.9 µs |
| r-1k-fin (restart, then mixed) | 53,421 / 54,127 commits/s, 2,357,620 / 2,460,360 gets/s | +1.3 % (0.2 / 0.4 %), +4.4 % (1.3 / 1.7 %) | startup 0.692 / 0.700 s; commit p99 88.1 / 92.2 µs, get p99 1.46 / 1.30 µs |

The other read metrics (historical gets, four threads, long keys, scans)
are within -2.6 to +3.1 %, each inside its CV. Bytes appended a put are
the same: 1.22 and 1.68 per user byte, 1687.2 against 1687.1 bytes a put
in w-uni-1k-fin.

Beyond the CV, with the 3 runs of each build not overlapping:

* **Finite retention, the commit's tail: +9 to 11 percent at p99 and
  p99.9.** w-uni-1k-fin's append p99 is 64.5 against 70.1 µs and its p99.9
  92.7 against 102.9 µs (+11.0 %), and r-1k-fin's prepare phase, the same
  workload, gives +9.2 and +10.5 %; r-1k-fin's mixed phase +4.7 % at p99.
  The median commit is 2 to 6 percent faster, the throughput the same.
  The stream shows where: a put writes the same bytes, but more of them
  in reclaim's step records (462.8 against 430.0 bytes a put) and less
  index in its own record (138 against 171). Index writes move from the
  user's records to reclaim's steps; a commit that carries a step is
  slower, so the tail grows a little and the median falls. Why the take
  moves them there was not looked into.
* **Startup: +1 to 4 percent.** r-1k-fin's start reruns 33,355
  transactions against 32,540 (+2.5 %, the same in every run) from the
  same position (1864.5 MB), in 0.700 against 0.692 s; w-uni-1k-fin's
  restart is 0.620 against 0.595 s (+4.1 %).
* **r-1k-fin's gets: +4.4 %**, p99 1.30 against 1.46 µs. Not explained;
  the change touches no read path, so probably the machine (CV 1.3 and
  1.7 %).
* **w-uni-1k-inf's slowest commit**, performance.sh's only EXPLAIN (a
  median of 0.14 against 32.0 ms), is a GC pause's: every run of both
  builds had a G1 pause of 151 to 170 ms, and one run of each build had
  its slowest commit at 159 to 164 ms. Whether a pause falls inside an
  append is chance; GC pauses in total are +3.2 %.

### 12.2 Props

[night/props-ab.sh](07-step3-paced-take/night/props-ab.sh): 005-46's
props.sh, four rounds of each build in turns (ABBA), 20:33 to 20:41. The
output stayed in `/Users/f/fl/bench/006-10/w1props/night/out/`.

| property | main-cefb473 | d4b-f89846d | change |
|---|---|---|---|
| MEM (bytes a KV) | 130 in all 4 rounds | 129 in all 4 rounds | -1 |
| CORE (lower is faster; get, get4t, getmany, set) | mean 0.237 (0.23 to 0.24) | mean 0.240 (0.24 in all rounds) | +0.003, within a round's step |
| SS | 1.50 | 1.51 | +0.01 |
| SS1 (1 kB KVs, 100 a transaction) | 1.10 | 1.10 | 0 |
| SS2 (1 kB KVs, 1 a transaction) | 1.19 | 1.20 | +0.01 |
| SS3 (100-byte KVs, 100 a transaction) | 1.62 | 1.65 | +0.03 |
| SS4 (100-byte KVs, 1 a transaction) | 2.37 | 2.40 | +0.03 |

CORE's parts moved within their noise: set 0.28 to 0.29 before, 0.30 to
0.31 after, the others the same. MEM and SS do not depend on the machine:
every round of a build gave the same values. Level1's logs agree on the
SS before 007-07: `SS:1.50 (1.10, 1.19, 1.62, 2.37)` in every night run
from 2026-10-23 to 2026-10-28 02:10, and `SS:1.51 (1.10, 1.20, 1.65,
2.40)` at 18:22, after 007-07.

### 12.3 SS against level1's limits

level1.sh (step 6) has `SS_MAX="1.51 1.11 1.20 1.63 2.38"`: the values of
2026-10-19 plus one step of 0.01 for other machines. Its rule: "a change
that needs a higher one needs a reason in docs/log.md".

| | SS | SS1 | SS2 | SS3 | SS4 |
|---|---|---|---|---|---|
| before 007-07 | 1.50 | 1.10 | 1.19 | 1.62 | 2.37 |
| after 007-07 | 1.51 | 1.10 | 1.20 | 1.65 | 2.40 |
| raised by | 0.01 | 0 | 0.01 | 0.03 (1.9 %) | 0.03 (1.3 %) |
| level1's limit | 1.51 | 1.11 | 1.20 | 1.63 | 2.38 |
| after 007-07 against it | at it | below | at it | over by 0.02 | over by 0.02 |

SS3 and SS4 fail; SS and SS2 pass only at the limit, without the step
for other machines that the limits are meant to have.

Why: the SS scenarios use the default startup distance, 50 MB, and each
writes 100 MB of user data, 110 to 240 MB of stream, so the take works
for 2 to 5 sd of each run. 007-07 makes the setting the section's target
(005-49, in Frans's terms): the paced take holds the section at about
the setting, where the old take let it grow past it. The same setting
then holds a smaller section and pays it off sooner, which writes more.
docs/levels.md, section 5, gives the size of it at 50 MB with small KVs
(10M keys, 32-byte puts): 867 against 699 bytes a put, 24 percent more.
In the SS scenarios the user's data are most of the stream and the keys
fewer (100k of 1 kB, 1M of 100 bytes), so the rise is 0 to 2 percent,
largest where the KVs are small (SS3, SS4). That is the expected cost of
the bound, not a regression. The section sizes in the SS runs themselves
were not logged; this is the reading of docs/levels.md's figure, which
007-06 and section 10.4 measured.

**Recommendation for Frans:** raise level1.sh's limits to the new values
plus the one noise step:

    SS_MAX="1.52 1.11 1.21 1.66 2.41"   # SS, then SS1 to SS4

(SS1 unchanged), change step 6's comment to say that the SS limits are
the values of 2026-10-28 (`f89846d`, 007-07), and add to docs/log.md, as
the rule asks, something like:

> 2026-10-29. level1.sh's SS limits raised to 1.52 1.11 1.21 1.66 2.41
> (from 1.51 1.11 1.20 1.63 2.38). 007-07's paced take holds the startup
> section at the startup distance, the setting being the section's
> target (005-49), where the old take let it grow past it; at Props' 50 MB
> it pays the section off sooner and writes more: SS 1.50 to 1.51, SS2
> 1.19 to 1.20, SS3 1.62 to 1.65, SS4 2.37 to 2.40, SS1 unchanged (bergdb
> 007-07, section 12). The same cause as docs/levels.md's 24 percent at
> 50 MB with 32-byte puts. The limits keep one step of 0.01 above the new
> values.

level1.sh is not changed here; Frans decides. Until then night.sh's
level1 fails on main.

### 12.4 Section 8's quick performance suite

**Done, in substance:** 007-03's step 3 asks for "the quick performance
suite unchanged", and it is: every throughput within -0.3 to +1.3 %
(gets +4.4 %), the bytes a put the same, no alerts. What did change is
small and explained: the commit's p99 and p99.9 under finite retention
up 9 to 11 percent (about 6 and 10 µs), the median commit down, and the
startup 1 to 4 percent longer. The runs were not in a quiet block, so
they are not a reference; with 3 runs a build in ABBA order and CVs of
0.1 to 2 percent on the metrics above, a quiet rerun would refine the
figures, not the verdict. Of section 8 there remain the Lean comments
(step 4), and of 10.5 the questions there.


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
  (section 10.5); `night/props-ab.sh`: Props before and after 007-07;
  `night/results-quick-2026-10-28.md`: the quick suite's comparison
  (section 12).
* `step2-50m/`: section 11's runs at 50M keys: `run50.sh`, `queue50.sh`,
  `cmp50.py`, `big.py` and `share.py` (with 007-06's `pick.py`,
  `summary.py` and `tables.py` and 10.4's `ratchet.py` beside them), and
  the outputs `runs.txt`, `summary.txt`, `tables.txt`, `big.txt`,
  `ratchet.txt` and `share.txt`.
