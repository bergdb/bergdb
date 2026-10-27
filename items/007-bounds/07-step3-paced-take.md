007-07. Step 3 as a patch: the paced take with the deadline
===========================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code) for Frans Lundberg
(006-09, W10), at his choice (17:27): "007-03 step 3 as a patch". Status:
the patch is ready for review, gated in a scratch clone; it is not in
`java/` and not committed to main, since every stream changes. Frans
decides.

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

### 7.4 Existing databases

A database whose section today's take left past 2 × sd (up to 2.75 sd at
50 MB in 005-49's runs) gets the deadline at its first commits after the
patch, with a series of records as in 7.3. Once; not measured.


## 8. What remains of step 3's "Done when"

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

1. Apply the patch? Every stream changes; the format does not.
2. Sections 7.1 and 7.2: accept that a small commit after a large take can
   write a whole transaction, as with the old take, or a pace by nodes (a
   model change, with step 4)?
3. Section 7.3: D4:B inside `setStartupDistance` now, and how, or the
   caller's steps as the Javadoc now says?


## Files

In [07-step3-paced-take/](07-step3-paced-take/):

* `step3.diff`: the patch, `git diff 2eaaa45` of the clone's commit.
* `ShareProbe.java`, `TakeProbe.java`, `DecreaseProbe.java`,
  `MixedProbe.java`: the probes behind sections 2, 3 and 7, in package
  `bergdb.core`; compile against a build's bergdb.jar and put the classes
  first on the class path.
* `level2-step7.sh`: level2.sh's step 7 on its own (section 4).
* `digest-summary.txt`, `digest-base.txt`, `digest-patch.txt`:
  StreamDigest (section 5).
