028-26. Fix: reclaim's allowance charge omits the index nodes that PE creates
============================================================================

Status: in progress. Kind: Fix. Frans: decision.
Created 2026-11-19 by Frans Lundberg.

What: a reclaim step's row (`/#i/dreclaim/-current.txt`) is made by a
value transformation (`Reclaim.step`) that runs in `Db.putKvs` before the
writer gets the step's operations as one batch (record format 8, the
writer PE, 026-25). So the row's `rewritten` holds the bytes of the index
nodes that the step's touch made dirty (`Trans.dirtiedBytes` then), and
not those of the nodes that the batch then makes dirty: PE's replacement,
cut and joined nodes, and a new top node. `endOfOp` adds them to
`Trans.dirtiedBytes` after the row is made, and nothing charged them, in
the row or in the iteration's counter in memory; a restart kept the
charge as stored. Reclaim's own comment (011-04, "Level 3 cost") says the
allowance charges the index nodes that the step makes dirty, by its puts
and its touch.

Why: found by an independent Codex review of Java's PE (merge 9bcbeea8),
2026-11-19, finding 1 (P2): pacing and write amplification, not an unsafe
cut or a lost value. In its probe (the workload of
`Reclaim.Tester.testAllowanceCountsIndexNodes` with keys `/!k/N`, which
sort before the row's key), the first iteration charged 211,024 of the
301,856 bytes that its steps made dirty at node size 8 (90,832 omitted)
and 161,696 of 211,520 at node size 30 (49,824 omitted); the old writer,
applying the operations one by one, omitted 2,304 at node size 8 (the
puts after the row's key). 026-25, section 2, had disclosed the change
("a reclaim step's row now stores only the bytes its touch made dirty"),
for Frans to confirm; he confirmed it on 2026-11-19 as recommended, and
the review showed it is a defect: coord-1118 registered this fix, with
Frans's priority of the day, "Stability and bug fixes are prio."

Frans: decision (section Decision): option A, made and gated on the
branch, adds an internal record after most reclaim steps, which changes
the stream and adds a mechanism; coord-1118 holds the landing for Frans's
word.

Done when: the charge, in the row as stored and in the counter in
memory, includes the bytes of every index node that the step's
transaction makes dirty, PE's new nodes included; a unit test of the
probe's scenario at node sizes 8 and 30 that fails before the fix;
`java/before-commit.sh`, `level1.sh`, `level2.sh` and `level3.sh` full,
`kill-restart.sh 1000` with one seed; 027-13, 026-25 section 2, 028-19
and `releases/next.md` updated.

First step: read the review's finding 1 and its probe
(/Users/f/fl/bench/2026-11-19/codex-pe/, not kept in Git).


Decision
--------

The fault: since record format 8, a reclaim step's charge leaves out the
index nodes that the writer makes for the step's batch (replacements,
cuts, joins, a new top node), because the row that stores the charge is
made before the batch. In Codex's probe that is 30 % of the index bytes
that the first iteration made dirty at node size 8 (90,832 of 301,856)
and 24 % at node size 30 (49,824 of 211,520); with the old writer it was
under 1 % (2,304). Reclaim then rewrites more than its fraction f of the
stream's growth. The choice is how to charge those bytes, or whether to.

* **A. The row stored again after the step (made and gated; recommended).**
  After the step's transaction commits, the step adds the bytes that its
  batch made dirty after the row was made (`Trans.dirtiedBytes` at the
  end less what the row counted) to the row's `rewritten`, and, if they
  are more than 0, stores the row again at `/#i/dreclaim/-current.txt`
  in an internal transaction of its own; after the iteration's last step
  the row stored done with the table holds them, with no extra
  transaction. The charge is exact, in memory and in the stream, after
  every call, so a restart resumes with the same charge and INV-RESTART
  holds (StreamDigest: each l3-* configuration's four modes, plain,
  reads, restarts and restarts-once, give one digest). Cost: one more
  internal record after most steps, about 400 bytes besides the index
  nodes that its take writes (a record header and the row's value node);
  in a run of 20,000 updates at node size 8, 912 such records for 981
  steps, about 375 kB of 38.8 MB of growth (1 %; about 410 bytes each,
  the records' bytes less their index nodes, less those of the table's
  121 records at their average before). The bytes that this
  record makes dirty itself are not charged, as those of the table's
  transactions are not. Effect: reclaim keeps closer to f; the stream
  grew 1.5 to 7.8 % less in the probe's workloads, with 7 to 23 % fewer
  steps; StreamDigest's l3-* digests changed (+1.7 %, -4.1 %, -0.8 %,
  -6.9 % in length), l2-* identical. No change of the record format or
  of the row's text; one mechanism more (`Reclaim.storeCurrent`, 20
  lines); internal transactions after a user transaction at most six,
  not five. A crash between the step and its second record loses that
  step's new nodes from the charge (a crash only; a clean restart does
  not).
* **B. Keep the undercount, documented.** No code change: 027-13 says
  that the row counts the touch's nodes only and that PE's new nodes are
  not charged, and 028-19 measures reclaim's pace at 10M keys with it.
  Cost: reclaim rewrites more than f of the growth, by about the share
  above (in the probe, 1.5 to 7.8 % more stream growth than A); the
  comment in Reclaim (011-04, "Level 3 cost") that the allowance charges
  the nodes of the puts and the touch stays untrue. No stream change
  against main today.
* **C. Carry the post-batch bytes into the next step's row.** As A, but
  without the second record: the bytes are added in memory at once and
  stored with the next step's row, or with the row stored done. Made
  first (11:15) and refused by `before-commit.sh`:
  `DbTesterRestart.testReclaimSettingsKeptOverRestarts`, "the decided
  cut, expected 1240592, got 1441224". A restart between two steps loses
  the carry, the last step's new nodes (about 2.8 kB a step on average at
  node size 8 in the probe, 90,832 bytes over 33 steps), as nothing that a
  start reads holds it; the run with restarts then paces its steps
  otherwise and writes another stream, so INV-RESTART (027-13, section 3;
  RestartInvariance in level 3, StreamDigest's restarts modes) fails. To
  keep the carry over a restart it would have to be written, which is A.
* **D. Count PE's nodes before they are made** (in the plan, before the
  emit), so that the step's own row is exact. Not possible without
  changing the stream: PE makes a value node, and gives it its id, when
  the plan applies its operation at its segment leaf, and emits a
  segment tree's new nodes during the plan, before the leaf's later
  operations (026-25, section 2, "The ids"); the row's value is needed
  before the nodes it would count exist. Running the plan twice, or
  reordering the ids, changes PeWriter and the ids that the model proves.
* **E. Write the charge into the row's value node after the batch.**
  Exact and without a record, but it changes a value that is already a
  node (`ValueNode.value` is immutable, and the trace records the value
  when the node is made), and the row's text would need a fixed width
  for its number. Not tried.

**Recommendation: A.** It is the only option that charges what the
allowance says it charges, exactly and over restarts, without touching
the writer or the record format; its cost, about 1 % of the growth in
records of the row, is smaller than what it saves (1.5 to 7.8 % of the
growth in the probe). B leaves a known accounting defect in reclaim's
pacing; C breaks INV-RESTART; D and E change the writer or a node after
it is made. Whether A's saving holds at 10M keys is 028-19's measurement
(Measurements, "For 028-19").


The fix (option A)
------------------

**The mechanism: the row stored again after the step.** After a step's
transaction has committed, `Reclaim.step` adds to the row's `rewritten`
the bytes that the batch made dirty after the row was made
(`t.dirtiedBytes` less what the row stored) and, if they are more than
0, stores the row again at `/#i/dreclaim/-current.txt` in an internal
transaction of its own (`Reclaim.storeCurrent`); after an iteration's
last step the row stored done with the table holds them, with no extra
transaction. So, after every call of `transactionCompleted` (and of
`maintain`), the row in the stream is the row in memory, and its charge
is every byte that the steps made dirty.

**Why this one.** The row is a value of the transaction whose dirty bytes
it must count, so no value of that transaction can hold the bytes that
its batch makes dirty:

* **A carry** (the bytes added in memory and stored with the next step's
  row) was made first and failed `before-commit.sh`:
  `DbTesterRestart.testReclaimSettingsKeptOverRestarts` ("the decided
  cut, expected 1240592, got 1441224"). A restart between two steps
  loses the carry, so the run with restarts paces its steps otherwise and
  writes another stream: INV-RESTART (027-13, section 3; RestartInvariance
  in level 3) does not hold. Nothing that a start reads gives the carry
  back.
* **Counting PE's nodes before they are made** (in the plan, before the
  emit) is not possible without changing the stream: PE makes a value
  node, and gives it its id, when the plan applies its operation at its
  segment leaf, and emits a segment tree's new nodes during the plan,
  before the leaf's later operations (026-25, section 2, "The ids"); the
  row's value is needed before nodes whose bytes it would count are made.
* **Writing the row's bytes into its value node after the batch** would
  break the value node's immutability and the trace, which records the
  value when the node is made.

The second transaction costs a record of its own, about 400 bytes
besides the index nodes that its take writes (a header, the row's value
node), for each step whose batch made nodes (about 93 % of the steps in
the longer run below, about 1 % of the stream's growth), and the bytes it
makes dirty itself are not charged, as those of the transactions that
store the table are not. The record format, the row's text and the
stream's layout are unchanged; a stream gets one more internal record
for most steps. A crash between the step and its second transaction
loses that step's new nodes from the charge, which a crash may (a clean
restart does not).

Code: `java/src/bergdb/core/Reclaim.java` (`step`, `storeCurrent`,
`Stats.Iteration.dirtiedAfterRow` and `rowRecords`), comments in
`Db.java` (`putKvs`, `transformValues`).


Tests
-----

`Reclaim.Tester.testAllowanceCountsNodesMadeAfterTheRow`, the probe's
scenario at node sizes 8 and 30: 3,000 keys `/!k/N` of 10-byte values,
startup distance 2,000, retention one second, random updates until the
first iteration is done. After each user transaction from the first step
on, the row in memory charges the steps' values and every byte they made
dirty, and equals the row stored at `/#i/dreclaim/-current.txt`; the row
stored done charges the same; some step's batch made nodes after its
row. On the code before the fix it fails: "M=8, charged in memory,
expected 12848, got 9488". Reclaim's other tests, the f-tests of
`DbTesterRestart` and the gates pass (State).


Measurements
------------

Codex's probe (`ReclaimPaceProbe`, the first iteration; charged = the
index bytes the rows charge):

* node size 8: before, 33 steps, 211,024 of 301,856 bytes charged
  (90,832 omitted), the row's `rewritten` 365,161, the steps' records
  253,808 bytes; after, 32 steps, 298,960 of 298,960 (0 omitted), the row
  446,151, the steps' records 245,416;
* node size 30: before, 34 steps, 161,696 of 211,520 (49,824 omitted),
  the row 318,361, the steps' records 241,832; after, 33 steps, 216,208 of
  216,208, the row 369,359, the steps' records 232,552.

With keys `/k/N` (after the row's key, the existing test's), before: 27,312
of 304,512 omitted at node size 8, 16,800 of 250,000 at node size 30.

A longer run of the same workload (a probe of this entry, 20,000 user
updates after the load, the same seed; stream growth over the updates;
before = the classes of main a0a76461):

* node size 8, keys `/!k/N`: growth 42.05 MB before, 38.78 MB after
  (-7.8 %); steps 1,273 and 981; iterations done 38 and 30; the
  internal records that store the table or the row 153 and 1,033;
* node size 8, keys `/k/N`: 40.80 and 38.51 MB (-5.6 %); steps 1,031 and
  846;
* node size 30, keys `/!k/N`: 45.30 and 44.12 MB (-2.6 %); steps 1,374
  and 1,222;
* node size 30, keys `/k/N`: 44.59 and 43.94 MB (-1.5 %); steps 1,009
  and 941.

The charge now covers what the steps make dirty, so reclaim takes fewer
and later steps for the same growth, and the stream grows less. With a
startup distance of 2,000 bytes every record takes the dirty nodes then
due, so the rows' own records carry index nodes that the user records
carried before; only the total is compared.

**StreamDigest** (`java/stress/StreamDigest.java quick`, before = main
a0a76461's Reclaim classes, after = dfc3c55e): the l2-* configurations
(no reclaim) are identical; every l3-* configuration changed, its four
modes (plain, reads, restarts, restarts-once) still one digest each. The
plain mode's length, firstAvailablePos and sha256 (the stream from the
decided cut):

    l3-every1   before 1808736 1632608 731ebc7dc44d441caa592590df9dbc4aa9cce947bad777f03e981c8fa7b9fa71
                after  1839088 1611392 47b08c257b3b24904203d467dce6a19fb1e3b203d954db29b872caaa4aae81c7
    l3-node8    before 6323200 5461496 33965d4236baf2447db251853492608cbce645435432e5885af040cd8450c124
                after  6063664 5312160 ad41a52b955d92c0f68e98de62d1d547c6a6fd31a4146cbda6f0ccf7870b7424
    l3-node14   before 1528208 1390752 ec6969c11e7585d7bdc7cec91b1ca73033ccca99273ceba035cae3818dcdcdbe
                after  1515600 1394944 a5601457a2f876ab0aa0affb74c9313a2de112cffcfd664c7a874a13fa6edfe9
    l3-node62   before 8347896 7227056 b12ca730ea64fa7ba5606bbc954689bcf8cb1ca24f40b64b76decaa741acca46
                after  7771824 6757744 e423f31cec2cf06812f37f444abd0a15c9c6f39de2fd7ef6888e14728ed29082

The lengths: +1.7 %, -4.1 %, -0.8 %, -6.9 %; l3-every1, of 1,000
transactions with a restart after each, grows by the rows' records.

**For 028-19** (timing at 10M keys): remeasure Perf write with reclaim
(retention 0.1 updates a key) on F53 and s1 as 026-25, section 7: bytes
a put (1,348 against main's 1,262 before this fix), physical cuts in 6M
transactions (3 against 1), the stream kept at most, reclaim's steps and
their records, and the worst commit; and CCBench's cases with history
kept as a control (no change expected: no reclaim).


State
-----

2026-11-19, 13:12. **GATED e27141f4** (the code; later commits change
items only), on the branch `028-26-reclaim-charge` in
/Users/f/fl/bench/2026-11-19/rch/clone, with main 5bdb6773 (028-20,
028-23) and 028-21's branch 94ecce18 merged: BEFORE COMMIT OK (152 s),
LEVEL 1 OK, LEVEL 3 OK, LEVEL 2 OK (full), KILL RESTART OK (1,000 kills
and 50 exits, seed 20261126). Not merged into main, not pushed: the
landing waits for Frans's choice in Decision (A recommended).


Log
---

2026-11-19. Registered by coord-1118 from Codex's review of PE, finding
1; taken by an agent of coord-1118, on the branch
`028-26-reclaim-charge` in /Users/f/fl/bench/2026-11-19/rch/clone (from
main a0a76461). The carry (11:15) failed `before-commit.sh`'s restart
test; the row stored again after the step (11:25).
Before-commit and level 1 passed on dfc3c55e (11:30, 11:36); the chain
stopped at coord-1118's word to merge main (028-20, 028-23) and 028-21's
branch (94ecce18) first. `testLastStepWithinRecordLimit`'s comment
brought to 028-21's bound (a probe of its user transactions: at most 902
index nodes, 175 kB; 866 with the bound before 028-21, on PE's trees).
Gated on e27141f4 from 11:59 to 13:11 (State). The Decision section
at coord-1118's word: option A changes the stream and adds a mechanism,
so the landing waits for Frans.
