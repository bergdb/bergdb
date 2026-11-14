028-12. Investigate: can the take's byte limit stop the startup section's bound?
================================================================================

Status: done (2026-11-14). Kind: Investigate. Frans: decision (A; the
answer needs none).
Created 2026-11-13 by Frans Lundberg.

What: `TransSeq.take` stops at the first transaction whose taken nodes
do not fit in `maxBytes`, the room left in the record, also after the
deadline (its Javadoc: "It matters for records near the record limit
only"). Today's Lean (prover "t44", 007, `SIS/BoundTakeBytes.lean`,
checkpoint 183c2ec7) proves T3's bound for this take when the debt's
nodes always fit (`T3_takeB`: nodeB·|D| ≤ maxB before every
transaction), and refutes it without that, by two runs checked by
running (`BoundTakeBytesExample`): a transaction whose nodes never fit
is never taken, so the span grows by a record each time; and even when
each fits, a costly record leaves cheap ones queued behind the limit,
and the span reaches 103 against 2M = 6.

Why: bounded startup (007, Frans's top priority since 2026-10-23) rests
on T3: the startup section stays below 2 sd. If the byte limit can hold
the take back in Java, the section is not bounded. 005-31 (007-02) fixed
the case of a single transaction that never fits; the second case is
new.

Frans: none; the answer is: whether Java's runs can reach it (the room
left in a record against the bytes of D's nodes, at 1M to 100M keys and
the record limit), and if they can, a proposal.

Done when: a measurement or an argument from the code that says whether
`bytes + cost > maxBytes` stops a take past the deadline in Java's runs
(007-06's debt test drives the debt up; its runs or a probe give the
numbers), written here with the numbers; if it can, a proposal (for
example: past the deadline, take at least one transaction, or bound D's
bytes) for Frans.

First step: read `TransSeq.take`, where `maxBytes` comes from
(`StoredTrans.recordLimit`, the record's own bytes), and 007-06's
largest debt in bytes.


1. The answer
-------------

**No, not in Java's runs.** In none of the 18 runs here (counts, on main
`f4282972`) did the byte limit stop a take at a transaction past the
deadline (a "stop"). 007-06's and 007-07's runs did not count stops, but
their debt stayed below 1 GB, under half the room, so none of them could
stop either. Without a stop, the limit only holds back the pace, and T3
holds for every pace (007-08), so T3's bound applies to these runs as it
is: the section stayed below 2 sd in every one. The margin at the real
record limit is large:

* The room left in a record is at least 2,114 MB (the record limit,
  2,147 MB, less a record's own part, at most about 34 MB by L5).
* The whole debt, every node of D, is at most half of that room in the
  runs at the real limit (1.07 GB, at 10M keys with sd 2^31 - 1; at most
  0.28 of it with sd up to 10^9), and at most 849 MB in 007-07's runs at
  50M keys. So `T3_takeB`'s premise, the whole debt fits, held in every
  record of every run: the Lean theorem applies to them directly.
* The deadline took nothing in any run at the real limit with sd 50 MB
  or more: the pace keeps the section at 1.04 to 1.31 sd. Where it did
  take (sd 10 MB with records of 41 MB, 4 sd each, the shape of the Lean
  example's case 2), it took at most 624 bytes in a record.
* The largest got-dirty set of one transaction was 9.6 MB, against the
  2,114 MB room: 005-31's premise (`T3_takeB_count`'s) holds with a
  margin of 220.

With the record limit lowered (scaled runs, section 4), the debt was up to
54 times the room, and costly records up to 85 percent of the limit,
far beyond what L5 allows at the real limit (1.6 percent); still no stop:
the deadline's due part was at most 0.78 of the room. The deadline makes
due only a window about one record long, which the pace has partly taken
already; the Lean example's case 2 has no pace and records that carry more
nodes than the room (section 4).

The limit could stop a take only with a debt of more than about 2.1 GB,
which needs a startup distance near the largest DbBuilder allows (2^31 -
1) and many more keys than measured; and then only if the deadline has to
take more than 2.1 GB in one record, which no run came near (section 5).
Section 6 proposes to close that corner: DbBuilder takes at most 10^9,
as `setStartupDistance` does.


2. From the code
----------------

`maxBytes` (`Db.store`, 2026-10-21, bergdb 005-17) is
`StoredTrans.recordLimit - fixedBytes`:

* `recordLimit` is `MAX_RECORD_SIZE` = 2^31 - 9 = 2,147,483,639 bytes
  (the record's size field is an int); only tests lower it.
* `fixedBytes` is the record's own part: its own bytes (48 and its value
  nodes, `TransSeq.ownBytes`), 16 bytes for each of its transaction's
  got-dirty nodes, and its own top and key nodes with 16 bytes each.
* A user transaction has at most 500 operations (L1), values of at most 8
  MiB (L4) and 32 MiB of keys and values (L5), so its own bytes are at most
  about 34 MB. A reclaim step puts about 16 kB of KVs and at most one more
  value (8 MiB); `setStartupDistance` puts 200 kB; `maintain` puts none.
* So the room is at least about 2,147 - 34 MB less the got-dirty list:
  2,114 MB in the probe's runs with 33 MB transactions, 2,147 MB without.
* `StoredTrans.valueLimit` (7/8 of the limit) and `dirtyLimit` (15/16)
  are far above L5 at the real limit; they matter only where tests lower
  the limit.

What a stop needs. The take stops past the deadline only at a due
transaction (one that begins at or before hardSp) whose nodes, with those
taken before it in the record, pass the room. Due nodes are D's nodes, so
a stop needs more than the room in D: a debt over 2,114 MB, or a single
transaction's got-dirty set over it.

* **One transaction (005-31's premise; the coordinator's question (a)).**
  `Db.checkDirtyNodes` refuses a user transaction whose puts and deletes
  could make dirty more than `dirtyLimit()`, 15/16 of the limit (2,013 MB),
  at the largest node size. A record's own part is at most about 34 MB
  plus its got-dirty list (at most about 59 MB by the same bound), well
  below the 1/16 (134 MB) that the bound leaves. So the nodes that a user
  transaction's own operations make dirty always fit in the room, in any
  later record. Not covered by the check: the parents that the record's
  own writes make dirty (writing a taken node moves it, so its parent gets
  dirty in the writing transaction; 007-06, section 1). They are at most
  as many as the nodes the record took, so they are bounded by the take,
  not by a constant; measured, the largest got-dirty set of any
  transaction was 9.6 MB (in r10m-big-sd1000, whose records of 33 MB
  transactions took up to 30 MB of nodes). A gap in the argument, not in
  the runs: 220 times below the room.
* **The whole debt (`T3_takeB`'s premise).** Nothing in the code bounds D
  in bytes. Measured, the paced take holds it at about sd or less: 0.47 to
  1.10 sd in 007-06's and 007-07's runs (10M and 50M keys, sd 50 to 1000
  MB), 0.50 to 1.02 sd here at the real limit. `setStartupDistance` clamps
  the setting to 10^9; `DbBuilder.startupDistance` allows up to 2^31 - 1.


3. The runs at the real limit
-----------------------------

The probe, [TakeBytesProbe.java](TakeBytesProbe.java), runs a database in
memory as 007-06's WriteBench does (no eviction, every version kept), with
a hook after every record. It recomputes the deadline that `take` used
(the stream's length at the record, less the larger of 2 sd and the span
before it) and counts a stop when the oldest transaction left after the
take began at or before it. It also logs the span after each take (the
section without its last record, T3's quantity), the debt (the sum of
`TransSeq.recordBytes` over the queue, walked every sd/200 of stream),
the room (the limit less the record's bytes other than the nodes it took,
a lower bound), the records whose take took a due transaction, the due
bytes taken, and the largest got-dirty set of one transaction.
[run.sh](run.sh) runs one; [queue-1m.sh](queue-1m.sh),
[queue-10m.sh](queue-10m.sh) and [queue-scaled.sh](queue-scaled.sh) are
the runs. The outputs are in [out/](out/). Each run loads the keys (24
bytes, 8-byte values, random order, 500 puts a transaction, L1) and then
makes random updates; "one" is single puts; "big" adds a transaction of 33
MB (four values of 8 MiB, near L5) every 100, 10 or 200 update
transactions, at most 40 to 60 of them. Counts, not timing.

The columns: stops past the deadline; the span's maximum in sd; the
debt's maximum in MB (and sd); the least room in MB; the debt against the
room, at most; the largest record, the largest take and the largest
got-dirty set of one transaction, in MB; the records in which the
deadline took a transaction; and the most due bytes one take took, in MB
(and against that record's room). Over the update phase.

| run | stops | span | debt | room | debt / room | record | take | one tx | deadline | due |
|---|---|---|---|---|---|---|---|---|---|---|
| r1m-sd50 | 0 | 1.09 | 36.8 (0.74 sd) | 2147 | 0.0171 | 0.29 | 0.26 | 0.21 | 0 | 0 |
| r1m-sd1000 | 0 | 1.04 | 543 (0.54 sd) | 2147 | 0.253 | 0.24 | 0.21 | 0.21 | 0 | 0 |
| r1m-one-sd50 | 0 | 1.06 | 32.8 (0.66 sd) | 2147 | 0.0153 | 0.24 | 0.21 | 0.21 | 0 | 0 |
| r1m-big-sd50 | 0 | 1.31 | 38.6 (0.77 sd) | 2115 | 0.018 | 65.4 | 33.8 | 1.6 | 0 | 0 |
| r1m-big-sd10 | 0 | 1.15 | 10.2 (1.02 sd) | 2115 | 0.0047 | 41.5 | 8.9 | 0.55 | 60 | 0.001 (0.00) |
| r10m-sd1000 | 0 | 1.06 | 574 (0.57 sd) | 2147 | 0.267 | 0.30 | 0.27 | 0.27 | 0 | 0 |
| r10m-sdmax | 0 | 1.04 | 1071 (0.50 sd) | 2147 | 0.499 | 0.30 | 0.27 | 0.27 | 0 | 0 |
| r10m-big-sd1000 | 0 | 1.17 | 604 (0.60 sd) | 2115 | 0.281 | 62.4 | 30.2 | 9.6 | 0 | 0 |

* **No stop, and the section at most 1.31 sd.** The debt is 0.50 to 1.02
  sd, as in 007-06 and 007-07, and at most 0.28 of the room with sd up to
  10^9, 0.50 with sd = 2^31 - 1.
* **sd = 2^31 - 1** (r10m-sdmax, possible only through DbBuilder): the
  debt reached 1.07 GB, 0.50 sd at 10M keys. 007-07 measured 0.85 sd at
  50M keys and sd 1000 MB; at that ratio, 2^31 - 1 would carry a debt of
  about 1.8 GB, near the room.
* **Costly records** (big): each takes a large share of D, as the pace
  gives shares by own bytes, so records reach 41 to 65 MB. The deadline
  never fires at sd 50 MB or more. At sd 10 MB, records of 4 sd move the
  deadline past most of the section, as in the Lean example's case 2, and
  the deadline took in 60 records, but the costly record's own share had
  already taken nearly all of D: at most 624 bytes were due.


4. Scaled runs: the debt far above the room
-------------------------------------------

To see what the limit does when `T3_takeB`'s premise fails, these runs
lower `StoredTrans.recordLimit` (as DbTester does) to 4.88, 1 or 0.5 MB,
with sd 5 MB and 1M keys, so the debt is 1 to 54 times the room. The
costly records (big) are 1.6 percent of the limit (as L5 is at the real
limit), or 80 to 85 percent of it, which no record can be at the real
limit. Columns as in section 3, in kB.

| run | stops | span | debt | room | debt / room | record | take | one tx | deadline | due |
|---|---|---|---|---|---|---|---|---|---|---|
| s-r4.9 | 0 | 1.17 | 5445 (1.09 sd) | 4870 | 1.12 | 189 | 184 | 127 | 0 | 0 |
| s-r4.9-big78k | 0 | 1.27 | 5871 (1.17 sd) | 4807 | 1.21 | 778 | 719 | 273 | 0 | 0 |
| s-r1 | 0 | 1.17 | 5445 (1.09 sd) | 990 | 5.49 | 189 | 184 | 127 | 0 | 0 |
| s-r1-big800k | 0 | 2.00 | 7923 (1.58 sd) | 199 | 25.1 | 997 | 734 | 409 | 62 | 734 (0.73) |
| s-r0.5 | 0 | 1.10 | 5042 (1.01 sd) | 495 | 10.2 | 94.3 | 92.0 | 64.8 | 0 | 0 |
| s-r0.5-big400k | 0 | 2.00 | 8697 (1.74 sd) | 99.6 | 53.5 | 498 | 339 | 221 | 70 | 339 (0.77) |
| s-r1-one | 0 | 1.07 | 4734 (0.91 sd) | 991 | 4.77 | 153 | 148 | 105 | 0 | 0 |
| s-r1-one-big800k | 0 | 2.00 | 6637 (1.33 sd) | 203 | 19.7 | 996 | 292 | 112 | 22 | 292 (0.29) |
| s-r1-sd1-big850k | 0 | 2.00 | 2195 (2.19 sd) | 149 | 10.9 | 979 | 790 | 281 | 126 | 790 (0.78) |
| s-r1-one-big850k | 0 | 2.00 | 5809 (1.16 sd) | 149 | 27.2 | 993 | 618 | 202 | 16 | 618 (0.61) |

* **No stop in any of them**, also with the debt 54 times the room
  (s-r0.5-big400k) and records of 85 percent of the limit. The span
  reached 2 sd (just below it) in the runs with costly records of 80 to 85
  percent: the deadline took in 16 to 126 records.
* **The due part stayed below the room**: at most 0.78 of the record's
  room (790 kB of 1 MB), though the debt was 11 to 54 times the room.
  The deadline makes due only what lies in a window about one record
  long, and the pace had taken part of it.
* **Why Java escapes the Lean example's case 2.** A costly record moves
  the deadline by its length, and the next record must take what lies in
  that window. In the example every cheap record carries nodes worth more
  than the room per byte of record, and nothing has taken them (`noPace`).
  In Java the pace has taken part of the window before it is due, and the
  rest is about the window's length in nodes or less (here at most 790 kB
  for windows of about 1 MB, the largest take of these runs). At the real
  limit the room is 60 times the largest record's own part, and the
  costly record's own share (in proportion to its own bytes, 005-49) takes
  most of D at once: in r1m-big-sd10 the deadline then found at most 624
  bytes due.
* With the limit at 4.88 MB and sd 5 MB, the real limit's ratio at sd =
  2^31 - 1, the debt was up to 1.21 times the room, and the deadline took
  nothing.


5. Can it happen?
-----------------

A stop needs a due part over the room in one record: over 2,114 MB at
the real limit. That needs a debt over 2,114 MB, and the deadline to take
most of it at once.

* **The debt.** About sd or less in every measured run; at most 1.07 GB
  here and 849 MB at 50M keys in 007-07. With `setStartupDistance`'s range
  (at most 10^9) the debt would have to be over twice the setting, which
  no workload measured comes near (the most is 1.10 sd, 007-07, 11.1). With
  DbBuilder's 2^31 - 1, a debt near the room is plausible at 50M keys or
  more.
* **The deadline taking it at once.** The deadline makes due, a record at
  a time, the transactions in a window about as long as the record before
  it (the stream grows by it), or as the costly record that just left the
  section. Each got-dirty node of a due transaction has a 16-byte entry in
  that transaction's record, and is at most 528 + 16 bytes when written
  (node size 30), so the due part is at most 34 times the window's bytes.
  A stop at the real limit needs a window of more than about 62 MB of
  records dense in got-dirty entries, and the pace more than 1 sd behind.
  In every run the deadline took nothing at sd 50 MB or more, and records
  were at most 65 MB, those of 33 MB transactions whose share took most of
  D at once (so little was left for the deadline).
* **Workloads tried** to make it happen: costly records (33 MB, every 10
  to 200 transactions, at sd 10 and 50 MB, and 1000 MB at 10M keys),
  single puts (up to about 2,000 got-dirty nodes in a 32 kB record),
  sd = 2^31 - 1. None stopped. In the scaled runs the debt was up to
  54 times the room and the most due in one record 0.78 of the room.

So the Lean example's case 2 needs what Java's limits prevent: a record that is
costly against a room that is small against the debt. At the real limit
L5 makes every record's own part at most 1.6 percent of the room, and the
debt stays near sd.

What `T3_takeB_count` adds (SIS/BoundTakeBytesCountTheorems.lean,
checkpoint 418ab85d; the coordinator's question (b)). With 005-31's
premise, the take with the limit keeps the section at fewer than 2M/m + 2
transactions, m the least record. In Java m is about 100 bytes (a single
put's record), so at sd 50 MB the count bound allows about a million
transactions; with records of up to 34 MB own, that bounds the cost at
far more than 2 sd. So in Java the count bound alone does not bound
startup; what does is that no take stops past the deadline, which these
runs show and which a debt below the room guarantees (`T3_takeB`). A
theorem that would match Java's runs more closely, for the prover: T3's
bound in cost for the byte-limited take when no take stops at a due
transaction (then the limit acts only as a pace, and T3 holds for every
pace).


6. Proposal for Frans
---------------------

The answer needs no change. One corner is open: a database made with a
startup distance near 2^31 - 1, at many keys, could carry a debt above the
room, and a run that then fell behind the pace could stop. Options:

* **A. DbBuilder takes at most 10^9, as `setStartupDistance` does**
  (`DbBuilder.startupDistance` refuses a larger value with
  IllegalArgumentException, as it refuses one below 10; or clamps it, as
  the setter does). Then the debt, measured at most 1.10 sd, stays below
  half the room in every measured workload, and `T3_takeB`'s premise holds
  with a margin of about 2 there. A few lines and a test; a database made
  before with a larger setting starts as before (the setting is in its
  stream).
* **B. Past the deadline, take at least the oldest due transaction**,
  whatever the room. Not possible as such: the record limit is hard (the
  size field is an int). It would need a record split in two, more code in
  `Db.store` for a case no run reaches.
* **C. No change.** Write the premise down: Java's T3 rests on the debt
  staying below the room, about 2.1 GB, which holds in every measured run
  with sd ≤ 10^9 by a factor of 2 or more, and keep this probe for a check
  at 50M keys with sd 2^31 - 1 if such a setting is ever used.

Recommendation: **A**, refuse. It is small, it matches the setter's range,
and it turns the open corner into a measured margin. Not applied: product
code is outside this entry.


State
-----

Done: the answer, the runs, the probe. Not done: a run at 50M keys with sd
2^31 - 1 (22 GB heap and more; the only workload that could bring the debt
near the room). Clone `/Users/f/fl/bench/2026-11-13/takebytes/clone`,
branch `028-12-take-bytes`; the runs' scratch directory
`/Users/f/fl/bench/2026-11-13/takebytes` (cls/, out/). To rerun: build the
clone's jar (java/build.sh), compile the probe as run.sh says, run a queue.


Log
---

2026-11-13. Registered by coord-1113, from prover t44's target D (007).

2026-11-13. Evaluated by an agent of coord-1113 (takebytes, branch
028-12-take-bytes): no stop in Java's runs; the probe and 18 runs (1M and
10M keys at the real limit, 1M keys scaled); the coordinator's two
questions from `T3_takeB_count` (checkpoint 418ab85d) answered in sections
2 and 5; proposal A for Frans.

2026-11-14, 11:58. Frans: "Decisions 4 and 5, as recommended." For this
entry: option A, DbBuilder refuses a startup distance above 10^9.

2026-11-14. Done by an agent of coord-1114, on branch 028-12-builder-sd:
`DbBuilder.startupDistance()` refuses a value above 10^9
(`DbBuilder.MAX_STARTUP_DISTANCE`, the largest that
`Db.setStartupDistance()` sets) with IllegalArgumentException ("Too
large, ..."), where it already refused one below 10, so the builder keeps
the value it had; its Javadoc says the limit and why, and
`Db.setStartupDistance()`'s Javadoc no longer says that the builder allows
more. A database made before with a larger setting starts with it, as the
stream keeps it. The Pub API needs no change: `DatabaseBuilder` and
`Database.setStartupDistanceInMb()` clamp to 5 to 1000 MB, at most 10^9.
The unit test `DbTesterJavadoc.testBuilderStartupDistanceLimit`: 10^9
taken (a database started with it), 10^9 + 1, 2^31 - 1, 9, 0, -1 and
-2^31 refused, 10 taken, and a refused value leaves the one before. No
test, demo or stress script in java/ used more than 10^9; this entry's
own run r10m-sdmax (`queue-10m.sh`, `-Dtb.sd=2147483647`) is now refused,
and so is the run at 50M keys with sd 2^31 - 1 that State lists as not
done. `java/before-commit.sh` printed `BEFORE COMMIT OK`.
