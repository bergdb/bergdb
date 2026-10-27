005-49 report: smooth index writes
==================================

2026-10-27, by Claude (Opus 5.5, Claude Code), for Frans Lundberg (006-09, W2). On F53, JDK 27, all in memory. Only byte counts were measured, no time. Today's take is `565499f`. The recommended take is [paced-take.diff](paced-take.diff): made on `a6cd234`, it applies to `78a8d38`.

The answer. Today's take writes the index in bursts. At 200 and 1000 MB, 85 and 95 percent of the index bytes come from records with more than 4 times the mean index bytes; the largest records are 2.5 to 11.6 MB, and most records write no index node. 007-03's deadline alone makes it worse: at 50 MB it writes records of up to 110 MB.

A paced take removes the bursts and holds the startup section at the startup distance. Each commit writes the waiting dirty index nodes, oldest first, in proportion to the stream it adds. Compared at the startup distance that gives today's peak section, it writes 3 to 13 percent fewer bytes a put than today's take, and its largest record is 6 to 11 times smaller. At the same startup distance it writes 12 to 36 percent more, because its section no longer goes past sd.

Recommendation: this take in 007-03's step 3, with the deadline at 2 sd as the backstop. The deadline never fired in the runs.


## 1. What was measured

The tool is 005-38's `WriteBench` with every record logged ([wb/](wb/)). The workload is 005-38's `run3.sh`: 10M keys of 24 bytes with 8-byte values, loaded in random order with 1,000 puts a transaction, then 30M random updates of the loaded keys. Two variants:

* 50M keys with 20M updates, at 200 MB.
* At 1000 MB, 68M updates, so that the section is passed many times; they are compared over their first 68M updates. WriteBench keeps every version and never evicts, so a run ends where its heap ends.

The startup distances (sd) were 50, 200 and 1000 MB. For the paced take there were also runs at today's peak sections (137, 380, 541 and 1310 MB).

[summary.py](summary.py) gives one line a run:

* the stream's bytes a put, over the update phase and over its second half, where the take has settled (the tables use the second half);
* the largest record's index bytes, the largest over the mean, and the share of the index bytes in records over 4 times the mean;
* the startup section after each record (the stream's end minus the startup pos), in units of sd.

[analyze.py](analyze.py) gives percentiles a record and the age of a node when it is written. Every run's line is in [results.txt](results.txt). The stream is deterministic: the first 30M updates of the 68M run at 1000 MB are byte for byte those of the 30M run.


## 2. Today's take (question 1)

| run | B/put | index B/put | records with no index node | largest record | largest / mean | bytes in records > 4 x mean | section, mean / max |
|---|---|---|---|---|---|---|---|
| 10M keys, 50 MB | 699 | 604 | 65 % | 4.9 MB | 7 | 11 % | 1.29 / 2.75 sd |
| 10M keys, 200 MB | 384 | 303 | 79 % | 4.2 MB | 14 | 85 % | 1.08 / 1.90 sd |
| 10M keys, 1000 MB | 176 | 104 | 90 % | 2.5 MB | 23 | 95 % | 1.01 / 1.31 sd |
| 50M keys, 200 MB | 682 | 587 | 64 % | 11.6 MB | 20 | 11 % | 1.26 / 2.71 sd |

A record's index bytes against its own bytes (its value nodes and its 48-byte header) at 10M keys:

| sd | median | 99th percentile | largest |
|---|---|---|---|
| 50 MB | 0 | 40 | 72 |
| 200 MB | 0 | 30 | 62 |
| 1000 MB | 0 | 31 | 37 |

With 50M keys the largest is 171. At 50 MB a record's index bytes average 9 times its own bytes, so the bursts stand out less there. But the section goes furthest at 50 MB: 12 percent of the records end with it past 2 sd.

Nodes are written at a mean age of 1.73, 1.42 and 1.13 sd at 50, 200 and 1000 MB, and 1.71 sd with 50M keys.

The cause is the one 005-49 describes. A transaction's got-dirty nodes are written when it falls sd behind the end, and the transactions of a wave fall due together. The node limit, 4 nodes a put of the record, then writes the wave at about 1.4 MB a record while the section grows. The nodes it writes are clean at once, and the next puts make them dirty in a new wave.


## 3. The deadline alone

This is 007-03's step 3 as written: today's take, and every transaction older than 2 sd taken whatever the node limit. At 50 MB:

* 171 records over 10 MB; the largest is 110 MB (2.2 sd);
* 73 percent of the index bytes are in those records;
* with its last record, the section reaches 4.2 sd.

Today's take goes past 2 sd at the waves' peaks, and the deadline then writes the whole debt beyond 2 sd in one record. The nodes it cleans come back as the next wave, so the deadline fires again and again.

A pace that takes what is due at sd, at most twice the section's rate (the clone `pdue`), did the same at 50 MB: records of up to 115 MB. Step 3 must not be built without a pace that keeps the section away from 2 sd.


## 4. Why a smooth take costs more at the same sd, and not at the same peak

A node that stays dirty longer takes more puts before it is written, so the bytes a put fall as the age at write grows. Today's take writes few nodes at sd and most of them at its peaks. At 200 MB its section is about sd most of the time (median 1.01 sd), but 85 percent of the index bytes are written in the bursts, at ages up to 1.9 sd. A paced take writes every node at the age of its section. With the section bounded, writing at the bound is the latest any take can write.

At 200 MB, the paced take with its section at 1.0 and 1.5 sd wrote 523 and 433 bytes a put, roughly section^-0.47. On that curve it reaches today's 384 at 1.9 sd, today's peak.

Measured directly, the paced take with sd set to today's peak section:

| today's take | its peak section | B/put, today / paced | largest record, today / paced | paced section, max |
|---|---|---|---|---|
| 10M keys, 50 MB | 137 MB (2.75 sd) | 699 / 608 (-13 %) | 4.9 / 1.2 MB | 144 MB |
| 10M keys, 200 MB | 380 MB (1.90 sd) | 384 / 374 (-3 %) | 4.2 / 0.68 MB | 384 MB (403 at the end of the load) |
| 10M keys, 1000 MB | 1310 MB (1.31 sd) | 176 / 169 (-4 %) | 2.5 / 0.22 MB | 1.32 sd (1.39 at the end of the load) |
| 50M keys, 200 MB | 541 MB (2.71 sd) | 682 / 594 (-13 %) | 11.6 / 1.17 MB | 552 MB |

At 1000 MB the paced take ran with sd 1000 MB and its section at 1.31 sd, a constant T = 1.31 in the share. That is the same as sd 1310 MB except for the deadline, which never fired.

So at the same worst-case section, the bound that bounded startup promises, the paced take costs no more than today's take. At 50 MB and with 50M keys it costs 13 percent less, because today's take writes many nodes well before its peak.

The startup distance becomes what its name says: the section. A database that wants today's write cost chooses an sd near today's peak and gets today's worst-case startup, with no bursts. The typical startup then equals the worst case; today it is about sd. The Pub API clamps sd to 1000 MB.


## 5. The options

* **Today's take:** bursts (section 2); the section is unbounded in principle.
* **Today's take with the deadline** (007-03, step 3): bounded, but with records of up to 110 MB (section 3).
* **A due pace (`pdue`):** takes what is due at sd, at most f times the section's got-dirty nodes per own byte, with a carry for records that take nothing. The carry builds up in records that have nothing due and is spent at once, giving 1.6 MB records at 200 MB. At 50 MB, with f = 2, it fell behind and the deadline fired (115 MB).
* **The first paced take (`paced`, the default-effort agent's prototype):** the share of section 6, a carry for records that take nothing, the last transaction taken if half of it fits, and nothing younger than sd/2.
  * It is smooth: largest record 0.7 MB at 200 MB, and the deadline never fired.
  * Its section stays where the load left it: 1.37 times the target at 50 and 200 MB, and 1.71 sd with a target of 1.25 sd.
  * The cause: with one transaction a record, it takes exactly one transaction whenever the share is between 2/3 and 3/2 of it. That leaves a band of 0.7 to 1.5 times the target where nothing moves the section.
* **The recommended take** (section 6): the same share, with the last transaction rounded by a hash of the stream position, so a record takes its share on average. No carry, no floor. Its section stays at sd.
* **Writing nodes, not whole transactions** (question 4): a commit could then write exactly its share, even when transactions differ much in size. But it changes the model (sis-model 6.1, step 6: the algorithm writes the nodes it takes) and needs proofs of its own (007-03, step 4). It is not needed for the workloads measured: with whole transactions, a commit writes at most its share and one transaction.
* **A pace in time:** ruled out by P2 (the stream's bytes would depend on timing) and P3.
* **Other systems** (question 5), not studied further:
  * InnoDB's adaptive flushing sets the number of pages to flush from the rate of redo generation and the checkpoint age against the log's capacity.
  * LeanStore's continuous checkpointing (SIGMOD 2020, `docs/prior-art.md`) writes dirty pages in proportion to the log's growth.
  * The recommended take is the second idea, counted in stream bytes.


## 6. The recommended take

The rule in one sentence: each commit writes the dirty index nodes waiting in the startup section, oldest first and in whole transactions, in proportion to the stream it adds; a commit that adds a thousandth of sd writes a thousandth of them.

In the code ([paced-take.diff](paced-take.diff), `TransSeq.take`), a record of o own bytes has the share

    share = D * (o / O) * (S / sd)

where:

* D is the number of got-dirty nodes of the section's transactions;
* O is the own bytes of their records;
* S is the section's length.

o * S / O is the record's part of the stream, estimated before its index nodes are known. How the share is used:

* The transactions that fit in the share are taken.
* The next one, which fits only in part, is taken with the probability of that part. The test is a hash of the stream's length, `((pos * 0x9E3779B97F4A7C15L) >>> 11) * 0x1.0p-53`.
* Every transaction that begins 2 sd or more before the end is taken whatever the share: the deadline, d_h = 2 sd.

Why it keeps up with sd. A commit adds the nodes it makes dirty and writes its share of D. In a steady state the two are equal on average. That happens when D is what the commits make dirty in sd of stream; the oldest waiting transaction, at the startup pos, is then about sd behind the end. If D is larger, the commits write more than they make dirty and D shrinks; if smaller, D grows.

Seen from the section: D / O is the rate at which the section's commits made nodes dirty. A commit writes at that rate times S / sd, so it writes more than it makes dirty while the section is longer than sd, and less while it is shorter. A wave of new dirty nodes raises D at once, and with it the writes of all the following commits, spread over the next sd of stream.

The hash makes a record take its share on average, so there is no band (section 5). The deadline is the backstop that T3's proof uses (007-01). A pace that takes whole transactions oldest first needs nothing more from that proof (007-03, step 4).

What it keeps:

* P2: the sums D and O are functions of the startup section, which a start reads again (`DbStarter` computes each transaction's own bytes), and the hash is a function of the stream. So the stream does not depend on restarts.
* P10: no new setting.
* P2, P3: no time, thread or timer.
* P4, P1: a commit writes at most its share and one transaction, so its index writes follow its own size.

Results at the same sd, the second half of each run:

| run | B/put, today / paced | largest record, today / paced | largest / mean, paced | paced section: mean / p99 / max |
|---|---|---|---|---|
| 10M keys, 50 MB | 699 / 866 (+24 %) | 4.9 / 1.9 MB | 2.5 | 1.00 / 1.12 / 1.14 sd (min 0.88) |
| 10M keys, 200 MB | 384 / 523 (+36 %) | 4.2 / 1.0 MB | 2.3 | 1.00 / 1.02 / 1.03 sd |
| 10M keys, 1000 MB | 176 / 196 (+12 %) | 2.5 / 0.27 MB | 2.2 | 1.00 / 1.01 / 1.01 sd (1.10 at the end of the load) |
| 50M keys, 200 MB | 682 / 851 (+25 %) | 11.6 / 1.7 MB | 2.2 | 0.99 / 1.03 / 1.04 sd |

At 50 and 200 MB the mean section in windows of 2M puts stays between 0.99 and 1.01 sd. At 50 MB the section moves slowly between 0.88 and 1.14 sd as it absorbs the waves.

A record's index bytes against its own bytes at 200 MB: median 6.4, 99th percentile 12, largest 15; today's take: 0, 30 and 62. 3 to 6 percent of the records write no index node: those whose share fell short of the next transaction and whose hash said no.

A constant T in the share (section at T × sd) only relabels sd. T = 1.5 at 200 MB, a section of 300 MB, wrote 433 bytes a put.

Gates on the diff:

* `java/before-commit.sh`: BEFORE COMMIT OK.
* level2.sh's RestartInvariance cases, all eight including default-100MB: each stream identical, 6 of 6 checks.
* StreamDigest, today's take against the paced take:
  * all 36 standard streams change;
  * lengths change by -3 to +20 percent (small test workloads with sd of 100 bytes to 100 kB);
  * within each, the plain, reads and restarts streams agree.


## 7. For 007-03's step 3

What step 3 should change (I may not edit 007-03):

1. The take becomes the paced take of section 6 (paced-take.diff):
   * the node limit (`nodeCountLimit`) and the minimum of two transactions go;
   * `TransInfo` gets its record's own bytes, which `DbStarter` computes at a start;
   * `TransSeq` keeps the sums D and O, and its checksum covers the own bytes.
2. The deadline stays as written (d_h = 2 sd, `hardSp` in a long), as the backstop. In 005-49's runs it never fired.
3. "Streams change only where the take lagged" no longer holds: every stream changes (StreamDigest, section 6), for the same reason, the pace.
4. "Done when", in step 2's and 005-49's runs:
   * the section stays at about sd, and below d_h without its last record;
   * the largest record stays below a few times the mean (below 3 in 005-49's runs).
5. Step 4 models the take as whole transactions from s(i-1) + 1, taken while the pace allows or while the transaction begins d_h before the end. For T3 the pace can be any predicate on the stream and T(i).
6. Docs:
   * docs/levels.md, section 5: the take is paced, and the section stays at about sd;
   * the write overhead at 50, 200 and 1000 MB (005-38's figures) rises at the same sd and should be measured again;
   * P4's and P5's "Where BergDB stands" in 010-01.
7. `Db.setStartupDistance`'s Javadoc stays true. After a decrease the share grows by the factor S / sd, and the deadline writes what lies beyond the new 2 sd at once (D4).


## 8. Not done, and questions

* Question 2, what a burst costs a commit in time, was not measured: timed runs belong to the quiet block. Today's largest records are 2.5 to 11.6 MB; the paced take's are 0.27 to 1.9 MB.
* Transactions of mixed sizes were not measured: WriteBench uses 1,000 puts a transaction. A small commit after a large transaction may take it whole, with the probability of its share. A node pace (section 5) would avoid that.
* For Frans: is a section held at sd, with the write cost that follows at a given sd, the right meaning of the startup distance?
* For Frans: with the paced take, should the default startup distance (50 MB), or the advice of 200 to 1000 MB from 10M keys (005-38), change? Today's peaks are 2.75, 1.9 and 1.3 times sd at 50, 200 and 1000 MB.

Scratch, for reruns: `/Users/f/fl/bench/006-09/w2/`. The clone `rec` is the take with `-Dpace.T`; `final` is the diff; the runs are in `out2/`, `run2.sh` and `results.sh` are there, and the gate logs are in `inv-final.out` and `digest/`.
