007-06. A test that drives the debt up (007-03, step 2)
=======================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, in
006-09 (W8), at his choice: "007-03 step 2: debt test". Status: ran
2026-10-27, 16:54 to 20:37, on F53; the results and what they mean are
below.

The answer. 007-01's hypothesis (4.2) holds in every run on today's take:
once the debt of D goes past sd, the section goes as far as the debt. That
holds for updates, deletes and single puts alike. On today's take, a
decrease of the startup distance is slow but makes no large commit: the
section gets below the new d_h after 1.2 to 1.4 times the debt at the
decrease, in stream bytes, and later goes past it again. On 005-49's paced
take, which brings the deadline at 2 sd, one call to `setStartupDistance`
writes nearly all of D in one record (490 MB at 1000 to 100 MB). Steps of
10 MB back to back do not help (records of up to 54 MB). What works is
to lower the distance that the pace uses at once and let the deadline come
down with the lag. The section is then below the new d_h after 0.1 to 0.7M
puts, and no record is over 5.6 MB. That is how D4's option B can be
built in step 3. 007-07's patch, step 3 as made the same evening,
behaves as the prototype in these runs.


What it measures
----------------

007-03, step 2. After every transaction it records the section without
its last record (R(s+1), ..., R(k-1); 007-01, section 3), the record's
size, D in nodes, and the debt: the stream size of D's nodes plus 16 bytes
each, as `TransSeq.recordBytes` counts them. The workloads are the ones
that 007-04 (1) left:

* The startup distance lowered at runtime (`Db.setStartupDistance`), from
  1000 to 100 MB and from 200 to 50 MB, in one call and in calls of at most
  10 MB back to back (the Javadoc's advice). It measures how long, in
  stream bytes and puts, until the section is below the new d_h = 2 sd,
  and the largest record meanwhile (006-06, question 2; D4's sizes).
* Deletes of existing keys, spread over the keys.
* Single puts: transactions of one put.

For the hypothesis it also reruns 005-38's first workload: random updates
spread over the keys, in transactions of 1,000 puts.

All runs use 10M keys of 24 bytes with 8-byte values, in memory as 005-38
ran it (12 GB heap, no eviction, every version kept), at startup distances
of 50, 200 and 1000 MB. Today's take is `e6dbc82`. The same runs were made
on 005-49's paced take
([paced-take.diff](../005-todo/49-smooth-index-writes/paced-take.diff),
applied to `e6dbc82`), as "the same runs again after step 3" will need,
and most of them on 007-07's patch.
Only bytes and nodes were counted, no time.


The tool
--------

[06-debt-test/WriteBench.java](06-debt-test/WriteBench.java) is 005-49's
WriteBench, which logs every record, with 24 more bytes an entry: the
section without its last record, D in nodes, the debt, and the startup
distance in force. D and the debt are kept up to date a record at a time
from a mirror of `TransSeq`: each transaction's nodes are counted when it
is added and subtracted when it is taken. They are recomputed exactly
every sd/100 bytes of stream. After the load the drift was at most 1.1
percent of the debt; it comes from dirty nodes that change size while they
wait. New options: `wb.utx` (puts a transaction after the load),
`wb.op=delete`, and `wb.lowerAt`, `wb.lowerTo`, `wb.lowerStep`,
`wb.lowerGap` and `wb.lowerPace` for the decrease.

Each run loads 10M keys in random order, 1,000 puts a transaction, and
then runs one workload:

* updates: 30M random puts to loaded keys, 1,000 a transaction;
* deletes: 8M distinct loaded keys in random order, 1,000 a transaction;
* single puts: 6M random puts, one a transaction;
* a decrease: the updates, with the distance lowered after some of them
  and 10M more updates after it. It is lowered at two points: after 20M
  updates ("20M"), and just before the record with the largest debt after
  10M updates in the run without a decrease ("worst"). The runs are
  deterministic, so the two runs share the prefix.

[run.sh](06-debt-test/run.sh) runs one; [queue1.sh](06-debt-test/queue1.sh)
to [queue5.sh](06-debt-test/queue5.sh) are the evening's runs.
[summary.py](06-debt-test/summary.py) gives a few lines a run,
[tables.py](06-debt-test/tables.py) the tables below, and
[pick.py](06-debt-test/pick.py) the worst point. The outputs are in
[out/](06-debt-test/out/): runs.txt, digest.txt (each run's output without
the per-window lines), summary.txt and tables.txt. The records (wb.rec,
1.6 GB in all) stay in the scratch directory, /Users/f/fl/bench/006-09/w8.

Steady runs are measured over the second half of the workload by puts. In
the tables, "section" is the section without its last record, in units of
the startup distance (sd); "debt" is the debt in sd; records are in MB.


## 1. Today's take: the section follows the debt

| run | B/put | largest record | section mean / p99 / max | debt max | D max | section + debt max |
|---|---|---|---|---|---|---|
| updates, 50 MB | 699 | 4.56 | 1.24 / 2.60 / 2.70 | 2.69 | 354k | 3.98 |
| updates, 200 MB | 384 | 4.42 | 1.07 / 1.83 / 1.88 | 1.85 | 943k | 2.85 |
| updates, 1000 MB | 219 | 2.56 | 1.01 / 1.28 / 1.31 | 1.02 | 2271k | 2.02 |
| deletes, 50 MB | 589 | 3.79 | 1.21 / 2.60 / 2.68 | 2.68 | 370k | 3.90 |
| deletes, 200 MB | 293 | 2.78 | 1.06 / 1.82 / 1.83 | 1.79 | 950k | 2.79 |
| deletes, 1000 MB | 300 | 2.34 | 1.00 / 1.10 / 1.10 | 0.96 | 2126k | 1.96 |
| single puts, 50 MB | 776 | 0.73 | 1.16 / 1.93 / 1.98 | 1.89 | 256k | 3.00 |
| single puts, 200 MB | 483 | 0.96 | 1.06 / 1.48 / 1.50 | 1.43 | 780k | 2.43 |

Wherever the debt goes past sd (at 50 and 200 MB, in all three
workloads), the largest section and the largest debt agree to within 0.09
sd. At 1000 MB the debt stays near sd and the section reaches 1.10 to
1.31 sd, the node limit's lag. In the update runs, the section's peak
comes 0.4 to 2.3 GB of stream after the debt's, while the take works
through the debt. That is 007-01's hypothesis, now measured a record at
a time: the section reaches the larger of sd and the debt, plus at most
about 0.3 sd. Section plus debt is what option C of 007-01 (4.2) keeps
below d. On today's take it reaches 2 to 4 sd.

Deletes behave as updates: about the same debt and section. At 50 and
200 MB they cost fewer bytes a delete than an update costs a put. The run
at 1000 MB covers only 1.4 sd of stream. A delete writes a 56-byte value
node (the deletion), so a record of deletes has own bytes, and the paced
take paces it (sections 3 and 4).

Single puts keep the section shorter (2.0 and 1.5 sd at 50 and 200 MB),
but they show the burst at its worst. One put's record writes up to 1.6
MB of index nodes: 0.73 and 0.96 MB in the second half, and about 500
records in 3M write over 100 kB. The cause is in the take. It always takes
two transactions, and a single put's transaction can have up to 1,981
got-dirty ids. Writing a wave of nodes moves them in the stream, which
makes their parents dirty in the writing record's own transaction, and
the next records take those parents. The debt breeds debt.


## 2. Today's take: lowering the distance

Each row is one decrease. The columns:

* the section and the debt just before the decrease;
* the dummy records that `setStartupDistance` writes: their count, their
  bytes and the largest;
* from the first dummy record until the section is first below the new 2
  sd, and below the new sd: the update puts, the stream bytes and the
  largest user record;
* after that, over the second half of the rest of the run: the largest
  section and record.

| decrease | section / debt before | dummy records | to 2 sd | to sd | after |
|---|---|---|---|---|---|
| 1000 to 100, once, worst | 1000 / 1016 MB | 1, 2 MB, 1.92 MB | 0.62M, 1202 MB, 3.29 MB | 0.68M, 1320 MB, 3.29 MB | 2.22 sd, 3.68 MB |
| 1000 to 100, steps, worst | 1000 / 1016 MB | 90, 97 MB, 2.14 MB | 0.59M, 1215 MB, 3.17 MB | 0.64M, 1335 MB, 3.17 MB | 2.21 sd, 3.50 MB |
| 1000 to 100, once, 20M | 999 / 599 MB | 1, 0 MB, 0.42 MB | 0.41M, 766 MB, 4.00 MB | 0.45M, 880 MB, 7.06 MB | 2.21 sd, 4.35 MB |
| 1000 to 100, steps, 20M | 999 / 599 MB | 90, 63 MB, 1.35 MB | 0.39M, 781 MB, 3.10 MB | 0.44M, 899 MB, 4.51 MB | 2.23 sd, 3.53 MB |
| 200 to 50, once, worst | 200 / 372 MB | 1, 1 MB, 1.06 MB | 0.27M, 510 MB, 3.48 MB | 0.29M, 567 MB, 4.66 MB | 2.69 sd, 3.76 MB |
| 200 to 50, steps, worst | 200 / 372 MB | 15, 16 MB, 1.38 MB | 0.26M, 511 MB, 3.49 MB | 0.29M, 568 MB, 4.67 MB | 2.68 sd, 3.71 MB |
| 200 to 50, once, 20M | 200 / 286 MB | 1, 1 MB, 1.25 MB | 0.21M, 410 MB, 5.47 MB | 0.24M, 473 MB, 5.47 MB | 2.71 sd, 3.64 MB |
| 200 to 50, steps, 20M | 200 / 286 MB | 15, 30 MB, 2.96 MB | 0.20M, 408 MB, 4.03 MB | 0.22M, 472 MB, 5.27 MB | 2.66 sd, 3.64 MB |

Today's take hardly notices a decrease. Whatever the distance, it takes
at most its node limit a record: 4 nodes a put, but at least two
transactions. So the startup pos moves at its usual pace while the old
section is worked off. The section gets below the new d_h after 0.2 to
0.6M puts: 0.8 to 1.2 GB of stream at 1000 to 100 MB, and 0.4 to 0.5 GB at
200 to 50 MB. That is 1.2 to 1.4 times the debt at the decrease. No commit
is large: the dummy records are 0.4 to 3 MB, and the user records
meanwhile are 3 to 7 MB, as in a steady run. Steps change nothing. They
only add their dummy values (200 kB each) and the nodes taken with them:
63 to 97 MB for 90 calls. Afterwards, the new distance's own overshoot
takes the section past the new 2 sd again: 2.2 sd at 100 MB and 2.7 sd at
50 MB.

So on today's take, fast restart's "lower, then restart" (006-06) works,
slowly and without a burst. It cannot promise a section below 2 sd,
because today's take does not keep up with 2 sd at these distances
(007-04, 1).


## 3. The paced take (005-49)

These are the same runs with paced-take.diff, which also brings 007-03's
deadline at 2 sd.

| run | B/put | largest record | section mean / p99 / max | debt max | D max | section + debt max |
|---|---|---|---|---|---|---|
| updates, 50 MB | 867 | 2.03 | 0.97 / 1.08 / 1.12 | 1.04 | 136k | 2.12 |
| updates, 200 MB | 523 | 1.10 | 1.00 / 1.02 / 1.02 | 0.88 | 451k | 1.90 |
| updates, 1000 MB | 190 | 0.35 | 1.03 / 1.10 / 1.10 | 0.59 | 1416k | 1.67 |
| deletes, 50 MB | 786 | 1.81 | 0.97 / 1.09 / 1.12 | 1.05 | 144k | 2.13 |
| deletes, 200 MB | 422 | 0.93 | 1.00 / 1.01 / 1.01 | 0.86 | 466k | 1.88 |
| deletes, 1000 MB | 121 | 0.23 | 0.96 / 1.03 / 1.03 | 0.47 | 1213k | 1.50 |
| single puts, 50 MB | 846 | 0.26 | 1.11 / 1.14 / 1.14 | 0.99 | 134k | 2.12 |
| single puts, 200 MB | 538 | 0.22 | 1.00 / 1.00 / 1.00 | 0.79 | 422k | 1.79 |

In every workload, the paced take holds the section at 1.0 to 1.14 sd and
the debt at about sd or less, and section plus debt stays below 2.2 sd.
Its largest record is 2 to 10 times smaller than today's. Its single
puts write at most 0.22 to 0.26 MB of index nodes a record, a third or a
quarter of today's.

Lowering the distance was run in four ways. The first two are as in
section 2. The other two are made for D4's option B:

* once: one call;
* steps: calls of at most 10 MB, back to back;
* follow: every 10 update transactions, the distance becomes max(new sd,
  section / 2) when that is lower, so that the deadline at 2 sd stays near
  the section's start (`wb.lowerGap`);
* pace: one call, with the deadline given a distance of its own (a probe
  in `TransSeq`, [deadline-probe.diff](06-debt-test/deadline-probe.diff),
  on top of paced-take.diff). The deadline starts at the lag and is
  lowered every 10 update transactions to max(2 × new sd, lag), so the
  pace uses the new distance at once and the deadline never fires
  (`wb.lowerPace`).

| decrease | section / debt before | dummy records | to 2 sd | to sd | after |
|---|---|---|---|---|---|
| 1000 to 100, once, worst | 993 / 605 MB | 1, 490 MB, 489.80 MB | 0, 490 MB, none | 0, 634 MB, 144.67 MB | 1.08 sd, 2.10 MB |
| 1000 to 100, steps, worst | 993 / 605 MB | 90, 676 MB, 40.32 MB | 0, 676 MB, none | 0.02M, 680 MB, 2.07 MB | 1.05 sd, 2.33 MB |
| 1000 to 100, follow, worst | 993 / 605 MB | 345, 386 MB, 3.45 MB | 3.44M, 1710 MB, 1.50 MB | 3.62M, 1900 MB, 2.04 MB | 1.02 sd, 1.59 MB |
| 1000 to 100, pace, worst | 993 / 605 MB | 1, 3 MB, 3.29 MB | 0.67M, 825 MB, 2.50 MB | 0.74M, 934 MB, 3.21 MB | 1.04 sd, 1.59 MB |
| 1000 to 100, once, 20M | 1052 / 577 MB | 1, 462 MB, 462.13 MB | 0, 462 MB, none | 0, 623 MB, 161.31 MB | 1.06 sd, 2.00 MB |
| 1000 to 100, steps, 20M | 1052 / 577 MB | 90, 666 MB, 27.45 MB | 0, 666 MB, none | 0.01M, 675 MB, 3.17 MB | 1.04 sd, 1.93 MB |
| 1000 to 100, follow, 20M | 1052 / 577 MB | 298, 366 MB, 3.70 MB | 2.97M, 1617 MB, 1.66 MB | 3.12M, 1792 MB, 2.08 MB | 1.03 sd, 1.53 MB |
| 1000 to 100, pace, 20M | 1052 / 577 MB | 1, 4 MB, 3.61 MB | 0.59M, 815 MB, 3.11 MB | 0.64M, 916 MB, 3.11 MB | 1.04 sd, 1.59 MB |
| 200 to 50, once, worst | 202 / 176 MB | 1, 87 MB, 87.39 MB | 0, 87 MB, none | 0, 210 MB, 73.31 MB | 1.10 sd, 2.38 MB |
| 200 to 50, steps, worst | 202 / 176 MB | 15, 197 MB, 54.09 MB | 0, 197 MB, none | 0, 213 MB, 11.21 MB | 1.11 sd, 2.41 MB |
| 200 to 50, follow, worst | 202 / 176 MB | 23, 79 MB, 4.55 MB | 0.22M, 328 MB, 2.37 MB | 0.26M, 382 MB, 2.58 MB | 1.12 sd, 2.03 MB |
| 200 to 50, pace, worst | 202 / 176 MB | 1, 5 MB, 5.36 MB | 0.10M, 246 MB, 3.95 MB | 0.12M, 288 MB, 3.95 MB | 1.15 sd, 1.93 MB |
| 200 to 50, once, 20M | 200 / 172 MB | 1, 86 MB, 85.86 MB | 0, 86 MB, none | 0, 205 MB, 69.93 MB | 1.13 sd, 2.39 MB |
| 200 to 50, steps, 20M | 200 / 172 MB | 15, 192 MB, 51.18 MB | 0, 192 MB, none | 0, 208 MB, 11.13 MB | 1.11 sd, 2.37 MB |
| 200 to 50, follow, 20M | 200 / 172 MB | 20, 72 MB, 5.17 MB | 0.19M, 299 MB, 2.10 MB | 0.23M, 361 MB, 2.75 MB | 1.07 sd, 1.96 MB |
| 200 to 50, pace, 20M | 200 / 172 MB | 1, 6 MB, 5.57 MB | 0.10M, 240 MB, 3.87 MB | 0.12M, 284 MB, 3.87 MB | 1.12 sd, 1.99 MB |

**Once.** With the deadline, the dummy transaction of one call takes every
transaction that the new d_h makes due. That is one record of 86 to 490
MB, nearly all of D, written while every other writer waits. The record is
itself in the section, and it moves the stream's end, so the next user
record takes the rest past the deadline: 70 to 161 MB. The section is then
below the new sd at once. This is D4's option A, measured. Startup also
reads the last record whole (T3_bounded: d + 2M), so such a record
lengthens a start as well as a commit.

**Steps.** Steps of 10 MB back to back do not spread the debt. Each step
lowers d_h by 20 MB, and each dummy record moves the end by its own size,
so the next step finds as much due again. The result is 15 to 90 dummy
records of up to 27 to 54 MB, 192 to 676 MB in all, more than one call
writes.

**Follow.** Following the section down keeps every record small: at most
5.2 MB, a dummy record, and at most 2.75 MB for a user record. But it is
slow at 1000 to 100 MB: 3.0 to 3.4M puts and 1.6 to 1.7 GB of stream,
slower than today's take. The pace's factor, section / sd, is at most 2
there. The dummy records also weigh: 298 to 345 of them, 366 to 386 MB.
Each carries a 200 kB value, which the pace counts as own bytes, so each
dummy also takes a large share of nodes.

**Pace.** Lowering the pace's distance at once and letting the deadline
follow the lag is the fastest way, and still smooth. The section gets
below the new 2 sd after 0.59 to 0.67M puts and 0.82 GB at 1000 to 100
MB, and after 0.10M puts and 0.24 GB at 200 to 50 MB. That is 1.4 times
the debt at the decrease, a smaller debt than today's take carries. There
is one dummy record of 3.3 to 5.6 MB, and user records of at most 3.1 to
4.0 MB while the section shrinks, about twice the paced take's steady
records at the new distance (1.6 to 1.9 MB). Afterwards the section
settles at 1.04 to 1.15 sd, as in a steady run.


## 4. 007-07's patch

007-07, step 3 as a patch, was made the same evening by another session:
[step3.diff](07-step3-paced-take/step3.diff), on `fc8f7c3`. The steady
runs and the one-call decreases at the worst points were run on it, as
step 3's "Done when" asks (007-07, section 8).

| run | B/put | largest record | section mean / p99 / max | debt max | D max | section + debt max |
|---|---|---|---|---|---|---|
| updates, 50 MB | 867 | 1.93 | 0.97 / 1.08 / 1.10 | 1.04 | 137k | 2.13 |
| updates, 200 MB | 524 | 1.12 | 0.99 / 1.01 / 1.02 | 0.88 | 448k | 1.89 |
| updates, 1000 MB | 190 | 0.34 | 1.03 / 1.09 / 1.09 | 0.59 | 1417k | 1.66 |
| deletes, 50 MB | 787 | 1.72 | 0.97 / 1.08 / 1.10 | 1.03 | 137k | 2.12 |
| deletes, 200 MB | 422 | 0.85 | 0.99 / 1.01 / 1.01 | 0.86 | 464k | 1.87 |
| deletes, 1000 MB | 121 | 0.23 | 0.96 / 1.02 / 1.03 | 0.47 | 1219k | 1.50 |
| single puts, 50 MB | 873 | 0.29 | 1.00 / 1.03 / 1.03 | 0.90 | 121k | 1.93 |
| single puts, 200 MB | 537 | 0.23 | 1.00 / 1.01 / 1.01 | 0.79 | 425k | 1.80 |

| decrease | section / debt before | dummy records | to 2 sd | to sd | after |
|---|---|---|---|---|---|
| 1000 to 100, once, worst | 988 / 601 MB | 1, 486 MB, 485.92 MB | 0, 486 MB, none | 0, 631 MB, 144.58 MB | 1.04 sd, 2.05 MB |
| 200 to 50, once, worst | 201 / 175 MB | 1, 87 MB, 86.73 MB | 0, 87 MB, none | 0, 207 MB, 72.16 MB | 1.14 sd, 2.13 MB |

The patch behaves as the prototype, within a few percent in every
column: the section at most 1.10 sd, the debt at most 1.04 sd, and single
puts' records at most 0.29 MB. One call from 1000 to 100 MB writes a
486 MB record and then a 145 MB one; from 200 to 50 MB, 87 MB and then
72 MB. 007-07's Javadoc advice (a third a call, with stream between
calls) was not run as such; "follow" in section 3 is close to it.


## 5. What it means for step 3 and D4

1. **Step 3, the paced take with the deadline as backstop, holds on the
   new workloads.** Deletes and single puts keep the section and the debt
   at about sd, as updates do, and single puts lose most of their burst.
   The hypothesis says why: the paced take pays the debt as it arises
   (between options A and C of 007-01, 4.2), so the debt never gets ahead
   of sd.
2. **The deadline must not jump when the distance is lowered.** With
   paced-take.diff or 007-07's patch as they are, a decrease writes the
   debt in one record (D4, A), or in records of tens of MB if done in
   steps back to back. 2 × the new sd must not apply at once. D4's B, in
   step 3, should lower the pace's distance at once and bring the
   deadline's distance down with the lag, for example to max(2 × new sd,
   lag) every few commits, as the probe did. The deadline then stays a
   backstop that never fires during a decrease, and T3 still holds for
   the lag in force: the take keeps up with the deadline that applies.
   `setStartupDistance` (or a new method for fast restart) returns when
   the section is below 2 × new sd. 007-07 found the same series of
   records in small probes (its 7.3), and its Javadoc recommends
   decreases of at most a third a call with stream between calls, which
   is close to "follow" here; "pace" catches up about twice as fast at
   1000 to 100 MB, with records of the same order. What remains for step
   4 and T3 is a policy whose deadline distance changes over time (006-06,
   question 4).
3. **Sizes for D4.** At 10M keys, a decrease from 1000 to 100 MB took
   0.8 GB of stream and 0.6 to 0.7M puts with the probe, and from 200 to
   50 MB, 0.24 GB and 0.1M puts. The largest record was 3.3 to 5.6 MB,
   the dummy record. The stream needed is about 1.4 times the debt at the
   decrease. At 50M keys the debt is larger (005-38: D up to 1.57 GB on
   today's take at 1000 MB), so expect a few GB. Without writers, nothing
   pays the debt. A fast restart with no traffic needs `setStartupDistance`
   to write the debt itself, in its own records of bounded size, with the
   write lock released between them.
4. **The dummy transaction.** `setStartupDistance` writes a 200 kB value so
   that a meta block records the new distance. Under the paced take that
   value counts as own bytes and earns the dummy record a large share
   (3 to 5 MB records; 0.37 GB in all when following). Step 3 should
   either store the distance without it or not count the dummy value as
   own bytes.
5. **Fast restart (006-06, question 2), on today's take.** The catch-up
   needs 1.2 to 1.4 times the debt at the decrease, in stream bytes, with
   no large commit. The section can then be read as the stream's end
   minus the startup pos, which Db knows (`x.startupPos`) but its
   public API does not expose. On today's take the section does not stay
   below 2 sd.


Left
----

* The same runs at 50M keys (22 GB heap; 005-38's largest D). Not run
  tonight. The commands are those of queue1.sh to queue5.sh with
  `-Dwb.keys=50000000`, fewer updates (005-49 ran 20M at 50M keys) and
  `HEAP=22g`, one JVM at a time. Run on main with D4:B: 007-07, section
  11.
* The deletes at 1000 MB cover only 1.4 sd of stream; 10M keys allow at
  most 10M deletes. A longer run would need more keys. Run with 40M
  deletes at 50M keys: 007-07, section 11.
* D4's B as in section 5, point 2, in step 3's take, then these
  decreases again, to replace the probe.
* "follow" and "pace" on 007-07's patch: the probe is the same two
  lines in its `TransSeq`.
