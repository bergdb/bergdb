005-49. Investigate smooth index writes
=======================================

Status: done (2026-10-27; see Results). Kind: investigate. Created 2026-10-26.

Found in 005-38 ([report](38-writes-at-scale/report.md), section 5);
registered at Frans's request (2026-10-26: "Yes, register the burst
entry."), after: "I am now more worried about the bursts you report. I like
smooth operation. Good worst case behaviour. Bursts are to be avoided. In
general I like the cost of a user operation to be predicable and
proportionell to the size of the user-visible operation."


The issue
---------

At the startup distances a large database should use (200 to 1000 MB,
005-38), the index nodes are written in bursts. Stream bytes a put in
windows of 1M random updates, 10M keys, startup distance 1000 MB, node size
30 (`38-writes-at-scale/wb/out/u-sd1000-10M.txt`):

    71 71 70 70 1012 83 79 87 75 85 75 75 83 90 91 111 1055 80 76 74 75 ...

At 200 MB, windows of 131 to 555 bytes a put; at 50M keys and 1000 MB,
windows of 2.5M updates, 107 to 793. Most commits write their own record and
little more; a few write a large share of the index.

The cause, from the code: a transaction's got-dirty nodes are written when
the transaction falls more than the startup distance behind the stream's
end (`TransSeq.take`). The transactions of one wave, which dirtied many
nodes, fall due together. `take()`'s node limit (`nodeCountLimit`: 4 nodes
a put of the record, and a KB of nodes for each KB of keys and values)
spreads a wave over the next records but does not smooth it: a record of
1,000 puts can take about 4,000 nodes, some 1.4 MB. And a written node with
a dirty child is dirty again, in the record's own transaction, so the waves
repeat.

007-03's step 3, the deadline (D1, decided 2026-10-24), makes it steeper:
past 2 × sd the take ignores its node limit, and the next transaction
writes the whole debt beyond that at once. 007-03 says that step 3 waits
for this entry.


Questions
---------

1. How large are the bursts, per record: the largest record, the index
   bytes a record against its puts, and their distribution, at 50, 200 and
   1000 MB, for 10M and 50M keys, today. 005-38 measured windows of 1M
   puts only.
2. What does a burst cost a commit: the time of the largest records, with
   a forcing stream (on F53 and on s1), against a commit without one?
3. A paced take: each record takes about D's debt divided by the puts in a
   window, scaled by the record's own size, oldest first, so that a
   commit's index writes are proportional to its puts. What does it cost
   in total bytes (nodes written before their deadline absorb fewer later
   puts), and does it keep the startup section within its bound (T3, the
   take keeps up)?
4. Other ways: a node limit that follows the debt; writing the oldest
   nodes, not whole transactions' lists; a time-based pace. How each meets
   bounded startup, the record limit (005-17, 005-31) and the Lean model
   of the take (007-03, step 4).
5. What do other systems do? Adaptive flushing of dirty pages against the
   redo log's age in InnoDB, and continuous checkpointing (LeanStore,
   SIGMOD 2020, in `docs/prior-art.md`).


Done when
---------

A report (a subitem here, or an item of its own if it grows): question 1
measured, a paced take prototyped on a scratch clone and measured for
total bytes, the largest record and the startup section, and a
recommendation, which 007-03's step 3 then follows.


First step
----------

Extend 005-38's `WriteBench` (`38-writes-at-scale/wb/`) to record each
record's index bytes and puts, and run the update phase of 005-38's
`run3.sh` again: the distribution of a record's index bytes against its
puts.


Size and order
--------------

M. Before 007-03's step 3 (the deadline) and step 4 (the take in Lean): the
take that 007 proves should be the paced one, if that is the choice.


Results
-------

2026-10-27, by Claude (Opus 5.5, Claude Code), 006-09, W2. The report is
[49-smooth-index-writes/report.md](49-smooth-index-writes/report.md). The recommended take is
[paced-take.diff](49-smooth-index-writes/paced-take.diff), against `78a8d38`
(`java/before-commit.sh` OK; level2.sh's RestartInvariance cases identical). It was measured
with [summary.py](49-smooth-index-writes/summary.py) and the tools beside it, and every run's
line is in [results.txt](49-smooth-index-writes/results.txt). Nothing in `java/` of the main
tree.

Recommendation for 007-03's step 3: a paced take. Each commit writes, oldest first and in
whole transactions, the dirty index nodes waiting in the startup section in proportion to the
stream it adds: a commit that adds a thousandth of sd writes a thousandth of them. The
deadline at 2 sd stays as the backstop; in the runs it never acted, and the section stayed
between 0.88 and 1.14 sd. At the startup distance that gives today's peak section, the paced
take wrote 3 to 13 percent fewer bytes a put than today's take, and its largest record was
0.2 to 1.2 MB against 2.5 to 11.6 MB (10M keys at 50, 200 and 1000 MB; 50M keys at 200 MB).
At the same startup distance it writes 12 to 36 percent more, because its section no longer
passes sd.
