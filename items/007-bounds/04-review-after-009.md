007-04. Review: 007 after item 009 and the day's work
====================================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Go through bergdb item 007-bounds and check how this is still
relevant or not after the 009 work and other recent work. Update the plan if
needed. Don't start any implementation." On bergdb `d9d350d`, with 005-38's
report and 005-49, not yet committed then. Nothing was implemented. The
plan, [007-03](03-plan.md), is updated from this review.


The answer
----------

007 is as relevant as before. Item 009 changed nothing that 007 is about:
not T3, not the take, not the records, not what startup reads. So BergDB's
own take is still not bounded, and the day's measurements (005-38) show it
going past the deadline's 2 × sd at the startup distances Frans recommends.
What changed is around the plan:

* the index is written in bursts, which the deadline would make steeper,
  and smooth writes are now an entry of their own (005-49), before the
  deadline;
* a cold startup takes minutes on a slow disk, for a reason the plan does
  not cover;
* D, which the plan leaves to T4, is now the floor of BergDB's memory;
* startup distances of 200 to 1000 MB and fast restart change what to
  measure and what to promise.


Unchanged
---------

T3 is about the algorithm only: `lean/SIS/Bound.lean` imports
`SIS.Algorithm` and nothing of the physical layer, and the Bound files are
as on 2026-10-23. `TransSeq.take` is as 005-31 left it on 2026-10-24, and
so is its call in `Db.store`: the node limit, the record limit, whole
transactions, the TODO of 2015. Handles (item 009, merged 2026-10-26)
changed what a memory pointer holds, not the records: every record is
2026.1's byte for byte (009-01, target 5), so the cost of a record and the
debt of D are as before. And startup reads what it read before (009-02,
4.9). So the startup section is still not bounded for BergDB's own take, as
README.md and docs/levels.md say.

Release 2026.1, which steps 2 to 5 waited for, is out (2026-10-25).


What changed
------------

1. **The take goes past 2 × sd at the startup distances that suit large
   databases.** 005-38 ([report](../005-todo/38-writes-at-scale/report.md),
   section 4) ran random updates, 1,000 puts a transaction, on 10M and 50M
   keys at 50, 200 and 1000 MB. It sampled the startup lag (the stream's end
   minus the startup pos) and D at the end of every window of 1M or 2.5M
   updates, so the true largest lag may be a little higher. The lag, mean
   and largest:

   | Startup distance | 10M keys | 50M keys |
   |---|---|---|
   | 50 MB | 66, 131 MB | 70, 132 MB |
   | 200 MB | 215, 335 MB | 248, 465 MB |
   | 1000 MB | 985, 1,002 MB | 1,082, 1,647 MB |

   Between peaks the lag stays near sd. At the peaks it reaches 2.6 × sd at
   50 MB, and 2.3 × at 200 MB with 50M keys, past the deadline's 2 × sd. D
   held up to 4.57 million nodes, 1.57 GB of stream bytes (50M keys, 1000
   MB). 007-01's hypothesis (4.2: the section reaches the larger of d and
   the debt, plus a little) fits: the lag's peaks are about D's largest
   bytes (131 and 124 MB at 10M keys and 50 MB; 465 and 466 MB at 50M keys
   and 200 MB).

2. **The index is written in bursts, and Frans wants smooth operation.** At
   large startup distances the transactions of a wave fall due together,
   and their nodes are written in a short stretch of records (005-38's
   report, section 5): at 10M keys and 1000 MB, about 70 bytes a put in most
   windows of 1M updates, and about 1,000 in one window per startup
   distance. The lag's peaks in 1 are those waves; the take's node limit
   spreads a wave but does not smooth it. Frans, 2026-10-26: "Bursts are to
   be avoided. In general I like the cost of a user operation to be
   predicable and proportionell to the size of the user-visible operation."
   The deadline makes a burst steeper where it acts: past 2 × sd the take
   writes the whole debt beyond it at once. Registered the same day as
   [005-49](../005-todo/49-smooth-index-writes.md), "Investigate smooth
   index writes", whose main candidate is a paced take: each commit writes
   index nodes in proportion to its puts. It comes before 007-03's steps 3
   and 4. D1 still has a place, as the backstop: a paced take that also
   takes every transaction that begins at least d_h before the end keeps
   up with d_h, which is all T3 needs, and the deadline then acts only if
   the pace falls behind.

3. **A cold startup takes minutes on a slow disk, and neither 007 nor 009
   bounds it.** After the OS cache was dropped, startup took 9 s at 1M
   keys, 175 to 194 s at 10M and 287 to 303 s at 18.4M keys on s1, at a
   startup distance of 10 MB. With a warm cache it took 1.5 s at 10M on
   F53, and 15 to 17 s at 100M, partly from the SSD
   ([004-02](../004-indirect-swizzling/02-scale-tests.md), 10.5.8, measured
   the night after 007-01 was written). By two stack samples and the
   process's I/O counters, the time goes to rule 4: `DbStarter.linkD` calls
   `NodeCollection.idOf` for each stream pointer of D's nodes that
   startup's maps do not resolve, and each call reads the pointee's header
   from the stream to learn its id: about 590,000 random reads at 10M keys.
   009 left the cold startup out (009-01, section 1, "Not in 009") and
   measured it unchanged with handles: 191 to 200 s, against 197 s for
   2026.1 ([009-03](../009-handles/03-measurements.md), section 6).
   `NodeCollection.linkToCanonical` still calls `idOf`. 007-01 (5.3)
   expected the rerun's first touches to dominate a cold startup; it is
   rule 4. T3 and the deadline bound what startup reads in order and
   reruns, not these reads, whose number follows D's pointers. The measured
   startups had a startup distance of 10 MB; at the distances of 1, D held
   0.34 to 4.6 million nodes at its largest. How many reads that gives is
   not known.

4. **With handles, D is the floor of the resident memory.** The capacity
   controller's trigger is the budget, or the pinned bytes plus the gap
   between its watermarks if that is more (009-02, section 9), and D's
   nodes are pinned. So when D outgrows the budget, the resident bytes
   follow D: at the distances of 1, up to 124 MB of node bytes at 50 MB and
   1.57 GB at 1000 MB (stream bytes; the heap holds more). docs/levels.md
   lists it among Level 4's limits ("D bounded only loosely by the startup
   distance"). So T4 bounds more than 007-01 said: the records at the ends
   of the section, the memory that eviction cannot free, and the cold
   startup's random reads of 3, unless those are removed.

5. **Startup distances of 200 to 1000 MB for large databases.** Frans,
   2026-10-26, in 005-38: "A startup distance of 10 MB is not reasonable
   for a large database like 10M or 100M keys. For such a database, we
   should use more like 100 MB to 1000 MB for startup distance." 2016's
   notes had 200 MB as "a typical value" (docs/problem.md, R3). A put costs
   less with them (005-38: 681, 373 and 180 bytes of stream at 50, 200 and
   1000 MB, 10M keys), and startup takes longer. At the 29 ms per MB of
   100-byte values measured warm at 20 to 50 MB (docs/levels.md), a section
   of d_h = 2 GB would take about a minute to rerun. A promise of about
   10 s, warm, would hold up to a startup distance of about 170 MB, or
   about 700 MB with 10 kB values (7 ms per MB). The Pub API and
   `Db.setStartupDistance` clamp the distance to 1000 MB, but
   `DbBuilder.startupDistance` takes any int, and 2 × sd overflows an int
   above 1,073 MB.

6. **Fast restart** ([006-06](../006-2026-q4/06-fast-restart.md), Frans's
   idea, 2026-10-26): lower the startup distance for a while before a
   controlled restart, for a short startup with a large distance the rest
   of the time. Its question 2, how the take catches up after a decrease,
   is a workload of 007-03's step 2. With the deadline, the dummy
   transaction that `setStartupDistance` runs takes every transaction that
   the new d_h makes due, in one record, or a few at the record limit. That
   is the "write D now" of 006-06's question 3, at the price of one long
   commit while the other writers wait, and the readers of the stream's
   last file too ([005-46](../005-todo/46-stream-file-lock.md)). And its
   question 4 asks what a changing distance means for T3, whose proof uses
   only the startup pos of the last transaction.

7. **A worst case of about 20 ms for a get or a commit**: 009-01's target 2
   (2026-10-25, for eviction and the collector), after Frans's "We never
   want stop-the-world. Or at least not more than 10 ms or something like
   that." (004-04). Both came after D1. The deadline's price is then the
   longest commit it makes, and the readers it stops while that record is
   appended and forced (005-46), not only the largest record. It acts at
   the waves' peaks (2) and at decreases of the startup distance (6).

8. **The trace checker.** 009's step 4c is changing `TraceExport` and
   `Check/` now. Step 4's later work, the records' lengths in bytes in the
   traces, comes after it.

Not changed by any of it: 005-31's open point (a dirty limit of 1/8 instead
of 15/16, 007-03's step 1), the TODO that step 3 removes (006-05, T7), and
D3.


What it does to the plan
------------------------

The changes made in [007-03](03-plan.md):

* The goal: the promise also covers a startup from a cold disk, and is
  given per startup distance (3, 5).
* Step 2, smaller: the first workload is measured (1). What is left (a
  decrease of the startup distance at runtime, deletes, single puts) runs
  on 005-49's version of WriteBench, at 50, 200 and 1000 MB (5, 6).
* Step 3 follows 005-49's recommendation, and waits for it and for D4 (2,
  6). d_h is computed in a long (5). Its price is the longest commit and
  the readers' waits, not only the largest record (7).
* Step 4 models the take that step 3 chooses, and checks a startup
  distance that changes between transactions (2, 6).
* Step 5 can go first: it needs neither 005-49 nor the deadline. It runs at
  50, 200 and 1000 MB and counts a startup's random reads by source, cold
  on s1 (3, 5).
* Step 6, new and proposed: fewer random reads at startup, rule 4's first
  (3).
* New decisions for Frans: D4, how a decrease of the startup distance
  meets the deadline (6, 7); D5, step 6 in the plan or not (3).
* After the plan: T4 bounds more (4). The trace checker's comparison comes
  after 009's step 4c (8).
