005-03. Investigate the sweep's cost
===================================

Status: done (2026-10-27, by item 009; see Outcome). Kind: investigate.
Created 2026-10-19.


The issue
---------

A performance problem, not a fault: reads stay correct and memory stays
bounded. Item 001's final report, finding 10
([06-final-report.md](../001-lean-model-levels-3-4/06-final-report.md)),
and P4's soak in [docs/level4-evidence.md](../001-lean-model-levels-3-4/10-level4-evidence.md):

* The capacity controller's sweep walks every resident object, twice (the
  sweep and the resync after it), under the write lock, each time a quarter
  of the budget has been loaded.
* In P2's soak workload with eviction (an 8 GB heap, a budget of 1.6 GB,
  below what the readers touch) a sweep took 3.2 s on average, about every
  9 s: 35 percent of the time. The paced writer reached 123.5 of its 200
  commits a second, the readers 60 percent of their pace; the maxima were
  about 4.2 s.
* G1 needed 81 full collections in two hours: evicted objects are old
  garbage by the time they are released.

So eviction costs in proportion to what stays in memory, not to what it
frees. With data much larger than the budget and reads spread over it, that
is most of the time.


Questions
---------

1. How does the cost grow: with the budget, the read churn, the number of
   readers? Where is the time spent (the walk, the lists and maps built per
   sweep, the write lock held, GC)?
2. The cheap steps first (001-06, "What comes next", 1): drop the resync's
   second walk (since J7's fix the sweep's count is exact), and keep the
   walk's lists and maps between sweeps. How much do they give?
3. The structural options, compared on the same workload:
   * an incremental sweep (a bounded slice per load, a clock hand);
   * the incoming-reference lists of Q9;
   * handles, indirect swizzling: item 004's study
     ([004-01](../004-indirect-swizzling/01-report.md)), which also proposes
     taking the pointer lock and the `readSync` monitor off the read path,
     whatever is chosen.
   What each costs in Java, in the Lean model (the physical layer and
   INV-SLOT would change for handles) and in the gates.
4. Can the sweep run without the write lock, or with it held in short
   slices, under the readers' protocol (Q8)?
5. The GC side: does a different collector or setting (ZGC, generational
   ZGC, region size) remove the full collections, independent of the sweep?


Done when
---------

A report (a subitem here, or an item of its own if it grows): the measured
profile, the cheap steps measured, the options compared with a
recommendation, and acceptance targets for a fix (proposed: P4's commits
near P2's, the readers at their pace, warm gets within 10 percent of today,
as Q13). The fix itself is a following item.


First step
----------

Profile P4's workload at a smaller scale (a shorter soak, the same budget
ratio) with JFR, to see where a sweep's time goes, then measure the two
cheap steps.


Size and order
--------------

M for the investigation, mostly machine time on the quiet machine. After
005-01 and 005-02, which change the same part of Java. Read item 004 first;
its recommendation 1 may be the first change either way.


Outcome
-------

2026-10-27, by Claude (Opus 5.5, Claude Code), at Frans's word ("Yes", to
closing 005-03 as done by 009 if handles removed the sweep; 006-09).

Handles, item 009, removed the sweep that this entry is about. Since 009's
step 3b the capacity controller runs batches: CLOCK steps over the node
table from where the last batch stopped, for at most `BATCH_NANOS` (2 ms)
under the write lock, with no walk of the resident objects and no resync
(`Eviction.sweep`, which kept its name; 009-02, 4.7). Readers never take
the write lock; they wake the eviction thread (009, decision T5a). The
questions, answered by 009 rather than by an investigation here:

1. The cost no longer grows with what stays in memory: a batch's work is
   bounded by the maps it takes, whatever the size of the database and of
   the budget. 10M keys on s1 with a 600 MB budget (009-03, section 7):
   1,566 batches, 2.3 s in all, the longest 5 ms, where 2026.1 had 14
   sweeps, 119 s in all, the longest 24.5 s.
2. The cheap steps were not made: the walk they would have trimmed is
   gone.
3. Of the structural options, handles were chosen (004-03) and made
   (009); the batches are the incremental sweep with a clock hand.
4. The batches run under the write lock in slices of at most 2 ms, and a
   writer that waits goes first (009, step 3d).
5. The collector: in P4's soak, ZGC and Shenandoah without generations
   had no stop (009-04, sections 7 and 8); G1 has full collections at
   large heaps (009-03, section 5). Since 2026-10-27 the collector's
   pauses do not count against 009's target 2.

Against this entry's proposed targets: in P4's soak the writer makes its
paced 200 commits a second and the readers 14,624 of their 15,000 reads a
second, where the code before handles made 120 and 8,755 (009-04,
sections 1 and 4; 004-04); eviction took about 1,450 batches, 1.5 s in
all, 2 ms at most. A warm get in memory costs 3 percent more on one thread
under G1 and 11 percent under ZGC, the hop through the handle (009-03,
section 5), against the proposed 10; with 8 threads gets are twice as
fast. The slowest commits and reads left in the soak are reclaim's
physical cuts, 005-46's.
