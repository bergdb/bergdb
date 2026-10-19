005-03. Investigate the sweep's cost
===================================

Status: open. Kind: investigate. Created 2026-10-19.


The issue
---------

A performance problem, not a fault: reads stay correct and memory stays
bounded. Item 001's final report, finding 10
([06-final-report.md](../001-lean-model-levels-3-4/06-final-report.md)),
and P4's soak in [docs/level4-evidence.md](../../docs/level4-evidence.md):

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
