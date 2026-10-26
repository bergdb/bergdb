009-04 Shenandoah's stop-the-world in P4's soak
===============================================

Written 2026-10-26 by Claude (Opus 5.5, Claude Code), at Frans's request
("Document the 'two degenerated collections' in 009-04."). The one result of
phase 5 that misses target 2 of 009-01, and why the merge waits for Frans.
The run's outputs are in
[03-measurements/f53-block2/](03-measurements/f53-block2/) (`soak/`, and
`runs.txt`); the GC log stayed on F53 (java/build/soak/p4-009-shen/ of the
branch's worktree, 36 MB).


# 1. The run

P4's soak with eviction, 004-04's parameters: 1M keys, a writer paced at 200
commits a second, three readers at 5,000 reads a second each, reclaim with a
retention of 300 s, one restart, a budget of 1.6 GB, an 8 GB heap
(`-Xms8g -Xmx8g`), 30 measured minutes. Generational Shenandoah
(`-XX:+UseShenandoahGC -XX:ShenandoahGCMode=generational`), JDK 27
(Homebrew), F53. The branch at `a04a418`. 2026-10-26, 06:33 to 07:19, after
the same soak under ZGC (05:32 to 06:19).

`SOAK OK`: every get and scan checked, 200.0 commits and 14,624 reads a
second, the paced rates. BergDB's eviction: 1,450 batches, 1.5 s in all, 2 ms
at most; the resident bytes at the budget.


# 2. What happened

Two stops, at uptime 1,651.5 and 1,652.0 s, about 680 s into the measured 1,800:

| GC | Kind | Time | Heap |
|---|---|---|---|
| GC(2426) | Degenerated young collection (in Update Refs) | 182 ms | 8,190 MB to 8,114 MB of 8,192 |
| GC(2428) | Degenerated young collection, upgraded to a full collection | 821 ms | old generation 8,000 MB to 3,834 MB |

Both started with "Cancelling GC: Allocation Failure": a concurrent young
cycle could not finish before the threads that allocate found no free memory.
`gcsum.py` (004-04) counts them as two fallbacks, 1,003 ms; every other pause
of the run was at most 7.4 ms (6,264 pauses, 818 ms in all).

What the readers and the writer saw: the longest backward scan 822 ms and the
longest delay of the writer's pacing 817 ms, at that moment. The longest
commit, 88.5 ms at 1,786 s, and the longest latest get, 10.9 ms, were not at
it.


# 3. Why: the old generation filled with garbage it did not reclaim

The full collection left 3,834 MB of old generation: that much was live. Yet
the old generation had grown, without a drop, for the whole soak:

| Uptime | Old generation used |
|---|---|
| 720 s | 4,937 MB |
| 886 s | 6,250 MB |
| 1,437 s | 7,152 MB |
| 1,651 s | 7,962 MB (of 8,000 it could have) |

So about 4 GB of the old generation was garbage that the collector's own
old-generation work did not take back in time:

* **Mixed evacuations reclaimed less and less.** Early, one reclaimed 876 MB
  (346 s); late, 15 MB (1,564 s: 29 regions, 100 MB moved) and 9 MB (1,625 s:
  15 regions, 53 MB moved). The garbage was spread thinly over many old
  regions, so few were worth evacuating; just before the stop the heap's
  external fragmentation was 41 percent.
* **The young generation was squeezed** to about 120 to 200 MB of capacity,
  so young cycles ran back to back ("Free (Soft) is below minimum threshold
  (819M)"); 439 concurrent cycles were cancelled in the run.

Where such garbage comes from, in BergDB's terms: objects that live long
enough to be promoted and then die, scattered among objects that stay. With
eviction that is what the cache is: a node's object is loaded, lives while
it is used and its handle's CLOCK bit is set, and dies when eviction takes
it, minutes later; values the same with their leaves.

ZGC, on the same workload half an hour earlier, had no stall and no fallback;
its heap after a collection stayed between 3.7 and 5.9 GB at the same points
of the soak.


# 4. Why 004-04 did not see it

004-04 ran the same soak with Shenandoah on 2026-10-24, on the design before
handles: no fallback, pauses at most 0.53 ms. But BergDB then managed 120
commits and 8,755 reads a second of the paced 200 and 15,000: its sweeps held
the writer and the readers. With handles both run at their paced rates, so
the soak loads, evicts and promotes more each second. That is the likely
difference; 004-04's GC log was not kept, so it is not checked.


# 5. What it means for target 2

Target 2 (009-01, section 1): "In P4's soak and in 004-02's runs with
eviction ... under ZGC and under generational Shenandoah, the longest time a
get or a commit is stopped by eviction or by the collector is below about
20 ms."

* ZGC: met (P4's soak: pauses at most 0.02 ms; 004-02's runs: 3.45 ms).
* Generational Shenandoah, 004-02's runs at 10M keys: met (the longest get
  of the thread phases 1.9 to 2.5 ms).
* Generational Shenandoah, P4's soak with an 8 GB heap: missed, by the
  collector, 821 ms. BergDB's own work in eviction stayed at 2 ms a batch.

As decided for this run (the readme's log, 2026-10-25, 20:14), a missed target
stops the work before the merge, for Frans to decide.


# 6. What could be done

Not done, in order of cost:

1. **The same soak with a 12 GB heap** (soak.sh's default; P4 has 8 GB), to
   see whether headroom is enough. Started 2026-10-26 at 07:22; it waited for
   a quiet machine until 08:31 (`mediaanalysisd` kept the load above 2) and
   was stopped. About 50 minutes on a quiet F53.
2. **Shenandoah without generations** (`-XX:ShenandoahGCMode=satb`): every
   cycle sees the whole heap, so thinly spread garbage is found each time; at
   the cost of more marking.
3. **Generational Shenandoah's old-generation tuning**, for example the
   garbage threshold that decides which old regions a mixed evacuation takes.
4. **Less middle-aged garbage from BergDB**: fewer objects per resident node
   (004-01's off-heap direction, which 009-01 leaves out), or an eviction
   order that takes objects before they are promoted. A design question, not
   a fix.

Meanwhile the guidance that 004-04 gave stays: for pauses near 20 ms under
eviction, ZGC; Shenandoah with its heap and mode to be settled by (1) and (2).
