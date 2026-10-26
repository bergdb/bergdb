009-04 Shenandoah's stop-the-world in P4's soak
===============================================

Written 2026-10-26 by Claude (Opus 5.5, Claude Code), at Frans's request
("Document the 'two degenerated collections' in 009-04."). The one result of
phase 5 that misses target 2 of 009-01, and why the merge waits for Frans.
The run's outputs are in
[03-measurements/f53-block2/](03-measurements/f53-block2/) (`soak/`, and
`runs.txt`); the GC log stayed on F53 (java/build/soak/p4-009-shen/ of the
branch's worktree, 36 MB).

Sections 7 and 8 added 2026-10-27 by Claude (Opus 5.5, Claude Code): the
two soaks of section 6 that Frans scheduled ("009-04. Schedule this work to
22:30 tonight."), and what they settle. Their outputs are in
[04-shenandoah-degenerated/](04-shenandoah-degenerated/).


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

As of 2026-10-26, 08:45; section 8 has the state after the soaks of section
7.

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
   was stopped. About 50 minutes on a quiet F53. Run in the evening:
   section 7.1.
2. **Shenandoah without generations** (`-XX:ShenandoahGCMode=satb`): every
   cycle sees the whole heap, so thinly spread garbage is found each time; at
   the cost of more marking. Run in the evening: section 7.2.
3. **Generational Shenandoah's old-generation tuning**, for example the
   garbage threshold that decides which old regions a mixed evacuation takes.
4. **Less middle-aged garbage from BergDB**: fewer objects per resident node
   (004-01's off-heap direction, which 009-01 leaves out), or an eviction
   order that takes objects before they are promoted. A design question, not
   a fix.

Until (1) and (2) ran, the guidance that 004-04 gave stayed: for pauses near
20 ms under eviction, ZGC; Shenandoah with its heap and mode to be settled by
(1) and (2). Section 8 has what they settled.


# 7. The two soaks of section 6

P4's soak as in section 1, the same jar (the branch at `a04a418`, which
`main` merged), JDK 27, F53, after the quiet check (load 1.9, the other
sessions idle), on 2026-10-26:

* generational Shenandoah with a 12 GB heap (section 6, point 1), 22:47 to
  23:34;
* Shenandoah without generations, `-XX:ShenandoahGCMode=satb` (JDK 27's
  default mode), with P4's 8 GB (point 2), 23:34 to 00:20.

Both `SOAK OK`: every get and scan checked, 200 commits and 14,624 reads a
second, the paced rates; BergDB's eviction about 1,460 batches, 1.5 s in
all, 2 ms at most, the resident bytes at the budget. The script
(`f53-009d.sh`), the runs' summaries and outputs, and the cycle tables
(`series-*.txt`, made from the GC logs by `shenseries.py`) are in
[04-shenandoah-degenerated/](04-shenandoah-degenerated/); the GC logs stayed
on F53 (java/build/soak/ of the branch's worktree).

The four soaks of the branch, the first two from the morning (section 1;
[03-measurements/f53-block2/](03-measurements/f53-block2/)):

| | ZGC, 8 GB | Generational, 8 GB | Generational, 12 GB | Without generations, 8 GB |
|---|---|---|---|---|
| Longest pause of the collector | 0.02 ms | 821 ms | 4.7 ms | 4.1 ms |
| Degenerated or full collections | 0 | 2 | 0 | 0 |
| Time in the collector's cycles | 56 s | 277 s | 102 s | 66 s |
| Heap after a collection, at most | 6.6 GB | 8.2 GB | 11.1 GB | 6.4 GB |
| Longest latest get | 11.8 ms | 10.9 ms | 11.9 ms | 131.5 ms |
| Longest scan | 166 ms | 822 ms | 96 ms | 136 ms |
| Longest commit | 171 ms | 88.5 ms | 165 ms | 132 ms |

The time in cycles is that of the JVM's GC beans over the whole run of
2,794 s, the load and the warmup included. The gets, scans and commits
above 20 ms in the three runs without a stop are not the collector's
(section 7.3).


## 7.1 Generational, 12 GB: no stop, as far as the restart

No degenerated or full collection, pauses at most 4.7 ms: target 2 met in
this run. But the old generation grew as with 8 GB, with more room
(`series-gen-12g.txt`; the old generation's use at the end of the young
cycle nearest each time, as in section 3):

| Uptime | 8 GB | 12 GB |
|---|---|---|
| 720 s | 4.9 GB | 2.5 GB |
| 886 s | 6.3 GB | 4.2 GB |
| 1,437 s | 7.2 GB | 7.5 GB |
| 1,651 s | 8.0 GB, the stop | 8.6 GB |
| 1,889 s | | 10.35 GB |
| 1,891 s | | 3.9 GB |
| the end | 5.5 GB | 4.9 GB |

Each old marking before 1,881 s found 0.6 to 1.7 GB that a mixed
evacuation could take (`old-marks-gen-12g.txt`), and from 1,650 s a young
cycle came every 2.6 s on average, eight from 1,881 to 1,889 s. The soak's
restart at 1,881.6 s made the first database's objects garbage: the old
marking that followed, at 1,890 s, found 6.8 GB to take over 2,198 regions,
and the old generation fell from 10.35 GB to 3.9 GB in two seconds.

So 12 GB carried this soak to its restart, and the restart emptied the old
generation. Whether 12 GB holds without restarts, or through P4's two
hours, this run does not show: until the restart the old generation's
growth did not stop. The 8 GB run had gone further the same way when it
stopped: 1,087 young cycles in the 150 s before its stop, seven a second,
and its old marking preempted by young cycles 435 times, against once in
the 12 GB run.


## 7.2 Without generations, 8 GB: no stop, and room to spare

No degenerated or full collection, pauses at most 4.1 ms, with P4's 8 GB
heap. Every cycle marks the whole heap: 159 cycles, 0.49 s of marking on
average (0.62 s at most). At the end of a cycle in the measured phase the
heap held 2.4 to 6.1 GB, on average 5.3 GB in the first fifth of the phase
and 5.2 GB in the last, and at least 1.65 GB was free
(`series-satb-8g.txt`). A cycle starts when the free memory falls below
0.8 GB (10 percent of the heap; 153 of the 159 started so); at the 77 MB a
second that the soak allocated between cycles, a cycle of 0.7 s uses about
50 MB of it.

More marking than with generations, as section 6 expected: 78 s, against
44 s with 12 GB (young and old). But less time in the collector in all,
66 s against 102 s: a young cycle with generations also scanned the
remembered set (54 ms on average) and spent 263 ms updating references, a
cycle without them 134 ms.


## 7.3 Beside the collector: reclaim's physical cuts

In all four soaks the slowest commits are the same three: the measured
phase's physical cuts (reclaim, Level 3) at uptime 1,786, 2,106 and 2,531
s, which deleted 11, 2 and 4 of the stream's files (2.3, 1.0 and 2.0 GB):
88 to 171 ms, 17 to 31 ms and 46 to 96 ms across the four runs, about 8 to
24 ms a file. `FileStream.pretruncate` deletes the files and forces the
directory after each, all under the stream's monitor, and every stream read
takes that monitor to find its file (`findFile`). So every get or scan that
loads from the stream while a cut runs waits for the whole cut. The longest
reads match the cuts within a few milliseconds where the collector did not
stop (ZGC 166 ms against 171; without generations 136 and 131.5 ms against
132; generational with 12 GB 96 ms against 96), with no collection or batch
under them.

It is reclaim's stop, not eviction's or the collector's, so outside target
2; for the pause target of about 20 ms it is one under every collector. It
is added to [005-46](../005-todo/46-stream-file-lock.md), the stream's
other lock that readers wait on.


# 8. What the soaks settle

* **ZGC:** met target 2 in every run (section 5).
* **Shenandoah:** met target 2 in P4's soak without generations, with P4's
  8 GB heap (4.1 ms). Generational: missed with 8 GB (821 ms); met with
  12 GB in this soak (4.7 ms), but only as far as the restart that emptied
  its old generation. In 004-02's runs at 10M keys generational Shenandoah
  met it (1.9 to 2.5 ms); those runs were not made without generations.
* **Why, as far as the logs show:** with generations, objects of BergDB's
  cache that live for minutes are promoted and then die spread thinly over
  old regions, of which mixed evacuations take little (section 3; in the
  12 GB run each old marking before the restart found 0.6 to 1.7 GB to
  take, while the 8 GB run's old generation held about 4 GB of garbage at
  its stop). Without generations every cycle marks the whole heap and may
  take any region, and in this soak that kept up.
* **So, for BergDB with eviction under Shenandoah:** its default mode,
  without generations. 009-01's target 2 names generational Shenandoah;
  whether it should name the default mode instead is Frans's decision. If
  so, 004-02's runs (ScaleBench at 10M keys) in that mode would complete the
  evidence, about 35 minutes on F53, and section 6's points 3 and 4 are not
  needed for target 2.
* **Beside the collector:** reclaim's physical cuts stop commits, and the
  reads that load from the stream, for up to 171 ms under every collector
  (section 7.3; 005-46).

[docs/levels.md](../../docs/levels.md), section 7 (Level 4's limits), says
this since 2026-10-27.
