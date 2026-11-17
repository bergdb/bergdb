004-04. ZGC on today's code
===========================

JVM garbage collection. Options for this. Performance and lenght of
stop-the-work pauses. 

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-24, at Frans's request: "OK,
for now: start with 'the ZGC run on today's code, which is cheap and decides the GC
assumption'." It follows the discussion after 004-03 of what is missing before a plan for
handles: handles remove the sweep, but not the full collections that G1 runs under
eviction.

Status: **done 2026-10-25 06:30**: runs from 2026-10-24 16:43 to 2026-10-25 06:30,
unattended (Frans: "Run the testing. Work unattended if possible. You have until Sunday
morning at 08:00 to finish."). Results in section 3: only the concurrent collectors, ZGC
and generational Shenandoah, keep the GC's pauses below 10 ms under eviction.

Frans's target, 2026-10-24, after the explanation of G1's full collections: "We never want
stop-the-world. Or at least not more than 10 ms or something like that. If we are limited by
Java's GC, I guess that is it. But if we can improve this somehow, we should. This obviously
affects the worst-case read and write times."


## 1. The question

Evicted objects have lived through several collections, so G1 has moved them to its old
generation by the time BergDB releases them. G1 frees old garbage only after a concurrent
marking cycle has found it. When eviction fills the old generation faster than that, G1
runs out of free regions to copy into (an evacuation failure) and falls back to a full
collection: every thread stops while the whole heap is marked and compacted, for a time
that grows with the live heap. Handles do not change this; eviction makes the same garbage.

* **P4** ([docs/level4-evidence.md](../001-lean-model-levels-3-4/10-level4-evidence.md); 8 GB heap, budget 1.6
  GB, two measured hours): 81 full collections, 22.7 s in all, median 0.27 s, and 392
  evacuation failures. A typical one: `Pause Full (G1 Compaction Pause) 8192M->1473M(8192M)
  269 ms`, the heap full and 82 percent of the old regions garbage (2,034 regions to 368).
* **004-02's 100M load** (budget 8 GB, heap 20 GB): during its sweep of 266 s, two full
  collections, 19,817 MB to 16,134 MB in 12.7 s and 16,134 MB to 16,106 MB in 16.3 s. The
  live heap, 16.1 GB, was about twice what BergDB counted as resident when the sweep began
  (7.8 GB); what the rest was is not measured.

ZGC, generational in JDK 27 (the only mode left), marks and compacts while the program runs;
its pauses stay below a millisecond whatever the heap's size. Its costs: no compressed
references (64-bit colored pointers, so every reference takes 8 bytes instead of 4, and
BergDB's pointer arrays double), barriers on reference loads, CPU for its own threads, and
a failure mode of its own, the allocation stall: a thread that allocates waits until the
collector has freed memory.

* **Z1 Pauses.** With eviction at work: the longest GC pause, full collections, allocation
  stalls, and the longest waits of gets and commits.
* **Z2 Memory.** The heap per key without eviction; the heap that a budget needs.
* **Z3 Speed.** Gets in memory and from the OS cache, the load's puts a second, the soak's
  commits and reads; the sweep's time.
* **Z4 CPU.** The process's CPU time (user and system) for the same work.

How it decides: if ZGC removes the full collections without allocation stalls, at a cost in
memory and speed that Frans accepts, the plan for handles assumes ZGC, and allocates a
handle right before its object (ZGC keeps the allocation order, 004-02 part B). Otherwise
the plan assumes G1 and must bound its full collections some other way.


## 2. The runs

F53 only (MacBookPro18,3, OpenJDK 27 from Homebrew). bergdb `4fdec5b` built in a scratch
clone, `bergdb.jar` SHA-256 `e6d52dc6ac78aafb7fb150d65c49c360cab35e183766f4a6b0597171af4281db`.
Each configuration runs with G1 and with ZGC, back to back, with 004-02's flags otherwise
(`-Xms` equal to `-Xmx`, `AlwaysPreTouch` for ScaleBench, `gc*` and `safepoint` logged).
The tools are unchanged: 004-02's ScaleBench and `java/stress/Soak.java` (`soak.sh`, which
takes `GC=g1|zgc`). [javatime.sh](04-zgc/javatime.sh) runs each JVM under `/usr/bin/time
-l` for its CPU time and peak RSS. The script: [run.sh](04-zgc/run.sh).

| Run | What | Heap | With G1 before |
|---|---|---|---|
| m-10m | 10M key24 keys loaded with no eviction (M), then the get phases in the same JVM | 6 GB | 004-02: 98 s, 243 bytes of heap per key |
| c-10m-b133 | the same database, budget 133 MB, the stream in the OS cache (C) | 600 MB; ZGC also 1,200 MB | 004-02: 49 full collections, longest sweep 0.6 s |
| c-10m-b665 | the same, budget 665 MB | 2,660 MB | 004-02: 12 full collections, longest sweep 6.0 s |
| p4z | P4's soak, shortened: 1M keys and 1,000 long ones, 1,000-byte values, retention 5 minutes, a writer at 200 transactions a second, 3 readers at 5,000 operations a second, a budget of 1.6 GB; 30 measured minutes and one restart instead of two hours and three | 8 GB | P4: 81 full collections in two hours |

Order: the ScaleBench block (about 35 minutes), then the soak with G1 and with ZGC (about an
hour each, with P4's warm-up of about 20 minutes). Each block waits for a quiet machine as
in 004-02 (`quiet.sh`: a load below 2.0, no other JVM or gate, no Claude session busy from
05:00 to 22:00, nothing from 02:00 to 05:00).

Further runs, after these, if a quiet window lets them end before Sunday 06:45
([run2.sh](04-zgc/run2.sh)): the two M runs again (the first ZGC one overlapped this
session's work on Frans's next message); **Shenandoah** in its generational mode, concurrent
like ZGC but with compressed references, on the same runs and the soak (if ZGC's 8-byte
references cost too much memory, this is the other concurrent collector); and **G1 with a
pause goal of 10 ms** (`-XX:MaxGCPauseMillis=10`) at the 665 MB budget.

Not in this run: s1 (two virtual CPUs, where a concurrent collector's threads compete with
BergDB's), the 100M sizes, G1 with a larger heap per budget.


## 3. Results

Runs: the ScaleBench block on 2026-10-24 from 16:43 to 17:12, the soaks from 20:08 to 20:58
(G1) and 21:14 to 22:08 (ZGC), run2.sh's block from 22:19 to 22:45 (the M runs again,
Shenandoah, G1 with a 10 ms goal), each on a quiet machine with every Claude session idle.
The first ZGC M run overlapped this session's work from 16:49; its repeat at 22:24 agreed
within 2 percent. The night gave no further quiet window (the 1-minute load stayed near
2.0), so run2.sh skipped the Shenandoah soak at its deadline; it was started by hand on
Sunday at 05:38, without the quiet wait, beside this session's analysis. Every run ended
`SCALEBENCH OK` or `SOAK OK`, with every value read checked. The figures below come from
the runs' outputs and [gcsum.py](04-zgc/gcsum.py)'s summaries of their GC logs; the outputs
were not kept in the repository.

### 3.1 Summary

1. **Only the concurrent collectors meet the 10 ms target.** ZGC's pauses were at most 0.02
   ms in every run, and its longest safepoint, the time to reach it included, 3.9 ms (once,
   in the soak; 0.9 ms elsewhere). Shenandoah's pauses were at most 0.53 ms, and its longest
   safepoint 0.55 ms. Neither fell back: no allocation stall, no degenerated or full cycle.
   G1 paused up to 230 ms in ScaleBench and 344 ms in the soak (a safepoint of 477 ms), ran
   full collections in every run with eviction (47 at a budget of 133 MB, 11 at 665 MB, 19
   in the soak's 30 minutes), and paused 150 to 175 ms during the load without any
   eviction. With a pause goal of 10 ms, G1 still paused up to 58 ms, and 384 times above
   10 ms.
2. **What G1's pauses do to reads.** In the phases without a sweep (10M keys, budget 665
   MB), the longest of a million timed gets: 216 ms with G1 (one young pause), 15 ms with
   G1 at a 10 ms goal, 0.27 ms with ZGC, 0.38 ms with Shenandoah.
3. **Today's worst case is the sweep, and the concurrent collectors make it slower.** The
   sweep walks every resident object; a sweep took 24 to 35 percent longer under ZGC (soak:
   4.1 s at most against 2.9 s; 7.7 s against 6.0 s at 665 MB), and under Shenandoah 3
   percent longer at 133 MB, 20 percent in the soak and 28 percent at 665 MB. So with
   today's code the soak's longest commit and get were longer with ZGC (4.5 s) and
   Shenandoah (3.5 to 3.8 s) than with G1 (3.1 to 3.4 s). Handles remove the sweep; then
   the collector's pauses are the worst case, and only ZGC and Shenandoah keep them below
   10 ms.
4. **The costs.** ZGC: 30 percent more heap per key (316 against 243 bytes: no compressed
   references, so every pointer takes 8 bytes), 13 percent fewer gets a second in memory on
   one thread and 7 percent fewer on eight, a 7 percent slower load, 8 percent fewer
   commits and reads in the soak. Shenandoah: 3 percent more heap per key (251 bytes), 10
   percent fewer gets in memory on one thread and 3 percent fewer on eight, a 7 percent
   slower load, 5 percent fewer commits and reads in the soak. With the OS cache, where
   loads set the cost, a get took the same with all three (p50 5.0 to 5.1 µs). ZGC needed
   no more heap than G1: 4.5 times the budget gave no stall.
5. **What is left are safepoints.** With a concurrent collector, the stops left are
   safepoints, mostly the time for every thread to reach one. Once, under Shenandoah, a
   thread dump (ScaleBench's sampling, not BergDB) waited 152 ms for a thread to reach its
   safepoint; a GC safepoint at that moment would have waited as long. Which code runs that
   long without a safepoint poll is not known yet.

### 3.2 GC pauses

Longest safepoint: the longest stop for any operation but ScaleBench's thread dumps (and,
in the M runs, the full collections that ScaleBench asks for with `System.gc()` to measure
the heap). Soak: its 30 measured minutes.

| Run | Collector | Pauses, in all | Longest pause | Above 10 ms | Full, degenerated | Evacuation failures, stalls | Longest safepoint |
|---|---|---|---|---|---|---|---|
| M 10M | G1 | 8 young, 0.9 s | 174 ms | 8 | 0 | 0 | 174 ms |
| M 10M | ZGC | 55, 0.3 ms | 0.01 ms | 0 | 0 | 0 | 0.28 ms |
| M 10M | Shenandoah | 34, 5.7 ms | 0.41 ms | 0 | 0 | 0 | 0.43 ms |
| C 10M, 133 MB | G1 | 855, 8.9 s | 44 ms | 406 | 47 full, 1.2 s | 340 | 59 ms |
| C 10M, 133 MB | ZGC, 600 MB | 1,711, 12 ms | 0.02 ms | 0 | 0 | 0 | 0.94 ms |
| C 10M, 133 MB | ZGC, 1,200 MB | 446, 2.9 ms | 0.01 ms | 0 | 0 | 0 | 0.12 ms |
| C 10M, 133 MB | Shenandoah | 1,016, 177 ms | 0.38 ms | 0 | 0 | 0 | 0.43 ms |
| C 10M, 665 MB | G1 | 136, 9.6 s | 230 ms | 101 | 11 full, 1.7 s | 60 | 230 ms |
| C 10M, 665 MB | G1, 10 ms goal | 450, 7.3 s | 58 ms | 384 | 0 | 0 | 58 ms |
| C 10M, 665 MB | ZGC | 399, 3.1 ms | 0.02 ms | 0 | 0 | 0 | 0.36 ms |
| C 10M, 665 MB | Shenandoah | 670, 96 ms | 0.36 ms | 0 | 0 | 0 | 0.42 ms |
| Soak | G1 | 446, 41.6 s | 344 ms | 330 | 19 full, 4.7 s | 89 | 477 ms |
| Soak | ZGC | 415, 3.4 ms | 0.02 ms | 0 | 0 | 0 | 3.9 ms |
| Soak | Shenandoah | 790, 133 ms | 0.53 ms | 0 | 0 | 0 | 0.55 ms |

G1 spent 2.3 percent of the soak's time in pauses (P4: 2.4 percent), and its 19 full
collections in 30 minutes match P4's 81 in two hours. ZGC's longest safepoint in the soak,
3.9 ms, was spent at the safepoint, not in reaching it, while the GC's own pause in it took
0.02 ms or less; the operating system may have descheduled the VM thread.

### 3.3 Gets, loads and sweeps

| | G1 | ZGC | Shenandoah |
|---|---|---|---|
| M: load, puts a second | 99,100 and 105,400 | 94,600 and 95,800 | 94,900 |
| M: heap per key after the load | 243 B | 316 and 318 B | 251 B |
| M: gets a second, 1 thread (uniform) | 712,000 and 722,000 | 626,000 and 617,000 | 642,000 |
| M: gets a second, 8 threads | 2.23 M and 2.23 M | 2.06 M and 2.09 M | 2.16 M |
| M: get p50 and longest of a million timed | 1.34 to 1.38 µs; 38 to 179 µs | 1.46 µs; 28 to 30 µs | 1.42 µs; 33 µs |
| C 133 MB: gets a second, 1 thread | 54,700 | 51,700 (1,200 MB: 53,000) | 55,500 |
| C 133 MB: sweeps, mean and longest | 306 ms, 584 ms | 380 ms, 720 ms | 315 ms, 673 ms |
| C 665 MB: get p50, p99, longest (no sweep) | 5.02, 10.8 µs, 216 ms (10 ms goal: 15 ms) | 5.06, 11.0 µs, 0.27 ms | 5.09, 11.1 µs, 0.38 ms |
| C 665 MB: sweeps, mean and longest | 5.3 s, 6.0 s | 7.1 s, 7.7 s | 6.8 s, 7.1 s |
| RSS at most, C 665 MB | 3.0 GB | 3.7 GB | 3.2 GB |

Two values where the run was done twice (G1 and ZGC in M). In C with 133 MB every timed
pass had sweeps, so its longest gets (0.3 to 0.6 s) are sweeps under all three.

### 3.4 The soak

| | G1 | ZGC | Shenandoah |
|---|---|---|---|
| Commits a second (paced at 200) | 126.5 | 116.1 | 120.0 |
| Reads a second (paced at 15,000) | 9,206 | 8,471 | 8,755 |
| Commit (append): p50, p99, p99.9, longest | 0.37 ms, 5.0 ms, 2.3 s, 3.4 s | 0.34 ms, 4.9 ms, 2.7 s, 4.5 s | 0.34 ms, 4.9 ms, 2.7 s, 3.8 s |
| Get, latest: p50, p99, p99.9, longest | 2.2 µs, 49 µs, 3.4 ms, 3.1 s | 2.0 µs, 48 µs, 3.6 ms, 4.5 s | 2.0 µs, 48 µs, 3.6 ms, 3.5 s |
| Sweeps: count, total, longest | 141, 336 s, 2.9 s | 144, 457 s, 4.1 s | 144, 410 s, 3.5 s |
| GC pauses: in all, longest | 41.6 s, 344 ms | 3.4 ms, 0.02 ms | 133 ms, 0.53 ms |
| CPU time of the whole run (user and system) | 4,391 s in 3,045 s | 3,877 s in 3,264 s | 4,221 s in 3,186 s |
| RSS at most | 9.0 GB | 10.0 GB | 9.2 GB |

The soak's tail is the sweep under every collector: the slowest commits overlapped a sweep,
with G1 also a GC pause of up to 344 ms. The concurrent collectors' commits and reads fell
with their slower sweeps (a sweep took 33 percent longer on average under ZGC, 20 percent
under Shenandoah). Both used less CPU than G1 for the whole run although they ran longer:
G1's evacuation failures and full collections cost CPU too. The Shenandoah soak ran on
Sunday morning without the quiet wait, beside this session's analysis; the soak is paced,
so this touches its throughput little and its pauses not at all.

### 3.5 What it means for the plan

* **Assume a concurrent collector.** G1 cannot keep pauses near 10 ms with BergDB's
  eviction, not even with a 10 ms goal, and not even during a load without eviction. The
  plan for handles assumes ZGC or generational Shenandoah, and its acceptance targets
  include the longest safepoint, not only the longest get.
* **ZGC or Shenandoah.** ZGC has the smallest pauses and ships with every JDK. Shenandoah
  keeps compressed references, so it costs 3 instead of 30 percent heap per key (the MEM
  metric), with pauses below half a millisecond; but Oracle's JDK builds do not include it
  (most other OpenJDK builds, Homebrew's among them, do). Both cost 10 to 13 percent of
  in-memory get throughput on one thread. To decide with Frans; BergDB could support both.
* **Handles under a concurrent collector.** ZGC keeps the allocation order, where G1's
  evacuation puts a handle next to its object (004-02, part B); Shenandoah was not
  measured. So a handle must be allocated right before its object, as 004-01's loader
  sketch does.
* **Whole-memory walks get slower.** A walk of the resident set takes up to a third longer
  under the concurrent collectors. Handles remove the sweep's walks; any walk that
  stays (the audit, an accounting resync) should not be on a path that readers wait for.
* **Safepoints.** The remaining stop-the-world is the time to reach a safepoint. One
  thread dump under Shenandoah waited 152 ms for one; the prototype's runs should log
  safepoints and find any code that delays them.
* **Not measured here:** a machine with few cores (s1), where a concurrent collector's
  threads compete with BergDB's; the 100M sizes; BergDB with handles (no sweep), where
  only the collector's pauses and the safepoints are left.
