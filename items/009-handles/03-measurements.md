009-03 Measurements
===================

Started 2026-10-25 by Claude (Opus 5.5, Claude Code), during Frans's
unattended run of 009 ("I want you to work on the 009 implementation until
completion."). The runs of phase 3 and phase 5 (009-01, section 4; 009-02,
section 5): what each step of the branch `009-handles` does to pauses,
gets, memory and the barriers, against release 2026.1, in turns on one
machine. The raw outputs are in [03-measurements/](03-measurements/);
`ppsum.py` and `sbsum.py` make the tables from the pause probe's and
ScaleBench's outputs.


# 0. Where the targets stand

Targets 2 to 4 of 009-01, section 1, against 2026.1 in turns, with the
branch at step 3d (`66c8f3a`), as of 2026-10-26, 00:30:

* **Target 2, pauses (about 20 ms with ZGC or generational Shenandoah).**
  Met with ZGC on F53: in 004-02's run from the OS cache at 10M keys and
  665 MB (section 5), the longest get of the 1 to 8 thread phases took
  3.45 ms (2026.1: 7.3 s); in the pause probe, gets and single-put commits
  14.7 ms at most (2026.1: 570 ms). On s1, from the device, the longest get
  was 60 ms (2026.1: 2.6 s), and the waits above 20 ms there are the
  device's reads and two CPUs shared by the readers, the eviction thread
  and the collector, with no collection or batch under them. Shenandoah in
  the pause probe: one full collection of 79 ms and degenerated cycles, as
  the probe's 1.2 GB heap filled at 700,000 loads a second (the collector,
  not eviction). Not yet run: P4's soak, and ScaleBench with Shenandoah
  (planned for F53 after 05:00, section 8).
* **Target 3, gets.** In memory on one thread: 3 percent fewer with G1, 11
  percent fewer with ZGC (target: within 20 percent). With 4 threads 12 and
  3 percent more, with 8 threads 101 and 61 percent more (target: more).
  From the OS cache 1.4 to 4.6 times as many gets a second, from s1's device
  the same on one thread and 32 to 53 percent more with 4 (target: no
  difference beyond the noise).
* **Target 4, memory.** MEM 130 bytes per KV (2026.1: 191); heap per key
  after the 10M load 186 bytes under G1 (243) and 225 under ZGC (315).

And beside the targets: the 10M load on s1 with a 600 MB budget took 767 s,
2026.1 3,015 s (step 3e, section 7); the cold startup at 10M keys on s1 is
unchanged (191 to 200 s, 2026.1 197 s); loads in memory (no eviction) are 8
percent slower with G1 and 20 percent with ZGC.


# 1. The pause probe on s1, steps 1d and 3c

`java/stress/PauseProbe.java` (step 1a): 1M keys of 100-byte values on
disk, a writer in transactions of 1 put (phase `tsize=1`) and then of 1,000
puts (`tsize=1000`), two readers of random keys, 60 s a phase, each get and
commit timed. JDK 27 on s1 (two virtual CPUs, x86), `-Xmx1200m`, pretouched;
the capacity controller with a budget of 20 or 100 MB. The startup
distance is the default, 50 MB, which pins about 55 MB: a 20 MB budget is
below the pinned state, 100 MB above it. Script:
[run-pp.sh](03-measurements/s1-probe/run-pp.sh) and
[run-pp2.sh](03-measurements/s1-probe/run-pp2.sh); 2026-10-25, 21:17 to
22:01, s1 to itself. Jars: 2026.1 (`4d90eb92`), `main` at step 1d
(`67638ad7`), the branch at step 3c (`c223edb2`).

Times in ms; "resident" is the controller's resident bytes at the end of
the phase (2026.1 and 1d: after the last sweep); "longest batch" is the
longest sweep or batch so far.

| run | phase | gets | p99.9 | max | commits | p99.9 | max | resident | longest batch |
|---|---|---|---|---|---|---|---|---|---|
| 2026.1 G1, 20 MB | tsize=1 | 824,022 | 4.2 | 778 | 221,900 | 7.3 | 777 | 54 MB | 776 |
| 2026.1 G1, 20 MB | tsize=1000 | 633,999 | 2.1 | 2,464 | 213 | 2,147 | 2,503 | 65 MB | 836 |
| 2026.1 ZGC, 20 MB | tsize=1 | 835,732 | 4.2 | 716 | 223,869 | 8.4 | 715 | 54 MB | 714 |
| 2026.1 ZGC, 20 MB | tsize=1000 | 702,458 | 2.1 | 772 | 242 | 805 | 826 | 58 MB | 763 |
| 1d G1, 20 MB | tsize=1 | 806,354 | 4.2 | 702 | 231,236 | 7.3 | 703 | 51 MB | 728 |
| 1d G1, 20 MB | tsize=1000 | 639,483 | 2.1 | 959 | 219 | 940 | 1,014 | 66 MB | 956 |
| 1d ZGC, 20 MB | tsize=1 | 780,103 | 4.2 | 711 | 212,994 | 8.4 | 715 | 61 MB | 710 |
| 1d ZGC, 20 MB | tsize=1000 | 689,649 | 2.1 | 759 | 228 | 671 | 790 | 64 MB | 757 |
| 3c G1, 20 MB | tsize=1 | 9,684,632 | 1.8 | 61 | 2,583 | 84 | 110 | 138 MB | 84 |
| 3c G1, 20 MB | tsize=1000 | 6,557,831 | 1.8 | 217 | 876 | 336 | 377 | 109 MB | 104 |
| 3c ZGC, 20 MB | tsize=1 | 5,726,320 | 2.6 | 52 | 110,950 | 25 | 172 | 110 MB | 75 |
| 3c ZGC, 20 MB | tsize=1000 | 5,419,702 | 2.6 | 49 | 885 | 268 | 290 | 143 MB | 75 |
| 2026.1 G1, 100 MB | tsize=1 | 2,585,765 | 2.1 | 1,369 | 611,571 | 5.2 | 1,371 | 74 MB | 2,084 |
| 2026.1 G1, 100 MB | tsize=1000 | 2,305,425 | 1.8 | 1,091 | 601 | 1,074 | 1,134 | 74 MB | 2,084 |
| 2026.1 ZGC, 100 MB | tsize=1 | 2,465,340 | 2.1 | 1,487 | 572,530 | 5.2 | 1,482 | 74 MB | 3,156 |
| 2026.1 ZGC, 100 MB | tsize=1000 | 2,213,049 | 2.1 | 1,134 | 561 | 1,074 | 1,167 | 74 MB | 3,156 |
| 1d G1, 100 MB | tsize=1 | 2,505,478 | 2.1 | 1,362 | 595,337 | 5.2 | 1,360 | 74 MB | 1,969 |
| 1d G1, 100 MB | tsize=1000 | 2,291,364 | 1.8 | 1,032 | 591 | 1,074 | 1,081 | 75 MB | 1,969 |
| 1d ZGC, 100 MB | tsize=1 | 2,347,740 | 2.1 | 1,531 | 539,722 | 6.3 | 1,531 | 77 MB | 2,837 |
| 1d ZGC, 100 MB | tsize=1000 | 2,311,854 | 2.1 | 1,223 | 586 | 1,074 | 1,263 | 74 MB | 2,837 |
| 3c G1, 100 MB | tsize=1 | 8,159,136 | 1.8 | 100 | 204,299 | 34 | 190 | 153 MB | 102 |
| 3c G1, 100 MB | tsize=1000 | 6,114,276 | 2.1 | 241 | 1,181 | 336 | 381 | 181 MB | 139 |
| 3c ZGC, 100 MB | tsize=1 | 6,169,559 | 2.6 | 384 | 246,946 | 17 | 383 | 107 MB | 34 |
| 3c ZGC, 100 MB | tsize=1000 | 5,228,677 | 3.1 | 67 | 1,085 | 235 | 278 | 133 MB | 63 |

What it says:

* **2026.1 and step 1d stop the world.** Every sweep stops gets and
  commits for its whole length, 0.7 to 3.2 s; the readers do 0.6 to 2.6
  million gets a minute. Step 1d (4,096 maps, reads without `readSync`) is
  2026.1 within the noise.
* **At step 3c no batch stops a get**: 2.4 to 12 times as many gets, the
  longest 49 to 384 ms. But three things are wrong, and step 3d is about
  them: the writer waited for the eviction thread (2,583 commits in a
  minute under G1 at 20 MB, where 2026.1 made 221,900; a monitor is not
  fair, and the thread ran batch after batch); a batch took up to 100 ms
  (65,536 handles under pressure, on two CPUs with two busy readers); and
  the resident bytes went above the budget, to 107 to 181 MB, as the
  values that reads load into pinned leaves stayed (a pinned object is
  never evicted) and as the thread did not keep up with the readers' loads.
* **The load phase** (1,000 transactions of 1,000 puts, not in the table)
  has a commit of 3.5 to 13.4 s in every jar at the 100 MB budget, and the
  GC log shows no collection in it: s1's disk, not eviction or the
  collector. Not part of target 2.


# 2. The jcstress tests of step 3c

`java/stress/jcstress/run.sh` in default mode, jcstress 0.16, against the
jar of step 3c, JDK 27: the four tests of 009-02, 3.5 (a handle published
by a swizzle and read plainly, T6b; an install against a fast-path read;
an eviction against a fast-path read; a value published and read with an
acquire, C5) and a control (a plain store and a plain read of an object
with a plain field), which shows that the harness can see a race. Output:
[f53-3c-default.txt](03-measurements/jcstress/f53-3c-default.txt).

| Test | Samples, F53 (AArch64) | Samples, s1 (x86) | Forbidden seen |
|---|---|---|---|
| HandlePublication | 1,523,335,814 | 1,438,896,774 | 0 |
| InstallPublication | 1,183,890,054 | 870,156,934 | 0 |
| EvictionRace | 1,017,367,174 | 1,425,697,414 | 0 |
| ValuePublication | 1,734,699,654 | 1,443,351,174 | 0 |
| PlainPublication (control) | 5,106,547,334 | 6,296,210,054 | none forbidden; F53 showed the race 166,641 times, s1 never (x86 keeps stores in order) |

s1's output: [s1-3c-default.txt](03-measurements/jcstress/s1-3c-default.txt)
(2026-10-25, 22:16 to 22:32). A forbidden outcome on F53 would have been a
fault of the code or of the argument of 009-02, 3.4; on x86 the hardware
hides most such faults, so F53's runs are the ones that count.

Again on F53 on the final branch (2026-10-26, 01:25; `fb0c770`, where a
reader's swizzle is `Node.swizzle`, which HandlePublication now uses): no
forbidden outcome in 1.1 to 1.9 billion samples a test, the control's race
168,789 times in 5.6 billion
([f53-final-default.txt](03-measurements/jcstress/f53-final-default.txt)).


# 3. Memory: MEM

Props' MEM (`java -cp JAR bergdb.dev.props.Mem`: heap bytes per KV, a
million small KVs, all resident), two runs a jar, on F53, 2026-10-25 at
22:18 (memory, not time: the gate that ran meanwhile does not change it).

| Jar | MEM, bytes per KV |
|---|---|
| 2026.1 | 191, 191 |
| `main`, step 1d (4,096 maps, no CacheEntry) | 174, 173 |
| branch, step 3c (handles) | 130, 130 |

Handles take 32 percent less than 2026.1 (009-02, 4.11, estimated about
135): the node table holds the index nodes' handles only, as values have
no handles and left the table, and an entry is a handle, not a
`CacheEntry` and its node. 004-01 (5.4) expected 3 to 4 percent more for
compact keys, as it counted a handle on top of today's table.


# 4. The pause probe on s1, step 3d

As section 1, on the jar of the branch at `66c8f3a` (`14692722`),
2026-10-25, 22:31 to 22:41. 2026.1's rows from section 1.

| run | phase | gets | p99.9 | max | commits | p99.9 | max | resident | longest batch |
|---|---|---|---|---|---|---|---|---|---|
| 2026.1 G1, 20 MB | tsize=1 | 824,022 | 4.2 | 778 | 221,900 | 7.3 | 777 | 54 MB | 776 |
| 3d G1, 20 MB | tsize=1 | 5,971,049 | 2.1 | 82 | 645,083 | 8.4 | 82 | 41 MB | 69 |
| 3d G1, 20 MB | tsize=1000 | 4,892,950 | 3.1 | 2,696 | 1,478 | 168 | 2,721 | 68 MB | 69 |
| 3d ZGC, 20 MB | tsize=1 | 5,685,931 | 2.6 | 57 | 608,820 | 8.4 | 57 | 46 MB | 46 |
| 3d ZGC, 20 MB | tsize=1000 | 4,680,326 | 3.7 | 1,363 | 1,420 | 117 | 1,416 | 65 MB | 46 |
| 2026.1 ZGC, 100 MB | tsize=1 | 2,465,340 | 2.1 | 1,487 | 572,530 | 5.2 | 1,482 | 74 MB | 3,156 |
| 3d G1, 100 MB | tsize=1 | 8,514,043 | 1.8 | 132 | 2,045,071 | 3.7 | 112 | 99 MB | 107 |
| 3d G1, 100 MB | tsize=1000 | 7,006,443 | 1.8 | 2,672 | 2,173 | 134 | 2,691 | 99 MB | 107 |
| 3d ZGC, 100 MB | tsize=1 | 8,077,749 | 2.1 | 45 | 1,528,274 | 5.2 | 44 | 99 MB | 9 |
| 3d ZGC, 100 MB | tsize=1000 | 6,675,948 | 2.6 | 75 | 1,885 | 117 | 123 | 99 MB | 10 |

* The writer is no longer kept out (645,083 commits where 3c made 2,583),
  and the resident bytes stay at the budget (99 MB) or, below the pinned
  state, near it (41 to 68 MB with 55 MB pinned).
* A batch ends after 2 ms of its own time, but on two CPUs shared with two
  busy readers and the collector it takes up to 107 ms of wall time.
* The waits of 1.4 to 2.7 s in the `tsize=1000` phase have no collection,
  safepoint or batch under them: the readers' reads of the stream file wait
  for the writer's append and its `fsync` on s1's disk (section 7).

Then a batch of the eviction thread also ends when a writer waits (`a04a418`,
jar `274e4e46`), and again on s1, 2026-10-26, 01:38 to 01:48:

| run | phase | gets | p99.9 | max | commits | p99.9 | max | resident | longest batch |
|---|---|---|---|---|---|---|---|---|---|
| ZGC, 20 MB | tsize=1 | 5,882,681 | 2.6 | 40 | 635,552 | 7.3 | 42 | 42 MB | 8.3 |
| ZGC, 20 MB | tsize=1000 | 4,713,131 | 3.7 | 73 | 1,465 | 101 | 130 | 65 MB | 10.9 |
| ZGC, 100 MB | tsize=1 | 7,978,250 | 2.1 | 52 | 1,543,606 | 5.2 | 51 | 99 MB | 11.0 |
| ZGC, 100 MB | tsize=1000 | 6,524,722 | 2.6 | 53 | 1,861 | 134 | 143 | 99 MB | 11.0 |
| G1, 20 MB | tsize=1 | 6,144,494 | 2.1 | 69 | 673,012 | 7.3 | 72 | 43 MB | 67 |
| G1, 100 MB | tsize=1 | 8,385,073 | 1.8 | 107 | 2,066,265 | 3.7 | 104 | 99 MB | 98 |

With ZGC the longest batch fell from 46 to 8 to 11 ms of wall time, and the
longest get and single-put commit are 40 to 52 ms. What is left on s1 is not
a batch, and not the collector's pauses (at most 0.04 ms); ZGC stalled
allocations three times, 42 to 47 ms, at the start of a phase at 100 MB, not
when the longest waits were. It is the readers' wait for the writer's
`fsync` (005-46), which also gave the waits of 1.4 and 2.7 s at 3d with
transactions of 1,000 puts, and two CPUs shared by two busy readers, the
writer, the eviction thread and the collector's threads. With G1, its
pauses (a batch's wall time includes them).


# 5. F53's timed block

`f53-009.sh` ([f53-block/](03-measurements/f53-block/)), 2026-10-25, 22:55
to 23:52, after `quiet.sh` (the Lean session paused, this session idle):
Props twice a jar; the pause probe at 1M keys, 4 readers and a 100 MB budget
with three collectors; and 2026.1's ScaleBench block (`baseline/tools/f53.sh`
of releases/2026.1: 10M key24 keys in memory, M, and from the OS cache, C)
for each jar, ScaleBench ported to the branch by
[ScaleBench-009.diff](03-measurements/ScaleBench-009.diff) (a removed
method reached by reflection). JDK 27 (Homebrew), M1 Pro, 10 cores.

**Props.** MEM 191 and 191 (2026.1), 130 and 130 (branch); CORE 0.29 and
0.29, 0.24 and 0.22 (lower is faster); SS 1.50 for both.

**The pause probe** (ms):

| run | phase | gets | p99.9 | max | commits | p99.9 | max | longest batch |
|---|---|---|---|---|---|---|---|---|
| 2026.1 G1 | tsize=1 | 7,036,720 | 0.10 | 475 | 946,829 | 4.2 | 475 | 797 |
| 2026.1 G1 | tsize=1000 | 5,973,816 | 0.13 | 400 | 892 | 403 | 425 | 797 |
| 3d G1 | tsize=1 | 26,871,270 | 0.07 | 73 | 2,994,493 | 1.3 | 33 | 24 |
| 3d G1 | tsize=1000 | 19,279,886 | 0.20 | 19 | 3,363 | 50 | 75 | 24 |
| 2026.1 ZGC | tsize=1 | 6,520,883 | 0.10 | 567 | 857,646 | 4.2 | 570 | 1,146 |
| 2026.1 ZGC | tsize=1000 | 5,520,077 | 0.13 | 426 | 851 | 470 | 487 | 1,146 |
| 3d ZGC | tsize=1 | 27,416,328 | 0.07 | 14.5 | 2,696,672 | 1.8 | 14.7 | 2.2 |
| 3d ZGC | tsize=1000 | 19,331,701 | 0.20 | 14.6 | 3,167 | 50 | 83 | 2.2 |
| 2026.1 Shenandoah | tsize=1 | 6,910,446 | 0.12 | 451 | 931,650 | 4.2 | 451 | 1,000 |
| 2026.1 Shenandoah | tsize=1000 | 5,828,898 | 0.13 | 394 | 862 | 403 | 418 | 1,000 |
| 3d Shenandoah | tsize=1 | 25,002,891 | 0.08 | 80 | 2,772,611 | 1.6 | 80 | 80 |
| 3d Shenandoah | tsize=1000 | 18,326,189 | 0.20 | 69 | 3,168 | 59 | 82 | 80 |

A commit of 1,000 puts does the transaction's work too: its median is 15 to
17 ms on the branch (2026.1: 29 ms), so its longest, 75 to 83 ms, is not a
stop. With ZGC no get and no single-put commit waited more than 14.7 ms.
With Shenandoah the 80 ms is a full collection (79 ms, `gcsum.py` of
004-04: 23 degenerated or full cycles, 699 ms in all) as the 1.2 GB heap
filled; with G1, its pauses.

**ScaleBench at 10M key24 keys** (gets a second; `sbsum.py`):

| run | startup | uniform, 1 thread | timed max | threads 1 | 2 | 4 | 8 | longest of the thread phases | heap a key |
|---|---|---|---|---|---|---|---|---|---|
| M G1, 2026.1 | | 715,203 | 0.03 ms | 707,118 | 1,233,169 | 2,119,607 | 2,111,922 | 0.78 ms | 243.1 B |
| M G1, 3d | | 693,400 | 0.03 ms | 684,962 | 1,307,728 | 2,381,443 | 4,247,964 | 0.99 ms | 186.0 B |
| M ZGC, 2026.1 | | 625,577 | 0.03 ms | 627,860 | 1,120,133 | 1,886,658 | 2,225,542 | 8.18 ms | 315.0 B |
| M ZGC, 3d | | 554,142 | 0.04 ms | 553,125 | 1,057,006 | 1,934,869 | 3,584,649 | 7.35 ms | 225.0 B |
| C 665 MB G1, 2026.1 | 1.56 s | 178,717 | 186 ms | 133,639 | 195,931 | 208,362 | 151,838 | 5,356 ms | |
| C 665 MB G1, 3d | 1.51 s | 260,181 | 53 ms | 254,787 | 442,212 | 698,702 | 377,500 | 258 ms | |
| C 665 MB ZGC, 2026.1 | 1.61 s | 179,485 | 0.27 ms | 119,847 | 157,849 | 191,197 | 129,618 | 7,253 ms | |
| C 665 MB ZGC, 3d | 1.60 s | 247,592 | 0.27 ms | 239,463 | 412,605 | 601,347 | 391,900 | 3.45 ms | |
| C 133 MB G1, 2026.1 | 1.53 s | 56,978 | 337 ms | 57,294 | 74,676 | 81,648 | 64,455 | 379 ms | |
| C 133 MB G1, 3d | 1.50 s | 107,226 | 12 ms | 107,864 | 176,478 | 262,883 | 176,642 | 12 ms | |

* **In memory (M)** the hop through the handle costs 3 percent of the gets
  on one thread with G1 and 11 percent with ZGC (004-01 measured 9 to 13);
  with more threads the pointer lock and the stamp are gone: 4.2 million
  gets a second with 8 threads where 2026.1 stops at 2.1.
* **From the OS cache (C)** the branch reads less: 1.66 stream reads a get
  at 665 MB where 2026.1 made 2.75 (a pointer's handle has the node's id,
  so no header is read to find it; and CLOCK keeps the upper levels), and
  no sweep stops the readers. With ZGC the longest get of the thread phases
  is 3.45 ms (2026.1: 7.3 s). With G1 it is the collector's: at 665 MB
  (2.66 GB of heap) 9 full collections and 25 evacuation failures, a longest
  safepoint of 212 ms (2026.1: 10, 45 and 257 ms), as 004-04 found.
* The load in memory is slower: 93,503 puts a second against 101,934 under
  G1, 77,782 against 97,192 under ZGC.


# 6. ScaleBench on s1

`s1-009.sh` ([s1-scalebench/](03-measurements/s1-scalebench/)),
2026-10-25, 22:41 to 23:27: the 10M key24 load with a 600 MB budget on the
branch's jar, then from the device (D: caches dropped, a cgroup of the heap
and 300 MB) at 133 MB with the cold startup, the branch and 2026.1 in turns,
G1 and then ZGC, on the same database. 2026.1's load from its release runs
(releases/2026.1, `baseline/s1/`).

| run | startup | uniform, 1 thread | timed max | threads 1 | 2 | 4 | longest of the thread phases |
|---|---|---|---|---|---|---|---|
| D G1, 2026.1 | 197.6 s | 1,130 | 1,380 ms | 1,072 | 3,081 | 3,377 | 1,163 ms |
| D G1, 3d | 199.7 s | 1,115 | 2,690 ms | 1,057 | 2,959 | 5,178 | 68 ms |
| D ZGC, 2026.1 | 196.7 s | 1,108 | 1,485 ms | 1,146 | 2,874 | 3,774 | 2,581 ms |
| D ZGC, 3d | 191.1 s | 1,184 | 60 ms | 1,124 | 3,089 | 4,973 | 60 ms |

From the device the gets on one thread are the device's, the same for both
(the cold startup too, 191 to 200 s). With 4 threads the branch makes 32 to
53 percent more, as no reader waits for a sweep or a pointer lock. The
longest gets of the branch, 60 to 68 ms in the thread phases, overlapped no
collection or batch (ScaleBench's ten slowest gets list what overlapped
them): the device and two CPUs. Its 2.69 s in the timed pass under G1 (and
a 975 ms one) overlapped nothing either: s1's disk.


# 7. Step 3e: 005-38's question, writes at scale on s1

004-02 (10.5.5) found the load of 10M keys on s1 with a 600 MB budget slow,
and asked how much of it was the sweep (005-38). The two loads, same keys,
same budget and heap, G1, same disk:

| | 2026.1 | 3d |
|---|---|---|
| Time, puts a second | 3,015 s, 3,317 | 767 s, 13,045 |
| Sweeps or batches: count, in all, longest | 14, 119 s, 24.5 s | 1,566, 2.3 s, 5 ms |
| Node loads | 343,144 | 960,397 |
| Stream reads | 10,133,190 | 2,014,116 |
| Bytes read from the device | 25.9 GB | 4.6 GB |
| Device reads | 5,936,584 | 945,414 |
| GC pauses: in all, longest | 17.2 s, 464 ms | 6.1 s, 216 ms |

The sweep's own time was 4 percent of 2026.1's load. Most of the rest was
reading back what it evicted, and reading headers: 30 stream reads a node
load, 25.9 GB from the device for a 7.5 GB stream. A sweep takes the oldest
objects, the upper levels of the index among them, and an unswizzled
pointer is followed by a header read to find the node's id. With handles
the id is in the handle, and CLOCK keeps what the writer touches. So
005-38's slowness at 10M keys on s1 was 2026.1's eviction, not the writes;
whether writes at 30M and 100M keys are still slow is for 005-38.

**A second finding, for the stream layer, not 009:** a reader's read of the
stream's last file waits while the writer appends to it, its `fsync`
included (`FileStream.DbFile.read` and `append` are both `synchronized` on
the file). On s1's disk an `fsync` can take seconds, and the pause probe's
longest waits on s1 at step 3d (1.4 to 2.7 s, with transactions of 1,000
puts) are those. Positional reads (`FileChannel.read(buffer, position)`)
need no lock; that is work of its own:
[005-46](../005-todo/46-stream-file-lock.md). The finding of the load went
into [005-38](../005-todo/38-writes-at-scale.md).


# 8. Still to run

* P4's soak with eviction (004-04's parameters: 8 GB heap, a 1.6 GB budget,
  30 measured minutes, a restart) under ZGC and generational Shenandoah on
  the branch; 2026.1's are 004-04's (2026-10-24), the same machine.
* ScaleBench with Shenandoah on both jars (M; C at 133 and 665 MB), as
  004-04's run2.sh.
* `performance.sh ab` with the quick suite, 2026.1 against the branch.

On F53 from 05:00 (`quiet.sh` keeps timed blocks off 02:00 to 05:00, for
`night.sh`).
