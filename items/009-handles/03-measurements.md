009-03 Measurements
===================

Started 2026-10-25 by Claude (Opus 5.5, Claude Code), during Frans's
unattended run of 009 ("I want you to work on the 009 implementation until
completion."). The runs of phase 3 and phase 5 (009-01, section 4; 009-02,
section 5): what each step of the branch `009-handles` does to pauses,
gets, memory and the barriers, against release 2026.1, in turns on one
machine. The raw outputs are in [03-measurements/](03-measurements/);
`ppsum.py` makes the tables from the pause probe's outputs.


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
