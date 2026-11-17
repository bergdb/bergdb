004-02. Measurements at scale and on a second machine
=====================================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-23, at Frans's request:
"Yes, create 004-02 for testing as proposed. Including on my VPS. Before starting, write
a plan for this." What was proposed follows Frans's comments on 004-01 the same morning:
run the measurements on at least one more platform, his VPS; check that a handle stays
next to its node when the collector moves objects; and get a feeling for how a get's cost
grows with the database, at 1M, 10M and 100M keys, as the data leave the processor's
caches, the heap and RAM. The largest cases and the worst cases matter most; small
databases are fast anyway.

Status: **done 2026-10-24: runs on s1 from 2026-10-23 10:24 to 2026-10-24 08:35, on F53
2026-10-23 17:03 to 21:51; results in section 10.** Frans approved the plan the same day with three
answers (section 9): s1 may hold the JDK and the tools afterwards; start now; use keys
longer than 8 bytes, 24 bytes. The tools, scripts and outputs are in `02-scale-tests/`,
the results will be in section 10.


## 1. Questions

* **Q1 Platform.** Do 004-01's results hold on x86 Linux under a hypervisor: what a
  handle, today's pointer lock and stamp, and a hash lookup per edge cost
  (IndirectionBench), and what the read path costs in BergDB (IndexCensus)?
* **Q2 Placement after collections.** Out of cache, a handle was cheap only next to its
  node: 583 ns a lookup, against 647 with its parent's other handles and 874 scattered
  (004-01, 5.1), in a tree allocated in one go. Does that survive the collector moving
  the objects?
* **Q3 Scale.** How do the latency distribution of gets (p50, p99, p99.9, max) and their
  throughput change from 1M to 10M to 100M keys, in three regimes: everything in the heap
  (M); a cache budget smaller than the data, with the stream in the OS file cache (C); the
  same with reads that go to the device (D)?
* **Q4 Cold gets.** How many loads, stream reads and device reads does a get cost when
  the data do not fit? Under pressure today a get loads about two versions, and each load
  reads the stream twice, the node's header for its id and then the node
  ([level4-performance.md](../001-lean-model-levels-3-4/11-level4-performance.md)).
* **Q5 Tails.** What sets the maximum: sweeps (they walk every resident object: 1.5 s on
  average at a budget of 500 MB in J8, 3.2 s at 1.6 GB in P4), collections, the device?
* **Q6 Readers in parallel.** How do 1, 2, 4 and 8 reader threads scale in each regime,
  and do they wait for each other when gets load? A load reads the stream while it holds
  a striped pointer lock (`NodeCollection.followPointer`) that other gets need too, and a
  sweep holds the write lock.
* **Q7 Size.** Heap bytes and disk bytes per key at each size.


## 2. The machines

| | F53 | s1 |
|---|---|---|
| What | MacBookPro18,3 | HostUp VPS XS, KVM (sk26 B056) |
| Processor | Apple M1 Pro, 8 performance and 2 efficiency cores | AMD EPYC Rome, 2 virtual CPUs; L2 512 KiB a CPU, L3 16 MiB |
| Memory | 32 GB | 3.8 GB, 3.2 GB available; a 1 GB swap file, swappiness 1 |
| Disk | 1 TB SSD, 666 GB free | 50 GB virtual disk (QEMU), 42 GB free |
| System | macOS 27.0.1 | Ubuntu 26.04 LTS, Linux 7.0, clock source kvm-clock |
| JDK | OpenJDK 27 (Homebrew) | none; OpenJDK 27 to be installed (section 6) |
| OS file cache | cannot be dropped (no passwordless sudo) | can be dropped, and limited per process with a cgroup (root) |

s1 was idle when looked at (read only, 2026-10-23 09:50): load 0.07, Docker installed but
no container running.


## 3. The measurements

### 3.1 Part A: 004-01 again, on s1 (Q1)

* IndirectionBench unchanged: 20,000 and 8 million keys; 1 and 2 threads, and 4 (more
  threads than CPUs, reported apart). Heap 2 GB instead of 4 (the 8-million-key tree is
  about 550 MB). F53 repeats it with 2 GB, so that the machines are compared with the same
  flags.
* IndexCensus as in 004-01 (1 million keys; int4, pre16, rnd16), 2 threads, heap 2.6 GB
  instead of 8 (its data, the in-memory stream included, are about 0.6 GB). F53 repeats it
  with the same settings.
* On s1 three times, at different times of day, since a VPS shares its host. The steal
  time (`/proc/stat`) is recorded for every run.

### 3.2 Part B: a handle's place after collections (Q2)

A copy of IndirectionBench with one option more: after the tree is built (each handle
right before its object), it is aged by the collector before the lookups: (a) G1 young
collections until the tree has been evacuated into old regions; (b) a full collection
(G1's full collection slides objects and keeps their order); (c) ZGC, generational, with
the same aging. Then `direct` and `handleacq` in the layouts `before` and `scattered`, 8
million keys, one thread, on both machines. The guess to check: G1's evacuation copies the
objects an array points to as it scans the array, so a node's handles end up together and
their objects elsewhere, which is 004-01's `parent` layout (11 percent dearer than
`before` out of cache).

F53 also runs the 004-01 matrix at 64 million keys (a tree of about 4.4 GB, one level
deeper and further out of the caches; heap 16 GB), one thread: does a hop cost the same at
that size as at 8 million?

### 3.3 Part C: the devices

Random reads of 4 and 16 KiB, at queue depths 1 and 8, past the OS cache (O_DIRECT on
Linux; JDK 27's `ExtendedOpenOption.DIRECT` also opens and reads on F53, tried; whether it
bypasses the cache there is checked by the tool's first run), in an 8 GB file next to the
databases: what each device gives, to read D's figures against. A small Java tool,
`DiskBaseline.java`; nothing to install.

### 3.4 Part D: BergDB at scale (Q3 to Q7)

**The tool.** `ScaleBench.java` in this item, against `bergdb.jar` as IndexCensus is
(package `bergdb.core`; nothing in `java/` changes). It loads and checks values as
`LargerThanMemory` does and uses `PerfUtil`'s histogram and GC log reader from
`java/stress`. Perf's read mode is not used: it assumes resident data and a history of
updates, and `java/stress` should not change for an item.

**The databases.** Keys of 24 bytes (Frans: "something longer than 8 bytes ... 24 bytes
could be used"; no test had a default for that; Perf's and the soak's long keys are 120
bytes). BergDB cuts a key into segments of 7 bytes (`Keys.toSegments`), so a 24-byte key
has four, and how the keys differ decides the index's shape: keys that differ before the
last segment get single-entry segment nodes of their own, one per later segment (004-01's
rnd16 got two per key). Two kinds:

* **key24**, the main series: `/scale/key/` and the key's number in 13 decimal digits.
  Keys differ only in the third and fourth segments, as with a common prefix and an id at
  the end; the index is as compact as with 4-byte keys (pilot: 53.9 bytes per key in the
  latest tree against 53.4 for int4).
* **rnd24**, on F53 at 1M and 10M keys: 16 bytes of a hash of the number, then the number.
  Keys differ in the first segment, as random ids, hashes or ids followed by more fields
  do, so each key gets three single-entry segment nodes (pilot: 3.08 index nodes and 437
  bytes per key in the latest tree): BergDB's long-key worst case, also the case where
  handles would cost the most (004-01, 5.4).

8-byte values (the key's number and its version, so that every value read is checked);
node size 30; loaded in random order, 1,000 puts a transaction; on disk (`FileStream`);
infinite retention, no updates; a startup distance of 10 MB, as in J8. One database per
size and machine, kept on disk for all its runs.

**The regimes.**

* **M**, in memory: no eviction (`noEvict`) and a heap that holds everything, so gets
  never load. M runs right after the load, in the loading JVM.
* **C**, in the OS cache: a budget B (`cacheSizeIndicator`) and a heap of 4B (J8 and P4
  used a quarter and a fifth); the stream's files read once before the run; the device
  counters must show that the run read nothing from the device.
* **D**, from the device: as C, but the OS cache cannot hold the stream. On s1, the caches
  are dropped before the run, and the JVM runs in a cgroup without swap
  (`systemd-run --scope -p MemoryMax=...`) whose limit leaves the OS cache about 100 MB
  beside a pretouched heap. On F53, only where the stream is much larger than the memory
  left over (100M keys, if the pilot shows that); otherwise F53 has no D runs.
* Budgets: R/4 and R/20, where R is the heap a size takes in M (measured by the pilot,
  extrapolated), not below 40 MB.

**The pilot** (F53, 2026-10-23, 1M keys loaded in M, not timed): heap after a full
collection (all history resident, the node table included), bytes on disk, and the load's
puts a second:

| Keys | Heap per key | Disk per key | Latest tree per key | Puts a second |
|---|---|---|---|---|
| key24 | 266 B | 282 B | 53.9 B, 12.3 keys a node | 235,000 |
| rnd24 | 874 B | 731 B | 437 B, 0.32 keys a node | 109,000 |
| int4 (for comparison) | 268 B | 227 B | 53.4 B, 12.5 keys a node | 275,000 |

So R is about 266 MB per million key24 keys: 100M keys would be 27 GB live, and M stops at
50M on F53 (13 GB live, a 20 GB heap; 30M with a 12 GB heap if the Mac's free memory is
short then). 100M keys take 28 GB on disk; 30M on s1 take 8.5 GB. A budget must stay well
above the pinned state, about 11 MB with a startup distance of 10 MB: in a trial at 0.1M
keys with a 4 MB budget every sweep was complete and ended above the budget. The heap is 4
times the budget, at least 512 MB.

**The runs** (budget in MB, heap in parentheses):

| Machine | M (no eviction) | C (OS cache) | D (device) |
|---|---|---|---|
| F53, key24 | 0.1M (512m), 1M (1g), 10M (6g), 50M (20g) | 1M: 66 (512m); 10M: 665 (2660m), 133 (600m); 100M: 1,330 (5300m), 2,660 (10600m) | — |
| F53, rnd24 | 1M (3g), 10M (14g) | 10M: 437 (1750m) | — |
| s1, key24 | 0.1M (512m), 1M (1g), 3M (2600m) | 1M: 66 (512m) | 1M: 66 (512m); 10M: 133 (600m), 600 (2400m); 30M: 200 (800m), 600 (2400m) |

At 100M, F53 uses R/20 and R/10 (R/4 would need a 27 GB heap), and its C runs are partly D
(the 28 GB stream does not fit the memory left over), as the device counters will show.
s1's heaps of at most 2.6 GB cap its budgets at 600 MB. The 10M, 30M and 100M databases
are loaded with a budget, since they do not fit in memory: 600 MB and a 2.5 GB heap on s1;
on F53 8,000 MB and a 20 GB heap (4,000 MB and 12 GB if less than 75 percent of the memory
is free), a budget that holds the latest index, as s1's 10M load with 600 MB took an hour
(changed 2026-10-23 14:40, before F53's runs; it was 2,660 MB and 11 GB). Repeated, for the spread between runs: on F53 C at
10M with 133 MB; on s1 C at 1M and D at 10M with 133 MB. The blocks are in
`plan-f53.sh` and `plan-s1.sh`.

**A run with gets**, in a fresh JVM on a kept database (M: in the loading JVM):

1. Warm-up: uniform gets until the loads a second are steady (C, D). The gets a second
   during the warm-up are kept: a cold start's curve.
2. Uniform gets from one thread: untimed windows for the throughput, then a timed pass of
   1 million gets or 60 s, with two `System.nanoTime()` calls a get (their own cost is
   measured and reported): mean, p50, p90, p99, p99.9, max, and the ten slowest gets with
   the collections and sweeps that overlapped them.
3. Hot gets, 90 percent on 1 percent of the keys (C, D): what a skewed load gets.
4. Gets from 1, 2, 4 and 8 threads (s1: 1, 2 and 4), 30 s each: gets a second and their
   latency; ten thread dumps during the 4-thread phase (s1: 2 threads), counting readers
   blocked on a pointer lock or on the write lock.
5. M only: IndexCensus's read-path variants (as it is; without the pointer lock and the
   stamp; without `readSync` too), one thread and the most threads: what the lock and the
   stamp cost at 10M and 50M keys.

**Recorded** for every phase: loads (`NodeCollection.loads()`); stream reads and their
bytes (a counting wrapper around the `FileStream`); the bytes the process read from the
device (`/proc/self/io` on s1, `proc_pid_rusage` on F53 with a copy of 005-14's
`procstat.c`); the device's read operations (s1, `/proc/diskstats`); sweeps (count, total
time, longest; `Eviction.stats()`); resident bytes; GC pauses and full collections (the GC
log); steal time (s1). For a load: puts a second, disk bytes per key, and in M the heap
per key after a full collection.

**Flags.** G1, `-Xms` equal to `-Xmx`, `-XX:+AlwaysPreTouch`, assertions off (these are
performance runs; every value is checked anyway), `gc*` and `safepoint` logged. One
commit of bergdb (HEAD when the tools are ready; now `faa4269`), built once in a scratch
clone; the same jar on both machines, with its commit and SHA-256 in every result.


## 4. Order and rules

1. The tools: ScaleBench, the aging option, DiskBaseline and the scripts, tried at 0.1M
   keys on F53 (not timed).
2. s1 set up (section 6). Part A starts there, about 2 hours unattended; work on F53 does
   not disturb s1.
3. The pilot: 1M keys on both machines, each regime once. It gives the disk and heap bytes
   per key, the load rates and the warm-up's length. The largest sizes and the budgets are
   then fixed and written here, before the runs.
4. Parts B and C on both machines.
5. Part D on s1.
6. Part D on F53, 100M last.
7. Results and conclusions in section 10, and the item's log.

* F53: a script waits for a quiet machine, as in 004-01: no other JVM or trace check, a
  1-minute load below 1.5 for 5 minutes, no other Claude session busy
  (`~/.claude/sessions`). Not between 02:00 and 05:00, as `night.sh` starts at 02:10. This
  session stays idle while a timed run is on.
  Changed 2026-10-23 at 14:10 and 14:40, as nothing could start from 10:58 to 14:30 while
  Frans worked and six other sessions were busy: a load below 2.0 (while Frans works it
  stays at 1.5 to 1.9 with little CPU in use); other sessions count only from 05:00 to
  22:00; a block starts only if its length (estimated generously) ends it before 02:00.
  Every run's start and end in `runs.txt` record the load and the sessions' states, so
  that a run beside busy sessions can be told apart; the repeats check the spread.
* s1: a run that swapped (`vmstat`) or lost more than 2 percent to steal is repeated, with
  a smaller heap if it swapped.
* A wrong value read stops the work: a correctness problem at scale comes before timing.
* No load starts unless its predicted size leaves 8 GB free on s1 and 100 GB on F53.


## 5. Time

The tools and the pilot: about half a day of my work. The runs: about 6 hours on each
machine, s1 unattended, F53 in two or three quiet blocks. The M run at 50M keys needs an
18 GB heap, so F53 should not be in other use then. Two to three days in all.


## 6. On s1

Everything goes in `/opt/bergdb-bench/`: OpenJDK 27 as a tarball from jdk.java.net, its
SHA-256 checked against the published one (Ubuntu 26.04's packages stop at JDK 25, and the
comparison needs F53's JDK, with compact object headers by default); `bergdb.jar` and the
tools; the databases; the outputs. Files are copied with scp over the existing root
login. No packages, no services, no lasting change to system settings: dropping the caches
and the cgroup scopes belong to single runs. Afterwards the databases are deleted; the JDK
and the tools (about 350 MB) stay for the prototypes of 004-01's recommendation, unless
Frans wants everything removed.

Done 2026-10-23 10:20: OpenJDK 27 GA, build 27+35 (F53's Homebrew JDK is version 27 too),
from jdk.java.net's archive, its SHA-256 checked; 386 MB in `/opt/bergdb-bench/jdk-27`.
The measured jar is bergdb `faa4269`, built in a scratch clone (`java/build.sh`), SHA-256
`5357202587f0bf4d6cd8a683c67acbf90530dd9f9c856e9d2c2589d031cb1dba`, the same file on
both machines.

Done 2026-10-24 08:40: the databases on s1 deleted (22 GB; 42 GB free again);
`/opt/bergdb-bench` keeps `jdk-27`, `bergdb.jar`, `classes/`, `item/` (the scripts and
sources) and `out/` (the raw outputs with the GC logs), 394 MB. F53's databases (125 GB) are
in the session's scratch directory, kept until Frans decides on reruns.


## 7. Predictions

Written before the runs, to be checked against them:

* M: each tenfold adds a level and a few cache misses; a get at 50M keys takes 1.2 to 2 µs
  on F53 (0.7 µs at 1M in 004-01).
* C: 10 to 30 µs a get, for its two loads (J10 under pressure: p50 10 µs).
* D on s1: about as many device reads a get as loads, so a get costs one or two device
  latencies, 0.1 to 1 ms depending on the virtual disk.
* Sweeps take about 2 s per GB of resident data. With F53's largest budget (R/4 at 100M,
  about 5 GB) a sweep takes about 10 s and is the maximum of every phase.
* With the pointer lock held during loads, 4 readers in C and D do well under 4 times the
  gets of one.
* After G1's evacuations, handles cost what 004-01's `parent` layout cost.


## 8. Not in this plan

* Writes at scale; J8 measured them at 20M keys. Load rates are recorded on the way.
* Updates and history: one 10M database with 10M uniform updates on F53, if time allows.
* Other value sizes: one C run at 10M keys with 100-byte values (J8's) on F53, if time
  allows.
* Transparent huge pages, a third machine, Linux on bare metal.
* Prototypes of handles or of a forest (004-01, section 8, steps 2 and 3): this subitem
  measures BergDB as it is.
* Any change to BergDB.


## 9. Decisions for Frans

1. s1: the JDK and up to about 30 GB of databases in `/opt/bergdb-bench/`, as in section
   6. Keep the JDK and the tools afterwards?
2. F53: when it can be left quiet for blocks of two or three hours, one of them with an
   18 GB heap.
3. The choices of 3.4: 8-byte values and load-only databases.

Frans's answers, 2026-10-23 10:18: (1) "Yes ok. JDK and tools can stay." (2) "You can
start the run now. I will do other things. Tell me if I need to stop some software or
something before the testing." (3) "Yes this is fine. I suppose value size is not
important for this testing. However, key size could be. Use something longer than 8 bytes
for this. Not sure if there is some default already for other tests. If not, 24 bytes
could be used." Hence key24 and rnd24 in 3.4, and F53's blocks wait for a quiet machine
(`quiet.sh`) while Frans works.


## 10. Results

Runs: s1 from 10:24 on 2026-10-23, F53 from 17:03 to 21:51 the same day, with every other
Claude session idle (the 1-minute load at the blocks' starts 1.4 to 2.2). Every value read
was checked, and every run ended `SCALEBENCH OK` but s1's 30M load, which was stopped
(10.5.5). The outputs are in [02-scale-tests/out/](02-scale-tests/out/) (`f53/`, `s1/`: the
summaries, the JSON results and `runs.txt` with the load and the sessions' states at each
run; the GC logs stayed on the machines); `summarize.py` makes the tables of 10.5 from the
JSON. Deviations from the plan: s1's 30M load was stopped after 9 hours at 18.46M keys, and
its from-the-device runs used the first 18.4M keys of the load order (10.5.7); F53 loaded 100M keys with an
8 GB budget in a 20 GB heap, only 2.5 times the budget, which matters for one result
(10.5.4).

### 10.1 Summary

1. **In memory, a get grows slowly with the database.** F53, 24-byte keys, median: 0.38 µs
   at 0.1M keys, 0.83 at 1M, 1.33 at 10M, 1.92 at 50M; s1 about twice that (0.76, 1.49 and
   2.06 µs at 0.1M, 1M and 3M). About half a microsecond per tenfold on F53.
2. **Once gets load, loads and the device set the cost, not pointers.** With the stream in
   the OS cache: 4 to 10 µs (1 to 2 loads, 3 to 6 stream reads). From F53's SSD (100M keys,
   114 GB on disk): 109 µs. From s1's virtual disk (0.45 ms a read): 0.37 to 0.88 ms, 1.1
   to 2.1 device reads a get, p99 2 to 7 ms, p99.9 13 to 27 ms (10M and 18.4M keys). A get from the device costs
   60 (F53) to 350 (s1) gets in memory. A handle adds 9 to 18 percent to a lookup in memory
   (parts A and B), 0.05 to 0.15 µs.
3. **The worst case is the sweep, and it grows faster than the budget.** Every run with
   eviction had its longest wait in a sweep, often with full collections around it: 0.5 to
   1.4 s at budgets of 66 and 133 MB, 2.7 s at 437 MB (rnd24), 6.0 s at 665 MB (10M keys),
   5.3 and 13.8 s at 1.33 and 2.66 GB (100M), 25 s during s1's 10M load (600 MB), and 266 s
   during F53's 100M load (8 GB in a 20 GB heap; G1 failed evacuations and ran two full
   collections of 13 and 16 s inside it).
4. **Writing when the index does not fit is slow, and the stream grows faster than the
   keys.** Bytes on disk per key after a random-order load: 71 at 0.1M keys, 282 at 1M, 754
   at 10M, 1,028 at 50M, 1,142 at 100M. With a budget below the latest index the load
   collapses on a slow disk: s1's 10M load took an hour, its 30M load reached 18.46M keys in
   9 hours, at under 100 puts a second at the end.
5. **Parallel readers: the locks in memory, the sweep in the OS cache, the device on disk.**
   In memory today's read path stops at about 2.1 million gets a second at 8 threads on F53,
   whatever the size (3.5 to 4.9 million without the pointer lock and the stamp; without
   `readSync` too, 14 million at 0.1M and 3.8 at 50M). In the OS cache, 4 readers do 1.4 to
   1.6 times the gets of one, 8 fewer than 4: 34 to 44 percent of the readers' samples wait
   for the write lock in `Eviction.afterLoad`, a sweep. From the device, readers overlap
   their reads (4 readers 4.3 to 6 times one), with 5 to 20 percent of the samples blocked
   on `FileStream`'s per-file monitor while they hold a pointer lock.
6. **Platform.** s1 is about twice as slow as F53 out of cache and 1.3 times in cache; the
   follow variants rank the same on both (part A).
7. **A handle's place is the collector's business, and G1 helps.** After one G1 evacuation
   of the whole tree, handles allocated in random order cost what handles allocated next to
   their objects cost (F53: 575 against 542 ns, direct pointers 496; s1: 1,317 against
   1,115, direct 993). ZGC keeps the scattered order (851 ns). At 64M keys a handle costs 13
   percent over a direct pointer, as at 8M.
8. **Memory.** Heap per key after a load, all history resident: 243 to 262 bytes with key24,
   852 to 871 with rnd24; the latest tree alone 54 and 437 bytes per key.
9. **Startup with a cold OS cache takes minutes on a slow disk.** On s1: 9 s at 1M keys,
   175 to 194 s at 10M, 287 to 303 s at 18.4M (warm: 1.5 s at 10M on F53). The time goes to
   reading one header per pointer of D to learn its id (`DbStarter.linkD`, about 590,000
   random reads at 10M).

### 10.2 Part A: s1 against F53 (Q1)

The same flags on both (heap 2 GB; the census 2.6 GB). One thread, ns a lookup (median of 5
rounds), and in parentheses the ratio to direct:

| Variant | 20,000 keys: F53 | s1 | 8M keys: F53 | s1 |
|---|---|---|---|---|
| direct | 63.9 | 81.4 | 509 | 1,005 |
| lockstamp (today) | 82.6 (1.29) | 126.6 (1.56) | 571 (1.12) | 1,061 (1.06) |
| handleacq, before | 71.3 (1.12) | 95.0 (1.17) | 553 (1.09) | 1,138 (1.13) |
| handleacq, parent | 72.0 (1.13) | 99.7 (1.22) | 621 (1.22) | 1,135 (1.13) |
| handleacq, scattered | 75.6 (1.18) | 116.7 (1.43) | 788 (1.55) | 1,813 (1.80) |
| hash | 84.5 (1.32) | 124.4 (1.53) | 948 (1.86) | 1,991 (1.98) |

F53's figures repeat 004-01's (heap 4 GB) within 1 to 5 percent, but for scattered at 8M (788 against 874 ns). s1 has two CPUs; at two
threads the monitor already collapses in cache: lockstamp 3.5 million lookups a second
against 22.6 direct (F53: 14.1 against 30.3). The census's gets after the load are 1.5 to
2.1 times F53's (int4 1,322 against 862 ns; F53's run at 2.6 GB gave 862 where 004-01's at
8 GB gave 709, unexplained; pre16 and rnd16 matched 004-01 within 7 percent). Steal time on
s1 stayed below 0.2 percent in every run. [Part A's second and third sessions on s1:
10.8.]

### 10.3 Part B: a handle's place after collections (Q2)

8M keys, one thread, ns a lookup:

| Treatment | F53: direct | before | parent | scattered | s1: direct | before | parent | scattered |
|---|---|---|---|---|---|---|---|---|
| g1 (as 004-01) | 508 | 566 | 635 | 834 | 1,063 | 1,231 | 1,182 | 2,065 |
| alloc (allocation order) | 509 | 557 | 641 | 821 | 1,073 | 1,156 | 1,315 | 2,087 |
| young (one G1 evacuation) | 496 | 542 | 583 | 575 | 993 | 1,115 | 1,176 | 1,317 |
| zgc | 544 | 607 | 671 | 851 | 1,193 | 1,221 | 1,287 | 2,116 |

In alloc and young no collection ran while the tree was built (0 in the outputs), and no
evacuation failed. G1 copies the objects an array points to as it scans the array, and then
those objects' fields: a handle is reached from its parent's array and its object from the
handle, so the two end up near each other in whatever order they were allocated. After the
evacuation, scattered costs what before costs (F53 +6 percent, s1 +18 percent), and every
layout is 9 to 18 percent over direct pointers on F53. BergDB's objects live through young
collections before they get old, so under G1 they get this order; ZGC relocates in address
order and keeps the allocation order.

The 004-01 matrix at 64M keys (F53, one thread, a tree of about 4.4 GB, depth 8): direct 797
ns, lockstamp 877, handle 903 (+13 percent), handleacq parent 990, child 1,018, scattered
1,280, hash 1,398, chm 1,588: the same ratios as at 8M (004-01: handle +13 percent,
scattered +69).

### 10.4 Part C: the devices

| | F53, SSD | s1, virtual disk |
|---|---|---|
| 4 KiB, 1 thread: reads a second; p50, p99, p99.9 | 11,841; 82 µs, 103 µs, 143 µs | 1,850; 450 µs, 2.3 ms, 14 ms |
| 4 KiB, 8 threads: reads a second | 95,124 | 14,247 |
| 16 KiB, 1 thread: p50 | 97 µs | 494 µs |
| 4 KiB through the OS cache: p50 | 0.8 µs | 0.7 µs |

s1's disk behaves like network storage: half a millisecond a read, and a long tail.

### 10.5 Part D: BergDB at scale

#### 10.5.1 In memory (M)

24-byte keys (key24, and rnd24 where marked), one thread: the untimed throughput, then the
timed pass's latency in µs; and the gets a second of more threads:

| Machine, keys | Gets a second | p50 | p99 | p99.9 | Max | Hot p50 | 2 threads | 4 threads | 8 threads |
|---|---|---|---|---|---|---|---|---|---|
| F53, 0.1M | 2.55 M | 0.38 | 0.50 | 0.6 | 27 | 0.29 | 3.18 M | 5.10 M | 2.37 M |
| F53, 1M | 1.14 M | 0.83 | 1.25 | 4.9 | 41 | 0.34 | 1.85 M | 3.05 M | 2.06 M |
| F53, 10M | 715 k | 1.33 | 1.88 | 2.9 | 26 | 0.54 | 1.22 M | 2.03 M | 2.20 M |
| F53, 50M | 511 k | 1.92 | 3.76 | 7.5 | 46 | 1.00 | 904 k | 1.56 M | 2.03 M |
| F53, rnd24 1M | 925 k | 1.05 | 1.42 | 1.7 | 31 | 0.75 | 1.58 M | 2.47 M | 2.60 M |
| F53, rnd24 10M | 575 k | 1.71 | 2.51 | 5.7 | 30 | 1.67 | 1.01 M | 1.72 M | 2.27 M |
| s1, 0.1M | 1.10 M | 0.76 | 1.42 | 11.6 | 73 | 0.34 | 835 k | 853 k | — |
| s1, 1M | 629 k | 1.49 | 2.80 | 14.9 | 193 | 0.53 | 655 k | 703 k | — |
| s1, 3M | 470 k | 2.06 | 3.62 | 16.4 | 71 | 0.87 | 537 k | 608 k | — |

s1's 4 threads are more than its two CPUs. The read-path variants (3.4, step 5), one thread:
the pointer lock and the stamp cost 51 ns a get at 0.1M (13 percent), 65 at 1M, 62 at 10M,
77 at 50M (4 percent). At 8 threads, million gets a second as it is, without the lock and the
stamp, and without `readSync` too: 2.40, 4.87, 14.0 at 0.1M; 2.07, 3.68, 8.12 at 1M; 2.22,
3.70, 5.20 at 10M; 2.07, 3.52, 3.81 at 50M. Today's read path stops at about 2 million gets a
second at any size; at 50M the memory limits the others too.

#### 10.5.2 From the OS cache (C) and from the device (D)

One thread unless marked; latency in µs unless marked:

| Machine, keys, budget | Regime | Gets a second | p50 | p99 | p99.9 | Max | Loads a get | Device a get | 4 threads | 8 threads |
|---|---|---|---|---|---|---|---|---|---|---|
| F53, 1M, 66 MB | C | 165 k | 4.25 | 10.0 | 12.7 | 372 ms | 0.96 | 0 | 255 k | 168 k |
| F53, 10M, 665 MB | C | 160 k | 4.96 | 10.9 | 13.6 | 204 ms | 1.00 | 0 | 197 k | 152 k |
| F53, 10M, 133 MB | C | 57 k | 10.4 | 17.9 | 22.1 | 355 ms | 2.04 | 0 | 81 k | 66 k |
| the same, repeated | C | 58 k | 10.3 | 17.9 | 22.1 | 377 ms | 2.04 | 0 | 81 k | 67 k |
| F53, rnd24 10M, 437 MB | C | 28 k | 20.0 | 26.1 | 30.6 | 2.09 s | 4.50 | 0 | 38 k | 29 k |
| F53, 100M, 1.33 GB | (C) D | 10.7 k | 109 | 295 | 397 | 5.25 s | 2.04 | 10.5 KB | 44 k | 34 k |
| F53, 100M, 2.66 GB | (C) D | 10.6 k | 110 | 281 | 397 | 2.4 ms | 1.70 | 11.3 KB | 50 k | 77 k |
| s1, 1M, 66 MB | C | 96 k | 4.45 | 16.5 | 40.4 | 941 ms | 0.96 | 0 | 114 k | — |
| s1, 1M, 66 MB | D | 98 k | 4.77 | 15.5 | 40.4 | 1.13 s | 0.95 | 0 reads | 110 k | — |
| s1, 10M, 133 MB | D | 1,005 | 721 | 5,177 | 22,544 | 1.40 s | 2.05 | 1.85 reads | 3,982 | — |
| s1, 10M, 600 MB | D | 1,907 | 371 | 2,179 | 13,107 | 159 ms | 1.22 | 1.14 reads | 12,194 | — |
| s1, 18.4M, 200 MB | D | 966 | 877 | 5,702 | 20,840 | 1.76 s | 2.23 | 2.14 reads | 3,311 | — |
| s1, 18.4M, 600 MB | D | 1,233 | 672 | 3,408 | 16,712 | 55 ms | 1.64 | 1.63 reads | 5,862 | — |
| s1, 1M, 66 MB, repeated | C | 102 k | 4.32 | 16.1 | 28.9 | 988 ms | 0.96 | 0 | 105 k | — |
| s1, 10M, 133 MB, repeated | D | 1,265 | 741 | 6,717 | 27,263 | 1.51 s | 2.04 | 1.85 reads | 3,617 | — |

* "Device a get": s1 counts the device's reads (`/proc/diskstats`), F53 only the bytes the
  process read (`proc_pid_rusage`). At 1M keys s1's D run read nothing from the device: the
  latest versions the gets need fit the 100 MB or so that the cgroup leaves the OS cache. On
  F53 at 100M the 114 GB stream does not fit the memory left over, and the gets read 10 to
  11 KB each from the SSD: C in name, D in fact.
* A load costs three stream reads (6.1 for 2.04 loads, in every run); J10 described two,
  the node's header for its id and then the node.
* Hot gets (90 percent on 1 percent of the keys) stay mostly in memory: F53 10M with 133 MB,
  p50 0.71 µs and 248,000 gets a second; s1 10M with 600 MB, p50 2.6 µs, p99 0.86 ms,
  12,000 a second.
* A cold start (the warm-up after opening the database) took until the gets a second were
  steady: 236 s on F53 at 100M with 2.66 GB (from 6,250 to 10,600 a second), 516 s on s1 at
  10M with 600 MB (from 897 to 1,821).
* The repeats: F53's C run at 10M agreed within 2 percent; s1's C run at 1M within 7
  percent; s1's D run at 10M had the same latency (p50 741 against 721 µs) but 26 percent
  more gets in the untimed windows (1,265 against 1,005): a shared virtual disk varies.

#### 10.5.3 Where readers wait

The sampled states of 4 readers (s1: 2), in percent of the samples. In memory, all RUNNABLE
in the search (`Dag.getEqNodeInSegment`, `KeyNode.searchEq` and others). In the OS cache
(F53 1M and 10M, s1 1M): 34 to 44 percent BLOCKED in `Eviction.afterLoad` on the write lock
(waiting for a sweep), 23 to 33 percent reading the stream while holding a pointer lock, 5
to 9 percent sweeping. From the device, s1 at 10M: 84 to 86 percent reading the stream while
holding a pointer lock, 5 to 9 percent blocked on `FileStream$DbFile` (FileStream's
per-file monitor: one file's reads are serialized), 2 to 6 percent blocked on a pointer
lock; F53 at 100M: 41 to 56 percent reading, 18 to 20 percent blocked on the file's monitor,
11 to 18 percent on a pointer lock, up to 18 percent on the write lock.

#### 10.5.4 The tails: sweeps and collections

The capacity controller's sweeps over a whole run, and G1's full collections in its log:

| Run | Budget | Heap | Sweeps | Longest sweep | Full collections |
|---|---|---|---|---|---|
| F53, 1M, C | 66 MB | 512 MB | 193 | 0.50 s | 8 |
| F53, 10M, C | 133 MB | 600 MB | 298 | 0.60 s | 49 |
| F53, 10M, C | 665 MB | 2.66 GB | 16 | 6.0 s | 12 |
| F53, rnd24 10M, C | 437 MB | 1.75 GB | 57 | 2.7 s | 7 |
| F53, 100M | 1.33 GB | 5.3 GB | 8 | 5.3 s | 1 |
| F53, 100M | 2.66 GB | 10.6 GB | 2 | 13.8 s | 0 |
| F53, 100M load | 8 GB | 20 GB | 9 | 266 s | 2 (and 2 by the tool) |
| s1, 1M, C | 66 MB | 512 MB | 87 | 1.4 s | 1 |
| s1, 10M, D | 133 MB | 600 MB | 8 | 1.4 s | 0 |
| s1, 10M load | 600 MB | 2.5 GB | 14 | 25 s | 2 (by the tool) |

The longest sweep does not follow the budget (0.5 s at 66 MB, 6 s at 665 MB, 13.8 s at 2.66
GB), and the longest coincide with collections: during the 100M load's sweep of 266 s, G1
failed two evacuations and ran full collections of 12.7 and 16.3 s in a heap only 2.5 times
the budget. In the timed passes of F53's 10M runs with 133 MB, all ten slowest gets
overlapped a reader's wait after a load (`Eviction.afterLoad`). In memory, the timed passes'
maxima were 26 to 46 µs on F53 and 71 to 193 µs on s1.

#### 10.5.5 Loads (writes)

| Machine, keys, budget | Heap | Time | Puts a second | Disk per key |
|---|---|---|---|---|
| F53, 0.1M, none | 512 MB | 0.4 s | 254 k | 71 B |
| F53, 1M, none | 1 GB | 4.2 s | 236 k | 282 B |
| F53, 10M, none | 6 GB | 98 s | 102 k | 754 B |
| F53, 50M, none | 20 GB | 720 s | 69 k | 1,028 B |
| F53, 100M, 8 GB | 20 GB | 5,115 s | 19.6 k (134 k at first, 20 k at the end) | 1,142 B |
| F53, rnd24 10M, none | 14 GB | 155 s | 65 k | 1,057 B |
| s1, 1M, none | 1 GB | 23 s | 44 k | 282 B |
| s1, 3M, none | 2.6 GB | 36 s | 83 k | 486 B |
| s1, 10M, 600 MB | 2.5 GB | 3,616 s | 2.8 k | 754 B |
| s1, 30M, 600 MB | 2.5 GB | stopped at 18.46M keys after 32,550 s | 567 (84 k over the first 2.5M keys, 7.6 k at 9.8M, under 100 at the end) | 850 B |

The disk bytes per key grow with the database, also without eviction. The likely reason: D,
bounded by the startup distance (10 MB), holds a smaller share of the leaves as the index
grows, so with 1,000 random puts a transaction nearly every put dirties a leaf that is then
written again before another put reaches it; at 50M and more, about one leaf written a put.
With a budget below the latest index, a put must also load its leaf: on s1's disk that is a
millisecond or more a put, growing with the index. s1's 30M load was stopped at 21:53, as it
would have needed another day or more.

#### 10.5.6 Memory

Heap per key after a load, everything resident with its history (the heap after a full
collection less the heap before the load): key24 262 bytes at 1M, 253 at 3M (s1), 243 at
10M, 245 at 50M; rnd24 871 at 1M and 852 at 10M. The latest tree: 54 bytes per key and 12.3
keys a node with key24; 437 bytes and 0.32 keys a node with rnd24, whose keys each get three
single-entry segment nodes. rnd24's gets are 25 to 30 percent slower in memory, and with the
OS cache they need 4.5 loads a get instead of 2.

#### 10.5.7 From the device at 18.4M keys on s1

The stopped 30M load (18.46M keys written; the first 18.4M of the load order read, 10.5.5):
with 200 MB, p50 877 µs, p99 5.7 ms, p99.9 21 ms, 2.14 device reads a get, 966 gets a
second, 3,311 with 4 threads; with 600 MB, p50 672 µs, 1.63 device reads, 1,233 and 5,862
gets a second. Against 10M (table of 10.5.2): about 0.2 to 0.3 more device reads a get and
20 to 80 percent more latency at the median for 1.8 times the keys. The longest wait was a
sweep again, also with 600 MB: 7.2 s, in the 4-thread phase.

#### 10.5.8 Startup with a cold OS cache

Opening a database after the OS cache was dropped (the D runs on s1) took 9 s at 1M keys,
175 to 194 s at 10M and 287 to 303 s at 18.4M; with the cache warm, 0.6 s at 1M and 1.5 s at
10M on F53 (and 15 to 17 s at 100M, partly from the SSD). Two stack samples and
`/proc/<pid>/io` of a further startup at 10M on s1 (2026-10-23 23:20, `out/s1/startup/`)
show where the time goes: `DbStarter.linkD` (rule 4) calls `NodeCollection.idOf` for the
pointers of D's nodes, and each call reads the target's header from the stream to learn its
id: about 590,000 reads and 1.9 GB from the device. D is bounded by the startup distance
(10 MB here), so the startup is bounded, but by a number of random reads, about one per
pointer of D: minutes on a disk with half a millisecond a read. J8 noted the header read
as a cost of loads; it is also the startup's.

### 10.6 The predictions (section 7)

* M at 50M on F53, 1.2 to 2 µs a get: 1.92 µs. Right.
* C, 10 to 30 µs: 4 to 10 µs with key24, 20 µs with rnd24. Lower than predicted.
* D on s1, one or two device latencies, 0.1 to 1 ms: 1.1 to 1.9 device reads and 0.37 to
  0.72 ms. Right.
* Sweeps about 2 s per GB, about 10 s at 5 GB: worse, and not in proportion: 6 s at 665 MB,
  13.8 s at 2.66 GB, 266 s at 8 GB in a heap 2.5 times the budget.
* 4 readers well under 4 times one in C and D: right in C (1.4 to 1.6 times); from the
  device they overlap their reads (4.3 to 6 times).
* After G1's evacuations, handles cost what the parent layout cost: they cost what the
  before layout cost, scattered or not. Better than predicted.

### 10.7 What it says

For the question behind this subitem, what matters as the database grows:

1. Up to the memory's size, the get in memory is not the problem: it grows by about half a
   microsecond per tenfold on F53, and a handle would add about a tenth to it.
2. Beyond the memory, gets are bounded by their loads: how many a get needs (2 with key24,
   4.5 with rnd24; three stream reads each), the device (0.08 ms on F53's SSD, 0.45 ms on
   s1's disk), and how many can run at once (the pointer lock held during a read,
   FileStream's per-file monitor). A larger budget cuts the loads: s1 at 10M, from 1.85 to
   1.14 device reads and from 0.72 to 0.37 ms.
3. What does not "always work" today, in order of harm: (a) the sweep, a stall of half a
   second to minutes that grows faster than the budget, during which readers and the writer
   wait, with G1's full collections around it (P4's second finding); (b) writes into an
   index larger than the budget, which on a slow disk slow to a few puts a second; (c) the
   stream's growth, about 1.1 KB per 32-byte key at 100M keys loaded in random order; (d)
   the startup after a restart with a cold OS cache, minutes on a slow disk (one header read
   per pointer of D); (e) parallel reads from the OS cache, which the sweep's write lock
   serializes.
4. For 004: the reason to change eviction is the tail, not the speed of a hop. The hop's
   cost (9 to 18 percent of a lookup in memory, a percent or two of a get that loads from
   the OS cache, nothing beside a device read) is small beside the rest, and under G1 a
   handle's placement takes care of itself (part B). Any local eviction without a walk
   (004-01's options C and D) attacks (a); (b) to (e) need their own work: fewer loads a
   get and fewer header reads at startup (keeping the id with the pointer, as J8 suggested;
   004-01's notes on long keys), reads that do not hold a pointer lock, a FileStream that
   reads in parallel. 004-01's first recommendation, the pointer lock and the stamp off the
   read path and no `readSync` monitor a get, is confirmed: it is the ceiling in memory,
   about 2 million gets a second at any size, and the pointer lock also holds reads from
   the device.

### 10.8 Part A again on s1

The second session (2026-10-23, 21:53 to 22:25) against the first (10:24 to 10:56), one
thread: in cache, every variant within 6 percent; at 8M keys most within 4 percent, four
variants 9 to 12 percent apart (handle +11.6, stamp +10.8, handleacq child −10.7,
handleclock −9.3). Differences under about 10 percent out of cache are not significant on
s1. The census: int4 1,276 ns a get (first session 1,322), pre16 1,538 (1,554), rnd16
1,866 (1,978). Steal time below 0.2 percent.

The third session (2026-10-24, 08:00 to 08:35), and the spread of all three (the largest
over the smallest), one thread: in cache a median of 5 percent and at most 9.5; at 8M keys a
median of 10 percent and at most 14 (lockstamp 1,061, 1,100 and 1,209 ns). With threads, the
variants without a monitor (direct, handleacq, hash) stayed within 5 percent in cache and 20
out of cache; those with a monitor swung by a factor of up to 3 at 4 threads on the two CPUs
(lockstamp in cache 3.5, 10.3 and 9.7 million lookups a second; direct 24.0 to 24.4), but
stayed far below the others in every session. The census's gets: int4 1,322, 1,276 and
1,364 ns; pre16 1,554, 1,538 and 1,333; rnd16 1,978, 1,866 and 1,876. So on s1 a single
session's one-thread figures out of cache are good to about 15 percent, and its
multi-threaded figures with monitors only as an order of magnitude.
