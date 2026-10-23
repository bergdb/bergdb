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

Status: **running since 2026-10-23.** Frans approved the plan the same day with three
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
  ([level4-performance.md](../../docs/level4-performance.md)).
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
are loaded with a budget (600 MB and a 2.5 GB heap on s1; 2,660 MB and an 11 GB heap on
F53), since they do not fit in memory. Repeated, for the spread between runs: on F53 C at
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
commit of bergdb (HEAD when the tools are ready; now `f206e58`), built once in a scratch
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
The measured jar is bergdb `f206e58`, built in a scratch clone (`java/build.sh`), SHA-256
`5357202587f0bf4d6cd8a683c67acbf90530dd9f9c856e9d2c2589d031cb1dba`, the same file on
both machines.


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

To come.
