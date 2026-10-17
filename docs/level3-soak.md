# BergDB Level 3: the soak

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-16 and 17.
Task 2 of [level3-plan.md](level3-plan.md), as WP P2 of bergdb item 001
([../items/001-lean-model-levels-3-4/01-plan.md](../items/001-lean-model-levels-3-4/01-plan.md)).

## Result

Both runs passed (`SOAK OK`).

* **The main run** (section 3): the plan's pilot scale, one million keys,
  1,000-byte values and a retention of five minutes, at 200 transactions a
  second, two measured hours with 19 physical cuts and three cold restarts:
  105 million reads checked at their snapshots (67.4 million gets, 37.7
  million scans of 1.9 billion KVs); after each restart and at the end,
  every key at the latest time and 21,000 keys at six earlier times. No
  wrong result; 2.7 million reads expired at admission, none during its
  execution.
* **The companion** (section 8): 20,000 keys, a retention of one minute,
  20 steady minutes with 12 physical cuts and three restarts; after each
  restart and at the end, every key at the latest time and at 11 times in
  the retained window (244,600 gets each time), exhaustively. No wrong result.

What it shows. Reclaim bounds the stream: on disk 3.6 to 6.7 GB in 8 to 20
files while 28.8 GB were appended, each iteration followed by one cut at the
retention. Commits take 0.26 ms at the median and 0.59 ms at p99; the tail
(up to 208 ms) is G1's young collections, and the commits that delete files
take 59 to 111 ms. Reads take microseconds. The longest pauses (3.3 s, and
two Remark pauses of 1.6 s) follow restarts and are mostly system time.
Level 3's memory grows by 2.6 to 2.9 MB a second (1.3 to 1.5 KB per update)
between restarts and nothing gives it back: at this rate the 24 GB heap
would have run out after about two hours without the restarts. That is what
Level 4's eviction is to bound.


## 1. What runs

`java/stress/Soak.java`, run by `java/stress/soak.sh NAME [PROP=VALUE ...]`
(both new in P2). One JVM, the database on a `FileStream` in a disposable
directory (a marker file, as `Perf`), the system clock, and a retention in
wall-clock seconds: reclaim cuts the stream and deletes whole files as time
goes by.

* **The workload.** n keys that are 4-byte ints and 1,000 long keys of 120
  bytes ("/soak/long/" and 9 digits and a filler), 1,000-byte values. One
  writer (the main thread), paced at a fixed rate of transactions of 10
  distinct keys: a hot set of 1,000 keys (half of them long keys) gets 30
  percent of the picks, the rest are uniform; 5 percent of the keys that are
  present are deleted, the others get their next version (a deleted key is
  put again). One commit a second is also synced (`sync(ORDINARY)`): the
  durable commits. Three readers, paced at 5,000 operations a second each:
  gets at the latest time (35 percent), at a time in the retention window
  (25), and within a second of the first available lookup time (5), so that
  some expire; forward and backward scans of 50 keys at the latest time (20)
  and at a time in the window (15).
* **The model and the checks.** A bounded model of every key's versions and
  deletes with their transaction times, pruned to what a lookup at or after a
  "keep" time can see: the older of the first available lookup time less 2
  seconds and the latest time less the retention and a minute, and never
  newer than a lookup time a reader has announced. Every successful
  operation is checked at its actual snapshot (`GetData.actualLookupTime`,
  `GetMany.actualLookupTime`): a get's value, a scan's keys in order, each
  with its value, none skipped. An operation that throws
  `LookupTimeNotAvailableException` counts as expired at admission, or during
  if a cut overtook it (a `ReadBelowFirstPosException` as the cause), and is
  allowed only if its lookup time is before the first available lookup time;
  anything else fails the run. A latest read that sees a transaction before
  the model has it waits for the model, as `ReclaimReaders` does.
* **Phases.** The load (every key once, 100 keys a transaction); the
  warm-up (the workload, at least 300 s and until the first physical cut);
  the measured phase (7,200 s of steady running, the restarts and their
  checks not counted, with three cold restarts at 30, 60 and 90 minutes;
  extended by up to an hour if it has fewer than 10 physical cuts); the end
  check.
* **A restart.** The readers pause; the database is synced (`STRONG`) and
  closed, opened again from its directory and started: a cold node cache,
  the OS file cache warm. Then the check: every key at the latest time, and
  the hot keys and 20,000 others at six times from the first available
  lookup time to the latest. With at most 20,000 keys (the companion case),
  every key at every such time.
* **What it records** (`result.json`): latency histograms (`PerfUtil.Hist`)
  of append commits, also split by whether reclaim stepped in the commit, of
  durable commits, of the pacing delay, of gets and scans; the slowest
  commits with their times; reclaim's iterations and cut decisions
  (`Reclaim.Stats`) and the physical cuts (moves of `FileStream`'s first
  position) with their times; samples every second of the heap, the GC
  counts, the stream, the first available position, the files and bytes on
  disk, the resident set size (every 10 s) and the dirty nodes (every 60 s);
  the restarts and checks; commits per second. `Soak finish` adds the GC
  log's pauses and safepoints for each phase and the pauses that overlap the
  slowest commits.
* **The JVM**: G1, a fixed heap (`-Xms` = `-Xmx`, not pretouched), assertions
  off, the GC and safepoint log of `performance.sh`
  (`-Xlog:gc*,safepoint:file=...:uptime,level,tags`). `soak.sh` runs from a
  copy of the build in the run directory, so `build.sh` cannot change it, and
  records the commit, the changed files, the jar's SHA-256, the JVM, the
  flags and the machine.

The machine: MacBookPro18,3, Apple M1 Pro, 10 cores, 32 GB, macOS 27.0.1,
APFS on the internal SSD, on AC power; OpenJDK 27 (Homebrew build 27). Source:
bergdb `309243b` (production code as at `a66e4d9`), with `Soak.java` and
`soak.sh` uncommitted; jar SHA-256 `939d3f755a9c916e...` for the main run.


## 2. The pilot, and the scale

The plan's pilot: one million keys, 1,000-byte values, a retention of five
minutes, one writer, two to four readers (`soak.sh pilot2`, 22:43 to 23:11;
300 transactions a second, `-Xms12g -Xmx12g`, warm-up until the first
physical cut, 900 measured seconds, one restart). It passed (`SOAK OK`):
269,179 commits at 299.1 a second, 0.90 updates per key per retention
window; 8,370,238 gets and 4,689,717 scans (234 million KVs) checked at
their snapshots, no failure; 335,470 reads expired at admission, none during;
one restart (started in 0.95 s, 5,678 transactions rerun from the 50 MB
section; its check, 1,127,000 gets, 13.1 s).

What it showed, for the main run:

1. **Memory grows with the updates, and nothing gives it back.** The heap
   after the young collections rose by about 4 MB a second, about 1.3 KB per
   update, cuts or not. Level 3 keeps every node it has made or read:
   `Cache3`'s entries are never removed (`pointerDestroyed` has no caller;
   [level4-alignment.md](level4-alignment.md), M25 and M26). A restart starts
   from a new database object that loads lazily (about 4.4 GB after its check
   had read every key), and the old one becomes garbage. In the 12 GB heap
   the restart's check, with the old database not yet collected and the new
   one loading, ended in a full collection of 2.6 s, the pilot's longest
   pause. So the scale fits the machine only for a while: the memory between
   restarts, not the data, sets the heap.
2. **Reclaim's rhythm.** The first iteration rewrote the loaded data in about
   470 s; the later ones took 240 to 270 s, each followed by one physical cut.
   A cut is decided as soon as the iteration's tEnd is the retention old
   (the age of the new first available time at the decision was 300.0 s
   every time), and the iteration after the first cut has its cut point
   there, so the first available lookup time was 300 to 750 s old.
3. **The slowest commits are the physical cuts.** The two slowest (136 and
   39 ms) were the commits whose reclaim call deleted files
   (`FileStream.pretruncate`, which forces the directory after each file it
   deletes). Durable commits took 70 to 148 ms, the buffer's flush interval
   (`StorageManager.DEFAULT_BUFFER_TIME`, 100 ms): a sync waits for the next
   flush.

The main run keeps the plan's scale and workload and lowers the rate to 200
transactions a second (about 0.6 updates per key per retention window), with
`-Xms24g -Xmx24g` (the item plan's limit, its 2.4): about 2.7 MB a second of
memory growth between restarts, and room for a restart's transient.


## 3. The main run

`soak.sh main1` (23:12:41 to 01:30:02; source, flags and the jar's hash in
its `source.txt`): `SOAK OK`, exit 0.

| | |
|---|---|
| Load | 1,001,000 keys in 11.9 s (84,300 puts a second), a stream of 1,287 MB |
| Warm-up | 972 s, until the first physical cut (the first iteration took 671 s) |
| Measured | 7,200 steady seconds (7,255 s of wall time, the restarts' pauses and checks not counted) |
| Commits | 1,438,664 (199.8 a second, paced at 200), 13,701,372 puts and 685,268 deletes: 0.60 updates per key per retention window |
| Reads checked | 67,378,447 gets and 37,733,061 scans (1,883,977,271 KVs), 14,599 reads a second |
| Expired | 2,696,284 reads at admission (2.5 percent: the gets within a second of the first available time, and the historical reads that fell below it), none during |
| Wrong results | none; no unverifiable read |
| Physical cuts | 19 in the measured phase (20 with the warm-up's), each one cut decision |
| Restarts | three, cold, at 1,800, 3,619 and 5,438 measured seconds, each followed by its check |

Reclaim ran 26 iterations (four segments, one per database object: a restart
starts a new one). In steady state an iteration took 320 to 480 s and touched
the 950,000 keys present, rewriting 140,000 to 600,000 live values stored
before its cut point (the first iteration of the loaded data: 604,375); each
iteration was followed by one physical cut, decided when its end time was the
retention old (every decision at an age of 300.0 s of the new first available
time, one at 311.7 s after a restart). So the first available lookup time
moved in a saw-tooth between 303 and 1,069 s old, and the stream kept on disk
between 3.6 and 6.7 GB in 8 to 20 files while 28.8 GB were appended in the
measured phase (2.09 bytes appended per byte the transactions wrote: the
rewrites of values and the records of each iteration).


## 4. Latency and throughput

All latencies are of the measured phase, from `PerfUtil.Hist` (exact to
about 3 percent).

| Operation | Count | p50 | p95 | p99 | p99.9 | Max |
|---|---|---|---|---|---|---|
| Append commit | 1,438,664 | 0.26 ms | 0.40 ms | 0.59 ms | 2.2 ms | 208 ms |
| ... with a reclaim step | 1,403,611 | 0.26 ms | 0.40 ms | 0.59 ms | 2.2 ms | 208 ms |
| ... without | 35,053 | 0.15 ms | 0.23 ms | 0.31 ms | 0.57 ms | 3.7 ms |
| Durable commit (`ORDINARY`) | 7,194 | 67 ms | 124 ms | 137 ms | 148 ms | 171 ms |
| Get, latest | 37,729,195 | 1.9 µs | 4.0 µs | 7.2 µs | 84 µs | 197 ms |
| Get, historical | 29,649,252 | 2.3 µs | 5.2 µs | 20 µs | 189 µs | 201 ms |
| Scan forward, 50 keys | 18,327,823 | 17 µs | 81 µs | 147 µs | 1.1 ms | 621 ms |
| Scan backward, 50 keys | 19,405,238 | 17 µs | 82 µs | 155 µs | 1.2 ms | 3.3 s |

Throughput held: 199.8 commits a second against the pace of 200. Outside the
restarts, 26 of the 7,200 seconds had fewer than 195 commits, and three
episodes had seconds with none: the three longest GC pauses (section 5). The
pacing delay (how late a commit started against its schedule) was 0.17 ms at
the median and 82 ms at p99: the writer catches up after each durable
commit. A durable commit waits for the buffer's next flush
(`StorageManager.DEFAULT_BUFFER_TIME`, 100 ms), as in the pilot.

The 20 slowest append commits took 59 to 208 ms. Fourteen of them overlap a
GC pause of about their length (`Soak finish` matches the GC log); the other
six are commits whose reclaim call made a physical cut (59 to 111 ms;
`FileStream.pretruncate` deletes whole files and forces the directory after
each). So in this run the young collections, not the cuts, set the tail of
the commit latency; in the pilot, with half the heap, the cuts were the two
slowest commits (136 and 39 ms).


## 5. The worst pauses

From the GC log (`-Xlog:gc*,safepoint`), the measured phase: 143 pauses, 25.3 s
in all (0.35 percent of its wall time), 121 ms at the median, 1.65 s at p99,
no full collection; safepoints are the pauses (the same 143, within 0.1 ms).

| Uptime | Pause | Length | Heap | Note |
|---|---|---|---|---|
| 6,477.6 s | Young (Prepare Mixed) | 3,305 ms | 17,871 → 12,512 MB | 55 s after restart 3; User 1.9 s, Sys 8.4 s |
| 2,838.1 s | Remark | 1,646 ms | 11,591 MB | 54 s after restart 1; User 4.8 s, Sys 6.2 s |
| 4,752.5 s | Remark | 1,645 ms | 11,500 MB | 149 s after restart 2; User 4.1 s, Sys 5.4 s |
| 6,481.6 s | Young (Mixed) | 620 ms | 12,768 → 12,240 MB | after the 3.3 s pause |
| 2,797.2 s | Young (Normal) | 525 ms | 11,771 → 10,081 MB | during restart 1's check; Sys 2.4 s |

The long pauses all follow a restart, when the old database object is
garbage and the new one fills up as the checks and readers load it. Their
time is mostly system time (8.4 s of system time in a 3.3 s pause with nine
workers; the two Remark pauses, of the same length to the millisecond, 6.2
and 5.4 s), not collection work: the operating system's handling of the
heap's memory, I think, page faults on regions used for the first time since
the heap is reserved but not pretouched (`-Xms` = `-Xmx` without
`-XX:+AlwaysPreTouch`, the flags of `performance.sh`). A pretouched run would
tell; P4 should use one. During the restarts' checks the pauses were
at most 525 ms (restart 1), 470 ms (restart 2) and 61 ms (restart 3). In the
pilot's 12 GB heap the longest was a full collection of 2.6 s during a
restart's check; the 24 GB heap avoided full collections.


## 6. Memory and storage

The heap after collections, sampled every second, between restarts:

| Segment | Heap after GC, start → end | Growth (fitted) | Resident set, max |
|---|---|---|---|
| 1 (983 to 2,784 s) | 4,145 → 9,458 MB | 2.92 MB/s | 8.3 GB |
| 2 (2,804 to 4,604 s) | 10,890 → 9,181 MB | (−0.38 MB/s, see below) | 13.5 GB |
| 3 (4,623 to 6,423 s) | 10,687 → 16,291 MB | 2.65 MB/s | 12.0 GB |
| 4 (6,439 to 8,239 s) | 11,778 → 16,425 MB | 2.56 MB/s | 11.8 GB |

So Level 3 keeps about 2.6 to 2.9 MB a second at 2,000 updates a second,
1.3 to 1.5 KB per update, as the pilot found: `Cache3` keeps every node the
database has made or read. A segment starts above the end of the one before
because the old database object is still counted until a concurrent cycle
and mixed collections free it (segment 2 shows this: it starts with
restart 1's garbage, 10.9 GB, and ends below it). Peak: 16.4 GB after a
collection, 20.9 GB used, against the 24 GB heap; the means of the first and
last tenths of the measured phase, 5.1 and 14.7 GB. Without restarts the
heap would have run out after about two hours at this rate: the restarts,
not the data (4 to 7 GB on disk), made the scale fit. This is the memory that
Level 4's eviction is to bound (P4 repeats this soak with eviction on and a
capped heap).

D stayed small: at most 47,070 dirty nodes (counted every 60 s, in at most
7.9 ms).


## 7. Restarts

Each restart: the readers paused, `sync(STRONG)`, close, open from the
directory and start, then the check (every key at the latest time, and 21,000
keys, the hot ones and 20,000 others, at six times from the first available
lookup time to the latest).

| | Restart 1 | Restart 2 | Restart 3 | End |
|---|---|---|---|---|
| Measured second | 1,800 | 3,619 | 5,438 | 7,255 |
| Close | 0.003 s | 0.072 s | 0.019 s | |
| Startup | 0.87 s | 0.79 s | 1.08 s | |
| Transactions rerun (section of 50 MB) | 4,883 | 5,154 | 4,871 | |
| Stream / first available position | 11,876 / 6,854 MB | 19,108 / 13,694 MB | 26,377 / 22,007 MB | |
| First available lookup time, age | 562 s | 650 s | 399 s | 491 s |
| Check: gets (keys present) | 1,127,000 (954,076) | 1,127,000 (953,483) | 1,127,000 (953,620) | 1,127,000 (953,192) |
| Check: time (latest part) | 19.1 s (16.6 s) | 18.2 s (14.4 s) | 14.8 s (12.8 s) | 1.1 s (0.9 s) |
| Readers paused | 19.9 s | 19.1 s | 15.9 s | |

A restart neither moved the first available lookup time nor the last time
(`first_lookup_moved_s`, `last_time_moved_s` 0). The check after a restart
reads every key cold, from the OS file cache (section 9): 60,000 to 78,000
latest gets a second, against 1.1 s for the same check at the end, warm.


## 8. The companion case

`soak.sh comp1` (01:31:15 to 01:54:37; `HEAP=4g`, 20,000 keys and 200 long
keys, 400 hot keys, retention 60 s, 100 transactions a second, warm-up at
least 60 s, 1,200 steady seconds, three restarts, at least ten cuts, 11
check times; bergdb `065c21f`, the same jar as the main run): `SOAK OK`.

| | |
|---|---|
| Measured | 1,200 steady seconds; 119,998 commits (100.0 a second), 1,143,056 puts and 56,924 deletes: 3.0 updates per key per retention window |
| Reads checked | 11,246,785 gets and 6,301,138 scans (312,527,825 KVs) |
| Expired | 451,291 at admission, none during |
| Physical cuts | 12 in the measured phase (13 with the warm-up's), one every 91 s, each decided when the new first available time was 91 s old |
| Restarts | three, at 300, 601 and 902 measured seconds: startup 0.41 to 0.46 s, 4,604 to 5,780 transactions rerun |
| Checks | after each restart and at the end: every key at the latest time and all 20,400 keys at 11 times from the first available lookup time to the latest, 244,600 gets, in 0.2 to 0.9 s |

Latency: append commits 0.13 ms at the median, 0.24 ms at p99, 39 ms at most;
durable commits 68 ms (the buffer's flush); gets 1.3 and 2.1 µs (latest,
historical) at the median; scans 18 µs at the median, 96 µs at p99. Here the
slowest commits (32 to 39 ms) are the physical cuts, none with a GC pause.
GC: 28 pauses in the measured phase, 613 ms in all, the longest 48 ms; near
the end the old generation, full of the database objects closed at restarts
(the live data was 207 MB), filled the 4 GB heap and took one full
collection of 44 ms.


## 9. What it does not show

* One machine, one JVM, one collector (G1); no ZGC comparison yet (the plan
  allows one as a separate configuration).
* The OS file cache is warm: a restart reads files just written; the reads
  of the checks are not device reads.
* Observed maxima are measurements, not latency guarantees.
* Memory: Level 3 has no eviction, so the run measures how fast memory grows,
  not a bound. Level 4 (eviction) is what bounds it; P4 repeats this soak
  with eviction on and a capped heap, to compare.
* Readers are paced and few; a read-heavy or scan-heavy load, and a hot
  set larger than memory, are other experiments.
* The machine was not idle during the main run: other work ran at the lowest
  priority (`nice -n 19`, one core at a time), single Lean files of the
  item's WPs E2 and E3 and, from 00:36 to 00:38 (uptime 4,994 to 5,134 s),
  E2's random tests. None of the slowest commits or the long pauses falls in
  that window; the effect of that work on the latencies is not measured.
* The heap is not pretouched (section 5), so first-use page faults are in
  the pause times.


## 10. Where the data is

`java/build/soak/NAME/` (ignored by Git, not touched by `build.sh`):
`source.txt`, `stdout.txt`, `gc.log`, `result.json`. Copies of the main run's
and the companion's `source.txt` and `stdout.txt`, and their `result.json`
without the per-second samples, commit counts and histogram buckets
(`NAME-result.json`), are in [evidence/level3-soak/](evidence/level3-soak/).
