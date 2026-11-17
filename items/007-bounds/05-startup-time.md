007-05. Startup time against the section (007-03, step 5)
=========================================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Schedule Step 5 tonight at 04:00; I assume night.sh is done by
then; report to news.md." Status: ran 2026-10-27, 04:00 to 05:27; the
results and what they mean are below.


What it measures
----------------

007-03, step 5: how long a start takes against the startup section, at the
startup distances that suit large databases (50, 200 and 1000 MB; 007-04,
5), warm on F53 and cold on s1, and where the time goes. Besides the time:
the section's bytes, the transactions rerun, D, and the reads that reach
the stream file by startup phase, above all the rerun's first touches
(`starter.rerunTransactions`) and rule 4's header reads (`starter.linkD`;
007-04, 3), for step 6.


The tool
--------

[05-startup-time/StartupBench.java](05-startup-time/StartupBench.java), in
package `bergdb.core`, against bergdb.jar as it is (`2966bca`, built in a
scratch clone). Mode `make` builds a database on disk (FileStream): key24
keys in random order, 1,000 puts a transaction, then random updates, as
005-38's WriteBench; it reports the startup lag after every update, and D
at the end, and closes (a close does not write D). Mode `start` times
`start()` in a fresh JVM, counts the reads by phase (the step of
`Db.startInner` or of `DbStarter.doOrdinaryStartup` they come from) with
their bytes and time, samples the starting thread every 2 ms, and checks
2,000 keys. Counting by phase takes a stack trace a read, about 6 µs, so
the timed starts count the reads in all only (`st.phases=0`): on a test of
200,000 keys, 0.36 s against 0.63 s.

[summary.py](05-startup-time/summary.py) makes the table.


The night
---------

[f53-step5.sh](05-startup-time/f53-step5.sh) starts at 04:00 and waits until
F53 has been quiet for 5 minutes (no other JVM, gate, `night.sh` or lake),
giving up at 06:30 with a "needs a look" in news.md. It starts
[s1-step5.sh](05-startup-time/s1-step5.sh) on s1, detached, and then, on
F53, makes each database and starts it three times (the first counting by
phase, the next two timed), warm (the files were just written; a start
reads what the one before it read):

| Database       | Keys | Value | Startup distance | Updates | Last make start |
|----------------|-----:|------:|-----------------:|--------:|----------------:|
| f53-10m-sd50   |  10M |   8 B |            50 MB |      2M |           07:15 |
| f53-10m-sd200  |  10M |   8 B |           200 MB |      3M |           07:15 |
| f53-10m-sd1000 |  10M |   8 B |          1000 MB |     12M |           07:00 |
| f53-2m-v100    |   2M | 100 B |           200 MB |      2M |           07:15 |
| f53-200k-v10k  | 200k | 10 kB |           200 MB |    100k |           07:15 |
| f53-50m-sd200  |  50M |   8 B |           200 MB |      3M |           06:00 |
| f53-50m-sd1000 |  50M |   8 B |          1000 MB |     10M |           05:30 |

The updates fill at least two startup distances after the load (005-38's
bytes a put). Starts with ZGC, a 4 GB budget (2 GB for the small ones, 6 GB
at 50M keys); makes with ParallelGC, without eviction at 10M keys and with
an 8 GB budget at 50M.

On s1 (2 CPUs, 3.8 GB, the virtual disk of 009-03): 10M keys at 50 MB (2M
updates) and at 200 MB (3M updates), each started twice after `echo 3 >
/proc/sys/vm/drop_caches` (the first counting by phase) and once warm, with
`/proc/self/io`'s bytes from the device. Not 1000 MB: D, about 1 GB of node
bytes at 10M keys, does not fit s1 with a heap and an OS cache. Databases
for s1 are made on s1, as F53's upload to it is under 2 MB/s.

At the end: s1's outputs fetched (until 09:30 at most), everything copied to
[05-startup-time/out/](05-startup-time/out/), `out/summary.txt` written, and
an entry in news.md (OK or FAILED). It runs in `/Users/f/fl/bench/007-05`
(the compiled tool, a clone at `2966bca` with its jar, `data/`, `out/`), as
a process detached from any session; the 10M databases stay in `data/`
there for step 6, and the 50M ones are deleted.


Results
-------

Ran 2026-10-27 from 04:00 to 05:27, with no failures; every start found
its 2,000 keys. F53 was quiet from 04:05 (`night.sh` had ended at 02:56).
The ssh that started s1's part returned only when that part was done (its
background job kept the channel open), so s1 ran from 04:05 to 04:50 and
F53 after it, from 04:50 to 05:27: one after the other, not in parallel,
and nothing else changed. The outputs are in
[05-startup-time/out/](05-startup-time/out/), s1's in `out/s1/`, the
table in `out/summary.txt`; the split by phase and the fit below come from
[analyze.py](05-startup-time/analyze.py).

The databases are deterministic: s1's two are F53's (the same stream,
section and D). A transaction is 1,000 puts.

| Database                 |  Stream | Section at the start | Largest in the make | Transactions in the section |                 D |
|--------------------------|--------:|---------------------:|--------------------:|----------------------------:|------------------:|
| 10M keys, 8 B, 50 MB     |  5.3 GB |     108 MB (2.15 sd) |    117 MB (2.33 sd) |                         109 | 177k nodes, 60 MB |
| 10M keys, 8 B, 200 MB    |  2.9 GB |     201 MB (1.00 sd) |    345 MB (1.72 sd) |                         307 |      387k, 137 MB |
| 10M keys, 8 B, 1000 MB   |  2.6 GB |   1,000 MB (1.00 sd) |  1,101 MB (1.10 sd) |                       7,558 |     1.83M, 766 MB |
| 2M keys, 100 B, 200 MB   |  1.0 GB |     200 MB (1.00 sd) |    201 MB (1.00 sd) |                         649 |       211k, 81 MB |
| 200k keys, 10 kB, 200 MB |  3.1 GB |     216 MB (1.08 sd) |    216 MB (1.08 sd) |                          20 |         14k, 5 MB |
| 50M keys, 8 B, 200 MB    | 24.4 GB |     245 MB (1.23 sd) |    485 MB (2.43 sd) |                         956 |     1.28M, 425 MB |
| 50M keys, 8 B, 1000 MB   | 12.2 GB |   1,001 MB (1.00 sd) |  1,654 MB (1.65 sd) |                       4,984 |   3.90M, 1,336 MB |

The make of 10M keys at 50 MB stopped at one of the take's peaks, so its
starts read a section of 2.15 times the startup distance.

### Startup times

| Database                 |          F53, warm | s1, cold | s1, third start |
|--------------------------|-------------------:|---------:|----------------:|
| 10M keys, 8 B, 50 MB     |              7.4 s |    214 s |           175 s |
| 10M keys, 8 B, 200 MB    |             12.4 s |    209 s |           164 s |
| 10M keys, 8 B, 1000 MB   |               70 s |          |                 |
| 2M keys, 100 B, 200 MB   |              9.1 s |          |                 |
| 200k keys, 10 kB, 200 MB |              1.9 s |          |                 |
| 50M keys, 8 B, 200 MB    | 26 s (49 s, 141 s) |          |                 |
| 50M keys, 8 B, 1000 MB   | 86 s (90 s, 215 s) |          |                 |

F53: the mean of the two timed starts, which differ by 2 percent or less;
at 50M keys the third start, with the second and the first in brackets.
F53 has 32 GB, and after a make with a 22 GB heap the OS cache did not hold
the 24 and 12 GB streams: the first start read from the SSD, the next ones
less, and the third may still not be fully warm. The first start of each
database counts its reads by phase and is slower by about 5 µs a read
(13.2 s against 7.4 s at 10M keys and 50 MB). s1: the timed cold start,
after `echo 3 > /proc/sys/vm/drop_caches`; the counted cold starts took 241
and 249 s. The third start on s1 is not warm: 2.6 GB still came from the
device, as s1's 3.8 GB does not hold the stream beside the JVM.

### Where the time goes, warm

F53, the third start, split by the sampler (every 10 ms), in seconds:
reading the section's records, the rerun, rule 4 (`linkD`), the section's
nodes (`createMaps` to `registerSectionNodes`), and the check
(`postStartupCheck`); the rest is under 0.4 s.

| Database          | Start | Reading | Rerun | Rule 4 | Section's nodes | Check |
|-------------------|------:|--------:|------:|-------:|----------------:|------:|
| 10M keys, 50 MB   |   7.4 |     0.8 |   3.1 |    1.3 |             1.6 |   0.5 |
| 10M keys, 200 MB  |  12.5 |     1.4 |   3.6 |    2.1 |             4.3 |   1.1 |
| 10M keys, 1000 MB |  70.1 |     6.5 |  42.6 |    2.1 |            11.9 |   6.8 |
| 2M keys, 100 B    |   9.1 |     1.3 |   4.6 |    0.4 |             2.0 |   0.7 |
| 200k keys, 10 kB  |   1.9 |     1.3 |   0.3 |    0.0 |             0.1 |   0.0 |
| 50M keys, 200 MB  |  25.6 |     1.6 |  11.2 |    7.1 |             3.1 |   2.6 |
| 50M keys, 1000 MB |  85.9 |     6.4 |  47.3 |   11.0 |            12.7 |   8.3 |

* Reading the section's records: 6.0 to 7.1 ms a MB, in all seven.
* The rerun: 5.6 µs a put where it reads little (10M keys at 1000 MB, 0.02
  reads a put, as D holds most of the index), up to 28 µs a put where a put
  reads 2.3 nodes it touches first (10M keys at 50 MB).
* Rule 4: 1.5 to 2.1 µs a header read from the OS cache; 0.6 to 4.9 reads
  a node of D.
* The check, `postStartupCheck` (a pass over the value nodes, and
  `Db.checkNodes`, which checks every key node in memory; always on): 2.0
  to 3.7 µs a node of D, 7 to 10 percent of a start.
* Only the records, the rerun's first touches and rule 4 read the stream
  (and a few reads before them). The third source that step 5 was to
  count, nodes of D that the rerun does not reach, gives none.

The fit of 007-03, step 5, over the five databases that F53 keeps warm:

    time ≈ 9.3 ms × section MB + 7.2 µs × puts rerun + 5.0 µs × reads

It is within 1 percent for the three of 10M keys, 11 percent for 100-byte
values, and 25 percent (0.5 s) for 10 kB values. It overestimates the 50M
ones by 19 and 68 percent, whose reads cost less each: a rough model, and
c, a read with the work that follows it, is not a constant. Cold, c is
the device's: 108 to 180 µs a read on s1 (below).

### Cold, s1

| Start                   |    Time |     Reads | In reads | A read | The rest | From the device |
|-------------------------|--------:|----------:|---------:|-------:|---------:|----------------:|
| 10M keys, 50 MB, cold   | 213.5 s | 1,113,136 |  200.3 s | 180 µs |   13.2 s |          2.9 GB |
| 10M keys, 200 MB, cold  | 208.9 s | 1,722,436 |  185.3 s | 108 µs |   23.6 s |          2.9 GB |
| 10M keys, 50 MB, third  | 175.0 s | 1,113,136 |  162.1 s | 146 µs |   13.0 s |          2.7 GB |
| 10M keys, 200 MB, third | 164.5 s | 1,722,436 |  142.2 s |  83 µs |   22.3 s |          2.6 GB |

* A start on s1 waits for reads 86 to 94 percent of its time: 1.1 and 1.7
  million reads, 83 to 180 µs each, spread over the whole stream (2.9 GB
  from the device, as much as the whole stream at 200 MB). A read costs
  less where the stream is smaller (2.9 GB against 5.3 GB) and more of it
  stays in the OS cache during the start. The rest is about 2.2 times
  F53's time without its reads.
* Rule 4: 78 and 73 percent of the reads (863,609 and 1,254,124), 84
  percent of the time in reads, 80 and 77 percent of the samples. The
  rerun's first touches are the rest: 248,742 and 466,683 reads, 34 s in
  reads in both.
* Not counted: how many of rule 4's reads find a canonical object (for
  step 6).

### What it means

For the promise, measured on F53 (an M1 Pro) and s1 (2 virtual CPUs, a
virtual disk):

|                                   |                        50 MB | 200 MB | 1000 MB |
|-----------------------------------|-----------------------------:|-------:|--------:|
| Warm, 10M keys, 8-byte values     | 7.4 s (a section of 2.15 sd) | 12.4 s |    70 s |
| Warm, 50M keys, 8-byte values     |                              |   26 s |    86 s |
| Warm, 2M keys, 100-byte values    |                              |  9.1 s |         |
| Warm, 200k keys, 10 kB values     |                              |  1.9 s |         |
| Cold, s1, 10M keys, 8-byte values |                        214 s |  209 s |         |

1. Warm, a promise of 10 s (007-01) holds at 50 MB for 10M keys with small
   values, even with the section at 2.15 times the distance, but not at
   200 or 1000 MB, nor at 50M keys. For small values the time follows the
   puts in the section more than its bytes: 62 to 70 ms a MB of section at
   10M keys with 8-byte values, 86 to 104 at 50M keys, 45 with 100-byte
   values, 9 with 10 kB values. With a section of up to twice the distance
   (the deadline), 10 s warm on F53 holds up to a startup distance of
   about 75 MB at 10M keys with 8-byte values, 50 MB at 50M keys, 110 MB
   with 100-byte values and 580 MB with 10 kB values; on a CPU like s1's,
   half as fast, about half of that. 007-04, 5, estimated 170 and 700 MB
   from 29 and 7 ms a MB, measured at 20 to 50 MB with 100-byte and 10 kB
   values; here, 45 and 9 ms a MB.
2. The startup distances of 200 to 1000 MB that 005-38 found best for the
   write overhead at 10M and 50M keys give warm starts of 12 to 86 s. A
   put costs 681 to 1,013 bytes of stream at 50 MB and 180 to 299 at 1000
   MB (005-38); a start, 7 s and 70 to 86 s. The promise and the default
   distance need both in view. Fast restart (006-06) covers planned
   restarts at large distances, not crashes.
3. Cold, on s1's disk, no promise in seconds holds at 10M keys: 3.5 minutes
   at 50 and at 200 MB, nearly all of it random reads. Without rule 4's
   reads (step 6, B or C), about 45 to 55 s on s1: the rerun's first
   touches (250,000 to 470,000 reads, 34 s) and the CPU. A cold start in
   seconds needs the rerun's first touches cheaper or fewer too, for
   example read in position order (step 6, A).
4. Warm, at large distances, the rerun (about 5.6 µs a put, 42 s for 7.6M
   puts at 1000 MB) and the section's nodes take most of the time. The
   check takes 7 to 10 percent and is always on: as a test-only check it
   would save 6.8 to 8.3 s at 1000 MB, if Frans wants that.
5. The section's size counts directly: at 50 MB the make stopped at a peak
   of the take, 2.15 times the distance, and the start paid for it. 005-49
   and the deadline (step 3) bound that.
