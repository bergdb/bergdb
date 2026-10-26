007-05. Startup time against the section (007-03, step 5)
=========================================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Schedule Step 5 tonight at 04:00; I assume night.sh is done by
then; report to news.md." Status: scheduled for 2026-10-27, 04:00; results
below when it has run.


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
package `bergdb.core`, against bergdb.jar as it is (`851acdf`, built in a
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

| Database | Keys | Value | Startup distance | Updates | Last make start |
|---|---|---|---|---|---|
| f53-10m-sd50 | 10M | 8 B | 50 MB | 2M | 07:15 |
| f53-10m-sd200 | 10M | 8 B | 200 MB | 3M | 07:15 |
| f53-10m-sd1000 | 10M | 8 B | 1000 MB | 12M | 07:00 |
| f53-2m-v100 | 2M | 100 B | 200 MB | 2M | 07:15 |
| f53-200k-v10k | 200k | 10 kB | 200 MB | 100k | 07:15 |
| f53-50m-sd200 | 50M | 8 B | 200 MB | 3M | 06:00 |
| f53-50m-sd1000 | 50M | 8 B | 1000 MB | 10M | 05:30 |

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
(the compiled tool, a clone at `851acdf` with its jar, `data/`, `out/`), as
a process detached from any session; the 10M databases stay in `data/`
there for step 6, and the 50M ones are deleted.


Results
-------

Not yet run.
