005-64. Investigate: the buffer time after group commit, 20, 50 or 100 ms
=========================================================================

Status: open. Kind: investigate. Created 2026-10-28.

Registered at Frans's request (2026-10-28, when he closed 005-48 with the
buffer time kept at 20 ms): "create a new 005 item to investigate 20 ms
vs 50 ms, vs 100 ms."


The issue
---------

The main stream's buffer time (`StorageManager.DEFAULT_BUFFER_TIME`) has
been 20 ms since 005-13 (it was 100 ms). It was chosen for syncs: a sync
waited for the timer, so its latency was the buffer time plus 20 to 50
percent.

Since 005-48 (`e611709`) a sync does not wait for the timer: a waiting
sync has the buffer written at once (`BufferedStream.flushSoon`). The
timer now only bounds how long bytes nobody syncs on stay in the buffer
(the constant's comment). So the reason for 20 ms is gone, and the
choice is open again:

* **Longer (50 or 100 ms)**: fewer and larger writes and forces for
  writers that do not sync (on s1 at 20 ms, 30 to 45 forces a second;
  005-48's tables), and fewer wake-ups of the stream's thread while data
  trickles in (005-14, 010-P3).
* **Shorter (20 ms)**: less data that nobody synced on is lost when the
  power goes, and the bytes reach the disk sooner for readers of other
  processes or a replica.

The buffer also flushes when a quarter of it is filled (2.5 MB of 10 MB),
whatever the timer.


Questions
---------

1. Writers that do not sync: puts a second, forces a second, bytes a
   force, append p99.9 and max, and CPU, at 20, 50 and 100 ms (005-13's
   scenarios `a-100`, `a-1k`, `a-1k-x100`).
2. Writers that sync after each transaction (`d-t1` to `d-t64`): unchanged
   at every buffer time, as 005-48 expects? A check, not a sweep.
3. Mixed: some threads sync, others do not. Does a longer buffer time
   change the syncing threads' latency, as each sync's flush then carries
   more of the others' bytes?
4. Trickle and idle: wake-ups and energy of the stream's thread at a low
   rate (say 10 transactions a second) and with no writes, measured per
   process with `proc_pid_rusage` (005-14's `procstat.c`).
5. Data at risk: the most data that nobody synced on a power loss can take,
   at each buffer time and write rate (bounded by the quarter-buffer
   flush). Written out, so that the default's Javadoc can say it.
6. The replica's 2,000 ms (`DEFAULT_REPLICA_BUFFER_TIME`, 005-48's
   question 5), if replication stays (005-11).


Done when
---------

The runs of questions 1 to 4 at 20, 50 and 100 ms on F53 (quiet, in the
background) and on s1, a recommendation, and Frans's decision. If the
default changes: `DEFAULT_BUFFER_TIME` and its comment, `releases/next.md`,
and `before-commit.sh` and `level3.sh` pass.


First step
----------

A suite of 005-48's scenarios at `bufftime=20`, `50` and `100`
(`48-group-commit/night/group-commit.suite` has them at 20), plus a mixed
scenario if Perf can make one, run with `performance.sh` on HEAD in a
quiet block on F53, as 005-48's `night/run-f53.sh` was set up.


Size and order
--------------

S to M, measurements only, unless the default changes. Needs quiet
machines, so it fits an unattended night, as in 006-09. Builds
on 005-13 (the sweep before group commit), 005-14 (calm when idle) and
005-48 (group commit); 005-47 (written, not forced) touches the same path,
and the measurements should note which durability they ran with.


Data at risk (question 5)
-------------------------

Written 2026-10-28 by Claude (Opus 5.5, Claude Code), from the code at
`bf9fc7f` (`BufferedStream`, `StorageManager`); no runs. It is the most
data, appended but nobody synced, that a power loss (or a crash of the
process: the buffer is in the heap) can take.

**What is at risk.** `StorageManager.append` hands a transaction's bytes
straight to the main stream's `BufferedStream`; nothing else buffers them.
A byte is safe once the flush that carries it has returned:
`FileStream.append` writes and forces each append (`F_FULLFSYNC` on macOS,
fsync on Linux; hard sync, since 005-47's "written, not forced" is not in).
So the bytes at risk are those between the consumer's position and the
producer's, `pStart - cStart`: the bytes still buffered and those of the
flush in progress. A sync makes every byte before it safe when it returns,
so "nobody synced" means the bytes after the last finished flush that
someone waited for, or that the timer or the quarter rule started.

**The rules that bound it** (`BufferedStream`, default buffer of 10 MB,
`DEFAULT_BUFFER_SIZE`):

1. The ring buffer holds every byte at risk, so they never exceed its
   capacity, 10 MB, at any buffer time and any rate. The writer waits for
   room when less than 1 MB (a tenth) is free.
2. The consumer wakes every bufferTime / 4 (5, 12 and 25 ms at 20, 50 and
   100 ms; `waitTime`, integer division). On this macOS a wait lasts
   longer: wait(5) 7.6 ms, wait(12) 18.1 ms, wait(25) 32.3 ms (005-13's
   WaitProbe, `runs/waitprobe.txt`); on Linux about what is asked. Call
   the real wait w'.
3. **The timer.** A flush starts after 4 wakes counted from the start of
   the last flush (`waitCount` is set to 0 when a flush starts, and
   counts the wakes after it ends): 4w' after the last flush ended, about
   30, 72 and 129 ms on F53 (20, 48 and 100 ms on Linux).
4. **The quarter rule.** At a wake, a flush also starts if a quarter of the
   buffer, 2.5 MB, is buffered. Nothing wakes the consumer when that is
   reached, so up to w' more is buffered first.
5. A flush takes everything buffered when it starts, at most half the
   buffer (5 MB); what arrives during its force waits for the next one.
6. **Idle.** When nothing has been buffered for 4 wakes, the consumer
   waits until an append wakes it (005-14); it then waits once more, w',
   and flushes.

**The bound.** Let R be the rate at which the stream grows (bytes a
second; the stream has some 1.0 to 1.6 bytes per user byte with the
index) and F the time of one force (on F53 about 5 ms for a small append
and 7 to 12 ms for 1 to 4 MB; on s1 about 4 ms for 4 KB; 005-13's and
005-48's force probes). A flush that started at s_k is safe at its end
e_k = s_k + F; the next starts at s_k+1 and ends at e_k+1. Until then,
everything appended since s_k is at risk, so the most is just before
e_k+1:

* **At a low rate** (the timer; R × 4w' under 2.5 MB):
  R × (4w' + 2F), the writes of the last 4w' + 2F. With F = 5 ms that is
  about **40 ms of writes at 20 ms, 82 ms at 50 ms and 139 ms at 100 ms**
  on F53 (30, 58 and 110 ms on Linux). On average about half of it.
* **At a high rate** (the quarter rule; R × 4w' at least 2.5 MB, that is
  from about 83, 35 and 19 MB/s at 20, 50 and 100 ms on F53, and 125, 52
  and 25 MB/s on Linux): at most 2.5 MB + R × (w' + F), whatever the
  buffer time beyond its w'.
* **When the disk cannot keep up** (more than 5 MB a force): the buffer
  fills, the writer waits, and the bound is the buffer, 10 MB.
* **A trickle**: when the transactions come further apart than 5w' + F
  (the consumer goes idle in between), each is flushed alone, one w' + F
  after its append, about 13 ms on F53 at 20 ms and 23 ms at 50 ms. At 10
  transactions a second (100 ms apart) that holds at 20 and 50 ms (5w' +
  F is 43 and 95 ms), so at most one transaction is at risk; at 100 ms
  (5w' + F = 167 ms) the consumer never goes idle, the timer flushes every
  4w' + F, about 134 ms, and up to two transactions are at risk. (The
  smoke test of `night/trickle.sh` agrees: 10.0 forces a second at 20 and
  50 ms, 8.1 at 100 ms.)

**Worked out for F53** (macOS waits, F = 5 ms below the quarter rule and
12 ms above it; the most at risk, not the mean):

| stream growth | 20 ms | 50 ms | 100 ms |
|---|---:|---:|---:|
| 10 small transactions a second | 1 transaction, 13 ms | 1 transaction, 23 ms | 2 transactions, 134 ms |
| 100 KB/s | 4 KB | 8 KB | 14 KB |
| 1 MB/s | 40 KB | 82 KB | 139 KB |
| 10 MB/s | 0.4 MB | 0.8 MB | 1.4 MB |
| 30 MB/s | 1.2 MB | 2.5 MB | 3.8 MB (quarter rule) |
| 100 MB/s (F53's bulk writes) | 4.5 MB (quarter rule) | 5.5 MB (quarter rule) | 6.9 MB (quarter rule) |
| any rate | at most 10 MB | at most 10 MB | at most 10 MB |

So for a writer that never syncs, a longer buffer time puts up to about
3.5 times as much at risk at the same rate (139 against 40 ms of writes),
until the quarter rule takes over at some tens of MB/s, and never more than
the 10 MB buffer. A writer that syncs loses nothing it synced, at any buffer
time. For the default's Javadoc: a power loss can take the writes of
about 1.1 to 2 buffer times that nobody synced (4 waits and two forces:
the most at short buffer times on macOS, whose waits run long), fewer at
high rates, where a quarter of the buffer starts a flush, and never more
than the buffer, 10 MB.

What the night's runs add to it: `night/trickle.sh` counts the forces a
second of the trickle at each buffer time; nothing measures the bytes at
risk directly.


State
-----

2026-10-28, 10:06, by Claude (Opus 5.5, Claude Code), 006-10's W3.1: the
scripts for tonight's runs are written and smoke-tested; nothing timed has
run. Clone `/Users/f/fl/bench/006-10/w3` (from `main` at `bf9fc7f`), where
these files are committed; the lead copies them into `main`.

* **The build**: `main-bf9fc7f`, `main`'s HEAD of 2026-10-28 (before
  007-07), made with `performance.sh build` in
  `/Users/f/fl/bench/006-10/w3/java/build/perf/builds/main-bf9fc7f`, its
  harness compiled. `night/prepare.sh` (run) made the tools in
  `w3/java/build/perf/005-64-tools` (MixedProbe, TrickleProbe, 005-13's
  ForceProbe, the CPU agent `cpu64.jar`, 005-14's `procstat`) and the
  package for s1 in `w3/java/build/perf/005-64-s1-package`. After a
  change to a file in `night/` or `tools/`, run `sh night/prepare.sh`
  again (the package copies them). For another build: `performance.sh
  build LABEL` in `w3/java`, then `BUILD=LABEL` for prepare.sh and the
  three scripts.
* **The steps** (each with `# minutes:`, `SMOKE=1` for a smoke test, and
  a summary checked row by row: `table.py --check` or `trickle-table.py
  --check` must print CHECK OK, or the script exits 1). Raw output goes
  to `/Users/f/fl/bench/006-10/night/out/`.
  * `night/run-f53.sh` (90 minutes; F53, the quiet block): questions 1 to
    3. Up to 9 rounds of `night/rounds.sh` (`bufftime.suite` through
    `performance.sh reference`, RUNS=1, then `MixedProbe` for each line
    of `mixed.txt`), the buffer times rotated 20 50 100 / 50 100 20 /
    100 20 50; no round starts that would end more than 84 minutes after
    the script started. FORCE from the
    environment goes to `performance.sh`. Output `out/64-f53/`
    (`table.md`, `check.txt`).
  * `night/trickle.sh` (26 minutes; F53): question 4. Two rounds of a
    database at 20, 50 and 100 ms with 10 transactions a second for 135 s
    and then idle, and a JVM alone; `procstat` windows of 120 s (trickle)
    and 60 s (idle). Output `out/64-trickle/`.
  * `night/run-s1.sh` (60 minutes; s1, in the background): the same
    rounds on s1 (heap 2 GB, up to 6 rounds, none past 55 minutes);
    waits up to 15 minutes for s1 to be idle (exit 2), copies the package
    to `/opt/bergdb-bench/005-64/`, fetches the summaries to
    `out/64-s1/`. `sh night/run-s1.sh check` is a dry check of s1;
    `fetch` fetches again.
* **Smoke tests** (10:03 to 10:06, each `SMOKE=1`, each parsed row by
  row): `run-f53.sh` CHECK OK, 15 rows (2 scenarios and 3 mixed
  configurations at 3 buffer times, 2 rounds); `trickle.sh` CHECK OK, 4
  rows; `run-s1.sh` (the package run here, then the same fetch) CHECK OK,
  15 rows, and the fetch had `table.md` and no JSON. On s1 itself, the
  runner's smoke mode (one round; before the third smoke configuration
  was added) CHECK OK, 12 rows: the shims, `rounds.sh` and the CPU agent
  work there. `sh night/run-s1.sh check` at 09:58: s1 idle (load 0.10,
  no JVM), JDK 27 and Python 3.14 there, 33 GB free, the package copied
  to `/opt/bergdb-bench/005-64/`.
* **Question 3, mixed threads**: Perf cannot express it (a run's threads
  all sync or none do), so a probe of our own, `tools/MixedProbe.java`,
  with three configurations (`night/mixed.txt`).
* **Question 1's CPU**: Perf does not record CPU, so the runs carry a Java
  agent (`tools/CpuAgent.java`, through `JFLAGS`) that prints the
  process's CPU and the consumer thread's for the whole run.
* **Question 5**: written out above, from the code.
* **Question 6** (the replica's 2,000 ms): not measured, as replication
  waits for 005-11.
* **For the morning**: the three `table.md` into this entry, with what
  they show and a recommendation (keep 20 ms or change the default), and
  Frans's decision. The runs measure today's durability (every append
  forced; 005-47 not in).
