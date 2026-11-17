005-64. Investigate: the buffer time after group commit, 20, 50 or 100 ms
=========================================================================

Status: done (2026-10-29: Frans decided 50 ms; see Decision and
Outcome). Kind: investigate. Created 2026-10-28.

Registered at Frans's request (2026-10-28, when he closed 005-48 with the
buffer time kept at 20 ms): "create a new 005 item to investigate 20 ms
vs 50 ms, vs 100 ms."


The issue
---------

The main stream's buffer time (`StorageManager.DEFAULT_BUFFER_TIME`) has
been 20 ms since 005-13 (it was 100 ms). It was chosen for syncs: a sync
waited for the timer, so its latency was the buffer time plus 20 to 50
percent.

Since 005-48 (`d8ed1aa`) a sync does not wait for the timer: a waiting
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
`ffb890a` (`BufferedStream`, `StorageManager`); no runs. It is the most
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


The night's scripts
-------------------

The State note of 2026-10-28, kept for how the runs were made and how to
repeat them.

2026-10-28, 10:06, by Claude (Opus 5.5, Claude Code), 006-10's W3.1: the
scripts for tonight's runs are written and smoke-tested; nothing timed has
run. Clone `/Users/f/fl/bench/006-10/w3` (from `main` at `ffb890a`), where
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


Results, 2026-10-28 night
-------------------------

Written 2026-10-29 by Claude (Opus 5.5, Claude Code), 006-10's morning
write-up. All runs on `main-bf9fc7f` (today's durability: every append
forced, 005-47 not in), each exit 0, every row parsed (CHECK OK). The
summaries: [night/results-f53-2026-10-28.md](64-buffer-time-after-group-commit/night/results-f53-2026-10-28.md)
(9 rounds, 2026-10-29 00:05 to 01:11),
[night/results-s1-2026-10-28.md](64-buffer-time-after-group-commit/night/results-s1-2026-10-28.md)
(6 rounds, 2026-10-28 17:55 to 18:49) and
[night/results-trickle-2026-10-28.md](64-buffer-time-after-group-commit/night/results-trickle-2026-10-28.md)
(F53, 2 rounds, 19:59 to 20:23). Medians of the rounds; a range in
parentheses is the spread across rounds, given when wider than 10 %
(15 % for the trickle); no range means the rounds agree within that.

**F53 ran not quiet.** The conductor's 10-minute check found it busy
(other sessions), so `run-f53.sh` ran with FORCE=1; before each round the
CPU was 81 to 86 % idle. The trickle's quietness was not checked. F53's
spreads are still mostly under 10 %, and the conclusions below hold on
both machines. s1 was idle (100 % idle CPU before each round); its spreads
are wider, as in 005-48. s1's 20 ms rows agree with 005-48's prototype
(now `main`) on s1: a-100 169,000 against 164,000 puts a second, a-1k
81,600 against 80,500, a-1k-x100 88,700 against 90,500; d-t1 248 against
213 commits a second, d-t16 1,735 against 1,758, d-t64 7,023 against
6,429.

### 1. Writers that do not sync

One thread, no sync; x100 is 100 puts a transaction. F53 | s1.

| scenario | buffer time | puts/s | forces/s | KB per force | append p99.9 us | append max ms | process CPU s |
|---|---:|---:|---:|---:|---:|---:|---:|
| a-100 | 20 ms | 286,450 \| 168,988 (161,013–182,693) | 33.5 \| 30.0 | 2,132 \| 1,428 (1,331–1,526) | 35.6 \| 67.3 (57.6–80.4) | 68 (0.4–73) \| 131 (99–156) | 10.2 \| 15.7 |
| a-100 | 50 ms | 286,628 \| 165,944 | 29.8 \| 19.5 | 2,396 \| 2,133 | 35.3 \| 70.4 (68.1–77.8) | 61 (0.4–69) \| 140 | 10.3 \| 15.9 |
| a-100 | 100 ms | 288,071 \| 170,613 (161,210–184,157) | 28.4 \| 17.8 (16.8–19.0) | 2,524 \| 2,384 | 34.8 \| 63.7 (57.3–76.3) | 52 (45–67) \| 131 (96–152) | 10.0 \| 15.7 |
| a-1k | 20 ms | 105,211 \| 81,609 | 56.7 \| 43.3 | 2,253 \| 2,274 | 26.0 \| 55.4 (44.3–60.4) | 53 (0.1–60) \| 98 (4–122) | 11.6 \| 16.6 |
| a-1k | 50 ms | 105,141 \| 82,123 | 49.0 \| 35.4 | 2,617 \| 2,809 | 25.9 \| 52.0 (45.6–57.3) | 0.1 (0.1–55) \| 95 (2–162) | 11.6 \| 16.1 |
| a-1k | 100 ms | 91,748 \| 70,601 | 33.4 \| 25.8 | 3,313 \| 3,307 | 27.4 \| 57.9 (56.1–66.0) | 30 (17–55) \| 104 (40–166) | 11.6 \| 16.6 |
| a-1k-x100 | 20 ms | 112,577 \| 88,730 | 58.0 \| 43.2 | 2,277 \| 2,403 | 1,016 \| 3,858 (2,802–4,293) | 32 (1–43) \| 151 (21–358) | 15.5 \| 23.3 |
| a-1k-x100 | 50 ms | 112,752 \| 90,483 | 50.0 \| 34.9 | 2,647 \| 2,976 | 999 \| 4,391 (3,473–7,864) | 1.2 (1.1–42) \| 22 (9–173) | 15.5 \| 23.2 |
| a-1k-x100 | 100 ms | 96,027 \| 74,198 | 33.7 \| 26.2 | 3,332 \| 3,326 | 16,515 (14,746–17,302) \| 24,576 (21,365–33,554) | 31 (19–45) \| 42 (35–288) | 15.5 \| 23.1 |

* **50 ms**: the same puts a second as 20 ms on both machines, and fewer,
  larger forces: 11 to 14 % fewer on F53 (a-1k 56.7 to 49.0), 18 to 35 %
  on s1 (a-100 30.0 to 19.5, a-1k 43.3 to 35.4). The append p99.9 is
  unchanged. The process's CPU is unchanged (within 3 %).
* **100 ms**: fewer forces still (a-1k 33.4 on F53, 25.8 on s1), but with
  1 KB values (about 100 MB/s of user data) **13 to 16 % fewer puts a
  second on both machines** (a-1k 105,211 to 91,748 on F53, 81,609 to
  70,601 on s1), and the x100 transaction's p99.9 goes from about 1 ms to
  16.5 ms on F53 and from 3.9 to 24.6 ms on s1. The likely cause, from
  question 5's rules: the quarter rule is checked only at a wake, every
  bufferTime / 4 (32 ms on F53 at 100 ms, 7.6 ms at 20 ms); at 100 to
  170 MB/s of stream that is 3 to 5 MB between checks on F53, a flush takes at
  most 5 MB, and the writer waits when less than 1 MB of the 10 MB is free.
  At 100 bytes (30 MB/s on F53, 18 on s1) it does not happen.
* The append max is bimodal at every buffer time (a few tenths of a ms in
  some rounds, tens of ms in others); its median does not separate the
  buffer times.
* The consumer thread's CPU (in the summaries) is small beside the
  process's (0.1 to 1.7 s of 10 to 23 s); it moves by at most a few tenths
  of a second between buffer times, down with longer ones on F53, up on
  s1.

### 2. Writers that sync after each transaction

sync(ORDINARY) after each transaction, 1 KB values. F53 | s1.

| scenario | buffer time | commits/s | sync p50 ms | sync p99 ms | forces/s |
|---|---:|---:|---:|---:|---:|
| d-t1 | 20 ms | 187 (181–208) \| 248 (194–260) | 5.2 \| 3.6 (3.5–4.3) | 8.2 \| 10.7 (8.4–23.1) | 187 \| 248 |
| d-t1 | 50 ms | 187 (179–209) \| 232 (209–278) | 5.3 \| 3.7 (3.3–4.2) | 7.6 \| 14.6 (8.7–16.9) | 187 \| 232 |
| d-t1 | 100 ms | 185 (180–205) \| 235 (159–252) | 5.3 \| 3.7 (3.5–4.9) | 8.1 \| 14.0 (11.4–24.8) | 185 \| 235 |
| d-t16 | 20 ms | 1,545 \| 1,735 (1,507–2,050) | 10.3 \| 8.0 (7.1–9.0) | 14.9 \| 29.1 (19.9–44.3) | 193 \| 217 |
| d-t16 | 50 ms | 1,543 \| 1,758 (1,560–2,083) | 10.2 \| 7.8 (7.1–8.6) | 14.9 \| 29.5 (15.9–35.7) | 194 \| 220 |
| d-t16 | 100 ms | 1,548 \| 1,914 (1,632–2,053) | 10.2 \| 7.5 (7.2–8.5) | 14.5 \| 23.3 (19.8–36.4) | 194 \| 239 |
| d-t64 | 20 ms | 5,994 \| 7,023 (6,377–7,650) | 10.4 \| 8.0 (7.3–8.7) | 15.4 \| 26.5 (20.3–28.7) | 188 \| 222 |
| d-t64 | 50 ms | 5,997 \| 6,685 (6,326–7,381) | 10.4 \| 8.1 (7.6–8.5) | 15.9 \| 31.5 (24.9–37.0) | 189 \| 211 |
| d-t64 | 100 ms | 5,991 \| 7,098 (5,467–7,247) | 10.4 \| 7.8 | 16.6 \| 23.5 (21.2–44.6) | 188 \| 224 |

Unchanged at every buffer time, as 005-48 expects: on F53 the commits a
second and the sync p50 within 2 %, on s1 within the spread (no trend; the s1 differences change sign between
scenarios). The force paces the commits, not the timer.

### 3. Mixed writers

`MixedProbe` (`night/mixed.txt`), 1 KB values: m-s1-p1 is one thread that
syncs back to back beside one that never syncs, as fast as it can;
m-s16-p1r10k is 16 syncing threads beside 10,000 plain puts a second
(10 MB/s); m-s1r10-p1r10k is a sync 10 times a second beside 10 MB/s of
plain puts. F53 | s1.

| scenario | buffer time | sync commits/s | sync p50 ms | sync p99 ms | plain puts/s | forces/s | KB per force |
|---|---:|---:|---:|---:|---:|---:|---:|
| m-s1-p1 | 20 ms | 123 (115–131) \| 43 (36–58) | 7.2 \| 12.6 (11.5–16.6) | 17.0 \| 119 (78–138) | 119,835 \| 80,653 (57,725–111,662) | 138 \| 56 | 1,032 \| 1,782 |
| m-s1-p1 | 50 ms | 125 \| 42 (18–53) | 7.2 \| 14.5 (12.9–16.0) | 16.9 \| 105 (89–135) | 120,192 \| 93,507 (34,979–109,806) | 139 \| 56 | 1,022 \| 1,872 |
| m-s1-p1 | 100 ms | 123 \| 41 (34–61) | 7.3 \| 15.1 (12.4–16.1) | 17.4 \| 117 (83–124) | 119,846 \| 91,080 (65,544–111,562) | 137 \| 54 | 1,040 \| 1,947 |
| m-s16-p1r10k | 20 ms | 1,538 \| 1,761 (1,651–1,850) | 10.2 \| 8.0 | 19.9 \| 29.6 (23.7–35.3) | 10,000 \| 10,001 | 194 \| 219 | 69 \| 63 |
| m-s16-p1r10k | 50 ms | 1,538 \| 1,696 (1,633–1,876) | 10.2 \| 8.2 | 19.8 \| 31.8 (22.2–33.1) | 10,000 \| 10,000 | 194 \| 210 | 69 \| 65 |
| m-s16-p1r10k | 100 ms | 1,537 \| 1,845 (1,614–1,896) | 10.2 \| 7.9 (7.6–8.7) | 19.9 \| 24.4 (21.9–33.0) | 10,000 \| 10,000 | 194 \| 227 | 69 \| 63 |
| m-s1r10-p1r10k | 20 ms | 10 \| 11 | 5.6 (5.2–5.9) \| 5.4 | 18.1 (14.4–21.8) \| 51 (17–85) | 10,000 \| 10,540 | 40.7 \| 40.9 | 288 \| 311 |
| m-s1r10-p1r10k | 50 ms | 10 \| 11 | 5.6 \| 6.6 (6.4–7.4) | 17.2 (14.8–17.8) \| 47 (25–204) | 10,000 \| 10,521 | 21.2 \| 22.0 | 553 \| 580 |
| m-s1r10-p1r10k | 100 ms | 10 \| 11 | 8.4 \| 8.9 | 20.3 \| 49 (30–107) | 10,000 \| 10,494 | 11.2 \| 12.3 | 1,050 \| 1,032 |

* When the syncs come often (m-s1-p1, m-s16-p1r10k), the syncs make the
  flushes and the timer hardly fires: no change on F53; on s1 m-s1-p1's
  sync p50 rises from 12.6 to 14.5 and 15.1 ms, but within a wide spread
  (s1's m-s1-p1 rows range by a factor of 2 to 3 between rounds).
* **When the syncs are rare (m-s1r10-p1r10k), a longer buffer time makes
  each sync slower**: between the syncs the timer flushes less often, so
  the sync's flush carries more of the plain writer's bytes (288, 553 and
  1,050 KB a force on F53). The sync's p50 is 5.6, 5.6 and 8.4 ms on F53
  and 5.4, 6.6 and 8.9 ms on s1: at 100 ms 50 to 65 % slower on both, at
  50 ms the same on F53 and 22 % slower on s1. In return the forces a
  second halve with each step (41, 21, 11).

### 4. Trickle and idle (F53)

`night/trickle.sh`: 10 small transactions a second, no sync, then nothing;
`proc_pid_rusage` over 120 s (trickle) and 60 s (idle), 2 rounds.

| process | wake-ups/s | CPU ms/s | energy uW | forces/s |
|---|---:|---:|---:|---:|
| trickle, 20 ms | 85 | 21.6 (17.9–25.2) | 1,316 | 10.0 |
| trickle, 50 ms | 84 | 23.7 (18.1–29.2) | 1,303 | 10.0 |
| trickle, 100 ms | 65 | 20.0 (16.7–23.4) | 1,299 | 7.5 |
| idle, 20 ms | 25 | 1.7 (1.3–2.1) | 50 | 0.01 |
| idle, 50 ms | 25 | 1.8 (1.3–2.4) | 52 | 0.01 |
| idle, 100 ms | 25 | 2.6 (2.3–2.9) | 51 | 0.01 |
| JVM alone, no database | 25 | 2.3 | 49 | 0.00 |

* **Idle**: the same at every buffer time and the same as a JVM with no
  database (25 wake-ups a second, about 50 uW). 005-14's idle wait does not
  depend on the buffer time.
* **Trickle**: 50 ms is the same as 20 ms (each transaction is flushed
  alone, 10 forces a second, as question 5 expects). 100 ms has 24 % fewer
  wake-ups (65 against 85) and 25 % fewer forces (7.5), but the same
  energy (1.30 against 1.32 mW, within 1.5 %) and CPU within the spread.

### Recommendation

**Keep 20 ms.** For Frans to decide.

* **100 ms is worse.** It costs 13 to 16 % of the throughput of writers
  that do not sync at about 100 MB/s, on both machines, a p99.9 of 16 to
  25 ms for large transactions (from 1 to 4 ms), and 50 to 65 % on the
  latency of a rare sync beside a writer that does not sync. It gains
  fewer forces, and on the trickle fewer wake-ups but no less energy.
* **50 ms gains little.** Its one clear gain is fewer forces for writers
  that do not sync: 11 to 14 % on F53, 18 to 35 % on s1, with the same
  throughput, latency and CPU. Fewer forces matter for the disk's wear and
  for other processes on the same disk, not for BergDB's own speed here.
  It costs up to 22 % on a rare sync beside a plain writer (s1).
* **010-P3, calm**: no reason to change. Idle is the same at every
  buffer time (and the same as a bare JVM); at 10 transactions a second 50
  ms changes nothing, and 100 ms saves wake-ups but not energy.
* **Data at risk** (question 5): for a writer that never syncs, a power
  loss can take up to about 40 ms of writes at 20 ms, 82 ms at 50 ms and
  139 ms at 100 ms on F53 (30, 58 and 110 ms on Linux), until the
  quarter rule caps it at some tens of MB/s, and never more than 10 MB. 50
  ms doubles it, 100 ms about triples it, for the gains above. Writers
  that sync lose nothing they synced at any buffer time.
* **The stream is unchanged**: the buffer time decides only when the
  bytes are written and forced, not which bytes; the stream's bytes are
  the same at 20, 50 and 100 ms. So the choice has no format consequence
  and can be changed later at the cost of one constant, its comment and
  `releases/next.md`; nothing forces it now.

If Frans prefers fewer forces, 50 ms is the change to make (not 100 ms);
the Javadoc would then say "about 1.1 to 2 buffer times of writes nobody
synced", from question 5.

### What is not measured

* **Question 6**, the replica's 2,000 ms (`DEFAULT_REPLICA_BUFFER_TIME`):
  not measured, as replication waits for 005-11.
* **The bytes at risk** are computed from the code (question 5), not
  measured; the trickle's forces a second (10, 10, 7.5) agree with it.
* **005-47's "written, not forced"** would make a flush cheaper (an fsync
  of 4 KB takes 0.08 ms on F53 against 5.4 ms for `F_FULLFSYNC`), and with
  it the case for fewer flushes; the runs are with every append forced.
* **F53 quiet**: F53's rounds ran on a busy machine; a quiet repeat would
  firm up the small differences, but the two findings that decide (100
  ms's throughput loss and the rare sync's latency) are on both machines.
* **Several databases, or other processes on the same disk**, where fewer
  forces might matter more than here.

Decision
--------

Frans, 2026-10-29, 09:36: "Use 50 ms. Also register a 005 fix for the
rest." His reasons, from the conversation: fewer forces mean fewer
rewrites of the stream's last, partly filled page, so less wear of the
SSD and fewer chances that a power loss tears a page that already holds
forced bytes; at 50 ms the night's runs showed 11 to 14 % fewer forces on
F53 and 18 to 35 % on s1 for writers that do not sync, half the forces of
a rare sync beside a plain writer (m-s1r10-p1r10k, 41 to 21 a second),
with the same throughput, latency and CPU. The cost is about twice the data that nobody synced at risk (about
82 against 40 ms of writes on F53, question 5). Syncing writers are
unchanged (group commit, 005-48), and the stream's bytes do not depend on
the buffer time. "The rest", the quarter rule seen only when the thread
wakes (the cause of 100 ms's throughput loss), is
[005-76](76-wake-at-a-quarter.md).


Outcome
-------

2026-10-29, by Claude (Opus 5.5, Claude Code), 006-10's session, in a
clone on `main`'s `5dda08b`.

* **The default**: `StorageManager.DEFAULT_BUFFER_TIME = 50` (was 20).
  Its comment gives the history (100 until 2026-10-20, 20 until
  2026-10-29, 50 since, with the reasons) and question 5's sentence: for
  bytes nobody synced, a power loss can take the writes of about 1.1 to 2
  buffer times (about 82 ms of writes on macOS), fewer at high rates, and
  never more than the buffer. Everything else follows the constant and
  needed no change: `BufferedStream(stream)`, `DbBuilder.stream(name,
  stream)` and `mainStream`, and the Pub API's builder
  (`DatabaseBuilderImp`, the database and the replicas it adds). The
  replicas' 2,000 ms (`DEFAULT_REPLICA_BUFFER_TIME`) and the tests' 10 ms
  (`DbBuilder.testSetup`) are unchanged.
* **Docs that said 20 ms**: `Db`'s class Javadoc (what an unstopped
  database still writes), docs/levels.md (Level 3's limits),
  010-01's P3 (and P2: the buffer time checked, below); the stale "buffer time 100 ms" comment of
  `java/stress/performance.suite`'s durable commits. `releases/next.md`:
  a line under Performance (the default 20 to 50 ms, and what it means
  for data that is not synced). `releases/2026.1/` and the history in
  items and docs/log.md are left as they were.
* **Tests**: none changed. No test asserts the default (no test names
  `DEFAULT_BUFFER_TIME` or a buffer time of 20 ms); most unit and f-tests
  run with `testSetup`'s 10 ms or a buffer time of their own, and all pass
  with the default at 50 ms. No timing check was loosened.
* **StreamDigest** (P2): `StreamDigest all`, main `5dda08b` against the
  change, one compiled copy (main's): "DIGESTS IDENTICAL (36 of 36)". As
  StreamDigest's databases use `testSetup` (10 ms), the default does not
  reach them; so also main with `testSetup`'s buffer time set to 50 ms
  against main: "DIGESTS IDENTICAL (36 of 36)", a check that the buffer
  time leaves the bytes unchanged (010-01, P2's "to check").
* **Gates**, `nice -n 10`, F53 not quiet (other sessions): `before-commit.sh`
  "BEFORE COMMIT OK (99 s)" (1,069 unit tests, 77 f-tests); `level1.sh`
  "LEVEL 1 OK" (MEM:129, SS:1.51); `level2.sh quick` "LEVEL 2 OK";
  `level3.sh` (full) "LEVEL 3 OK".

Files: [64-buffer-time-after-group-commit/outcome/](64-buffer-time-after-group-commit/outcome/):
`gates.txt` (the gates' summary lines), `digest-base.txt`,
`digest-cur.txt` and `digest-probe50.txt`.


State
-----

2026-10-29, 06:15, by Claude (Opus 5.5, Claude Code), 006-10's morning
write-up: **ready to decide.** The night's runs of questions 1 to 4 are in
(F53 9 rounds, not quiet; s1 6 rounds; the trickle 2 rounds on F53), with
the tables and the recommendation in "Results, 2026-10-28 night" above:
keep 20 ms (100 ms costs 13 to 16 % of the throughput at 1 KB values and
slows a rare sync by 50 to 65 %; 50 ms only saves 11 to 35 % of the forces
of writers that do not sync, for twice the data at risk; idle and the
trickle's energy are the same at every buffer time). The summaries are in
`night/results-*-2026-10-28.md`; the raw output stays in
`/Users/f/fl/bench/006-10/night/out/64-f53/`, `64-s1/` and `64-trickle/`,
outside the repository. Question 5 is written (from the code), question 6
not measured (005-11). Next: Frans's decision. If he keeps 20 ms, the item
is done with no code change (perhaps question 5's sentence in the
constant's comment); if he changes it, see "Done when".

2026-10-29, by Claude (Opus 5.5, Claude Code), 006-10's session:
**done.** Frans decided 50 ms (Decision); the default, its comment, the
docs and `releases/next.md` changed, StreamDigest identical, the four
gates pass (Outcome). The rest is 005-76.
