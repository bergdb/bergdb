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
