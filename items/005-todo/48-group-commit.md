005-48. Group commit: a waiting sync starts the flush
====================================================

Status: done (2026-10-28; see Outcome). Kind: investigate. Created 2026-10-26.

Proposed in [005-13](13-buffer-time.md) (question 5, "Then, likely, group
commit"), not done there; registered at Frans's request (2026-10-26: "Yes,
group commit as 005-48."), after a discussion of the buffer time and the
hard sync of `FileStream` (every append forced, since 2026-10-14).


The issue
---------

BergDB already commits in groups: the transactions appended to
`BufferedStream` before a flush go out in that flush's one write and one
force. What decides when a flush happens is the timer only:

* `BufferedStream.runConsumer` wakes every bufferTime / 4 (5 ms at the
  default of 20 ms) and flushes after four wakes, or earlier when a
  quarter of the buffer (2.5 MB of 10 MB) is filled (`shouldFlush`).
* `StorageManager.sync(length)` and `syncStrong(length)` only wait on
  `d1Lock` or `d2Lock` until the confirmed length reaches the position.
  Nothing tells the consumer that someone waits.

So a sync waits for the timer, even when the disk is idle. 005-13's sweep
on F53 (SSD, `F_FULLFSYNC`): one thread that syncs after each commit gets
35 ms a sync (p50) and 29 commits a second at 20 ms, while one force of a
small append costs 4 to 5 ms. 16 threads get 456 commits a second, 64
threads 1,813. `Object.wait` on macOS also sleeps longer than asked
(wait(5) 7.6 ms; 005-13), which adds to it.

A replica's stream has a buffer time of 2,000 ms
(`DEFAULT_REPLICA_BUFFER_TIME`), so `sync(STRONG)` with a replica waits
up to about 2 s for the same reason (replication is experimental, 005-11).


The change
----------

The classic group commit (InnoDB, PostgreSQL and others): the flush is
started by demand, and the force paces the groups.

1. A sync that must wait asks the consumers of the streams its rule needs
   for a flush, before it waits: a call on `BufferedStream`, say
   `flushSoon()`, that sets a flag and notifies the consumer.
2. The consumer, when the flag is set, flushes at once instead of waiting
   for its timer: everything buffered so far, in one write and one force.
3. While a force runs, new transactions collect in the buffer. When it
   ends and the flag was set again, the next flush starts at once and
   takes them all. Under load the group is what arrived during one force;
   at low load it is one transaction, with a latency of about one force.
4. The timer stays, as the longest time data that nobody syncs on is
   buffered.

What does not change: `sync(level)`, the sync levels and the rules D1 and
D2; writers that do not sync; the stream (StreamDigest identical, as only
the cut points between chunks move, not the bytes).

Expected on F53, not measured: one thread about 5 ms a sync (some 200
commits a second, against 29); 64 threads several thousand a second, each
force carrying up to 64 transactions. Where a force takes seconds (s1's
disk, 005-46), the force sets the pace both today and with the change.


Questions
---------

1. The gain, measured with 005-13's suite (`performance-bufftime.suite`,
   `commit=durable threads=1, 4, 16, 64`): sync p50, p99 and commits a
   second, today against the change, at 20 ms.
2. Writers that do not sync: unchanged throughput, forces a second and
   bytes a force (Perf's force counters).
3. Does a group commit want a short wait before the flush (a few hundred
   microseconds, as some systems do) to collect more transactions, or is
   the force's own duration enough? Measure before adding one.
4. With demand flushes, what should the timer be? It no longer sets the
   latency of a sync, so it can be chosen for fewer forces and wakeups
   when data trickles in (005-14) and for how much unsynced data a power
   loss may take.
5. The same for the replica's 2,000 ms, if replication stays (005-11).
6. How it meets 005-46 (a reader of the last file waits for the force)
   and 005-47 (written, not forced): a demand flush means more, smaller
   forces at low load.


Done when
---------

A prototype on a scratch clone, the measurements of questions 1 and 2 on
F53 (quiet, in the background) and on s1, and a recommendation; if Frans
says go, the change with a test (a sync after a single commit returns
within about a force, with a forcing `FileStreamIo` that sleeps),
`before-commit.sh`, `level3.sh` (the durability path), StreamDigest
identical, and `StorageManager.DEFAULT_BUFFER_TIME`'s comment updated.


First step
----------

Prototype `flushSoon()` in `BufferedStream` and the call in
`StorageManager.sync` and `syncStrong`, and run the durable-commit runs of
`performance-bufftime.suite` at 20 ms against today's code.


Size and order
--------------

S for the code, S to M with the measurements. After 005-46, which changes
`FileStream.append`, the force that this item paces on. Independent of
005-47, but the measurements should note which durability they ran with.


Prototype
---------

2026-10-27, by Claude (Opus 5.5, Claude Code), in 006-09's W5: the prototype by 12:31,
then the ReclaimReaders failure, the gates, the digests and s1's runs from 14:40. Frans
decided at 12:03 that the change is committed tonight if it passes the gates, keeps the
stream's bytes and measures well. It is one local commit, java/ only, `200aaab` on
`a43058f` in the clone `/Users/f/fl/bench/006-09/gc48`, in `main` as `d8ed1aa`
(the same diff).

* **The change** (010-P3: work in response to a call; no thread, timer or setting).
  `BufferedStream.flushSoon(length)`: if a byte before `length` is still buffered, it
  raises `flushTo` and wakes the consumer, and returns. While a sync waits for buffered
  bytes, the consumer skips its timed wait and flushes, flush after flush; what arrives
  during a force goes out in the next one. `StorageManager.sync(length)` calls it on the
  main stream (rule D1 is `MainConfirmedRule`), `syncStrong(length)` on every stream (rule
  D2 may need a replica), before each wait. The timer stays, as the longest time that
  bytes nobody syncs on stay buffered (`DEFAULT_BUFFER_TIME`'s comment). Locks: a sync
  holds `d1Lock` (`d2Lock`) and takes the stream's monitor; the consumer calls the
  listener, which takes `d1Lock`, after it has left the monitor; so no cycle. A sync that
  comes before its bytes are appended is served at the consumer's next wake, a quarter of
  the buffer time at most: only `StorageManagerTester.testWait2` does that; `Db.sync`
  waits for what `store()` appended.
* **Tests.** `DbTesterStream.testSyncAfterOneCommitWaitsForOneForce` ("Done when": forces
  of a `FileStreamIo` made 50 ms longer, a buffer time of 4 s; the sync after one commit
  takes one force and 50 to 250 ms) and `StorageManagerTester.testSyncStartsTheFlush`
  (sync, and syncStrong with a replica, buffer times of 4 s, each under 1 s). Both fail on
  the code before, where the syncs wait 4 s for the timer. `testWait2` asserted a sync of
  more than 20 ms (the timer); it asserts that the bytes are written when the sync
  returns.
* **ReclaimReaders, a race in the test.** level3.sh failed once at step 5 (seed 16), and 1
  of 15 reruns (seed 22): a reader's get of the latest state reported "model was not
  published through T". The interleaving, at the end of a session:
  1. The writer executes the session's last transaction; T becomes a lookup time.
  2. A reader's get of the latest state reads T; `awaitModel`'s loop condition reads
     `lastCompleted` < T, as the writer is still updating the model.
  3. The writer sets `lastCompleted` (T or later), returns from `session()` and sets
     `stopReaders`: some hundred nanoseconds when the last transaction has no sync after
     it.
  4. The reader, held up between its two reads, reads `stopReaders` and fails, though the
     model is published through T.

  No lookup time that a reader sees in a session is beyond the writer's last publication:
  only `Db.execute` makes lookup times (`DbClock.transactionEnd`), in the writer's thread;
  reclaim's internal transactions (steps, table stores) run inside the user transaction's
  execute (`Reclaim.transactionCompleted`), before it returns; `Db.sync` runs none. So the
  database did nothing wrong (005-57's guess, an internal transaction after the last
  publication, cannot happen). Evidence (the experiment in
  [48-group-commit/runs/reclaimreaders/experiment/](48-group-commit/runs/reclaimreaders/experiment/):
  the instrumented copy as a diff, the scripts, `results.txt`; the run logs were not
  kept): with a pause of 2 ms between the two reads, all 36 seeds
  of level3's three JVMs fail, each in its first or second session with readers, on HEAD
  as on the prototype, each with `lastCompleted`, read again, at or past T; with the fix
  none fails (862 sessions on each, with 902 and 1,086 readers that the second read let
  through). Without the pause, six JVMs at once (level3's three on each build; D in
  `experiment/results.txt`): 3 readers let through by the second read in 27,882 sessions
  on the prototype, all in seeds 13 to 24 like the two failures (3 in 13,500 sessions
  there), none in 8,396 on HEAD (3,500 of seeds 13 to 24, where 0.8 were to be expected);
  never a lookup time beyond the last publication. A first count, with an atomic increment
  between `session()` and `stopReaders`, saw none in 67,700 sessions: the window is that
  narrow. The same failure came without group commit in 005-57 (level4.sh quick, 8
  readers, seed 302, on `c1f1f15`). The fix, in the same commit: `awaitModel` reads
  `lastCompleted` again after it has seen `stopReaders` (or a failure) and fails only if T
  is still not published, so it still finds a lookup time beyond the last publication.
  With it, 101 runs of step 5's JVMs (1,212 seeds) at level3's load, 0 failures.
* **Gates**, on `200aaab`'s tree: `before-commit.sh` "BEFORE COMMIT OK (120 s)" (1,046
  unit tests, 73 f-tests); `level3.sh` (full) "LEVEL 3 OK", step 5 with 0 failures in its
  36 seeds.
* **StreamDigest** (P2), [48-group-commit/tools/digest.sh](48-group-commit/tools/digest.sh)
  (the outputs were not kept): `StreamDigest all` (12
  configurations; modes plain, reads, restarts) "DIGESTS IDENTICAL (36 of 36)", HEAD
  against the change. With syncs (`tools/SyncDigest.java`: a sync after every 7th
  transaction and a thread that syncs in a loop, the path that the change moves): each
  build gives the stream of mode plain, and HEAD against the change "DIGESTS IDENTICAL (12
  of 12)", firstPos included (and the runs with syncs were 13 to 150 times faster with the
  change).
* **s1** (question 1 and 2; `night/run-s1.sh`, 14:52 to 15:12, the jars of `head-e718347`
  and `proto-e718347`, 6 runs of each, in turns, heap 1 GB; a force of 4 KB took 4.0 ms at
  the median, 005-13's ForceProbe). Durable commits, a sync after each transaction, 20 ms:

  | threads | commits/s, HEAD | change | sync p50 ms | p99 ms | forces/s |
  |---:|---:|---:|---|---|---|
  | 1 | 38 | 213 | 24.8 to 3.8 | 44.6 to 20.6 | 38 to 213 |
  | 4 | 149 | 453 | 25.3 to 7.7 | 51.5 to 30.5 | 37 to 222 |
  | 16 | 603 | 1,758 | 25.2 to 8.0 | 45.6 to 26.0 | 38 to 221 |
  | 64 | 2,364 | 6,429 | 25.4 to 8.2 | 44.2 to 28.6 | 38 to 208 |

  With the change the disk forces about 95 percent of the time (213 forces of 4.5 ms a
  second): the force paces the groups, 31 commits a force at 64 threads. Writers that do
  not sync (question 2): puts a second 160,961 and 163,686 (100-byte values), 78,566 and
  80,507 (1 KB), 89,598 and 90,534 (1 KB, 100 puts a transaction; heap 2 GB, as HEAD's
  first run ran out of a 1 GB heap); forces a second and bytes a force the same (29.9 and
  29.8, 42.1 and 43.2, 45.1 and 45.1). Tables:
  [night/out/s1/table.md](48-group-commit/night/out/s1/table.md) and
  [night/out/s1-x100/table.md](48-group-commit/night/out/s1-x100/table.md); the raw
  outputs were not kept.
* **F53**: `night/run-f53.sh` (HEAD against the change in turns, 10 runs of each, the same
  suite at 20 ms, heap 8 GB; about 45 minutes) did not run, see below.
* **Questions.** 1 and 2: s1's answers above. On s1 a short wait before the flush
  (question 3) looks unneeded: under load the disk forces nearly all the time, and the
  group forms during the force.


The F53 runs did not run: in 006-09's quiet block at 00:57, `performance.sh`
found the machine not quiet (89.2 percent idle) and refused, by its own
check; s1's runs stand.


Outcome
-------

2026-10-28, closed by Frans: "Close, keep 20 ms as recommended. Commit.
And also: create a new 005 item to investigate 20 ms vs 50 ms, vs 100 ms."

* Group commit is in `main` since 2026-10-27 (`d8ed1aa`): a sync that
  waits has the buffer written at once (`BufferedStream.flushSoon`), and
  the force paces the groups. On s1 one thread's durable commits went from
  38 to 213 a second (the sync's median from 24.8 to 3.8 ms), 64 threads'
  from 2,364 to 6,429; writers that do not sync are unchanged; the stream's
  bytes are unchanged (StreamDigest). The gates, `level3.sh` and `night.sh`
  (2026-10-28) pass with it.
* Question 4: the buffer time stays 20 ms. Whether 50 or 100 ms is better
  now that a sync does not wait for it is investigated in
  [005-64](64-buffer-time-after-group-commit.md), with question 5 (the
  replica's 2,000 ms).
* Questions 1 and 2 are answered on s1; F53's runs were refused by
  `performance.sh`'s quiet check and are not a condition any more; 005-64
  measures on F53. Question 3: no wait before the flush (s1: the group
  forms during the force). Question 6: since 005-46 a reader does not wait
  for the force; 005-47 is its own entry.
* Files kept in [48-group-commit/](48-group-commit/): the scripts of the
  runs (`night/`), the two tables, the tools (`tools/`) and the
  ReclaimReaders experiment; the test runs' raw outputs and the prototype's
  diff (the same as `d8ed1aa`) were removed on 2026-10-28.
