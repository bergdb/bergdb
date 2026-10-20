005-13. The buffer time: should the default change?
====================================================

Status: done (2026-10-20; see Outcome). Kind: investigate. Created 2026-10-20.


The task
--------

In Frans's words (2026-10-20): the buffering is a careful design, but from
the 2012 era, made for rotating hard drives, where writing in batches about
every 100 ms raised throughput a lot. With SSDs that may no longer be so;
it is worth testing, and 50 ms may be better. sync(STRONG) should seldom be
needed. The question is whether the default should change. Run a sweep
before deciding.

The design stays: `sync(level)` is the general, high-level interface, and
the storage layer defines what a level means, by medium, replication and
so on. The buffer time is a property of a storage (a stream), not of the
database; a storage could be over a network. The flexibility of the
settings and of the implementations is wanted.


How it works today
------------------

* **Where it is set.** Per stream: `StorageManager.Builder.stream(name,
  stream, bufferSize, bufferTime)`, `DbBuilder.stream(...)` with the same
  parameters, and `addReplica(..., bufferSize, bufferTime)`. Values below
  10 ms become 10 ms. The defaults are in `StorageManager`:
  `DEFAULT_BUFFER_TIME = 100` (main) and `DEFAULT_REPLICA_BUFFER_TIME =
  2000`. The Pub API's `DatabaseBuilder` (`dir()`, `replica()`) does not
  take a buffer time; it uses 100 ms, also for a replica added by the
  builder, where `Database.addReplica` uses 2000 ms.
* **The flush rule** (`BufferedStream`). The consumer thread wakes every
  bufferTime / 4 (25 ms). It flushes when the buffer holds at least 25
  percent of its capacity (2.5 MB of 10 MB), or when four wakes have
  passed since the last flush and there is data. Each flush appends to the
  underlying stream, and `FileStream.append` forces the file
  (`F_FULLFSYNC` on macOS, fsync on Linux; docs/level3-durability.md).
  Nothing wakes the consumer when data is appended or when a sync waits.
* **What a sync waits for.** `sync(ORDINARY)` waits until the main
  storage has confirmed the position (`MainConfirmedRule`, D1);
  `sync(STRONG)` also until one active replica has, if there is one
  (`OneActiveReplicaRule`, D2). Both wait for the buffered flush; neither
  flushes at once.
* **The latency this gives.** The wake count keeps counting while the
  database is idle, so the first sync after an idle period waits 0 to
  25 ms, plus the force. A sync that follows a flush waits about 100 ms:
  one thread that syncs after each transaction gets 9 transactions a
  second, 116 ms each (docs/levels.md, "Durable commits").
* **Like Nagle's algorithm**, as the class's Javadoc says: latency traded
  for throughput. One difference: Nagle is clocked by the network (send at
  once when nothing is unacknowledged, else wait for the ACK), not by a
  timer. A flush that starts when someone waits, and collects what arrives
  during the force before it, is that same rule; today's timer is closer to
  a fixed delay.
* **An old data point that does not hold.** A sync that flushed at once
  (tried and reverted on 2026-10-13) gave 13,000 to 18,000 synced
  transactions a second, p50 47 us. That source wrote with `"rws"`, without
  `F_FULLFSYNC` (docs/levels.md, Reclaim c), so it measured a write
  through the OS, not to the device. It must be measured again on today's
  source.


Questions
---------

1. On today's source and machine (F53, SSD, `F_FULLFSYNC`), what do the
   durable commits cost as a function of the buffer time: throughput and
   p50/p99 sync latency, with 1, 4, 16 and 64 threads that sync after
   each transaction?
2. What does a shorter buffer time cost writers that do not sync: bulk
   throughput, bytes per force, forces per second?
3. What does one force cost on this machine (`F_FULLFSYNC` of a small
   append), the floor of any sync?
4. Should the default change (50 ms, or less), and should the Pub API's
   builder take a buffer time per storage?
5. Should a waiting sync start the flush (group commit, below), and does
   the timer then stay as the longest time unsynced data is buffered?


Proposal
--------

**First a sweep, with no change to production Java.** `Perf` already has
durable commits (`commit=durable threads=N`, suites `d-1k-t1`, `d-1k-t16`,
`d-1k-t64`) and builds its database with `Db.builder().stream("main",
stream)`. Give `Perf` a parameter `bufftime=` that passes a buffer time to
`DbBuilder.stream(name, stream, bufferSize, bufferTime)`, and a suite
`performance-bufftime.suite`:

* buffer times 10, 25, 50, 100 (today) and 200 ms;
* durable writes, 1 KB values, threads 1, 4, 16, 64: commits a second,
  sync p50, p99, max;
* append-only writes (no sync), 100-byte and 1 KB values, one thread:
  commits a second, and forces a second with bytes per force (a counter
  in the run, or `FlushOrderProbe`'s trace);
* a probe of the force alone: N small appends to a `FileStream`, each
  forced, for the time of one `F_FULLFSYNC`.

Run it in the background and stay idle (bench-session noise), three
repeats, results and the table in a folder `13-buffer-time/`. The floor of
10 ms means the sweep cannot try "flush at once"; question 5's prototype
can.

**Then, likely, group commit**, if the sweep shows what is expected
(latency set by the timer at low load, a force cheap enough on the SSD):

* `StorageManager.sync(pos)` and `syncStrong(pos)`, before they wait,
  wake the consumers of the streams their rule needs (a call on
  `BufferedStream`, say `flushSoon()`, that sets a flag and notifies).
* The consumer flushes when the flag is set, as when four wakes have
  passed. While it forces, new transactions collect in the buffer, and
  the next flush takes them all: under load, the batches come from the
  forces themselves, not from the timer.
* The timer stays, as the longest time that data nobody syncs on is
  buffered; its default can then be longer or shorter on its own merits.
* `sync()` and the sync levels do not change; what a level means stays
  the storage's (the rules), and a stream over a network or a slow
  medium keeps its own buffer time.
* Prototype it on a scratch clone and run the same suite against it, as
  a fifth column.

**And the default.** If group commit goes in, the default buffer time
matters little for syncs; keep 100 ms or take the sweep's best for
append-only throughput. If it does not, take the sweep's choice
(probably 25 or 50 ms). Separately, a buffer time per storage in the Pub
API's builder (`dir(dir, bufferTime)` or a storage options object), and
the 100 / 2000 ms mismatch for replicas made by the builder, are small
API decisions for Frans, best with 005-05 and 005-11.


Done when
---------

The sweep's table is in `13-buffer-time/` with a recommendation, and Frans
has decided: the default, group commit or not, the Pub API. Any change to
`java/` (production code, `Perf` or a suite) needs `java/before-commit.sh`
to print `BEFORE COMMIT OK` (the unit tests and the f-tests) before it is
committed. As performance work, this task also needs the performance
tests: the sweep's suite for the results, and for a change to production
Java (`java/src`) the suite run again on the changed code, its results
then recorded here.


First step
----------

Add `bufftime=` to `Perf` on a scratch clone, and run `d-1k-t1` with 10,
50 and 100 ms to see that the parameter takes effect (sync p50 near the
buffer time).


Size and order
--------------

S for the sweep; M with the group-commit prototype and its tests.
Related to 005-07 (synchronization of transactions; group commit is on
its list of what may need to change) and to 005-11 (replicas, D2). The
sweep can go any time; the group commit is best after or with 005-07.


Outcome
-------

2026-10-20, by Claude (Opus 5.5, Claude Code), at Frans's request. The
sweep was run as proposed. Frans then decided (2026-10-20): "keep this very
simple. Just set the default to 20 ms unless you find a good reason for
not to." No such reason was found. `StorageManager.DEFAULT_BUFFER_TIME` is
20 (was 100); `BufferedStream(stream)` takes the same defaults. Group
commit, a buffer time in the Pub API's builder and the replicas' 2000 ms
are not done. A redesign of the storage for SSDs and flash, which would
need disk performance on several targets, embedded included, is out of
scope (Frans).

**The sweep.** On F53 (M1 Pro, SSD, macOS), commit 9d909cc, three rounds of
[performance-bufftime.suite](../../java/stress/performance-bufftime.suite),
each with every buffer time, 12:30 to 13:22. Round 1 began while another
session's night run had two Lean checks running (78 percent idle; the
runs are marked not quiet); rounds 2 and 3 were quiet. Medians of the three
rounds, the full table in [13-buffer-time/table.md](13-buffer-time/table.md):

| buffer time | sync p50, 1 thread | synced commits/s, 1 / 16 / 64 threads | puts/s, no sync, 100 B / 1 KB / 1 KB x100 |
|---:|---:|---:|---:|
| 10 ms | 15 ms | 66 / 1,035 / 4,141 | 267k / 104k / 111k |
| 25 ms | 35 ms | 29 / 458 / 1,815 | 262k / 101k / 109k |
| 50 ms | 64 ms | 16 / 250 / 995 | 259k / 98k / 109k |
| 100 ms (was the default) | 122 ms | 8 / 132 / 528 | 266k / 98k / 104k |
| 200 ms | 221 ms | 5 / 72 / 289 | 261k / 62k / 64k |
| **20 ms (the new default)** | **35 ms** | **29 / 456 / 1,813** | **271k / 105k / 112k** |

The last row is the changed code with the default (no `bufftime=`), on
4b459df: [default-check.suite](13-buffer-time/tools/default-check.suite),
three runs each, in `13-buffer-time/runs/default20/` (86 percent idle, so
marked not quiet).

**What it shows.**

* Synced commits: a sync waits for the timer, so the latency is the
  buffer time plus 20 to 50 percent, and the commits a second of N
  threads are N over that. 20 ms gives 4 times the synced commits of
  100 ms at every thread count.
* Writers that do not sync: 260,000 puts a second with 100-byte values
  and about 100,000 (100 MB/s of user data) with 1 KB values, the same
  from 10 to 100 ms; the writer's CPU is the limit, not the forces. 100
  puts per transaction add 7 percent. A shorter buffer time costs no
  throughput; 20 ms is as fast as 10 and slightly faster than 100.
* One force (question 3, [tools/ForceProbe.java](13-buffer-time/tools/ForceProbe.java),
  `runs/forceprobe-*.txt`): `F_FULLFSYNC` of 100 bytes 4.2 to 5.2 ms, of
  1 to 4 MB 7 to 12 ms (p50); plain fsync, which on macOS does not empty
  the drive's cache, 0.03 ms. So about 5 ms is the floor of any durable
  sync here, and a 20 ms timer is still four forces long.
* At 200 ms, bulk writes of 1 KB values lose 37 percent (62,000 puts a
  second): the consumer wakes only on its timer (every 50 ms) and flushes
  at most half the 10 MB buffer, so the buffer fills and the writer waits.
  Nothing wakes the consumer when the buffer is full. Not fixed; it does
  not matter at 20 ms.
* 20 ms gives the same latency as 25 ms (35 ms). The consumer waits
  bufferTime / 4 four times, and `Object.wait(ms)` on this macOS sleeps
  longer than asked: wait(5) 7.6 ms, wait(6) 9 ms, wait(25) 32 to 34 ms
  ([tools/WaitProbe.java](13-buffer-time/tools/WaitProbe.java),
  `runs/waitprobe.txt`). The buffer time is a rough bound, not a
  deadline.

**Why not shorter, or a reason against 20 ms.** None strong enough. The
costs of a shorter time are more forces of small appends when data
trickles in (at most about 30 a second at 20 ms, against 8 at 100 ms;
more writes to flash, which matters for the out-of-scope storage design)
and a consumer thread that wakes every 5 ms instead of 25 ms, also when
the database is idle (power, on a laptop or a small device). Neither was
measured as a problem. A side effect: unit tests that sync wait less
(006-03 found syncs waiting for the poll).

**Tests.** `java/before-commit.sh` printed `BEFORE COMMIT OK` (933 unit
tests, 59 f-tests) on the changed code. The performance tests for the
change: the default check above.

**Files.** In [13-buffer-time/](13-buffer-time/): `table.md` (the sweep's
table, by `tools/table.py`); `tools/run-sweep.sh` (the rounds and the force
probes), `tools/ForceProbe.java`, `tools/WaitProbe.java`,
`tools/default-check.suite`; `runs/` (each round's results and runner log,
`sweep.log`, the probes, `default20/`). In `java/`: `Perf`'s `bufftime=`
parameter and force counters (`forces_per_s`, `bytes_per_force`,
`force_ms_mean`, `force_busy_fraction`, also in every other write run),
and `stress/performance-bufftime.suite`.
