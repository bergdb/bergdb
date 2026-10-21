005-14. Calm when idle: the storage thread's timer
===================================================

Status: done (2026-10-21; see Outcome). Kind: decide. Created 2026-10-21.


The task
--------

In Frans's words (2026-10-21), after 005-13 set the default buffer time
to 20 ms: "I did not consider CPU load, power. It is a bit ugly to have a
thread running all the time and waking up that often. I would like the
database to be 'calm' when not used. And consuming insignificant CPU
resources. Please have a look at how 20 vs 50 vs 100 ms affects this. On
this computer."


How it works today
------------------

* Each stream's `BufferedStream` has a consumer thread that waits
  bufferTime / 4 at a time (`wait(waitTime)`), also when nothing is
  buffered: four wakes per buffer time, as long as the database is open.
  `Object.wait` on this macOS sleeps longer than asked (wait(5) 7.6 ms,
  005-13), so at 20 ms the consumer wakes about 130 times a second.
* Nothing else in an idle database wakes. No other thread of BergDB has a
  timer: `Jmx.Speed`'s one-second thread is started by manual tests only,
  and the index and replica threads run only while they work. A replica's
  consumer (2000 ms) wakes twice a second.


Measured
--------

F53 (M1 Pro, macOS 27), 2026-10-21, commit fdee608. One process at a
time: a JVM with the JDK's defaults (G1) that opens a database on a
FileStream, writes 1000 small transactions, syncs, and then does nothing
([tools/IdleProbe.java](14-calm-when-idle/tools/IdleProbe.java)). From 16 s
after the writes, the kernel's counters of the process over 60 s
(`proc_pid_rusage`, [tools/procstat.c](14-calm-when-idle/tools/procstat.c)):
interrupt wakeups, CPU time, and the energy that the kernel attributes to
the process (`ri_energy_nj`: an estimate of its model, not a power meter).
Two rounds on a quiet machine, medians; all of it in
[14-calm-when-idle/table.md](14-calm-when-idle/table.md):

| idle process | wakeups/s | CPU ms/s | of it, the consumer | energy, uW |
|---|---:|---:|---:|---:|
| JVM only, no database | 25 | 1.3 | - | 45 |
| database, 100 ms | 56 | 2.2 | 1.0 | 76 |
| database, 50 ms | 85 | 2.9 | 1.8 | 107 |
| database, 20 ms (today's default) | 163 | 4.4 | 3.3 | 182 |
| database, 20 ms, the consumer sleeps when idle (prototype, below) | 25 | 1.3 | 0 | 44 |

* Three earlier rounds (`runs-busy/`) began while Photos analysis
  (`mediaanalysisd`) used a core. In the first, the database at 20 ms
  used 15 ms of CPU a second (1.5 percent of a core), 186 wakeups and
  360 uW; the third matched the quiet rounds.
* For comparison, in the same windows: Finder and the Dock 0 wakeups a
  second, VS Code's main process 2 (25 uW), and VS Code's Java language
  server, an idle JVM with the parallel collector, 6 (6 uW).

**What it shows.**

* The cost is per wake: about 25 to 35 us of CPU, mostly on the
  efficiency cores, and about 1 uJ. 100 ms adds 31 wakes a second to the
  JVM's own 25, 50 ms adds 60, 20 ms adds 138.
* In absolute terms it is small: at 20 ms, 0.3 percent of one core and
  0.14 mW, on a laptop that idles at watts.
* It is not calm. At 20 ms an idle database wakes 6.5 times as often as
  the JVM it runs in and has 4 times its idle energy; at 100 ms, 2.2 and
  1.7 times. On a small device, a timer that fires every few ms may also
  keep the CPU out of its deeper sleep states (not measured here).
* No buffer time makes it calm: the timer runs while nothing happens.


The prototype: the consumer sleeps when idle
--------------------------------------------

[tools/idle-consumer.patch](14-calm-when-idle/tools/idle-consumer.patch),
13 lines in `BufferedStream`:

* When nothing has been buffered for a whole buffer time, the consumer
  waits without a timeout. `append()` wakes it (only when it is idle, so
  once per idle period); `stop()` and `close()` wake it too.
* While data arrives, nothing changes: the same timer and the same
  flushes. The consumer goes to sleep one buffer time after the last
  flush.
* An idle database then costs nothing measurable beyond the JVM: 25
  wakeups a second, 1.3 ms of CPU and 44 uW, as the JVM alone, at any
  buffer time.
* A commit and a sync after an idle second, 30 times at 20 ms
  ([tools/SporadicProbe.java](14-calm-when-idle/tools/SporadicProbe.java),
  [runs-sporadic.txt](14-calm-when-idle/runs-sporadic.txt)): p50 15.6 ms,
  max 23.8 ms, against 14.2 and 23.2 ms today. The first flush after an
  idle period comes one wait (about 7.6 ms) after the append; today it
  comes 0 to one wait after. `close()` ends the consumer, with the patch
  as without it. The unit tests pass (934).

**Found on the way: a latent fault.** `waitCount` is an int, and today it
counts every wake while nothing is written. After 2^31 wakes it is
negative, and the timer flushes nothing until it is positive again, as
long again; a sync then waits until 2.5 MB are buffered. At 20 ms that is
190 days without a write (2.2 years at 100 ms, the default before 005-13).
With the prototype the count stops at 4 when idle; without it, a count
that stops at `waitsBeforeFlush` is a one-line fix.


Proposal
--------

Take the prototype as a fix and keep 20 ms. Its tests: unit tests in
`BufferedStream`, that the consumer of a stream with nothing buffered for
a buffer time is `WAITING` (not `TIMED_WAITING`), that an append to an
idle stream is flushed within about one wait, and that `stop()` and
`close()` end an idle consumer; `java/before-commit.sh`; and 005-13's
suite at 20 ms (`d-t1`, `d-t64`, `a-1k`), to show no change under load.

Without a change to the code, 100 ms is the calmest of the three (31
wakes a second more than the JVM) at 122 ms per sync; 50 ms is between.


Done when
---------

Frans has decided. If the fix goes in: its unit tests,
`java/before-commit.sh` printing `BEFORE COMMIT OK`, the suite's results
recorded here, and docs/levels.md saying that an idle database does not
wake.


Size and order
--------------

S. Any time; it changes `BufferedStream` only.


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code), at Frans's request ("OK, do
005-14 as proposed. Also fix the overflow problem."). Three changes in
`BufferedStream`; the buffer time stays 20 ms.

1. **The consumer sleeps when idle**, as in the prototype. When nothing
   has been buffered for a whole buffer time, it waits without a timeout
   until `append()`, `stop()` or `close()` wakes it (the field `idle`, and
   `notifyAll()` in the three). After `stop()` it ends at once.
2. **The wake count stops at 4.** `waitCount++` became `if (waitCount <
   waitsBeforeFlush) waitCount++`. What reads the count asks only whether
   it has reached `waitsBeforeFlush` (4), so nothing else changes, and the
   overflow cannot happen.
3. **No flush when nothing is buffered, also when closing.** Found while
   making the change. `close()` sets `flushAndClose` before it stops the
   consumer. A consumer that woke in between, with nothing buffered,
   flushed 0 bytes, and for 0 bytes `flushToStream()` appended the whole
   ring buffer (index2 is then index1 - 1): stale bytes after the last
   transaction, 10 MB for the main stream. A database with them fails to
   start ("Bad transaction size",
   [garbage-tail.txt](14-calm-when-idle/garbage-tail.txt)). In a test of
   `BufferedStream` alone at a buffer time of 10 ms, 34 of 24,000 closes
   did it before the fix and 0 of 12,000 after
   ([close-race.txt](14-calm-when-idle/close-race.txt),
   [tools/CloseRace.java](14-calm-when-idle/tools/CloseRace.java)). The
   chance per close goes with the time that `close()` holds the lock over
   the length of one wait, so 005-13's 20 ms made it about 4 times as
   likely as 100 ms. Now `shouldFlush()` is true only when something is
   buffered, and `flushToStream()` asserts more than 0 bytes. A database
   that already has such bytes is not repaired by this.

**Tests.** Four unit tests in `BufferedStream`, each failing on fdee608
and passing with the change: `testIdleConsumerWaitsForAppend`,
`testStopAndCloseEndIdleConsumer`, `testWaitCountStaysSmall` (a count of
21 after 50 ms before the fix) and `testNoFlushOfNothingWhenClosing`.
`java/before-commit.sh` printed `BEFORE COMMIT OK`: 938 unit tests and 59
f-tests ([before-commit.txt](14-calm-when-idle/before-commit.txt)).

**Under load, no change.** [tools/load-check.suite](14-calm-when-idle/tools/load-check.suite)
at 20 ms, fdee608 against the fix, the two builds alternating, three
rounds each (`runs-load/`); medians, with the range where it matters:

| scenario | before the fix | with the fix |
|---|---:|---:|
| 1 thread, a sync after each commit | 33 commits/s, p50 30.0 ms | 34 commits/s, p50 30.0 ms |
| 64 threads, a sync after each commit | 2,099 commits/s, p50 30.1 ms | 2,097 commits/s, p50 30.1 ms |
| no sync, 1 KB values | 102,766 puts/s (98,912 to 104,175) | 100,470 puts/s (99,000 to 101,701) |

**Idle, with the fix** (`runs-final/`, two rounds of 60 s; VS Code was in
use, so every process's energy is higher than in `runs-quiet/`):

| idle process | wakeups/s | CPU ms/s | energy, uW |
|---|---:|---:|---:|
| JVM only, no database | 26 | 1.4 | 98 |
| database, 20 ms, before the fix | 187 | 5.4 | 422 |
| database, 20 ms, with the fix | 26 | 1.4 | 103 |
| database, 100 ms, with the fix | 26 | 1.4 | 66 |

An idle database now costs what the JVM costs, at any buffer time. A
commit and a sync after an idle second take p50 14.5 ms against 12.8 ms
before ([runs-sporadic.txt](14-calm-when-idle/runs-sporadic.txt)): the
first flush after an idle period comes one wait after the append.

docs/levels.md says that an idle database does not wake, and lists the
two faults with the others found in `BufferedStream`; docs/log.md has an
entry. The change in `java/` is left for Frans to commit.
