005-51. Eviction only in response to the calls
==============================================

Status: done (2026-10-27; see Outcome). Kind: fix. Created 2026-10-26.

Found in [010-01](../010-principles/01-principles.md), 010-P3 ("Calm when
not used"), by Claude (Opus 5.5, Claude Code); registered at Frans's request
(2026-10-26: "Yes, register it. We likely want to change this so eviction
happens in response to user API calls.").


The issue
---------

The eviction thread, `bergdb-evictor` (item 009, decision T5a), wakes once
a second for as long as the database is open, also when nothing uses it.
When idle it waits with a timeout, `evictorLock.wait(1000)` in
`Eviction.EvictorRun`, to see whether the database has stopped
(`in.isActive()`); nothing else wakes it then: `Db.stop()` does not notify
`evictorLock`. Each wake-up is work that nothing in the application asked
for, against 010-P3: a database that is not used consumes no resources besides
memory, and BergDB does no sporadic actions (Frans's reasons in 010-01:
BergDB is a library and does not know what the application does;
maintenance outside the calls is the application's to start, visibly;
tests and determinism).

The rest of eviction already follows the calls (009, step 3d):

* A commit's end runs a batch under the write lock
  (`Eviction.afterTransaction`, `sweep()`, at most `BATCH_NANOS`, 2 ms),
  and wakes the thread if the resident bytes are still over the trigger.
* A reader's load wakes the thread (`afterLoad`) and waits for its batch
  at most `LOAD_WAIT_NANOS` (2 ms). A reader never takes the write lock,
  which a batch needs; that is why the thread exists.
* Woken, the thread runs batches until the resident bytes are at most the
  trigger, or a batch frees nothing, and waits again.


The scope
---------

Eviction runs only in response to the application's calls: no timer, no
wake-up of its own. A thread is fine (Frans, 010-P3: "Eviction can be
run on its own thread with its work triggered by user API calls."), as
long as 010-P1 holds for the calls (a worst case of about 20 ms) and the work
a call triggers is limited (010-P4).


Questions
---------

1. The idle wait. A wait without a timeout, which `stop()` and `close()`
   wake (`notifyAll()` on `evictorLock`), as `BufferedStream`'s consumer
   does since 005-14. Or the thread ends when it has nothing to do, and the
   next `wake()` starts a new one (`wake()` starts one already if there is
   none). Which is simpler and safe against a stop that races a wake?
2. The work one call triggers. Woken, the thread batches until the
   resident bytes are below the trigger, which, after many loads by
   readers, can be many batches. Is that "limited" in 010-P4's sense, or
   should a wake buy a bounded number of batches, the rest left to the
   next calls?
3. Eviction in the calls themselves, without the thread. A commit does
   that already; a reader cannot (no write lock). Worth it only if it
   keeps 010-P1 and the read performance of 009-03; probably not part of this
   entry.


Done when
---------

* An open, idle database's eviction thread does not wake: no wake-ups of
  BergDB's own threads over a minute idle, after loads and commits that
  started the thread (a test, or the per-process wake-ups of 005-14's
  measurement, `proc_pid_rusage`).
* `stop()` and `close()` end the thread at once, not within a second.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `level4.sh` passes,
  as a change to Level 4's mechanism.


First step
----------

Read `Eviction.EvictorRun`, `wake()` and the stop path of `Db`, and answer
question 1.


Size and order
--------------

S for question 1: about 10 lines in `Eviction` and `Db.stop()`, and a
test. Questions 2 and 3 may grow it.


Outcome
-------

2026-10-27, by Claude (Opus 5.5, Claude Code), at Frans's request ("yes,
put it in java and commit."; 006-09, W4), in a clone on `e773562`.

* Question 1: a wait with no timeout. `Eviction.EvictorRun` waits for the
  next request with `evictorLock.wait()`. The database's close wakes it:
  `Db.closeStorage()`, which `stop()`'s closing thread, `close()` and a
  failed start run, calls the new `Eviction.endThread(wait)` once the
  state is `STOPPING` and a running transaction has ended. It wakes the
  thread, which sees that the database is no longer active and ends, and
  waits until it has ended; only wakes it when the close runs inside a
  transaction, as a batch takes the write lock that the close then holds.
  So `close()` returns after the thread has ended, also after `stop()`.
  No wake-up is lost: the thread reads the state under `evictorLock`
  before each wait, and the close sets the state before it takes that
  lock. The other option, a thread that ends when it has nothing to do,
  would start a thread for each burst of loads; one thread a database is
  009's decision T5a.
* Question 2: what one wake buys is limited, as 010-P4 asks, and nothing
  changed. Each batch ends after at most `BATCH_NANOS` (2 ms) under the
  write lock, a writer that waits goes first, and the batches stop when
  the resident bytes are at most the trigger or a batch frees nothing.
  Their sum follows the bytes that the calls loaded.
* Question 3: not done, as the scope says.
* The test, `Eviction.testEvictionThreadIdleUntilClose` (unit, about 0.1
  s): loads start the thread under a small budget; idle, the thread must
  be in `Thread.State.WAITING`, a wait with no timeout, and `close()`, with
  and without `stop()` first, returns after it has ended. On the code
  before, it fails: the idle thread was in `TIMED_WAITING`.
* BergDB's other threads, read for the first point of "Done when":
  `BufferedStream`'s consumer waits with no timeout when nothing is
  buffered (005-14); `FileStream-cut` (005-46) ends when nothing is left
  to delete; the JMX monitor (`DBMonitor.MThread`, a sleep of a second)
  runs only when an application starts it (`Jmx.registerAndStart()`). A
  sync waits with `wait(500)` on `StorageManager`'s locks, but only while
  a call waits for durability.
* Measured, the first point of "Done when": an idle database whose
  eviction thread has run wakes no more than the JVM it runs in. 005-14's
  method ([idle-run.sh](51-eviction-on-calls/idle-run.sh),
  [IdleEvict.java](51-eviction-on-calls/IdleEvict.java), 005-14's
  `procstat`): a database on a `FileStream` with a budget of 2 MB and a
  startup distance of 1 MB, 200,000 puts and a read of every key, which
  start the eviction thread; then 60 s idle, measured after 15 s; two
  rounds each, on F53 with other work running, 2026-10-27, 12:27 to
  12:35 ([out/](51-eviction-on-calls/out/)):

  | process | wakeups/s | CPU ms/s | energy, uW | the eviction thread, idle | its CPU in 60 s |
  |---|---|---|---|---|---|
  | the JVM alone | 26.1, 26.2 | 0.54, 0.66 | 469, 473 | none | none |
  | the code before 005-51 (`74bc2dc`) | 26.2, 26.9 | 0.56, 0.73 | 502, 512 | `TIMED_WAITING` | 1.25, 1.63 ms |
  | with 005-51 (`043a09c`) | 23.7, 24.2 | 0.62, 0.60 | 459, 437 | `WAITING` | 0 |

  Before, the eviction thread used about 1.4 ms of CPU a minute, its 60
  wake-ups; after, none. The process counts differ by less than their
  noise: the eviction thread was 1 of about 26 wake-ups a second, most of
  them the JVM's own.
* `before-commit.sh` prints `BEFORE COMMIT OK` (1,044 unit tests, 73
  f-tests, 128 s), and `level4.sh` in full passes (`LEVEL 4 OK`, 16
  minutes), on `e773562` with the change.
