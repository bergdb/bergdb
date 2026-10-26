005-51. Eviction only in response to the calls
==============================================

Status: open. Kind: fix. Created 2026-10-26.

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
