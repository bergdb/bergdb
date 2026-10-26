005-48. Group commit: a waiting sync starts the flush
====================================================

Status: open. Kind: investigate. Created 2026-10-26.

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
