005-46. Fix: reads wait for the stream's writer, and interrupts fail the database
=================================================================================

Status: open. Kind: fix. Created 2026-10-26.

Found in item 009's measurements
([009-03](../009-handles/03-measurements.md), sections 4 and 7), by Claude
(Opus 5.5, Claude Code), during Frans's unattended run of 009.

Item 009's target 2 waits for this item (009-01): no get or commit stopped
for more than about 20 ms by BergDB's own code, the collector's pauses not
counted (Frans, 2026-10-27). The waits below are BergDB's own.

Investigated on 2026-10-27 by Claude (Opus 5.5, Claude Code), at Frans's
request ("Investigate this more thouroughly. What is you proposal.
Document your findings. Don't implement it yet, but propose a
solution."): the sections from "Where a read waits" on. The options of the
first version are weighed in "Alternatives". The probes and their output
are in [46-stream-file-lock/](46-stream-file-lock/). No change to `java/`.

Decided by Frans on 2026-10-27, on the investigation's five questions ("1.
as proposed. 2. Yes. 3. Include in this item. 4. Please elaborate in this
one. 5. no, but such conditions are worth noting in test reports."): the
cut's files are deleted on a thread of their own; a failed delete fails
the stream at its next operation; `SalsaStream` is part of this entry, and
so are interrupts, in the section "Interrupts", added the same day by
Claude (Opus 5.5, Claude Code); a writer's wait for room in the write
buffer does not count against item 009's target 2, and the test reports
note it (change 7). One by one in "Decisions".

Implemented on 2026-10-27 by Claude (Opus 5.5, Claude Code), at Frans's
request ("Decision: A. When possible, implement this and commit it."), in
one commit: changes 1 to 7 and their tests, in "Implemented". Still open:
the measurements on s1 and P4's soak of "Done when".


The fault
---------

`FileStream.DbFile.read` and `DbFile.append` are both `synchronized` on the
file, and `append` writes and then forces the file (`io.forceFile`, an
`fsync`) inside that monitor. So a reader that needs a node from the last
file of the stream, the one the writer appends to, waits for the writer's
whole append and its `fsync`.

On F53 an `fsync` is short and it does not show. On s1 (a virtual disk) it
can take seconds: with handles (009, step 3d), where no sweep stops the
readers any more, the pause probe's longest waits on s1 are these, 1.4 to
2.7 s for a get and for the commit beside it, with no collection, safepoint
or eviction batch under them (009-03, section 4). They were there before 009
too, hidden among 2026.1's sweeps of 0.7 to 2.5 s.

It is a stop of its own: every reader that loads from the last file, at any
level of the index, waits for the writer's I/O.


The cut
-------

Added 2026-10-27 by Claude (Opus 5.5, Claude Code), from the soaks of
[009-04](../009-handles/04-shenandoah-degenerated.md), section 7.3: a second
wait of the same kind. `FileStream.pretruncate`, reclaim's physical cut, is
`synchronized` on the stream and deletes the files before the cut one by
one, forcing the directory after each (so that a crash cannot keep an
older file and lose a newer one). Every `FileStream.read` takes the same
monitor to find its file (`findFile`), so every read from the stream waits
for the whole cut.

In P4's soak on F53, the cuts of 11, 2 and 4 files took 88 to 171 ms, 17
to 31 ms and 46 to 96 ms, about 8 to 24 ms a file, and they were the
soak's slowest commits under ZGC and under Shenandoah alike; the longest
gets and scans matched them. On a disk like s1's, where a force can take
seconds, a cut would stop the readers longer.


Where a read waits
------------------

A get or a scan that misses the cache reads from the stream through these
layers, and so does a commit for the index nodes on its path:

| Layer | What it does | The lock it takes |
|---|---|---|
| `RecoverableStream.read` | splits the read at the meta blocks, so a read below is at most 200 KB | none |
| `StorageManager.read` | passes it on | none |
| `BufferedStream.read` | copies what is still in the write buffer; reads the rest below | its monitor, for the copy only |
| `SalsaStream.read`, an encrypted database only | reads below, decrypts | `readLock`, also while it reads below |
| `FileStream.read` | finds the file (`findFile`) | the stream's monitor, to find the file |
| `FileStream.DbFile.read` | `seek` and `readFully` on the file's `RandomAccessFile` | the file's monitor, for the read |

`BufferedStream` asks the stream below only for bytes whose append has
returned, so a read never needs what an append is writing: every wait
below is for a lock, not for data.

The stream's writer is `BufferedStream`'s consumer thread: it writes the
buffer in chunks of up to half of it (5 MB of the default 10 MB), and
waits 5 ms, a quarter of the buffer time, before each. The physical cut
is made by a committing thread. Four waits:

1. **The force.** `DbFile.append` holds the file's monitor while it writes
   the chunk and forces the file. A read of the last file waits for both
   (the fault). Reads of the same file, any file, also wait for each
   other: a `RandomAccessFile` has one file pointer, which `seek` moves.
2. **A new file.** When the last file is full, `FileStream.newFile` holds
   the stream's monitor while it reopens the old file read-only, creates
   the new file, forces it and forces the directory (`openForRw`). Every
   read waits, whatever its file. Not in the first version of this entry.
3. **The cut.** `FileStream.pretruncate` holds the stream's monitor while
   it deletes the files before the cut and forces the directory after
   each: every read waits. It runs on the thread of the commit that makes
   the cut, in `Reclaim.cutIfDurable` at the end of the transaction, under
   the database's write lock: that commit waits for the whole cut, and the
   commits behind it wait for the write lock.
4. **Encryption.** `SalsaStream.read` holds `readLock` while it reads
   below. In an encrypted database every read waits for any other, and for
   whatever that one waits for: a read of any file waits for the force.


What the probes found
---------------------

On `167597a`, today's `java/`, on F53 (M1 Pro, APFS, JDK 27), 2026-10-27,
while another session ran a correctness gate: the probes in
[46-stream-file-lock/](46-stream-file-lock/), run by
[run.sh](46-stream-file-lock/run.sh), their output in
[out/](46-stream-file-lock/out/).

**`StreamWaitProbe`**, a `FileStream` alone, through a `FileStreamIo`
that times the physical operations and can make some of them slower, as a
slow disk would. A writer appends for 10 s; reader "last" reads 100 bytes
at random places in the file the writer appends to, reader "first" in the
first file, which the writer never touches
([stream-wait.txt](46-stream-file-lock/out/stream-wait.txt)):

| The writer | Its appends: count, longest | Reader last: reads over 10 ms, longest | Reader first: reads over 10 ms, longest |
|---|---|---|---|
| 4 KB every 20 ms; a force takes 6.1 ms on average | 320, 30.5 ms | 38, 14.5 ms | 3, 14.6 ms |
| 2.5 MB at a time, without a pause; 50 new files | 165, 144 ms | 150, 19.3 ms | 47, 16.7 ms |
| 4 KB every 20 ms, every 10th force 300 ms slower | 161, 339 ms | 35 (16 over 100 ms), 318 ms | 3, 14.0 ms |
| 1 MB every 50 ms, each new file's directory force 200 ms slower; 28 new files | 50, 1,123 ms | 41 (28 over 100 ms), 220 ms | 28 (28 over 100 ms), 220 ms |
| As the third, through a `SalsaStream` | 163, 323 ms | 34 (17 over 100 ms), 316 ms | 35 (17 over 100 ms), 318 ms |

* A read of the last file waits for the append in progress: in the first
  run 325 of its reads took more than 1 ms, for 320 appends, and in the
  third each of the 16 slow forces stopped it for the whole force.
* A new file stops every read. In the fourth run each of the 28 new files
  stopped both readers for its 200 ms; in the second, the 47 waits over 10
  ms of reader first match the 50 new files, each with two forces, 10 to
  17 ms on F53.
* Through `SalsaStream` the reader of the first file waits as the reader
  of the last one, for every slow force.

A cut of every file but the last two, 57 files of a 300 MB stream, while
the two readers read the two files it keeps:

| | The cut | A delete, a directory force | Both readers' longest read |
|---|---|---|---|
| As is | 309 ms | 0.3 ms, 5.1 ms | 309 ms |
| Each directory force 100 ms slower | 6,059 ms | 0.3 ms, 106 ms | 6,059 ms |

Every read waits for the whole cut. A directory force takes about 5 ms on
F53, and the files here are small, so a delete is quick; in P4's soak the
deleted files were 210 MB on average, and each took 8 to 24 ms (009-04,
section 7.3).

**`SlowForceProbe`**, 009's pause probe (`java/stress/PauseProbe.java`:
1M keys of 100 bytes, a 20 MB budget, two readers, 20 s a phase; ZGC) on a
`FileStream` whose every 100th force takes 1 s more
([slow-force-1000.txt](46-stream-file-lock/out/slow-force-1000.txt); the
same without, [slow-force-0.txt](46-stream-file-lock/out/slow-force-0.txt)):

| Phase | Longest get | Longest commit | Without the slower forces: get, commit |
|---|---|---|---|
| 1 put a transaction | 1,012.9 ms | 1,012.9 ms | 26.5 ms, 26.3 ms |
| 1,000 puts a transaction | 1,022.8 ms | 1,040.0 ms | 51.4 ms, 147.0 ms |

Each of the ten slow forces of the two phases stopped the writer: a
commit of about 1 s ended 8 to 20 ms after each force. The longest gets
come in pairs, one per reader, at the same moments. The force at uptime
12.858 to 13.863 s, for one: gets of 1,012.9 and 1,012.3 ms and a commit
of 1,012.9 ms, all ended at 13.870 to 13.871 s. That is s1's pattern at
step 3d (009-03, section 4; the outputs `jar-3d2-*.txt` in
[s1-probe/](../009-handles/03-measurements/s1-probe/)): with transactions
of 1,000 puts, both readers' longest gets and the longest commit ended
together, 2,695.7, 2,691.3 and 2,720.9 ms at uptime 72.88 to 72.91 s under
G1, and 1,363.0, 1,363.0 and 1,416.5 ms at 122.09 to 122.14 s under ZGC,
with no collection or batch under them. So those waits were, most likely,
forces of 1.4 to 2.7 s on s1's disk. A single-put commit waits as a get
does, most likely when it loads an index node of its path from the last
file, where the recent ones are.

**`ReadPathProbe`**, the JDK and the file system alone, without BergDB
([read-path.txt](46-stream-file-lock/out/read-path.txt)):

* A writer appends to a file and forces it (`force(true)`, `F_FULLFSYNC`)
  under its monitor, as `DbFile.append` does, 5 ms apart, as the consumer
  does. A reader under the same monitor, today's way, waits for every
  append: with appends of 4 KB, 815 reads over 1 ms for 814 appends, the
  longest 17.8 ms; with 2.5 MB, 316 reads over 10 ms, the longest 21.6 ms.
  A reader with positional reads (`FileChannel.read(buffer, position)`, a
  `pread`) on a channel of its own: with 4 KB, 2 reads over 5 ms, the
  longest 8.4 ms; with 2.5 MB, 180 over 5 ms and 2 over 10 ms, the
  longest 10.0 ms. So APFS does not hold a read of a file for the whole
  force of it; a read waits at most about 10 ms, for part of a write or a
  force of the same file.
* Ten files of 20 MB deleted, the directory forced after each, 52 ms in
  all: a positional read of another file took 0.7 ms at most.
* A positional read by a thread whose interrupt flag is set closes the
  channel (`ClosedByInterruptException`), for every thread: the next read
  by another thread fails (`ClosedChannelException`). A `RandomAccessFile`
  read ignores the flag. Readers that clear the flag before a read and set
  it again after, and that open the channel again and read again when they
  find it closed, made 1,793,474 reads in 2 s while their threads were
  interrupted every 100 µs: the channel was reopened 13,755 times, no read
  failed, and each of the 1,018 reads by a thread whose flag was set left
  it set.
* Random reads of 4 KB of a 256 MB file in the OS's cache, a second:

  | Threads | 1 | 2 | 4 | 8 |
  |---|---|---|---|---|
  | One `RandomAccessFile` under its monitor (today) | 632,508 | 465,460 | 471,190 | 509,658 |
  | Positional reads on one channel | 861,594 | 1,035,498 | 1,046,007 | 939,541 |
  | A `RandomAccessFile` for each thread | 630,050 | 674,310 | 609,867 | 502,191 |

  One system call a read instead of two (`lseek` and `read`), and no
  lock: 1.4 times today's reads on one thread, about twice with 2 to 8. On
  APFS the reads of one file stop at about a million a second; Linux's
  page cache should take more, to be seen on s1.

**`InterruptCutProbe`**, a database with reclaim on a `FileStream`
(`FileStreamPowerLossTester`'s configuration: a startup distance of 20 KB,
a retention of 2 s on a test clock), whose writer sets its own interrupt
flag before each commit and clears it after
([interrupt-db.txt](46-stream-file-lock/out/interrupt-db.txt)):

* The commit that made the first physical cut, the 197th, failed the
  database: `ClosedByInterruptException` from
  `FileStreamIo.forceDirectory`, in `FileStream.pretruncate`, in
  `Reclaim.cutIfDurable`. Every later commit and get threw
  `DbFailedException`. Without the interrupts, the same commit cut the
  stream and the database went on.
* With a write buffer of 100 KB (`DbBuilder.testSetup`'s) and no syncs,
  the writer filled the buffer, and the 82nd commit failed the database:
  "Thread interrupted while appending." (`BufferedStream.append`).


Found on the way
----------------

1. **A new file stops every read**: the second of the four waits above,
   of the same kind as the two of the first version. How often depends on
   the files' sizes, which follow the stream's: a new file is at most a
   quarter of the stream kept (`determineFileSizeIndex`), so a stream of
   300 MB gets a new file every 20 MB written, one of 10 GB every 2 GB.
   Each costs two forces: 10 to 17 ms on F53, maybe seconds on s1.
2. **A commit by an interrupted thread that makes a physical cut fails
   the database.** `FileStreamIo.forceDirectory` forces the directory
   through a `FileChannel`, and a channel closes itself when the thread
   that uses it has its interrupt flag set; `pretruncate` keeps the
   `ClosedByInterruptException` as the stream's failure, after it has
   deleted one file and before it moved the first position, and every
   later read, append and `close()` throws it (`StreamWaitProbe
   interrupt`). The cut runs on the committing thread, an application
   thread: the probe's database failed at its first cut. The fix below
   moves the cut's I/O to a thread of BergDB's own.
3. **A commit by an interrupted thread that waits for room in the write
   buffer fails the database too**: `BufferedStream.append` turns the
   `InterruptedException` into an `IOException`, and
   `StorageManager.append` takes any `IOException` of the main stream as
   its failure. With point 2, part of the section "Interrupts" (decision
   4), which has the other calls an interrupt breaks.
4. **Encrypted databases read one at a time** (the fourth wait): no two
   reads of an encrypted database run at once, whatever their files.
5. **The reads of one file wait for each other**, on its monitor, and
   every read takes the stream's monitor too (`findFile`). In the table
   above today's way reads less with more threads.


The fix, proposed
-----------------

No read takes a lock that the writer holds during I/O, and the writer's
I/O, and its order on disk, stay as they are: four changes in
`FileStream`, one in `SalsaStream`. Then the interrupts (change 6) and the
test reports (change 7).

1. **Positional reads, without a lock.** Each file (`DbFile`) gets a read
   channel of its own, `FileChannel.open(path, READ)`, opened with the
   file. `DbFile.read` is no longer `synchronized`; it reads with
   `FileChannel.read(buffer, position)`, a `pread` on Linux and macOS,
   which the JDK does not lock there (its `needsPositionLock()` is true on
   Windows only). Reads then run beside the writer's append and force, and
   beside each other. What a read must get right without the monitor:
   * **The length it may read.** A `volatile` length that `append` sets
     after its force; a read checks against it as today, and past the end
     it throws `EOFException` (005-24).
   * **A deleted file.** The cut (change 4) sets `isDeleted` before it
     closes the channel. A read checks it first, as today, and again when
     it finds the channel closed; then it throws
     `ReadBelowFirstPosException`, and the stream goes on (011-04, W1). A
     read in progress when the channel is closed finishes first:
     `FileChannel.close()` waits for it (the JDK's
     `NativeThreadSet.signalAndWait`).
   * **A closed stream.** The same with `isClosed`; the read fails as
     today.
   * **Interrupts.** A read clears its thread's interrupt flag before it
     reads and sets it again in a `finally`. If it finds the channel closed
     while the file is neither deleted nor closed, an interrupt during a
     read closed it: it opens a new channel, once for each one closed,
     under a small lock of its own (not the file's monitor, which the
     writer holds during its force), and reads again. A read is then not
     interruptible, as a `RandomAccessFile` read is today, and an interrupt
     fails neither the read nor the stream (`ReadPathProbe`'s readers).
     The cut and `close()` close the channel under the same small lock, so
     that a channel opened again cannot outlive them. Without this, one
     interrupted reader would fail the database: `StorageManager` and `Db`
     take any other `IOException` of a read as a failure of the storage
     (005-30).
   * **The JDK's native buffer.** A positional read into a `byte[]` goes
     through a native buffer that the JDK keeps for each thread, as large
     as its largest read (`sun.nio.ch.Util`; `jdk.nio.maxCachedBufferSize`
     sets no limit by default). The reads that reach `FileStream` are at
     most about 200 KB (`RecoverableStream` splits at the meta blocks,
     the replicas' copy reads 50 KB), so at most that for each reading
     thread.
   * **Windows.** There the JDK locks a channel for a positional read, so
     the reads of one file wait for each other, but not for the writer.
2. **The writer keeps its handle and its monitor.** `DbFile.append` is
   unchanged: the `RandomAccessFile` from `FileStreamIo.open`, the write
   and the force through `FileStreamIo`, under the file's monitor, which
   no read takes now. The power-loss model
   (`FileStreamPowerLossTester`) and the native audit (`flush-order.sh`)
   see the same operations. When the file is full, the writer closes its
   handle, and the read channel stays: `newFile` no longer reopens the old
   file read-only.
3. **The file list without a lock.** The files, their first positions and
   the stream's first position go in one immutable object, in a `volatile`
   field: `findFile` and `getFirstPos` read it without a lock. The
   writer's side (`newFile`, `pretruncate`, `seekFirstPos`, `close()`)
   still takes the stream's monitor, and publishes a new list.
   `newFile` creates the new file and forces it and the directory before it
   takes the monitor, and takes it only to publish the list: no read needs
   the new file before an append to it has returned.
4. **The cut's deletes on a thread of their own** (decision 1).
   `pretruncate`, under
   the stream's monitor, only takes the files off the list: it marks them
   deleted, publishes the list with the new first position, queues the
   files, and starts the cut's thread if it is not running. The thread
   deletes the queued files oldest first, each followed by a directory
   force, as `pretruncate` does today, with no lock held during the I/O,
   and it ends when the queue is empty (010-P3, calm when not used: no
   thread while nothing is cut). `close()` waits for it, then closes what
   is left.
   * The commit that makes the cut returns at once, with no I/O, and no
     read or commit waits for the deletes. An interrupt of the committing
     thread no longer reaches a channel (found on the way, point 2).
   * The deletes and forces reach the disk in today's order, so the
     power-loss argument holds as it is (011-07). A crash before the thread
     has deleted the files leaves them on disk; the next start cuts them
     again, as after a crash between the reclaim table's write and the cut
     today (`Reclaim`, at the start: `aos.getFirstPos() < firstPos`).
   * A failed delete or directory force stops the thread, which keeps the
     exception as the stream's failure, as `pretruncate` does today: the
     next read, append or cut throws it, and so does `close()`. Today the
     commit that makes the cut throws it at once (decision 2).
   * The first position moves when the files leave the list, at the moment
     it moves today: `PHYSCUT` in the traces (`TraceExport`) and the
     conformance check of it, and the soak's count of physical cuts, are
     unchanged. The disk gets the space back a little later.
5. **`SalsaStream` reads before it locks** (decision 3). `read` reads the
   encrypted bytes into its own array before it takes `readLock`, and holds
   the lock only to decrypt with the shared `Salsa` object, CPU work only.
   Two lines move.
6. **Interrupts**: the rule and the changes of the section "Interrupts"
   (decision 4).
7. **The test reports note the disk's waits** (decision 5).
   `BufferedStream` counts its writer's waits for room in the write
   buffer: how many, how long in all, the longest, and the JVM uptimes of
   the five longest, as the pause probe keeps its own; `Db.internal()`
   gives them, as it gives the cache's statistics. The tools time the
   forces themselves, through a `FileStreamIo` of their own, as this
   entry's probes do (file forces, directory forces, deletes; the five
   longest with their uptimes), so `FileStream` keeps no statistics for it.
   `PauseProbe`, `Soak` and ScaleBench print both for each phase, and a
   report sets a long commit or get beside them, as 009-03 sets them
   beside collections and batches.

For the tests:

* `FileStreamIo` opens the read channel (`openRead(File)`), so that a test
  can make reads slow, fail, or close under them, as it does with writes.
* A hook on `FileStream` that waits for the cut's thread and throws its
  failure, public as `FileStreamIo` is, for `FileStreamPowerLossTester`:
  its tests that count deletes right after `pretruncate`, or expect
  `pretruncate` to throw, wait for it first; its database traces may wait
  for it after each transaction, so that their images stay deterministic.
* `FileStreamPowerLossTester.testPendingCutForceFailureDoesNotAcknowledgeFlush`
  changes with change 4: the flush's bytes are forced and acknowledged,
  and the failed directory force fails the storage at its next operation
  (decision 2).


Interrupts
----------

Part of this entry since 2026-10-27 (decision 4). An interrupt is how a
Java application asks a thread to stop what it does: `Future.cancel(true)`,
`ExecutorService.shutdownNow()`, a server that gives up on a request. A
thread may call BergDB with its interrupt flag already set, or get it set
during a call. `Object.wait`, `Thread.sleep` and `Thread.join` then throw
`InterruptedException`, and a `FileChannel` closes itself, for every
thread, when the thread that uses it is interrupted
(`ClosedByInterruptException`; `ReadPathProbe`). A `RandomAccessFile` and
`synchronized` ignore interrupts.

What each call does today, by `InterruptProbe`
([interrupt-calls.txt](46-stream-file-lock/out/interrupt-calls.txt)),
`InterruptCutProbe`
([interrupt-db.txt](46-stream-file-lock/out/interrupt-db.txt)) and the
code; "the flag" is the thread's interrupt flag:

| A call, its thread interrupted | Today | Proposed |
|---|---|---|
| A read: a get, a scan, `getTrans`, a commit's loads | works; the flag kept | the same, with positional reads (change 1) |
| A commit | works; the flag kept | the same |
| A commit that waits for room in the write buffer | fails the database: `BufferedStream.append` turns the `InterruptedException` into an `IOException` ("Thread interrupted while appending."), which fails the main stream | waits on (a) |
| A commit that makes a physical cut | fails the database: `ClosedByInterruptException` in `forceDirectory` | works: the cut's thread does the I/O (change 4) |
| `sync()` | throws a `StreamIoException` (an `InterruptedIOException`), and the database goes on (005-30); the flag cleared | the same, the flag kept (d) |
| `Db.close()`, the first close | returns at once, after 0.3 ms with transactions in the buffer, before they are written and the files closed; the storage thread stays, waking every 5 ms, its file open | waits until the storage is closed (b) |
| `Db.stop()`, `Database.stop()`, a `Db.close()` beside another | works: the close runs on a thread of its own, or the wait ignores interrupts (005-35) | the same |
| A new `FileStream`: the builder's `dir()` and `replica()`, `addReplica` | throws `ClosedByInterruptException`, in a `StreamIoException` from `dir()`: the directory's force | works (c) |
| `Db.start()`, the stream made before | works; the flag kept. A replica's `seekFirstPos` at the start, or a full write buffer, would fail it as above | works (a, c) |
| A job's `join()`: `addReplica`, the index jobs | throws `java.lang.Error` ("Internal thread unexpectedly interrupted."); the flag cleared | returns the job's status (e) |
| The Pub API's wait before it runs a transaction again after a conflict (`RwTransaction`) | throws a `RuntimeException`, the transaction not run; the flag cleared (the code; not probed) | throws a `DbException`, a refusal; the flag kept (f) |
| BergDB's storage thread, interrupted by the application (`ThreadGroup.interrupt()`) | ends with a `Bug` ("consumer thread interrupted and stop==false"); a commit and a sync then wait for ever: the database hangs | goes on (g) |

**The rule, proposed.** An interrupt never fails the database or its
storage, never hangs it, and never cuts short a call that must complete.
Three calls only wait, and can stop waiting with no effect on the
database: `sync()`, a job's `join()`, and the Pub API's wait before a
transaction's rerun; an interrupt ends them, as today. Every other call
ignores an interrupt until it is done, as file I/O in `java.io` and
`synchronized` do, and as `Db.close()` does already when another close
runs (`waitUntilClosed`, 005-35). If the flag was set when a call began, or
got set during it, it is set when the call returns or throws: BergDB never
swallows an interrupt. BergDB's own threads go on when something
interrupts them.

**The changes**, beyond changes 1 and 4:

* **(a)** `BufferedStream.append`'s wait for room: on an
  `InterruptedException` it notes it and waits on, and sets the flag again
  before it returns. It still throws when the stream has stopped (005-35).
  The wait comes after the transaction's go point, where nothing may throw
  (005-01).
* **(b)** `BufferedStream.close`'s two waits, for the last flush and for
  the storage thread to end: the same, so that `close()` returns when the
  stream is written and closed, as its Javadoc says, and leaves no thread.
* **(c)** The forces on an application thread: those of a new
  `FileStream` (`createDirIfNeeded`, and `openForRw` of the last file, or
  of the first in an empty directory) and those of a replica's
  `seekFirstPos` at the start (`deleteAllFiles`, `newFile`). `FileStream`
  clears the flag before them and sets it again after. A force that an
  interrupt during it closes anyway is made again: a directory's on a new
  channel, as `forceDirectory` opens one for each force; a file's after
  `openForRw` has opened the file again, as the close of a channel from a
  `RandomAccessFile` closes the file too. On the storage thread and the
  cut's thread, which nothing interrupts, nothing changes, and
  `FileStreamIo` and the power-loss model stay as they are.
* **(d)** `StorageManager.sync` and `syncStrong` set the flag again before
  they throw the `InterruptedIOException`.
* **(e)** A job's `join()` (`IndexBuilderImp`, `IndexManager`,
  `DatabaseImp`, `DbHelper`): an interrupt ends the wait, and `join()`
  returns the job's status, the flag set; no `Error`.
* **(f)** `RwTransaction`'s wait before a rerun: an interrupt ends it with
  a `DbException` that says the transaction was not run (a refusal, in
  `DbException`'s terms: nothing changed, and the database goes on), the
  flag set.
* **(g)** BergDB's own threads go on when interrupted: the storage thread
  (`BufferedStream.runConsumer`), the cut's thread, and the index jobs'
  threads (`IndexBuilderImp`'s pause between steps throws an `Error`
  today). The eviction thread ends, as today, and the next load starts
  another.
* **(h)** The Pub API says it: `Database`'s class Javadoc states the rule;
  `sync()`'s, that an interrupt ends its wait with a `DbException` (a
  `StreamIoException` with an `InterruptedIOException` as its cause) and
  the transaction stays committed; `Job.join()`'s, that an interrupt ends
  the wait.

**Tests.** A unit test for each row of the table, with the flag set before
the call; those of the rows that are wrong today fail today. The commit
that waits for room uses a small buffer and a `FileStreamIo` whose force
waits on a latch; the cut is made as in `InterruptCutProbe`. And a stress,
`InterruptStress` in `java/stress`: readers, scans, a writer with syncs,
reclaim's cuts and eviction on a `FileStream`, and a restart, while a
thread interrupts the workers at random, about every 100 µs, and now and
then the storage thread. It checks that the database never fails or
hangs, that every value read is right, that only a sync throws for an
interrupt, and that a call that began with the flag set, or got it, ends
with it set. In `level3.sh`, which makes the cuts.


What it does not fix
--------------------

* **A writer that fills the write buffer waits for the disk.** During a
  force of seconds, a writer that commits more than the disk takes fills
  the 10 MB buffer and then waits for room, whatever the locks: the
  device's throughput, not BergDB's code. It does not count against
  target 2 (decision 5), and the test reports show it apart (change 7). On
  s1, with transactions of 1,000 puts, it may be part of the commits'
  waits; the pause probe there will tell how much.
* **The device and the OS.** A read that misses the OS's cache waits for
  the device. On APFS a read can wait a few milliseconds for a write to the
  same file (`ReadPathProbe`). Linux's ext4 takes no lock for a buffered
  read; to be seen on s1.


Alternatives
------------

The three options of the first version are among them.

* **Only the force outside the file's monitor** (the first version's
  second option): a read of the last file would still wait for the write,
  of up to 5 MB, and for the other reads of the file; a new file and a cut
  would still stop every read. Not enough by itself; with change 1 it is
  not needed.
* **The cut's deletes outside the stream's monitor, on the committing
  thread** (the third option as first written): no read waits, but the
  commit that makes the cut waits for the whole cut, 88 to 171 ms in P4's
  soak on F53 and seconds on a slow disk, and the commits behind it for the
  write lock; and the interrupt of point 2 stays. Not enough for target 2.
* **The deletes on `BufferedStream`'s consumer thread**, where a pending
  cut is made today: no new thread, but the flushes, and so every sync,
  would wait for the deletes.
* **A pool of `RandomAccessFile`s for each file**, instead of a channel:
  not interruptible, so nothing to open again; but two system calls a
  read, a file descriptor for each reading thread and file, a pool to
  keep, and in the probe fewer reads than positional reads (0.50 to 0.67
  million a second against 0.86 to 1.05).
* **Memory-mapped files**: no system call a read; but the last file grows
  and must be mapped again, an I/O error becomes an `InternalError` at any
  read of the memory instead of an `IOException`, and unmapping before a
  delete needs Java 22's `Arena` (BergDB builds with `--release 17`). No.
* **`AsynchronousFileChannel`**: an interrupt of the caller does not close
  it, but each read goes to a thread of its pool and back. No.


Decisions
---------

Frans, 2026-10-27, on the investigation's questions:

1. "as proposed": the cut's files are deleted on a thread of their own
   (change 4), not on `BufferedStream`'s consumer, where the flushes and
   syncs would wait behind them.
2. "Yes": a failed delete or directory force fails the stream at its next
   operation, and the flush before it stays acknowledged, its bytes
   forced. 011-07's rule, that a failed pending cut keeps the flush from
   being acknowledged, goes; `docs/levels.md`, section 8 ("the failures of
   deferred cuts passed on"), is to say so when the change is made.
3. "Include in this item": `SalsaStream` is part of this entry (change 5).
4. "Please elaborate in this one": interrupts are part of this entry (the
   section "Interrupts"), not an entry of their own.
5. "no, but such conditions are worth noting in test reports": a writer's
   wait for room in the write buffer, the disk's limit, does not count
   against target 2; the test reports note it, and the forces (change 7).


6. The rule for interrupts, decided on 2026-10-27 after Frans asked for
   more ("I have limited knowledge here. So, please tell me more before we
   make the decision about the rule.") and was given two options: A, as
   proposed in "Interrupts" (the three calls that only wait, `sync()`, a
   job's `join()` and the Pub API's wait before a rerun, end on an
   interrupt; every other call ignores it until it is done; the flag is
   always kept; BergDB's own threads go on), or B, every call ignores
   interrupts, simpler to state, but no thread waiting in `sync()` or
   `join(0)` could be cancelled. Frans: "Decision: A. When possible,
   implement this and commit it."


Implemented
-----------

2026-10-27, as proposed, in one commit:

* **`FileStream`** (changes 1 to 4). A file's reads are positional reads on
  a read channel of its own (`FileStreamIo.openRead`), without a lock;
  `DbFile.read` clears the interrupt flag, sets it again after, and opens
  the channel again when an interrupt closed it. The list of files is a
  `volatile` array, replaced, never changed; `findFile` and `getFirstPos`
  take no lock. `newFile` forces the new file and the directory before it
  takes the stream's monitor, and the old last file keeps its read channel
  (`closeWriter`). `pretruncate` only takes the files off the list; the
  thread `FileStream-cut` deletes them, oldest first, with a directory
  force after each, and ends when nothing is left; `close()` waits for it;
  `awaitDeletes()` waits for it and throws its failure, for tests. The
  forces on an application thread (`DbFile.force`, `forceDirectory`) clear
  the flag and force again after an interrupt closed their channel. One
  thing found in the tests: `FileChannel.size()` is interruptible too, so
  `openForR` takes the file's length from `File.length()`.
* **`SalsaStream`** (change 5) reads before it takes `readLock`.
* **Interrupts** (change 6): `BufferedStream`'s wait for room and its
  `close()` ignore interrupts and keep the flag, and its storage thread
  goes on when interrupted; `StorageManager.sync` and `syncStrong` set the
  flag again before they throw; a job's `join()` returns on an interrupt
  (`IndexBuilderImp`, `IndexManager`, `DatabaseImp`, `DbHelper`), and
  `IndexBuilderImp`'s own pause goes on; `RwTransaction`'s wait before a
  rerun throws a `DbException`, the flag set. The rule in `Database`'s class
  Javadoc, and in `sync()`'s and `Job.join()`'s.
* **Test reports** (change 7): `BufferedStream` counts the writer's waits
  for room (`takeRoomWaits()`, through `Db.Internal.takeWriteBufferWaits()`);
  `java/stress/TimedIo.java` times the file and directory forces and the
  deletes; `PauseProbe` prints both after the load and each phase, and
  `Soak` puts them in its result (`disk_waits`). ScaleBench, which lives in
  `releases/2026.1/`, is not changed.
* **Tests**: in `FileStream`, a read of the last file while its force is
  held, a read of the first file while a new file's directory force is
  held, a cut on its own thread (reads go on, `close()` waits for it), a
  failed delete of a cut, reads and interrupts (the flag kept, a channel
  closed under the reads), a cut and a new `FileStream` by an interrupted
  thread, and an f-test of four readers, one of them always interrupted,
  beside a writer and cuts. In `BufferedStream`, the wait for room, `close()`
  and the storage thread, each interrupted. `InterruptTester` (core):
  commits that make cuts, a commit that waits for room, `sync()`, a start,
  commits and `close()`, and the storage thread, each interrupted.
  `PubInterruptTester`: the builder's `dir()` and a job's `join()`.
  `FileStreamPowerLossTester` waits for the cut's thread where it counts
  deletes, and its trace after each transaction, so that the images stay
  deterministic; its test of a failed pending cut now expects the flush
  acknowledged and the stream failed at its next operation (decision 2).
  `InterruptStress` (`java/stress`, step 9 of `level3.sh`): a writer with
  syncs, readers, cuts, eviction and restarts, interrupted at random every
  100 µs and the storage threads every 100 ms; 20 s: about 4 million calls,
  150,000 of them interrupted, the flag kept by all, 9,900 syncs ended by
  an interrupt. On the jar from before, it fails in seconds: the storage
  thread ends with a `Bug`, and a call loses the flag.
* **Gates**: `java/before-commit.sh` (1,042 unit tests and 72 f-tests),
  `level3.sh` in full (its new step 9: 60 s, 10.6 million calls, 457,702
  of them interrupted, the flag kept by all, 31,191 syncs ended by an
  interrupt, 15 restarts; `ReclaimReaders` on `FileStream` and the
  power-loss traces, 440 cold recoveries, as before), and `flush-order.sh`
  (4 writes, 9 file forces, 12 directory forces and 2 deletes in the
  required order, as in 011-07). `level2.sh` and `level4.sh` were left
  out, at Frans's word ("Yes, commit sooner."): `before-commit.sh` is the
  only requirement (AGENTS.md); they run in `night.sh`.

Left from "Done when": the probes of this entry again on the new code, the
pause probe on s1 (s1 was busy with another session's runs), P4's soak,
and Props and ScaleBench from the OS's cache.


Done when
---------

* No read waits for an append, a new file or a cut: unit tests with a
  `FileStreamIo` whose force, directory force and delete wait on a latch;
  a read of the last file, of another file and of a file the cut keeps
  returns while they wait, `pretruncate` returns while the deletes wait,
  and `close()` waits for them. They fail today.
* An interrupt fails neither a read nor the stream: a read by a thread
  whose interrupt flag is set returns its bytes and leaves the flag set;
  readers interrupted over and over read on while the channel closes
  under them (as `ReadPathProbe`'s, on `FileStream`); a cut by an
  interrupted thread works (`InterruptCutProbe`'s second case goes on).
* A failed delete or directory force stops the deletes, so that no file
  after it is deleted, and the stream's next read, append and `close()`
  throw it.
* `SalsaStream`: a read of one file does not wait for a read of another.
* Interrupts: the unit tests of the section "Interrupts", one for each
  row of its table, and `InterruptStress`; `InterruptProbe` and
  `InterruptCutProbe` again: no call fails the database or hangs it, and
  the flag is kept. The Pub API's Javadoc says the rule.
* The test reports (change 7): `PauseProbe`, `Soak` and ScaleBench print
  the writer's waits for room in the buffer and the forces, each with the
  five longest and their uptimes.
* The probes of this entry again: no reader's longest read follows the
  forces, the new files or the cut, and in `SlowForceProbe` no get and no
  single-put commit waits for a slow force.
* `java/before-commit.sh`; `level3.sh` in full (reclaim, `ReclaimReaders`
  on `FileStream`, the power-loss traces, conformance); `level2.sh` and
  `level4.sh` quick, as every read takes the new path; `flush-order.sh`,
  the native order of writes, forces and deletes, now from two threads.
* The pause probe on s1 (009-03's `run-pp2.sh`): no get waits for a force,
  and its report sets the longest commits beside the writer's waits for
  room and the forces. P4's soak under ZGC: the cuts are no longer its
  slowest commits and reads (009-04, section 7.3).
* No fewer reads a second: Props (CORE), and 009-03's ScaleBench block
  from the OS's cache (C) on F53.


First step
----------

The unit tests that fail today, with latches in a `FileStreamIo`: a read
while a force is held, while a new file's forces are held and while a
cut's directory force is held; and those of the interrupts: a commit that
waits for room, a commit that makes a cut, the first `close()`, a new
`FileStream`, a job's `join()` and the storage thread, each with the flag
set.


Size and order
--------------

M to L, in three steps that can be committed one by one: the reads, the
file list, `newFile` and the cut's thread in `FileStream`, about 200
lines, and `SalsaStream`'s two, with their tests, about 250; the
interrupts, about 100 lines in `BufferedStream`, `StorageManager`,
`FileStream` and `pubimp`, the Javadoc, their unit tests and
`InterruptStress`, about 400; the test reports, about 100. Independent of
the other open entries; before 005-47, whose option A changes the forces
of the same class. Item 009 waits for the first step and the last: the
pause probe on s1 needs the reports.
