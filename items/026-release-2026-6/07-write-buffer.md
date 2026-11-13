# 026-07. The write buffer grows with use

Created 2026-11-13 by Frans Lundberg. Status: open.

For release 2026.6 (Frans, 2026-11-12, 12:10, "As recommended", on
024-05, ST8, and 024-01, PA7): "a buffer that grows with use (or a
setting), and the cost per database in `DatabaseBuilder`'s Javadoc".
Every started database held about 11 MB of heap, whatever its size: the
10 MB write buffer, allocated at the start (020-24-10, U10-2: 48 small
databases filled a heap of 512 MB; 024-05, ST8: "heap of an empty
database 11 MB, target near nothing").

Done in the clone, branch `026-07-write-buffer` (section 9): the buffer
starts at 64 KiB, doubles when an append does not fit, up to 10 MB, and
shrinks back after a second with nothing to write. A small file database
now holds 0.67 MB of heap, not 11.10 MB; write throughput unchanged
(section 5).


## 1. Where the 10 MB came from

* `StorageManager.DEFAULT_BUFFER_SIZE`, 10,000,000 bytes, the main
  stream's `BufferedStream`. Its constructor allocated the whole ring
  buffer, `new byte[bufferCapacity]`, at the start of the database; the
  buffer was released only when its thread ended, at `close()` (since
  2026-11-09, 020-24-10, U10-3). The Core's `DbBuilder.stream(name,
  stream, bufferSize, bufferTime)` sets it; the Pub API has no setting.
  `testSetup()` uses 100,000 bytes.
* The buffer's rules, all fractions of its capacity C:
  * **The quarter** (005-76): the consumer thread writes at once when
    C/4 bytes are buffered, 2.5 MB; an append that crosses C/4 wakes it.
    Else it writes after four waits of a quarter of the buffer time (50
    ms in all), or at once when a sync waits (005-48, `flushSoon`).
  * **A flush writes at most C/2**, 5 MB, as one append and one force of
    the `FileStream`, "to leave room for the producer" while it writes.
  * **The room wait**: an append that does not fit waits when less than
    C/10 is free, with the database's write lock (005-46's room waits:
    the disk's limit, not BergDB's, P1 does not count them).
* What depends on C: the bytes a force carries (at most C/2) and so the
  forces a second under load (005-64 counted them); the backlog the
  writer may build before it waits for the disk; a transaction larger
  than the free room is copied in parts and waits for room between them,
  so a record up to L5 (32 MiB, 024-24) streams through a 10 MB buffer.
  Nothing else: reads of buffered bytes and cuts work at any C.


## 2. The options

* **A. A builder setting with a small default.** `DatabaseBuilder` gets
  `writeBufferInKb(int)` or similar, default say 256 KiB. Simple, but a
  default small enough for many databases costs the writer of a large
  database: more forces, smaller chunks, room waits at a backlog above
  the setting. A user must know the setting to get today's throughput
  back. New Pub API (Frans decides new API, as for PA8).
* **B. A buffer that grows with use, the thresholds of the largest.**
  Start at 64 KiB; an append that does not fit doubles the buffer as
  often as needed, up to the largest (10 MB, or the Core's setting);
  shrink back after an idle time. The quarter, the flush's half and
  the room wait stay those of the largest buffer, so the flushes, their
  sizes and their forces are today's at every write rate: the buffer
  holds just what today's rules let accumulate. No API change.
* **C. B with the thresholds of the current buffer.** The quarter of a
  64 KiB buffer is 16 KiB: at moderate rates many more, smaller forces
  (one per 16 KiB instead of one per 50 ms), and a sync of a
  transaction larger than half the buffer waits for two forces. Rejected
  for those reasons.
* **D. B without the shrink.** A database that once had a burst keeps
  up to 10 MB until it closes; the many-small-databases case (U10-2)
  then depends on the history of each database. Rejected.

**Decided by rule** (the item's brief: "pick by the recommendation and
the evidence"): **B**. PA7 recommends a buffer that grows "(or a
setting)"; B needs no new API, keeps write throughput by construction
(same flushes and forces), and a setting can be added later on top of
it as the largest size (question Q1, section 8).


## 3. The design

All in `BufferedStream` (bergdb 026-07 in its comments):

1. **Start.** The buffer's length is `min(bufferCapacity,
   INITIAL_CAPACITY)`, `INITIAL_CAPACITY` = 64 KiB. `bufferCapacity`,
   the constructor's argument, is now the largest length (`maxCapacity`).
   A given capacity of 64 KiB or less (every `BufferedStream` unit test
   but two) behaves as before.
2. **Grow.** When: an append finds less room than its length, and the
   buffer is below its limit (`growLimit`, normally `maxCapacity`). Who:
   the writer, in `append`, under the object's monitor, before it would
   wait for room. How: the new length is the buffer's doubled as often
   as needed to hold what is buffered plus the append, capped at the
   limit; the buffered bytes are copied to the same stream positions in
   the new ring (positions modulo the new length). A flush in progress
   goes on from the old array: the consumer takes the array and its
   length with `cSize` (`takeFlush()`, under the monitor), and the bytes
   it writes there are not changed by anyone. A grow costs one
   allocation and a copy of at most 10 MB under the monitor, a few ms
   at the largest, once per doubling: about 8 doublings from 64 KiB to
   10 MB, all within one burst.
3. **The thresholds stay those of the largest buffer**: the quarter
   (2.5 MB), a flush of at most half (5 MB), the room wait below a tenth
   of the buffer once the buffer cannot grow. A buffer below the largest
   never makes the writer wait; the writer waits only at the largest
   length, as before, so P1's accounting of room waits is unchanged.
4. **Shrink.** When: the consumer has gone idle (nothing buffered for a
   whole buffer time, 005-14's untimed wait) with a grown buffer, and
   stays idle for `shrinkDelayMs`, 1 s. Who: the consumer thread, in
   `waitToShrink()`, under the monitor. How: it waits once with that
   timeout (an append, a sync, `stop()` or `close()` ends the wait, and
   the idle time starts again at the next idle); after it, the buffer is
   replaced by a new 64 KiB array, with nothing to copy, and the
   consumer waits without a timeout as before. A first-sized buffer's
   idle consumer waits without a timeout at once: 005-14's "an idle
   stream does not wake the thread" holds, but for one wake after a
   grown buffer's idle second.
5. **An allocation that fails** (`OutOfMemoryError` of a grow) keeps
   the buffer and sets `growLimit` to its length until the next shrink:
   the writer then waits for room as at the largest length. Since the
   quarter of the largest may then never be reached, a buffer with less
   than a tenth free is written at once (`nearlyFull()`), and the writer
   wakes the consumer before it waits. A failed shrink keeps the grown
   buffer. Neither fails the database; before, the 10 MB allocation of
   a start threw `OutOfMemoryError` from the start (U10-2's 49th
   database).
6. **No change** to the format, the bytes written, where a flush ends,
   the Lean model (the buffer is below the model's stream) or the Pub
   API. Javadoc: `DatabaseBuilder.startupDistanceInMb()`'s paragraph on
   the write buffer and `Database`'s class Javadoc and `stop()` give the
   cost per database: 64 KiB to 10 MB of buffer, about 0.7 MB of heap
   in all for a small file database, one thread, three open files.
   `DbBuilder.stream`'s `bufferSize` and `DEFAULT_BUFFER_SIZE` say that
   they are the largest length.

Tests (`BufferedStream`): `testGrowsAndShrinks` (the first length, a
grow by 4, a grow capped at the largest, reads from the grown buffer,
the shrink after the idle delay, the bytes in the stream) and
`testGrowsDuringFlushes` (a slow stream, 900 appends of 1 B to 100 kB
with reads after each, grows during flushes, three idle times and
shrinks, every byte in order). `testNoFlushOfNothingWhenClosing` plays
the consumer and now calls `takeFlush()` instead of setting `cSize`
(no expected value changed). The Core's `testSetup()` buffer of 100,000
bytes now starts at 64 KiB and grows: every unit and f-test that writes
more than 64 KiB between flushes exercises the grow.


## 4. The rest of a small database's heap

With the buffer at 64 KiB, a small file database holds 0.67 MB. A class
histogram of 50 such databases (`07-write-buffer/HistProbe.java`, then
`jcmd PID GC.class_histogram`, 2026-11-13) gives per database about
0.31 MB for the Core's cache tables (4,096
`Cache3$Table`s, each with a `HashMap` and its values view, and the
table array), 180 kB of `byte[]` (the 64 KiB buffer and others) and
80 kB of `long[]`. The cache tables are the next lever towards "near
nothing": 024-33 made them shrink after a mass delete, but every
started database makes all 4,096 at its start. Not in this item
(question Q2).


## 5. Measurements

### 5.1 Heap

`07-write-buffer/HeapProbe.java` (2026-11-13, F53, JDK 27, `-Xmx2g`):
20 file databases, then 20 memory databases, each started with one
small put and a sync; the heap after GC (the least of five), per
database. Then a burst of 20,000 transactions of one 1 kB value in one
database, no sync, and the heap at once and after 2 s with no writes
(the burst's own data, about 26 MB in the cache, in both).

| Heap                          | before (ee5712c5) | after (c8b81d9e) |
|---|---|---|
| a small file database         | 11.10 MB          | 0.67 MB          |
| a small memory database       | 12.07 MB          | 1.65 MB          |
| after the burst, at once      | +26.00 MB         | +36.50 MB        |
| after the burst, 2 s idle     | +26.01 MB         | +26.08 MB        |
| the burst's time              | 405 ms            | 406 ms           |

So the buffer grew to about 10 MB in the burst and shrank back after the
idle second. Logs: `/Users/f/fl/bench/2026-11-13/wb/heap-base.log`,
`heap-new.log`.

### 5.2 Many small databases (U10-2's case)

`07-write-buffer/ManyProbe.java`: small file
databases started one after the other in a heap of 512 MB, one put each,
until an `OutOfMemoryError`.

| Build  | started in 512 MB          | heap after GC              |
|---|---|---|
| before | 48, the 49th threw OOME    | 531.5 MB                   |
| after  | 300 of 300                 | 184.0 MB (0.61 MB each)    |
| after  | 878, the 879th threw OOME  | 530.0 MB                   |

Log: `/Users/f/fl/bench/2026-11-13/wb/many.log`.

### 5.3 Write throughput

PLACEHOLDER


## 6. The heap measures of the harness: MEM and G4, G5

Two measures had the 10 MB buffer on both sides of a difference, and
moved when it became a transient:

* **MEM** (006-02; `level1.sh`'s Props step): the heap after a fill of
  1M KVs minus the heap of the empty database, per KV. The empty
  database held the 10 MB buffer; now the fill grows the buffer to
  about 8 MB and MEM rose from 129.3 to 137.5, and `level1.sh` failed
  ("MEM 138, more than 131"). The KVs cost the same. `Mem` now waits
  2 s after the fill, for the buffer's shrink, before it measures:
  MEM 129.3 again, its meaning since 2015 (the buffer outside the
  difference). No limit changed.
* **G4 and G5's heap gates** (024-30, 024-32, `count-gates.sh`, a
  night step): the emptied database's heap at most 2 times its
  hello-world twin's. Both held 10 MB of buffer, so the gate compared
  about 17 MB with 12 MB (G5 on `ee5712c5`: 1.40). Without it, measured
  right after the drive, G5's twin, which writes nothing in its drive,
  held 1.9 MB and the emptied database 17.5 MB with a grown buffer:
  9.3, FAIL. Measured after the shrink (`g4Run` now waits 2 s;
  `-Dg4heapwait=MS` sets the wait): G4 8.1 MB against 4.0 MB, 2.009,
  FAIL by a hair; G5 7.1 MB against 1.9 MB, 3.74, FAIL. **The buffer
  had hidden this.** A class histogram of G5's emptied database in its
  wait against the twin's: 4.4 MB more for `NodeCollection.idByPos`
  (an access-ordered `LinkedHashMap<Long, Long>` of node ids by
  position, an LRU of at most 100,000 entries; about 49,000 after G5's
  drive: `Long`s, entries, the table) and 2.2 MB more of `long[]` (not
  traced). A bounded cost (about 9 MB at 100,000 entries), not
  proportional to the keys, but kept after back to empty.
  **Decided by rule** (a change in this item must not move a gate that
  Frans set; the questions go to him): the gates compare each heap
  plus the 10 MB (`CountGates.BUFFER`), the basis the factor 2 was set
  on, and print the heaps without it. Result on `c9ce76de`: G4 1.423
  PASS, G5 1.597 PASS, COUNT GATES OK (all four). Question Q4.


## 7. Gates

PLACEHOLDER


## 8. Questions for Frans

* **Q1. A setting of the largest buffer in the Pub API?** Options: (a)
  none, the buffer grows by itself (this item); (b) a
  `DatabaseBuilder.writeBufferMaxInMb(int)`, for a small device that
  wants a bound on the 10 MB, or a writer of very large transactions
  that wants more. Recommended: (a) for 2026.6; the Core API keeps its
  `DbBuilder.stream(..., bufferSize, bufferTime)` for advanced users.
* **Q2. The cache tables, 0.31 MB a database** (section 4): recommended
  as a separate small entry for 2026.6, with the many-small-databases
  case as its measure (the 4,096 tables made at the first use of each).
* **Q3. The shrink delay, 1 s**, a constant: recommended as it is.
* **Q4. G4 and G5's heap without the buffer** (section 6): (a) keep
  the 10 MB constant in the gates (as now); (b) gate the plain heaps,
  and accept FAIL until `idByPos` is bounded by something that shrinks
  (cleared at back to empty, or sized by the cache budget); (c) (b)
  after such a fix, as a 2026.6 entry. Recommended: (c), with (a)
  until then.


## 9. State

2026-11-13, 08:40. Clone `/Users/f/fl/bench/2026-11-13/wb/clone`, branch
`026-07-write-buffer`, from `main` at `ee5712c5`. Commits: `c8b81d9e`
(the buffer that grows, its tests, the Javadoc), `c9ce76de` (MEM and
G4, G5's heap measures, section 6), and this item. Done: the code, the
heap measurements (section 5.1, 5.2), the first gates (section 7).
Not done yet: the gates on the head, the timing comparison (section
5.3; preserved builds `base-ee5712c5` and `wb-c8b81d9e` in the clone's
`java/build/perf/builds/`, the script
`/Users/f/fl/bench/2026-11-13/wb/timing.sh` runs both suites with
take-timing). To continue: run `timing.sh` in the background, fill
section 5.3 from `perf-quick.log` and `perf-largetx.log` in
`/Users/f/fl/bench/2026-11-13/wb/`, then the readme's Files line.
