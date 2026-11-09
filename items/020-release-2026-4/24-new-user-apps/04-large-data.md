# 020-24-04 A catalogue larger than memory

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of release 2026.4 would write it
(020-24's brief, round 2): the release jar alone on the class path, and
only what a user reads (README.md, the Pub API's Javadoc in
`java/src/bergdb/pub`, `overview-pub.html`, `releases/next.md`). The jar
was built from `cf287ad`. The implementation and docs/levels.md were read
only afterwards, to explain a surprise (U4-1 to U4-3).


## 1. The application

**What it does.** A product catalogue of 2 million Data Objects in a file
database with the smallest cache budget the API takes,
`cacheSizeInMb(4)`, so that eviction works hard, and the default startup
distance, 50 MB. Four phases, each a JVM of its own (`phase.sh PHASE
DATADIR [N] [HEAP]`; `run.sh DATADIR` runs them in order):

1. `load1`: create; the index `by-cat-price` (category, price) on the
   empty `/p/`; four writers and four readers; when 900,000 products are
   in, `Runtime.halt()` with the writers in flight, no close.
2. `load2`: start after the crash; find what the crash kept and compare it
   exactly; check every read of `load1`; load the rest, to 2 million, with
   the readers; the index `by-supplier` (supplier, stock) started at the
   250,000th new product of the phase, while the writers write; check
   everything; close.
3. `verify`: start; cold gets; every value and both indexes against the
   oracle; the indexes at past times; the whole state of the time after
   the crash, read at that time; readers at past times for a minute;
   close.
4. `small`: start in a smaller heap (U4-2); gets; readers for a minute;
   close; their reads against the oracle.

**The data.** A product (`Product`: sku, name, category, price, stock,
supplier, a description of 90 to 130 chars, a version; about 250 bytes
stored) at `/p/P0001234`; every 1,000th product has a 50 KB `byte[]`
image field; every 500th has a 50 KB attachment at `/att/P0001234.bin`,
4,000 in all. 500 categories (`cat-001`, `kök-007`), 2,000 suppliers.
Every value is a function of its id and version, so the oracle keeps
versions only. The stream is 1.6 GB after `load1` and 4.9 GB in 88 files
after `load2`, for about 1 GB of values put.

**The writers.** Writers 0 to 2 write `w()` transactions of 100 to 1,000
new products, their attachments, and updates and deletes of earlier
products (up to 5 percent of a transaction); writer 3 writes single
`put()`s and `delete()`s and small `w()`s. Each id has one writer in a
phase. Each writer logs its transactions to a file of its own, one
`write()` per record, so that a halt keeps them: the entries before
`execute()`, the transaction's time after it, and the times for which
`sync()` returned.

**The readers.** Two do gets of 20 random products (and an attachment) at
one frozen lookup time; one pages through the primary scan, 100 values a
page, forward and backward, a page at a time or 20 pages at one frozen
time, and pages of 10 attachments; one queries the indexes:
`eq(category)` with price bounds, a whole category, `prefix("kök-14")`,
the 50 most expensive below a price (`to()` and `backward()`), and
`eq(supplier)` with stock bounds. One read in ten is at a past time, an
earlier transaction's time or a time between two. Each read is checked at
once (each value is the function of its id and version; the order; the
bounds), and logged with its lookup time (`freezeLookupTime()`, then
`getLookupTime()` after the first read) for the oracle. `by-supplier`
became active only after `load2`'s writers had ended (U4-3), so its
bounded queries were few, those of `small`; the whole of it was compared
in order after `load2` and after the restart.

**The oracle, on disk.** The writers' logs are merged in time order; the
readers' logs are sorted by time; a replay applies the transactions to an
array of versions (8 MB) and compares each logged read at its time, the
index queries by filtering the 2 million products and sorting. After the
crash, B is the time of the last transaction that the start kept: the
frozen lookup time of the first read after the start, checked against the
logs (a pending transaction without its time is looked up, and its time
read with `transactionInfo()`); the transactions after B are lost. The
whole state at B is then compared, every product, attachment and index
entry, and the writers go on from it. The heap is sampled with `Runtime`
every 20 ms, and read after `System.gc()` at the phases' checkpoints.

**Size.** About 1,750 lines of Java in 6 files, `run.sh` and `phase.sh`,
in `/Users/f/fl/bench/2026-11-09/app-u4/app/`, and the probes `Probe.java`
(U4-1) and `Probe2.java` (U4-2), 100 lines. The outputs are in `app-u4/`:
`run1-load1.txt`, `run1-load2.txt`, `run1-verify.txt`, `run1-small-*.txt`,
`probe1.txt` to `probe5.txt`, and `run2.txt`, a second run of `run.sh`
with the final code; run 1's database and logs are in
`app-u4/data-after-verify/`. A run compares about 15 million values and
index entries in full, and about 78,000 logged reads (2.7 million entries)
at their lookup times. Run 1 took 3.5 minutes for `load1`, 20 for `load2`
(over the brief's 15: its full comparison at 4 MB, U4-1; the final code
compares at 64 MB there), 9 for `verify` and 1.5 for `small`, on F53 under
a load of 20 to 60 from other sessions. Run 2, the final code, printed
`APP OK` after 22 minutes: 3, 11, 7 and 1 for the four phases.


## 2. The findings

No wrong result, no throw from legal use and no hang: every value, index
entry and logged read agreed with the oracle, across the crash, the
restart and past times. The findings are of memory and speed, and of the
documentation.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U4-1 | doc | medium | a budget below what must stay in memory paces the reads   | Probe, (c)    |
| U4-2 | doc | medium | the heap follows the startup distance, not the budget     | small, Probe2 |
| U4-3 | doc | low    | a build of 1.5M values took 7 minutes: paused, no total   | load2         |
| U4-4 | API | low    | an index scan has no resume point for paging              | the app       |
| U4-5 | doc | low    | a scan's iterator has no close(): may one drop it?        | the app       |
| U4-6 | doc | low    | starts of 3 to 12 s where the Javadoc says 0.6 to 1.4 s   | the starts    |

Timings below are from F53 under a load of 20 to 60 from other sessions:
they are no measurements, only what a user would see; the ratios of
U4-1 held in each of four pairs of runs.

### 2.1. U4-1: a budget below what must stay in memory paces the reads

With `cacheSizeInMb(4)` and the default startup distance, the database is
over its budget all the time: what it must keep (D, the nodes changed
since the startup position) is most of a heap of 110 to 160 MB after a
start (U4-2), and the budget is 4 MB. Nearly every transaction then ends
with an eviction batch (up to 2 ms, under the write lock), and a reader's
load from the stream waits up to 2 ms for the eviction thread whenever the
resident bytes are more than a quarter of the budget, 1 MB, above the
trigger (`Eviction.afterLoad`; the trigger follows the pinned bytes of the
hand's last round, so while a writer makes D grow, the readers find it
behind). What the app saw:

* In `load1` the two get readers did 188,668 gets in the first 10 s and
  17,368 in the next 10 s, once the stream had passed the startup distance
  (run 2: 171,630 and 15,162), and the index reader did 2,624 queries and
  then 4. A thread dump (`jstack-load1.txt`) has the readers parked in
  `Eviction.afterLoad` and the single-put writer in `Eviction.sweep` at
  its transaction's end; in `load2`'s (`jstack-load2.txt`) the eviction
  thread had used 140 s of CPU in 450 s.
* A scan of a whole index of 2 million entries, alone after the restart:
  `by-cat-price` 291.8 s at 4 MB, `by-supplier` 75.4 s right after
  `setCacheSizeInMb(64)` in the same JVM; in `load2`, 369.5 s and 270.7 s
  at 4 MB, and in run 2, 64.5 s and 45.2 s at 64 MB.
* `Probe.java` on copies of the catalogue, 10 s for each case, a budget of
  4 MB against 200 MB (and 50 MB once):

  | Startup distance | Budget | Gets alone | Gets while a writer writes |
  |------------------|--------|------------|----------------------------|
  | 50 MB | 4 MB   | 26,041  | 15,187  |
  | 50 MB | 200 MB | 62,856  | 291,608 |
  | 50 MB | 200 MB | 148,702 | 468,213 |
  | 50 MB | 4 MB   | 94,909  | 38,403  |
  | 5 MB  | 4 MB   | 466,428 | 111,906 |
  | 5 MB  | 200 MB | 110,672 | 493,584 |
  | 5 MB  | 200 MB | 104,408 | 351,639 |
  | 5 MB  | 4 MB   | 99,084  | 24,320  |
  | 5 MB  | 50 MB  | 467,000 | 579,828 |

  Gets in one thread while a second writes `w()`s of 500 puts: 4 to 19
  times fewer at 4 MB, in all four pairs; the other cases vary with the
  OS's cache and the machine's load, and show no steady difference. The
  heap after `System.gc()` at the end: 150 MB at 4 MB, 234 MB at 200 MB
  (startup distance 50 MB); 41 MB and 223 MB (5 MB).

Reproduction: `java -Xmx1g -cp bergdb-release.jar:probe-classes Probe DIR
4`, then `... Probe DIR2 200`, on two copies of a database of 2 million
products in `/p/` with an index (`cp -c` of `app-u4/data-after-verify/db`):
case (c), gets of random keys in one thread for 10 s while another thread
puts random products in `w()`s of 500.

Not a wrong result, and by design (009, step 3d; 005-52). But the
Javadoc of `cacheSizeInMb()` says only that what must be kept "may exceed"
the budget, and "a small value will leave more available memory": it
does not say that a budget below it (here 110 to 160 MB of heap, at the
default startup distance) makes reads go at the eviction thread's pace
while anything is written, nor where the useful range starts. Fix: say
so, with the figure; or raise a budget below the pinned bytes, or make
the gap that readers wait at a fraction of the pinned bytes rather than
of the budget (a design question).

### 2.2. U4-2: the heap follows the startup distance, not the cache budget

A user who wants a small process sets the smallest budget,
`cacheSizeInMb(4)`, as `DatabaseBuilder` invites ("a small value will
leave more available memory for the rest of the JVM application"). With
the default startup distance of 50 MB:

* After a start (`System.gc()`): 110 MB (1.6 GB stream), 162 and 163 MB
  (4.9 GB); 139 to 185 MB at the checkpoints of `verify`.
* The start fails with `OutOfMemoryError` in heaps of 64, 128 and 256 MB
  (`run1-small-*.txt`; in `DbStarter.linkD`; without
  `-XX:+ExitOnOutOfMemoryError` it is a clean throw from `start()`, and
  the JVM ends); it starts in 384 MB, which then holds 131 MB after a
  minute of reads.

With a startup distance of 5 MB (`Probe2`: `setStartupDistanceInMb(5)`,
then 300,000 puts so that the section follows it) the same database of 2
million products, 4.9 GB, starts in 0.7 to 1.9 s, holds 21 MB after the
start and 23 to 42 MB after reads, and runs in a heap of 96 MB.

So the startup distance sets the heap; the budget only trims the part
above it (150 against 234 MB in U4-1's probe). The Javadoc does not say
how much heap a database needs: `startupDistanceInMb()` speaks of startup
time and "overall database performance" (and of 5 MB for a PC with 0.5
GB), `cacheSizeInMb()` of "the order of the startup distance" that is
never evicted. The rule that a start needs about twice the startup
distance of heap above the running database's is only in
`releases/next.md` and docs/levels.md, section 7; here it gives about
260 MB, and 256 MB was not enough. Fix: a paragraph in `DatabaseBuilder`
(or the package's "Good to know"): the heap a database needs, by the
startup distance (here about 3 times it running, and a start failed in 5
times it), and that a small heap is made with a small startup distance,
the budget on top.

### 2.3. U4-3: an index build of 1.5 million values took 7 minutes

`by-supplier` was started with 1.14 million products in `/p/`, three
writers and four readers at work and the 4 MB budget; its build read
1,480,037 values and became active after 438.1 s, 3.4 thousand values a
second (run 2: 1,477,794 values in 438.2 s), while
`useIndex("by-supplier")` refused, as documented. After the writers ended
(339 s), it took 205 s more. Two things a user does not learn from the
Javadoc: the build pauses half the time of each of its steps, by design
(`IndexBuilderImp.pause`, 020-10, section 6.1), and its reads go at the
eviction pace of U4-1. `JobStatus.count()` gives the values read, but
nothing gives a total to compare it with, short of a primary scan of the
directory. Fix: a sentence in `IndexBuilder.start()` on the pause and what
slows a build; maybe the directory's size in the status.

### 2.4. U4-4: an index scan has no resume point for paging

`UsePrimaryBuilder` pages exactly: `startAt(lastName).inclusive(false)`,
forward or backward, which the app did about 28,000 times. `UseIndexBuilder`
has no such point: page 2 of `eq("cat-042")` in price order is
`from(lastPrice, true)`, then the entries of that price up to the last
key read are skipped by hand, and backward the same with `to()`. With
large data paging is the normal use, and products that share a price are
real (4,000 products of a category over 1,000,000 prices; equal prices
are more common in real catalogues). A `startAfter(key)` that applies to
the entries of the last level's bound, or a resume token from a `Kv`,
would make it exact.

### 2.5. U4-5: a scan's iterator has no close()

Paging reads 100 values and drops the iterator. The Javadoc of
`objects()` and `kvs()` does not say whether an iterator that is not read
to its end holds anything (a lookup time against reclaim, memory,
handles). The app dropped about 30,000 iterators without a sign of a leak
(the heap stayed level over 20 minutes), so the answer is probably
"nothing to close"; a sentence would save a JDBC or LevelDB user the
search for `close()`.

### 2.6. U4-6: starts of 3 to 12 s at the default startup distance

`startupDistanceInMb()`: "The default is 50: startup then takes about 0.6
s with 1000-byte values and 1.4 s with 100-byte values, on a fast SSD
(measured 2026-10-13)". The catalogue's starts at 50 MB: 7.2 s and 5.1 s
after the crash (1.6 and 1.4 GB), 12.4 s, 5.5 s, 3.1 s and 3.1 s, and in
the probes 7.0 to 11.8 s (4.9 and 4.7 GB); the budget made no difference
(10.6 s at 4 MB, 11.8 s at 200 MB). At 5 MB: 0.7 to 1.9 s. F53 was loaded
by other sessions, so these are not measurements, but the gap is a factor
of 2 to 9: worth a measurement on a quiet machine with values of about 250
bytes and two indexes, and the figure in the Javadoc with its conditions
(keys, values, indexes).


## 3. What went well

* No wrong result, in each of two runs: about 15 million values and index
  entries compared in full and 78,000 logged reads compared at their
  lookup times, through a crash, a clean restart, past times, budgets of
  4 and 64 MB and heaps of 384 and 512 MB; 0 self-check failures and 0
  errors in 2.3 million gets, 28,000 pages and 3,500 index queries (run
  1).
* The crash: the frozen lookup time of the first read after the start was
  exactly the time of the last transaction that the start kept, as
  `setLookupTime()`'s Javadoc implies. 11 transactions (81 entries) were
  lost, all committed in the 43 ms before the halt and after the last
  returned `sync()`; every other one was there, and the state at B agreed
  in every product, attachment and index entry (run 2: 12 transactions,
  65 entries, the last sync at B itself). The 35,500 logged reads
  of `load1` agreed with the oracle.
* Past times: after a restart and 1.1 million later writes, the whole
  state at B, read at B, agreed in all 885,095 products, 1,200 attachments
  and every `by-cat-price` entry; `by-supplier` before its creation
  refused with "No index named 'by-supplier' at the lookup time."
* Eviction keeps a database of 2 million keys and 4.9 GB in a bounded
  heap: level for 20 minutes of writers and readers, 23 to 42 MB at a
  startup distance of 5 MB. `setCacheSizeInMb()` at run time took effect
  at once (U4-1's index scan, 4 times faster at 64 MB).
* An index built while three writers wrote agreed in all 1,982,792
  entries, after the build and after the restart.
* `close()` after a `sync()` returned at once; a start in too small a heap
  is a clean `OutOfMemoryError` from `start()`.
* The Javadoc was enough to write the application: frozen lookup times,
  `startAt()` with `inclusive(false)` and `backward()`, the index grammar,
  `transactionInfo()`, the job's states.


## 4. Fixes

Made 2026-11-09 for coord-1109, in `clone-x25`, by the rule for 2026.4: the
Javadoc made true and complete where the code is as designed; no new API and
no change of meaning. One commit, `e91238f`, after those of 020-24-05
(`b81232f`, `084069b`; its section 4); the three gated on one tree under the
gate lock: BEFORE COMMIT OK (145 s, unit 1577, f 86), JAVADOC PUB OK.

* **U4-1** (`e91238f`): `DatabaseBuilder.cacheSizeInMb()` says that a budget below
  what the database must keep (the nodes changed since its startup position,
  about 2 to 3 times the startup distance of heap) slows it down by design:
  each commit ends with a batch of eviction, and a reader's load waits for
  the eviction thread, at most 2 ms, so that reads go at eviction's pace
  while anything is written; a useful budget is well above it.
  `Database.setCacheSizeInMb()` points there. The design questions of 2.1
  (raise a budget below the pinned bytes; the readers' gap as a fraction of
  the pinned bytes) are for Frans.
* **U4-2** (`e91238f`): `startupDistanceInMb()` says that the startup distance, not
  the budget, sets the heap, and that a start needs about twice the startup
  distance more (019-45), with this app's figures: at 50, 110 to 160 MB after
  a start, refused in 256 MB, ran in 384 MB; at 5, 21 to 42 MB, ran in 96 MB.
  Checked against 006-19 (what must be kept: about the startup distance in
  stream bytes, 2 to 2.5 times that in the heap) and docs/levels.md, section
  7 (up to 2.9 times in stream bytes at 50 MB; a start's peak 3.3 to 4.9
  times the startup distance).
* **U4-3** (`e91238f`): `IndexBuilder.start()` says that a build is paced (steps of
  at most 25 values or about 1 MB, a pause of half each step's time, at most
  a second; 020-10, section 6.1) and its loads paced as other reads;
  `JobStatus.count()` is its progress without a total.
* **U4-4**: new API (a resume point for an index scan's pages), for Frans's
  list; not done.
* **U4-5** (`e91238f`): `UsePrimaryBuilder` and `UseIndexBuilder` say that an
  iterator holds nothing to release, and may be dropped. Test
  `testDroppedIteratorsHoldNothing`: reclaim cuts past the lookup time of
  400 iterators read in part.
* **U4-6** (`e91238f`): the Javadoc's 0.6 and 1.4 s were measured on 2026-10-13,
  before eviction, with 100,000 and 1 million keys, single puts, the stream
  in the OS's cache (011-04); it now says so, with 006-19's 3 to 5 s at 10 to
  50 million keys. Not changed from this app's loaded runs. To measure, in a
  quiet block: a cold and a warm start at the default 50 MB of a database of
  2 million objects of about 250 bytes with two indexes, against the
  Javadoc's figures.
