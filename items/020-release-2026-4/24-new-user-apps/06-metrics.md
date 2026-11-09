# 020-24-06 A metrics service with expiring history

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u6, for coord-1109, by the
common brief of 020-24, round 2): only the release jar on the class path, and only what a
user reads (README.md, `java/src/overview-pub.html`, the Javadoc of `bergdb.pub` and
`bergdb.pub.util`, `releases/next.md`). The jar was built from a clone of main at
`cf287ad`. The implementation was read only afterwards, to explain U6-1 and U6-4.


## 1. The application

A metrics service: many sensors write small values at a high rate, readers ask for the
current values and for the values at past times, and the history expires after a retain
duration of 3 s, so that reclaim cuts the stream many times in each run. `MetricsApp.java`
(1,610 lines) holds the application and its checks, in
`/Users/f/fl/bench/2026-11-09/app-u6/app/`, with `run.sh`, which runs eight JVMs one after
the other on one database and prints `APP OK` when every step passes; the output of the last
full run is `run.txt` there. `crash-loop.sh` repeats the crash and the recovery
(`crash-loop2.txt` and `crash-loop3.txt`, 17 rounds). The probes and the minimal
reproductions are in `/Users/f/fl/bench/2026-11-09/app-u6/probe/`.

How it uses BergDB:

* 2,180 keys. 800 fast sensors, one `put()` of a Data Object `Sample` per sample at
  `/cur/fNNNN`; 1,000 batch sensors, 50 samples per `w()` transaction, each batch synced
  with `tx.sync(SyncLevel.ORDINARY)`; 200 raw sensors, 16 bytes at `/raw/rNNN.bin`; 40
  slow sensors, every 0.5 to 8 s, each with a `Status` object at `/status/sNN` in the same
  `w()`; 100 idle sensors written once, half of them rewritten and then deleted a third into
  the first phase. A full run writes about 25 million samples, some 90,000 a second.
* `Database.setRetainDuration(3 s)` and a startup distance of 5 MB; a user index
  `by-state` of `/status/` on the string field `state`.
* Sync: a syncer thread calls `Database.sync()` every 250 ms; the batch writer syncs each
  batch (an acknowledged ingest); the other writers never sync.
* Readers: gets, `exists()` and index scans at times near the cut (the first available
  lookup time less 10 ms, 1 ms and one unit, the time itself, plus one unit, 1, 10 and
  100 ms, and random times up to now), with `transactionInfo()`; current values
  (`freezeLookupTime()`, a get, then `getLookupTime()` gives the time read at); a frozen
  reader that lists `/cur/` and `/raw/` (`usePrimary()`) every 200 ms at one frozen time
  until it is refused, a third of the listings slow (about 10 s each); a history reader
  that walks a sensor's versions newest first, by `transactionInfo().time()` less one unit;
  and the size of the `*.bergdb` files each second.
* The oracle knows each write's time (`Transaction.getTime()`) and seq; a value is a
  function of its key and seq, so each value read tells its seq and is checked in full. A
  read at a time after the last recorded write of its key waits until the oracle is sure.
* What it checks, and exits with 1 on a wrong result: each value against the oracle; a
  `LookupTimeNotAvailableException` only for a time before the first available lookup
  time, as read before the read, or overtaken by the cut during it, and never for a time
  within the retain duration of now; the first available lookup time never moves back and
  is never after now less the retain duration; a current read is never older than a write
  that had returned; `transactionInfo()`'s time and KVs; the index's listing; after each
  start the settings, every key's current value and past states; after each crash, the
  writes before the last sync, a prefix of the rest, and `transactionInfo()` of the last
  four versions of each key against the journal; the size on disk after the first cut.
* The steps, one JVM each: phase 1 (40 s, creates the database); phase 2 (30 s, after a
  restart); twice a crash (writes with a journal of each write and a mark after each sync,
  and halts the JVM at a random time) and a recovery (checks the database against the
  journal, then 20 s more); the retain duration changed while writing (3 s, 10 s, 3 s,
  `Duration.MAX`, 3 s); phase 3 (20 s). About 5 minutes.

The probes: `ReclaimProbe` (when reclaim cuts, by startup distance and write rate),
`LargeLiveProbe` (a million idle keys), `ClockStepProbe` (the clock stepped back and
forward), `SettingHaltProbe`, `CloseUnderLoadProbe`, and `TiRepro`, `TiAgeProbe` and
`TiProbe` for U6-1.


## 2. The findings

Most severe first. A reproduction names a file in `probe/`, or the application.

| ID    | Kind | Severity | What                                                | Reproduction        |
|-------|------|----------|-----------------------------------------------------|---------------------|
| U6-1  | bug | medium | `transactionInfo()` refuses a fresh transaction     | TiRepro             |
| U6-2  | doc | medium | when reclaim cuts and the disk size: not said       | ReclaimProbe        |
| U6-3  | doc | low    | `setRetainDuration()` lost in a crash before sync   | SettingHaltProbe    |
| U6-4  | doc | low    | first available time moved back over a crash        | the app             |
| U6-5  | doc | low    | a read after `close()` throws a `bergdb.core` class | CloseUnderLoadProbe |
| U6-6  | doc | low    | `get()` and `exists()` omit LookupTimeNotAvailable  | the Javadoc         |
| U6-7  | doc | low    | before the first cut, the first available is 1970   | the app             |
| U6-8  | doc | low    | retain is in database time; a clock stepped back    | ClockStepProbe      |
| U6-9  | API | low    | no history of a key; the app stores "last seen"     | the app             |
| U6-10 | doc | low    | no advice on sync for a high-rate writer            | the app             |

Two suspected bugs were the application's own errors. After a crash, `transactionInfo()` of
some recovered values seemed to name a transaction a few milliseconds after the one the
journal held for the value: those values had been written after the journal's last flush,
and the check took the time of the last journaled write at or before the lookup time. On a
copy of the crashed database every version agreed with the journal, and a check by the
value's seq found none wrong in 28 crashes. And the first available lookup time
seemed to move back 756 ms within a run: two threads read it, and the one with the older
read compared it after the other had recorded the newer one; `Reclaim` sets it only at the
start and at a cut, to a later iteration's end.

### U6-1. transactionInfo() refuses a fresh transaction that nothing has cut (bug, medium)

With a finite retain duration, `Connection.transactionInfo()` throws
`LookupTimeNotAvailableException` "No available transaction info: reclaim has rewritten the
value, and the transaction that wrote it is no longer available." for values written
milliseconds before, well within the retain duration, and before any cut:
`getFirstAvailableLookupTime()` is still 1970-01-01. The transaction is there: the same
call after a get at the value's own write time gives it, with the right time. The data is
right in every case; only the call is refused.

Reproduction, `probe/TiRepro.java`, in memory, deterministic:

```java
try (Database db = Factory.database().memory().startupDistanceInMb(5).start()) {
    db.setRetainDuration(Duration.seconds(60));
    Connection c = db.connection();
    Time written = c.put("/sensor/a.txt", "21.5").getTime();
    byte[] filler = new byte[1000];
    for (int i = 0; i < 20_000; i++) c.put("/fill/k" + (i % 100) + ".bin", filler);  // 0.45 s
    c.get("/sensor/a.txt", String.class);   // "21.5"
    c.transactionInfo();                    // throws LookupTimeNotAvailableException
    c.setLookupTime(written);
    c.get("/sensor/a.txt", String.class);   // "21.5"
    c.transactionInfo().time();             // = written
}
```

`getFirstAvailableLookupTime()` gives 1970-01-01 throughout. `TiAgeProbe` (one thread, a put
of a small String at 1,000 keys in turn, a get of a random key and `transactionInfo()` after
each put): with retain 3 s and 60 s alike, 79 refusals (startup distance 50 MB) or 170 (5
MB), all for values 7 to 69 ms old, all before any cut, in one burst at about one startup
distance of stream; with retain `Duration.MAX` (`TiProbe`), none in 1.7 million calls. In
the application, phase 1 of the last run had 2,153 refusals before the first cut and 3,426
after cuts began for transactions inside the retain duration (written 0.4 to 3.0 s before,
retain 3 s). Every idle sensor's `transactionInfo()` at the latest state is refused from the
first reclaim iteration on (50 of 50 at the end of each step), though nothing was cut there.

Why it matters: `Connection.transactionInfo()`'s Javadoc names the case ("reclaim has
rewritten the value, in a transaction of its own, so that the transaction that wrote it
can be cut"), but a user reads it as the fate of old values about to be cut, not of a
value 10 ms old with a retain duration of a minute. The exception's own Javadoc says it is
thrown "when a read needs data that reclaim has removed", the message says the
transaction "is no longer available", and `getFirstAvailableLookupTime()` advises to retry
with a later lookup time: here nothing was removed, the transaction is available, and a
later lookup time never helps (it finds the copy again); only an earlier one, which the
user does not know, would. A metrics service cannot ask when an idle sensor last reported,
and a walk back through a sensor's versions (U6-9) stops inside the retain duration.

Why, read afterwards: `Reclaim`'s class comment. An iteration starts when the stream has
grown by twice the startup distance and a quarter of the retain duration has passed; a
step rewrites each value that is live at the iteration's start and stored before its cut
point, which for the first iteration is its own start, so a value written a moment before
is rewritten; the cut comes only when the iteration's end is older than the retain
duration. `ConnectionImp.transactionInfo()` throws for any record with a KV under
reclaim's prefix, so from the step on every lookup time finds reclaim's copy and is
refused, long before the original record can be cut. A fix could give the original
transaction while it is not cut (the copy could name it), or the Javadoc could say what
happens and when, and the exception's message that the transaction may still exist.

### U6-2. When reclaim cuts and how large the disk gets is not said (doc, medium)

`Database.setRetainDuration()` says that reclaim rewrites live values and cuts the front of
the stream, and gives write and store efficiencies; `DatabaseBuilder.startupDistanceInMb()`
speaks of startup time only. Nothing tells a user when the first cut comes, what the
startup distance has to do with it, or how large the database gets on disk. Measured
(`ReclaimProbe`, small objects, retain 3 s):

* startup distance 5 MB, 20,000 writes a second (3.5 MB/s of stream): the first cut after
  about 8 s; then 22 to 31 MB on disk;
* the default, 50 MB, at the same rate: no cut for 55 s, 184 MB on disk before it; then
  about 100 MB;
* 50 MB, as fast as one thread writes (about 35 MB/s): 200 to 340 MB;
* the application (5 MB, about 18 MB/s): 29 to 120 MB, and 30 to 43 MB with retain 1 s;
* 1,000,000 idle keys (92 MB written) and fast writes at 1,000 keys (`LargeLiveProbe`):
  750 to 1,100 MB, the first available time 3 to 17 s behind now.

So the size on disk in steady state is a few times the startup distance plus a few times
the stream written within the retain duration, plus the live data several times; and at a
modest rate, such as 2,000 samples a second, a retain duration of 3 s with the default
startup distance would not cut for many minutes. Reading `Reclaim` afterwards gives the
rule (U6-1): an iteration starts after twice the startup distance of growth and a quarter
of the retain duration. One paragraph in `setRetainDuration()` with that rule and the
order of the size on disk would let a user choose the two settings.

### U6-3. setRetainDuration() is lost in a crash before a sync (doc, low)

`SettingHaltProbe`: a database with retain 3 s and startup distance 5 MB, synced and
closed; a JVM opens it, calls `setRetainDuration(7 s)` and `setStartupDistanceInMb(9)`,
and halts itself. Halted at once, 3 of 3 restarts had 3 s and 5 MB again; halted after
100 ms or 2 s, they had 7 s and 9 MB. That is as for any transaction, and expected, but
the Javadoc says "a restart keeps the value" and "The new value is in force when the
method returns", without the sentence that `IndexBuilder.start()` and `deleteIndex()`
have: a crash before it is durable (`sync()`) can undo it. For an increase, made to keep
history longer, a crash undoes it and reclaim then cuts what the user meant to keep. The
same holds for `setStartupDistanceInMb()`.

### U6-4. The first available lookup time moved back over a crash (doc, low)

In 1 of 31 crashes, the first available lookup time after the recovery was 792 ms before
the one the crashed JVM had read 15 ms before its halt (`recover3-1.txt`). 2,000 reads at
times in that gap all gave the right values, so nothing was lost; but
`getFirstAvailableLookupTime()` says "The time only moves forward". Read afterwards:
`Reclaim.pretruncateIfPossible()` sets the first available time when it decides a cut,
before the table that marks the cut is durable, and the stream is cut only after that
(`cutIfDurable()`); a crash in between brings back the time before. The Javadoc could say
"in a run", or the time could move when the cut is durable.

### U6-5. A read after close() throws an exception of bergdb.core (doc, low)

`CloseUnderLoadProbe`: `close()` while a writer and three readers run. Each thread's next
call throws `bergdb.core.DbStoppingException` ("Cannot call getOne() while DB is
stopping.", "Cannot call execute() while DB is stopping."): an `IllegalDbStateException`,
so a catch works, but of a package that is not API, with a message that names an internal
method. `Connection.put()` lists `IllegalDbStateException` for a stopping database;
`get()`, `exists()` and the scans do not. Every write that returned before `close()` began
was there after a restart.

### U6-6. get() and exists() do not list LookupTimeNotAvailableException (doc, low)

`Connection.get()`, `exists()` and `ReadInterface` do not name the exception in their
`@throws`, though it is the usual result of a read near the cut; `setLookupTime()`,
`transactionInfo()`, `useIndex()` and `UsePrimaryBuilder` do. It extends
`IllegalArgumentException`, so code that catches `IllegalArgumentException` for a bad key
catches an expired lookup time too; worth a word.

### U6-7. Before the first cut, the first available lookup time is 1970 (doc, low)

`getFirstAvailableLookupTime()` gives `1970-01-01 00:00:00` until reclaim first cuts, also
with a retain duration set: everything is readable, so it is right, but the Javadoc does
not say it, and a service that shows "history available: now less first" shows 56 years.
After a restart, the time stays where it was until writes resume, so a past state older
than the retain duration stays readable meanwhile (frozen times held up to 13 s with retain
3 s); that agrees with "minimum duration".

### U6-8. The retain duration is in database time; a clock stepped back (doc, low)

`ClockStepProbe`, a `Clock` stepped back 30 s, then forward 60 s, while 20,000 samples a
second are written. While the clock is behind, each transaction takes the next unit after
the last (as `Clock`'s Javadoc says): 20 s of writes took 0.04 s of database time, no cut
came for those 20 s, and the disk grew from 30 to 89 MB; the step forward then cut at once.
Every read near the cut was right. A metrics server meets such steps (NTP); the Javadoc
of `setRetainDuration()` could say that the duration is measured in the database's time,
so that a clock stepped back by s stops reclaim for s.

### U6-9. No history of a key; "last seen" must be stored by the application (API, low)

A metrics service wants a sensor's samples over the last seconds. The API reads a state at
a time, and has no listing of a key's versions; walking back by `transactionInfo().time()`
less one unit works, and in the application the median walk reached back 0.65 to 7.5 s
with retain 3 s, but U6-1 stops it inside the retain duration, and the walk costs a storage read
per version. "When did this sensor last report" needs a time in the value (U6-1). And the
retain duration expires old versions only, never current values: a service that keeps each
sample at a key of its own must delete them itself. The Javadoc implies it ("rewrites live
values"); one sentence in `setRetainDuration()` would say it.

### U6-10. No advice on sync for a high-rate writer (doc, low)

`SyncLevel` has `NONE` and `ORDINARY`; the Javadoc says a transaction is written "soon
after it returns" and `stop()` speaks of "the buffer time", with no value. For a writer of
100,000 samples a second a user wants to know what a sync costs and what is lost without
one. Measured here: of the calls of `Database.sync()` every 250 ms, the longest in a step
took 34 to 132 ms in the last run (350 ms once before); a synced batch about 6 ms (160
synced batches a second). In each of 36 crashes, every write before the last sync mark was
there, and so was every write after it that the journal held, as the halt of a process
leaves what was written in the operating system's cache; a power loss would not.


## 3. What went well

* No wrong value. The last full run checked about 136 million values against the oracle
  (gets, 1.9 million `exists()`, 681,000 index scans, 610 listings of 2,180 keys at frozen
  times, 11 million versions in history walks), at times near the cut and at the latest
  state, through restarts, two crashes and changes of the retain duration.
* Reclaim behaved as the Javadoc says: 8.0 million reads behind the cut were refused, 47
  were overtaken by a cut while they ran, none was refused within the retain duration of
  now, and the first available time never moved back within a run and was never after now
  less the retain duration. Frozen times were refused after 3.1 to 7.7 s with retain 3 s
  (up to 13 s after a restart, U6-7; 1.0 to 2.5 s with retain 1 s), never sooner; slow
  listings of 10 s were refused cleanly.
* Deleted idle sensors stayed deleted after reclaim rewrote and cut around them; idle
  values written once stayed right, also a million of them (`LargeLiveProbe`).
* The size on disk stopped growing: 40 to 140 MB in each step of the last run after the
  first cut, and back from 345 MB to about 95 MB within 4 s after the retain duration went
  from 10 s or `MAX` to 3 s.
* Retain changes as documented: an increase holds the first available time until the span
  reaches the new duration, `MAX` stops the cut, 0.5 s is refused.
* Restarts kept the retain duration, the startup distance and the first available time
  exactly; starts took 0.1 to 1.1 s.
* Crashes (`Runtime.halt`, 36 checked): every write before the last sync was there, the
  recovered state was a prefix of the writes, `transactionInfo()` of the last four versions
  of each key agreed with the journal (28 crashes), and the index was right.
* The Javadoc of `getFirstAvailableLookupTime()`, `setLookupTime()` and
  `freezeLookupTime()` was enough to write the readers' rules right the first time.
