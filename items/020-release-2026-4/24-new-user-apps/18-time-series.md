# 020-24-18 Time series with retention

Created 2026-11-09 by Frans Lundberg.

A new user of 2026.4 writes the metrics store of an embedded monitoring agent (u18, for
coord-1109, round 6 of the common brief of 020-24). The agent stores one sample a second
from each of many sensors, makes minute and hour rollups, deletes raw samples itself once
they are rolled up, and sets a retain duration. Its dashboards read the latest state and
earlier states ("what did the dashboard show 10 minutes ago"). The questions were these.
Does the retain duration keep its promise? How large does the directory grow against the
live data? Does such a time series meet the new known issue of releases/next.md, "Reclaim
stops cutting a log keyed by time" (021-25), and does the note let a user recognise it?

The class path held only the frozen release candidate's `night/candidate/bergdb-release.jar`
(`d00096e`, buildinfo `2026.4-dev`, release int 264). The documentation was read in a clone
of the candidate's repository at `d00096e`: README.md, `java/src/overview-pub.html`, the
Javadoc comments of `bergdb.pub` and `bergdb.pub.util`, and releases/next.md. Item 021-25
was read only after the observations of U18-1 were made, and no implementation code was
read. Stack frames were sampled once, to tell where a run spent its time. Nothing in
BergDB was changed. F53 was loaded by other sessions (load 6 to 14), so the wall times are
rough.


## 1. The application

Everything is in `/Users/f/fl/bench/2026-11-09/app-u18/`: the app in `app/`, and the
outputs of the runs in `data/` (`*.out`, a `*.csv` row every simulated minute, and
`*.jumps.csv` for each tick that grew the directory by more than 1 MB).

* `TimeSeriesApp.java`, 640 lines, plain javac and java. Its main runs a whole scenario,
  checks every result against an oracle, and exits non-zero on a wrong result:
  `java -cp bergdb-release.jar:classes TimeSeriesApp DIR layout=sensor mode=batch del=each
  hours=12`.
* `Repro.java`, 70 lines: the minimal reproduction of U18-1.
* `runs.sh` runs the configurations one after another, one JVM at a time, and removes each
  database directory after its run.
* `CrashCheck.java` and `crash.py`: a kill -9 of the time-ordered workload while one of
  its large records is written, then a check of the restarted database (section 3).

How the app uses BergDB:

* **Clock.** The database runs on an application `Clock` (`DatabaseBuilder.clock()`), a
  volatile long that the program sets to second k at tick k. A tick takes 1 to 3 ms of
  wall time with its dashboards, so 24 simulated hours ran in 4 minutes. The simulated day starts at
  2026-11-09 00:00 UTC.
* **Writes.** There are 50 sensors, with one sample per sensor per second as an 8-byte
  `byte[]`. About 1 in 97 samples is missing, as a sensor sometimes is. A raw sample is
  deleted 15 minutes after it is written. Three settings vary:
  * `layout`. With `sensor`, the keys are `/raw/sNNN/<epoch second>.bin`: a directory per
    sensor, so 50 FIFOs side by side. With `time`, they are `/rt/<epoch second>-sNNN.bin`:
    one directory in time order. `ring` is the control: `/ring/sNNN/<second mod 900>.bin`,
    a ring of 900 slots per sensor, overwritten in place, with no deletes. The value holds
    the second and the sample.
  * `mode`. With `batch`, one `w()` transaction per second holds all sensors' puts and
    deletes. With `single`, each sample is its own transaction of one put and one delete.
  * `del`. With `each`, a sample is deleted at the tick 15 minutes after its own. With
    `minute`, a whole minute of raw samples is deleted in the minute rollup's transaction.
* **Rollups.** At each minute, the app scans the minute's raw samples with
  `usePrimary(byte[].class).dir(..).startAt(..)` and puts a `Rollup` Data Object (min, max,
  sum, count) for each sensor at `/m1/sNNN/<minute>`. The rollup of the minute 180
  minutes back is deleted. At each hour, the app scans the hour's 60 minute rollups and
  puts `/h1/sNNN/<hour>`.
* **Retention.** `setRetainDuration(Duration.seconds(1200))`, 20 minutes, with startup
  distance 5 MB, the smallest, as an embedded agent would choose.
* **Dashboards.** A panel of one sensor shows the raw samples of the last 5 minutes, the
  last 60 minute rollups, and the newest hour rollup (`backward()`). It also checks
  `exists()` of the raw sample deleted last and of the oldest one kept. The app reads a
  panel through a second connection (`newConnection()`, `setLookupTime()`):
  * every 10 ticks at `Time.MAX`;
  * every 7 ticks at a random past time within the retain duration;
  * every minute at exactly 10 minutes back;
  * every 50 ticks at a time 1 to 3 retain durations back, where a refusal is allowed.

  A past lookup time is the middle of tick k, k s + 0.5 s. Every transaction of tick k
  has a time in [k s, k s + 0.5 s), which the app checks with `Transaction.getTime()`.
* **Oracle.** A sample is a pure function of sensor and second (splitmix64 and
  `StrictMath.sin`), and the times of writes and deletes follow from the tick, so the
  state at the end of any tick is known without the database. The app computes each
  panel from that, independently of what it read, and compares.
* **The promise.** After every tick the app checks `getFirstAvailableLookupTime() <=
  currentTime() - retain`: the Javadoc guarantees "lookups work for every time in [now -
  retain duration, now]". It also checks that the time never moves back. A read within the
  retain duration must not throw `LookupTimeNotAvailableException`. An older one gives the
  right panel, or that exception with a lookup time before the first available time.
* **Restart.** In the middle of each run the database is closed and started again with
  `open()` on the same clock. The app then checks the retain duration (kept in the stream),
  the first available time (unchanged) and a panel.
* **Measurements.** After every tick the app sums the sizes of the directory's files,
  counts the live bytes of its model (keys' UTF-8 and values' logical bytes, 1.8 to 2.0 MB
  in every run), and times each tick's writes and rollups.


## 2. The findings

| ID | Kind | Severity | What |
|---|---|---|---|
| U18-1 | bug, known | high   | A metrics store meets the known issue of 021-25 within an hour |
| U18-2 | doc        | high   | The known issue's note does not let a time-series user see it  |
| U18-3 | doc        | medium | `setRetainDuration()`'s size on disk has no word of U18-1      |
| U18-4 | API        | low    | No way to see the stream's size or reclaim's progress          |
| U18-5 | API        | low    | A primary scan has `startAt()` but no end                      |
| U18-6 | doc        | low    | `clock()` names only `TestClock` and testing                   |
| U18-7 | API        | low    | `StartupInfo` has no `toString()`                              |

Each finding's section gives its reproduction, or the text that it cites.

No wrong result. Over 12 runs and 140 simulated hours, all checks held. There were 50,400
reads of the latest state and 80,274 reads at past times within the retain duration (8,280
of them exactly 10 minutes back), and every one matched the oracle. None was refused. Of
9,528 reads older than the retain duration, 7,135 were right and 2,393 were refused, each
before the first available time. At each of 504,000 ticks the first available time was at
most now - retain, and it never moved back. Over 12 restarts, the retain duration and the
first available time were kept. Two kills of the JVM while a large record of U18-1 was being
written lost nothing that had been synced (section 3).

### U18-1, bug (the known issue of 021-25), high: a metrics store meets it within an hour

Reclaim falls behind, and in the time-ordered layout it stops cutting after the first cut.
The directory then grows without a bound, about 70 to 100 MB of stream per simulated hour,
with 1.8 MB of live data. Single commits take seconds. In the table, "Cuts" counts the moves
of the first available time, "Last cut" is in simulated hours, and "Back at most" is the
largest distance from now back to the first available time, with 1,200 s retained.

| Run | Layout, mode, del | Hours | Transactions | Cuts | Last cut | Dir at end | Back at most |
|---|---|---|---|---|---|---|---|
| b   | time, batch, each        | 12 | 43,930    | 1  | 0.91  | 1,188 MB | 41,140 s |
| f   | time, single, each       | 6  | 1,079,790 | 1  | 0.76  | 942 MB   | 20,050 s |
| a2  | sensor, batch, each      | 24 | 87,862    | 18 | 20.70 | 820 MB   | 14,132 s |
| c   | sensor, single, each     | 12 | 2,160,048 | 17 | 11.01 | 390 MB   | 7,106 s  |
| e   | sensor, batch, minute    | 12 | 43,930    | 9  | 11.84 | 402 MB   | 13,353 s |
| d   | ring, batch, no deletes  | 12 | 43,930    | 26 | 11.85 | 150 MB   | 3,407 s  |
| g   | ring, single, no deletes | 12 | 2,160,730 | 29 | 11.89 | 153 MB   | 3,345 s  |

(Run a, sensor/batch/each for 12 hours, is the first 12 hours of a2 cut for cut.
Run b2 is b for 8 hours, with the jumps logged. Its wall time, 475 s, went mostly to the
app's own past-time scans of 15,000 keys in the time layout, which read old index nodes
from the stream; five stack samples of the main thread were all there. A tick's time below
covers its writes, and at a minute its rollup, not the dashboards.)

* **Keys in time order (b, b2, f).** One cut, at 0.91 simulated hours in b (about 3,300
  transactions) and 0.76 in f (about 135,000), with 90,000 to 117,000 keys deleted by then.
  After that there was no cut in the remaining 5 to 11 hours. The directory grows
  steadily, and some single ticks add much more. These are run b2's ticks that grew the
  directory by more than 4 MB. Each is one transaction of 50 puts and 50 deletes, but for
  4.33 h, a minute's tick with its rollup's transaction too:

  | Sim h | Growth   | Tick     |
  |---|---|---|
  | 0.96  | 4.2 MB   | 57 ms    |
  | 1.27  | 7.8 MB   | 126 ms   |
  | 1.74  | 22.6 MB  | 297 ms   |
  | 2.65  | 44.1 MB  | 715 ms   |
  | 4.33  | 91.6 MB  | 2,763 ms |
  | 7.44  | 17.4 MB  | 3,225 ms |
  | 7.44  | 148.6 MB | 2,496 ms |

  So the large record roughly doubles at intervals that roughly double. The slowest tick
  of b2 took 4,189 ms (an hour's tick), and 7 ticks took over 1 s. In f, a tick of 50
  transactions of 1 put and 1 delete each took 4,181 ms and grew the directory by 127 MB.
  The ticks were not timed transaction by transaction; `Repro` times single transactions,
  1.0 and 1.35 s. For an agent that samples every second, a commit of seconds is a gap in
  its data.
* **One directory per sensor (a2, c, e).** Reclaim goes on cutting, and each cut puts the
  first available time about 1,210 to 1,260 s back, as it should. But the gap between cuts
  grows nearly linearly over the run: 0.2 to 0.3 h in hour 1, 1.2 h at 7 h, 2.0 h at 12 h,
  and 3.6 h at 21 h. The directory's peak before a cut grows with it: 46, 113, 206, 304,
  419, 589 and 726 MB. The stream is written at a steady 75 MB per hour, so the directory
  grows without a bound, more slowly than with time order. The writes slow down as well.
  In a2, the slowest tick of each hour went from 31 ms in hour 0 to 796 ms in hour 23, and
  242 ticks took over 100 ms. The wall time of half a simulated hour went from about 1.2 s
  to 27 s. Deleting a minute at a time (e) is worse than deleting each sample at its own tick
  (a): 9 cuts against 15 in 12 hours, and 493 MB at most. A transaction per sample (c),
  2.16 million transactions, behaves like batch (a).
* **Ring, no deletes (d, g).** The control stays bounded: a cut about every 0.5 h, the
  directory between 71 and 266 MB after the third hour with no growth over 12 hours, and
  no tick over 41 ms. The workload is the same but for the deletes. So the cause is the
  deletes of keys in key order, as 021-25 says. Its parts 1 and 2 fit: a touch passes every
  key deleted since its iteration began. In time order that is one long run of keys, which
  grows faster than an iteration can finish. Per sensor it is 50 shorter runs, so each
  iteration takes longer than the last.
* **The default startup distance, 50 MB (runs h, i and j, 6 to 12 hours).** These runs
  are too short to tell. Reclaim is paced by twice the startup distance, so even the ring
  cut only once, at 7.9 h, after about 214 MB of stream. That is what `setRetainDuration()`
  says: nothing is cut "after about 200 MB of puts with the default 50 MB". The
  time-ordered run had not cut by 6 h (372 MB), and the per-sensor run cut 3 times (419 MB
  at most). So an agent that keeps the default keeps hours readable, not 20 minutes, and
  150 to 250 MB on disk for 2 MB of data, as documented, before U18-1 begins to show.
* **Records of 1 to 3 MB** come in every run, the ring too: 360 to 738 ticks over 1 MB, the
  largest 2.6 to 3.2 MB. So in these workloads they are reclaim's normal steps, not a sign
  of the issue.
* **The data stays right**, as the note says: every read matched the oracle, and the
  promise held throughout. "Back at most" only grows: the retain duration is a lower bound.

Reproduction, 11 s on F53: `java -cp bergdb-release.jar:classes Repro DIR time 5` (the app
directory's `Repro.java`). It writes 50 time-ordered keys a second, deletes each 15 minutes
later, retains 20 minutes, and uses startup distance 5 MB. It printed:

    sim  1.0 h: first available   1534 s back (retain 1200 s), directory    76.8 MB
    sim  2.0 h: first available   5134 s back (retain 1200 s), directory   179.4 MB
    sim  3.0 h: first available   8734 s back (retain 1200 s), directory   293.7 MB
    sim  4.0 h: first available  12334 s back (retain 1200 s), directory   363.9 MB
      sim 14982 s: one transaction took 1049 ms
      sim 14983 s: one transaction took 1354 ms
    sim  5.0 h: first available  15934 s back (retain 1200 s), directory   518.8 MB

`Repro DIR sensor 24` gives the per-sensor layout, in 43 s. Its cuts came at about 1.9,
3.3, 5.0, 7.7 and 14.7 h, at gaps of 1.4, 1.7, 2.7 and 7 h. The first available time was
33,339 s back at 24 h, and the directory 1,608 MB. That is worse than the app's a2, whose
rollup keys are in the stream too. The whole app: `TimeSeriesApp DIR
layout=time hours=8` (b2), `layout=sensor hours=24` (a2), `layout=ring hours=12` (d).

### U18-2, doc, high: the note does not let a time-series user recognise the issue or act

The note ("Known issues and limits") describes 021-25's FIFO. A user with a time series
would not see their own case in it:

* "after some 200,000 transactions". Here, with keys in time order, the last cut came at
  0.8 to 0.9 simulated hours: after 3,300 transactions of 100 keys (b), or 135,000 of 2
  (f). What counted was the deleted keys, not the transactions: batch and single runs
  behave alike, with 44,000 or 2.16 million transactions in 12 hours. Name the
  deleted keys (about 100,000 to 200,000 before the cuts stop), or the time: "within hours".
* "each transaction putting a new key and deleting an old one (a FIFO, such as an audit
  log)". That reads as one put and one delete per transaction. Transactions of many puts
  and deletes meet it too, and so do many FIFOs side by side, one directory per sensor.
  There reclaim does not stop cutting; it falls behind more with every iteration, which the
  note does not mention.
* "a record of 1 to 4 MB". Records of that size come in the healthy ring as well. With keys
  in time order they grew to 149 MB, and a tick with one such commit took 2.5 to 3.2 s.
  The note says nothing of commit times.
* No symptom to check. A user can watch `now - getFirstAvailableLookupTime()` against the
  retain duration. Here it stayed below about 3 times the retain duration while reclaim
  kept up (the ring: 3,407 s at most for 1,200 s), and reached 6 to 34 times when it did
  not. The directory's size against the live data shows it too.
* No advice. In these runs, overwriting a fixed set of keys in place (a ring), instead of
  new keys and deletes, kept the directory bounded. Other possible advice: when the
  directory passes a limit, copy the live data to a new database. Or keep the time order
  out of the keys (021-25's hashed keys still cut, with a larger stream).

### U18-3, doc, medium: `setRetainDuration()` promises a size on disk with no word of U18-1

`Database.setRetainDuration()`'s "What stays on disk" says the stream within the retain
duration plus one or two iterations, and "the retain duration bounds what stays readable,
not the size on disk". Database's "The files" says "with a finite retain duration the
stream holds several times the live data". A reader of the Javadoc, who does not read
the release notes, expects a bounded directory. A time series with deletes, the common
case for a retain duration, gets 180 to 660 times its live data after 12 hours, and
growing. One sentence there, pointing at the known issue, would do.

### U18-4, API, low: no way to see the stream's size or reclaim's progress

The only signs available to a user are `getFirstAvailableLookupTime()` and a listing of the
directory's files. Neither tells "an iteration is running and will cut" from "stuck".
`getStartupInfo()` gives only the start's duration. A call that gives the stream's length,
or reclaim's last cut and its iteration's start, would let an agent alarm on U18-1.

### U18-5, API, low: a primary scan has `startAt()` and no end

Each time-range query, such as a 5-minute window, a minute's raw samples or an hour's
rollups, reads from `startAt()` and breaks out of the loop by parsing each key. A scan
reads a page of up to 100 keys and values (`UsePrimaryBuilder`), so each query reads up to
99 entries past its end. An `endAt(name, inclusive)` would fit range queries, which a time
series makes all the time.

### U18-6, doc, low: `clock()` names only `TestClock` and testing

`DatabaseBuilder.clock()` says "Use this method together with a TestClock to do
deterministic testing". The app used a `Clock` of its own, as `Clock`'s Javadoc allows,
and it worked. Reclaim followed it: the first cut came at the simulated time that
`setRetainDuration()` predicts. The method does not say that an application's clock is
supported outside tests, or that reclaim's pacing ("a quarter of the duration has passed")
is measured on it. A sentence would help a user who simulates or replays time.

### U18-7, API, low: `StartupInfo` has no `toString()`

`System.out.println("startup " + db.getStartupInfo())` printed
`bergdb.pubimp.StartInfoImp@643b983a`: a class name outside the API and a hash.
`getStartupDuration()` is its only getter.


## 3. What went well

* **The retain promise held**, in every layout and also while reclaim was stuck. All the
  reads above were right or refused as documented, never wrong, and the first available
  time was kept over each restart. `LookupTimeNotAvailableException` came only for times
  before the first available time.
* **An application clock** through `DatabaseBuilder.clock()` made it possible to test
  retention over a simulated day in minutes. The transaction times were the clock's, as
  `Clock` documents. Reclaim's pacing matched `setRetainDuration()`'s Javadoc: the first cut
  came at 0.88 h, after the stream had grown by more than four times the startup distance
  and the retain duration had passed, and it put the first available time 1,254 s back.
* **Data Objects for rollups** and **primary scans** with `startAt()` and `backward()` made
  the dashboards short to write. The newest hour rollup was one `backward()` iterator.
* **Earlier states with `setLookupTime()`** on a connection of its own
  (`newConnection()`) gave "the dashboard 10 minutes ago" exactly, 8,280 times.
* **A crash in a large record.** `CrashCheck` writes the time-ordered workload with a
  `sync()` after each second. `crash.py` kills its JVM with SIGKILL when the directory grows
  by more than 5 MB in 0.1 s, at 4.10 simulated hours, while the record of about 90 MB is
  written. The kill came 10 MB into the record in one run and 46 MB into it in the other.
  Both starts recovered the database at the last synced second, 14,761. All 45,000 live keys
  and 38 earlier states matched the oracle. Another 600 seconds were written, and the
  database was closed and started again. The start took 0.5 s after the earlier kill and
  3.1 s (startup duration 3.07 s) after the later one, at startup distance 5 MB. That is
  likely the cut tail of the large record, read at the start; it was not looked into.
* **Restarts** of a database of 145 to 600 MB took 0.2 to 0.7 s
  (`getStartupDuration()`), with startup distance 5 MB.
* **The Javadoc of reclaim** (`setRetainDuration()`, `getFirstAvailableLookupTime()`)
  explains when cuts happen, what stays on disk, and that the first available time moves
  only at commits. It answered every question the app raised except U18-1.
