# 020-24-01 An event log with time travel

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u1, for coord-1109, by
the common brief of 020-24): only the release jar on the class path, and only what a user
reads (README.md, `java/src/overview-pub.html`, the Javadoc of `bergdb.pub` and
`bergdb.pub.util`, `releases/next.md`). The jar was built from a clone of main at
`0a59cf3`. The implementation was read only afterwards, to explain finding U1-1.


## 1. The application

An audit log of a small shop: users and orders, and every change to them as an event.
`EventLogApp.java` holds the application and its checks; `EdgeProbes.java` what a user
would try beyond the Javadoc. Both are in `/Users/f/fl/bench/2026-11-09/app-u1/app/`, with
`run.sh`, which runs four JVMs one after the other and prints `APP OK` when every step
passes; the output of the last run is `run.txt` there. The minimal reproductions are in
`/Users/f/fl/bench/2026-11-09/app-u1/probe/`.

How it uses BergDB:

* Data Objects: `User`, `Order` (with a `String[]`), `Event` (with the `User` or `Order`
  after the change nested, and a `byte[]` attachment) and `Counter`.
* Each command (create, rename, deactivate or delete a user; create an order, pay, ship,
  deliver, cancel it, change its amount) is one `rw()`: it reads the current state, checks
  the command (a bad one throws from the action and writes nothing), puts the new state,
  appends the event at `/events/${transactionTime}` with key replace on, and steps the
  counter `/meta/seq`. Its outputs give the event's seq and the state after.
* Two user indexes: `events-by-entity` (the events of `/events/` by the field `entity`, an
  entity's history in time order) and `orders-by-state`.
* Queries: the state at any time T (`setLookupTime(T)`, primary scans of `/users/` and
  `/orders/`); the events between two times (a primary scan from `startAt()` the name of
  T0 to T1); the last 10 events as of T (backward); an entity's history through the index,
  now and at a past T; orders by state at a past T; who wrote a value
  (`transactionInfo()`); `freezeLookupTime()` for a consistent state of several reads.
* Sync: a payment waits for `tx.sync(SyncLevel.ORDINARY)`; the other commands do not;
  each phase ends with `Database.sync()` and `close()`.

What it checks, and exits with 1 on a wrong result:

* Phases 1 to 3 on a database in a directory, with a restart between them: 1,200
  commands, about 1,140 events. After each phase, about 120 states at past times (each a
  command's time and the unit before it) against an in-memory model; the state at a time
  rebuilt from the events alone against the state read; 30 time ranges; 20 histories; 10
  last-10s; 30 keys by `exists()`, `get()` and `transactionInfo()` at past times; 10
  index scans at past times. Phase 1's states, as SHA-256 digests, must read the same after
  each restart.
* Times a user tries: 1970, the unit after it, 2000, yesterday, the creation, the unit
  before the first event (all empty); `useIndex()` before the index existed; the future;
  `"-0.5 s"`; a frozen time read by another connection; a listing made before a write.
* A new JVM (`verify`) reads the 163 saved digests and checks every event and history.
* A JVM that halts itself (`Runtime.halt`) after 282 synced and 476 committed events, and
  a JVM that checks the recovery (`crash-writer`, `crash-check`).
* `EdgeProbes`: 20,000 small puts and 5,000 small `rw()` commands, then a restart; 95 MB
  in one transaction (a 20 MB attachment, a 64 MB `.bin`, a 10 M char text); 2 writers and
  3 readers for 4 seconds; `transactionInfo()` while another thread writes; `close()` while
  4 threads run; clocks (a `TestClock` at 0, a stopped one across restarts, one started
  behind, one stepped back an hour, the end of time, one before 1970); a retain duration
  of 1 s and 300 MB of writes; per-thread connections; an order read by a later version
  of its class; synced events in 1 and 4 threads; key replace off; `transactionInfo()` at
  a past time and of a delete; time arguments (null, out of range, DST).

Size: `EventLogApp.java` 1,034 lines, `EdgeProbes.java` 983 lines, `run.sh` 22 lines;
about 100 calls of `check()`. A run takes about 40 seconds on F53 under a load of 20 to 25, and
writes about 370 MB in `data/`.

The last run: every check passed but the two of U1-1 and U1-2, which fail in every run.


## 2. The findings

Most severe first. A reproduction names a file in `probe/` or the probe of `EdgeProbes`.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U1-1  | bug | high   | `transactionInfo()` during writes fails the database   | InfoRace4       |
| U1-2  | bug | medium | that race throws IllegalArgumentException, not ISE     | InfoRace3       |
| U1-3  | doc | medium | the format of `${transactionTime}` is not documented   | Probe1          |
| U1-4  | API | low    | key replace off: `${transactionTime}` is a literal key | keyReplaceOff   |
| U1-5  | API | low    | `connection()` resets the lookup time, not key replace | connectionTraps |
| U1-6  | doc | low    | two puts at one key in a transaction: the last wins    | keyReplaceOff   |
| U1-7  | doc | low    | a read at t sees the transaction of time t: not said   | the app         |
| U1-8  | API | low    | `Time` not `Comparable`; no end bound for a scan       | the app         |
| U1-9  | doc | low    | a local time in a DST gap or overlap: silent           | timeArguments   |
| U1-10 | doc | low    | the last 1,024 units before `Time.MAX` are reserved    | clocks          |
| U1-11 | doc | low    | a delete leaves personal data readable at past times   | the app         |
| U1-12 | doc | low    | nits: a message's parenthesis; `setLookupTime(null)`   | retain          |

### U1-1. transactionInfo() while another thread writes fails the database (bug, high)

A reader that gets a value and calls `Connection.transactionInfo()`, while another thread
commits, can fail the whole database: `DbFailedException` "A read failed on the storage
(the cause). The database takes no more transactions or reads and must be restarted.",
with the cause `StreamFormatException` "Bad item byte size, 1088, at spos 599608: beyond
the stream's record bytes, length 600000." Every later read and transaction, the writer's
too, throws `DbFailedException` until a restart. The restart recovers: the value and its
transaction are there, and a put works (`InfoRestart.java`). No data was lost in the runs.
Both calls are legal, and the Javadoc of `transactionInfo()` foresees the case ("a get
right after the put, in another thread"), with `IllegalStateException` and "call get()
again".

Reproduction, `probe/InfoRace4.java`: one thread puts `/a.bin` in a loop; the main thread
gets `/a.bin` and calls `transactionInfo()`, catching `IllegalStateException` and
`IllegalArgumentException`. The database failed after 46 to 169 ms in each of 5 runs, in
memory and in a directory, with values of 10 and 1,000 bytes. One thread alone (put, get,
`transactionInfo()`, 100,000 and 200,000 times, `InfoSingle.java`) never met it. In the
application, a reader that asks when the log last changed (`get("/meta/seq")`, then
`transactionInfo()`) failed the database within 10 to 110 ms, in every run. The core of
the reproduction, shortened:

```java
try (Database db = Factory.database().memory().start()) {
    new Thread(() -> {
        Connection w = db.connection();
        for (long i = 0; ; i++) w.put("/a.bin", new byte[] {(byte) i});
    }).start();
    Connection c = db.connection();
    while (true) {
        if (c.get("/a.bin", byte[].class) == null) continue;
        try {
            c.transactionInfo();
        } catch (IllegalStateException | IllegalArgumentException e) {
            // ISE is documented; IAE is U1-2.
        }
    }   // DbFailedException within a fraction of a second
}
```

Why, read afterwards: `ConnectionImp.transactionInfo()` throws the documented
`IllegalStateException` only when the value node's position is `Spos.NULL`. A value node
has its real position (`ValueNode.getTpos()`) once its record is serialized, before all
of the record's bytes are in the stream that `Db.getTrans()` reads. `getTrans()` then
reads a record cut at the stream's length and takes it for corrupt data
(`failOnStorage`), or, when none of it is there yet, throws U1-2's exception.

### U1-2. The same race throws IllegalArgumentException (bug, medium)

When the record is not in the stream at all yet, `transactionInfo()` throws
`IllegalArgumentException` "Not a position of a transaction, 307976: at or past the end of
the stream.", which its Javadoc does not name; it names `IllegalStateException` for a
transaction still being stored. It is often more frequent than the documented one: in the
application's 3-second probe, in three runs, 38,916 to 93,680 reads, 75 to 6,696
`IllegalStateException` and 790 to 3,764 `IllegalArgumentException`; in an earlier version
of the probe 3,154 and 8,629. `probe/InfoRace3.java` (one writer of `/a.txt`, one reader
catching only `IllegalStateException`, as the Javadoc says) ended with it in 10 of 10
rounds, within milliseconds. The database goes on after it. The fix of U1-1 likely fixes
this one too.

### U1-3. The format of ${transactionTime} is not documented (doc, medium)

`Connection.setEnableKeyReplace()` says that `${transactionTime}` is replaced by "the
unique transactionTime of the transaction", but not how it is written. It is the time in
clock units as 18 decimal digits with leading zeros: `/events/017942246172270000`. That
makes key order time order, which an ordered event log needs: the events between two
times are a primary scan from `startAt(String.format("%018d", t0.units()))`. A user finds
the format only by trying (`probe/Probe1.java`), and may not trust it to stay. The key
that a put wrote is not returned either: the application formats `Transaction.getTime()`
the same way to find it. Suggested: the format in the Javadoc, and a sentence that key
order is time order.

### U1-4. With key replace off, ${transactionTime} is a literal key (API, low)

Key replace is off for each new connection, and each thread's `db.connection()` is a
connection of its own. With it off, three puts at `/events/${transactionTime}` store one
key, `/events/${transactionTime}`, each over the last, without an error. An event log
whose second thread forgot `setEnableKeyReplace(true)` keeps only that thread's last
event (the earlier ones only at past times). Documented ("This method must be called to
enable it"), but silent. Possible: refuse a key with `${` when replace is off, or make key
replace a setting of the database.

### U1-5. connection() resets the lookup time but keeps key replace (API, low)

`Database.connection()` sets the thread's connection's lookup time to `Time.MAX` at every
call, as its Javadoc says. So `db.connection().setLookupTime(t);
db.connection().get(k)` reads the latest state, not the state at t: an easy mistake in
code that passes the database around and asks it for the connection. Key replace, on the
other hand, stays as the last caller set it: `db.connection().setEnableKeyReplace(true)`,
then `db.connection().getEnableKeyReplace()` is true, so one task's setting carries over
to the next task on a pooled thread. The two pieces of the connection's state behave
differently. The application uses `newConnection()` for its queries.

### U1-6. Two puts at one key in one transaction: the last wins (doc, low)

`c.w().put("/events/${transactionTime}", a).put("/events/${transactionTime}", b)` stores
only `b`: both keys are the transaction's time. That two puts at the same key in one
transaction leave the last is the natural rule, but `WBuilder`, `RwEnvironment.put()` and
the note on key replace do not say it, and with key replace it is easy to meet: an event
log that writes two events in one transaction needs a suffix of its own
(`${transactionTime}-1`).

### U1-7. Is the transaction at exactly the lookup time read? (doc, low)

`setLookupTime(t)` reads "at" t. Whether the transaction whose time is t is part of that
state is not said; it is (the state at `tx.getTime()` has the transaction, the state at
one unit before does not), and the application relies on it for "the state after event
E". The package's example of earlier states takes `currentTime()` before the put, which
avoids the question. One sentence would do: a read at t sees the transactions of time t
and earlier.

### U1-8. Time is not Comparable; a primary scan has no end bound (API, low)

`Time` has `isBetween()` but no `compareTo()`, `isBefore()` or `isAfter()`, and is not
`Comparable`, so sorting and range checks go through `units()`; nor does it convert to
`java.time.Instant`. `UsePrimaryBuilder` has `startAt()` but no end bound, where
`UseIndexBuilder` has `from()` and `to()`: the events between two times need a loop that
compares names and breaks. And an `rw()` action cannot learn its transaction's time, so an
event cannot carry its own time as a field; it is only in its key.

### U1-9. A local time in a DST gap or overlap is resolved silently (doc, low)

`Time.resolve(Europe/Stockholm, "2026-03-29 02:30")`, a local time that does not exist,
gives 01:30 UTC, the same as 03:30 local; `"2026-10-25 02:30"`, which exists twice, gives
the later one (01:30 UTC). The parse is otherwise strict ("24:00" and "2013-02-30" are
refused), so a user may expect a refusal, or at least the rule in the Javadoc.

### U1-10. The last 1,024 units before Time.MAX are reserved (doc, low)

`Time` and `Clock` say that the largest valid time is 2^56 - 1. With a `TestClock` at
`Time.MAX - 1`, a new database does not start: `DbException` "No database time is left for
a user transaction: its time would be 72057594037927934, after the last,
72057594037926911 (the times up to 72057594037927935 are kept for reclaim's internal
transactions)." It is the creation that fails, not a user's transaction. With the clock
at `MAX - 1028`, transactions run up to `MAX - 1024` and the database goes on. Only a test
meets it, in 2198; the reserve could be in `Clock`'s Javadoc.

### U1-11. A delete keeps personal data readable at earlier times (doc, low)

The audit log deletes a user (`user.deleted`, as for an erasure request), but the user's
name and email stay readable at every earlier lookup time, and in the earlier events,
for the retain duration: forever by default. "Good to know" says that earlier states are
kept forever until `setRetainDuration()` limits them, which is right; a sentence on what
it means for a delete, and that there is no erasure of one key's history, would help an
application that stores personal data. With a retain duration of 1 s and a clock a day
on, nothing was cut until about 200 MB had been written (20 MB stream files); the Javadoc
says the duration is a minimum, so that is correct.

### U1-12. Nits (doc, low)

* `LookupTimeNotAvailableException`'s message has an unclosed parenthesis: "Cannot lookup
  at time 15778369000000000 (2020-01-01 00:01:40.000 UTC, the first time available for
  lookup is 15779241901000001 (2020-01-02 00:16:30.100 UTC)."
* `Connection.setLookupTime(null)` throws `IllegalArgumentException` ("lookupTime == null
  not allowed"); the Javadoc does not say.


## 3. What went well

* Time travel was exact in every check of every run: about 350 states at past times and
  the unit before them against the model, the same states rebuilt from the events, time
  ranges, histories and orders by state through the indexes at past times, the last 10
  events as of a time both ways, and `exists()`, `get()` and `transactionInfo()` at past
  times. Before the first event, from 1970 on, the state is empty; `useIndex()` before
  the index's creation throws `NoSuchIndexException`, as documented.
* Restarts kept the history: phase 1's 80 or so states read the same after two restarts,
  and a new JVM read all 163 saved states, 1,138 events and 416 entity histories.
* A crash: after 282 synced and 476 committed events and `Runtime.halt()`, the restart
  had 472 events, contiguous, the log and the state in agreement, every synced one there.
* `close()` while 2 writers and 2 readers ran took 26 to 187 ms; the threads ended with
  `IllegalDbStateException`, and every acknowledged command (44,362 in the last run) was
  there after the restart.
* Reading while writing: 2 writers (61,000 to 105,000 `rw()` commits in 4 s on one
  counter, 33 to 60 reruns) and 3 readers. Every frozen state agreed with itself (events
  and state, counter and event count, index and log), past states agreed, an iterator
  held for seconds kept its time. The counter, a key of 61,000 to 95,000 versions, read
  exactly at 2,000 past times, 2.2 to 2.6 µs a get.
* Many small transactions: 20,000 puts at 49,000 to 145,000 a second, with unique,
  increasing times although 99 % fell in the same millisecond as the one before; 5,000
  `rw()` commands at 14,000 to 54,000 a second; a restart in 0.2 to 0.7 s.
* Large values: 95 MB in one transaction read back exactly at its time, just before the
  overwrite and after a restart.
* Clocks: a `TestClock` at 0, a stopped one across restarts, one started four and a half
  years behind, a clock stepped back an hour: the times always rose and no event key was used
  twice. A clock before 1970 is refused at the start with a clear message.
* Retain: after reclaim, reads at an old time throw `LookupTimeNotAvailableException` as
  documented (`get()`, the iterator of `usePrimary()`, `useIndex()` at its call,
  `transactionInfo()` of a rewritten value), and the latest state keeps every event.
* Data Objects with nested objects and arrays worked as documented, and an order read by
  a later version of its class was converted as 020-09 says (a long into a double, a long
  clamped into an int, a new field at its default).
* Key replace in `rw()` worked, on reruns too; in an object key's directory it is refused
  with a clear message.
* Sync: a synced payment took 8 to 16 ms on F53 under load; 4 threads syncing at once got
  2.6 to 4.9 ms an event, so syncs are shared.
* The Javadoc answered nearly every question: the package page's examples, the lookup
  time, `freezeLookupTime()`, when a scan's time is fixed, what `connection()` resets,
  that `rw()` reads the latest state, and the refusals all matched what the application
  saw.


## 4. Fixes

By coord-1109's fixer x24, 2026-11-09, in the clone
`/Users/f/fl/bench/2026-11-09/clone-x24` rebased on `main` at `740ffdf`, under Frans's rule for
2026.4 (2026-11-09): fix faults against today's specs and Javadoc, make the Javadoc true
where the code is as designed, no new API and no change of meaning. Each commit below has
its tests in `PubTesterJavadoc` and a line in `releases/next.md`, Documentation; JAVADOC
PUB OK. The gate under the lock, on the clone's tip `ed23b80`: BEFORE COMMIT OK (187 s, unit
1535, f 86, demos; `/Users/f/fl/bench/2026-11-09/x24-gate2.txt`).

* U1-3, U1-4 and U1-6 (with 020-24-02's I-6): `00523e0`.
  `Connection.setEnableKeyReplace()` gives the text, the time in clock units as 18
  decimal digits with leading zeros, so that such keys are in time order; says that
  `put()`, `w()` and `rw()` replace it, with the setting as it was at that call; that two
  puts of one transaction at such a key are one key, the last counting; and that with key
  replace off the text is a part of the key as written. Test `testKeyReplaceText`.
* U1-7, and U1-12's `setLookupTime(null)`: `fbe92d4`. `setLookupTime()` says that a read
  at t sees the transaction of time t, and names the `IllegalArgumentException` for null.
  Test `testLookupTimeIncludesItsTransaction`.
* U1-9: `3e8e4f5`. `Time.resolve()` says that a local time that summer time skips or
  repeats is taken as standard time, as `GregorianCalendar` takes it: a skipped 02:30 is
  the time the clocks show as 03:30, a repeated one the second. Test
  `testSummerTimeLocalTimes`.
* U1-11, and U1-12's message: `e68315e` (with 020-24-03's U3-9). `Connection.delete()`
  and the package page say that a deleted value stays readable at earlier lookup times
  until reclaim cuts them, forever by default. The message of
  `LookupTimeNotAvailableException` closes its parenthesis, in `Db.getOne()` and
  `getMany()`: a plain bug, the test failed first. Test `testReclaimCutsLater`.
* U1-10: 020-25's J5 says it in `Clock.getTime()` (on `main` as `09ad69c`),
  not repeated here.
* Not here: U1-1 and U1-2, bugs for another fixer; U1-5 and U1-8, API, for Frans's list
  (U1-5's reset of the lookup time is now said in `Connection`'s class comment, `8ba4003`).
