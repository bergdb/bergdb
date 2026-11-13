# 026-13. User apps against 2026.6's changes

Created 2026-11-13 by Frans Lundberg. Status: open.

A round of "AI as the user" testing (006-20; the last round 024-26)
against what `main` changed on 2026-11-13 for release 2026.6: each reclaim
step scans at its own time (026-05, P8), value and key transformations
that throw or pass a limit refuse their transaction (026-06), the write
buffer that grows with use and shrinks after 2 idle seconds (026-07),
`bergdb.pub.Limits` with `keyBytes` and `checkKey` (026-02), the node
size fixed at 30 for users (026-08) and G4's lag gate (026-11). Agents
"apps" of coord-1113 played a new user: they built the release jar from a
clone of `main` and wrote applications from the README, the Javadoc and
`releases/next.md` only, not from the implementation, each with an oracle
of its own that checks every result. Nothing in the product code was
changed.

Findings are U13-1, U13-2, ...; cited from elsewhere as "026-13, U13-1"
(020-24-13 also had findings named U13-n).


## 1. In short

Written 12:00; section 7 has the exact state.

* **Twelve programs**, about 3,600 lines of Java, in
  `/Users/f/fl/bench/2026-11-13/apps/` (a copy in this item's directory,
  `13-user-apps/`), on the release jar of `main` at `9c9650d6` (the
  first runs at `eefd8bb4`).
* **No bug found in BergDB**: no wrong value at any time, no refusal
  that wrote anything, no database failed by a refusal, no recovery
  short of a synced transaction, no lost transaction 2 s before a kill
  (section 3).
* **U13-4 and Q1**: after a mass delete, commits give the space back
  only as the stream grows by twice the startup distance an iteration,
  `maintain()` by the clock; with slow writes the space comes back many
  retain durations later unless the application calls `maintain()`
  (C2, a 5-second reproduction). Recommended: document it now, and study
  a commit that also uses `maintain()`'s rule.
* **Javadoc findings** U13-1, U13-2, U13-5, U13-6 and a note, U13-3;
  five proposed 028-todo entries (section 5).


## 2. The applications

Each is plain Java with `main`, compiled with `javac` against
`bergdb-release.jar` alone, and exits non-zero on a wrong result. They
share `common/Common.java` of 024-26 (the oracle of each key's versions,
and checks of a Core `Db` against it: full scans, gets, range and prefix
scans, `Kvt.time`). `run.sh quick` runs each once (about 4 minutes);
`run.sh soak N` and `run.sh kill N` the long runs, new seeds per N. Since
026-08 every database has the node size 30: the apps' node-size argument
must be 30 (the first quick round, on `eefd8bb4`, still ran 8 to 62).

* **B1 BackToEmpty** (026-05; Core API, a clock that the application
  moves, a retain duration of 1 s, a startup distance of 400 kB to 2 MB
  (200 kB asked is 400 kB: `Db.setStartupDistance()` clamps),
  some runs with a cache budget below the data). A round: a load of N
  keys of eight shapes (the empty key, runs of 00 and FF up to 105
  bytes, random keys up to 111 bytes, keys that extend each other, a
  long shared start); a mass delete in key order, in reverse, at random,
  or of all but every 100th key, with new keys put above the largest and
  below the smallest meanwhile and deleted at the end; then a drive of 8
  R transactions (R = the retain duration in drive transactions: dt = 1,
  2 or 5 ms a transaction, values of 200 to 1,500 bytes, as 026-11's
  G4), since soak 2 at least 6 startup distances of stream (U13-4), or, in a third of the rounds, of `maintain()` calls only with the
  clock moving. Restarts (half by `stop()` then `close()`) during the
  load, the deletes and the drive. After each phase and restart: a full
  scan, 200 gets, range and prefix scans, reads at older times inside the
  retain duration, and the duration's promise
  (`getFirstAvailableLookupTime()` at or before now less the duration).
  After every cut (`getFirstAvailablePos()` moved), the oldest available
  state and the two after it must be whole (P8: a step that scans at its
  own time must not lose a value that a state still available has). The
  stream kept, `getStreamLength() - getFirstAvailablePos()`, is compared
  with a fresh twin, a new database with the same settings and the same
  live KVs given the same drive: the lag (026-11's definition, twice the
  twin's most kept over the last R) is printed, and a kept stream at the
  end above twice the twin's and 500 kB more is a FAIL.
* **B2 Transform** (026-06; Core API, a retain duration of 1 s on the
  system clock, so that reclaim runs beside the writers). Plain writers
  in key ranges of their own; transformer threads, each with a group of
  five keys that every transaction of it puts with one stamp, its own
  counter and one of four shared counters incremented by value
  transformations, and now and then a log key that a key transformation
  ends with the transaction's time. A quarter of the transformer
  transactions carry a KV that must refuse them: a value transformation
  that throws, gives 8 MiB + 1, or takes the transaction over 32 MiB
  (four values of 7 MiB and a transformation to 5 MiB); a key
  transformation that throws, gives a key of 112 or more bytes, or gives
  another key of the transaction; or a value transformation that throws
  once, after which the same `Trans` runs again and must commit with its
  value transformed from the value as given. After a refusal: a
  `DbException` whose cause is the transformation's exception, the
  `Trans`'s keys and values given back, the thread's keys and counter as
  before. Readers check that a group is never seen with two stamps. At
  the end every range, counter (each the number of committed increments)
  and log key against the models, again after a restart; then alone,
  each kind of refusal must leave the stream's length, the transaction
  and the KV counts unchanged; then probes of a value transformation
  that returns null, and of one that throws an Error (the database
  fails; the restart recovers the synced state).
* **B2b GivenBack** (026-06, "its time given back"). While a
  transaction's value transformation runs (and then throws), a reader
  takes `currentTime()` and reads a key that the next transaction
  writes; after the refusal the next transaction commits; a read at the
  time the reader got, and at its actual lookup time, must still not see
  the write (Db's "Threads": a read at such a time reads the same state
  whenever it runs), with a clock that does not move and one that moves.
* **B3 Buffers** (026-07; Pub API, file databases). Mode `many`: N
  databases open at once (a cache budget of 2 MB asked, 4 MB in force:
  `cacheSizeInMb` clamps to 4 to 100,000); six threads write bursts
  (small values, or one in ten of values of 0.1 to 1.1 MB) to a
  database that has been idle at least 1.5 s, many of them at 1.5 to
  2.5 s, around the shrink; two threads close and open databases (half
  by `stop()` then `close()`) and check every key; one opens, writes and
  closes databases of a spare pool. Then a heap phase on N new
  databases with a budget of 1 MB asked (4 in force): the heap of each
  just started, 0.3 s after a fast write of small values to each (the
  buffers grown), 3.5 s and 10 s after, and after a close and an open
  of each; 3.5 s after the writes (since soak 2, after the writes and a
  `sync()` of each) the heap must be within 500 kB a database of the
  reopened one (the buffers shrank back), and a new database must hold
  under 1 MB.
  Mode `kill`: a child JVM writes bursts with idle gaps of 1.5 to 2.5 s
  to 8 to 12 databases, each transaction a function of the seed, the
  database and its number, with a marker; the parent SIGKILLs it at a
  random time, a checker JVM opens each database and checks every value
  against the function at its marker, which must be at or after the last
  synced transaction and no earlier than before; a transaction committed
  2 s or more before the kill and lost is printed as LATE (Database's
  "written soon after ... once the buffer time, 50 ms, has passed").
* **B3c OneBuffer** (026-07). One database: a fast write of 10,000
  small puts, then the heap after a GC every 100 ms; prints when it is
  back within 1 MB of the heap before, from the last write and from
  `sync()`.
* **B3b Huge** (026-07). Transactions of 7 to 31 MB, over the buffer's
  most (10 MB) and its start (64 KiB), right after a start and after
  2.2 s idle (the buffer shrunk), alone and beside a writer of small
  values; each read back at once, after a sync, after a restart.
* **B4 KeyLimits** (026-02; Pub API, then the Core API). Keys of random
  odd characters (U+0000, U+0001, U+007F, å, U+07FF, €, 中, U+FEFF,
  U+FFFF, U+E000, emoji, U+10FFFF, "${transactionTime}", many '/'), most
  of 95 to 116 bytes by the oracle's count (UTF-8 and one byte a '/'),
  and now and then a bad form (ends with '/', "//", a lone surrogate, no
  leading '/', "/"). For each key: `keyBytes()` equals the oracle or
  throws for a bad form; `checkKey()` throws if and only if the form is
  bad or the key is over 111 bytes; a put, `w().put`, `rw()` put,
  delete or `w().delete` of it is refused if and only if `checkKey()`
  threw, with the same message, and writes nothing then; a taken put
  reads back (as `Object.class`, the package's Objects). Edge keys of
  109 to 113 bytes ending with characters of 1 to 4 bytes; an object put
  at a ".txt" key (the key passes, the put is refused); a `w()` spoiled
  by a long key. Key replace: "${transactionTime}" counts as written and
  is replaced by 18 digits, so the stored key has as many bytes. Every
  key again after restarts. The Core part: a `String` key is taken if
  and only if its UTF-8 has at most 111 bytes (Db, "Limits"), and its
  bkey has as many bytes; a `byte[]` key of 111 is taken and of 112
  refused.
* **B5 KillEmpty** (026-05 and 026-06 under SIGKILL; from 024-26's
  Kill). The workload is a function of the seed, the transaction number
  i and the state before it, in cycles of 1,500 transactions: a load of
  150 transactions of 100 to 500 keys, a delete of every key in key
  order, 499 a transaction, and a drive of one overwrite of 200 to 1,500
  bytes a transaction, with `maintain()` calls; a retain duration of 1
  or 3 s on the system clock. Before one transaction in seven, a
  transaction that puts poison values over live keys and whose value
  transformation throws or gives 8 MiB + 1: it must be refused, and the
  database must not fail. A child JVM recovers, replays the oracle to
  the marker, checks a full scan and 200 gets, prints "R n" and goes on,
  syncing every 17th transaction; the parent kills it (SIGKILL) after a
  random delay and checks that each recovery has at least the last
  synced transaction and no fewer than the start before it.
* **C1 OldNodeSize** (026-08). A database that the jar of `eefd8bb4`
  made at the node size 62 (B2's data of the first soak, cut by the
  machine's restart at 11:18) started three times by the Core API: each
  start must throw `StreamFormatException`, and every file must keep its
  name, size and SHA-256.
* **C2 SlowDrive** (026-05, U13-4's reproduction). A memory database
  with a clock that the program moves, a retain duration of 1 s:
  30,000 keys loaded and deleted, then overwrites of one key of 900
  bytes every DT ms, beside a fresh twin with the same drive; the stream
  kept of both printed every R; with "maintain", `maintain()` until false
  after each commit. No oracle of its own: it shows a rate.
* **A5 Readers** and **A6 IndexChurn** of 024-26 (readers at older
  times while a writer deletes; Pub objects with two indexes, long keys
  and levels, reclaim, restarts), on new seeds.


## 3. The runs

Times are F53's, from `date`. Each heavy run in one slot (slot.sh), on a
machine with a load of 10 to 12 on its 10 cores (other agents' runs).
The logs are in `results/` of this item's directory.

| When | Jar | What | Result |
|---|---|---|---|
| 10:53 to 10:56 | `eefd8bb4` | `run.sh quick` | all OK |
| 11:12 to 11:18 | `eefd8bb4` | soak 1, node sizes 8 to 62 | 14 B1 and 1 B2 OK; cut by a restart |
| 11:34 to 11:36 | `9c9650d6` | `run.sh quick`, with C1 | all OK |
| 11:37 to 11:52 | `9c9650d6` | `run.sh soak 1` | 3 B1 FAILs (U13-4), 1 B3 (the app's) |
| 11:55 to 11:56 | `9c9650d6` | B3 at 150 databases, the heap curve | OK |
| 11:56 to PENDING | `9c9650d6` | `run.sh kill 1` | PENDING |

Soak 1 (`results/soak-1-1136.log`) ran 14 B1 (12 at 30,000 keys and
startup distances of 400 kB to 1 MB, one at 200,000 keys with a cache
budget of 4 MB, one at 300,000 keys with 10 MB and a startup distance
of 2 MB; 141 restarts in the 11 that passed, every cut checked at the
oldest state), four B2 of
90 s (910,000 transformer commits, 289,000 refusals of the seven kinds,
41,000 reruns after a throw, 480,000 plain transactions), B3 at 150
databases for 90 s (975,000 transactions, 6.5 GB, 5,000 gaps near the
shrink, 258 reopens), three B4 of 30,000 keys (39,000 taken, 16,000
refused for length, 25,000 of a bad form, 41,000 messages compared with
`checkKey`), A6 (6,000 transactions, 22 restarts), two A5 of 60 s
(172,000 transactions under 3 readers, 2,118 cut reads), B2b 600
rounds, B3b 16 rounds.

* **B1's three FAILs** (seeds 115, 125, 145) are U13-4: at a startup
  distance of 1 MB and R = 200 drive transactions, a drive of 8 R had
  not written enough stream for commits to begin the iterations that cut
  the deleted data. The check now waits for 6 startup distances of
  stream as well as 8 R.
* **B3's FAIL** was the app's: 3.5 s after the last put of a fast
  write to 150 databases (10,000 small puts each, by six threads), the
  heap was 937 kB a database above that after a reopen (with 60
  databases, 23 kB). The heap curve of the same run (the heap after a GC
  every 0.7 s): 1,089 MB at 0.3 s, then 960, 930, 927, 896 and 813 MB at
  0.8 to 3.4 s, and 468 MB from 4.1 s on, the reopened level; so every
  buffer shrank, most of them 3.4 to 4.1 s after the last put. One
  database alone (B3c OneBuffer) is back 2.1 to 2.2 s after its last
  write, 2.1 s after its `sync()` returned. The Javadoc's 2 s count from
  "nothing to write", which a database under a backlog and a loaded
  machine reaches later than its last put; the check now starts after a
  `sync()` of each database (soak 2). The exception was not printed as
  a FAIL line, so `run.sh` now also looks for "Exception in thread" and
  for FAIL after a time.


## 4. Findings

No bug found in BergDB: no wrong value at any time, no failed database
but by an `Error` that the app threw on purpose, no refusal that wrote
anything, no recovery short of a synced transaction. Javadoc and API
findings:

* **U13-1 (doc).** The package's "Good to know" (bergdb.pub,
  package.html) still says "Each started database holds a write buffer
  of 10 MB of heap until it closes, whatever its size: many small
  databases open at once need heap accordingly". Since 026-07 the
  buffer is 64 KiB to 10 MB, as `DatabaseBuilder.startupDistanceInMb()`
  and `Database` say. B3 (60 databases, a budget of 4 MB each) measured 601 kB
  a new database, 5.9 MB more a database 0.3 s after a fast write, and
  within 23 kB a database of the reopened heap 3.5 s after.
* **U13-2 (doc).** `ValueTransformation.transform()` does not say what
  a null result does. It deletes the key: the transaction commits, the
  key reads null at its time and the old value one unit before,
  `getTrans()` lists the KV, and a restart keeps it (B2's probe). The
  Javadoc says that the result "is checked as a value given directly",
  and a null value given directly is refused with
  `IllegalArgumentException` (Trans.Builder), so a user may expect a
  refusal; the Javadoc should say which it is.
* **U13-3 (note).** After an `OutOfMemoryError` in the app (B3's first
  version, which gave 60 databases the default cache budget, a fifth of
  the heap each), a `create().start()` of another database waited for
  ever in its creation's sync (`Db.syncCreation`), holding the lock of
  the class `DatabaseImp`, and every other start in the JVM waited
  behind it (`tools/jstack2.txt` in this item's directory). Db's
  "Errors" says that after an `OutOfMemoryError` a sync or close may
  wait, and advises `-XX:+ExitOnOutOfMemoryError`, which the apps then
  used. A note: one start's waiting sync blocks the starts of every
  database of the JVM, also for a reason other than an
  `OutOfMemoryError`, such as a slow disk.
* **U13-4 (doc, and a question: Q1).** After a mass delete, commits
  alone give the dead stream back only as fast as the stream grows,
  while `maintain()` gives it back by the clock. A reclaim iteration
  begins at a commit only after the stream has grown by twice the
  startup distance (the Pub's `Database.setRetainDuration()`, "nothing
  is cut before the stream has grown by about four times the startup
  distance"); `maintain()` begins one when a quarter of the retain
  duration has passed and its cut would release 400 kB (`Db.maintain()`).
  So back to empty's lag in drive transactions is about the same at
  every R, and in R it grows as the drive writes less per R; with slow
  writes the space comes back many times sooner if the application
  calls `maintain()`, which the Javadoc calls optional. Measured in soak 1 (B1's drives,
  values of 850 bytes on average): at a startup distance of 400 kB a
  lag of 0.9 to 1.8 R at R = 1,000 drive transactions (G4's rate; G4's
  own startup distance is 100 kB), 1.0 to 2.4 R at R = 500, 4.4 R to
  over 8 R at R = 200; at 1 MB, 1.35 R at R = 1,000, 2.2 to 5.6 R at R =
  500, and over 8 R in all three drives at R = 200: seeds 115, 125 and
  145 ended their drive of 8 R (1,600 transactions, 1.9 MB) with 15.3,
  5.0 and 19.1 MB kept, the twin 1.5 MB, FAILs of B1's check, which
  assumed that 8 R is enough; the check now waits for 6 startup
  distances of stream as well. C2 SlowDrive is the reproduction (5
  seconds, the jar alone): 30,000 keys loaded and deleted, then
  overwrites of one key of 900 bytes every 5 ms (R = 200), a startup
  distance of 1 MB, beside a fresh twin with the same drive:

      java -cp bergdb-release.jar:out SlowDrive 1000000 5 10            commits alone
      java -cp bergdb-release.jar:out SlowDrive 1000000 5 10 maintain   maintain() after each

  Commits alone: 6.0 MB kept after the delete, 6.4 MB at 10 R (the
  drive wrote 2.4 MB), 4.5 to 7 MB through 40 R, when the twin (one live
  key) has come to the same 4.6 to 5.7 MB, the paced steady state that
  `setRetainDuration()` describes. With `maintain()` until false after
  each commit: 1.2 MB at 2 R, 0.5 MB at 3 R, then 0.5 to 2.5 MB with the
  twin. In the Pub API, whose startup distance is 5 to 1,000 MB (50 by
  default), the space of a mass delete comes back after about 20 to 200
  MB of new puts, or by `maintain()` calls. The Pub's
  `Database.maintain()` says so in part ("An application that has
  deleted much and then writes little or nothing can call this
  method"); the Core's `Db.maintain()` speaks only of a database that
  the application no longer writes to, and the Core's
  `Db.setRetainDuration()` and `Db.setStartupDistance()` do not say that
  the startup distance paces reclaim (the Pub's do). 026-11's gate of 2 R holds at G4's rate, where the clock
  paces reclaim, as its "R/4 + about 25 + R" says.
* **U13-5 (doc).** `maintain()` "brings a database that has been
  emptied to about the stream of a fresh one": with `maintain()` calls
  only, B1's emptied databases came to 12 to 357 kB kept (soak 1; up to
  408 kB in the first soak), their fresh twins 0 to 201 kB, and stayed
  there: an iteration starts only when its cut
  would release at least 400 kB, as the same Javadoc says. "About"
  could say "within about 400 kB".
* **U13-6 (doc).** Db's "The Core API" lists what the Core API is and
  says "Everything else that is reachable from them is internal,
  whatever is public". It does not name `ValueTransformation` and
  `KeyTransformation`, which `Trans.Builder`'s puts take and whose
  refusals are a Core API change of 2026.6 (`releases/next.md`, 026-06);
  by the letter they are internal. The list should name both.

Confirmed as documented (no finding): a database of the node size 62
made by `eefd8bb4` is refused by `DbBuilder.start()` with
`StreamFormatException`, a clear message ("The database's maximum node
size is 62, and this start uses 30. ... The start has written nothing")
and no file changed (C1); `Limits.keyBytes` and `checkKey` agree with
every put and delete of 30,000 keys a seed (B4); a refused transaction
gives its time back (B2b); transactions of up to 31 MB pass through the
grown and the shrunk buffer (B3b).


## 5. Proposed 028-todo entries

For the coordinator, who registers them.

* **Fix: the package's write buffer sentence (U13-1).** What: bergdb.pub's
  package.html, "Good to know", says each started database holds a write
  buffer of 10 MB; since 026-07 it is 64 KiB, growing to 10 MB while it
  writes fast and back after 2 idle seconds. Done when: the sentence
  says so, as `DatabaseBuilder.startupDistanceInMb()` does, and names the
  cache budget (a fifth of the heap by default, for each database) as
  what many databases in one JVM must set. Frans: none.
* **Fix: what a null result of a value transformation does (U13-2).**
  What: `ValueTransformation.transform()`'s Javadoc says nothing of a
  null result; it deletes the key. Done when: the Javadoc says that a
  null result deletes the key (or, if Frans prefers, `execute()` refuses
  it with a `DbException` as 026-06's other refusals, with a test).
  Frans: decision (A: document the delete, recommended, no behaviour
  change; B: refuse it).
* **Fix: the Core API names the transformations (U13-6).** What: Db's
  "The Core API" does not list `ValueTransformation` and
  `KeyTransformation`, so by its last sentence they are internal. Done
  when: the list names both (as what `Trans.Builder`'s puts take).
  Frans: none.
* **Fix: what maintain() adds, and how reclaim is paced, in the Core's
  Javadoc (U13-4, U13-5; Q1, option A).** What: `Db.maintain()` speaks
  only of a database no longer written to; after a mass delete with
  slow writes the calls also bring the space back many times sooner (C2:
  1.2 MB kept at 2 R with them, 6.4 MB at 10 R without), since commits
  begin an iteration only after twice the startup distance of stream,
  as the Pub's `Database.maintain()` says in part ("deleted much and
  then writes little or nothing"). And
  `Db.maintain()`'s "about the stream of a fresh one" is within about
  400 kB (its own 400 kB rule). The Core's `Db.setRetainDuration()` and
  `Db.setStartupDistance()` do not say that the startup distance paces
  reclaim, as the Pub's do. Done when: `Db.maintain()` says, as the
  Pub's does, that calls help a database written to slowly, and "within
  about 400 kB", and `Db.setRetainDuration()` says how commits pace
  reclaim (the Pub's paragraph, in the Core's terms). Frans: none.
* **Study: a commit begins a reclaim iteration on maintain()'s rule too
  (U13-4; Q1, option B).** What: commits begin an iteration after twice
  the startup distance of stream and a quarter of R; `maintain()` after
  a quarter of R if the cut would release 400 kB. Let a commit also use
  `maintain()`'s rule, so that a slowly written database gets the space
  of a mass delete back by the clock without calls of `maintain()`
  (Frans, 2026-11-10: "the user explicitely calling maintain() should be
  optional"). Done when: a measurement of G4 with C2's settings (a
  startup distance of 1 MB, R = 200 drive transactions) before and
  after, and of G4 and the count gates unchanged at their own settings,
  with the stream's cost (the fillers that `maintain()` writes) per
  iteration; then Frans decides. Frans: decision (which release).
* **Study: one start's sync blocks every start of the JVM (U13-3).**
  What: a Pub start holds the lock of the class `DatabaseImp` through
  `Db.syncCreation`; a sync that waits (after an `OutOfMemoryError`, or a
  slow disk) blocks every other start and open of the JVM. Done when:
  the lock is not held across the sync, or `DatabaseBuilder.start()`'s
  Javadoc says that starts wait for each other. Frans: none.


## 6. Question for Frans

**Q1. Should commits give the space of a mass delete back by the clock,
as `maintain()` does?** (U13-4.) A commit begins a reclaim iteration
only after twice the startup distance of stream (and a quarter of R);
`maintain()` when a quarter of R has passed and the cut would release
400 kB. After a mass delete followed by slow writes the space comes back
many R later unless the application calls `maintain()`: in C2, 6.4 MB
kept at 10 R by commits alone, 1.2 MB at 2 R with `maintain()` after
each commit; in the Pub API, at its startup distance of 5 to 1,000 MB,
after about 20 to 200 MB of new puts.

* A. Document it in the Core's Javadoc, as the Pub's partly does
  (`maintain()` helps a slowly written database too; `setRetainDuration()`
  says how commits pace reclaim). No behaviour change.
* B. A also, and let a commit begin an iteration on `maintain()`'s rule
  as well, so that `maintain()` is optional in effect: a reclaim change
  measured with G4 at C2's settings; it changes the stream's bytes of a
  slowly written database, not the format.

Recommended: A now, as a 028-todo entry, and B registered as a study
(both in section 5); B's release is Frans's choice (2026.6 has 026-05
and 026-09 in reclaim). Applied: the two entries are proposed.


## 7. State

Interim, 12:02.

* **Done**: the apps at node size 30 on the jar of `9c9650d6`; C1, C2,
  B3c; quick and soak 1 (section 3); the findings and Q1.
* **Running / next**: `run.sh kill 1` (from 11:56) and `run.sh soak 2`
  (waiting for a slot), then `run.sh kill 2` if time allows; then the
  copy of the apps into `13-user-apps/`, the commit (items only).
* **Where**: `/Users/f/fl/bench/2026-11-13/apps/` (the clone in `clone/`,
  branch `026-13-user-apps`, the release jar copied to
  `bergdb-release.jar`, the sources, `run.sh`, the logs in `results/`,
  the old node-62 database in `old-dbs/`, scratch classes in `out2/`).


Log
===

2026-11-13. Created by "apps" of coord-1113; the applications and their
quick round on `eefd8bb4` (10:53 to 10:56); a first soak, stopped by the
machine's restart at 11:18. A second agent continued from 11:22: the jar
rebuilt on `9c9650d6`, the apps at node size 30 (026-08), C1 added.
