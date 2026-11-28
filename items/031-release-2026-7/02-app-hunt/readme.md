# 031-02. An app hunt on main before 2026.7

Created 2026-11-25 by Frans Lundberg. Status: open.

A hunt for faults with new user applications, written as a new user
would write them, from the README and the Javadoc only, each with an
oracle of its own, run on the release jar of `main`. Apart from the
earlier hunts (024-26, 026-13, 026-26), whose apps it does not read; it
stresses most what changed since 2026.6: STM's record of recent writes
(028-01, 028-48), transactions with key transformations near the
record limit (028-50), `maintain()` (028-51), and the index writer's
short way and routing (028-19). Findings are named by severity as in
026-26: S1 data lost or wrong, S2 a database that fails or cannot
start, S3 a call refused wrongly, S4 minor or documentation.

Since 2026-11-28 the eleven apps are maintained in `java/stress/apps/`,
as g1 to g11 (e1 to e11 here, in that order), and run by
`java/stress/apps.sh` (quick, soak N, kill N; its header says more); the
files here are the record as of the item, and section 9 says what was
changed for `main`. The item's copies of the eleven sources and its
`run.sh` were removed then (Git has them); `apps/` keeps
`ZeroTailProbe`, a test of the system's appends, not of BergDB.

Made by an agent of lead-1125 on 2026-11-25, from 15:02 to 17:15,
on the branch `031-02` of a clone of `main` at `64d9d1c6`. Nothing in
`java/` was changed. The comparisons ran on the release jar built from
the tag `release-2026.6`.

## 1. In short

* **One S2 finding, F1:** after a kill of the writing process on macOS,
  the last stream file can end in zeros within its length; when they
  cover a meta block's position, the next start refuses the database
  with a message about encryption and foreign streams, though every
  synced transaction is there and a cut of the file at the torn record
  recovers them. Three times in about 9,500 kills; the system makes the
  zeros, BergDB's start refuses them; 2026.6 refuses the same files
  (section 5).
* **One S4 finding, F2:** an emptied database keeps 0.4 to 15.2 MB of
  stream under `maintain()` at a startup distance of 5 MB, where the
  Javadoc says within about 400 kB of a fresh one; the same in 2026.6;
  like RB-007, but beyond its stated bound and not given back by
  028-53's prototype A2 (section 5).
* **No wrong value, no lost transaction:** in 81 runs of eleven apps on
  `main`, with about 9,500 kills and a check of the whole recovered
  state after each, every check of the oracles passed but F1's three
  refused starts; what changed
  since 2026.6 (STM's record of recent writes, key transformations near
  the limits, `maintain()`, PE) was found sound (section 6).
* The apps are in [apps/](apps/), with `run.sh`; adding them to
  `java/stress/apps.sh` is a later step.


## 2. The applications

Eleven apps, one Java file each, in [apps/](apps/), written from the
README, the Pub API's package page and the Javadoc of `bergdb.pub`, and
for four of them the Javadoc of the Core API (`bergdb.core.Db`,
`Trans.Builder`, `KeyTransformation`, `ValueTransformation`,
`GetMany`). Each exits non-zero on a wrong result.

* **e1 StmBank** (Pub). Accounts as objects with an index on the
  balance, hot counters, transfers whose amount depends on what they
  read, transfers over 20 to 300 accounts, slow transfers that sleep 5 ms
  to 14.5 s inside their action, blind puts, and noise writers that put
  hundreds of thousands of keys so that the record of recent writes
  wraps many times. Every committed `rw()` returns what it read through
  its outputs; the oracle replays all transactions in time order, and
  each must have read exactly the replay's state just before it
  (serializability in commit order). The final state, 150 sampled older
  states and the index scans (forward, backward, a range) must equal the
  replay's, also after a restart; readers that freeze their lookup time
  are checked against the replay at their frozen time. Options: a
  retain duration with a thread that calls `maintain()` again and again,
  and noise keys that wrap, so that the noise overwrites.
* **e2 CoreTransform** (Core). Transactions of 1 to 520 KVs mixing plain
  puts and deletes with key transformations that lengthen a short key to
  7 to 112 bytes with the transaction's time (a sixth of them 500 KVs of
  111 bytes with distinct starts, the most dirty index nodes the limits
  allow), transformations that throw, that give a key of the Core's own
  (`/#i/-sd`) or that make two keys one, and value transformations that
  add to a counter, delete, throw or pass 8 MiB. A refused transaction
  must leave nothing written and its KVs as written; one refused by a
  transformation that throws once is executed again, the same `Trans`,
  and must be taken. A second thread increments the same counters by
  optimistic transactions (`keyRead`, `RerunException`): each counter
  must end at the sum of the committed adds. Scans forward, backward
  from a key, ranges with an end key, at the latest and at older times,
  restarts every 1,500 transactions.
* **e3 RetainChurn** (Pub). A test clock that the app moves, a retain
  duration of 5 to 24 s, a startup distance of 5 MB; rounds of fill,
  churn (overwrites, deletes, ranges deleted and put again in reverse
  order, keys near the 7-byte steps and near 111 bytes, names outside
  ASCII), emptying, then `maintain()` as the clock moves until the stream
  kept stops shrinking, and a restart, some with a cache budget of 4 MB.
  Every version of every key is kept: listings forward and backward from
  a name, inclusive or not, at the latest and at older times; a read
  before the first available time refused; that time never later than
  the clock less the retain duration, never moving back in a run, kept
  by a restart; `transactionInfo()` of versions still available. Prints
  the stream kept after emptying.
* **e4 KillWriter** (Pub). A child JVM writes transactions that are a
  function of the seed and their number j: `w()` batches of values and
  deletes, objects in a directory with two indexes, `rw()` counters that
  also write a value made from keys they read, values of up to 1.6 MB,
  transactions of 501 operations that must be refused, `maintain()`
  loops, with a retain duration of 1 s and a startup distance of 5 MB;
  later also a third index created and deleted again and again, its
  build cut by the kills, and the startup distance changed up and down.
  Each commit puts j at `/meta/seq.txt`; the child prints each commit
  and each sync, in a file of its own. The parent kills it with
  `destroyForcibly` after 0.3 to 8 s (options: half the kills 50 to 750
  ms after the spawn, during the child's start; pauses of over 2 s in
  the child, so that its write buffer shrinks and grows again), starts
  the database itself and checks: the recovered k at least the last
  synced, at most the next after the last commit that returned, never
  below the last recovery; every key, object,
  index scan (forward, backward, a prefix), counter and large value equal
  to the oracle's after 1..k; states at older times equal the oracle's
  where still available; the third index, after its build joins.
* **e5 ReplaceLimits** (Pub). Key replace (`${transactionTime}`) in
  `w()` and `rw()` transactions of objects in a directory with two
  indexes and of texts with the time in a directory's name, near and
  over the limits: 500 operations, 56 KiB of keys with the index entries
  of long keys and long string levels, a level over 111 bytes (L6).
  Each transaction taken whole (every key checked once the time is
  known) or refused whole (listings and index scans unchanged); for each
  shape of long keys the largest taken and the smallest refused must not
  cross. Two puts at one replaced key, a replace in an object key's
  directory refused at once, a connection without key replace; updates
  and deletes; index scans with `eq`, `from`, `to`, `prefix` and
  `backward`, and listings at older times.
* **e6 IndexQuery** (Pub). Indexes of the four level types, compound
  and nested, over objects that two writer threads put, change, delete
  and replace by a String; absent fields, ties, -0.0, infinities, NaN,
  zero bytes, names outside the Basic Multilingual Plane (code point
  order, not UTF-16's). Indexes created while the writers write, deleted
  and created again under the same name with another definition. Full
  scans both ways and six random queries per index (eq on the first
  level with a bound or a prefix on the next, ranges with each inclusive
  flag, prefixes of strings and bytes), at the latest and at older
  times, with restarts, some with a cache budget of 4 MB.
* **e7 TreeShaper** (Core). Overwrite and delete patterns that reshape
  the index: bulk puts in key order, reverse and random; every other key
  deleted, ranges deleted, a family of keys emptied, everything deleted;
  keys that share starts of 7, 14 and 21 bytes, keys of exactly 7, 14 and
  21 bytes, the empty key, bytes 00 and FF; values up to 110 kB; a cache
  budget of 4 MB, a startup distance of 5 MB, a test clock and a retain
  duration of 4 s with `maintain()`. Scans from a start key both ways,
  inclusive or not, ranges with an end key, `GetN`, `getOne`, at the
  latest and at older times; restarts every 10 steps.
* **e8 StmWindow** (Core). The edge of the record of recent writes:
  each trial reads a key K at t0, other transactions write K (or a
  virtual write hash that the reader reads) at a random place among M
  writes of other keys, M from 0 to 200,000; the reader's transaction
  must then be refused, whatever M; when nothing wrote K it may be
  refused only past 96,000 writes. Also a restart between, and readers
  at the time of K's write (must be taken) and one unit before it (must
  be refused).
* **e9 StmBins** (Core). Every position of the record, whatever its
  inner bins: 100,000 to 130,000 transactions each write a key of their
  own (single keys, or 1 to 500 a transaction), after 0 to 300,000
  earlier writes; for each of the last 90,000 keys a reader at one unit
  before its write must be refused, and 300 readers at the write's own
  time must be taken.
* **e10 BufferBurst** (Pub). The write buffer that grows with the write
  rate and shrinks after 2 s with nothing to write: bursts of 2 to 40 MB
  from one to three threads, values up to 200 kB, pauses of 2.2 to 3.5
  s, closes and `stop()`s right after a burst or in a pause; each value
  made from its key and version, every key checked after each restart.
* **e11 RwReplace** (Pub). Key replace in `rw()` transactions that
  conflict and run again: threads increment three counters, and each
  increment also puts the value at `/log/cN/${transactionTime}.txt`.
  Listed in key order, the order of the times, each log must hold 1, 2,
  3, ... with no gap or repeat, each entry's time that of the `rw()`
  that returned it, and the counter readable at that time and one unit
  before it with the right values.

Beside them, `ZeroTailProbe`, which does not use BergDB: F1's check of
what a kill leaves in an appended file (section 5).


## 3. How to run them

From the repository's root, after `java/build.sh`:

```sh
sh items/031-release-2026-7/02-app-hunt/apps/run.sh /tmp/w31 quick   # each app small
sh items/031-release-2026-7/02-app-hunt/apps/run.sh /tmp/w31         # the sizes of section 4
```

`run.sh` compiles the apps with `javac` against
`java/build/bergdb-release.jar` and runs them one after the other; each
prints an OK line and exits 0, or exits non-zero on a wrong result. One
app alone: `java -ea -cp java/build/bergdb-release.jar:/tmp/w31/classes
StmBank /tmp/w31/db/e1 11 600 8 3000` (the arguments are in each
source's header and in `run.sh`).


## 4. The runs

On the release jar of the clone at `64d9d1c6`, macOS, JDK 27, with
`-ea` and ZGC, from 15:05 to 17:15 on 2026-11-25, beside `week.sh` and
other sessions' runs (load averages of 40 to 110); each run at most about
30 minutes, its databases deleted after it. Counted are the runs of the
final sources and those of earlier versions whose oracle was right; a run
stopped by its time guard is named so, with what it had checked. Last,
`run.sh quick` on the final sources: all eleven OK.

* e1 StmBank, 4 runs: in memory, 20 s, 17,103 transactions; a file
  database, 600 s, 8 threads, 3,000 accounts: 119,971 transactions
  replayed, each read as the replay's state before it, 3,813 reader
  snapshots, 151 older states, 5.9 million noise keys; a file database,
  900 s, 12 threads, 400 accounts, noise wrapping at 250,000 keys and a
  retain duration of 3 s: 152,274 transactions, 5,865 snapshots, 38.7
  million noise key writes; a file database, 600 s, 10 threads, 800
  accounts, a retain duration of 2 s and a thread that called
  `maintain()` 135,664 times: 73,332 transactions, 3,910 snapshots, 645
  slow actions run again after their read time was cut.
* e2 CoreTransform, 3 runs: 1,600 and 2,200 transactions to the end
  (the second: 1,943 taken, 331 refused, 74 refused once and taken when
  run again, 87,566 optimistic increments with 35 reruns, 182,164 keys),
  and one stopped by its guard after about 3,000 of 5,000 (2,611 taken,
  492 refused), its cache budget of 8 MB making its scans slow.
* e3 RetainChurn, 16 runs of 1 to 6 rounds, seeds 1 to 8 (two stopped
  by the guard after 1 and 4 rounds; one with the retain duration
  changed between rounds): up to 30,401 transactions, 1,294 older-time
  listings and 1,208 reads before the first available time refused a
  run; 20 emptied rounds, each followed by `maintain()` until the stream
  stopped shrinking (F2). Also on 2026.6 (seeds 1 and 5) and on 028-53's
  prototype A2 (seed 5), for F2.
* e4 KillWriter, 38 runs, about 9,500 kills: the parent kills the
  child 0.3 to 14 s after its spawn; in some runs half the kills 50 to
  750 ms after it, while the child starts (some during the database's
  creation, which the start then reports as documented, and the files
  are removed); in some, pauses in the child for the write buffer; in
  some, no change of the startup distance. Up to 690 kills, 250,432
  transactions and 1,339 older states read back a run; the third index
  joined and scanned after 413 recoveries in one run. 8 runs went to the
  end, 6 were ended by their guard and 10 by hand to change the
  app, all with every check passed; 11 ended on an error of the app or
  its oracle of the time (section 8), each after the checks of every
  kill before it had passed; 3 ended on F1.
* e5 ReplaceLimits, 3 runs to the end (600 and 1,500 transactions in
  memory, 1,200 on a file database) and one stopped at 1,500 of 3,000
  transactions (its oracle's sorting too slow for the guard): up to 884
  transactions taken and 307 refused a run, refusals for 500 operations,
  for 56 KiB of keys and for L6; the 56 KiB boundary met to the object,
  134 taken and 135 refused for one shape; new objects counted as 1 + 2
  or 1 + 1 operations (`Limits`' "up to 1 + 2k"), every transaction
  between the two counts taken.
* e6 IndexQuery, 3 runs: 8 and 30 phases to the end, one stopped at
  phase 15 of 40 for disk space; up to 3,896 scans and 97 older states, 5
  indexes, 136,433 transactions.
* e7 TreeShaper, 4 runs: 25 steps; 100 steps keeping every state; 150
  steps with a retain duration of 4 s and 150 with 3 s: up to 5,611
  transactions, 4,065 scans, 122 older times and 13,067 `maintain()`
  calls a run, cuts made.
* e8 StmWindow, 4 runs: 40, 30, 400 and 300 trials (the last with the
  readers at the write's time and one unit before): every reader whose
  key was written after its read time refused, at every M up to 200,000;
  readers with nothing written to K taken up to 118,656 other writes and
  refused from 101,915, within the documented 96,000 to 128,000.
* e9 StmBins, 2 runs, 3 and 40 rounds: 3.6 million readers one unit
  before their key's write, all refused; 12,000 at the write's time, all
  taken.
* e10 BufferBurst, 1 run, 25 rounds: 417 MB in bursts, 10 restarts after
  bursts and pauses, every key checked after each.
* e11 RwReplace, 2 runs: 30 s in memory, 16,056 commits; 400 s on a file,
  16 threads, 251,477 commits and 87,124 runs again: every log whole and
  in order, every time the committed run's.

Not covered: power loss and damaged storage, many databases at once,
Android, other systems; the apps ran on one machine, with one JDK.


## 5. Findings

### F1 (S2). After a kill, a zeroed tail over a meta block stops the start

* **What:** three times in about 9,500 kills of KillWriter's child
  (`destroyForcibly`, SIGKILL, on macOS with APFS), the last stream file
  ended in zeros within the length the file system reports: the kill
  came during an append, and the bytes of that write from a page boundary
  on read as zeros, in the second case 458,752 bytes (28 pages of 16 KiB)
  from offset 3,915,776 of a file of 4,374,528, which covered the meta
  block positions 4,000,000 and 4,200,000; in the third 114,688 bytes (7
  pages) over the meta block at 14,800,000. The next start throws
  `StreamFormatException: Invalid magic bytes in stream: the stream is
  not a BergDB stream, or it is damaged; or an earlier release ...
  encrypted it` (cause `BadMagicBytes ... got: 00000000`, from
  `Db.refuseOtherNodeSize`, which reads the last meta block before
  recovery), and the database does not start until a person cuts the
  file. The data are there: cut at the start of the record that the
  zeros reach (3,902,640), the database starts with every transaction
  up to the last that a sync returned for (56,280, of the child's
  56,284 commits). A zeroed tail that ends before the next meta block
  is recovered by the start as a cut tail (tried on copies of the files,
  cut 10 and 10,000 bytes short of the block: both start, at 56,280);
  in the last two runs, which looked at the files before each start,
  the start took 9 zeroed tails that began after a meta block's first
  bytes, and refused the one that covered a meta block's magic.
* **What the Javadoc says:** `Database`, "What a crash keeps": a crash
  or a power loss cuts the stream's tail and the start recovers it; only
  a power loss is said to leave "a tail of zeros", which is refused with
  "Bad transaction size in db stream, S, spos P" and the advice to cut
  the stream at P. `FileStream`'s Javadoc: the bytes "survive a crash of
  the process". Here a process kill, with no power loss and no crash of
  the system, left the zeros, and the message names neither the zeros
  nor P, but encryption and a foreign stream.
* **The system, not BergDB, makes the zeros:** `ZeroTailProbe` (in
  [apps/](apps/)), a Java process that appends chunks of 64 kB to 2 MB
  with `RandomAccessFile.write()` and forces each, as `FileStream` does,
  killed after 0.3 to 0.9 s: in 1 of 150 trials the file ended in
  442,368 zero bytes (27 pages) within its length. BergDB's part is the
  start's answer to such a tail.
* **Reproduction:** `java -DnoSd=true KillWriter parent DIR 63 500`
  (seed 63 failed at kill 392, about 25 minutes under load; seed 91, the
  same options, at kill 555); the first case was at kill 21 to 29 of
  seed 5 (an earlier version of the app, its directory deleted by the
  run's script). Timing-dependent: none in the other runs.
* **Release 2026.6:** the same refusal on a copy of the same files
  (its start reads the same meta block first; `java/src/bergdb/stream`
  and `storage` have not changed since the tag).
* **Kept:** the files as the kills left them (seeds 63 and 91, 42 and
  63 MB), outside the repository; the lead can ask for them.

### F2 (S4). An emptied database keeps 2 to 3 times the startup distance under maintain()

* **What:** with a retain duration of 5 to 24 s and a startup
  distance of 5 MB, a database whose keys are all deleted, and which is
  then not written to, keeps 0.4 to 15.2 MB of stream under `maintain()`
  called again and again as the clock moves, over 20 emptied rounds of
  RetainChurn (seeds 1 to 7); 19 of them more than 400 kB above a fresh
  database with the same settings, which keeps 904 bytes. The first
  available time stops near the end of the deletes and stays: in seed 1,
  19 minutes (114 retain durations) behind the clock, through 340 more
  steps of half a retain duration and a restart; `maintain()` goes on
  committing its own transactions. `Database.maintain()` says that its
  calls bring "a database that has been emptied to within about 400 kB
  of the size of a fresh one". Disk space only: every value and every
  older state read was right; writes give the space back by the
  commits' rule (30 MB of puts and deletes after it: 10 to 11 MB kept).
* **Reproduction:** `java RetainChurn DIR 5 1` (about 4 minutes):
  "emptied and maintained, stream files 10400 kB", first available
  00:01:38, clock 00:04:39, retain 12 s. The 15,200 kB of seed 1 came
  from an earlier version of the app, whose checks drew from the
  workload's random numbers (`-Dprobe=true` there: 200 more steps, a
  restart and 100 steps more, all at 15,200 kB, first available 19
  minutes behind).
* **Release 2026.6:** the same, byte for byte: 15,200 kB in seed 1,
  10,400 kB in seed 5.
* **RB-007:** the case looks like RB-007's (writes and deletes while an
  iteration waits for its cut, then no writes), but 15.2 MB is above
  RB-007's stated "below 2 sd" (10 MB), and 028-53's prototype A2
  (`prototype-a2.diff`, applied to `64d9d1c6`) keeps 9,200 kB in seed 5,
  with the same first available time: A2 does not give this space back.
  For RB-007's owner (028-53) to tell whether it is RB-007 with a larger
  bound or a case of its own; not registered here.


## 6. Found sound

No wrong value, no lost transaction and no refused start or call that
the Javadoc does not allow, in all the runs of section 4, in what changed
since 2026.6:

* STM's record of recent writes (028-01, 028-48): no lost update in
  e1's replays (362,680 transactions read exactly the state before
  them, with readers over 20 to 300 keys, actions of up to 14.5 s and
  the record wrapped by 64 million noise writes), in e2's optimistic
  counters, in e8's 770 trials at the edge of the record, in e9's 3.6
  million readers at every position of it, and in e11's 87,124 reruns;
  refusals for age only past 96,000 writes, as documented.
* Key transformations near the limits (028-50): every e2 transaction of
  500 KVs transformed to 111-byte keys taken, every one over L1, L2, a
  throwing or duplicating or Core-key transformation, or a value
  transformation that throws or passes 8 MiB refused with nothing
  written and its KVs given back, and the same `Trans` taken when run
  again; key replace in e5 and e11 the same at the Pub API.
* `maintain()` (028-51): values, older states and the first available
  time right through every `maintain()` loop of e3, e4, e7 and e1's
  maintain thread, and across restarts; only F2's space.
* The index writer (028-19): e7's reshaping patterns, e6's indexes and
  e4's three indexes and recoveries read back right at every check, with
  a cache budget of 4 MB in e7 and some of e6's restarts.
* Recovery after kills: every recovery that started held every
  transaction that a sync had returned for, never fewer than the
  recovery before, a whole prefix, and the oracle's state at that prefix,
  its older states and indexes too; an index build cut by kills was
  taken again by the next start and joined. The two refused starts are
  F1.
* Also: older lookup times, scans both ways, inclusive and exclusive
  starts, end keys, prefixes of strings and bytes, code point order of
  names outside the BMP, -0.0 and NaN in indexes, the 56 KiB and L6
  limits of index entries, the write buffer's growth and shrink (e10).



## 7. Not settled

* F1's cause in the operating system: why a SIGKILL during an append
  leaves zeros within the file's length on macOS (APFS), and how often;
  and whether other systems do it. What the start should do with a
  zeroed tail over a meta block (take it as a cut tail, as it takes one
  that stops short of the block, or refuse it with a message that names
  the zeros and the position to cut at) is for the owners of the
  storage layer; Linux was not tried.
* F2: RB-007 or a case of its own, and whether 028-53's option A
  should cover it (section 5).
* No other check failed. Where the oracle was wrong, the app was
  corrected and the run repeated; those runs are not counted.


## 8. Notes for the apps

* `Process.destroyForcibly()` closes the parent's end of the child's
  stdout: lines that the child wrote just before the kill can be lost,
  and an oracle that reads its protocol from the pipe then sees fewer
  commits than were made. KillWriter's child writes its lines to a file
  of its own, which the parent reads after the kill (found in this hunt:
  it made recoveries look ahead of the last commit).
* A transaction refused on purpose takes a number in KillWriter's
  sequence and prints nothing; and the times that a killed child printed
  for transactions the kill lost belong to no one, as the next child
  makes those numbers again at other times. Both are in the parent's
  checks.
* An object put in a directory with k indexes counts up to 1 + 2k
  operations (the package page, "Limits"): KillWriter's first version
  put 99 objects with three indexes, over 500. A kill during the
  database's creation makes the next start throw
  `DatabaseNotCreatedException`, as `DatabaseBuilder.start()` says; the
  app removes the files then.
* An `rw()` action that sleeps longer than the retain duration has its
  read time cut, and its next read throws
  `LookupTimeNotAvailableException` out of `rw()`, as
  `RwEnvironment.get()` says; StmBank's slow transfers retry it (1,020
  times in the run with a retain duration of 3 s).


## 9. On main, 2026-11-28: the apps brought up to date and moved to apps.sh

Done on 2026-11-28, 09:49 to 12:30, by an agent of the lead (013-04), on
a clone of `main` at `8fe32468`; the runs of 9.3 on that commit's release
jar, macOS, JDK 27, with `-ea`, ZGC and heaps of 2 GB, at most two of the
apps' JVMs at a time, beside other sessions' work (load averages of 11 to
18). Nothing in `java/src` was changed.

### 9.1 What was changed in the apps

On `main` the apps did not compile: since 031-06 (2026-11-27)
`maintain()` takes a budget, `maintain(int budget)`, and returns
nothing. Four apps called it; each call keeps what it meant on
2026-11-25:

* **Do all that is due**, `while (db.maintain()) ...`: one call of
  `maintain(100000)`, the largest budget (the Javadoc clamps it to 100 to
  100,000 units of about 1 kB written; a pass takes about
  `getStreamSize()` divided by the budget's bytes in calls), as 031-06
  ported D2ScanHistory's and D3ObjectIndex's loops. In e3 RetainChurn (its
  four loops), e4 KillWriter (the child's `maintain()` steps) and e7
  TreeShaper. RetainChurn's check that `maintain()` did not return true
  100,000 times in a row, and its check of the first available time
  every 50 calls within a loop, went with the loop; its check after each
  call stays. The counts of `maintain()` calls that the apps print are
  now counts of calls, not of the calls that returned true.
* **One bounded part, called again and again**: e1 StmBank's maintainer
  thread, which called `maintain()` once every 2 ms ("about that of a
  commit's share of the maintenance"), calls `maintain(100)`, the
  smallest budget.
* e3 RetainChurn imports `bergdb.pub.Limits` by name, as 026-13's
  KeyLimits does: in `java/stress/apps/` 024-26's class `Limits`
  shadows it; and it prints the stream kept (`getStreamSize()`) beside
  the files' size after each emptied round.

Nothing else changed: the oracles, the workloads and the seeds are those
of 2026-11-25. Every app's scenario exists on `main`: what 031-06 changed
(the work in parts, each with a record of its own) is inside `maintain()`, which the apps call
but do not look into, so all eleven stay.

### 9.2 Where they went

The sources are in `java/stress/apps/`, e1 to e11 as `g1-stm-bank`,
`g2-core-transform`, `g3-retain-churn`, `g4-kill-writer`,
`g5-replace-limits`, `g6-index-query`, `g7-tree-shaper`,
`g8-stm-window`, `g9-stm-bins`, `g10-buffer-burst` and `g11-rw-replace`
(the letter e is 031-08's part A's, f its part B's). `apps.sh` runs them
(its header), each in a directory of its own, kept after a failure:

* quick: each once, smaller than `run.sh quick` (StmBank 6 s,
  RetainChurn seed 11, whose one round empties in about 10 s, KillWriter
  10 kills);
* soak N: `run.sh`'s runs but KillWriter's, its seeds plus 100 N, smaller
  (StmBank two runs of 120 s, RetainChurn two of 2 rounds, CoreTransform
  800 transactions, RwReplace 90 s), so that round 0 has `run.sh`'s
  seeds;
* kill N: KillWriter with `run.sh`'s three options (plain, early kills,
  early kills and pauses), 100 kills each, its seeds plus 100 N.

ZeroTailProbe stays in `apps/` here: it tests the system's appends, not
BergDB (035-01 has it).

### 9.3 The runs and their results

Every run passed: no failure of an oracle, no refused start.

* **`run.sh quick`'s eleven**, its seeds and sizes, 09:53 to 09:59: all
  OK, 342 s in all (KillWriter 10 kills, 1,241 transactions).
* **`run.sh`'s sizes**, its seeds, two lanes, 09:59 to 10:39 (each run
  as on 2026-11-25 but where named):
  * e1 StmBank seed 11, 600 s, 8 threads, 3,000 accounts: 117,271
    transactions replayed, each read the state before it, 3,804 reader
    snapshots, 151 older states, 5.8 million noise keys (2026-11-25:
    119,971, 3,813, 151, 5.9 million).
  * e1 StmBank seed 21, 900 s, 12 threads, 400 accounts, noise wrapping
    at 250,000 keys, a retain duration of 3 s with the maintainer:
    178,136 transactions, 5,824 snapshots, 44.9 million noise key
    writes, 214,431 calls of `maintain(100)`, 1,094 actions whose read
    time was cut and that ran again (152,274, 5,865, 38.7 million, and
    1,020 runs again).
  * e2 CoreTransform seed 6, 2,200 transactions: 1,943 taken, 331
    refused, 74 refused once and taken when run again, 182,164 keys, as
    on 2026-11-25 to the transaction (the workload is the seed's);
    89,410 optimistic increments with 17 reruns (87,566 and 35).
  * e3 RetainChurn seed 2, 6 rounds, and seed 5, 5 rounds with
    `-DretainChanges=true` (no change came in its rounds), and seed 5, 1
    round, twice: 28,522 and 31,263 transactions, 1,245 and 1,283
    older-time listings, 1,175 and 1,240 reads before the first available
    time refused; 8 emptied rounds (the figures below; seed 5's round 0
    the same in its three runs).
  * e5 ReplaceLimits seed 4, 1,200 transactions on a file database: 884
    taken, 226 refused (500 operations 189, key bytes 17, L6 20), 110
    between the two counts of the Javadoc, all taken.
  * e6 IndexQuery seed 4, 30 phases: 122,341 transactions, 3,192 scans,
    97 older states, 5 indexes (2026-11-25: 136,433, 3,896, 97).
  * e7 TreeShaper seed 7, 150 steps, a retain duration of 4 s: 5,540
    transactions, 4,011 scans, 122 older times, 199 `maintain(100000)`
    calls, cuts made.
  * e8 StmWindow seed 12, 300 trials: every conflicting reader refused
    (189), readers with nothing written taken up to 113,980 other writes
    and refused from 101,915 (2026-11-25: 118,656 and 101,915).
  * e9 StmBins seed 9, 40 rounds: 3.6 million readers one unit before
    their key's write, all refused; 12,000 at the write's time, all
    taken (as on 2026-11-25).
  * e10 BufferBurst seed 1, 25 rounds: 421 MB in bursts, 9 restarts,
    every key checked after each (417 MB and 10).
  * e11 RwReplace seed 2, 400 s, 16 threads: 262,448 commits, 84,683
    runs again, every log whole and in order (251,477 and 87,124).
  * e4 KillWriter, `run.sh`'s seeds and options (63; 61 with early
    kills; 81 with early kills and pauses), 100 kills each where `run.sh`
    has 500 to 600 (time; the kill round of 9.5 adds 300 with new seeds),
    10:39 to 10:50: 300 kills, 45,006 transactions, 558 older states read
    back, every recovery a whole prefix at least to the last sync and at
    most to the next commit, none beyond the last printed commit; no zeroed
    tail written while the child ran, and no refused start (on 2026-11-25,
    F1's three refusals were in about 9,500 kills, at kills 21 to 555 of
    their runs); 26 NOTEs of zeros at the last file's end that were there
    before the child ran, which the app tells apart.
* **New seeds, small**, 10:30 to 10:34: RetainChurn seeds 11, 13, 16,
  28, 33 and 34 (1 round each), StmBank, CoreTransform, IndexQuery,
  StmWindow and RwReplace at the quick sizes: all OK.
* **The gates' rounds** (9.5), on `main` of 11:16 (`32b7e6f1`) and
  this change: `apps.sh quick` (all eleven OK); `soak 28` for g1 to g11,
  12 runs, seeds 2801 to 2821: StmBank 22,978 and 29,771 transactions
  replayed, CoreTransform 687 taken and 148 refused, RetainChurn 3
  emptied rounds, ReplaceLimits 450 taken and 104 refused, StmWindow
  refused for age from 111,313 writes, RwReplace 54,293 commits, all OK;
  `kill 28` for g1 to g11: KillWriter 300 kills with new seeds (2861,
  2863, 2881), 90,446 transactions, 556 older states, no refused start,
  no zeroed tail written while the child ran.

**RetainChurn's emptied rounds against RB-011's bound.** The disk after
emptying and `maintain()` until the files stopped shrinking, and the
stream kept, `getStreamSize()`:

* seed 5 (the case of F2 and RB-011), round 0: 2,777 kB on disk, one
  file of 2,777,728 bytes from position 295,000,000, holding a stream
  kept of 256 kB; rounds 2 to 4 of the 5-round run: 1,903, 322 and 1,386
  kB on disk for 277, 315 and 468 kB of stream;
* seed 2, rounds 0, 2, 3 and 4: 849, 929, 753 and 1,001 kB for 104,
  689, 304 and 108 kB;
* seed 11, round 0: 493 kB for 417 kB;
* in the soak round of 9.5, seed 2802's two rounds and seed 2805's: 3,457
  and 3,801 kB for 443 and 176 kB (files of 20 MB, made at 200 MB kept),
  5,217 kB for 494 kB (5 MB files, made at 53 MB kept).

RB-011's bound since 028-73 (033): the disk holds up to about one file
more than the stream, a file being a tenth of the stream kept when it
was made, at least 1 MB from 4 MB kept (FileStream's sizes 200 kB, 1,
5, 20 MB ...). Seed 5's stream kept reached about 76 MB before the
emptying (the files' size at the first step of the loop: 75,784 kB), so
its files from then on are 5 MB ones (a tenth of more than 50 MB);
2,777 kB on disk is 2.5 MB more than the stream, within that file: in
the bound. On 2026-11-25 (the quarter, before 028-62) it was 10,400 kB;
028-62's measurement with the tenth, 400 kB on disk for 61 kB of
stream, was made before 031-06 changed `maintain()`, so the stream's cut
now falls elsewhere in the files; the figures differ, both within the
bound. F2's 0.4 to 15.2 MB are now 0.3 to 2.8 MB.

### 9.4 Findings

* **No product bug**: every run passed, and no result needed a reading
  of the implementation.
* **N1 (S4, a document).** The stream kept after emptying was above 400
  kB in three of the nine emptied rounds (468 kB in seed 5, 689 kB in
  seed 2, 417 kB in seed 11). No Javadoc on `main` promises 400 kB
  since 031-06 (its merge took the prototype's text of
  `maintain(int budget)`, which promises a pass and the space back after
  the retain duration, and no figure; `Db.maintain()`'s "about 400 kB"
  and its release threshold went with it). But 033's RB-011 says, in its
  Fix, that "the Javadoc of the Pub's `Database.maintain()` says that
  the calls bring the stream of an emptied database to within about 400
  kB of a fresh one's stream", and 027-13 and FileStream's class Javadoc
  cite RetainChurn's figures of before 031-06. For 033's and 027-13's
  owners: RB-011's text and the figures, against `main`'s Javadoc.
* Not found again: F1 (RB-012, fixed on `main` by 028-60): no refused
  start in KillWriter's 620 kills of 2026-11-28 (3 in about 9,500 kills
  on 2026-11-25).

### 9.5 apps.sh, week.sh and night.sh, and the gates

* **031-08's apps in the same change**, as the lead asked (2026-11-28),
  so that one agent edits `apps.sh`: part B's f1 to f5 at the sizes of
  its apps-b.md, section 5 (f4 without its database of 2026.6: `apps.sh`
  builds no 2026.6 jar), and part A's e1 to e8 at the sizes of its
  apps-a.md, section 5, for quick, and of its soak 3 and kill rounds,
  fewer, for soak and kill. `ONLY=LETTERS` runs some items' apps (a, b,
  d, e, f, g), for a trial; the name `APPS` was taken (the sources'
  directory).
* **The modes' growth**, F53 under load on 2026-11-28: quick from about
  6 minutes (238 to 263 s on 2026-11-25 and 26, 028-64) to about 15 (674
  s for all but e1 to e8, which took 239 s alone; the sets e, f and g
  about 4, 3 and 2.5 minutes); soak by 13 minutes for g1 to g11 (789 s
  measured), 16 for e1 to e8 (935 s measured) and, estimated from
  031-08's record, about 35 for f1 to f5; kill by 13 minutes for g1 to g11 (774 s
  measured), about 35 for f2 and 18 for e4 and e7 (1,059 s measured).
* **week.sh** (aim about 10 hours, at most 12; 028-64): its run's time
  is that of its longest lane, the large reclaim run's 5.5 to 6.6 hours;
  lane S, 4.1 to 4.9 hours, grows by about 2.3 hours with the three
  sets, to 6.4 to 7.2 hours, so the run takes about 7.2 hours at most:
  within the aim, with nothing left out. CC makes the soak and kill
  rounds a little longer (030-30).
* **night.sh** does not run `apps.sh`; its step 11d (`apptraces.sh
  night`) compiles all of `stress/apps/` (seconds more) and runs its
  fixed nine apps: its 2.5 hours do not change.
* **The gates**, on this change rebased onto `main`: `sh stress/apps.sh
  quick`, before e1 to e8 joined: APPS OK (674 s); `ONLY=g sh
  stress/apps.sh soak 28`: APPS OK (789 s); `ONLY=g sh stress/apps.sh
  kill 28`: APPS OK (774 s); `sh before-commit.sh`: BEFORE COMMIT OK
  (119 s); with e1 to e8 joined: `ONLY=e sh stress/apps.sh quick`: APPS
  OK (239 s); `ONLY=e sh stress/apps.sh kill 28`: APPS OK (1,059 s; e4
  150 kills, 143 recoveries checked; e7 200 kills, 210 recoveries
  checked); `ONLY=e sh stress/apps.sh soak 28`: APPS OK (935 s, 11
  runs). Not run for want of time: the soak and kill rounds of
  f1 to f5, and the whole rounds of soak and kill.

Log
===

2026-11-25. Created by lead-1125 (006-35): fixing bugs comes first, and
no bug is known on `main` but RB-007; an app hunt is the method that
found most of 2026.4's bugs.

2026-11-25. Eleven apps written and run by an agent of lead-1125, 15:02
to 17:15: F1 (S2) and F2 (S4), both also in 2026.6; nothing else
found (sections 1 and 5). Status stays open for the lead's decisions on
F1 and F2.

2026-11-28. The apps on `main`'s API (`maintain(int budget)`, 031-06)
and moved to `java/stress/apps/` as g1 to g11, run by `apps.sh` in its
three modes, with 031-08's e1 to e8 and f1 to f5 (the lead's request);
run on `main` at `run.sh`'s seeds and sizes and at new seeds, every run
passed; no product bug; one document finding, N1 (section 9).
