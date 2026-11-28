# 031-08, part A. User apps against 2026.7: the Pub API under reclaim

Created 2026-11-28 by Frans Lundberg. Status: open.

Part A of a round of "AI as the user" testing (006-20; the earlier
rounds 024-26, 026-13, 026-26 and 031-02) against what `main` changed
for release 2026.7 with 031-06, one record an action: every accepted
transaction, setting and part of a `maintain(budget)` call appends
exactly one record, the database appends nothing by itself or at a
start, reclaim's work rides in the commits' records and in the calls of
`maintain(int budget)`, new in the API; the stream format is new, and a
start checks more. Part A's field is the API in use under reclaim; part
B (`apps-b.md`) takes the stream's byte-for-byte determinism and a user's
handling of the files.

An agent of the lead played a new user: it built the release jar from a
clone of `main` at `ee8a8165` and wrote eight applications from the
README, the Javadoc of the Pub API and of `bergdb.core.Db`, and
`releases/next.md` only, each with an oracle of its own that checks
every result; the implementation was read only to tell a product bug
from a mistake of an app or an unclear document, after a result
disagreed. Nothing in `java/src` was changed.

Made by: Claude, Anthropic's model Opus 5.5, as an agent of the lead, on
2026-11-28 from 06:16, on the branch `031-08-apps-a` of a clone of
`main`.

Findings are UA-1, UA-2, ...; cited from elsewhere as "031-08, UA-1".


## 1. In short

STATE-SHORT


## 2. The applications

Each is plain Java with `main`, in `java/stress/apps/` beside the
earlier apps, compiled with `javac` against `build/bergdb-release.jar`
alone, as `java/stress/apps.sh` compiles them (they join it later); each
takes a seed and sizes, prints `OK ...` or a `FAIL ...` line with the
seed, and exits non-zero on a wrong result. e1, e3, e5, e6, e7 and e8 use
the Pub API, e2 and e4 the Core API, at the node sizes 8, 14, 30 and 62
through `bergdb.core.TestNodeSize`. The Pub apps share
`e0-common/EOracle.java`: the oracle of byte[] values at ".bin" keys,
one history per key, and its checks of a `Connection` (gets and both
listings of each directory at a lookup time, the expiry of a read just
before the first available time); the Core apps use `common/Common.java`
of 024-26. The names e1 to e8 are this part's; 031-02's apps, in its
item, also had names e1 to e11.

* **e1 E1MaintainBudget** (Pub; a test clock that the app moves; a
  file database, or one in memory for a fifth of the seeds; the startup
  distance 5 MB, the least). `maintain()` with the budgets
  `Integer.MIN_VALUE`, -1, 0, 1, 99, 100, 100,000 and
  `Integer.MAX_VALUE` on a new database and while the retain duration is
  forever: the stream size must not change ("With the retain duration
  forever (the default) there is nothing to do"). A load of 2,000 to
  3,000 keys (one in 37 a key of 111 bytes, the limit), then a retain
  duration R of 1, 3, 20 or 600 s, and rounds of churn: `w()`
  transactions of 1 to 500 puts and deletes, values of 0 to 3,000 bytes
  and now and then 10 kB to 1 MB, the clock moved by 0 to R/50 a round
  and by R/2 in a tenth of them, `maintain()` calls by the seed's style
  (the least budget, the most, every out-of-range budget, random, or
  bursts of up to 30 calls), restarts (half by `stop()` then `close()`).
  After every action: gets and listings at the latest time, at the first
  available time and at transaction times inside [now - R, now] and one
  unit before each, against the oracle; `transactionInfo()` of a value
  written at or after the first available time gives that write's time
  and exactly that transaction's KVs, none of reclaim's copies that a
  commit's record carries; `getFirstAvailableLookupTime() <=
  currentTime() - R` (its "lookups work for every time in [now - retain
  duration, now]"), after an increase of R from the first available time
  then on ("the actual duration available for lookups will increase
  until it equals or exceeds"); the time never moves back within a run;
  a read at the first available time less one unit is refused. Each
  `maintain()` call that cuts nothing may write its budget's bytes
  (clamped, 1 kB a unit) and "a small part's work": the excess is
  recorded, and over 4 MB is a FAIL (`-De1.maxOver=N` sets another
  limit). In a 400th of the rounds the retain duration changes to
  another of the four. A restart must keep
  the stream size (nothing is appended at a start), the first available
  time ("A restart after stop() or close() keeps the time"), the retain
  duration and the startup distance; a `maintain()` call right after a
  start is logged with what it wrote. Then every key but up to 30 is
  deleted and the database goes idle: the clock moved by R/4 a call,
  `maintain(budget)` until the stream size stays the same for 16 calls
  (a hang guard of 200,000 calls); the stream kept must then be within
  1 MB of a fresh twin's, a new database with the same settings and the
  same live data, quiet too (`getStreamSize()`: "in a database not
  written to for longer than the retain duration, what it holds beyond
  the live data is what maintain() can give back"). Prints the calls
  that wrote against the Javadoc's "a pass takes about getStreamSize()
  divided by the budget's bytes in calls", the files on disk against
  the stream size, and the largest ratio of the two during the churn.
* **e2 E2LimitsReclaim** (Core; a file stream; node sizes 8 to 62; a
  clock that the app moves; a startup distance of 100 kB, 300 kB or 1
  MB; a retain duration of 1 s). A base of 3,000 to 12,000 keys of 111
  bytes and two to four values of 8 MiB, which every reclaim iteration
  must rewrite, then rounds, the clock moved by 0.05 to 0.6 s each: 500
  KVs (MAX_OPERATIONS) of new random 111-byte keys, the most index nodes
  dirty; 500 overwrites and deletes of base keys; one value of exactly 8
  MiB (MAX_VALUE_BYTES) at one of eight 111-byte keys; four KVs whose
  keys and values are exactly 32 MiB (MAX_TRANS_BYTES); 32 MiB + 1 and
  501 KVs, which `execute()` must refuse with a `DbException`; a key of
  112 bytes and a value of 8 MiB + 1, which `Trans.Builder.put()` must
  refuse, spoiling the builder; commits of one byte, of an empty value
  and of a delete of a key without a value; mixes of up to 499 long keys
  and a large value; `maintain()` calls of 100 to 100,000. Each taken
  transaction commits while reclaim's steps ride in the records; each
  refusal leaves the stream's length, the transaction count and the
  state unchanged and the database going on. After each round, gets of
  what it wrote and of 100 random keys; every 10 rounds a full scan, a
  full scan at a transaction's time inside the retain duration, gets one
  unit before it and a range scan; restarts in a 25th of the rounds; the
  promise of the first available time as in e1. The stream kept
  (`getStreamLength() - getFirstAvailablePos()`) is compared, after each
  round, with the bound that `Database.setRetainDuration()` states ("the
  stream written within the retain duration plus that of one or two
  iterations, and an iteration spans at least twice the startup
  distance, the stream of a quarter of the duration, and four times the
  live data"), W(R) + 2 max(2 SD, W(R/4), 4 L), with L the live keys'
  and values' bytes: the largest ratio is printed, and over 3 is a FAIL.
* **e3 E3IndexReclaim** (Pub; a file database; a test clock; R of 1, 5
  or 30 s). Objects of one Data Object class (a long n, a long g, a
  String s, absent in a tenth, with U+0000, U+0001, å and 中; a double d
  with -0.0, 0.0 and the infinities; a byte[] b with 00, 01, 7F, 80 and
  FF) in two directories, with Strings put over objects and deletes. Five
  index definitions (by n; by g then n; by s; by d; by b then g) taken in
  turn by the names ix0 to ix3: an index started, written beside while it
  builds (with `maintain()` calls and, in a quarter, a restart, after
  which `indexJob()` gives the resumed build), then joined; deleted;
  deleted while it builds (its `join()` must throw `IndexBuildException`,
  FAILED, unless the build had ended); deleted and made again under its
  name with another definition. After every third round, three scans of
  each name against the oracle (the whole index, either way; `eq()` on
  the first of two levels; `from()` and `to()` bounds, inclusive or not;
  `prefix()` of a string level), each object's levels by IndexBuilder's
  rules (a level of another kind or an absent field gives no entry;
  levels by their order, then the names by UTF-8), at the latest time,
  at a transaction's time inside the retain duration and one unit before
  it, where the definition in force then counts: a deleted index still
  scans at a time when it was active, and a name that was absent at the
  time is refused with `NoSuchIndexException` (a name between its
  `start()` and the return of its `join()` is not checked). Listings of
  both directories at the latest time and at the start of the retain
  window.
* **e4 E4KillMaintain** (Core; file streams; node sizes 8, 14, 30 and
  62; a startup distance of 100 kB, 300 kB or 1 MB; a retain duration of
  1 or 3 s; the child's clock moved by the action number). A child JVM
  runs actions that are a function of the seed, the action number i and
  the state before it: transaction i (loads of 50 to 490 KVs, scattered
  deletes and overwrites, a mass delete of every second live key, 480 a
  transaction, churn of a hot range; keys of 4 bytes, of 111 bytes with
  a long shared start, random ones, and in time order; values up to 600
  bytes, now and then 6 kB, and in one in 500 KVs 0.1 to 2 MB) writes
  the marker 05 4d with i and, at 05 4c (i mod 64), the time of
  transaction i - 1; transaction i runs at T0 + i x 20 ms. After
  transactions, `maintain(budget)` calls (100 to 100,000; 3 to 12 after
  the mass deletes), each printed before and after. A child starts,
  reads the marker n, replays the oracle to n and checks the full state
  and 300 gets, and the full state at 3 logged times of the last 63
  transactions at or after the first available time against the oracle
  after that transaction; prints "R n", goes on, and syncs every 13th
  transaction. Every 150 transactions, before transaction k, the child
  sets another retain duration (1 s, 3 s or 500 s) and startup distance
  (100 kB to 1 MB); a recovery to n must have the settings of the last
  change at or before n, or, when n + 1 is a change, those of that change
  (whose calls came before transaction n + 1), or its retain duration
  alone (a kill between the two calls). The oracle keeps each key's
  versions of the last 64 transactions. The parent kills it (SIGKILL) at
  a random time after "R" (a tenth of the kills within 0.5 s of the
  child's start), counts the
  kills that landed in a `maintain()` call and in a start, and checks
  that each recovery is at or after the last synced transaction and not
  before the last recovery; a new database every 20 kills, each ending
  with a clean run that checks everything and closes.
* **e5 E5Threads** (Pub; a file or a memory database; a test clock that
  a thread moves by 0.2 to 5 ms every millisecond; R of 1 to 3 s).
  Writer threads (2 to 8) each own a directory and write `w()`
  transactions of 1 to 60 puts and deletes, recording their times; three
  transfer threads move amounts between 40 accounts (objects, with an
  index on the balance) in `rw()` actions that read both balances, move
  the amount if the source has it, say so through an output, and in a
  30th call `maintain(100)` inside the action; two threads call
  `maintain(budget)` with budgets of 0 to 100,000; reader threads (2 to
  6) open a listing of a writer's directory at t = `currentTime()`, read
  part of it, sleep while the others commit and maintain, read the rest,
  wait until the writer has recorded a transaction after t, and compare
  with the writer's oracle at t; a listing may expire only when t is
  then before the first available time; the writers' oracles are cut
  below the oldest time that a reader reads at and the first available
  time. An `rw()` that throws LookupTimeNotAvailableException is counted
  and not taken as a transfer (UA-3; the final balances show that it
  wrote nothing). Readers also sum the accounts at
  a frozen time: always the total. At the end every directory and every
  balance (the start plus the transfers that committed, by their
  outputs), again after a restart.
* **e6 E6Refusals** (Pub; file databases). Six scenarios in turn, each
  ending with a restart and a check of every key: `maintain()`,
  `setRetainDuration()` and `setStartupDistanceInMb()` after `stop()`
  and after `close()` (IllegalDbStateException, nothing changed); a
  `stop()` or a `close()` from another thread while a thread calls
  `maintain(100,000)` on a database with a mass delete to give back (the
  call returns or throws; the kinds of exception are counted; the
  database must not fail); `maintain()` with the thread's interrupt flag
  set (it returns, or throws a `DbException` "if the thread is
  interrupted during a sync"; the flag is still set after: Database,
  "Interrupts"); `setRetainDuration()` of null, 0 s, 0.999 s and one
  unit less than a second (IllegalArgumentException, nothing written),
  then exactly one second, and the same again (nothing written); an
  Error thrown in an `rw()` action (the database fails; `maintain()`,
  `setRetainDuration()` and a put throw `DbFailedException`; the restart
  has every synced transaction); the end of the clock, a test clock 20
  to 220 units before 2^56 - 1, puts and `maintain()` calls until they
  are refused with a `DbException`, a refused call writing nothing, then
  reads, `sync()`, `close()` and a restart with every committed put.
* **e7 E7PubKill** (Pub; file databases; a test clock that the child
  moves by the action number, 50 ms an action; R of 1 or 3 s). A child
  JVM writes `w()` transactions of 1 to 40 puts and deletes of objects
  in `/e7/obj/`, which the index "by-n" (a long) covers from the
  database's creation and the index "by-s" (a String, absent in an
  eighth) from its first build, and of byte[] values of up to 450 kB in
  `/e7/bin/`, with a mass delete of objects in 10 of every 200
  transactions; every 97th action deletes "by-s" and starts it again,
  its build running beside the next transactions; `maintain()` calls
  (budgets 100, 2,000 and 100,000) after a third of the transactions and
  3 to 8 after each of the 20 transactions that follow a mass delete
  (since kill round 4; before, after a fifth and 6), and in a third of
  the starts right after the recovery. The marker and the logged times as in e4. A child joins the
  builds that the start resumed, replays the oracle to the marker n and
  checks both listings, every value, "by-n" whole both ways and from a
  bound, "by-s" if it is active, and the listing and "by-n" at 2 logged
  times inside the retain duration; the parent's kills and checks as in
  e4, a new database every 20 kills.
* **e8 E8StopEverywhere** (Pub; a file database; the system clock; R
  of 1 to 3 s). Rounds on one database: a start; 2 to 5 writer threads,
  each with a directory of its own, in `w()` transactions of 1 to 30 puts
  and deletes; two transfer threads, `rw()` between 30 accounts (objects
  with an index on the balance); a thread of `maintain()` calls (100 to
  100,000); in a third of the rounds the index deleted and started again;
  after 20 to 1,500 ms a `stop()` or a `close()` from the main thread.
  Each thread records which calls returned and which threw
  IllegalDbStateException (`Database.stop()`: a call that has not begun
  its commit "is refused: it throws IllegalDbStateException, nothing of
  it is written, and the database has not failed"; one whose commit has
  begun completes). After `close()` and a new start: each writer's
  directory is what its returned transactions made, with nothing of a
  refused one; every account is the start plus the transfers that
  returned, the sum the total; the index lists the accounts in the
  oracle's order, after `indexJob().join()` of the build that the start
  resumed; an index whose creation the stop refused after its deletion
  returned is absent; the retain duration and the startup distance as
  set. No call may throw DbFailedException.

The probes for the findings, in `08-user-apps/probes/`, each a few
seconds with the jar alone: `CutFilesStay` (UA-1), `RwExpires` (UA-3),
`MaintainOverrun` (UA-5), `CoreGetTrans` (UA-6), `MaintainWaits` (UA-7),
`FreshMaintain` (UA-8), and `StaleRead`, a read-modify-write whose read
time a cut passes after another transaction wrote what it read (the
Core's `execute()` must refuse it with RerunException and the Pub's
`rw()` run the action again; both did).

Commands, from `java/` after `java/build.sh` (`apps.sh` will have them;
until then by hand):

    javac --release 17 -nowarn -encoding UTF-8 -cp build/bergdb-release.jar -d out \
        $(find stress/apps -name '*.java')
    J="java -ea -Xmx2g -XX:+ExitOnOutOfMemoryError -cp build/bergdb-release.jar:out"
    $J E1MaintainBudget SEED DIR [KEYS] [ROUNDS]          # 3000 3000: 10 to 60 s
    $J E2LimitsReclaim SEED DIR [NODESIZE] [ROUNDS]       # 300 rounds: 1 to 3 minutes
    $J E3IndexReclaim SEED DIR [ROUNDS]                   # 800 rounds: about 30 s
    $J E4KillMaintain parent SEED DIR KILLS [DBKILLS] [MAXDELAYMS]   # 300 kills: about 30 minutes
    $J E5Threads SEED DIR SECONDS [WRITERS] [READERS]
    $J E6Refusals SEED DIR [ROUNDS]                       # 24: about 30 s
    $J E7PubKill parent SEED DIR KILLS [DBKILLS] [MAXDELAYMS]        # 300 kills: about 12 minutes
    $J E8StopEverywhere SEED DIR [ROUNDS]                 # 60 rounds: about 1 minute


## 3. The runs

Times are F53's, from `date`, on 2026-11-28, while `java/week.sh` ran
its lanes (a load of 16 to 22 on 10 cores); at most two of the apps'
JVMs at a time, heaps of 1 or 2 GB. All on the release jar of
`ee8a8165`. Each run on a copy of the classes and the jar of its own;
the logs are in the run directory of the agent (not in the repository),
the seeds and outcomes below.

| When          | What                                                 | Result |
|---------------|------------------------------------------------------|--------|
RUNS-TABLE

RUNS-NOTES


## 4. Findings

No wrong value at any time, no lost synced transaction, no failed
database but by the Error that e6 throws on purpose, no refusal that
wrote anything (section 3). The findings are of the documents; UA-3 also
asks a question of the design.

* **UA-1 (document). The files of a decided cut stay on disk until the
  next commit or `maintain()` call.**
  * Expected: `Database.getStreamSize()`: "from the first position that
    reclaim has not cut to the stream's end ... The storage may hold a
    little more (a file storage drops whole files)"; FileStream's class
    Javadoc, "The files and the disk": "the disk can hold up to about one
    file more than the stream ... and, for a while after a cut, the files
    that the cut's thread has not yet deleted".
  * What happened: in e1's churn the stream files held up to 1.8 to 3.1
    times `getStreamSize()` (streams of 2 MB or more); seed 5 of the
    first runs, round 990: 18.5 MB of files for 6.0 MB of stream, the
    files from 183.6 MB to 196.0 MB of the stream, all before the first
    position, still there two rounds later. `CutFilesStay`: the commit
    that decides a cut makes `getStreamSize()` 18,607,784 bytes; after a
    `sync()` and 2 s of idle time the files hold 28,661,816; one put of 1
    byte later 19,861,928, or after one `maintain(100)` 18,912,440.
  * Why (read after the runs): `Reclaim.applyCut()` moves the first
    available time and position, which `getStreamSize()` counts from, as
    the record that decides the cut is applied; the cut, the deletion of
    the files, waits in `pendingCut` until `cutIfDurable()` finds the
    stream durable past that record, which runs at the next record's
    apply (a commit, or a part of `maintain()`, which syncs for it). The
    record is not durable when its own commit returns, so the files go
    at the next action at the earliest; with none they stay (010-01, P3:
    nothing by itself; a `sync()` does not make the cut; a restart does).
  * Reproduction (5 s, the jar alone):

        javac -cp bergdb-release.jar -d out probes/CutFilesStay.java
        java -cp bergdb-release.jar:out CutFilesStay DIR put
        java -cp bergdb-release.jar:out CutFilesStay DIR2 maintain

  * Judgment: document. `getStreamSize()` and FileStream's "for a while
    after a cut" should say that the stream before a decided cut stays
    on disk until the next commit or `maintain()` call or a restart, up
    to the stream of an iteration, so that an application that measures
    the disk after its last write, or that writes to have space back and
    then stops, knows it. A product change only if Frans wants `sync()`
    to make a pending cut whose record it made durable.

* **UA-2 (document). `maintain()` at a stop throws StreamIoException, not
  the IllegalDbStateException that its Javadoc names.**
  * Expected: `Database.maintain(int)`: "@throws IllegalDbStateException
    If the database is stopping or stopped, as a transaction does";
    "@throws bergdb.pub.util.DbException ... Or if the thread is
    interrupted during a sync."
  * What happened: e6, scenario 2, a `stop()` or `close()` from another
    thread while a thread calls `maintain(100,000)` on a database with a
    mass delete to give back: COUNTS-UA2. None failed the database, and
    every restart had every transaction.
  * Why: `Db.maintain()` syncs a decided cut's table outside the write
    lock; at a stop that sync throws "Storage is closing", as
    `Database.sync()` does. The Core's `Db.maintain()` says so ("@throws
    StreamIoException If the sync is interrupted, or the database is
    stopping"); the Pub's names the interrupt only.
  * Reproduction: `java E6Refusals 1 DIR 12` prints the outcomes of
    scenario 2 ("s2 maintain at a stop: ...").
  * Judgment: document: the Pub's `maintain()` should name the
    StreamIoException ("Storage is closing.") at a stop, as
    `Database.sync()` does, the database not failed; an application that
    catches IllegalDbStateException around `maintain()` at its shutdown
    meets the other.

* **UA-3 (document, and a question). An `rw()` whose action runs longer
  than the retain duration throws LookupTimeNotAvailableException when
  it writes an indexed directory, and commits when it does not.**
  * Expected: `Connection.rw()`: a transaction that conflicts is run
    again; "What the action throws, other than an Error, rw() throws as
    it is"; its @throws list has no LookupTimeNotAvailableException.
    `getFirstAvailableLookupTime()`: "a read that runs longer than that
    may expire. Retry such a read with a later lookup time", which the
    caller of `rw()` cannot, as the action's read time is not its own.
  * What happened: the first runs of e5 (seeds 2 and 3, R of 1 s, the
    test clock moved by 0.2 to 5 ms every millisecond) ended with a
    transfer's `rw()` throwing LookupTimeNotAvailableException from
    `RwEnvironmentImp.indexEntries()`, the read, at the action's read
    time, of the old values whose index entries the commit deletes (the
    accounts' directory has an index), after its action had run longer
    than the retain duration of the clock: it called `maintain(100)`
    inside, which waits while commits come (`Db.maintain()`, the
    handover). Nothing was written. Counted since: COUNTS-UA3.
    `RwExpires`: an action reads an account, waits while reclaim cuts
    past its read time, then writes the account: with an index on the
    directory `rw()` throws after one run and the balance stays 100;
    without one the same action commits (70), as no later transaction
    wrote what it read.
  * Reproduction (2 s):

        java -cp bergdb-release.jar:out RwExpires index
        java -cp bergdb-release.jar:out RwExpires plain

  * Judgment: document, and a question for Frans. `rw()`'s Javadoc
    should say that an action that runs longer than the retain duration
    may make `rw()` throw LookupTimeNotAvailableException, nothing
    written, and that a new `rw()` is the way out; or `rw()` could run
    the action again, as after a conflict, when its read time has
    expired (a product change, for indexed and plain directories alike).
    Not new in 2026.7: 2026.6's `rw()` reads so too.

* **UA-4 (note). A `maintain()` pass takes far fewer calls than the
  Javadoc's estimate after a mass delete.**
  * Expected: `Database.maintain()`: "a pass takes about getStreamSize()
    divided by the budget's bytes in calls".
  * What happened: e1's idle phase, after every key but up to 30 was
    deleted: COUNTS-UA4.
  * Why: a part's cost is what its record writes and a quarter of what
    its step reads (`Db.maintain()`); a stream of dead data costs little
    to pass, and the calls at the end wait for the cut (the retain
    duration, the safe positions).
  * Judgment: note: the estimate is an upper one, for a stream of live
    data; for the case that the paragraph is written for ("An
    application that has deleted much"), "at most about" would be exact.

* **UA-5 (document). One `maintain(budget)` call can write far more than
  its budget: a part's step copies a whole value.**
  * Expected: `Database.maintain(int)`: "The database may use less than
    the budget, or none, depending on its state, and may go past it by a
    small part's work"; the Core's `Db.maintain()`: "may go past it by
    one part's work (a step of about 16 kB of KVs, a take of at most 256
    kB beyond one transaction's, a table padded by at most 200 kB up to
    the next meta block)".
  * What happened: in e1, calls of `maintain(100)` (100 kB) that cut
    nothing wrote up to COUNTS-UA5. `MaintainOverrun`: with one live
    value of 8 MiB among small ones, MAINTAIN-OVERRUN.
  * Why: `Db.maintain()` runs parts while the cost spent is below the
    budget, and a part is never split: a step copies at least one KV
    whole, so a value of up to 8 MiB, and an M4 part takes a whole
    transaction's index nodes and 256 kB more.
  * Reproduction: `java -cp bergdb-release.jar:out MaintainOverrun 100`
    (2 s); `java -De1.maxOver=472000 E1MaintainBudget 102 DIR 3000
    3000` stops at the first call past the Core's list.
  * Judgment: document: the Pub's "a small part's work" and the Core's
    "a step of about 16 kB of KVs" should say that a step copies at
    least one whole value, up to 8 MiB, and that a take can be a whole
    transaction's index nodes, so that a small budget bounds the calls'
    number, not each call's work; a commit waits for the part that runs.


* **UA-6 (document, the Core API). `Db.getTrans()` of an application's
  own commit lists reclaim's copies and table beside its KVs.**
  * Expected: `Db.getTrans()`: "The StoredTrans gives the transaction's
    time (tt), its positions (tpos, lastPos) and, by getValueNodes(), its
    puts and deletes ... A value that reclaim has copied forward ... is
    read from reclaim's step, so that a get's tpos is the step's: a
    transaction of reclaim's, whose value nodes are the values that it
    copied"; `StoredTrans.getValueNodes()`: "its puts and deletes, one for
    each key it put or deleted ... a step of reclaim lists the values it
    copied and reclaim's own keys".
  * What happened: `CoreGetTrans`, 3,000 commits of 20 puts each under a
    retain duration of 1 s: `getTrans(t.tpos)` of 1,472 of them listed
    value nodes that the commit did not put, 31,802 in all with the copy
    mark (`StoredValueNode.isCopy()`) and one a commit without it
    (reclaim's table under "/#i/dreclaim/"); for example 60 value nodes
    for a commit of 20 puts. `st.tt` is the commit's time.
  * Why: since 031-06 a commit's record carries reclaim's step: its
    copies, marked, and its table, beside the action's KVs (StoredTrans,
    format 9). The Javadoc of `getTrans()` and `getValueNodes()` speaks
    of reclaim's steps as transactions of their own, as before 031-06;
    `isCopy()` is not among the members that "The Core API" names. The
    Pub API's `transactionInfo()` leaves the copies out: e1 compared its
    KVs with the transaction's own in every check (section 3), always
    equal.
  * Reproduction: `java -cp bergdb-release.jar:out CoreGetTrans` (3 s).
  * Judgment: document, for the Core API: `getTrans()` and
    `getValueNodes()` should say that a commit's record lists reclaim's
    copies, with the copy mark, and reclaim's keys beside the
    transaction's KVs, and "The Core API" should name `isCopy()`, which a
    Core user needs to tell them apart.

* **UA-7 (document). `maintain()` waits as long as other threads commit
  without a pause.**
  * Expected: `Database.maintain(int)`: "The work runs in parts ... a
    commit waits for the part that runs, and reads go on." Nothing says
    how long the call itself may wait. The Core's `Db.maintain()` does:
    "under commits without a pause the call waits as long as they come"
    (the handover of 031-04, Q9).
  * What happened: e5 seed 102 of soak 1 (8 writers, 4 readers, 60 s):
    the two threads that call `maintain()` ended 2 calls in all, the
    transfer threads, whose actions call `maintain(100)` in a 30th of
    the runs, 638 transfers (21 expired, UA-3), the writers 68,505
    transactions. `MaintainWaits`, `maintain(100)` in a loop for 10 s on
    a memory database with a retain duration of 1 s: with no writer 18.4
    million calls ended, the longest 77 ms; with 1 writer thread 2.85
    million, the longest 114 ms; with 8 writer threads the first call had
    not returned after 4 minutes, its thread parked in
    `Db.giveWayToWriters()` (jstack), until the writers were stopped. The
    probe as it is now, its calls in a thread of their own: 33.2 million
    calls with no writer, 3.24 million with one (1.66 million commits),
    none with 8 (1.78 million commits in the 10 s; the call then running
    returned when the writers stopped). e8's first run: 1 call of
    `maintain()` ended in 15 rounds of 20 to 1,500 ms beside 2 to 5
    writers and 2 transfer threads, and every stop came while a call ran.
  * Reproduction: `java -Xmx1g -cp bergdb-release.jar:out MaintainWaits`
    (35 s).
  * Judgment: document: the Pub's `maintain()` should say, as the Core's
    does, that the call gives way to every commit that waits and so can
    wait as long as commits come without a pause, so that an application
    calls it when it is idle (as the paragraph "What it is for" says), not
    from a thread beside busy writers, nor inside an `rw()` action (UA-3).

* **UA-8 (a question, and the document). `maintain()` on a small new
  database writes about 200 kB and keeps it.**
  * Expected: `Database.maintain()`, "What it is for": to have the space
    of deleted and overwritten data back; "Calls after that do little or
    nothing until the application writes again"; `getStreamSize()`: "in
    a database not written to for longer than the retain duration, what
    it holds beyond the live data is what maintain() can give back". In
    2026.6 a call began an iteration only when its cut would release 400
    kB (026-13, U13-5).
  * What happened: `FreshMaintain`, a new memory database, the startup
    distance set to 5 MB and the retain duration to 1 s, the clock moved
    0.5 s a call: with no value, the stream of 704 bytes became 5,128
    bytes at the first `maintain(100,000)` and 199,728 at the fourth, and
    stayed so for 36 more calls; with 20 puts of a few bytes, 2,976 became
    195,032. In e1 every fresh twin with no live key kept 199,728 bytes,
    and the emptied databases 29 to 241 kB.
  * Why: since 031-06 a call begins a pass while the stream kept holds a
    record of the application's (the settings' records count), with no
    floor; the pass's cut must wait for a meta block, so the part M5
    pads reclaim's table with spaces up to the next one, 200 kB on
    (`Reclaim.planPart`; 031-03, R2), to cut a few hundred bytes.
  * Reproduction: `java -cp bergdb-release.jar:out FreshMaintain` and
    `... FreshMaintain 20` (1 s).
  * Judgment: a question for Frans, with the document: by design (the
    filler is how a cut gets its meta block), but a pass whose cut
    releases less than the filler writes makes a small database about
    200 kB larger; either a floor as 2026.6's 400 kB (a product change),
    or `maintain()` and `getStreamSize()` say that a database of less
    than a meta block's distance, 200 kB, grows to about it under the
    calls.

* **UA-9 (product, S4). A `maintain()` call whose thread has its
  interrupt flag set spins on a core while it gives way to commits.**
  * Expected: `Database`, "Interrupts": "An interrupt of the calling
    thread never fails the database. Three calls only wait, and an
    interrupt ends the wait ... Every other call ignores an interrupt
    until it is done"; nothing says that a call burns a core while it
    waits.
  * What happened: `MaintainSpins`, one `maintain(100)` call beside 8
    writer threads that commit without a pause (a memory database, a
    retain duration of 1 s): without an interrupt the call had not
    returned after 5.2 s and its thread used 310 ms of CPU in 5 s (parks
    of 20 µs); with the thread's interrupt flag set before the call, it
    had not returned either and its thread used 3,961 ms of CPU in the 5
    s. When the writers stopped, the interrupted call ended with a
    StreamIoException ("Thread was interrupted while waiting for D1 ...",
    an InterruptedIOException in its sync), as its Javadoc allows.
  * Why: `Db.giveWayToWriters()` waits while a commit waits for the lock,
    with 100 spins and then `LockSupport.parkNanos(20 µs)`; with the
    interrupt flag set `parkNanos` returns at once ("An interrupt is left
    as it is: parkNanos then returns at once, and the wait spins until
    the writers have the lock", its comment), and with UA-7 the wait has
    no end while commits come.
  * Reproduction: `java -cp bergdb-release.jar:out MaintainSpins` (12 s).
  * Judgment: product, S4: a call that an application interrupts, as at
    its shutdown, uses a core until the writers pause, and without an
    interrupt wakes 50,000 times a second. Not a wrong value; the call
    ends when the writers pause or the database stops. With UA-7 it is
    for 031-04's handover (Q9) to bound the wait or to end it on an
    interrupt, as the three waiting calls do.

## 5. State

STATE


Log
===

2026-11-28. Created; the apps e1 to e7 and their first runs on the
release jar of `ee8a8165`.
