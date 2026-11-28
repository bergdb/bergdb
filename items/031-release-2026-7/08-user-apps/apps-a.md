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

Written 11:00; section 5 has the exact state.

* **Eight applications** in `java/stress/apps/e1-*` to `e8-*`, with their
  oracle `e0-common/EOracle.java`, about 3,300 lines of Java, and nine
  probes of a page each in `08-user-apps/probes/`, on the release jar of
  `main` at `ee8a8165`.
* **What they ran** (section 3), from 06:22 to 10:58, beside week.sh:
  about 200 runs of the apps (with the first and quick ones), 1,870
  SIGKILLs and 2,600 stops: e1 125,000 Pub transactions and 116,000
  `maintain()` calls under a moved clock, 5,900 cuts, 1,060 restarts,
  367 changes of the retain duration, 3.0 million reads checked at the
  latest and older times; e2 5,800 Core transactions at the limits (25.9
  GB in transactions of 8 to 32 MiB) and 1,770 refusals at node sizes 8
  to 62; e3 39,700 transactions, 4,420 index builds and 291,000 index
  scans checked; e5 4.7 million writer transactions, 6.6 million `rw()`
  transfers and 57,000 held listings checked beside 146,000 `maintain()`
  calls; e6 432 scenarios of refusals; e8 22.1 million writer
  transactions and 7.8 million transfers checked across 2,600 stops; e4
  750 SIGKILLs (more than 350 of them in a `maintain()` call) and e7
  1,120, each recovery checked against the oracle.
* **No bug of data found**: no wrong value at any time, at the latest
  state or an older one inside the retain duration; no recovery short of
  a synced transaction, none with a part of a transaction; no returned
  transaction lost at a stop and nothing of a refused one written; no
  refusal that wrote anything; no failed database but by e6's own Error;
  the first available time kept by every restart and its promise held;
  `transactionInfo()` exact under reclaim's copies; no lost update across
  a cut (`StaleRead`). Three FAILs became findings (UA-3, UA-5, UA-10);
  the others were the apps' own, each fixed (section 3).
* **Ten findings** (section 4): UA-9, a product issue of S4: a
  `maintain()` call with its thread's interrupt flag set spins on a core
  while it gives way to commits, which it does as long as commits come
  (UA-7, 0 calls ended in 10 s beside 8 writers). Nine of the documents:
  the files of a decided cut stay until the next action (UA-1); the
  exceptions at a stop, StreamIoException from `maintain()` (UA-2) and
  from a put's warm-up (UA-10), nothing written; `rw()` that outlives the
  retain duration expires when it writes an indexed directory and
  commits when it does not (UA-3, with a question); a pass's length
  (UA-4, a note); a call's overrun up to a whole 8 MiB value (UA-5); the
  Core's `getTrans()` lists reclaim's copies in a commit's record (UA-6);
  `maintain()` on a small new database writes about 200 kB and keeps it
  (UA-8, with a question).


## 2. The applications

Each is plain Java with `main`, in `java/stress/apps/` beside the
earlier apps, compiled with `javac` against `build/bergdb-release.jar`
alone, as `java/stress/apps.sh` compiles them (they are in none of its
modes yet, section 5); each
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
  forever (the default) there is nothing to do"). A load of KEYS keys
  (2,000 to 10,000 in the runs; one in 37 a key of 111 bytes, the
  limit), then a retain
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
  the starts right after the recovery. The marker and the logged times
  as in e4. A child joins the builds that the start resumed, replays the
  oracle to the marker n and
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
  set. No call may throw DbFailedException. A call that throws another
  DbException at the stop (UA-10) is printed with its stack, and the
  check takes its writer's directory with that transaction whole or
  without it, a transfer moved or not by the balances (the sum must be
  the total). `-De8.cache=N` sets the cache budget (32 MB by default) and
  `-De8.value=N` the most bytes of a value beyond its 16 (300).

The probes for the findings, in `08-user-apps/probes/`, each a few
seconds with the jar alone: `CutFilesStay` (UA-1), `EmptiedDisk` (the
files after an emptied database's calls), `RwExpires` (UA-3),
`MaintainOverrun` (UA-5), `CoreGetTrans` (UA-6), `MaintainWaits` (UA-7),
`FreshMaintain` (UA-8), and `StaleRead`, a read-modify-write whose read
time a cut passes after another transaction wrote what it read (the
Core's `execute()` must refuse it with RerunException and the Pub's
`rw()` run the action again; both did).

Commands, from `java/` after `java/build.sh`, by hand (`apps.sh` has
none of them yet):

    javac --release 17 -nowarn -encoding UTF-8 -cp build/bergdb-release.jar -d out \
        $(find stress/apps -name '*.java')
    J="java -ea -Xmx2g -XX:+ExitOnOutOfMemoryError -cp build/bergdb-release.jar:out"
    $J E1MaintainBudget SEED DIR [KEYS] [ROUNDS]          # 3000 3000: about 1 minute
    $J E2LimitsReclaim SEED DIR [NODESIZE] [ROUNDS]       # 300 rounds: 2 to 4 minutes
    $J E3IndexReclaim SEED DIR [ROUNDS]                   # 800 rounds: about 30 s
    $J E4KillMaintain parent SEED DIR KILLS [DBKILLS] [MAXDELAYMS]   # 300 kills: about 30 minutes, children of 2 GB
    $J E5Threads SEED DIR SECONDS [WRITERS] [READERS]     # 4 writers and 3 readers by default
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

* **First runs** (06:22 to 06:46): e1 seeds 1 to 8 (2,000 keys, 1,500
  rounds), all OK; e4 seed 1, 30 kills, OK; e4 seed 11, 45 kills, then
  stopped by the agent's own recompile, which removed the classes under
  the run (since then each run copies its classes); quick runs of e2,
  e3, e5, e6 and e7 (seeds 1 to 4): three bugs of the apps fixed (e3 read
  a String at an object key as a String through `Object.class`, which
  gives its bytes; e3's transactions of 150 objects in a directory with
  three indexes passed 500 operations; e6's loop at the end of the clock
  ended before a refusal), and e5 seeds 2 and 3 FAIL: UA-3.
* **Kill 1** (06:46 to 06:54): e4 seed 21, 84 kills in 5 databases,
  every recovery checked, then FAIL: the child's OutOfMemoryError, the
  app's (its oracle kept every version of every key); since then it keeps
  the last 64 transactions.
* **Soak 1** (06:54 to 07:23): 46 runs, two lanes. e1 seeds 101 to 120
  (3,000 keys, 3,000 rounds): seed 102 FAIL, the first sight of UA-5 (a
  call of `maintain(100)` wrote 1,054,352 bytes beyond its budget's; the
  check became a report, a FAIL beyond 4 MB); the even seeds 104 to 120
  were lost to the agent's recompile and rerun from 07:08 to 07:19, all
  OK. e2 seeds 101 to 108 (node sizes 8, 14, 30 and 62, 300 rounds), all
  OK. e3 seeds 101 to 110 (800 rounds): seeds 101 and 105 FAIL, "the
  restart changed the first available time", the app's: it compared the
  time read before `close()`, while an index build or the removal of a
  deleted index's entries can commit in the background, with the time
  after the start, and a start that resumes a build commits at once. e3
  now reads the time after `close()` (the getters give the last values)
  and allows a later time after a start that resumed a build or followed
  a deletion, never an earlier one. The rerun of seed 105 at 08:58 met
  one cut of a resumed build right after a start, its FAIL's case, and
  passed; seed 101, whose FAIL came at a restart with no build running,
  passed at 08:58 and six more times at 10:15, 54 restarts each, none
  with a time that moved: the case of its FAIL was not met again, and
  which background commit moved its time is not shown here. Shown on
  2026-11-28 by 028-83: the removal of a deleted index's entries, on its
  own thread (`IndexManager.startCleanup`), committed between the app's
  read of the first available time and `close()`, and that commit's
  record carried a reclaim step that decided a cut; the start moves
  nothing (it reads the cut row that the cut set). The app's mistake,
  with a Javadoc that did not say that the index jobs' commits move the
  time; `CleanupCutProbe` (028-83) sets the order. e5 seeds 101 to
  104 (60 s): 104 ran out of heap (the app's oracle kept every version;
  since then it keeps versions
  from the readers' oldest time on), the others OK. e6 seeds 101 to 104
  (24 scenarios), all OK.
* **Kill 2** (07:23 to 07:34): e7 seed 31, 300 kills (22 in a
  `maintain()` call, 20 in a start), 17 databases, 307 recoveries
  checked: OK.
* **Kill 3** (07:35 to 08:05): e4 seed 22 with the settings' changes,
  271 kills (133 in a `maintain()` call, 35 in a start), 15 databases,
  every recovery checked and right; then the final check of database 15
  ran out of a heap of 1 GB (the app's: the oracle and the check's scan
  each held every live value, values of 0.1 to 2 MB in one KV of 500);
  since then the children have 2 GB and such values are 4 times rarer.
* **Soak 2** (08:06 to 08:45): 32 runs. e1 seeds 201 to 206 (10,000
  keys, 6,000 rounds, retain durations changed in a 400th of the
  rounds); e2 seeds 201 to 208
  (400 rounds); e3 seeds 201 to 206 (2,000 rounds); e5 seeds 201 to 204
  (120 s, 3 to 8 writers, listings now and then held past the retain
  duration); e6 seeds 201 to 204 (36 scenarios); e8 seeds 201 to 204 (60
  rounds): all OK.
* **Kill 4** (08:45 to 08:58): e7 seed 32, 300 kills (16 in a
  `maintain()` call, 26 in a start), 18 databases, 321 recoveries
  checked: OK.
* **Soak 3** (08:58 to 09:24): the reruns of e3 seeds 101 and 105 (OK,
  seed 105 with one cut of a resumed build right after a start), and 34
  runs: e1 seeds 301 to 310 (5,000 keys, 5,000 rounds), e2 seeds 301 to
  306 (300 rounds), e3 seeds 301 to 306 (1,500 rounds; 667 restarts, the
  first available time the same after each), e5 seeds 301 to 304 (90 s),
  e6 seeds 301 to 304 and e8 seeds 301 to 304 (80 rounds): all OK but e8
  seed 303, FAIL at round 60: a writer's `w().execute()` threw
  StreamIoException at the stop (UA-10). The kill round that followed
  (e4 seed 23) was stopped after a minute to free the two slots for it.
* **The hunt of UA-10** (09:25 to 09:37): e8 with the stack and the
  whole-or-nothing check, seeds 303 and 501 to 503 at the default cache
  (no such call in 320 stops), then seeds 601 to 612 with
  `-De8.cache=4 -De8.value=3000`: 391 such calls in 960 stops, none of
  them written, all OK.
* **Kill 5** (09:43 to 10:15): e4 seed 24, with the settings' changes
  and children of 2 GB: 300 kills (173 in a `maintain()` call, 22 in a
  start), 17 databases, 311 recoveries checked: OK. (A run of seed 23 at
  09:37 was stopped after 20 kills, again for the slots, for the probe
  `EmptiedDisk`.)
* **Soak 4** (10:15 to 10:28): the six reruns of e3 seed 101 above,
  and 20 runs: e1 seeds 401 to 406, e2 401 and 402 (node sizes 8 and 62,
  200 rounds), e3 401 to 404 (1,000 rounds), e5 401 and 402, e6 401 and
  402, e8 401 to 404: all OK.
* **Kill 6** (10:28 to 10:41): e7 seed 33, 300 kills (16 in a
  `maintain()` call, 23 in a start), 17 databases, 306 recoveries
  checked: OK.
* **Soak 5** (10:41 to 10:45): e8 seeds 613 to 618 with `-De8.cache=4
  -De8.value=3000` (60 rounds; 140 calls threw StreamIoException at a
  stop, none written: UA-10) and e5 seeds 403 and 404 (60 s): all OK.
* **Kill 7** (10:45 to 10:53): e7 seed 34, 200 kills (13 in a
  `maintain()` call, 15 in a start), 12 databases, 208 recoveries
  checked: OK.
* **Soak 6** (10:53 to 10:58): e1 seeds 501 to 506, e3 501 to 504, e2
  501 and 502 (node sizes 14 and 30, 200 rounds): all OK.

Measurements that the apps print, against the documents (no FAIL):

* e2, the stream kept against `setRetainDuration()`'s "about the stream
  written within the retain duration plus that of one or two iterations"
  (W(R) + 2 max(2 SD, W(R/4), 4 L), section 2): at most 0.45 to 1.04 of
  it in the 22 runs, 1.04 in seed 202 of soak 2 (698 MB kept, 80 MB of
  live keys and values of 111-byte keys and values up to 8 MiB), where
  the iterations are bound by the live data.
* e1, the files on disk against `getStreamSize()` during the churn: at
  most 1.8 to 3.4 times (UA-1). Right after the idle phase's last call,
  0.2 to 38.4 MB of files for a stream of 29 to 212 kB (38.4 MB in seed
  204 of soak 2, whose stream had reached 76 MB): the cut's thread
  deletes the files of a cut a batch at a time (FileStream, "for a while
  after a cut, the files that the cut's thread has not yet deleted").
  `EmptiedDisk` (a probe of 1 minute): a stream of 80 MB emptied and
  given `maintain(100,000)` until quiet held 66,165,912 bytes of files
  for 211,008 of stream right after the last call, and 5 s later
  1,165,912 in one file, as after a restart.
* e1, the most that one `maintain()` call wrote beyond its budget's
  bytes: up to 1,236,312 bytes (UA-5).
* e5 and e8, `maintain()` beside busy writers: e8 ended 0 calls in
  most rounds of 20 to 1,500 ms beside 2 to 5 writer threads (UA-7).


## 4. Findings

No wrong value at any time, no lost synced transaction, no returned
transaction lost at a stop, no failed database but by the Error that e6
throws on purpose, no refusal that wrote anything (section 3). Of the
ten findings, nine are of the documents (UA-3 and UA-8 also ask a
question of the design, UA-4 is a note) and one, UA-9, is of the product,
of severity S4 (026-26's scale: S1 data lost or wrong, S2 a database
that fails or cannot start, S3 a call refused wrongly, S4 minor or
documentation). Read after each result that disagreed: the code named
under "Why".

Where they went (2026-11-28): UA-9, UA-10, UA-2 and UA-8 are 028-83's,
UA-4 to UA-7 028-84's, UA-1 028-82's (with part B's UB-1); UA-3 is on
Frans's list (006-37).

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
    mass delete to give back: in the 40 stops of soaks 1 and 2, 33 calls
    threw DbStoppingException (an IllegalDbStateException) and 7
    StreamIoException ("StorageManager has error: Storage is closing.");
    in the quick runs 2 and 1 of 5. None failed the database, and every
    restart had every transaction. e8 met the same at its stops and took
    either.
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
  * What happened: the first runs of e5 (seeds 2 and 3, R of 1 to 3 s,
    the test clock moved by 0.2 to 5 ms every millisecond) ended with a
    transfer's `rw()` throwing LookupTimeNotAvailableException from
    `RwEnvironmentImp.indexEntries()`, the read, at the action's read
    time, of the old values whose index entries the commit deletes (the
    accounts' directory has an index), after its action had run longer
    than the retain duration of the clock: it called `maintain(100)`
    inside, which waits while commits come (`Db.maintain()`, the
    handover). Nothing was written. Counted since, in e5's runs of soaks
    1 to 5: 118 of 6.6 million transfers (88 of 2,787 in seed 202, 8
    writers beside them), each followed by balances that the final check
    found exact.
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
    deleted, in the 41 runs of soaks 1 to 4: at the budgets of 100 and
    less (100 kB a call), 5 to 13 calls wrote, where the sentence gives 77
    to 563; at the budgets of 429 to 3,662, 6 to 9 calls, where it gives
    6 to 78; at 20,000 and more, 5 to 9 calls, where it gives 1 to 3,
    most of them for the cut's wait. Every quiet database kept 29 to 241
    kB, within 1 MB of its fresh twin (UA-8).
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
    nothing wrote up to 1,236,312 bytes beyond the budget's bytes, and
    600 calls of the 41 runs of soaks 1 to 4 more than 472 kB beyond (the
    sum of the Core's list); the largest values there are 1 MB. `MaintainOverrun`: with one live value of 8 MiB among small
    ones, a call of `maintain(100)` wrote 8,462,864 bytes, 84 times its
    budget.
  * Why: `Db.maintain()` runs parts while the cost spent is below the
    budget, and a part is never split: a step copies at least one KV
    whole, so a value of up to 8 MiB, and an M4 part's take may write a
    whole transaction's index nodes and 256 kB more (the Core's own
    list).
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

* **UA-10 (document). A put or a `w().execute()` at a stop can throw
  StreamIoException ("Storage is closing."), not IllegalDbStateException;
  nothing of it is written.**
  * Expected: `Database.stop()`: "A call that runs in another thread at
    the stop, and has not begun its commit, is refused: it throws
    IllegalDbStateException, nothing of it is written ... It holds for a
    put(), a delete() or a WBuilder's execute() that has not reached its
    commit, and for a read ... A read that loads from the storage as the
    storage closes may throw another DbException instead, a
    StreamIoException"; the second sentence names reads only.
  * What happened: e8 seed 303 of soak 3 FAIL, "writer 4:
    bergdb.storage.StreamIoException: Storage is closing.", the first in
    about 1,300 stops of e8 at a cache budget of 32 MB. e8 now keeps such
    a transaction and checks after the restart that it is there whole or
    not at all; with the least cache budget (`-De8.cache=4`) and values
    of up to 3 kB it comes in the first rounds: 12 seeds of 80 rounds
    (seeds 601 to 612, 960 stops) met 391 such calls, the writers'
    `w().execute()` with the stack of `Db.warmup()` and the transfers'
    `rw()` in their actions' reads (`Db.getOne()`, which the sentence on
    reads covers). None of them was there after the restart, and no
    database failed.
  * Why: `Db.executeInner()` warms the transaction's keys up before the
    write lock (`Db.warmup()`, reads of the KVs' keys at the latest time,
    which catch LookupTimeNotAvailableException only); a load from the
    stream while the storage closes throws the StreamIoException of
    `StorageManager.read()` out of `execute()`, before the go point. The
    warm-up of the record's reclaim step (`Db.warmupStep()`, 031-06)
    catches IllegalDbStateException only, so it can do the same.
  * Reproduction (about 10 s):

        java -ea -Xmx2g -De8.cache=4 -De8.value=3000 -cp build/bergdb-release.jar:out \
            E8StopEverywhere 601 DIR 20

    prints "writer N at a stop: bergdb.storage.StreamIoException: Storage
    is closing." with its stack (`Db.warmup()`), then that the
    transaction is not there.
  * Judgment: document, as UA-2 (or a small product change: the warm-ups
    end on a closing storage as on a stop, and the lock's check refuses
    the action with IllegalDbStateException, as `warmupStep()`'s comment
    intends). Nothing wrong was written and no database failed; an
    application that catches IllegalDbStateException at its shutdown
    meets a StreamIoException instead. Not new in 2026.7 for
    `Db.warmup()`; `warmupStep()` is 031-06's.

## 5. State

Written 11:00.

* **Done**: the apps e1 to e8 and their oracle in `java/stress/apps/`,
  the probes in `08-user-apps/probes/`, the runs of section 3 (quick
  runs, soaks 1 to 6, kill rounds 1 to 7, the hunt of UA-10), the
  findings UA-1 to UA-10. No product code changed; `java/stress/apps.sh`
  not changed.
* **Not done**: the apps are not in `apps.sh`'s modes (the lead's step);
  no 028-todo entries are written (the lead's, from section 4).
* **Where**: the branch `031-08-apps-a` of a clone of `main` at
  `ee8a8165`; the runs' logs and the kept data of the failures in the
  agent's run directory, not in the repository.
* **To continue**: new seeds of the soak lines of section 3 (each app's
  usage line in section 2), more kill rounds of e4 and e7, and e8 with
  `-De8.cache=4`. Sizes for apps.sh's quick mode, as the first runs of
  section 3 ran them (5 s to 2 minutes each on F53 beside week.sh):
  e1 `1 DIR 2000 1500`, e2 `1 DIR 30 100`, e3 `1 DIR 300`, e5 `1 DIR
  30`, e6 `1 DIR 12`, e8 `1 DIR 15`, e4 `parent 1 DIR 30 10 2000`, e7
  `parent 1 DIR 20 8 2000`; for soak and kill, section 3's rounds.


Log
===

2026-11-28. Created; the apps e1 to e8, the probes, the runs of section
3 on the release jar of `ee8a8165` (06:22 to 10:58) and the findings
UA-1 to UA-10.
