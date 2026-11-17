# 020-24-16 A job queue with competing consumers

Created 2026-11-09 by Frans Lundberg.

This is an application written the way a new user of 2026.4 would write it (u16, for
coord-1109, round 6 of 020-24's common brief). The class path held only the frozen release
candidate, `night/candidate/bergdb-release.jar` (d00096e). The only documents read were the
ones a user reads, from a clone of the candidate's repository: README.md,
`java/src/overview-pub.html`, the Javadoc of `bergdb.pub` and `bergdb.pub.util`, and
`releases/next.md`. The implementation was read only afterwards, to explain U16-1, U16-2 and
U16-5.


## 1. The application

The application is a durable job queue, as a small service would build one on BergDB. Its
files are in `/Users/f/fl/bench/2026-11-09/app-u16/app/` (1,524 lines):

* `JobQueueApp.java`: the queue, the oracle and the crash test.
* `RwProbe.java`: what rw() conflicts on, its waits and its throughput.
* `ScanCost.java`: U16-1.
* `EmptyRw.java`: U16-7.
* `StopProbe.java`: a close() while threads wait between reruns.

`run.sh` runs everything, one JVM at a time, in about 10 minutes, and writes the outputs to
`out/`.

* **Data.** A job is a Data Object at `/jobs/<id>` with these fields: state (PENDING,
  CLAIMED, DONE or DEAD), priority 0 to 9, prioRank (minus the priority), enqueuedAt,
  leaseUntil, owner, a claim token, attempts, a version, a payload, an account, an amount
  and a fail mode. A dead letter is moved to `/dead/<id>`. The effect of a job is its amount,
  added to an Account object at `/acct/<k>` in the same transaction that marks the job DONE.
  That makes the effect exactly once, not merely the claim.
* **Indexes.**
  * "pending": state, prioRank and enqueuedAt. `eq("PENDING")` lists the pending jobs by
    priority and then by age.
  * "leases": state and leaseUntil. `eq("CLAIMED").to(now, false)` lists the expired leases.
* **Producers.** Each producer enqueues 1 to 4 jobs per `w()` and stops while 3,000 jobs are
  outstanding. Of the jobs, 80% succeed, 15% fail their first attempt, and 5% always fail.
* **Consumers.** N threads each scan the "pending" index for 16 candidates and claim one,
  either the first ("first") or one at random ("random"). The claim is an `rw()` that reads
  the job, checks that it is PENDING, and puts it CLAIMED with a token and a lease of 1.5 s.
  The finish is another `rw()` that checks the state and the token, then does one of three
  things:
  * on success, adds the amount to the account and puts the job DONE;
  * on failure with attempts left, puts it back to PENDING;
  * after 3 attempts, deletes `/jobs/<id>` and puts `/dead/<id>`.

  A finish whose token no longer matches is stale and writes nothing. In the crash tests,
  0.3% of jobs sleep past their lease, to exercise stale finishes. A reaper thread returns
  expired leases in an `rw()`, either to PENDING or to dead letters.
* **The oracle.** Each run writes its own log, a memory-mapped file: a line reaches the OS
  when `log()` returns, so `Runtime.halt()` keeps it. The log has these lines:
  * an intent before each change;
  * each committed change, with the job's new version and `Transaction.getTime()`;
  * a durable mark every 50 ms: `t = db.currentTime(); db.sync()`, then log t.

  After each run, crashed or clean, the verifier opens the database and checks it against
  the log:
  * Per job, the run's changes have contiguous versions starting where the previous run
    ended. Each change starts from the state that the change before it left: a claim only
    from PENDING, a finish only from CLAIMED, and only by the claim's token. This catches a
    double claim or a lost update.
  * The database's version is at least that of every change at or before the last durable
    mark. It is at most the last logged version, or that version plus one with an open
    intent.
  * The transaction that wrote the job in the database, by `get()` and
    `transactionInfo().time()`, is the logged change of that version, in the logged state.
  * Each account holds exactly the amounts of its DONE jobs, and their count.
  * No job is in both `/jobs/` and `/dead/`.
  * Both indexes equal the primary scan, and "pending" is in order.

  After the last run, which drains the queue, every kept job is DONE or DEAD as its fail
  mode says, and done exactly once. The oracle was tested by injecting two faults into the
  application, and it found both (`out/inject-*.txt`): a claim that 1 time in 50 takes a
  CLAIMED job (reported by the oracle as "C from state CLAIMED"), and an effect added twice
  1 time in 1,000 (reported as account mismatches).
* **The crash test.** A parent JVM starts a child JVM, which halts itself after 1.5 to 4.5 s.
  The parent opens the database, verifies it and closes it, then starts the next child. The
  last child drains the queue and closes cleanly.


## 2. The findings

No wrong result was found. In two crash tests, there were 20 crashes with `Runtime.halt()`:
8 crashes with 8 consumers, 16 accounts and 20 ms of work per job, and 12 crashes with 16
consumers, 2 hot accounts and the "first" strategy. Up to 16 jobs were CLAIMED and durable
at a crash. Across both tests (`out/crash-8.txt`, `out/crash-12-first.txt`), 52,411 jobs
and 0 problems:
* no job was lost after it was durable;
* none was claimed twice for one version, or done twice;
* every account was exact;
* the transaction that wrote each job matched its logged change;
* both indexes always equaled the primary data.

After each crash, the database agreed with the Javadoc's "What a crash keeps": every change
at or before the last durable mark was there, and the changes lost were later ones, 1 to 205
per crash, the last 50 to 100 ms of work.

The findings are about performance under a queue's pattern, and about what a user cannot
learn about contention in rw() from the Javadoc. Most severe first:

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U16-1  | bug | high   | a scan's head slows with each entry that left it      | ScanCost    |
| U16-2  | bug | medium | rw() starves under a hot key: reruns are not fair     | RwProbe     |
| U16-3  | doc | medium | what rw() conflicts on is not said                    | RwProbe     |
| U16-4  | API | medium | no scan in an rw(): "claim the next job" is two steps | JobQueueApp |
| U16-5  | doc | medium | commits are serial: rw() throughput flat in threads   | RwProbe     |
| U16-6  | API | low    | no rerun policy or run count; the first wait 10 ms    | RwProbe     |
| U16-7  | doc | low    | an rw() that writes nothing writes a record           | EmptyRw     |
| U16-8  | doc | low    | no bound on rw()'s time, so a lease cannot be sized   | JobQueueApp |
| U16-9  | API | low    | a scan reads every value: no keys only, count, limit  | JobQueueApp |
| U16-10 | API | low    | an action has no clock of its transaction             | JobQueueApp |


## 3. The findings in detail

### U16-1. A scan's head slows with each entry that left it, without bound (bug, high)

A queue scans the head of its pending range, and every job it takes leaves that head. The
time to read the first 16 entries of `eq("PENDING")` grows linearly with the number of jobs
that ever left PENDING. A restart does not reduce it, and neither does reclaim. The primary
scan of a directory behaves the same way after deletes, about ten times less. The Javadoc of
UseIndexBuilder and UsePrimaryBuilder says nothing of this, and neither does
`releases/next.md`.

`ScanCost <dir|memory> N M1,M2,... [restart|retain|rebuild]` measures the mean of 100
scans after 20 to warm up. It puts N objects `{state: PENDING, n}` in `/jobs/` with the
index (state string, n long), and a copy of each in `/q/`. It then puts the first M back as
DONE and deletes them from `/q/`, in w()s of 100 each. File database, N = 200,000
(`out/scancost-restart.txt`):

| Left the head | First 16 of the index | First 16 of the primary scan |
|---------------|-----------------------|------------------------------|
| 0                  | 0.138 ms  | 0.043 ms |
| 50,000             | 4.973 ms  | 0.346 ms |
| 100,000            | 10.286 ms | 0.755 ms |
| 190,000            | 24.381 ms | 1.963 ms |
| 190,000, restarted | 27.242 ms | 2.849 ms |

* Reclaim, with N = 60,000 and M = 50,000 (`out/scancost-retain.txt`): startup distance 5,
  retain 1 s, then 12,000 puts of 10 KB. The first available lookup time moved, and the
  index's head took 5.5 ms, against 4.5 ms before the reclaim.
* A new index on the same fields, with the same data (`out/scancost-rebuild.txt`): built in
  0.5 s, its head took 0.049 ms against 4.5 ms for the old one. The only remedy a user has is
  to build the index again under another name and delete the old one.
* In the application (`out/bench-60s.txt`, 2 consumers, 60 s), the scan's mean grew from
  0.56 ms in the first 5 s to 5.1 ms at 60 s and 5.6 ms at 70 s. Claims fell from about
  2,650/s to about 350/s, and the scan is most of a consumer's loop. By the measured slope,
  about 0.125 ms per 1,000 entries, a queue of a million jobs a day would scan for about
  0.1 s at each claim after a day.
* The cause, read afterwards: a key tree keeps the nodes of deleted keys. Reclaim touches
  them ("Nodes that hold deleted keys only ... kept their versions before pStart, and
  lookups still pass through them", `Reclaim.java`, about line 672; 011-01, Q7), and a scan
  of the latest state passes through them. This is 021-25's option (b) seen from the
  reading side. The known issue in `releases/next.md` covers reclaim's cutting, not this.
* The severity is high because the slowdown is unbounded for a common pattern (a queue, an
  outbox, a FIFO). Neither a restart nor a retain duration reduces it.

### U16-2. rw() starves under a hot key (bug, medium)

N threads each run `rw()` read-modify-writes of one shared counter in a tight loop for 2 s
(`RwProbe`, `out/rwprobe.txt`). Every increment is counted, and the counter is exact. The
throughput, however, goes to one thread:

| Threads, one key | Tx/s | Reruns | Per thread, tx | Longest rw() |
|------------------|------|--------|----------------|--------------|
| 1  | 326,979 | 0   | 653,958      | 80 ms    |
| 2  | 324,328 | 9   | 1 to 648,655 | 2,599 ms |
| 4  | 301,263 | 32  | 1 to 555,173 | 2,620 ms |
| 8  | 311,292 | 91  | 1 to 432,727 | 2,063 ms |
| 16 | 292,935 | 172 | 1 to 508,745 | 2,692 ms |

A thread whose action conflicts sleeps 10, 20, 40 and up to 640 ms. Each of its reruns
conflicts again, because the winner commits every few microseconds. So its `rw()` returns
only when the winner stops: at the end of the test, 2.6 s in. With 8 keys and 16 threads,
the longest rw() took 2.0 s, and one thread made 634 transactions while another made 61,326.
In the application, with 8 consumers and 1 or 4 hot accounts, the finish took up to 189 and
676 ms (`out/hot-accounts-*.txt`), and up to 1,328 ms with one account in an earlier run,
close to the lease of 1.5 s. The Javadoc of `Connection.rw()` says "Under overload it may never
commit", with a long action as its example. It does not say that two threads with tiny
actions on one key are enough, or that the wait has no fairness. `RwTransaction.java`'s
loop sleeps and runs again, with no queue or priority for a transaction that has waited.

### U16-3. What rw() conflicts on is not said (doc, medium)

The package says: "If another transaction changes what the action has read before the
action's writes are made, BergDB runs the action again". `RwProbe` commits B in another
thread while A's first run is in its action (`out/rwprobe.txt`):

| A's action | B commits | A runs |
|------------|-----------|--------|
| reads a, writes x                 | a put of a                  | 2            |
| reads a, writes x                 | a put of b (another key)    | 1            |
| writes a without reading it       | a put of a                  | 1, A's value |
| reads an absent key n, writes x   | a put of n                  | 2            |
| exists(n2), writes x              | a put of n2                 | 2            |
| reads a, writes x                 | a delete of a               | 2            |
| reads a (absent), writes x        | a delete of a, still absent | 2            |
| reads b, writes x                 | a put of b, the same value  | 2            |
| reads a, writes nothing           | a put of a                  | 2            |
| reads a, writes x                 | an rw() reads a, writes y   | 1            |
| reads a, writes b                 | an rw() reads b, writes a   | 2            |
| reads /c/1, writes /c/1 (indexed) | a put of /c/2               | 1            |
| reads /c/1, writes /c/1 (indexed) | an index on /c/ created     | 2            |

So the read set is per key, an absent key included, and exists() counts. A put of the same
value is a change, and so is a delete of a key that is already absent. A blind write never
conflicts, and the later commit wins. A read-only action runs again. Write skew is
prevented. Other keys of an indexed directory do not conflict, but an index creation does.
None of this is in the Javadoc. A user needs it to design keys, for example to know that a
consumer which only checks a job's state still reruns when that job changes.

### U16-4. No scan in an rw() (API, medium)

RwEnvironment has `get()`, `exists()`, `put()`, `delete()` and `setOutput()`, but no
`useIndex()` or `usePrimary()`. A consumer therefore cannot take "the first pending job" in
one transaction. It scans outside the transaction, at the latest state, then claims one
candidate in an `rw()` that reads it again. The Javadoc does not show this pattern or say
that a scan is outside the read set. Its cost in the application is lost claims, the
candidates that another consumer took between the scan and the claim. Fresh databases, 8 s
of producers, 64 accounts (`out/matrix-*.txt`):

| Consumers | Claims/s, first | Lost, first | Claims/s, random | Lost, random |
|-----------|-----------------|-------------|------------------|--------------|
| 1  | 1,281 | 0%    | 1,271 | 0%    |
| 2  | 1,502 | 35.2% | 1,729 | 4.9%  |
| 4  | 1,825 | 59.0% | 2,469 | 18.0% |
| 8  | 2,359 | 74.5% | 2,924 | 41.4% |
| 16 | 2,807 | 84.3% | 3,045 | 66.2% |

Most lost claims run once: the scan was stale, and the claim sees CLAIMED. With 2 or more
consumers, 0.8 to 4.0% of the claims ran twice, a real conflict, each costing at least 10
ms (U16-6); the longest claim took 25 to 92 ms. Taking a random candidate of the 16 instead
of the first raised the throughput by 8 to 35%. A consumer's loop is mostly its scan: 0.70
to 1.63 ms for 16 candidates, against 0.04 to 0.98 ms for the claim's rw() (U16-1, U16-9).

### U16-5. Commits are serial: rw() throughput does not grow with threads (doc, medium)

Each thread does read-modify-writes of its own counter, so no transaction conflicts:
297,341 tx/s with 1 thread, 294,576 with 2, 302,618 with 4, 302,247 with 8 and 238,041 with
16 (`out/rwprobe.txt`). An action's reads run in parallel, but every commit takes the Core's
write lock (`Db.execute()`, `synchronized (writeLock)`). The Javadoc does not say that
transactions commit one at a time, which is what a user needs in order to size the number
of consumers. More consumers help a queue only where its time is outside the commit: the
scans and the job's own work.

### U16-6. No rerun policy and no run count; the first wait is 10 ms (API, low)

In `RwProbe`, A's read is changed k times in a row. The gaps between its runs were 11, 31, 51,
84, 169, 331 and 648 ms, so 7 conflicts took 1.3 s. A claim's rw() takes about 30 µs,
so the first wait is about 300 times the transaction. A consumer that loses a race would
rather give up at once and take another candidate, but it cannot:
* no option sets the waits or a maximum number of runs;
* the action's exception ends the rw() only after the sleep, when the next run begins;
* `Transaction` does not say how many runs it took, although `RwTransaction` counts them
  (`runCount`).

The application counts the runs with an AtomicInteger in the action.

### U16-7. An rw() that writes nothing writes a record (doc, low)

100,000 rw()s that only read grew the stream by 4,803,072 bytes, about 48 bytes each
(`out/emptyrw.txt`), and each has a transaction time. In the application, every lost claim
is such a transaction: with 16 consumers and "first", 153,423 of them in 10 s, about 7 MB
of stream. The Javadoc does not say that a read-only rw() is written. The application could
check the state with `get()` before the rw(), but that is one more read.

### U16-8. No bound on rw()'s time, so a lease cannot be sized from the docs (doc, low)

A lease must be longer than a consumer's finish takes, or the reaper takes the job back
while it is being finished. That would be correct, but wasted work. With one hot account the
finish took up to 1.3 s (U16-2), and the waits alone reach 640 ms each. The Javadoc gives the
waits but no bound on how many there are. The application uses 1.5 s and checks the token
at the finish, so a late finish writes nothing (20 stale finishes in the last run of
`out/crash-12-first.txt`, all correct).

### U16-9. A scan reads every value: no keys-only scan, count or limit (API, low)

`kvs()` and `objects()` both read and convert each value. A consumer that needs 16 keys
reads 16 jobs, and its "is the queue empty" check and its count of outstanding jobs read
every pending and claimed job. There is no `limit()`; the application breaks out of the
loop, which the Javadoc allows ("an iterator that is not read to its end may be dropped").

### U16-10. An action has no clock of the transaction (API, low)

A lease's expiry is set in the action. The transaction's own time is known only through key
replace (`${transactionTime}`) and after the commit, so the application uses
`System.currentTimeMillis()` in the action. A reaper in another process, or after a restart,
then depends on the wall clock, not on the database's.


## 4. What went well

* Serializable rw() worked as a user hopes. The claim "read PENDING, put CLAIMED" never let
  two consumers hold one version of a job, in about 400,000 claims in the runs of `out/`
  that print their counts, and more in the crashed runs. Write
  skew and the read of an absent key were protected (U16-3).
* "What a crash keeps", in Database's Javadoc, was exact and enough to build an oracle on: a
  prefix of whole transactions, and every transaction before a returned `sync()` durable.
  The durable marks (`currentTime()` then `sync()`) relied on `currentTime()`'s promise, and
  no check failed.
* `transactionInfo().time()` after a restart gave the time of the transaction that wrote each
  job, and it equaled the logged commit's time in every case checked (67,237 over the crash
  tests). This lets an application match its own log to the database.
* A restart took 0.23 to 1.47 s, growing with the stream while it was below the startup
  distance. The indexes needed no rebuild after a crash, and they always
  equaled the primary data.
* A shutdown in the middle of the contention worked (`StopProbe`, `out/stopprobe.txt`).
  8 threads ran rw()s on one hot key, most of them waiting between reruns. close() returned
  in 14 to 16 ms, and every waiting rw() threw an IllegalDbStateException
  (`bergdb.core.DbStoppingException`) within 0.51 to 0.56 s, at the end of its sleep. Each
  counter equaled the commits after a restart.
* Throughput, on a shared F53 (load 2 to 8, another session's C builds):
  * 1,270 claims/s with 1 consumer and 3,045/s with 16 (random), with about 2,400 jobs/s
    through the whole cycle (enqueue, claim, finish), on a fresh database (U16-1);
  * about 300,000 tiny rw()s a second without conflicts;
  * enqueue w()s of 1 to 4 jobs in 0.1 to 0.3 ms.
