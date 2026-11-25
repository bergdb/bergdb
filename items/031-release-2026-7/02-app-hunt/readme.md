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

Made by an agent of lead-1125 (Claude Opus) on 2026-11-25, from 15:02,
on the branch `031-02` of a clone of `main` at `64d9d1c6`. Nothing in
`java/` was changed. The comparisons ran on the release jar built from
the tag `release-2026.6`.

## 1. State

In progress (2026-11-25, 15:55): the nine apps written and run; one
start refused after a kill (section 4) being reproduced; the stream kept
by an emptied database under `maintain()` measured against RB-007.


## 2. The applications

Nine apps, one Java file each, in [apps/](apps/), written from the
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
  and each sync. The parent kills it with `destroyForcibly` after 0.3 to
  8 s, starts the database itself and checks: the recovered k at least
  the last synced, never below the last recovery; every key, object,
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



