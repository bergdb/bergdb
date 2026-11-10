# 023-03. The test specification

Created 2026-11-10 by Frans Lundberg. Status: open.

The tests that judge a solution of 023, whatever its mechanism: Frans's
rule as a test that can be run, its measures and pass criteria, the shapes
of data and the churn it must hold for, the correctness checks around it,
and what must not regress. Tests are T1 to T12, measures M1 to M14, pass
criteria C1 to C12; cite them as "023-03, T1". A prototype of T1 and T4
ran on `main` (section 8): today's code fails both, at every size tried.


## 1. What the tests are for

### 1.1 Frans's words

The rule, 2026-11-10, 08:50: "Deletes need to be handled so that
eventually, some time after the retain period has passed, deleted KVs
consume no resources of the database. [...] Either way, a deleted KV must
consume zero resources eventually after the retain period has passed."

The scan bound, 08:29: "Scans are supposed to be O(n) amortized for
scanning n items."

The test, 09:55: "It would be good to have a formulated rule that can be
tested in practice. Say we have an hello-world database, created with
c.put("/a.txt", "Hello world!"). We can check its resource consumption
and compare with the consumption of a database that adds a large amound
of data, then deletes it so only the "/a.txt" item remains. Eventually,
the consumed database resources should come back to something similar to
the original hello-world database." And: "Current correctness testing
must continue to work. No regression. Performance (stream size, memory,
time) should stay near current performance, but can be discussed."

### 1.2 How the tests are made

* **By what a user pays**, not by a mechanism: stream bytes, key nodes
  followed, objects in memory, the size of records, how far back the
  first available time lags. No test asks whether a node was unlinked or
  a klong dropped; it asks what is left and what it costs. So any
  solution can be judged, and so can today's code.
* **Counts before times.** A count is the same in every run and on every
  machine (P2, P8), so its tolerance can be small and justified from the
  code. Times are noisy on a shared F53; they appear in T10 only.
* **Against a twin.** Each database is compared with its twin, a database
  with the same settings and the same live KVs that never held the
  deleted ones (023-02, 3.2), driven by the same transactions. A ratio to
  a tiny database is fragile; a difference from the twin within a fixed
  allowance, the same for every N, is not.
* **Runnable today.** The Core API and test hooks that exist, or a few
  test-only lines (2.5); the prototype takes M1 to M11 of T1 and T4.
* **Correct as they go.** Every test checks lookups against a model at
  the latest time and at earlier available times (T6): the rule must not
  be met by losing history that should still be there.
* Each test names the requirements of 023-02 that it checks.

### 1.3 Terms

023-02's terms hold (its section 3.2): R, f, dead, B (the node size, 30),
H, the twin, an iteration span. Here also:

* **The emptied database**: puts N keys besides "/a.txt" and deletes them
  again, so that only "/a.txt" is left. **Its twin**: the same code and
  settings with N = 0.
* **The drive**: the transactions after the deletes, the same for both
  (2.3). **The window**: the drive's last R of time.
* **h_fill**: the most key nodes that a get of a key of the fill follows,
  after the fill, over a sample of 200 keys (H of the deleted keys).
* **L**: the twin's live keys, those a scan of every key returns:
  "/a.txt" and reclaim's three internal keys (settings, table, current
  row); L = 4 in T1, 1 with R forever.
* **A phase twin**: the twin with P more overwrites of "/a.txt" before the
  drive (P = 137 and 611). Its iterations fall elsewhere; what it differs
  from the twin by is the noise a tolerance must cover.
* **Strict** and **bounded**: the two allowances of 2.6. Strict: the
  emptied database ends as its twin, a few nodes apart. Bounded: each
  live key may keep a path as tall as the deleted keys' was (nodes are
  not merged; 023-02, R10's must, R12 (a), F5).


## 2. T1, the hello-world convergence test

Checks 023-02, R1 to R6 and R13 to R15. Frans's test, made exact.

### 2.1 The databases and their settings

| Setting           | T1, in the Core                            | Why                        |
|---|---|---|
| Stream            | CutStream: reads below the cut refused     | a stale read fails at once |
| Clock             | CoreTestClock, 1 ms a transaction          | R passes without waiting   |
| R                 | 1 s, set at the creation                   | the API's smallest         |
| Startup distance  | 100 kB (`DbBuilder.startupDistance`)       | an iteration every 0.2 MB  |
| Node size         | 30                                         | the default                |
| Eviction          | none (`testSetup`); budget 1 MB for M13    | exact counts               |
| Internal fraction | 0.25                                       | the default                |
| Fill              | N keys, 100 a transaction, values of 100 B |                            |
| Deletes           | the N keys, 100 a transaction              |                            |
| Drive             | 4,000 overwrites of "/a.txt", 1,000 B      | 4 R, 40 startup distances  |
| N                 | 1,000; 100,000; 1M; large: 10M             | one end state for all      |

Frans, 2026-11-10, 10:49 (023-02, F7): an explicit `maintain()` may be
added to test a solution; calling it again and again must, eventually,
bring the emptied database to about the resources of a fresh hello-world
database. A solution that adds it gets a second drive in T1 and T2:
repeated `maintain()` calls instead of the overwrites, measured as above.

The large run, on disk: a `FileStream`, the capacity controller with a
budget of 64 MB, a startup distance of 5 MB (the Pub API's smallest), 1,000
puts or deletes a transaction, and a drive of 200,000 transactions (40
startup distances of values, 200 R).

The Pub form, Frans's own words (a row of T2): a `Database` built with
`memory()`, a `TestClock`, `startupDistanceInMb(5)` and
`setRetainDuration` of 1 s; `c.put("/a.txt", "Hello world!")`; N files
"/k/" and 10 digits put and deleted through a `Connection`; the drive as
in the large run; the measures through `DatabaseImp.getDb()`.

### 2.2 The phases

1. **Create.** Start, set R, put "/a.txt" = "Hello world!" (12 bytes).
2. **Fill** (the emptied database only). Put the N keys of the shape (T2)
   in key order, once, or three times for old versions. Measure h_fill.
3. **Delete.** The N keys, in the order of the row (T2). Check lookups at
   once (T6), among them a scan at a time before the first delete, if it
   is still within R: all N keys.
4. **Drive.** K overwrites of "/a.txt", the clock 1 ms on each. In the
   window, M1 after each transaction and M8 after every 50th.
5. **Measure** M1 to M10 and M14 at the end of the drive.
6. **Restart.** Sync, close, and start on a copy of the stream (on disk:
   the same directory). M12 at once, before any read; M11 after the start
   and again after a probe: a scan of every key and a get of "/a.txt"
   through the ordinary follower.
7. **Check** lookups (T6), and close both databases with `close()`.

### 2.3 The drive

K = max(4 R / dt, 40 sd / w) transactions, with dt the clock's step, sd
the startup distance and w the value size: 4,000 with the settings above.
The same for both databases, and fixed: it does not grow with N.

* **Why a drive.** Nothing runs without the application's calls (010-01,
  P3), so an idle database never cleans up (023-02, 3.4 and F7):
  "eventually" is counted in the user's writes. Overwrites of "/a.txt"
  are the smallest writes that keep the live data the same; the old
  versions they make are on both sides and cancel out.
* **Why fixed.** "Some time after the retain period has passed" is a
  bound after R. A drive that grew with N would accept a cleanup that
  falls further behind with every key deleted, as reclaim does today
  (021-25, U18-1). A database that converges only after a drive in
  proportion to N fails T1 at the larger N, as it should (Q1).
* **Why 4 R and 40 startup distances.** Today's reclaim starts an
  iteration every max(2 sd of growth, R / 4 of time), and cuts at an
  iteration's pCut once its tEnd is R old and the startup position has
  passed its pSafe (`Reclaim`, class comment). The twin's first cut comes
  after 1.0 to 1.5 R of drive (prototype: between transactions 1,000 and
  1,500). 023-02 (F6) recommends that a dead version is gone two cuts
  later: about R and three iteration spans. 4 R allows that twice over,
  and 40 startup distances are 20 iteration spans of bytes.

### 2.4 The measures

Taken between transactions by the test's thread, under the write lock
where a read must not meet a writer. All exist on `main` but M14.

| ID  | Measure                                      | How, on `main`                        |
|---|---|---|
| M1  | kept: stream bytes from the decided cut      | length minus `getFirstAvailablePos()` |
| M2  | disk: the `.bergdb` files and their bytes    | the directory, after sync and close   |
| M3  | lag: now minus the first available time      | `getFirstAvailableLookupTime()`       |
| M4  | reach: key nodes reachable, latest and at f  | a scan of every key, H1               |
| M5  | dead: KEY klongs in M4's nodes, not live     | H1: deleted or shadowed               |
| M6  | get: key nodes a get of "/a.txt" follows     | `getOne`, H1                          |
| M7  | head: key nodes to the first, last user key  | `getMany` both ways, H1               |
| M8  | D: dirty index nodes, the most in the window | `TransSeq.visitGotDirtyNodes`         |
| M9  | the largest record in the window             | `Trans.nextPos - tpos`                |
| M10 | the touch: nodes visited, dirtied; steps     | `Reclaim.Stats`, last done iteration  |
| M11 | resident index objects, handles, restarted   | `Residents`, `Cache3.handles()`       |
| M12 | the start: versions loaded, records rerun    | `cacheStats().loads`, `StartInfo`     |
| M13 | resident bytes under eviction, the most      | `Residents.bytes()`, budget 1 MB      |
| M14 | kept records: deleted keys' value nodes      | H2, a record walker (new)             |

Notes:

* M1 is the decided cut, a function of the transactions. The physical
  cut waits for durability (`Reclaim.cutIfDurable`), so where it lands
  depends on timing, as StreamDigest found (its comment, 015-08). On a
  `FileStream` with a test clock the gap is large: the prototype's twin
  at a startup distance of 1 MB had 6.4 MB from the decided cut and 25 MB
  in 13 files. The cut waits for durability, a thread of its own deletes
  the files, and a test that runs thousands of transactions a second
  outruns both. So M2 is taken after `sync()`, one more transaction and
  `close()`, and reported.
* M4 counts every node that a scan of every key at the latest time
  follows, by id, the space root included: the nodes reachable at that
  time (023-01, 5.2). The same scan at f gives M4 at f (023-02, R3).
* M7's first user key is the first after the internal keys "/#i/...".
* M11's probe goes through the ordinary follower, which loads and
  installs as any read does; M12 is read before any read.

### 2.5 New test hooks

None in `java/src` is needed for T1 to T4. T1 to T4 live in package
`bergdb.core`, as StreamDigest and ReclaimStress do, so `Reclaim.Stats`
and `Db.internal()` are at hand.

* **H1, a counting follower** (the prototype's `Count`, 35 lines): a
  `PointerFollower` that wraps `NodeCollection.maintenance()` and counts
  the key nodes it follows, by id, with their KEY klongs and the dead
  ones (`KeyNode.getKlong`, `getDeleteBitmapAtTime`, `Klong`). Public
  methods only. A maintenance read loads without installing, so a
  measure changes nothing resident: after a restart, the emptied database
  at N = 100,000 held 31 resident objects after a measure that followed
  7,902 key nodes. Shared by the tests from `src-dev`.
* **H2, a record walker** for M14 (about 60 lines, test-only, not in the
  prototype): reads the records from `getFirstAvailablePos()` to the end
  (`NodeStream.createTransIteratorFromExactStartupPos`,
  `StoredTrans.parse`) and counts value nodes by key, delete nodes, key
  node versions and their klongs. It checks R2 directly: no value node
  of a deleted key once it is dead.
* **H3, a read hook for the Pub tests** (T5): the Pub API's scans make
  their own `GetMany`, so a Pub test cannot hand them H1. A test-only
  static beside `Db.testHooks` that wraps the follower of `newGetData`
  and `newGetMany` when set. No Core API (P12).

### 2.6 Pass criteria

All measures at the end of the drive, against the twin's. Three
allowances, from the prototype's phase twins and the shape:

* **a_n, nodes.** Strict: 10, twice 7, the largest difference in any
  node count between the twin and its phase twins (resident objects, 85
  against 92). Bounded: 10 + L h_fill, so each live key may keep a path
  as tall as the deleted keys' was.
* **a_b, bytes**: a_n times 512, a full key node version (32 + 16 B).
* **W**: the twin's swing of M1 in the window, its most minus its least
  (378,264 bytes in the prototype). The cut moves an iteration at a time.

| C   | Measure                    | At most               | Why this tolerance                   |
|---|---|---|---|
| C1  | M1, the most in the window | twin + W + a_b        | phase twins: 0 and -23 kB            |
| C2  | M3                         | twin + R / 4          | R / 4 apart; phase twins +137 ms     |
| C3  | M4, latest and at f        | twin + a_n            | phase twins +0                       |
| C4  | M5                         | twin + B, strict only | the twin's leaf: 0 to B - 1 shadowed |
| C5  | M6, M7                     | twin + a_n            | phase twins +0                       |
| C6  | M8                         | twin + a_n            | phase twins +5                       |
| C7  | M9                         | twin + a_b            | phase twins +376 bytes               |
| C8  | M10                        | twin + a_n            | the touch passes the twin's nodes    |
| C9  | M11, after the probe       | twin + a_n            | phase twins +7                       |
| C10 | M12, the start's loads     | twin + a_n            | the section holds the twin's records |
| C11 | M14, deleted keys' values  | 0                     | R2                                   |
| C12 | M2, M13                    | reported              | 023-02's non-goals, K17 and noEvict  |

T1 passes when C1 to C3 and C5 to C11 hold for every N with the bounded
allowance, and T6 finds nothing. C4 and the strict allowance are reported
until Frans decides 023-02's F1 and F5 (Q2). Because each measure is held
to the twin's, which does not depend on N, T1 also checks that the end
state is the same for every N, within a_n, which with the bounded
allowance grows with h_fill only.


## 3. T2, the matrix of shapes and orders

T1 for every row, at N = 1,000 and 100,000; at 1,000,000 for "after"
and "hashed"; at 10,000,000 for "after" in the large run.

| Shape     | The keys                            | What it exercises                        |
|---|---|---|
| after     | "/k/" and 10 digits, after "/a.txt" | a deleted range at the end (U17-1)       |
| before    | "/0/" and 10 digits                 | the head of a range (U16-1)              |
| around    | half before, half after             | both ends of a live key                  |
| inter     | 6 bytes, "/a" and 4 chars, spread   | a live key's own tree: K3, K11, F1       |
| long      | 50 bytes, 8 segments                | segment trees of deleted keys (K6)       |
| hashed    | "/h/" and a hash in 16 hex digits   | deletes in every leaf; leaves empty last |
| sparse    | "after", all but every 30th deleted | underfull nodes (K10, R12 (b))           |
| versions  | "after", each key put 3 times       | old versions (K7, K8, R7)                |
| Pub files | Frans's form, "/k/" files           | the Pub API's keys (2.1)                 |
| Pub index | N objects with an indexed field     | index entries are keys (K13)             |
| Pub drop  | an index filled, then `deleteIndex` | the cleanup thread's 100-key deletes     |

* **Orders**, for "after" and "hashed": ascending (a FIFO), descending,
  random; gradually, one delete a transaction with an overwrite of
  "/a.txt" between (N = 1,000 and 100,000); and in one transaction of
  10,000 deletes, for R11's large transactions.
* **Settings**, for "after" and "hashed" at N = 100,000: node sizes 8 and
  62; startup distances of 5 MB and, in the large run, 50 MB, the drive
  scaled to 40 of them.
* **The twin of "sparse"** holds the N / 30 keys left, put fresh in the
  same order and transaction sizes (023-02's twin), and L counts them.
* Why these: each row puts the deleted keys' remains where a different
  part of the Core meets them: scans from either end (`GetMany`), a live
  key's own path and leaf (`Dag.setValue`, the time split), segment trees
  (`Dag.setNode`), spread leaves (space splits), shadowed klongs, and the
  Pub API's key layouts. A solution that cleans up one shape only fails
  another row.


## 4. Scans and churn

### 4.1 T3, the scan bound at every time

Checks 023-02, R9 and R10; its F3 and F4.

* **Setup.** T1's emptied database and its twin at N = 100,000, each
  shape of T2, with R forever and with R = 1 s.
* **Rounds.** Right after the deletes, 1,000 rounds of: one overwrite of
  "/a.txt", then five scans at the latest time (the first user key
  forward, the last backward, every key, the deleted range, empty, n =
  0) and, while it is within R, a scan of every key at a time before the
  deletes (n = N + 1).
* **Measures.** For each scan, the key nodes it follows (H1) and n, the
  KVs handed to its stop condition.
* **Pass**, for each kind of scan over the 1,000 rounds: the sum of key
  nodes followed is at most 2 (n + 1) H summed over the scans, plus 2 H
  times the puts and deletes made, with H = h_fill (023-02, R9's form,
  c = c' = 2). A put or a delete may leave its path for later scans to
  pass once; the scans may not pay for it again in every round. The
  worst single scan is reported (P1; F4).
* **Why it is not part of T1.** T1 judges the end state; T3 judges every
  time on the way, R forever included, where nothing is ever cut. A
  solution that cleans up only at reclaim's touch passes T1 and fails T3
  between touches: that difference is 023-02's F3.

### 4.2 T4, a steady-state queue

Checks 023-02, R6, R9 and R11 to R14. A constant live set under ever more
operations: a solution cannot clean up only at the end while it is slow
during the deletes.

* **Setup.** T1's settings. L = 1,000 live keys; each transaction puts key
  i and deletes key i - 1,000. Keys in time order ("/q/" and 12 digits)
  and hashed ("/q/" and 16 hex digits); values of 100 bytes; M = 100,000
  and 1,000,000 transactions.
* **Checkpoints**, every M / 10: M1, M3, M4, M5, M8, M9 since the last
  checkpoint, the cuts, and the queue's head: the key nodes that a scan
  for the first entry from "/q/" follows.
* **Pass.** After a warm-up of 10 L transactions, every later checkpoint
  is within T1's bounded allowances of the first one after the warm-up
  (C1, C2, C3, C6 and C7, with h_fill measured there); the queue's head
  within 4 H; and T3's sum over a head scan after every transaction (M =
  100,000).
* **Its twin**, reported: a database with the same 1,000 live keys, no
  deletes, driven by T1's drive.

### 4.3 T5, the applications' workloads

Checks 023-02, R6, R9 and R13 through the Pub API. The reproductions of
020-24 and 021-25, which today live outside the repo, move into
`java/stress/` with counts (H3) instead of times:

| Workload             | From                    | Pass if                                   |
|---|---|---|
| A job queue's head   | U16-1, `ScanCost`       | 16 entries: within a_n of a rebuilt index |
| An index churned     | U17-1, `ScanAfterChurn` | after 160 cycles: within a_n of none      |
| A metrics store      | U18-1, `Repro`          | 12 h: cuts keep up; bytes as the ring's   |
| The ring, a control  | U18-1, `Repro` ring     | as today: bounded, a cut every 30 min     |
| Index churn          | U14-1                   | cuts keep up: M3 within R + 2 spans       |
| A FIFO in time order | 021-25, `ReclaimFifo`   | as T4, at its settings (2 MB, 20 s)       |

U16-1's head is the first 16 entries of `eq("PENDING")` after 190,000
jobs left it, against the same index built again over the same data;
U17-1's is an empty scan at the end of index "in" after 160 cycles of
index "ix2", against the same scan before the cycles. The ring is a
control: it passes today and must still pass.


## 5. Correctness during the tests

### 5.1 T6, lookups against a model

Checks 023-02, R1 and R19. Inside every test above, and in the prototype.

* **The model**: every key's history, its puts and deletes by
  transaction time, as ReclaimStress keeps it.
* **At the end of each phase and after every restart**: 300 sampled keys
  at the latest time, at f' = max(f, now - R) and at a random time in
  [f', now]; every key at every transaction time from f instead, when N
  is at most 1,000 (ReclaimStress's exhaustive check); scans of every
  user key at f', at a random time and at the latest time, the same keys
  and values as the model; a get at f - 1 refused with
  `LookupTimeNotAvailableException`; and f <= now - R, the retention
  guarantee.
* **The history a cleanup must not take**: right after the deletes, a
  scan at a time before the first delete, while it is within R, returns
  all N keys; at the end, a scan at f' equals the model.
* **Pass**: no difference, and no exception but the expected refusals.

### 5.2 T7, restarts, crashes and readers at chosen points

Checks 023-02, R16 to R18 and R20.

* **Restarts.** T1 at N = 1,000 and 100,000, with a restart (sync, close,
  start on a copy) after the fill, after half the deletes, right after
  them, at the drive's first cut, and every 500 transactions of the
  drive. Pass: T6 after each start, and the stream from the decided cut
  the same, byte for byte (SHA-256, as StreamDigest), as without the
  restarts (P2), so the end measures are the same too.
* **Crashes.** T1 at N = 1,000: for every 10th record of the deletes and
  of the drive's first 1,000 transactions, a copy of the stream cut at
  the record's end and at a byte inside it (`CutStream.truncate`, as
  CrashTest does); a start; the model's state after the last whole
  transaction (T6); then the rest of the drive, and T1's criteria at its
  end. A cleanup that is lost or done twice at a start fails here.
* **Readers.** 4 threads during T1 at N = 100,000 and during T4: gets and
  scans at random available times. Each answer is the model's, or
  `LookupTimeNotAvailableException` when a cut overtook it (D1 = A, as
  ReclaimReaders checks); the writer never fails.
* **Eviction.** T1 with the capacity controller at a budget of 1 MB and
  with the schedules "every" and "random": the same stream from the
  decided cut as without eviction (EvictionInvariance's rule), and M13.

### 5.3 T8, determinism

Checks 023-02, R17. Two runs of any test above give the same stream from
the decided cut and the same counts; so do runs with and without the
measures (the measures are maintenance reads), and T7's restarts. Times,
the physical cut and M2 may differ.


## 6. Regression and performance

### 6.1 T9, the tests that must pass unchanged

Checks 023-02, R27: they pass, unchanged in what they check.

* `before-commit.sh`: the unit tests, the f-tests, the demos, deps.py and
  doubles.py.
* `level1.sh` to `level4.sh`, full: DagFuzz, DeleteRepro, RestartStress,
  RestartInvariance (a run against itself with restarts), Props's MEM and
  SS within level1.sh's limits (`MEM_MAX` 131, `SS_MAX`), CrashTest,
  BryanRepro, A2A3Check2, ReclaimStress, ReclaimReaders, LoadTest,
  PowerLossTest, EvictionInvariance, LargerThanMemory, and
  `conformance.sh` small, reclaim and evict (the traces are made fresh).
* `night.sh`, and `night.sh large`: core-build, lean-tests, the night
  tests, harness-soak, fuzz, kill-restart, conformance medium and large.
* StreamDigest's agreement of its four modes in each configuration.
* `Reclaim.Tester.testDeletedKeysAfterCut` (011-01, Q7): kept.
* The 20 hand-made traces in `lean/test-traces`, and jcstress.

### 6.2 Tests that may get new expected values

A change of the bytes written is likely. These compare exact bytes or a
shape, and may get new expected values, each with Frans's approval,
recorded as 018-01, section 2 asks:

| What                   | It compares                   | A new value, approved by           |
|---|---|---|
| StreamDigest's digests | 12 configurations, all delete | both digests in the entry, next.md |
| The C port's bytes     | `cross.sh full`               | a new pin in 022 after 2026.4      |
| The trace checker      | A2 to A5, TREE, A6', A-COPY   | only for a new form (R24)          |
| Unit tests of a shape  | splits, node counts, D        | each named in the change's entry   |
| Version refusals       | `StoredTrans`'s format tests  | with the format (R22)              |
| Props's limits         | `SS_MAX`, `MEM_MAX`           | a reason; Frans's approval         |

The checker's theorems do not change, and the 20 hand-made traces stay
as they are. With a new record format (020-30-04, section 2), Frans's
approval of the format covers the digests of that release; the reference
then no longer compares for the configurations that changed, as 2026.3's
release notes did for reclaim's four ("Changes since 2026.2").

### 6.3 T10, performance before and after

Checks 023-02, R26 ("near current performance, but can be discussed").

* **Builds.** `performance.sh build pre-023` from `main` before the
  change, and the candidate preserved the same way.
* **Runs.** `performance.sh ab pre-023 CANDIDATE` with the quick suite,
  twice ("Run it twice before calling an alert a regression"), then the
  principal suite; G1, and ZGC for P1's pauses. On F53, quiet: no other
  timing run (QUIET-BLOCK markers, `ps`), as performance.sh's own check
  of 90 % idle asks. Props (`props.sh`): MEM and SS exactly, CORE as
  information. The same on s1 for the release.
* **New scenarios**, deletes where the suites have none: T1's emptied
  database at 1M and 10M keys and T4's queue at 1M, as performance runs:
  time a transaction, the largest record, the longest commit and get,
  directory bytes, startup warm and cold at a startup distance of 50 MB
  or more.
* **The numbers to agree on**: each scenario's median throughput against
  its alert threshold (`java/bench/thresholds.json`); the longest commit
  and get (P1: on F53 under 50 ms is good); SS, stream bytes per user
  byte; MEM, heap bytes per KV; directory bytes at the end; startup time.
* **The tolerance** is Frans's (023-02, F12). A form to discuss: no
  scenario beyond its alert threshold in both ab runs, MEM and SS within
  level1.sh's limits, P1 within 010-01's guide, and every difference
  reported with its cause. His earlier prices, for reference: "I would
  trade to 1.50 for bug-free" (2013) and "A < 2.0 factor performance
  degradation compared to now is OK if we can achieve this" (2015;
  010-01, P11).

### 6.4 T11, earlier databases and the format

Checks 023-02, R22 and R23.

* A database written by 2026.3's jar (`releases/2026.3`), with deleted
  keys, opened by the candidate: as Frans answers F9, either it starts
  and passes T1's drive and criteria, or it is refused at the start with
  a clear error; never a start that fails later or builds another tree.
* A database of the candidate opened by 2026.3's jar: refused, if the
  record format changed.
* StreamDigest against 2026.3's baseline: only the approved
  configurations differ.

### 6.5 T12, later: the Lean model and the C port

* **Lean.** SIS has no keys and deletes, so the rule is not a theorem
  (020-30-04, section 4). TraceExport can write T1's small run as a
  trace, and the checker then checks conformance (R24). A check of the
  rule on a trace's last state, nothing reachable with nothing live
  below, would read `blive` in the checker's BergDB instance: a later
  item, if Frans wants it.
* **The C port** (022, after 2026.4's release): T1 and T4 in C, the same
  workloads. C writes Java's bytes, so M1 and the SHA-256 of the kept
  stream must be equal, and M4 to M12 the same counts: a cross check of
  both.


## 7. Where the tests live and their run time

| Test         | Where                                | Sizes                    | Time on F53 |
|---|---|---|---|
| T1, small    | a unit test, `CleanupTester`         | N = 1,000, 5 shapes      | about 1 s   |
| T1, T2       | `java/stress/cleanup.sh`             | N = 1,000, 100,000; 1M   | about 1 min |
| T3           | cleanup.sh                           | N = 100,000, 7 shapes    | 1 to 2 min  |
| T4           | cleanup.sh                           | M = 100,000; 1M in order | about 20 s  |
| T5           | cleanup.sh; u18's 12 hours in large  | as in 020-24             | 1 to 3 min  |
| T6, T8       | inside the tests above               |                          |             |
| T7           | cleanup.sh                           | N = 1,000 and 100,000    | 1 to 3 min  |
| T1, T4 large | `cleanup.sh large`, `night.sh large` | N = 10M; M = 1M hashed   | 5 to 20 min |
| T9           | before-commit, the levels, night.sh  |                          | as today    |
| T10          | performance.sh, props.sh             |                          | hours       |
| T11          | by hand, with `releases/2026.3`      |                          | minutes     |

* The small T1 fits `before-commit.sh`: it may grow by a few seconds
  only (2026-11-05). In the prototype a pair of databases at N = 1,000
  takes 0.1 to 0.2 s, and at N = 1,000 `main` already fails C3 and C6 to
  C9 (section 8).
* `cleanup.sh` (about 5 to 10 minutes) is a new step of `night.sh`, after
  level4; `cleanup.sh large` runs by hand and in `night.sh large`.
* Times are from the prototype on `main` where it ran (section 8), else
  estimates. Today's failing runs are slower than a solution's will be:
  their scans pass the deleted keys.


## 8. Today's results on `main`

The prototype, `java/stress/CleanupRule.java` (T1 with T2's shapes and
T3's R forever, and T4; 700 lines), on branch `023-03-tests` of the clone
`/Users/f/fl/bench/2026-11-10/t23/clone` at `251c4b65` (on `main`'s
`668d64bd`; a copy, with the runs' output, in `03-test-spec/`). Run on
F53 on 2026-11-10, beside other work; only counts are cited. Every check
of T6 passed in every run: no wrong answer, the history within R kept.

### 8.1 T1, "after", against the twin

| Measure                    | Twin  | Phase twins  | N = 1,000 | N = 100,000 | N = 1M    |
|---|---|---|---|---|---|
| M1, MB, the most in window | 2.13  | 2.13, 2.11   | 2.26   | 40.42     | 319.02    |
| M3, ms (R = 1,000)         | 1,039 | 1,176, 1,149 | 1,221  | 5,951     | 12,956    |
| M4                         | 6     | 6, 6         | 84     | 7,902     | 78,999    |
| M5                         | 35    | 33, 28       | 1,047  | 102,918   | 1,028,078 |
| M6                         | 1     | 1, 1         | 1      | 1         | 1         |
| M8, the most in window     | 79    | 84, 83       | 166    | 26        | 31        |
| M9, bytes                  | 2,840 | 3,216, 3,216 | 25,968 | 1,729,720 | 2,224     |
| M10, touch visited         | 7     |              | 85     | 34,629    | 76,480    |
| M11, after the probe       | 85    | 92, 90       | 156    | 7,927     | 79,033    |
| Cuts in the drive          | 11    |              | 11     | 0         | 0         |
| h_fill                     |       |              | 4      | 6         | 7         |

* At N = 1,000 (bounded allowance: a_n = 26, a_b = 13,312 bytes), C1
  (2.26 MB against 2.52) and C2 (1,221 ms against 1,289) pass; C3 (84
  against 32), C4, C6 (166 against 105), C7 (25,968 against 16,152), C8
  (85 against 33) and C9 (156 against 111) fail. The counts see at 1,000
  keys what the stream shows only from 100,000.
* At N = 100,000 and 1M, reclaim's iteration in progress at the deletes
  never ends: its steps' touches each make up to 5,776 (100,000) and
  39,477 (1M) nodes dirty, run on to the next live key, and the next step
  waits for four times their bytes of growth (021-25, part 2). No cut in
  the drive: the first available time falls behind by the drive's time
  (M3), and the stream keeps all of it (M1). With a drive six times as
  long (24,000 transactions, N = 100,000): still no cut, M3 25,951 ms
  and M1 70.4 MB, against the twin's 1,043 ms and 2.2 MB.
* M10 at 100,000 and 1M: the touch of the iteration in progress, which
  never finished.
* On a `FileStream` with a startup distance of 1 MB, N = 100,000 and
  the long drive, reclaim does cut (57 cuts), but M1 is 18.1 MB against
  13.3 MB, M9 2.4 MB against 28.6 kB, M8 8,052 against 2,594, and M4
  stays 7,902.
* On a `FileStream` at 1 MB: M2 was 25.0 MB in 13 files for the twin and
  36.6 MB in 15 files for N = 100,000, against 6.4 and 9.1 MB from the
  decided cut (2.4).

### 8.2 T2, the matrix at N = 100,000

The twin: M1 2.13 MB, M4 6, M5 35, M6 1, M7 6, M9 2,840, M11 85.

| Shape, order      | M1, MB | M3, ms | M4      | M5      | M6 | M7     | M9, bytes | M11     |
|---|---|---|---|---|---|---|---|---|
| after, ascending  | 40.42  | 5,951 | 7,902   | 102,918 | 1 | 6      | 1,729,720 | 7,927   |
| after, descending | 40.50  | 5,951 | 7,902   | 104,050 | 1 | 6      | 1,808     | 7,925   |
| after, random     | 128.98 | 4,379 | 7,903   | 47,619  | 1 | 6      | 572,680   | 7,936   |
| after, 3 versions | 71.79  | 4,926 | 7,903   | 115,825 | 1 | 6      | 1,904     | 7,920   |
| before            | 39.91  | 5,951 | 7,902   | 102,970 | 1 | 7,902  | 1,808     | 7,927   |
| around            | 40.48  | 5,953 | 8,044   | 103,551 | 1 | 4,025  | 1,198,104 | 8,067   |
| inter             | 38.30  | 5,948 | 7,901   | 103,420 | 5 | 1,187  | 3,008     | 7,914   |
| hashed, random    | 248.11 | 4,527 | 112,765 | 132,004 | 4 | 9      | 2,280     | 112,785 |
| long, N = 10,000  | 23.97  | 4,185 | 60,792  | 10,429  | 1 | 60,792 | 1,976     | 60,819  |

* Every row fails C1, C2, C3 and C9, and C7 where the window held a step
  of the stuck iteration (M9 over 0.5 MB in three rows). M8, not shown,
  is below the twin's: in the window the stuck iteration makes no step.
* At N = 1,000 every row fails C3 (M4 83 to 86; hashed 2,070; long, N =
  1,000, 6,083), every row but "inter" C9, and hashed (3.30 MB) and long
  (7.20 MB) C1.

### 8.3 T3, single scans right after the deletes, R forever

N = 100,000 (long: 10,000). The twin with R forever: M4 1, M6 1, M7 1.
These are single scans; T3's rounds were not run, but each round today
repeats them, as nothing cleans up with R forever.

| Shape          | M4, a scan for 1 KV | M5      | M6 | M7, the first user key |
|---|---|---|---|---|
| after          | 7,897   | 100,022 | 1 | 1      |
| before         | 7,897   | 100,022 | 1 | 7,897  |
| around         | 8,039   | 100,036 | 1 | 4,020  |
| inter          | 7,896   | 100,016 | 5 | 1,182  |
| long           | 60,787  | 10,017  | 1 | 60,787 |
| hashed, random | 112,759 | 102,462 | 4 | 4      |

T3's bound for 1,000 rounds of a scan of 1 KV at N = 100,000 and H = 6 is
2 x 2 x 6 x 1,000 + 2 x 6 x 200,000 = 2.42M key nodes; today 7.9M for
every full scan (and "before"'s head scan), and 60.8M for "long"'s.

### 8.4 T4, the queue

1,000 live keys, R = 1 s, startup distance 100 kB; at three checkpoints.
M9 is the largest record of the run up to the checkpoint.

| Keys    | Transactions | M4        | Head    | M3, s | M1, MB  | Cuts | M9, kB |
|---|---|---|---|---|---|---|---|
| ordered | 10,000    | 1,119     | 1,006   | 2.0   | 2.4     | 8  | 169    |
| ordered | 100,000   | 11,147    | 11,033  | 78.2  | 53.2    | 9  | 1,860  |
| ordered | 1,000,000 | 111,434   | 111,320 | 893.1 | 557.1   | 10 | 20,643 |
| hashed  | 10,000    | 14,400    | 13      | 1.7   | 12.5    | 7  | 92     |
| hashed  | 100,000   | 112,782   | 130     | 9.9   | 112.5   | 20 | 391    |
| hashed  | 1,000,000 | 1,070,169 | 1,260   | 15.7  | 1,048.5 | 39 | 654    |

* In time order, the cuts all but stop after about 30,000 transactions
  (one more by 200,000, none after), as in 021-25 at its settings; at 1M
  the first available time is 893 s behind with R = 1 s, and a scan for
  the queue's head passes one key node per 9 keys ever deleted (U16-1).
* Hashed, the cuts go on, but the reachable index grows by one node per
  deleted key (each key a segment tree of its own), and so does M1.
* Run time: 1.3 s (ordered) and 4.4 s (hashed) for 100,000; 12.5 s and
  59 s for 1M.

### 8.5 Expected outcome on `main`, test by test

| Test | On `main` today                                                 | Shown here              |
|---|---|---|
| T1  | fails: from N = 1,000 C3, C4, C6 to C9; from 100,000 C1, C2 too | the prototype           |
| T2  | fails in every row and order                                    | the prototype           |
| T3  | fails: full scans; the head in before, around, inter, long      | single scans            |
| T4  | fails: ordered (no cuts, M3 893 s), hashed (M4 grows)           | the prototype           |
| T5  | fails as reported, but the ring control, which passes           | 020-24-14 to 18, 021-25 |
| T6  | passes: no wrong answer, the history within R kept              | the prototype           |
| T7  | passes, as level2.sh and level3.sh do today                     | not run                 |
| T8  | passes (StreamDigest's modes agree today)                       | not run                 |
| T9  | passes: it is today's suite                                     | 2026.3's release        |
| T10 | `main` is the reference                                         |                         |
| T11 | passes: the format is 2026.3's                                  |                         |


## 9. Open questions for Frans

Each with a recommendation. 023-02's F1 to F12 are not repeated; Q2 and
Q3 lean on them.

* **Q1. The drive.** Fixed, 4 R of time and 40 startup distances of
  values, the same for every N, so that "eventually" has a bound that
  does not grow with what was deleted; or a drive that grows with N, so
  that a cleanup paid later by the user's writes, in proportion to N,
  passes too? Recommended: fixed (and 023-02's F7, the user's writes).
* **Q2. Strict or bounded** (023-02, F1 and F5). Recommended: T1 to T4
  gate on the bounded allowance (a_n = 10 + L h_fill nodes) for 2026.4,
  and report the strict one (10 nodes, dead klongs within B) with the
  "sparse" row; the strict one gates once F5 is decided for the live
  keys.
  **Frans, 2026-11-10, 10:38:** "I agree in general. However, it depends
  on how difficult Strict is. If we find a good Strict solution, let's go
  for it. But Bounded is ok. For Strict, it is enough to eventually, after
  one or several reclaims, to get the original Hello-world resource
  consumption." So the bounded allowance gates; the strict one gates too
  if a good solution is found, measured after one or more reclaim
  iterations of the drive.
* **Q3. T3's constants** (023-02, F4 and F12): c = c' = 2, 1,000 rounds,
  the amortized sum gates and the worst single scan is reported.
  Recommended: so, checked against the first solution that passes.
* **Q4. Disk and memory.** M1, from the decided cut, gates; M2 (files on
  disk), M13 (resident bytes under eviction) and the heap (Props's MEM)
  are reported, as `FileStream`'s whole-file cut and `noEvict()` are
  023-02's non-goals. Recommended: so. If the large run shows a
  `FileStream` keeping a file sized at the stream's peak long after the
  deletes, that becomes a todo entry of its own.
* **Q5. The settings.** A startup distance of 100 kB and R of 1 s for the
  Core tests, below any production setting, so that a test of seconds
  passes through dozens of iterations; 5 MB in the Pub form and the large
  run; 50 MB at 10M keys in the large run as information. Recommended:
  so.
* **Q6. Where.** The small T1 as a unit test (about 1 s more in
  `before-commit.sh`), `cleanup.sh` as a step of `night.sh`, `cleanup.sh
  large` by hand and in `night.sh large`. Recommended: so.
* **Q7. The Pub form** in Frans's own words, `c.put("/a.txt", "Hello
  world!")`: a row of T2 at N = 100,000 in `cleanup.sh`, with the Core
  form gating the Core. Recommended: yes.


## 10. State

2026-11-10, by t23 for coord-1110: written; the prototype ran T1 (with
T2's rows and T3's single scans) and T4 on `main` (section 8): the clone
`/Users/f/fl/bench/2026-11-10/t23/clone`, branch `023-03-tests` at
`251c4b65`, `java/stress/CleanupRule.java`; its copy and the runs'
output in `03-test-spec/`. Not done: T3's 1,000 rounds, T5, T7 and the
Pub form; the hooks H2 and H3; the tests in the repo (`CleanupTester`,
`cleanup.sh`); the large run. Next: Frans's answers to Q1 to Q7, then
the tests as code on `main`, before any solution, so that each solution
is judged by the same tests.
