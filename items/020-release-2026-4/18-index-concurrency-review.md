# 020-18 The user indexes under concurrency: a review

Created 2026-11-09 by Frans Lundberg. Status: open.

A concurrency review of the user indexes of release 2026.4 (020-10), one
of the bug hunts before the release candidate (020): index maintenance at
writes, build jobs, deletes, stop and close, restarts and lookups. Code at
`a9e5488`; the work in the clone `/Users/f/fl/bench/2026-11-09/clone-c18`.


## 1. The request

Frans, 2026-11-09, 09:21: "Start 1 to 4"; 09:22: "Use effort xhigh". From
coord-1109's brief: write down the shared state and its guards; enumerate
the interleavings that matter (a write in each phase of a build, two
definitions of a name at once, a deletion during a build, a write and a
lookup, a redefinition right after it, stop and close during each, a
start that finds a build or a cleanup half done, a lookup across a
generation's change, many writers on one directory during a build, a
failed build racing with join and a new definition); show each unsafe one
with a deterministic test or a stress probe; fix with a failing test
first; compare the code with 020-10 wherever it promises an order or an
atomicity.


## 2. Method

1. Read 020-10 (sections 3 to 6) and the code at `a9e5488`: `IndexManager`,
   `IndexBuilderImp`, `RwEnvironmentImp`, `RwTransaction`, `WTransaction`,
   `UseIndexBuilderImp`, `UsePrimaryBuilderImp`, `DatabaseImp`,
   `IndexDefinition`, `IndexKeys`, `Job`, `JobStatus`, and the Core's
   conflict check (`Db.stmCheckConflicts`, `KeyModSet`, `DbClock`).
2. Wrote down the shared state and its guards (section 2.1), and every
   check-then-act that spans two guards (section 2.2).
3. Took each interleaving of the brief, and some more, to a verdict
   (section 2.3): safe with the reason, or a defect.
4. Probes in `/Users/f/fl/bench/2026-11-09/c18/probe/` (package
   `bergdb.pubimp`, compiled and run with the clone's `java/build/classes`
   first on the class path), each under two minutes on F53:
   * `ProbeIndexStress`: writers (objects, Strings, deletes, `rw()`, keys
     with a suffix, `w()`s over two directories), a thread that creates
     and deletes two indexes of one directory at random, and a checker
     that, at the latest time t again and again, compares the raw entries
     of each index active at t with f over the directory's values at t.
   * `ProbeIndexRestart`: the same writers and changes, cut by a crash (a
     copy of the `MemoryStream` taken while they run) and a restart, round
     after round; at each start the active indexes are checked at the
     start's time, and at the end, after the builds and cleanups, every
     index, no marker left and no entry of another generation.
   * `ProbeSuffixWriters`: a build of a small directory while threads write
     its keys with a suffix; the time to ACTIVE, and the longest object put
     of another directory meanwhile (F1).
   * `ProbeLargeValues` and `ProbeStepCost`: a build of objects of 4 MB
     under writers of them; the longest wait for the manager's lock, and
     where a step's time goes (F3).
   * `ProbeAppend`: a build of a directory that writers append to (F4).
   * `ProbeCleanupRate`, `ProbeCleanupCost` and `ProbeCleanupFollows`: the
     cleanup of a large deleted generation, step by step (F5).
   * `ProbeCreateGap`: a deletion and a new creation of the name between a
     creation's commit and its build's start (interleaving 14; F2).
   `ProbeIndexStress` takes `-Dstep=N` (steps of N values), `-DretainMs=N`
   (reclaim on), `-Ddir=PATH` (a file database, `-DcacheMb`) and
   `-Dappend=true` (writers that append past the build's end key);
   `ProbeIndexRestart` a mode, `crash`, `stop` or `close`.
5. A defect: a failing test, a minimal fix, the gate, one commit in the
   clone.

### 2.1. The shared state

Each item: who writes it; who reads it; what guards it.

* `IndexManager.byName` and `byIdir`: create, activate, delete and start;
  writers (their S), `job()`, `isLive()`; `lock`, and `byIdir`'s arrays are
  copied on write, so a writer keeps its S outside `lock`.
* `Live.def` and `Live.deleted`: the activation and the deletion; `isLive()`,
  the deletion, the activation; volatile, written under `lock`.
* A `BuildJob`'s state, count, cause and end: the build thread, `create`
  (a build that did not start), the start; `getStatus()` and `join()` in
  any thread; the job's monitor.
* `/#i/didef/-NAME`: the creation, the activation, the deletion, all under
  `lock`; the build steps (its hash in their read sets), the start,
  `useIndex` at its t.
* `/#i/div/IDIR`, a hash only: the creation and the deletion; every write
  at an object key (its read set); the Core's conflict check.
* The entries of (NAME, G): writers, build steps, the cleanup (deletes);
  scans at t and the tests; the read hashes below, and the cleanup only
  after the deletion.
* The markers `/#i/didel/`: the deletion puts one, its cleanup deletes it;
  the start reads them; one cleanup per marker.
* The directory's values: writers; build steps, writers (the previous
  value at R), scans; the Core.
* `IndexManager.db` and `database`: `start()`, once; every thread; published
  by `Thread.start()` and by the return of `createAndStart`.
* `Build.lastKey`, `count`, `ended`, and each `RwEnvironmentImp`: confined
  to one thread.

The read hashes that guard the entries: a writer has its key's hash (the
previous value read at R) and its directory's virtual hash; a build step
has the definition key's hash and the hashes of the values it reads
(since F1: of those whose entries it puts); the cleanup and the definition
changes need none beyond their own key, as no one else writes a deleted
generation or a definition.

### 2.2. Checks and acts under two guards

* A writer reads S under `lock` and commits under the Core's lock: a
  change of S committed after R conflicts with the writer's virtual hash
  (020-10, 5.2). Sound.
* A build step checks `isLive` under `lock` and commits under the Core's: a
  deletion after the step's read time writes the definition's key, which
  is in the step's read set. Sound.
* A creation checks the name, takes G, commits and changes the maps in one
  hold of `lock`; so do the activation and the deletion. Sound.
* `create` starts the build after it releases `lock`: a deletion and a new
  creation of the name may come between; the old build finds its `Live`
  deleted at its first step and ends FAILED "deleted". Sound.
* The build's locked phase (after three refused tries, `runStep`) assumed
  that only writers that read S before it took `lock` can collide with
  it. A write without an object key takes no `lock` and collided with the
  step again and again: F1.

### 2.3. The interleavings and their verdicts

Each safe one with the reason in a line; "probe" names the probes of
step 4 that ran it, with no finding.

1. A write before a build's first step: the writer's R is at or after the
   creation, or its virtual hash makes it run again; so it keeps the
   index, and the build later puts the same entry again. Safe; probe.
2. A write of a value that a step has read: the step has its key's hash
   (since F1, if the step puts its entry) and runs again if the write
   commits first; a write after the step's commit deletes the entry the
   step put. A value without an entry gives the step nothing to write.
   Safe; probe.
3. A write at the switch to ACTIVE: the activation does not change S, and
   both definitions have one generation, so a writer that read S before
   puts the same entries. Safe; probe.
4. Two creations of one name at once: the name's check, G and the commit
   in one hold of `lock`; the second throws IndexAlreadyExistsException.
   Safe.
5. A deletion during a build: the step checks `isLive` and has the
   definition's key hash; the activation checks under `lock`; the build
   ends FAILED "deleted" (`testBuildDeletedBeforeItsStep`, `InItsStep`,
   `BeforeActivation`). Safe.
6. A deletion during a write: the deletion writes the virtual hash after
   R, and the write runs again without the index (`testRacesDelete`).
   Safe; probe.
7. A deletion during a scan: the scan reads the definition, the entries
   and the values at its t; the cleanup deletes at later times. Safe until
   reclaim's cut, as promised; probe (scans at t during changes).
8. A redefinition right after a deletion: G_B is at least the deletion's
   time, above G_A; the old build's step conflicts on the definition's
   key; the old cleanup reads only G_A's prefix. Safe; probe.
9. stop() or close() during a creation, a step, the activation, a
   deletion, a cleanup, a scan: a refused transaction changes nothing (H3);
   a committed one is in the stream, and the next start goes on from it;
   the threads end at their next Core call with BUILDING. close() can
   return before an index thread ends (at most its pause, 1 s, or a wait
   of 640 ms); `join()` then returns BUILDING. Safe; probe in "stop" and
   "close" modes: every `join()` returned and every index thread had ended
   within 3 s.
10. A start that finds a build half done: it builds again from the first
    key (entries are idempotent). A deletion half cleaned: the marker
    resumes it. Safe; probe ("crash" mode, 70 rounds, directories of 80 and
    3,000 keys).
11. A scan whose t falls before, during or after a generation's change:
    the definition is read at t, so t sees one generation or none; a
    building one throws NoSuchIndexException. Safe; probe (each scan of an
    index active at t equal to f over the values at t, key by key and
    value by value).
12. Many writers of one directory during a build: the step goes under
    `lock` after three refused tries; writers of object keys take `lock`
    before their Core transaction, so the step meets at most the writers
    already past it (`testBuildEndsUnderWriters`). Writers of other keys
    of the directory did not take `lock`: F1, fixed. A step of large values
    held `lock` long: F3, fixed.
13. A failed build against `join()` and a new definition: `failed()` and
    `ended()` are under the job's monitor, `join()` reads under it, so a
    `join()` sees FAILED or BUILDING, never a mix; the name stays taken
    until `deleteIndex()`, then a new creation gets a new job. Safe.
14. A deletion between the creation's release of `lock` and the build's
    start, and a new creation of the name there: the old build finds its
    `Live` deleted at its first step. Safe (`ProbeCreateGap`: the old job
    FAILED "deleted", the new index exact, no marker or other generation
    left).
15. Key replace during a build: the value's key and the entry's K get the
    same time at the commit; the writer's read hash is on the literal key,
    which no one writes. Safe as a race. Two edges of key replace that are
    not races I saw and did not pursue: `${transactionTime}` in a key's
    directory (the index set read for the directory as written), and the
    previous value read at the key as written. Both are 020-14's X1, fixed
    on `main` in `a03111e` (read after this report was written).
16. Locks: `lock` and a job's monitor are taken in that order only
    (`start()`), never the other way; the build calls the Core under
    `lock` in its locked phase, and nothing calls the index manager under
    the Core's lock. No deadlock.
17. The Core's check: `KeyModSet` keeps exact hashes per bin and answers
    "modified" for a time older than its oldest bin; the commit makes its
    time visible and records its write hashes in one hold of the Core's
    write lock. So the virtual hash and the definition's key hash cannot
    miss a change. Safe.
18. Writers that append to the directory during a build (keys in
    increasing order): the build read to the directory's end at each step
    and so chased them: F4, fixed.
19. A build of large values under writers: F3, fixed.

### 2.4. 020-10 against the code

Every order and atomicity that 020-10 promises holds in the code: G under
`lock` (4.3), R before the virtual hash and S (5.1, steps 1 to 3), the
previous value at R with its hash (step 4), no definition key in a
writer's read set (step 5), a change's maps only after its commit (5.2),
the step, the activation and the errors (6.1), the deletion in one
transaction and the cleanup without a read set (6.2), the start's order
(4.5). The fixes change four points of 6.1 and 6.2 (section 4): "The
values' hashes are in the read set" is now the hashes of the values whose
entries the step puts (F1); "a getMany of at most 25 values" now also ends
after the value that takes the step to 1,000,000 bytes of values (F3); the
build stops at the directory's last key when it began (F4); the cleanup
reads after the last key it deleted (F5).

### 2.5. Observations, not defects

* O1. One thread per cleanup and per build: a burst of deletions, or a
  start with many markers, starts as many threads at once; with thousands,
  a thread's creation could throw OutOfMemoryError, which fails the
  database (P7). By 020-10's design; a queue with one thread is a later
  change, for Frans to weigh.
* O2. A job's status lags its index by a moment: between the activation's
  commit and `activated()`, `getStatus()` says BUILDING; a `deleteIndex()`
  then gives a job that ends ACTIVE, not FAILED "deleted", as the index
  was active when deleted. Consistent with the stream.
* O3. A read at the latest time visits the keys deleted in its range (the
  Core keeps them for earlier lookup times), as F5 showed. So a scan of an
  index range that many entries have left is slow: `ProbeChurnScan`, an
  `eq()` with no result over a range that 100,000 entries left, 2 to 12 ms,
  against 0.1 ms for a range never used; the primary scan likewise. Linear
  in the range's history, not a fault of the indexes; for Frans, with
  "optimize for large databases" in mind.


## 3. Findings

| ID | Severity | What | Fix |
|---|---|---|---|
| F1 | medium | A build step collided again and again with writes of keys with a suffix | `aae7f0b` |
| F2 | low    | The note of a deleted build: "The next start takes it again"            | `55ea9ab` |
| F3 | medium | A locked build step read 25 large values under the manager's lock       | `7a11609` |
| F4 | medium | A build chased writers that append to its directory, BUILDING for ever | `e471459` |
| F5 | medium | A cleanup's work grew as the square of the deleted index's entries      | `cb7c796` |

### 3.1. F1: writes of keys with a suffix and the build's locked step

`IndexBuilderImp.java`, `step()` (line 461 at `a9e5488`), with
`RwEnvironmentImp.getMany()` (line 466): a build step put the hash of every
KV it read in its read set, values of keys with a suffix (`/p/a.txt`)
too. Such a key never has an entry, and a write of it takes no index
manager's lock (`RwEnvironmentImp.indexEntries` returns at once without
object operations). So a write of it after the step's read made the step
run again. After three refused tries the step runs under `lock`
(`runStep`, ab06e26, the fix of I1-starve), assuming that only writers
that read the index set before it can collide; these writers never take
`lock`, so the step collided with them again and again while it held
`lock`, and every write at an object key of the database, in any
directory, and every index's change and `indexJob()`, waited.

Measured with `ProbeSuffixWriters` on F53 (10 cores), a directory of 10
objects and their `.txt` keys, 24 threads writing the `.txt` keys: the
build took 0.29 to 0.47 s, and an object put of another directory waited
up to 0.19 and 0.38 s (two runs), against 13 and 28 ms with the build in
an empty directory. With 16 writers over 40 keys: 0.81 s and 89 ms.

The fix: a step adds the hash of a value only when it puts the value's
entry (`step()`, line 486 after the fix), and `RwEnvironmentImp.getMany`,
whose one caller is the build, adds none. Why that is enough: a step
writes nothing for a value without an entry, so no write of it can leave
a stale entry; a write of a value whose entry the step puts conflicts as
before. The writers that can now collide with a step all take `lock`,
which is what the locked phase assumes. After the fix: the build 0.01 to
0.02 s, other puts at most 15 ms.

The test: a hook at `BUILD_STEP` writes the step's key `k2.txt` at each of
the step's first ten tries; before the fix the step took 11 tries (7 of
them under `lock`), after it 1. Gate: BEFORE COMMIT OK (unit 1,418, f 86,
demos 14, 139 s).

020-10, section 6.1 says "The values' hashes are in the read set"; since
F1 it is the hashes of the values whose entries the step puts. 020-10 is
not changed here (for the coordinator).

### 3.2. F2: the note of a build that ended for a deletion

`IndexBuilderImp.java`, `Status.note()` (line 284 at `a9e5488`): the
note of every FAILED status ended "The next start takes it again.", also
for the reason "deleted", whose index is gone (IndexBuildException's
Javadoc: "A deleted index is gone."). Found by `ProbeCreateGap`'s output.
The fix: for "deleted" the note ends "; the index was deleted while it was
building."; the reason is a constant, `DELETED`. The test: the helper
`assertDeleted` of `PubTesterIndexJobs` checks the note, so
`testBuildDeletedBeforeItsStep`, `testBuildDeletedInItsStep` and
`testBuildDeletedBeforeActivation` failed before the fix. Gate: BEFORE
COMMIT OK (unit 1,418, f 86, demos 14, 155 s).

### 3.3. F3: a locked build step reads large values under the lock

`IndexBuilderImp.java`, `step()` (lines 444 to 479 at `a9e5488`): a step
read up to 25 values, whatever their size, and its locked phase (after
three refused tries) does its reads under `lock`. A value over 1 MiB is
not kept in the cache, so each read of it goes to the storage: in a memory
database 25 objects of 4 MB took about 0.62 s to read (`ProbeStepCost`; the
entries took 0.3 ms). With large values a step's reads are long, writers
of the directory meet it often, and so the locked phase comes often and
holds `lock` long; every write at an object key of the database waits.

Measured with `ProbeLargeValues` on F53: a directory of 100 objects of
4 MB (a `long` and a `byte[]`), three threads that put such objects at its
keys, and a build; a thread that puts small objects in another directory
every millisecond, and one that takes `lock` every millisecond. Before
the fix: 4 tries under `lock`, `lock` waited for up to 0.84 s, the other
directory's put up to 0.83 and 1.25 s (two runs), the build 16.6 s;
without the build (the index on an empty directory) the put waited up to
0.13 s. After it: no try under `lock`, `lock` waited up to 26 and 45 ms,
the put up to 80 and 129 ms, the build 6.6 and 7.6 s.

The fix: a step also ends after the value that takes it to
`STEP_BYTES`, 1,000,000 bytes of values (at least one value; the 25 kept),
so a step under `lock` reads at most about 1 MB and one value. Its end is
now the end of the directory's keys only (`ended = end[0]`), not a count
below 25. Left: a single value of tens of MB still makes a step that long,
under `lock` if its key is written hot; the reads would have to move out
of the lock to remove it (section 4).

The test, `PubTesterIndexJobs.testBuildStepBoundedByBytes`: ten objects of
300,000 bytes build in three steps (4, 4 and 2 values), all entries made;
one step before the fix. Gate: BEFORE COMMIT OK (unit 1,419, f 86, demos
14, 154 s).

### 3.4. F4: a build chased the writers that append to its directory

`IndexBuilderImp.java`, `step()` (lines 444 to 479 at `a9e5488`): each
step read the directory's keys after the last one read, up to the
directory's end at the step's time. The values put after the creation are
kept by their writers, but the build read them too, so writers that
appended to the directory (keys in increasing order: a log, events, keys
with `${transactionTime}`) faster than the build read kept the index
BUILDING for as long as they wrote. Measured with `ProbeAppend`: a
directory of 20,000 objects, four threads appending about 57,000 objects
a second: BUILDING after 30 s, 777,200 values read; ACTIVE 14 s after the
writers stopped.

The fix: at its first step the build reads the directory's last key E
(a backward `getMany` at the latest time, after the creation's commit) and
stops after E. Why that is enough: the build runs after the creation, so
a key after E did not exist when E was read, and was put later by a writer
whose read time is at or after the creation's (or it ran again on the
directory's virtual hash), so it kept the index; a key up to E is read by
the build, or kept by its writer as before. A start that resumes a build
reads E anew. After the fix: ACTIVE after 4.0 s (count 57,059) and, from
200,000 objects, 7.6 s, the writers going on.

The test, `PubTesterIndexJobs.testBuildReadsUpToItsStartsLastKey`: three
objects, steps of two values, and a hook at the first step that appends 30
objects: the build reads 3 values, and the index has all 33 entries;
before the fix it read 33. Probes after it: `ProbeIndexStress` with
appends and deletes past E (`-Dappend=true`), and the restart probe, no
finding. Gate: BEFORE COMMIT OK (unit 1,420, f 86, demos 14, 143 s).

### 3.5. F5: the cleanup read from the generation's prefix at each step

`IndexManager.java`, `startCleanup()` (line 483 at `a9e5488`): each step
read up to 100 keys from the deleted generation's prefix. The Core keeps
deleted keys for earlier lookup times, and a read at the latest time
visits them before the live ones, so step k visited the k × 100 keys the
steps before had deleted: the cleanup's work grew as the square of the
entries' number. Measured with `ProbeCleanupCost` (100,000 entries, a
memory database): a step's read 0.23 ms at the start and 9.84 ms at the
end, 4.7 s of reads in all, against 0.4 s for the deletes; the whole
cleanup 8.4 s for 100,000 entries and 42.7 s for 200,000. By that rate
1,000,000 entries take about 8 minutes of reads, 10,000,000 about 13
hours, plus the pauses (half of each step), with the marker kept all that
time and the work done again from the start after a restart. No writer
waits for it (the cleanup takes no lock), so this is cost, not a stall.

The fix: a step reads the keys after the last key the cleanup deleted;
when none is left after it, one read from the prefix (a last check, as no
one writes a deleted generation), then the marker's deletion.
`IndexManager.scan` takes an `after` key for it. After the fix: the
cleanup of 100,000 entries 0.8 s, its steps flat (0.75 ms at the start,
0.61 ms at the end).

The test, `PubTesterIndexJobs.testCleanupWorkIsLinear`, counts pointers
followed, not time: `IndexManager.testScanListener` (test only) is the
pointer listener of `scan()`'s reads; the cleanup of 2,000 entries follows
at most three times the pointers of one read of all of them. Before the
fix 7.0 times (and 3.9, 6.4, 14.2 and 53 times for 1,000, 2,000, 5,000 and
20,000 entries in `ProbeCleanupFollows`); after it 1.6 times for each.
Gate: BEFORE COMMIT OK (unit 1,421, f 86, demos 14, 144 s).


## 4. State

Done, 2026-11-09 (09:22 to 10:40): every interleaving of the brief
has a verdict (section 2.3), and each defect found has a failing test, a
minimal fix and a gated commit in the clone
`/Users/f/fl/bench/2026-11-09/clone-c18`, branch `main`, on `a9e5488`:

| Commit    | Finding | Gate                     |
|---|---|---|
| `aae7f0b` | F1      | BEFORE COMMIT OK (139 s) |
| `55ea9ab` | F2      | BEFORE COMMIT OK (155 s) |
| `7a11609` | F3      | BEFORE COMMIT OK (154 s) |
| `e471459` | F4      | BEFORE COMMIT OK (143 s) |
| `cb7c796` | F5      | BEFORE COMMIT OK (144 s) |

Each commit was gated on its own, in order; the five touch
`IndexBuilderImp`, `IndexManager`, `RwEnvironmentImp` and
`PubTesterIndexJobs` only (303 lines added, 22 removed, no change of
whitespace elsewhere: `git diff` and `git diff -w` agree). After the last,
`ProbeIndexStress` (file database, 2 MB cache, appends, steps of 3) and
`ProbeIndexRestart` ("stop" mode) ran without a finding.

The five also apply cleanly onto `main` at `86dade8` (after 020-14's X1
to X3 and 020-20's commits): the clone's branch `c18-on-main`, `ebd30ef`
to `d1676e3`, gated as a whole: BEFORE COMMIT OK (unit 1,428, f 86, demos
14, 135 s).

For the coordinator, not done here:

* Take the five commits to `main` (cherry-pick, in order, or the branch
  `c18-on-main`), with a line each in `releases/next.md` and rows in
  020-11.
* 020-10 describes the code before them in three places: section 6.1
  ("The values' hashes are in the read set": now those whose entries the
  step puts, F1; "a getMany of at most 25 values": now also at most about
  1 MB, F3; the build reads "from the first key of its directory" to its
  end: now up to the directory's last key when the build began, F4) and
  section 6.2 (the cleanup's getMany "under the generation's prefix": now
  after the last key deleted, then one read from the prefix, F5).
* Two new constants and a test seam: `IndexBuilderImp.STEP_BYTES`
  (1,000,000, F3) and `DELETED` (F2); `IndexManager.testScanListener`
  (F5, test only, as `testHook`).

Left, each for a later decision:

* F3's rest: one value of tens of MB still makes a step that long, under
  the manager's lock if writers of its key meet the step three times. To
  remove it, a locked step would have to read its values outside the lock
  and check under it only that they are unchanged, which needs the
  values' times without the values from the Core.
* O1 (a thread per cleanup and per build), O2, O3: section 2.5.
* Longer runs of the probes (minutes per seed, more seeds, a file
  database) were not made: the machine was to stay quiet until 13:00. To
  continue: compile the probes against a clone's `java/build/classes` and
  run them as in section 2, step 4, for example
  `java -ea -Dstep=3 -Dappend=true -cp out:CLONE/java/build/classes
  bergdb.pubimp.ProbeIndexStress 600 4 60 SEED`.


Log
===

2026-11-09. Created at 09:40 by coord-1109's agent c18 (020-18), at
Frans's request (09:21, "Start 1 to 4"). Findings F1 to F5, each fixed and
gated in the clone (section 4); verdicts for the brief's interleavings and
three observations. Status stays open until the commits reach `main`.
Then, the report written, read 020-14's X1 on `main` (two key-replace
edges seen here and not pursued, section 2.3, item 15), and gated the five
commits on `main` at `86dade8` (branch `c18-on-main`). The six gates of
this item (09:42 to 10:35) ran before coord-1109's rule that gates run one
at a time under `lockf /Users/f/fl/bench/006-15/gate.lock`, so outside it;
one of them may be the gate of 10:28 that loaded other gates' timing
tests. A later gate of this item runs under the lock.
