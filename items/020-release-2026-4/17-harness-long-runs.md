# 020-17 Long runs of the Pub layer's randomized harnesses

Created 2026-11-09 by Frans Lundberg. Status: open.

One of the bug hunts before release 2026.4's candidate (020): the
randomized harnesses of the Pub layer against their references, run long
on the VPS s1, with many seeds and larger sizes than the night's runs;
their blind spots read and the cheap ones closed. Done by coord-1109's
agent in the clone `/Users/f/fl/bench/2026-11-09/clone-s17` (from `main`
at `a9e5488`); nothing of it is on `main` yet.


## 1. The request

Frans, 2026-11-09, 09:21: "Start 1 to 4" (the hunts that coord-1109
proposed), and 09:22: "Use effort xhigh". This hunt is 020-17: long runs
of IndexHarness (H2), IndexJobsHarness (H3) and PrimaryHarness (H4) of
020-10, section 9, and of the object harnesses of 020-08
(ObjectFormatTester's H0 against its reference codec, and
DataObjectsTester's properties R1 to R3 of 020-09, section 8.5), with many
seeds and larger sizes, on s1; a driver script; the blind spots of the
harnesses listed and the cheap ones added; each defect found with a
failing test and a fix in the clone.


## 2. How to check the run on s1

One command prints the summary, made again after each job:

    ssh root@s1 cat /root/bench/2026-11-09-s17/soak/summary.txt

Its table counts the jobs by harness and result (OK, FAIL, TIMEOUT, WARN);
below it, every job that did not pass, with its first line of failure.
The output of such a job is in `soak/fail/` (its first line is the command
that repeats it), each job's line in `soak/results.tsv`, the start's
settings in `soak/soak.log`. The soak starts no job at or after 18:00. To
end it earlier: `touch /root/bench/2026-11-09-s17/soak/STOP` (it ends
after the job that runs). The earlier runs are beside it, `soak1-*` to
`soak5-*` (section 3).


## 3. The method

**The harnesses and their knobs**, as `bergdb.dev.Run` starts them
(`main()` of each):

| Harness | Arguments of main() | What varies |
|---|---|---|
| IndexHarness (H2)       | SEED STEPS THREADS SEEDS [KEYS WIDE DIR RESTART] | operations, writer threads |
| IndexJobsHarness (H3)   | SEED RUNS OBJECTS                                | random fault, point, call; writer |
| PrimaryHarness (H4)     | SEED STEPS RUNS [RECLAIM]                        | steps |
| ObjectFormatTester (H0) | SEED TREES SAMPLES                               | random values, mutants |
| DataObjectsTester       | SEED COUNT [DB]                                  | random objects |

The arguments in brackets are this hunt's (section 5). Each job is its own
JVM with `-ea`. H3's `main()` exits 0 with findings: the driver reads its
line "0 kinds of findings, 0 of known faults".

**The driver**, `java/stress/harness-soak.sh` in the clone (its header
has the usage): rounds until a time of day; in each round one job of each
harness, with the seed BASE + round (H3 the seed times 1000, as its runs
take SEED to SEED + RUNS - 1), sizes that cycle with the round through
lists of coprime lengths, and for the jobs with a database the Core's
eviction schedules and audit by their system properties (`evict` none,
every, random, values, a budget of 20,000 bytes; `audit=10` in one job of
three; a failed audit prints "AUDIT FAILED", which fails the job). A job
passes if it exits 0 and prints its harness's line of success; past its
time limit (30 minutes) it is TIMEOUT, a hang; a passing job whose output
has "Exception in thread" or an OutOfMemoryError is WARN (a thread died
and the harness did not see it). On s1 (2 CPUs, 3 GB) the jobs take both
CPUs while no other java process runs and CPU 1 only (`taskset`) while
one does, decided before each job, as 020-15 and 020-16 also run there.
`-Xmx1g`.

**The runs on s1** (all in `/root/bench/2026-11-09-s17/`):

| Run   | Jar                               | Seeds from | Started | Ended                     |
|---|---|---|---|---|
| soak1 | `a9e5488`                         | 1709000    | 09:31   | 09:42, for H3-O1, H3-O2   |
| soak2 | `2d2fe01`                         | 1709100    | 09:47   | 10:05, for the options    |
| soak3 | wip1: `6177a43` but B7, B9        | 1709200    | 10:05   | 10:13, for wip2           |
| soak4 | wip2: `51d792d` but B16           | 1709300    | 10:13   | 10:29, for `51d792d`      |
| soak5 | `51d792d`, the driver `80bce7c`   | 1709400    | 10:29   | 10:37, for B17            |
| soak6 | `ed7ff00`, the driver `6c7b4aa`   | 1709500    | 10:37   | 18:00 (running)           |

wip1 and wip2 are jars built from the clone's working tree before the
gated commits of the same content (`bergdb-wip1.jar`, `bergdb-wip2.jar` on
s1), so that the soak did not wait for the gates' queue on F53; each soak
was stopped with its STOP file after its running job, and its directory
kept as `soakN-*`. soak1 ended otherwise: its script was copied over while
it ran (AGENTS.md says not to), and `sh` stopped at a syntax error after
its job 54; since then each version of the driver has a file of its own
on s1 (`harness-soak-<commit>.sh`).


## 4. The findings

Each is a false finding of a harness (severity: harness, no fault of
BergDB), in `java/src/bergdb/pubimp/IndexJobsHarness.java`; the lines are
the fix's, at the clone's `ed7ff00`:

| ID    | What                                                    | Where                     | Fix (clone) |
|---|---|---|---|
| H3-O1 | a deletion during a build taken for a fault taken again | `checkFinal`, 1150 to 1160 | `0c03b97` |
| H3-O2 | a stop met by the workload's own read                   | `Run.execute`, 503         | `2d2fe01` |
| H3-O3 | a check of the entries raced the writer thread          | `checkUnchanged`, 1022; 1639 | `303e2a8` |
| H3-O4 | a build's bound of 10 s, a "hang" at 20,000 objects     | `JOIN_MS`, 126 to 129      | `51d792d` |

No fault of BergDB so far.

**H3-O1.** A refusal, an expiry or an interrupt at the first build's step
is taken again (019-38); if the workload then deletes the index during
that build (its option "deleted during the build", at the third step
call), the build ends FAILED "deleted", as 020-10, section 3.2 says, and
`checkFinal()` expected ACTIVE, the rule of a fault taken again with no
deletion. The night's random runs with 500 objects draw it about once in
1,000 runs (a fault at one of the first 3 or 4 of 40 step calls); the
soak, with 30 to 260 objects, in every job of 200 runs. Fixed: a fault
taken again leaves the deletion's rule to decide. The test runs the three
faults at the first step with a deletion during the build; it failed
before the fix with one finding each.

**H3-O2.** A stop injected at the cleanup's step (in the cleanup's thread,
after the deletion returned) can come between the workload's `alive()`
and its own read of the stream's definition at the next creation
(`streamDefinition()`, `IndexDefinition.read`, `Db.getOne`), which throws
`DbStoppingException`; `execute()` reported it as a finding "workload: it
threw". Found by soak1 with 30 objects and a writer thread; a probe of
that configuration (STOP at the cleanup's first step, 30 objects, a
writer) found it in 4 of 300 runs. Fixed: a stop or a failure that the
workload's own read meets goes to `alive()`, which decides, as between the
calls, whether the fault allowed it; any other exception stays a finding.
The probe found none in 1,500 runs after the fix. No unit test: the
window is a race of two threads that the hook does not order.

**H3-O3.** After a refused deletion, the workload writes one value and
compares the index's entries with the model's values (`checkUnchanged`,
"after a refused deletion and a write"), while the writer thread (the
option "a writer") still runs: the model's values are taken first, then
the entries are read, and a write of the writer between the two is in the
entries and not in the values. Found on F53 by a random run (seed 3010,
500 objects, an expiry before the deletion's commit) after B14 below; it
is older: at `6177a43`, a probe of a refusal before the deletion's commit
with the writer found it in 5 of 300 runs, with the writer's keys `wNN`.
Fixed: the writer holds a lock for a write and its model's update, and
that check holds it for the values and the entries; the probe found none
in 600 runs after the fix. The other checks of the entries run after the
writer has stopped.

**H3-O4.** H3 takes a build that has not ended in 10 s (`JOIN_MS`), and a
cleanup in 5 s, for a hang. soak2's run of 20,000 objects with the Core's
audit and random eviction, on one CPU of s1, read about 1,000 values a
second: every build passed the bound, and the run reported 21 kinds of
findings, all of a build still going (its count growing: 8,200 to 12,250
values at the bound), none of a fault. The bounds are for the night's 500
objects. Added: the property `harness.slow`, a factor of both bounds; the
driver gives 1 + objects / 2000, five times that with the audit. No test:
a property for long runs.


## 5. The blind spots of the harnesses

Read from the code at `a9e5488`. "Added" means in the clone: B1 to B7,
B9, B12 and B13 in `6177a43`; B8, B10, B14 and B16 in `51d792d`; B17 in
`ed7ff00`; all in soak6. The defaults of the unit and night tests are
unchanged (the same seeds give the same operations); WIDE, KEYS, DIR,
RESTART, RECLAIM and DB are arguments of `main()`, `harness.sd` and
`harness.slow` system properties.

**H2, IndexHarness**

* **B1, sizes below every boundary** (added). 16 object names in each of
  its two directories: a build never takes a second step
  (`IndexBuilderImp.STEP_VALUES`, 25 values), a scan never a second page
  (`UseIndexBuilderImp`'s 100 entries), a cleanup never a second step
  (`IndexManager.CLEANUP_KEYS`, 100). So the paging of scans (forward,
  backward, with bounds, with stale entries at a page's end) and the steps
  of builds and cleanups with writes between them are not in H2; H3 has
  builds and cleanups of several steps but no scans. Added: KEYS more
  object names (`j0`, `m1`, ...) in `/h/a/` and bulk writes of up to 150
  of them; with 300 keys, 344 scans of more than a page in 2,000
  operations (seed 31).
* **B2, reclaim never cuts** (added, a property). The runs set a retain
  duration of a second, as 020-10, section 9.1 asks, but reclaim starts an
  iteration only when the stream has grown by twice the startup distance
  (`Reclaim`), at least 5 MB by the Pub API, 50 MB by default; a
  harness's stream is far smaller, so its checks at past lookup times
  never meet reclaim's cut, and a scan's `LookupTimeNotAvailableException`
  (020-10, section 3.6) is not run. Added: the system property
  `harness.sd` (bytes), which `IndexHarness.startupDistance()` sets with
  the Core's `Db.setStartupDistance` (400,000 at least) at each start, in
  H2 and H4; H2 counts the transactions' times behind the cut at its end.
  (H2's stream grows slowly; whether its runs reach a cut with it is
  measured by the soak, section 6.)
* **B3, one form of scan** (added). Every scan was `kvs()` as `DbObject`,
  iterated once by a for-each: never `objects()`, never `byte[]` as the
  type, never the same `Iterable` again (020-10, section 3.4: each
  iterator starts from the beginning at the same lookup time), never
  `hasNext()` twice, never `next()` past the end. Added, by the check's
  random: `objects()` one time in four, `byte[]` one in six, a second
  iteration one in six, `hasNext()` again one in eight, `next()` past the
  end always.
* **B4, few shapes** (added, WIDE). 1 to 3 levels (the design allows 8),
  and only the directories `/h/a/` and `/h/a/sub/`: never an index whose
  directory is a parent of another's keys (`/h/`, whose own values
  exclude `/h/a/`'s) or a neighbour whose name starts as another's
  (`/h/a0/`). Added: in a wide run, one index in four has 4 to 8 levels,
  one in five a directory of those two, one key in ten is there.
* **B5, no rerun of a writer** (added, WIDE). `rw()` never read, so in H2
  only an index definition's change could make a writer's transaction run
  again; the rerun's entries (the old value read again) were not
  exercised. Added: in a wide run, an `rw()` reads each key before it
  writes it, so that the other writer threads' writes of the key make it
  run again.
* **B6, `main()` in memory only** (added). The night's long run has one
  seed in four in a directory; `main()` had none, and a restart every 500
  fixed. Added: DIR and RESTART.
* **B7, definitions changed only between transactions** (added, WIDE).
  With several threads, the threads ran transactions only; a creation or
  a deletion never ran while they did (an activation could, in a build's
  thread). `PubTesterIndexRaces` forces 36 orders of one write against
  each change; random interleavings of many writers with a change were
  not run. Added: in a wide run with threads, every creation and deletion
  runs while the other threads run a transaction each; the model takes
  the change's time as the interval of the call, as it does alone.
* **B8, no key replace** (added, WIDE). No key with `${transactionTime}`
  (020-10, section 5.3, N11; `testKeyReplaceIndexedText` has one case).
  Added: one transaction in 30 also puts a new object at
  `/h/a/r${transactionTime}`, with key replace on for every connection,
  its field `c` one time in two a String that holds the pattern; the
  model replaces the pattern in the key by the time as 18 digits, and
  keeps the String as it is.
* **B9, the scan's conversion** (added, WIDE, in part). The scan's type
  was never a Data Object class, `Object` or `String`: the conversion of
  020-09 in `next()` was not in H2 (DataObjectsTester checks it for a
  get). Added: one scan in six as the class `Doc` (fields `a`, `b`, `c`,
  `z` and a nested `n`), each value checked field by field against
  `DbObject.toJavaObject(Doc.class)` of the stored bytes, the get's
  conversion; later (`e64fa77`, not in soak6) one in six
  as `Object`, each value a `DbObject` of the stored bytes. `String` is
  not added.
* **B10, `freezeLookupTime()`** (added, WIDE). H2 set lookup times only;
  020-10, section 3.6 says that the first read after a freeze fixes the
  time, and that later scans read at it. Added: one check at the latest
  time in four freezes the connection, reads once with `exists()`, takes
  the frozen time from `getLookupTime()` (it must be from the last
  transaction's time to the current time) and checks every scan there. A
  `useIndex()` as the first read is not checked: whether a call that
  throws `NoSuchIndexException` fixes the time is not promised.
* **B11, no eviction** (no code: the soak). The Pub harnesses run with a
  cache of a fifth of the heap and a startup distance of 50 MB: nothing
  of the index is evicted, and no read loads a node from the stream.
  The soak runs them with the Core's `evict` and `audit` properties, and
  with `harness.sd` (B2) so that index nodes too can be evicted.
* **B16, any `LookupTimeNotAvailableException` taken** (added). H2's
  checks returned at this exception whatever the lookup time; one at a
  time not behind reclaim's cut, which 020-10, section 3.6 does not allow,
  passed. Now it must be behind the cut, read when it has come (the cut
  only moves forward).
* **B17, no scan while transactions commit** (added, WIDE). The checks
  ran only between operations, so no scan paged while later transactions
  committed (and eviction ran). Added: in a wide run with threads, the
  main thread runs the checks at the time before the transactions while
  the writer threads run them; the model at that time is complete, as
  the transactions commit after it.
* **B18, no refused writer** (not added). H2 injects no fault: a writer's
  transaction is never refused or expired, so that a refused `w()` or
  `rw()` leaves no entry is H3's check for the jobs' transactions only,
  not for the writers'. Medium: it needs a hook in the writers' path that
  `PubTesterIndexRaces` has, and a model that drops a refused
  transaction.

**H3, IndexJobsHarness**

* **B14, no write behind a build's cursor** (added). The writer thread
  wrote the names `w00` to `w19`, which sort after the data's `k000` to
  `kNNN`, so during a build of several steps every write of it was ahead
  of the build's last key, which the build reads later anyway: a write
  behind the cursor, which only the writers' index maintenance keeps
  (020-10, section 5.1), was in no run but the racing writes at the first
  step. Added: one key in two of the writer is a key of the data.
* One index name, one directory, two fixed definitions (a `long` level;
  a `string` and a `long`), and no scans: the entries are compared raw
  after each phase. Builds of several indexes at once, of other types,
  and reads during jobs are H2's (with B1, of several steps).
* At most 500 objects at night: the soak takes 30 to 20,000 (H3-O4).

**H4, PrimaryHarness**

* **B12, no reclaim** (added, RECLAIM). No retain duration was set, so no
  listing met reclaim's cut. Added: a retain duration of a second and
  clock steps 2,000 times longer; a listing whose time is behind the cut
  must throw `LookupTimeNotAvailableException` (at any call of the
  listing), and a listing at a time not behind it must not. With
  `harness.sd=400000`, 729 of 4,295 listings met the cut in 8,000 steps
  (seed 23), all right; without it none.
* **B19, one thread** (not added). No listing runs while transactions
  commit, as B17 for H2; a listing is iterated again after a write, at its
  time, which is the cheaper half. Medium.
* No index (by design).

**The object harnesses**

* **B13, DataObjectsTester's `main()` without a database** (added, DB).
  Its night test puts one object in ten (R1) and one in sixteen (R2)
  through a database; `main()` passed no connection, so none. Added: DB 1.
* ObjectFormatTester's H0 runs on the codec alone, by design.


## 6. The results

At 11:32, after two hours (soak1 to soak5 done, soak6 for 55 minutes):

| Run   | Jobs | OK  | Not OK                                       |
|---|---|---|---|
| soak1 | 54   | 47  | 7 H3 jobs: H3-O1 (6), H3-O2 (1)              |
| soak2 | 37   | 36  | 1 H3 job: H3-O4                              |
| soak3 | 16   | 16  |                                              |
| soak4 | 31   | 31  |                                              |
| soak5 | 11   | 11  |                                              |
| soak6 | 41   | 41  | (running)                                    |

Every job that did not pass was a fault of a harness, fixed (section 4);
no FAIL, TIMEOUT or WARN since `2d2fe01`, and no fault of BergDB. What
the jobs checked, in all six runs:

* H2: 12.3 million scans against the reference, 26,297 of them of more
  than a page; with `harness.sd`, two runs of 5,000 operations passed
  reclaim's cut (16,232 transactions' times behind it), so scans at past
  times met `LookupTimeNotAvailableException`, each behind the cut (B16).
* H3: 4,698 random runs with faults, of 30 to 20,000 objects (by object
  count, in jobs: 30 7, 61 3, 110 7, 260 4, 500 7, 2,000 4, 5,000 4,
  20,000 3).
* H4: 4,045 listings behind reclaim's cut in 3 jobs, all as 020-10,
  section 3.6 says.
* ObjectFormatTester: 93,000 random values and 3.7 million mutants
  against the reference codec; DataObjectsTester: 12.7 million checks.
* Of the 120 jobs of H2, H3 and H4, 62 with a forced eviction schedule
  of the Core (`evict` every, random, values or a budget of 20,000 bytes)
  and 29 with its audit: no AUDIT FAILED.

The run goes on until 18:00; its summary is section 2's command.


### 6.1. soak6's end, triaged on 10 November

soak6 ended at 18:00 on 9 November, after 72 rounds, on a jar of
`ed7ff00` (the morning's code; none of the day's later fixes):

| Harness | Jobs | OK | FAIL | TIMEOUT |
|---|---|---|---|---|
| H2      | 73   | 61 | 6    | 6       |
| H3      | 73   | 71 | 2    | 0       |
| H4      | 73   | 73 | 0    | 0       |
| obj     | 72   | 72 | 0    | 0       |
| dobj    | 72   | 72 | 0    | 0       |

Nobody read it that evening. coord-1109's agent triaged it on 10
November, 06:11 to 06:27, with reruns of the seeds on the candidate
`03ce6ec` on F53 (files in `/Users/f/fl/bench/2026-11-10/soak-triage/`).
None is a fault of BergDB that returns wrong data; none blocks 2026.4.

* **H2-O5, harness (6 FAILs: jobs 96, 111, 156, 211, 231, 336).** "The
  frozen lookup time t+1, not from the last transaction's time to the
  current time t": `IndexHarness.checkAt` takes t from `currentTime()`
  before `freezeLookupTime()` and the read. In all six an index job ran
  in the background (a create without a join, or a deleted index's
  cleanup); its transaction, which the model does not record, committed
  between the two. `currentTime()`'s promise holds. On the candidate
  seeds 111 and 231 fail 1 of 2 runs; with the fix, a t taken after the
  read (`groupA-harness.patch` in that folder), 8 of 8 pass.
* **H3-O5, a status lag of BergDB, low (job 232).** After a restart in
  the middle of a build, `IndexManager.activateInner` sets the
  definition active under the manager's lock, and
  `IndexBuilderImp.activate` sets the job ACTIVE (`activated(0)`) only
  after the lock is released. For that moment `getStatus()` says
  BUILDING (count 67) of an index that is active and usable; `join()` is
  not affected. A probe that holds the window open gives the soak's
  finding 5 of 5 times on the candidate; without it 0 of 9. Fix after
  the tag: the job ACTIVE under the lock, or the harness reads the status
  before the definition. Open: the build's count 67 where 61 values were
  read back.
* **H3-O4 again (job 317, "hang").** No hang: the build was progressing
  (17,050 to 19,100 of 20,000 values read) when the bound of 110 s passed
  on s1. On F53 the seed passes in 70 s, on the candidate and on
  `ed7ff00`.
* **H2-O6, slow settings (6 TIMEOUTs at 1,800 s).** All with an eviction
  budget of 20,000 bytes and `harness.sd` 400,000 bytes, below the Pub
  API's least cache (1 MB) and startup distance (5 MB). Together they
  grow fast with the operations (800: 180 s; either alone or a 1 MB
  budget: 21 to 25 s); the main thread waits in `Eviction.afterLoad` for
  the evictor, which runs at about 80 % of a CPU. Fix: a smaller run or
  a longer bound for the pair in `harness-soak.sh`.


## 7. State

Done: the driver; soak1 to soak5 on s1, soak6 running until 18:00; H3-O1
to H3-O4 fixed in the clone; the blind spots read; B1 to B10 (B9 in part),
B12 to B14, B16 and B17 added in the clone.

Left: B9's `String`; B18 and B19 (medium); H3's single index
and definitions (a harness of its own size, not cheap); the fixes of
section 6.1 (H2-O5, H3-O5, H2-O6 in `harness-soak.sh`).

The clone's commits, all on top of `a9e5488`, none on `main`; each with
BEFORE COMMIT OK under the gate's lock but the two without Java:

| Commit    | What                                                    |
|---|---|
| `0c03b97` | H3-O1, with `testRetriedFaultThenDeletedDuringBuild`    |
| `2d2fe01` | H3-O2                                                   |
| `6177a43` | B1 to B7, B9, B12, B13 and `harness.sd`                 |
| `303e2a8` | H3-O3                                                   |
| `51d792d` | H3-O4 (`harness.slow`), B8, B10, B14, B16               |
| `80bce7c` | `java/stress/harness-soak.sh` (no Java)                 |
| `ed7ff00` | B17                                                     |
| `6c7b4aa` | the driver: H4's reclaim with `harness.sd` (no Java)    |
| `e64fa77` | B9: scans as `Object` (after soak6 started)             |

To continue: the coordinator decides whether they go to `main` (they
change harnesses and a stress script only, no code of BergDB), by
`git pull` from the clone or a cherry-pick in this order. Proposed for
`night.sh`, not added: after the night tests,

    step harness-soak sh stress/harness-soak.sh -r 2

two rounds of new seeds each night (the date's): rounds 0 and 1 took 3.5
to 4 minutes on s1 (39 s and about 200 s, the second with the audit);
its last line is HARNESS SOAK OK or FAILED.


Log
===

2026-11-09. Created the item, by coord-1109's agent; soak1 started on s1
at 09:31, soak2 at 09:47, soak6 at 10:37, until 18:00.

2026-11-09. H3-O1 to H3-O4 found and fixed in the clone, B1 to B10, B12
to B14, B16 and B17 added (section 5); the results until 11:32 (section
6); reported to coord-1109.

2026-11-10. soak6's end triaged by coord-1109's agent (section 6.1):
no fault of BergDB that gives wrong data; H2-O5 and H2-O6 of the
harness, H3-O5 a status lag of BergDB (low).
