018-03. Harness 6.2: failures and interrupts in storage
======================================================

Created 2026-11-05 by Frans Lundberg, as the next harness of 018-01's W2
("Next: 6.2, on 6.3's strict stream"). Built in the unattended night
006-12.

**Status: in progress (night 006-12).** See the State note at the end.


## 1. What it checks, and why

The known faults of 018-01, section 6.2 (015-06's rest, 015-32, 34, 35,
38, 53, 66, 78, 81, 82, and 019-09 of the same class) are each a path
where the storage fails or a thread is interrupted, and the database then
goes on with a wrong state, hangs, keeps its directory's lock or a thread,
loses a transaction that returned, or reports nothing. A review found each
by reading one path. The harness makes a fault at every call of the
storage, one call per run, so that a path that no review has read is run
too.

A run: a workload on a `FileStream` in a directory of its own, and a fault
at the Nth call of one layer. N = 1, 2, ... until the workload ends before
the Nth call.

* The layers:
  * **STREAM**: the calls of `AppendOnlyStream` that the storage makes to
    the `FileStream` (`getLength`, `getFirstPos`, `read`, `append`,
    `pretruncate`, `close`), through 018-02's `StrictStream` and its hook.
    The storage thread makes the appends and closes, the caller's thread
    the reads and cuts.
  * **IO**: the file calls of `FileStream`, through `FileStreamIo`, the
    test boundary it has had since 2026-10-14: `open`, `write`,
    `forceFile`, `openRead`, `forceDirectory`, `delete`, `rename`. They
    include the open of the stream, before the database exists (015-32).
* The faults:
  * an `IOException` (not in `getLength` and `getFirstPos`, which cannot
    throw one);
  * an unchecked exception;
  * an `Error`;
  * an interrupt of the calling thread (the call then goes on);
  * an interrupt of the calling thread and of every thread of BergDB that
    is alive (the storage thread, the evictor, the closer of `stop()`,
    `FileStream`'s cut thread);
  * a `stop()` at a call that the workload's thread makes, within a
    transaction, a read or a start (`stop()` does not wait, so this is a
    stop by another thread at that moment; 015-53's class).
* The workload, one thread: a start (`maxNodeSize8`, a startup distance
  of 1,000 bytes, a buffer of 8,000 bytes and 10 ms; eviction at every
  chance for two N of four, none for the other two, so that reads are
  served from memory as in 015-35's case), a retain duration of 1 s, then
  40 transactions, the clock 0.25 s on before each; each puts its own key
  `/tN` (3,000 bytes) and overwrites one of five keys `/hN`. A get of an
  older key after every third, of the transaction's own key after every
  fourth, a `sync()` after the sixth of every eight (so the last two
  transactions have none). Then `close()`, or `stop()` and `close()`
  (every other N). Reclaim makes 3 iterations and cuts the stream; with no
  fault the workload makes about 1,970 STREAM calls with eviction and 145
  without, and 150 IO calls. If
  the fault has not come when the transactions are done, the workload
  waits 50 ms before the close, so that the storage thread's flush (10 ms)
  meets it before the close does (019-09's case).
* Each run is made twice: on a new directory, and **reopened**: on a
  database that the first 20 transactions made, with no fault, and
  closed. A reopened run's start reads the stream, reclaim's table and
  settings.

The checks, after each run:

1. **P7.** After a call that threw `DbFailedException`, every later
   transaction and read is refused with `DbFailedException` (`sync()`,
   `stop()` and `close()` still work, by `Db.execute()`'s Javadoc).
   **Met**: a call that threw the fault itself, or an exception caused by
   it, must leave the database failed: the next transaction or read
   throws `DbFailedException` (docs/levels.md, section 3: a database
   whose environment has failed, or that has a bug, does not run on). A
   call that throws something else may leave the database going on (a
   transaction refused before its go point): then the transaction that
   threw is not in the stream.
2. **Interrupts** (005-46's rule, as `InterruptTester` checks it for its
   cases): an interrupt fails no call but `sync()`, which throws
   `StreamIoException`, and the database goes on.
3. **close() returns**, within 30 s, and after a failure that a call
   reported, normally (019-09, option (a)).
4. **The lock**: a new `FileStream` on the directory opens.
5. **No thread of BergDB is left** a second after `close()` returned.
6. **A background failure** (015-35): when the fault was thrown in a
   thread of BergDB, the harness waits up to 0.5 s before the next
   transaction or read until the storage has failed
   (`storageFailed()`); if it has, the call must fail the database.
7. **A failed close is reported**: if the storage had failed before the
   close and no call reported it, or the close met the fault, `close()`
   throws (its Javadoc; 015-78, 019-09).
8. **A stop fails nothing**: after a `stop()` at any call, no call
   throws `DbFailedException`, a transaction that threw is not in the
   stream, and every transaction that returned is (015-53).
9. **The restart**: a start on the directory works and holds:
   * every transaction that a `sync()` confirmed;
   * if no call reported a failure and `close()` returned normally, every
     transaction that returned (`close()`'s Javadoc: every transaction
     that has returned is written);
   * no transaction that was refused;
   * a prefix of the transactions: none after one that is missing, but
     the refused ones.
10. **The stream contract**: no breach of `StrictStream`'s, but the
   harness's own faults that `FileStream` passes on unchecked.

Why at the Core Layer, not the Pub API: the faults are made in
`FileStreamIo` and under `StorageManager`, which the Pub API builds
inside; `DatabaseImp` adds no path of its own to the storage's failures
but its `close()`, which 019-09's test covers.


## 2. The class

`bergdb.core.StorageFaultTester`, test code only, registered in the
package's `Pack`. Nothing in the production code changed.

Its parts:

* `Injector`: counts the calls of one layer and makes the fault at call
  number N. The STREAM layer's hook is `StrictStream.Hook`; the IO
  layer's is `FaultIo`, a `FileStreamIo` whose forces do nothing (forces
  cost tens of milliseconds each; durability is the power-loss tests'
  subject, `FileStreamPowerLossTester`) but count as calls.
* `run(layer, fault, N, stopFirst, reopen)`: one run. The workload runs in a
  thread of its own, which the harness joins for 10 s; a run that has not
  ended is a finding ("close returns"), with the thread's stack.
* `sweep(layer, stride, seed)`: the runs for N = 1, 2, 3, then every
  `stride`th from 4 + seed % stride, for each fault, new and reopened,
  until a run with eviction (which makes the most calls) ends before call
  N, or eight runs in a row do.
  `Results` keeps one example of each finding's signature: the check, the
  layer and fault, and the call with its numbers taken out.
* The skip list, as 018-02's (section 4 there): `FAULTS` says which entry
  a finding is (the check, and a regular expression on the finding's
  text), `SKIP` lists the entries that are skipped until their fixes
  remove their lines, and `TIMING` the entries whose findings depend on
  timing, whose lines are not checked for passing. A finding of a skipped
  entry is printed ("Known fault 015-80, skipped") and passes; one of an
  entry not in `SKIP` fails and names it; one with no entry fails as "No
  entry, a new fault". In the night tests, which run every N, a line of
  `SKIP` whose findings did not occur fails the test: its fix removes it.
  With `-Dbergdb.storagefault.skip=none` nothing is skipped.
* `main`, for runs by hand: `StorageFaultTester LAYER STRIDE` sweeps,
  `StorageFaultTester LAYER FAULT N` makes one run and prints its state
  (each transaction's fate, the reclaims, the calls).

The skip list is empty since 2026-11-06. It held 015-80 (one writer at a
time: in most runs the workload's `getFirstPos()` met the storage
thread's append, OVERLAP) until its fix (33a81b9, `BufferedStream`'s
`ioLock`), and 019-10, which the harness found (section 5), until its
fix. `StrictStream` tolerates every kind, so that a run goes on past a
breach, and the harness reports each breach after the run.


## 3. Where it runs, and its cost

* `testSample`, in the Nano group "unit": for each fault, new and
  reopened, the STREAM calls 1, 500 and 1,500 and the IO calls 2 (the
  open), 60, 140 (the last flush before the close, in a new run) and 147
  (the close): 84 runs, 3.4 s on F53 under a night's load (a full
  workload takes about 40 ms). The unit tests run beside the f-tests in
  `before-commit.sh`, and the f-tests set its time. The calls were chosen
  so that the sample alone fails on the known faults that the harness
  catches (section 4).
* `testStreamLayerAll` and `testIoLayerAll`, in the Nano group "night",
  run by `night.sh`'s step night-tests: every IO call (1,187 runs, about
  50 s), and every 5th STREAM call (and the first three), from an offset
  of the day of the year, so that five nights run every call (about 3,900
  runs, 152 s on F53 in the night's load). Every STREAM call took 806 s
  with the IO test (19,399 runs, 35 % of a core: the runs mostly wait, for
  the storage thread's 10 ms and the syncs), too long beside the other
  night tests (about 4.5 minutes); cut on 2026-11-06.

From `java/`:

```sh
./unit.sh -c StorageFaultTester                      # the sample
./night.sh tests -c StorageFaultTester               # the night tests
java -ea -cp build/bergdb.jar bergdb.core.StorageFaultTester IO 1        # a sweep, every N
java -ea -cp build/bergdb.jar bergdb.core.StorageFaultTester STREAM 13   # every 13th N
java -ea -cp build/bergdb.jar bergdb.core.StorageFaultTester IO ERROR 2  # one run, its state
java -ea -cp build/bergdb.jar bergdb.core.StorageFaultTester SAMPLE      # the unit sample
java -ea -Dbergdb.storagefault.skip=none -cp build/bergdb.jar bergdb.dev.Unit -c StorageFaultTester
```

A sweep by hand prints each finding's signature, the number of runs
with it, and one example, and the runs that took more than 200 ms.


## 4. The evidence: the known faults

The faults of the class were fixed on 2026-11-05, so the harness was run
on the code before and after each fix: in two more clones
(`/Users/f/fl/bench/006-12/h62-old`, `h62-old2`), at each fix's commit
and its parent, with the harness copied in. Each point: the IO layer at
every N, the STREAM layer at every 13th N (`sweep.sh`, `chain.sh` in
`/Users/f/fl/bench/006-12/h62-out/`, which keeps the outputs). The commits
form one line on `main`, from 49a814e (before 015-66's fix, the first of
the class) to 7295fc5 (019-09).

A finding's signature: the check, the layer and fault, and the call. Each
row's signatures are found at the fix's parent and at every earlier
point, and at no later one.

* **015-53**, fixed by fddaf1f (parent 2266d84). "restart", STREAM
  STOP at a READ or GET_FIRST_POS of the workload's thread: "transaction
  N was refused (it threw), and is there".
* **015-35**, fixed by dc46c1e (parent e24276a). "background", IO and
  STREAM IO_EXCEPTION, UNCHECKED, ERROR at a write or an APPEND of the
  storage thread, without eviction: "get N returned after the storage
  had failed".
* **015-78**, fixed by 1b66a34 (parent dc46c1e). "close", IO UNCHECKED
  and ERROR at the force of the close: "the close met the fault, and
  close() returned normally".
* **015-32**, fixed by 37ce61f (parent 1b66a34). "lock", IO ERROR in the
  FileStream's open (the open, its force, the directory's force,
  openRead): "a new FileStream on the directory threw
  DirectoryInUseException".
* **019-09**, fixed by 7295fc5 (parent 949c3b2). "close" and "restart",
  IO IO_EXCEPTION, UNCHECKED, ERROR at the last flush's write, before the
  close: "the storage had failed, no call reported it, and close()
  returned normally", and "transaction 39 is lost; it returned, and no
  call reported a failure".

On 7295fc5 and on `main` (4d7a1bb) nothing but 015-80's OVERLAP.

Notes:

* 015-78's row: 1b66a34 fixed 015-78 and 015-34 together, the storage
  thread's close of the stream. Before it, the storage thread discarded
  its close's failure: an IOException there (015-78), and an unchecked
  exception or Error too, which the harness finds at the force of the
  close. `FAULTS` names all three 015-78.
* 015-81 (an unchecked close error ends the storage thread before it
  publishes a failed append, so a waiting `sync()` waits for ever): its
  fix, in dc46c1e with 015-35's, removes no signature of its own. Its
  case needs a `sync()` that waits in another thread during the close;
  the workload has one thread. On 49a814e the storage thread's uncaught
  exception is printed (its name in the output) at the close's force,
  which the "close" check finds as 015-78's.
* 7a80d0d (the review's corrections of 015-35 and 015-81) changes no
  signature.
* 49a814e → 2266d84 drops two STREAM ERROR signatures ("background" and
  "close" at an APPEND); between them are 578c263 (015-66) and the fixes
  of other classes. At every 13th N, one run each, they may be sampling;
  not counted for 015-66, which section 6 explains.

The unit sample (`testSample`) alone, at the same points (SAMPLE):

```text
49a814e: 015-32 015-35 015-53 015-78 019-09  SAMPLE FAILED
2266d84: 015-32 015-35 015-53 015-78 019-09  SAMPLE FAILED
fddaf1f: 015-32 015-35        015-78 019-09  SAMPLE FAILED   (015-53 fixed)
e24276a: 015-32 015-35        015-78 019-09  SAMPLE FAILED
dc46c1e: 015-32               015-78 019-09  SAMPLE FAILED   (015-35 fixed)
1b66a34: 015-32                      019-09  SAMPLE FAILED   (015-78 fixed)
37ce61f:                             019-09  SAMPLE FAILED   (015-32 fixed)
949c3b2:                             019-09  SAMPLE FAILED
7295fc5:                                     SAMPLE PASSED   (019-09 fixed)
```

So `before-commit.sh` alone would have failed on each of the five until
its fix, each failure named by its entry.


## 5. What it found on main

On `main` (4d7a1bb), besides 015-80's OVERLAP, one new fault: **019-10**,
found by the check "met" (a call that threw the fault, or an exception
caused by it, must leave the database failed: the next transaction or
read throws `DbFailedException`). An unchecked exception or an `Error`
from a stream read in the workload's thread (a get, or a transaction's
warm-up) is thrown as it is, and the database goes on; an `IOException`
from the same read fails it. 43 of 1,548 STREAM runs at every 13th N, new
and reopened; none in the IO layer, whose reads go through an open
channel. Registered as 019-10, in `SKIP` until its fix, and fixed the
same night (`StorageManager.read()` fails the storage on it; 019-10's
entry). Since, the harness finds nothing on `main` but 015-80's
OVERLAP.

Nothing else: no lost transaction, no refused one in the stream, no lock
or thread left, no hang, and every interrupt and stop left the database
working (the night tests, every N, 2026-11-06, 01:32: 20,586 runs).


## 6. What it does not cover

Known faults of section 6.2's list that the harness does not reach, and
why:

* 015-06's rest: a start that is refused (a decision of the start, as a
  clock out of range) leaves an empty first file. A refusal is not a
  storage failure, and the harness's failed starts are followed by a
  start that works, which is all its check asks. The entry is in progress
  in another session.
* 015-34: `BufferedStream`'s storage thread, interrupted while it stops,
  returned before it closed its stream. Its entry says that `Db.stop()`
  and `close()` repair it; through `Db`, only the experimental replicas
  reached it. The harness's interrupts of every BergDB thread at the
  close found nothing on the old code.
* 015-38: `Jmx.Speed`'s monitor thread. Nothing in BergDB starts it;
  `InterruptTester` checks its interrupts.
* 015-66: R4-F1's window, a writer that takes the write lock between a
  failed eviction batch's release of it and the failure's publication.
  It needs three threads in a forced order (R4's probe); the harness has
  one workload thread, and the evictor makes no stream call.
* 015-82: R5-F7's cut that arrives while another is made; `Db` asks only
  for cuts within the durable length, so the window is not reached from
  `Db` (R5-F7 says so), and its effect is a longer stream, no lost data.

And, by design:

* Durability across a power loss: the forces are counted, not made
  (`FileStreamPowerLossTester` is for them).
* Several application threads: the workload is one thread; the storage
  thread, the evictor and the closer run beside it. jcstress is 6.6.
* The Pub API: `DatabaseImp` adds no path of its own to a storage
  failure but its `close()`, which 019-09's test `PubTester.
  testCloseReportsBackgroundWriteFailure` covers.
* A fault in a `FileStream` that the storage does not call through
  `FileStreamIo` (a read of an open channel): reads fail through the
  STREAM layer instead.
* Two faults in one run.


## 7. Log

2026-11-05. Started in the night 006-12, in the clone
`/Users/f/fl/bench/006-12/h62`, branch `h62`.

2026-11-06. Built: `StorageFaultTester`. It fails on 015-32, 35, 53, 78
and 019-09, each on the code before its fix (section 4), also with the
unit sample alone, and found 019-10 (section 5), registered and in its
skip list. In the unit tests (the sample) and the night tests (every N).
BEFORE COMMIT OK.

2026-11-06. 019-10 fixed the same night (its entry): `SKIP` holds 015-80
only. BEFORE COMMIT OK.

2026-11-06. The night test of the STREAM layer runs every 5th call from
an offset of the day: 152 s, not 806 s with every call. BEFORE COMMIT OK.

2026-11-06, 03:20. 015-80 fixed on `main` (33a81b9): out of `SKIP` and
`TIMING`, its `FAULTS` line kept to name a regression; the skip list is
now empty. On it, through gate.sh: `testSample` passes (5.5 s), the night
tests pass (1,187 IO runs, 3,508 STREAM runs, 166 s), no OVERLAP. With
it, review R5's F3 on 019-10 (docs/levels.md's reflow, the Javadoc of
`StorageManager.hasFailed()` and `getFailure()`). BEFORE COMMIT OK.


## State (night 006-12)

2026-11-06, 03:20. Clone `/Users/f/fl/bench/006-12/h62`, branch `h62b`
(from `main` at 8130710): the follow-up (015-80 out of the skip list,
R5's F3) committed. Nothing open here; 019-10 waits for Frans's decision
on R5's F1 and F2 (its entry). Possible later: 015-81's stranded sync
needs a second application thread, which the workload does not have.
