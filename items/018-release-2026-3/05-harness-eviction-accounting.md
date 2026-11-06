018-05. Harness 6.5: eviction's accounting
==========================================

Created 2026-11-05 by Frans Lundberg, for night 006-12 (018-01, W2; his
words of 21:33: "Will you fix all bugs? ... There is plenty of time for
you to code as well, right?!"). Built in the night's harness work,
2026-11-05 and 06.

**Status: built; runs in `before-commit.sh`'s unit tests and in
`night.sh`'s night tests.** It fails on each of the five known faults of
its class (018-01, section 6.5), on the code with each fix's main hunk
taken out, and it found three more, 019-20, 019-21 and 019-22, fixed the
same night. It passes on the night's code with no skip list.


## 1. What it checks, and why

018-01, section 6.5: "random eviction schedules and budget changes,
during reads and writes, with `Audit` after each batch, and the resident
bytes compared with a recount". Its known faults, 015-67 to 015-71, were
each found by review R4 by reading one mechanism of the capacity
controller and the resident registry (`Eviction`, `Residents`, `Audit`);
each was fixed on 2026-11-05 with a test that makes its one case. The
harness checks the promises of those classes together, in random runs,
so that a fault no review has met is found too.

The promises, from the Javadoc:

* **The audit** (`Audit.check`) reports only what is wrong: a reader's
  valid work (a load, a cleanup of an empty handle) beside it is not a
  failure (015-71).
* **The resident bytes** (`Residents.bytes()`, the controller's measure)
  are the counts of the objects of the live handles, and the resident
  objects their number (015-69); each object is counted with its bytes now
  (`Residents.bytesOf`), but for the objects the writer changed since
  their last count, which are pinned until their write (`Residents`'
  class comment; 019-20, 019-21); no other object is counted.
* **Admission**: no resident pointer holds a value over 1 MiB, between
  transactions, with eviction on (`Eviction`'s class comment; 015-68,
  019-22).
* **A batch examines at most its handles**: 4,096, or 65,536 under
  pressure (`Eviction.BATCH`; 015-67).
* **A lowered budget is reached** when what must stay (the pins) fits it
  (`Eviction.setBudget(Db, long)`; 015-70).
* And every answer of a reader is the value of its key at its lookup
  time, whatever eviction did meanwhile.


## 2. How it works

Test code in `bergdb.core` (`EvictionAccountingTester`, in the package's
`Pack`), and two package-private methods of `Eviction` for it:
`batchesOverTheirHandles()`, the batches whose handles examined passed
their limit (counted in `sweep`), and `idle()`, whether the eviction
thread is idle (no request, no batch, the thread waiting or none).

A run, from a seed, on a `MemoryStream`:

* The database: the capacity controller (`Schedule.BUDGET`) with a random
  budget (from a few bytes to about 1.5 times the resident bytes, or
  none), nodes of at most 8 entries, a startup distance of 200 to 20,200
  bytes, the audit's oracle on (`audit(1 << 30)`: the audit itself runs
  only at starts and when the harness calls it).
* Readers (2, or 3 in the night shape): each get is of a random key at a
  random time of the history, the latest time in a third of them, and its
  answer is compared with the harness's own record of each key's versions.
  A quarter of the gets keep nothing (`Dag.CACHE_NOTHING`): their reads
  leave empty handles, which they remove (`Cache3.dropIfEmpty`), the path
  of 015-71. No production read keeps nothing, but the policy is the
  Core's, and the path is the readers'.
* The writer runs batches of 1 to 30 transactions (400 in the night
  shape), each of 1 to 5 keys: small values, a value over 1 MiB with
  probability 0.002 (0.0005), deletes. Between transactions, at random: a
  test schedule's eviction (`Db.Internal.evictNow`: values, every or
  random, which ends with a resync of the counts while the readers load,
  015-69's path), or a new budget, lower or higher. After a batch, now and
  then (1 in 25) a restart on a copy of the stream with a new budget, half
  of them right after a value over 1 MiB, which the start's rerun makes
  again (015-68's path).
* After each batch:
  1. The audit, under the write lock, while the readers go on: no
     failure, and no failed audit at a start.
  2. With the readers paused (a lock of the harness that each get holds),
     under the write lock, the recount: every object of a live handle is
     counted; the counts sum to the resident bytes and their number is the
     resident objects; a clean object outside D is counted with its bytes
     now; no object that the walk (`Residents.walk`) finds outside the
     live handles is counted; no resident pointer holds a value over 1 MiB.
  3. No batch passed its handle limit.
  4. With the readers paused, in 1 batch end of 6, a decrease after the
     pins fell, as R4's probe of 015-70 (`Eviction.testLoweredBudget
     AfterPinsFell` makes it directly): the budget lowered to 1 byte, so
     that the hand's rounds count the pins (P0); raised again; the writer's
     transactions until a write of the dirty nodes lowers the pins below
     3/4 of P0 (P1); detachable objects evicted until the resident bytes
     are at most P0, where a batch that counted with P0 stops; the budget
     lowered to (P0 + P1) / 2. Else, in 1 of 4 of the others, a decrease to
     10 to 95 percent of the resident bytes, and below the budget in force
     (the resident bytes may be above that budget, with pins above it: a
     higher budget is an increase, after which the controller stops at its
     trigger, the pins plus the gap between the watermarks). Either way, the eviction thread
     must be idle within 5 s, and if the pins (the counts of the objects
     that are not detachable) fit the budget, the resident bytes must be at
     most the budget.

The adaptation: 018-01 asked for the resident bytes "compared with a
recount". The estimate is not exact for a dirty object (the writer's
changes are counted at its write, by design, 015-15), so the recount
compares each clean object's count with its bytes, and the total with the
counts; the walk of the resident objects is used only to find counted
objects outside the handles.

Each run prints a line: its seed, what it did (reads, audits, recounts,
evictions, budget changes, decreases checked, restarts, large values) and
its time. A failure names the batch and the check, with the run's log of
starts, budgets and decreases.


## 3. Where it runs, and its cost

* **The unit tests** (`before-commit.sh`): `testAccounting`, seeds 1 to
  3 of the unit shape (300 keys, 25 batches), about 1 s.
* **The night tests** (`night.sh`'s night-tests step, which runs every
  Pack's night group): `testAccountingLong`, seeds 100 to 109 of the night
  shape (30,000 keys, 60 batches, more than 4,096 handles resident, so
  that a batch reaches its handle limit), 9 to 13 s a seed: 93 s on F53
  (`./night.sh tests -c EvictionAccountingTester`, 2026-11-06).

From `java/`:

```sh
./unit.sh -c EvictionAccountingTester                  # the unit test
java -ea -cp build/bergdb.jar bergdb.core.EvictionAccountingTester unit 1 30
java -ea -cp build/bergdb.jar bergdb.core.EvictionAccountingTester night 100 3
java -ea -Dbergdb.accounting.seed=24 -Dbergdb.accounting.debug=true \
    -cp build/bergdb.jar bergdb.dev.Unit -c EvictionAccountingTester
```

`main` runs seeds of a shape and prints each run's line and the first
failure; `bergdb.accounting.seed` makes the tests run that one seed;
`bergdb.accounting.debug` recounts after every transaction, which finds
the transaction that broke the counts.

The unit test adds nothing measurable to `before-commit.sh`: the unit
tests run beside the f-tests, which take the longest.

| `before-commit.sh` on F53, 2026-11-06 | Unit tests | F-tests | BEFORE COMMIT OK |
|---|---|---|---|
| 019-22's tree, before the harness | 1,222 in 30.6 s | 70.2 s | 116 s |
| The harness's tree, with it       | 1,223 in 30.2 s | 69.3 s | 116 s |


## 4. The evidence: the known faults

Each fix's main hunk taken out of the night's code (in the clone), the
harness built and run; then the hunk put back:

| Fault  | Taken out                                                 | Caught by |
|---|---|---|
| 015-67 | `clockStep(hand, d, pinned, Long.MAX_VALUE)`: whole maps | night seeds 100, 101, 102 |
| 015-68 | `Db.startInner`'s `eviction.recordWritten(...)`          | unit seeds 2, 17, 25, 27 |
| 015-69 | the old `resync`: the total set to the walk's sum        | 20 of unit seeds 1 to 30 |
| 015-70 | `goal()` the trigger; `pins()` the last round's, any age | 22 of unit seeds 1 to 30 |
| 015-71 | the audit's map lock and `liveHandle` check per handle   | 17 of unit seeds 1 to 30 |

The unit seeds are of `main` (`unit 1 30`); the unit test runs seeds 1 to
3, which meet all but 015-67. The failures, one line each:

```text
015-67: seed 100: batch 19: 2 batches examined more handles than their limit (4096, 65536)
015-68: seed 2: batch 0: the recount: pointer 7 of node 5279 holds a value of 1126456 bytes
        (over 1 MiB: not kept)
015-69: seed 2: batch 17: the recount: the resident bytes are 338949, the counts of the live
        handles' 640 objects sum to 340498; the resident objects are 637, the live handles'
        counted objects 640
015-70: seed 1: batch 21: a decrease after the pins fell settled at 19763 bytes: P0 19933,
        P1 14029, 19763 bytes, budget 16981, pins now 14029: eviction BUDGET: ...
015-71: seed 7: batch 11: the audit: [handles: the node table has a dead handle of node 2788133]
```

015-67 needs more than 4,096 resident handles, which only the night shape
has. Before the readers' `CACHE_NOTHING` gets, 015-71 was not met at all:
with the production policies a reader keeps what it reads, and leaves no
empty handle. Before the pins-fell scenario, 015-70 was not met: a plain
decrease does not make its state. On the night's code with the fixes,
unit seeds 1 to 30 and night seeds 100 to 102 pass.


## 5. Faults it found

Three, each registered, fixed and closed the same night, one commit for
019-20 and 019-21 together and one for 019-22, before the harness's:

* **019-20**: a key node that its transaction grew (`addKlong`) and then
  replaced (`handleFullNode`, `toPreviousState`) was made clean by
  `Db.endOfTrans` with no count, and stayed counted below its bytes until
  its eviction. Found in unit seed 3: "the clean object of node 8117 is
  counted with 973 bytes, its bytes now 1165".
* **019-21**: a start counted the startup section's nodes before its rerun
  of the transactions changed them. Found in unit seed 2, after a restart:
  "the clean object of node 4293 is counted with 430 bytes, its bytes now
  608".
* **019-22**: a transaction's warmup read with `Dag.CACHE_ALL`, and so put
  a key's old value over 1 MiB back into its leaf. Found in unit seed 24:
  "pointer 1 of node 1298967 holds a value of 1126456 bytes (over 1 MiB:
  not kept)".

Each was traced to its line with a trace build (the counts of one node
id, and the changes of its pointers, printed with their stacks). The
stream's bytes are unchanged by the three: StreamDigest's quick digests of
the clone with the fixes equal those of the night's base, 45cfb4f ("DIGESTS
IDENTICAL (44 of 44; of the identical, the physical cut differs in 0)").


## 6. What it does not cover

* Reclaim: the runs keep every version (the test setup's retain duration
  is forever). Reclaim's eviction of a step's pins is level 4's
  ReclaimReaders and RestartInvariance with forced schedules.
* The values of a dirty object's pointers between its changes and its
  write: by design not counted until the write (015-15), so not compared.
* `FileStream`, crashes, and failures of the eviction thread (015-66):
  6.2 and level 4.
* Large databases: the night shape has 30,000 keys; `LargerThanMemory`
  (level 4, step 6) runs 2,000,000.
* The readers' concurrency with a batch beyond what the runs meet: 6.6
  (jcstress).


## 7. Log

2026-11-05, 21:35 to 22:10. Started in night 006-12: the harness in the
clone `/Users/f/fl/bench/006-12/h65`, branch `h65`; it found 019-20,
019-21 and 019-22 at once, and fails on 015-67, 68, 69 and 71 with their
fixes taken out. Stopped for the night's quiet block.

2026-11-06. Resumed at 00:49: the pins-fell scenario, which catches
015-70; the three faults fixed with their tests (019-20, 019-21, 019-22);
the item written. Gates of the harness's tree: BEFORE COMMIT OK (116 s),
LEVEL 4 OK (full, 01:29 to 01:43), the night test SUCCESS in 93 s.

2026-11-06, 01:50. 200 more unit seeds (31 to 230) and 8 night seeds (110
to 117): one failure, unit seed 56, "a decrease of the budget to 32601
settled at 32722 bytes (from 36533), the pins 27759 fit". Not a fault:
the budget in force was lower (21,089, from batch 5), so the "decrease"
was an increase, after which the controller rightly stops at the trigger.
The harness's plain decrease now goes below the budget in force; unit
seeds 1 to 60 pass. BEFORE COMMIT OK.
