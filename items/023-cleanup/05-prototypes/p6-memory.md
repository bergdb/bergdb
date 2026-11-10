# 023-05 P6. The memory of ended versions, released in ordinary operations

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P6 of 023 (023-05): the memory that ended versions hold is
released in the ordinary operations, on top of P4 (the upward unlink with
the empty key first). Frans, 12:35 (023-04, Y6): "Option (b), we follow
the rule for resource release, also for memory." And 12:31 (Y10): the
cleanup goes on in the ordinary operations, and `maintain()` is optional.
The code is on the branch `023-p6-memory` of the clone
`/Users/f/fl/bench/2026-11-10/p6/clone`, on P4's head `0e66d1c9` (fetched
at 12:40).

In short:

* **Two mechanisms, both eviction.** Each takes only objects that the
  capacity controller could take, and the records do not change.
  * **The dead hand.** After a cut at pCut, every object stored before
    pCut is dead. This is Reclaim's guarantee: whatever a lookup at an
    available time can reach is stored at pCut or later, or is dirty. A
    round over the node table, at most 4,096 handles and 2 ms a
    transaction, evicts these objects whatever the budget. It also turns
    the pointers to values stored before pCut into stream pointers.
  * **The replaced queue**, 023-04's X6 (b) as written. The objects of
    the nodes that a transaction replaced or unlinked leave memory once
    they are written, also with R forever.
* **T1 "after" at N = 100,000, budget 1 GB, end of the drive, no restart.**
  * P4: 11,612 resident objects and 37.9 MB counted.
  * The dead hand alone: 292 objects and 1.67 MB. The twin: 263.
  * Both mechanisms: 152 objects and 0.31 MB. The twin: 89.
  * The database's heap after a GC: 17.3 MB with P4, 2.7 MB with P6, the
    twin's 0.7 to 0.8 MB. Most of the rest is the STM's hashes of the
    deleted keys, a constant that later writes push out (section 4.4).
  * At N = 1M with a drive of 12,000: P4 113,768 objects (352 MB), P6
    236 (0.19 MB), the twin 90. Hashed keys at 100,000: P4 127,255, P6
    150.
* **T4's ordered queue, 100,000 transactions, budget 1 GB.**
  * P4: resident objects grow without end, 2,290 to 24,113 (52 MB).
  * The dead hand: steady at 712 to 858 objects.
  * Both mechanisms: steady at 151 to 185 objects.
  * Under a 1 MB budget: 6,515 loads with both mechanisms, against
    81,137 with P4.
* **Readers.** A scan held at the first available time while the dead
  hand took 59 to 78 of the objects around it expired with
  `LookupTimeNotAvailableException` from a read below the cut, in every
  one of 6 seeds. It never gave another answer, and the database went on.
* **The cost of the replaced queue.** Lookups at earlier times load what
  it evicted. So does reclaim's scan of an iteration in progress, at its
  tStart, after a mass delete: T1 at 100,000 with a 1 GB budget loads
  190,272 versions, where P4 loads none. Section 4.3; question Q2.
* **Gates.**
  * `before-commit.sh`, `level1.sh` and `level4.sh quick` passed on the
    dead hand.
  * `before-commit.sh` and `level4.sh` full passed on the head, with both
    mechanisms (section 3).
  * The model needs no change: both mechanisms are an eviction schedule.
    Conformance with C-P and C-H passed.
* **The run of dirty top nodes** (023-06, "top nodes in D"; P4's Q4). The
  cause is found. Rule A, with the take's oldest-first order, holds a
  sliding window of consecutive top nodes whose length freezes at what a
  disturbance left. No small fix exists (section 5).


## 1. The mechanism as built

Code places are on the branch's head, in `java/src/bergdb/core/`.

### 1.1 What is dead after a cut

Reclaim's class comment states that when an iteration is done, every node
and value reachable at times from tEnd on is stored at pCut or later
(index nodes at pStart or later), or is dirty and will be written there.
The cut waits for that: the startup pos must pass pEnd and then pSafe.
The cut then makes tEnd the first available time f, and pCut the first
available position (`Reclaim.pretruncateIfPossible`, Reclaim.java:875).

So an object whose version is stored before pCut is reached by no lookup
at a time of f or later:

* **A canonical object.** It holds the node's latest written version. If
  the node is reachable at a time of f or later, that version is at
  pStart or later, or the node is dirty, and so pinned.
* **A version read by a reader.** Its node may still be current with a
  newer version, but a lookup at an available time follows a reference at
  pCut or later, and an older version does not serve it
  (`Handle.usable`).
* **Top nodes**, which no touch reaches. A top node reachable at a time t
  of f or later is one of two kinds:
  * One that was super root at t. It was replaced after t, so after tEnd,
    and its last write came after the transaction before its replacement.
    That is a changing transaction of tEnd or later, as every changing
    transaction marks the super root.
  * One passed on the skip-list walk (`TopDs.findSuperRootAtTime`). Its
    root time is t or later, so it became super root after tEnd.

  Both are stored after pStart, so the guarantee holds for top nodes too.
* **Values.** A value live at a time of f or later was put after the cut
  iteration's tStart, or was rewritten by its step when stored before
  pCut. So a value pointer that names a position before pCut belongs to a
  klong that is deleted or shadowed at every available time.

### 1.2 The dead hand

* **What.** One round over the node table for each cut that moves the
  decided cut position.
  * Each handle's object stored before the cut (a stream position below
    `Reclaim.getFirstAvailablePos`) is evicted if it is detachable,
    whatever its CLOCK bit and the resident bytes (`Cache3.deadStep`,
    Cache3.java:498). The handle dies, its written position is kept, and
    the object leaves the handle and the table (`Cache3.kill`).
  * A live handle with no object leaves the table, as in a CLOCK step.
  * In each key node that stays, pinned ones included, a pointer that
    holds a value stored before the cut becomes a stream pointer
    (`Eviction.unswizzleValue`).
* **When and by whom.** The writer's thread, at the end of every
  transaction, under the write lock and between transactions
  (`Eviction.afterTransaction`, Eviction.java:332, which calls `deadStep`,
  549).
  * A step examines at most 4,096 handles (`DEAD_BATCH`; an empty map
    counts one) and runs at most 2 ms, as a batch of the capacity
    controller does (`BATCH_NANOS`).
  * A map is taken in parts as in the CLOCK steps (015-67). The next step
    goes on where the last one stopped, and the round ends after map
    4,095.
  * A round runs only when the decided cut position has moved since the
    last round began. Then the hand is idle until the next cut.
* **Where it runs.** In the capacity controller's schedule with a budget,
  and in the test schedule `random`. Not under `noEvict()`, whose
  contract is that nothing is freed: the test setups use it, and so does
  T1's default. Question Q3.
* **Switch.** `-Dbergdb.p6.dead=false` turns it off (prototype only).

### 1.3 The replaced queue

* **What.** The objects of the nodes that a transaction replaced or
  unlinked are queued at its end: Dag's `keyNodeReplaced` and
  `topNodeReplaced`, for a time split, a space split, the upward unlink,
  root collapse and a new super root (`Db.endOfTrans`, Db.java:1530;
  `Eviction.nodesReplaced`, 496).
  * After each transaction, a step evicts the queued objects that are
    clean, written and still their handles' objects (`replacedStep`,
    508), at most 4,096 entries a transaction.
  * A dirty one goes to the back of the queue: its take writes it later,
    and Rule A may keep it dirty longer.
  * A node made and taken back in its transaction was never written; it
    leaves the queue.
  * The newest written top node is pinned and waits.
* **Why it is right.** No lookup from the replacing transaction's time on
  follows such a node. Lookups at earlier times load it again from the
  stream, which holds it until a cut. This is 023-04's X6 (b) as written,
  and it works with R forever too, where no cut comes.
* **Where it runs.** In the same schedules as the dead hand.
* **Switch.** `-Dbergdb.p6.replaced=false` turns it off.

### 1.4 Readers, handles and the writer

Both mechanisms evict through the same steps as the capacity controller
(`Cache3.kill`, `Eviction.detachable`). So what holds for eviction holds
here (levels.md, 7; Eviction's class comment, "Readers"):

* **A reader that holds an evicted object finishes with it.** The kill
  clears a canonical object's flag (M31). The object is the version at
  its position, so its answers are right.
* **A reader that follows the pointer again** resolves the dead handle by
  the node's id. The slow path raises the reference to the handle's
  written position (`NodeCollection.followStreamPointer`, steps 2 and 3).
  * A reader admitted at a time of f or later then reads at pCut or
    later (1.1).
  * A reader admitted before the cut may read below it and expire with
    `LookupTimeNotAvailableException` (D1 = A). It cannot get a wrong
    answer.
  * If the physical cut has not been made yet, because it waits for
    durability, the load succeeds and a dead object is resident again
    until the next round. A load that expires leaves a live empty handle,
    which the next round or a CLOCK step removes.
* **Pinned objects are never taken** (`Eviction.detachable`): the super
  root, the newest written top node, D's canonical objects and the
  record's. So the writer's objects, D and Rule A are untouched.
  * Rule A (`DbHelper.hasDirtyChild`) sees an evicted child as clean, and
    it is clean.
  * The record rule writes a dead handle's written position, as after any
    eviction (`Handle.serializedRef`).
  * The writer reaches only current nodes, at tt of f or later, and never
    a dead one. The replaced queue takes only nodes that are no longer
    current, once clean.
* **Loads by reclaim and the warmup.** Reclaim's scan reads through the
  maintenance follower, which loads what is not resident and installs
  nothing. The warmup ignores an expired read (015-52).

### 1.5 The Lean model

No change. The model proves that with any eviction schedule over
detachable objects, the records, D and the answers are those without
eviction: T-CACHE, T-READ, T2-C and T-PIN (001-08, section 5), and with
handles and cuts `tc_handles`, `t9_handles` and `t12_handles` (009-05;
005-62). The dead hand and the replaced queue are such schedules.

Java's checks run them:

* The audit (INV-CAN, the pins, INV-SLOT), in Eviction's twins.
* `conformance.sh evict`, in `level4.sh` step 5. Its sets `e-r-small`,
  `e-r-long` and `e-r-restart` (random, with R) and `e-r-budget` run the
  dead hand under C-P and C-H.
* `EvictionInvariance` and the twins: the same stream, byte for byte.


## 2. What changed, and why

| Commit     | What                                                                  |
|---|---|
| `83e1cb86` | the dead hand (Eviction, Cache3.deadStep); CleanupRule's counts       |
| `411ae3d1` | tests (2.1); its timing; CleanupRule's heap, histogram and D probe    |
| `6451d774` | the replaced queue; CPU time and a 2 ms bound; the top-node probe     |
| `c46d607d` | DbTesterJavadoc's eviction-thread test: a budget below the resident   |

`c46d607d`: with the replaced queue, `testOwnThreadsAreDaemons` lowered
the budget to 100 kB while only about 77 kB were counted resident (161 kB
before). The eviction thread then had no reason to start, and the test
waits for it. The new budget is 10 kB. This is an expected change of a
test's value (023-03, 6.2), not a fault.

### 2.1 Tests added

* **`Eviction.testDeadHand`**, and an f-test with a longer drive. A twin
  pair: one database with a budget of 1 GB, against one without eviction,
  with R = 1 s; puts, deletes of most keys, then overwrites with
  restarts.
  * After every transaction whose round is done (`Twin.checkDead`), no
    detachable object stored before the cut is in the table, and no key
    node there holds a value stored before it.
  * The hand took objects and values.
  * The streams match byte for byte, and lookups at every available time
    match. The audit is on.
* **`Eviction.testReplacedQueue`.** The same with R forever. Fewer than
  half the twin's resident objects, the same stream, and the same lookups
  at every time, which load the evicted versions again.
* **`ReclaimReaderTester.testHeldReadersAndTheDeadHand`** (f-test). The
  existing scenario, with a budget of 1 GB:
  * A scan at the first available time first makes its nodes resident.
  * A second scan at that time is held after its first KV, while the
    writer runs until the cut passes the stream length at the restart,
    and 5 transactions more.
  * In each of 6 seeds the hand took 59 to 78 objects while the reader
    was held.
  * Every reader expired with `LookupTimeNotAvailableException` from a
    read below the cut (`ReadBelowFirstPosException`), and the database
    took writes after.
  * A reader that ends must return the first scan's KVs; in this run none
    ended.

### 2.2 CleanupRule

The measures are additions, so the existing output is unchanged:

* the dead hand's counts and times, and the replaced queue's count;
* the database's heap after a GC (`heapUsed`): the heap at the end of the
  drive less the heap after the close, the test's model being in both;
* a class histogram (`histo=N`);
* a probe of D's top nodes (`dprobe=1`, at every checkpoint with
  `dprobe=2`).


## 3. The gates

| Gate                    | On         | Result                                              |
|---|---|---|
| `before-commit.sh`      | `83e1cb86` | BEFORE COMMIT OK (355 s)                            |
| `level1.sh`             | `411ae3d1` | LEVEL 1 OK; Props MEM 129 (at most 131)             |
| `level4.sh quick`       | `411ae3d1` | LEVEL 4 OK, steps 1 to 6                            |
| `before-commit.sh`      | `6451d774` | 1 unit test failed: DbTesterJavadoc (2.1, c46d607d) |
| `level4.sh quick`       | `6451d774` | LEVEL 4 OK, steps 1 to 6                            |
| `before-commit.sh`      | `c46d607d` | BEFORE COMMIT OK (320 s)                            |
| `level4.sh` full        | `c46d607d` | LEVEL 4 OK, steps 1 to 6 (about 16 minutes)         |

`level4.sh quick` on `411ae3d1`, step by step:

* EvictionInvariance: 3 runs.
* RestartInvariance: stream identical.
* CrashTest and ReclaimStress with every and random: 0 failures, the audit
  0 failed.
* ReclaimReaders: 5 configurations, 0 failures. The capacity controller
  ran with a small budget; "expired during" counts 0 to 120.
* Conformance evict: 15 traces, TRACECHECK OK; C-P and C-H 0 of 3,454
  transactions fail.
* LargerThanMemory: live heap at most 44 MB.

`level4.sh quick` on `6451d774`, with the replaced queue, gave the same
result:

* ReclaimReaders: 0 failures.
* Conformance evict: 15 traces, TRACECHECK OK; C-P and C-H 0 of 3,454
  transactions fail.
* LargerThanMemory: live heap at most 44 MB.

On `6451d774` the f-tests (88, with P6's) and the demos passed.

`level4.sh` full on `c46d607d`, step by step:

* Unit tests: 1,627 passed.
* EvictionInvariance: 9 runs, 0 audits failed.
* RestartInvariance: stream identical.
* CrashTest: 8 rounds. ReclaimStress: 60 rounds with a cut, every and
  random, 0 failures.
* ReclaimReaders: 6 rounds in each of 5 configurations, 0 failures. With
  the capacity controller's small budget, 192 reads expired during their
  run, all as expected.
* Conformance evict: 45 traces, TRACECHECK OK; C-P and C-H 0 of 10,356
  transactions fail.
* LargerThanMemory: 2M keys, budget 50 MB; live heap at most 82 MB.

`level3.sh` was not run: P6 does not change reclaim. StreamDigest was not
run: the records are those of P4.


## 4. The measurements

All counts are on the clone, on F53, which other agents' runs loaded to
about 35 on 10 cores. Times are wall-clock unless marked CPU. Rows marked
"dead" have the dead hand only (`411ae3d1`). Rows marked "P6" have both
mechanisms (`6451d774`). P4 is the same build with both switches off. The
streams are the same in every row of a test: the same length and the same
cuts.

### 4.1 T1 "after", budget 1 GB, at the end of the drive, without a restart

| N       | Database | P4: objects | MB    | dead: objects | MB   | P6: objects | MB   |
|---|---|---|---|---|---|---|---|
| 1,000   | twin     | 581         | 4.63  | 263           | 1.54 | 89          | 0.29 |
| 1,000   | emptied  | 676         | 4.93  | 300           | 1.78 | 153         | 0.22 |
| 100,000 | twin     | 581         | 4.63  | 263           | 1.54 | 89          | 0.29 |
| 100,000 | emptied  | 11,612      | 37.88 | 292           | 1.67 | 152         | 0.31 |

At N = 1,000,000 the drive of 4,000 ends before reclaim has passed the
deletes. Reclaim's iteration in progress scans every key that was live at
its tStart, about 7,500 transactions (P2's finding 6). The table therefore
uses a drive of 12,000, as P4 did; the twin is driven 12,000 too. "D" is
the emptied database's D at the end.

| Build | Twin: objects | MB    | Emptied: objects | MB     | D   | Loads     |
|---|---|---|---|---|---|---|
| P4    | 1,738         | 14.10 | 113,768          | 352.18 | 166 | 0         |
| dead  | 274           | 1.57  | 382              | 1.81   | 166 | 0         |
| P6    | 90            | 0.20  | 236              | 0.19   | 166 | 1,040,504 |

* At drive 4,000 at 1M, the dead hand has not yet had its cut past the
  deletes: 107,011 objects; at drive 8,000, 383.
* With P6, 157 of the 236 objects are D's run of dirty top nodes and 9
  are its other objects (section 5); the twin's D is 77 of its 90.
* P6's loads are reclaim's scan of the iteration in progress over the
  million deleted keys (4.3).
* The database's heap after a GC is not given at 1M: two runs with the
  same counts gave 21 and 88 MB.

* Objects are the resident index objects (`Residents.objects`, M11's
  measure without the restart). The node table's live handles are the
  same number.
* MB is the counted resident bytes (`Residents.bytes`), which count a
  value once for each holder.
* The database's heap after a GC, at N = 100,000: P4 17.25 MB, dead 2.72
  MB, P6 2.68 MB. The twin's: 1.13, 0.81 and 0.68 MB.
* After a restart and the probe, as on P4 in every row: 85 (twin), 102
  (N = 1,000) and 99 (N = 100,000).
* With P6, the emptied database's objects are the twin's plus 64 at N =
  1,000 and 63 at N = 100,000. D accounts for 11 of these at 100,000
  (D = 90 against 79, section 5).
* What the dead hand did at N = 100,000: 15 rounds, 11,320 objects and
  58,131 values in 33 steps.
  * With the 2 ms bound: 41 steps, 36 ms of CPU in all, at most 2.0 ms of
    CPU a step.
  * Before the bound: at most 6.7 ms of CPU a step, and wall times up to
    104 ms on the loaded machine.
* With R forever (`retain=0`), N = 100,000: 36 objects with the replaced
  queue against 10,134 without it. The twin: 15 against 534. The
  database's heap: 2.30 MB against 14.22 MB.

### 4.2 T1 with a small budget (1 MB, M13's), and the loads

| N       | Database | P4: objects | loads   | dead: objects | loads   | P6: objects | loads   |
|---|---|---|---|---|---|---|---|
| 1,000   | twin     | 161         | 20      | 185           | 23      | 89          | 13      |
| 1,000   | emptied  | 177         | 17      | 197           | 23      | 153         | 651     |
| 100,000 | twin     | 175         | 23      | 193           | 11      | 89          | 13      |
| 100,000 | emptied  | 195         | 679,576 | 211           | 679,588 | 152         | 691,397 |

* Every row stays within the budget.
* The dead hand alone leaves a few more objects than P4. It takes dead
  objects before the capacity controller would, so the controller runs
  less often, and its last batch falls at another point. The loads are
  the same.
* P6 leaves fewer objects; the loads rise by 1.7 % at N = 100,000. Those
  are reclaim's, see 4.3.

### 4.3 T4, the queue, 100,000 transactions; hashed keys

Resident objects at the checkpoints:

| Budget | Build | 10,000 | 30,000 | 50,000 | 70,000 | 100,000 | Loads at 100,000 |
|---|---|---|---|---|---|---|---|
| 1 GB   | P4    | 2,290  | 7,138  | 11,991 | 16,847 | 24,113  | 0                |
| 1 GB   | dead  | 712    | 744    | 746    | 798    | 766     | 0                |
| 1 GB   | P6    | 158    | 178    | 181    | 177    | 159     | 6,515            |
| 1 MB   | P4    | 457    | 516    | 454    | 491    | 421     | 81,137           |
| 1 MB   | dead  | 484    | 454    | 458    | 489    | 415     | 83,470           |
| 1 MB   | P6    | 158    | 178    | 181    | 177    | 159     | 6,515            |

The counted bytes at 100,000 with a 1 GB budget: P4 52.4 MB, dead 1.40 MB,
P6 0.31 MB.

What the table shows:

* **P4 below its budget.** A steady-state queue keeps every replaced and
  unlinked version until the budget is reached: 0.24 objects for each
  transaction.
* **The dead hand** keeps the window since the last cut or two.
* **The replaced queue** keeps hardly more than D and the current tree.
* **Under pressure.** With 1 MB, the replaced queue saves 92 % of the
  loads: CLOCK no longer evicts current nodes to make room for replaced
  ones.

Hashed keys (T2's "hashed" in T1, and T4's hashed queue), N or M =
100,000, budget 1 GB, resident objects and loads:

| Test             | P4: objects | MB     | P4: loads | P6: objects | MB   | P6: loads |
|---|---|---|---|---|---|---|
| T1 hashed, twin  | 581         | 4.63   | 0         | 89          | 0.29 | 13        |
| T1 hashed        | 127,255     | 75.71  | 0         | 150         | 0.23 | 317,393   |
| T4 hashed, 10k   | 22,119      | 10.44  | 0         | 2,159       | 0.81 | 15,410    |
| T4 hashed, 50k   | 110,812     | 52.96  | 0         | 2,164       | 0.83 | 87,318    |
| T4 hashed, 100k  | 221,632     | 106.03 | 0         | 2,169       | 0.83 | 176,498   |

In the hashed queue, P6 loads about 1.8 versions a transaction. Reclaim's
scan at its tStart reads the leaves that the queue's puts and deletes
have replaced since; P4 keeps them in memory, 2.2 objects a transaction.

The cost is in T1, not in T4's ordered queue. With a 1 GB budget at
N = 100,000:

* P6 loads 190,272 versions, 82,326 of them by the end of the deletes.
  The dead hand alone and P4 load none.
* The loads come from reclaim's iteration in progress. It scans at its
  tStart every key that was live then, so it reads the leaves and values
  that the deletes unlinked and the queue evicted.
* With a budget the database needs, P4 pays these loads too (4.2).
* 023-06, section 2 proposes that reclaim's scan read at each step's time
  rather than at tStart. That would skip the deleted keys and remove
  these loads.

### 4.4 What is left in the heap

The class histogram at the end of the drive, N = 100,000 against the twin,
with the dead hand (`histo=30`). The test's model of 100,000 keys is in
both heap figures and so cancels out; it is the large `TreeMap`,
`HashMap$Node` and `HashMap$Node[]` entries. The database's 2.7 MB
against the twin's 0.7 MB is mostly one structure:

* `long[]`: 1.85 MB against 0.19 to 0.25 MB. This is `KeyModSet`, the
  STM's hashes of written keys: 128,000 pairs at most, in 4 bins (023-02,
  K18, "a constant"). It held the 100,000 deletes' hashes; new writes
  push them out, bin by bin.

Cache3's 4,096 maps were a suspect, as a HashMap's table never shrinks
(the K16 kind of 023-02, R4). A probe of the most handles each map held
found at most 9 (10,106 in all) at N = 100,000, so their tables are small
here. With a large budget they are not: 2 million resident objects make
about 500 handles a map, and tables of about 33 MB that stay after the
handles go.

A fix is written, but it is not on the branch: tested by unit tests only,
and it changes the node table's locking.

* Each map gets a lock object of its own, `getLock` returns it, and every
  access to a map is under it.
* A map that held 16 handles or more and now holds an eighth of them or
  fewer is replaced by a copy (`Cache3.shrink`).
* The dead hand calls it as it passes a map.
* The patch is `/Users/f/fl/bench/2026-11-10/p6/runs/cache3-shrink.patch`,
  with a unit test.


## 5. The run of dirty top nodes (023-06; P2's finding 7, P3's 5.2, P4's Q4)

### 5.1 What the probe shows

CleanupRule's `dprobe` reads D at checkpoints. It runs on P4's code with
both of P6's switches off and no eviction (`n=1000000 drive=12000`). This
reproduces P4's numbers: max D 178, and 184 objects after a restart.

* **D is mostly a run of dirty top nodes with consecutive ids**: 157 of
  166 at the end of the drive. They are all replaced but the super root.
* **The run is a sliding window.** Both of its ends advance about 72 ids
  every 1,000 drive transactions, which is the rate at which new top
  nodes are made. The space root is the segment leaf that holds "/a.txt",
  and its time split comes about every 14 overwrites.
* **Its length freezes early.** At N = 1M: 60 nodes at drive 1,000, 130
  at 2,000, then 152 to 161 to the end. The twin: 50 to 61 from the
  start.
* **Inverted pairs.** Count the pairs of consecutive dirty top nodes where
  the newer one waits in an older got-dirty list (`TransSeq`) than its
  predecessor. There are 39 such pairs at every checkpoint from drive
  3,000 on at 1M, and 10 or 11 in the twin.
* **The oldest dirty top node has no dirty child.** Its list is about 110
  kB of stream back. Every other node has a dirty skip target: the next
  older ones.
* **The newest few have a dirty replaced root.** Each replaced root has
  one dirty child, the same current node for all: the segment tree of
  the internal keys "/#i/dreclaim/...", which every reclaim step writes.
  The run's older roots are clean.

### 5.2 The cause

* **Rule A.** The still-dirty test (`Db.handleStillDirtyNodes`, Db.java:2838;
  `DbHelper.hasDirtyChild`) keeps a written node dirty while a node it
  points to is dirty. A top node points to its root and, by skip
  pointers, to older top nodes.
* **Where a re-dirtied node waits.** Rule A puts a re-dirtied node into
  the got-dirty list of the transaction whose record wrote it, which is
  the newest list. The take writes lists oldest first, a share in each
  record (005-49).
* **What an inversion costs.** Within one record, the fixpoint cleans a
  whole chain at once. Across records it does not. Where a newer top
  node waits in an older list than its predecessor, the take writes it
  first, it sees the predecessor dirty, and it waits a full cycle, about
  the take's lag. The next newer node waits on it in turn.
* **The window freezes.** Each cycle, the run cleans at its old end as
  many nodes as the inversions let through. That is as many as joined at
  the head in the cycle, since each new super root is dirty and points to
  its predecessor. The pattern of inversions moves with the window and
  keeps its count, so the run neither grows nor shrinks. Its length is
  whatever a disturbance left.
* **What formed the run at 1M:** the first 2,000 to 3,000 drive
  transactions after the deletes. Reclaim's iteration in progress scans
  every key that was live at its tStart (P2's finding 6), D grows to
  about 250, and roots change in quick succession.
* **Why it depends on the history.** That is why it depends on the batch
  size or the value size, and not on LE-b (P4, 3.6).
* **A risk not measured:** a later disturbance may add inversions, and so
  ratchet the run up.

### 5.3 Fixes, none small

Each changes what records hold, or the format, and so the Lean model's
take or Rule A:

* **(a) Write a top node's dirty skip targets in the same record.** The
  take adds a written top node's dirty older top nodes to its record
  (each about 100 bytes), so the fixpoint cleans the chain at once.
  * It must stay a function of the stream. A start rebuilds D from the
    records' got-dirty lists, so a node written ahead of its list must be
    known to be clean at a start too.
  * It changes the model's take and what the records hold.
* **(b) Rule A for a replaced node, by its replacement.** A replaced node
  needs, for each child, a version written after its replacement, not a
  clean child: any later version holds the history its times need (lemma
  M). This needs the replacement time of every node in D after a start,
  stored with the node's version: a format change (P3, 5.3).

Not done here. The run is bounded by what formed it: 157 top nodes, about
16 kB of stream at each of their writes, and 166 objects in D.


## 6. Requirements and tests met

023-02, as P4 gives them, with these changes:

* **R4 (memory).** As worded, and now with Frans's Y6 answer. A dead
  version's objects leave memory at the dead hand's round after the first
  cut whose pCut passes their position, whatever the budget. A node
  unlinked or replaced at tt and written at p is dead from the first cut
  with tEnd after tt, and goes at the first round with pCut above p:
  about one or two cuts later. With the replaced queue it goes as soon as
  it is written. Not with `noEvict()` (Q3).
  * R4's last clause, no structure keeping a size it reached, holds for
    KeyModSet by its bins (K18).
  * For Cache3's maps it holds only with the patch of 4.4.
* **R14 (memory).** Heap bytes for each live KV are as before: Props MEM
  is 129, at most 131 (`level1.sh`). D is P4's (section 5).
* **R1, R16 (lookups, readers).** Every check run (section 3), and the
  held reader (2.1).
* **R26 (performance).** The same stream. With the replaced queue, more
  loads at earlier times and by reclaim's scan of an iteration in
  progress (4.3); fewer loads under pressure. The dead hand costs at most
  2 ms of CPU a step, steps run only after a cut, and a round is bounded
  by the table.
* **023-03's C9** (M11 after the probe) is unchanged: a restart loads
  what it loads on P4.
  * P6 changes the same count without a restart, which 023-03 gives no
    allowance. At N = 100,000: 152 against the twin's 89, and 292
    against 263 with the dead hand alone.
  * The 63 more are above T1's allowances: 10 strict, about 14 bounded.
  * D accounts for 11 of them (section 5). The rest are the versions
    stored since the last cuts, still within reach of the available
    times, or not yet passed by a cut.
  * C12's M13 is in 4.2.


## 7. Faults and limits found

* **No fault found** in the gates run so far. The one test that failed,
  DbTesterJavadoc's, waited for an eviction thread that the replaced
  queue gave no reason to start: an expected value (2.1, `c46d607d`).
* **The held-reader test's first version** found that a writer phase of
  one cut leaves no dead objects resident: the loads of a newer version
  replace the scan's versions. The test now runs past two cuts (2.1).
* **Times on F53.** These are unreliable today. A step's wall time
  reached 104 ms before the 2 ms bound, while its CPU time was 6.7 ms at
  most. A quiet-machine timing is needed.
* **No cut, no dead hand.** With R forever, or before the first cut, only
  the replaced queue releases anything: values held by deleted or
  shadowed klongs of current leaves stay, as the history they are part
  of. An idle database does no work (P3): a round in progress waits for
  the next transaction.
* **Readers before the cut** may make dead objects resident again until
  the next round (1.4).
* **`noEvict()`** keeps everything, as its contract says (Q3).
* **No `maintain()`** on this branch. With P3's, a call would run the
  hand's steps too.


## 8. What is left for a production version

* Settle the schedules and the switches (Q2, Q3), and update levels.md,
  section 7. Its "an object stays while it is pinned, recently used, or
  the resident bytes are under the budget" changes.
* Time the dead hand and the replaced queue on a quiet machine, with
  large tables (10M nodes), against the 2 ms bound. The replaced queue's
  step is bounded by its 4,096 entries only.
* Cache3's maps that never shrink (4.4).
* Reclaim's scan at the step's time (023-06, section 2), which also
  removes the replaced queue's loads by reclaim.
* The run of dirty top nodes (section 5), with T1's C6 and C9.
* A test of the replaced queue with readers at earlier times under
  concurrency (`ReclaimReaders` with a large budget).
* Eviction's counts in `Db.cacheStats` and JMX.


## 9. Questions for Frans

* **Q1. Is the dead hand what you meant by Y6's (b)?** The dead hand
  releases what no available lookup can reach, after each cut, whatever
  the budget. The replaced queue is 023-04's X6 (b) as written, and also
  releases what only lookups at earlier times reach. Recommended: both.
* **Q2. The replaced queue's cost.** Lookups at earlier times, and
  reclaim's scan of an iteration in progress after a mass delete, load
  what it evicted (T1 at 100,000: 190,272 loads against none). Under a
  budget it saves loads (T4: 6,515 against 81,137). Keep it on by
  default? Recommended: yes, with reclaim's scan at the step's time
  (023-06, section 2) to remove the deletes' loads.
* **Q3. `noEvict()`.** It keeps "nothing is freed": the Core-only option
  the test setups use. Or should the dead hand run there too, so that an
  ended version leaves memory in every configuration? Recommended: keep
  `noEvict()` as it is.
* **Q4. The run of dirty top nodes** (section 5). Fix (a), the take writes
  a top node's dirty skip targets in the same record, as a change of what
  format 6's records hold and of the model's take? Or leave it bounded as
  it is, with a tolerance in C6 and C9? Recommended: (a), in phase 2,
  after a probe.


## 10. State

2026-11-10, 13:45. Done for this session. Branch `023-p6-memory` in the
clone `/Users/f/fl/bench/2026-11-10/p6/clone`, head `c46d607d`, on P4's
`0e66d1c9`.

* **Gates on the head:** `before-commit.sh` OK; `level4.sh` full OK.
* **Gates on the dead hand alone** (`411ae3d1`): `level1.sh` OK.
* **Not run:** `level2.sh` and `level3.sh` (P6 changes neither startup
  nor reclaim); StreamDigest.
* **Measurements** were made in a second clone,
  `/Users/f/fl/bench/2026-11-10/p6/mclone`: `6451d774` plus the Cache3
  shrink patch (4.4), a peaks probe and `c46d607d`'s test fix. The shrink
  changes no count.
* **Runs and logs:** `/Users/f/fl/bench/2026-11-10/p6/runs/`
  * `t1-*`, `t4-*`: P4 and the dead hand, with `deadfalse` and
    `deadtrue`.
  * `r2-*`: P6.
  * `t1m12-*`: 1M.
  * `hashed-*`, `t4h-*`: hashed keys.
  * `t1m-dprobe*.txt`: section 5.
  * `level*`, `before-commit-*`: the gates.
  * `cache3-shrink.patch`: the patch of 4.4.
* **Scripts:** `/Users/f/fl/bench/2026-11-10/p6/tools/`.
* **Next:** Frans's answers to Q1 to Q4. A quiet-machine timing.
